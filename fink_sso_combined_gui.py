"""
AstroPrak server dashboard.

This GUI does not run the Fink stream locally. It reads the SQLite database on
the server via SSH and shows the live recent alerts plus long-running collector
statistics.
"""

from __future__ import annotations

import ast
import importlib.util
import json
import os
import queue
import shlex
import subprocess
import threading
import traceback
import math
import time
import re
import contextlib
import base64
import gzip
import io
import tkinter as tk
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
from tkinter import ttk

import numpy as np
import pandas as pd
import requests
from matplotlib.figure import Figure
from matplotlib.patches import Circle
from matplotlib.ticker import ScalarFormatter
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from astroquery.mpc import MPC
from astroquery.jplhorizons import Horizons
from astropy.time import Time, TimeDelta
from astropy.timeseries import LombScargle
from scipy.optimize import curve_fit

try:
    from config import DEFAULT_WINDOWS_DATA_DIR
except ImportError:
    DEFAULT_WINDOWS_DATA_DIR = Path(os.environ.get("ASTROPRAK_DATA_DIR") or "data")


SERVER_HOST = os.environ.get("ASTROPRAK_SERVER_HOST", "127.0.0.1")
SERVER_USER = os.environ.get("ASTROPRAK_SERVER_USER", "astroprak")
SERVER_TARGET = f"{SERVER_USER}@{SERVER_HOST}"

DB_PATH = "/var/lib/astroprak/alerts.sqlite"
SERVICE_NAME = "astroprak-collector"
SCORING_CONFIG_PATH = "/opt/astroprak/scoring_config.json"
FINK_ZTF_CUTOUT_API_URL = "https://api.ztf.fink-portal.org/api/v1/cutouts"
FINK_ZTF_OBJECT_API_URL = "https://api.ztf.fink-portal.org/api/v1/objects"
FINK_LSST_CUTOUT_API_URL = "https://api.lsst.fink-portal.org/api/v1/cutouts"
DEFAULT_LIMIT = 2000
LIVE_POLL_MS = 15000
DASHBOARD_POLL_MS = 5000
SAVED_ALERT_CACHE_REFRESH_SECONDS = 120
STARTUP_LIVE_REFRESH_DELAY_MS = 15000
STARTUP_SKY_REFRESH_DELAY_MS = 15000
SEEN_PATH = Path.home() / ".astroprak_server_viewer_seen.json"
RECENT_ALERT_CACHE_PATH = Path.home() / ".astroprak_recent_alerts_cache.json.gz"
SSH_CONCURRENCY = 3
SSH_SEMAPHORE = threading.BoundedSemaphore(SSH_CONCURRENCY)
RECENT_ALERT_CACHE_LOCK = threading.Lock()
DEFAULT_DATA_DIR = DEFAULT_WINDOWS_DATA_DIR

# ============================================================
# Standalone Deep Analysis (copied into Sandbox7)
# ============================================================

# ============================================================
# Deep-analysis settings
# ============================================================

# The deep analysis below uses exactly the MPC + Horizons logic:
# 1) load historical MPC photometry,
# 2) load/interpolate Horizons r, Delta and phase angle,
# 3) compute reduced magnitude,
# 4) fit a quadratic phase function,
# 5) display the corrected brightness directly inside the GUI.
MPC_ANALYSIS_LOCATION = "500"
MPC_ANALYSIS_START_DATE_FILTER = "1990-01-01"
MPC_ANALYSIS_GRID_STEP = "5d"
MPC_ANALYSIS_CACHE_DIR = Path(".")
FINK_ZTF_SSO_API_URL = "https://api.ztf.fink-portal.org/api/v1/sso"
FINK_LSST_SSO_API_URL = "https://api.lsst.fink-portal.org/api/v1/sso"
FINK_HISTORY_TIMEOUT = 120
FINK_HISTORY_MEMORY_CACHE_SECONDS = 600
CUTOUT_HISTORY_MAX_EPOCHS = 8
CUTOUT_GENERAL_MAX_EPOCHS = 12
CUTOUT_GALLERY_PAGE_SIZE = 12
CUTOUT_GALLERY_MAX_EPOCHS = 48
CUTOUT_GENERAL_CANDIDATE_POOL = 24
CUTOUT_SIMILAR_CANDIDATE_POOL = 20
CUTOUT_REQUEST_TIMEOUT = 20
ZTF_PIXEL_SCALE_ARCSEC = 1.01
CUTOUT_SCALE_BAR_ARCSEC = 10.0
CUTOUT_HISTORY_CACHE_DIR = Path.home() / ".astroprak_cutout_cache"
CUTOUT_GEOMETRY_REL_TOLERANCE = 0.50
CUTOUT_PHASE_REL_TOLERANCE = 0.50
CUTOUT_PHASE_MIN_TOLERANCE_DEG = 1.0
WATER_SNOWLINE_AU = 2.7

ANALYSIS_MIN_PERIOD_HOURS = 1.5
ANALYSIS_MAX_PERIOD_HOURS = 48.0
ANALYSIS_LS_FREQUENCY_GRID_SIZE = 3000

FINK_HISTORY_MEMORY_CACHE = {}
FINK_HISTORY_INFLIGHT = {}
FINK_HISTORY_CACHE_LOCK = threading.Lock()
MPC_OBSERVATION_MEMORY_CACHE = {}
MPC_OBSERVATION_CACHE_LOCK = threading.Lock()
HORIZONS_ELEMENTS_MEMORY_CACHE = {}
HORIZONS_ELEMENTS_CACHE_LOCK = threading.Lock()
ALERT_ASSIGNMENT_MEMORY_CACHE = {}
ALERT_ASSIGNMENT_CACHE_LOCK = threading.Lock()

# ============================================================
# Deep analysis helper functions
# ============================================================

def make_figure(figsize=(12, 5)):
    return Figure(figsize=figsize, dpi=100)


def to_float(x):
    if x is None:
        return None

    try:
        value = float(x)
    except (TypeError, ValueError):
        return None

    if not np.isfinite(value):
        return None

    return value


def jd_to_night_key(jd, fallback_date=None):
    value = to_float(jd)

    if value is not None:
        return str(int(value - 0.5))

    if fallback_date is not None:
        try:
            return str(pd.Timestamp(fallback_date).date())
        except Exception:
            pass

    return "unknown"


def normalize_sso_id(sso_id):
    text = str(sso_id).strip()

    if text == "":
        return text

    try:
        value = float(text)

        if value.is_integer():
            return str(int(value))

    except (TypeError, ValueError):
        pass

    provisional_match = re.match(
        r"^(\d{4})\s*([A-Za-z]{1,2})\s*(\d*)$",
        text
    )

    if provisional_match:
        year, letters, number = provisional_match.groups()
        return f"{year} {letters.upper()}{number}"

    return text


def comparable_sso_id(sso_id):
    return normalize_sso_id(sso_id).lower().replace(" ", "")


ACTIVE_OBJECT_ALIASES = {
    "29p": {
        "display": "29P/Schwassmann-Wachmann 1",
        "mpc": "P/1927 V1",
        "horizons": "90000395",
        "fink": "29P",
    },
    "29p/schwassmann-wachmann": {
        "display": "29P/Schwassmann-Wachmann 1",
        "mpc": "P/1927 V1",
        "horizons": "90000395",
        "fink": "29P",
    },
    "29p/schwassmann-wachmann1": {
        "display": "29P/Schwassmann-Wachmann 1",
        "mpc": "P/1927 V1",
        "horizons": "90000395",
        "fink": "29P",
    },
    "schwassmann-wachmann1": {
        "display": "29P/Schwassmann-Wachmann 1",
        "mpc": "P/1927 V1",
        "horizons": "90000395",
        "fink": "29P",
    },
    "133p": {
        "display": "133P/Elst-Pizarro",
        "mpc": "7968",
        "horizons": "7968",
        "fink": "133P",
    },
    "133p/elst-pizarro": {
        "display": "133P/Elst-Pizarro",
        "mpc": "7968",
        "horizons": "7968",
        "fink": "133P",
    },
    "elst-pizarro": {
        "display": "133P/Elst-Pizarro",
        "mpc": "7968",
        "horizons": "7968",
        "fink": "133P",
    },
    "176p": {
        "display": "176P/LINEAR",
        "mpc": "118401",
        "horizons": "118401",
        "fink": "176P",
    },
    "176p/linear": {
        "display": "176P/LINEAR",
        "mpc": "118401",
        "horizons": "118401",
        "fink": "176P",
    },
    "288p": {
        "display": "288P/(300163) 2006 VW139",
        "mpc": "300163",
        "horizons": "300163",
        "fink": "288P",
    },
    "288p/2006vw139": {
        "display": "288P/(300163) 2006 VW139",
        "mpc": "300163",
        "horizons": "300163",
        "fink": "288P",
    },
    "433p": {
        "display": "433P/(248370) 2005 QN173",
        "mpc": "248370",
        "horizons": "248370",
        "fink": "433P",
    },
    "433p/2005qn173": {
        "display": "433P/(248370) 2005 QN173",
        "mpc": "248370",
        "horizons": "248370",
        "fink": "433P",
    },
    "p/2013r3": {
        "display": "P/2013 R3/Catalina-PANSTARRS",
        "mpc": "P/2013 R3",
        "horizons": "90004240",
        "fink": "P/2013 R3",
    },
    "p/2013r3/catalina-panstarrs": {
        "display": "P/2013 R3/Catalina-PANSTARRS",
        "mpc": "P/2013 R3",
        "horizons": "90004240",
        "fink": "P/2013 R3",
    },
    "p/2010a2": {
        "display": "P/2010 A2/LINEAR",
        "mpc": "P/2010 A2",
        "horizons": "354P",
        "fink": "P/2010 A2",
    },
    "p/2010a2/linear": {
        "display": "P/2010 A2/LINEAR",
        "mpc": "P/2010 A2",
        "horizons": "354P",
        "fink": "P/2010 A2",
    },
    "6478gault": {
        "display": "(6478) Gault",
        "mpc": "6478",
        "horizons": "6478",
        "fink": "6478",
    },
    "gault": {
        "display": "(6478) Gault",
        "mpc": "6478",
        "horizons": "6478",
        "fink": "6478",
    },
    "(6478)gault": {
        "display": "(6478) Gault",
        "mpc": "6478",
        "horizons": "6478",
        "fink": "6478",
    },
}


def resolve_analysis_ids(sso_id):
    text = normalize_sso_id(sso_id)
    key = text.lower().replace(" ", "")
    periodic_match = re.match(r"^(\d+)p(?:/.*)?$", key)

    if key in ACTIVE_OBJECT_ALIASES:
        return dict(ACTIVE_OBJECT_ALIASES[key])

    if key in ["1p", "1p/halley", "halley", "halley'scomet", "halleyscomet"]:
        return {
            "display": "1P/Halley",
            "mpc": "1P",
            "horizons": "90000001",
            "fink": "1P",
        }

    if key in ["ceres", "1ceres", "(1)ceres"]:
        return {
            "display": "1 Ceres",
            "mpc": "1",
            "horizons": "1",
            "fink": "1",
        }

    if key in [
        "u1",
        "1i",
        "1i/2017u1",
        "a/2017u1",
        "2017u1",
        "oumuamua",
        "'oumuamua",
        "Ê»oumuamua",
        "1i/oumuamua",
        "1i/'oumuamua",
        "1i/Ê»oumuamua",
    ]:
        return {
            "display": "1I/'Oumuamua",
            "mpc": "1I",
            "horizons": "1I",
            "fink": "1I",
        }

    if key in ["2p", "2p/encke", "encke"]:
        return {
            "display": "2P/Encke",
            "mpc": "2P",
            "horizons": "90000091",
            "fink": "2P",
        }

    if key in [
        "67p",
        "67p/churyumov-gerasimenko",
        "churyumov-gerasimenko",
        "churyumovgerasimenko",
    ]:
        return {
            "display": "67P/Churyumov-Gerasimenko",
            "mpc": "67P",
            "horizons": "90000702",
            "fink": "67P",
        }

    if key in ["46p", "46p/wirtanen", "wirtanen"]:
        return {
            "display": "46P/Wirtanen",
            "mpc": "46P",
            "horizons": "90000547",
            "fink": "46P",
        }

    if periodic_match:
        periodic_id = f"{periodic_match.group(1)}P"

        return {
            "display": periodic_id,
            "mpc": periodic_id,
            "horizons": periodic_id,
            "fink": periodic_id,
        }

    return {
        "display": text,
        "mpc": text,
        "horizons": text,
        "fink": text,
    }


def latest_horizons_record_from_ambiguity(error_text, primary_designation=None):
    candidates = []

    for line in str(error_text).splitlines():
        match = re.match(
            r"\s*(\d{6,})\s+(\d{4})\s+(.+)$",
            line
        )

        if match is None:
            continue

        record_id = match.group(1)
        epoch_year = int(match.group(2))
        rest = match.group(3)

        if primary_designation is not None:
            normalized_primary = str(primary_designation).lower().replace(" ", "")
            normalized_rest = rest.lower().replace(" ", "")

            if normalized_primary not in normalized_rest:
                continue

        candidates.append((epoch_year, record_id))

    if not candidates:
        return None

    candidates.sort()

    return candidates[-1][1]


def resolve_horizons_smallbody_id(query_id, mpc_id=None, summary_lines=None):
    try:
        get_horizons_elements_cached(query_id)

        return query_id

    except Exception as exc:
        error_text = str(exc)

        if (
            "JPL/HORIZONS" in error_text
            and ("EC=" in error_text or "QR=" in error_text or "A=" in error_text)
        ):
            if summary_lines is not None:
                summary_lines.append(
                    f"Horizons ID accepted    : {query_id} "
                    "(elements parser failed, ephemerides will be used)"
                )

            return query_id

        record_id = latest_horizons_record_from_ambiguity(
            error_text,
            primary_designation=mpc_id
        )

        if record_id is None:
            record_id = latest_horizons_record_from_ambiguity(error_text)

        if record_id is None:
            raise

        if summary_lines is not None:
            summary_lines.append(
                f"Horizons ID resolved    : {query_id} -> {record_id}"
            )

        return record_id


def mpc_phase_model(alpha, H0, a, b):
    return H0 + a * alpha + b * alpha**2


def get_horizons_column(table, possible_names):
    for name in possible_names:
        if name in table.colnames:
            return np.array(table[name], dtype=float)

    raise RuntimeError(
        f"Keine passende Horizons-Spalte gefunden. Gesucht: {possible_names}\n"
        f"Vorhandene Spalten: {table.colnames}"
    )


def angular_separation_arcsec(ra1_deg, dec1_deg, ra2_deg, dec2_deg):
    ra1 = math.radians(float(ra1_deg))
    dec1 = math.radians(float(dec1_deg))
    ra2 = math.radians(float(ra2_deg))
    dec2 = math.radians(float(dec2_deg))
    sin_ddec = math.sin((dec2 - dec1) / 2.0)
    sin_dra = math.sin((ra2 - ra1) / 2.0)
    haversine = (
        sin_ddec ** 2
        + math.cos(dec1) * math.cos(dec2) * sin_dra ** 2
    )
    angle = 2.0 * math.asin(math.sqrt(min(1.0, max(0.0, haversine))))
    return math.degrees(angle) * 3600.0


def horizons_location_for_alert(alert):
    survey = str(alert.get("survey") or "").strip().lower()
    if survey == "ztf":
        return "I41"
    if survey == "lsst":
        return "X05"
    return MPC_ANALYSIS_LOCATION


def verify_alert_object_assignment(sso_id, alert):
    if not isinstance(alert, dict):
        return {"status": "not_possible", "message": "No selected alert."}
    ra = to_float(alert.get("ra"))
    dec = to_float(alert.get("dec"))
    jd = to_float(alert.get("jd"))
    if ra is None or dec is None or jd is None:
        return {
            "status": "not_possible",
            "message": "Alert has no complete RA/Dec/JD position.",
        }

    analysis_ids = resolve_analysis_ids(sso_id)
    horizons_id = resolve_horizons_smallbody_id(
        analysis_ids["horizons"],
        mpc_id=analysis_ids["mpc"],
    )
    location = horizons_location_for_alert(alert)
    cache_key = (
        str(horizons_id),
        round(jd, 8),
        location,
        round(ra, 7),
        round(dec, 7),
    )
    with ALERT_ASSIGNMENT_CACHE_LOCK:
        cached = ALERT_ASSIGNMENT_MEMORY_CACHE.get(cache_key)
    if cached is not None:
        return dict(cached)

    try:
        eph = Horizons(
            id=horizons_id,
            id_type="smallbody",
            location=location,
            epochs=[jd],
        ).ephemerides(quantities="1,3", cache=True)
        expected_ra = float(eph["RA"][0])
        expected_dec = float(eph["DEC"][0])
        separation = angular_separation_arcsec(
            ra,
            dec,
            expected_ra,
            expected_dec,
        )
        if separation <= 2.0:
            status = "confirmed"
            label = "CONFIRMED"
        elif separation <= 5.0:
            status = "plausible"
            label = "PLAUSIBLE"
        elif separation <= 15.0:
            status = "uncertain"
            label = "UNCERTAIN"
        else:
            status = "contradiction"
            label = "ASSIGNMENT CONFLICT"
        result = {
            "status": status,
            "label": label,
            "separation_arcsec": separation,
            "observed_ra": ra,
            "observed_dec": dec,
            "expected_ra": expected_ra,
            "expected_dec": expected_dec,
            "jd": jd,
            "location": location,
            "horizons_id": str(horizons_id),
        }
    except Exception as exc:
        result = {
            "status": "not_possible",
            "label": "NICHT PRUEFBAR",
            "message": str(exc),
            "jd": jd,
            "location": location,
            "horizons_id": str(horizons_id),
        }
    with ALERT_ASSIGNMENT_CACHE_LOCK:
        ALERT_ASSIGNMENT_MEMORY_CACHE[cache_key] = dict(result)
    return result


def append_alert_assignment_verification(summary_lines, sso_id, injected_alerts):
    summary_lines.append("Independent Alert/Object Position Check")
    summary_lines.append("-" * 40)
    if not injected_alerts:
        summary_lines.append("Result                 : no selected alert")
        summary_lines.append("")
        return
    result = verify_alert_object_assignment(sso_id, injected_alerts[0])
    summary_lines.append(
        f"Result                 : {result.get('label') or result.get('status')}"
    )
    if result.get("separation_arcsec") is not None:
        summary_lines.append(
            f"Position separation    : {result['separation_arcsec']:.3f} arcsec"
        )
        summary_lines.append(
            f"Alert RA/Dec           : {result['observed_ra']:.7f}, {result['observed_dec']:.7f} deg"
        )
        summary_lines.append(
            f"Horizons RA/Dec        : {result['expected_ra']:.7f}, {result['expected_dec']:.7f} deg"
        )
    summary_lines.append(
        f"Observatory / epoch    : {result.get('location', 'n/a')} / JD {result.get('jd', 'n/a')}"
    )
    if result.get("message"):
        summary_lines.append(f"Technical detail       : {result['message']}")
    summary_lines.append(
        "Interpretation          : this independently tests positional consistency; it does not prove identity from position alone."
    )
    summary_lines.append("")


def make_horizons_cache_file(sso_id):
    safe_sso_id = "".join(
        char if char.isalnum() or char in ["-", "_"] else "_"
        for char in str(sso_id)
    )

    safe_grid_step = "".join(
        char if char.isalnum() or char in ["-", "_"] else "_"
        for char in str(MPC_ANALYSIS_GRID_STEP)
    )

    return MPC_ANALYSIS_CACHE_DIR / f"horizons_cache_{safe_sso_id}_{safe_grid_step}.csv"


def get_horizons_elements_cached(sso_id):
    cache_key = str(sso_id)
    with HORIZONS_ELEMENTS_CACHE_LOCK:
        cached = HORIZONS_ELEMENTS_MEMORY_CACHE.get(cache_key)
    if cached is not None:
        return cached
    elements = Horizons(
        id=sso_id,
        id_type="smallbody",
    ).elements()
    with HORIZONS_ELEMENTS_CACHE_LOCK:
        HORIZONS_ELEMENTS_MEMORY_CACHE[cache_key] = elements
    return elements


def load_mpc_observations_dataframe(sso_id, summary_lines=None):
    cache_key = str(sso_id)
    with MPC_OBSERVATION_CACHE_LOCK:
        cached = MPC_OBSERVATION_MEMORY_CACHE.get(cache_key)
    if cached is not None:
        if summary_lines is not None:
            summary_lines.append(
                f"MPC observations        : {len(cached)} rows (memory cache)"
            )
        return cached.copy(deep=True)

    try:
        obs = MPC.get_observations(sso_id)
    except Exception as exc:
        if summary_lines is not None:
            summary_lines.append(f"MPC observations        : failed ({exc})")

        return pd.DataFrame()

    df = pd.DataFrame({
        col: obs[col]
        for col in obs.colnames
    })

    if "epoch" not in df.columns:
        if summary_lines is not None:
            summary_lines.append("MPC observations        : missing epoch column; skipped")

        return pd.DataFrame()

    if "mag" not in df.columns:
        if summary_lines is not None:
            summary_lines.append("MPC observations        : missing magnitude column; skipped")

        return pd.DataFrame()

    df["epoch"] = pd.to_numeric(df["epoch"], errors="coerce")
    df["mag"] = pd.to_numeric(df["mag"], errors="coerce")

    finite_epoch_mask = np.isfinite(df["epoch"].to_numpy(dtype=float, copy=False))
    df = df[finite_epoch_mask].copy()

    if len(df) == 0:
        if summary_lines is not None:
            summary_lines.append("MPC observations        : no valid epochs")

        return pd.DataFrame()

    df["date"] = pd.to_datetime(
        Time(df["epoch"].to_numpy(), format="jd").datetime
    )

    df = df[
        np.isfinite(df["epoch"]) &
        np.isfinite(df["mag"]) &
        (df["mag"] > 5) &
        (df["mag"] < 30) &
        (df["date"] >= pd.Timestamp(MPC_ANALYSIS_START_DATE_FILTER))
    ].copy()

    df = df.sort_values("epoch").reset_index(drop=True)

    if len(df) == 0:
        if summary_lines is not None:
            summary_lines.append("MPC observations        : no valid rows after filtering")

        return pd.DataFrame()

    df["source"] = "MPC"
    df["fid"] = None

    if summary_lines is not None:
        summary_lines.append(f"MPC observations        : {len(df)} rows")

    with MPC_OBSERVATION_CACHE_LOCK:
        MPC_OBSERVATION_MEMORY_CACHE[cache_key] = df.copy(deep=True)
    return df


def build_fink_sso_payload(sso_id, with_ephem=True, with_residuals=False):
    return {
        "n_or_d": str(sso_id).strip(),
        "withEphem": bool(with_ephem),
        "withResiduals": bool(with_residuals),
        "output-format": "json",
    }


def fetch_fink_history_response(api_url, sso_id):
    key = (str(api_url), str(sso_id).strip())
    owner = False
    with FINK_HISTORY_CACHE_LOCK:
        cached = FINK_HISTORY_MEMORY_CACHE.get(key)
        if cached is not None:
            cached_at, status_code, content = cached
            if time.monotonic() - cached_at <= FINK_HISTORY_MEMORY_CACHE_SECONDS:
                return status_code, content, True
            FINK_HISTORY_MEMORY_CACHE.pop(key, None)
        event = FINK_HISTORY_INFLIGHT.get(key)
        if event is None:
            event = threading.Event()
            FINK_HISTORY_INFLIGHT[key] = event
            owner = True

    if not owner:
        event.wait(FINK_HISTORY_TIMEOUT + 10)
        with FINK_HISTORY_CACHE_LOCK:
            cached = FINK_HISTORY_MEMORY_CACHE.get(key)
        if cached is None:
            raise RuntimeError(f"Shared Fink history request failed for {sso_id}.")
        _cached_at, status_code, content = cached
        return status_code, content, True

    try:
        response = requests.post(
            api_url,
            json=build_fink_sso_payload(
                sso_id,
                with_ephem=True,
                with_residuals=False,
            ),
            timeout=FINK_HISTORY_TIMEOUT,
        )
        status_code = int(response.status_code)
        content = bytes(response.content)
        if status_code != 404:
            response.raise_for_status()
        with FINK_HISTORY_CACHE_LOCK:
            FINK_HISTORY_MEMORY_CACHE[key] = (
                time.monotonic(),
                status_code,
                content,
            )
        return status_code, content, False
    finally:
        with FINK_HISTORY_CACHE_LOCK:
            finished = FINK_HISTORY_INFLIGHT.pop(key, None)
            if finished is not None:
                finished.set()


def load_fink_sso_history_dataframe(sso_id, api_url, source_label, summary_lines):
    try:
        status_code, content, from_cache = fetch_fink_history_response(
            api_url,
            sso_id,
        )

        if status_code == 404:
            summary_lines.append(f"{source_label} history          : endpoint not available")
            return pd.DataFrame()

        df_raw = pd.read_json(io.BytesIO(content))

        if len(df_raw) == 0:
            summary_lines.append(f"{source_label} history          : no rows")
            return pd.DataFrame()

        jd_col = "i:jd" if "i:jd" in df_raw.columns else "jd"
        mag_col = "i:magpsf" if "i:magpsf" in df_raw.columns else "magpsf"
        sig_col = "i:sigmapsf" if "i:sigmapsf" in df_raw.columns else "sigmapsf"
        fid_col = "i:fid" if "i:fid" in df_raw.columns else "fid"

        if jd_col not in df_raw.columns or mag_col not in df_raw.columns:
            summary_lines.append(f"{source_label} history          : missing jd/magnitude columns")
            return pd.DataFrame()

        df = pd.DataFrame()
        df["epoch"] = pd.to_numeric(df_raw[jd_col], errors="coerce")
        df["mag"] = pd.to_numeric(df_raw[mag_col], errors="coerce")

        if sig_col in df_raw.columns:
            df["mag_err"] = pd.to_numeric(df_raw[sig_col], errors="coerce")
        else:
            df["mag_err"] = np.nan

        if fid_col in df_raw.columns:
            df["fid"] = df_raw[fid_col]
        else:
            df["fid"] = None

        df["date"] = pd.to_datetime(
            Time(df["epoch"].to_numpy(), format="jd").datetime
        )
        df["source"] = source_label

        df = df[
            np.isfinite(df["epoch"]) &
            np.isfinite(df["mag"]) &
            (df["mag"] > 5) &
            (df["mag"] < 30) &
            (df["date"] >= pd.Timestamp(MPC_ANALYSIS_START_DATE_FILTER))
        ].copy()

        df = df.sort_values("epoch").reset_index(drop=True)
        cache_note = " (memory cache)" if from_cache else ""
        summary_lines.append(
            f"{source_label} history          : {len(df)} rows{cache_note}"
        )

        return df

    except Exception as exc:
        summary_lines.append(f"{source_label} history          : failed ({exc})")
        return pd.DataFrame()


def build_live_alert_dataframe(injected_alerts, summary_lines):
    if not injected_alerts:
        return pd.DataFrame()

    rows = []

    for alert in injected_alerts:
        if not isinstance(alert, dict):
            continue

        jd = to_float(alert.get("jd"))
        mag = to_float(alert.get("magpsf"))

        if jd is None or mag is None:
            continue

        sigmag = to_float(alert.get("sigmapsf"))
        fid = alert.get("fid")

        try:
            date = pd.to_datetime(
                Time(jd, format="jd").datetime
            )
        except Exception:
            date = pd.NaT

        rows.append({
            "epoch": jd,
            "mag": mag,
            "mag_err": sigmag if sigmag is not None else np.nan,
            "fid": fid,
            "date": date,
            "source": "Live",
        })

    if not rows:
        summary_lines.append("Live server alerts      : no usable selected live alert")
        return pd.DataFrame()

    df = pd.DataFrame(rows)
    df = df[
        np.isfinite(df["epoch"])
        & np.isfinite(df["mag"])
        & (df["mag"] > 5)
        & (df["mag"] < 30)
        & df["date"].notna()
    ].copy()
    df = df.sort_values("epoch").reset_index(drop=True)
    summary_lines.append(f"Live server alerts      : {len(df)} injected row(s)")

    return df


def combine_observation_sources(mpc_df, extra_dfs, summary_lines):
    frames = []

    if mpc_df is not None and len(mpc_df) > 0:
        frames.append(mpc_df)

    for extra_df in extra_dfs:
        if extra_df is not None and len(extra_df) > 0:
            frames.append(extra_df)

    if not frames:
        raise RuntimeError(
            "No usable observations found from MPC, Fink/ZTF or Fink/LSST for this object."
        )

    combined = pd.concat(frames, ignore_index=True, sort=False)
    combined = combined.sort_values("epoch").reset_index(drop=True)
    source_counts = combined["source"].value_counts().to_dict()
    summary_lines.append("Observation sources     : " + json.dumps(source_counts, default=str))

    return combined


def source_color(source):
    colors = {
        "MPC": "black",
        "Fink/ZTF": "tab:blue",
        "Fink/LSST": "tab:orange",
        "Live": "red",
    }

    return colors.get(str(source), "tab:gray")


def scatter_by_source(ax, df, x_col, y_col, size=8, alpha=0.75):
    sources = sorted(
        df["source"].dropna().unique(),
        key=lambda value: (str(value) == "Live", str(value))
    )

    for source in sources:
        mask = df["source"] == source
        current_size = size
        current_alpha = alpha
        edgecolor = "none"
        linewidth = 0
        zorder = 3

        if str(source) == "Live":
            current_size = size
            current_alpha = 1.0
            edgecolor = "none"
            linewidth = 0
            zorder = 30

        ax.scatter(
            df.loc[mask, x_col],
            df.loc[mask, y_col],
            s=current_size,
            alpha=current_alpha,
            color=source_color(source),
            edgecolors=edgecolor,
            linewidths=linewidth,
            label=str(source),
            zorder=zorder,
        )


def load_horizons_grid_for_mpc_analysis(sso_id, jd_obs, summary_lines):
    cache_file = make_horizons_cache_file(sso_id)
    use_cache = False

    if cache_file.exists():
        try:
            eph_grid = pd.read_csv(cache_file)
            needed_cols = {"datetime_jd", "r", "delta", "alpha"}

            if needed_cols.issubset(eph_grid.columns):
                cached_min = np.nanmin(eph_grid["datetime_jd"].to_numpy(dtype=float))
                cached_max = np.nanmax(eph_grid["datetime_jd"].to_numpy(dtype=float))

                if cached_min <= np.nanmin(jd_obs) and cached_max >= np.nanmax(jd_obs):
                    use_cache = True
                    summary_lines.append(f"Horizons cache used     : {cache_file}")
                else:
                    summary_lines.append(
                        "Horizons cache ignored  : existing cache does not cover full MPC time range"
                    )
            else:
                summary_lines.append("Horizons cache ignored  : cache is incomplete")

        except Exception as exc:
            summary_lines.append(f"Horizons cache ignored  : could not read cache ({exc})")

    if not use_cache:
        t_start = Time(np.nanmin(jd_obs), format="jd") - TimeDelta(2, format="jd")
        t_stop = Time(np.nanmax(jd_obs), format="jd") + TimeDelta(2, format="jd")

        start_str = t_start.iso.split()[0]
        stop_str = t_stop.iso.split()[0]

        summary_lines.append(f"Horizons time range     : {start_str} to {stop_str}")
        summary_lines.append(f"Horizons grid step      : {MPC_ANALYSIS_GRID_STEP}")

        horizons_t0 = time.perf_counter()

        obj = Horizons(
            id=sso_id,
            id_type="smallbody",
            location=MPC_ANALYSIS_LOCATION,
            epochs={
                "start": start_str,
                "stop": stop_str,
                "step": MPC_ANALYSIS_GRID_STEP
            }
        )

        eph = obj.ephemerides(
            quantities="19,20,24",
            cache=True
        )

        horizons_t1 = time.perf_counter()

        datetime_jd = get_horizons_column(eph, ["datetime_jd"])
        r = get_horizons_column(eph, ["r"])
        delta = get_horizons_column(eph, ["delta"])
        alpha = get_horizons_column(eph, ["alpha", "S-T-O", "STO", "phi"])

        eph_grid = pd.DataFrame({
            "datetime_jd": datetime_jd,
            "r": r,
            "delta": delta,
            "alpha": alpha
        })

        eph_grid.to_csv(cache_file, index=False)

        summary_lines.append(f"Horizons runtime        : {horizons_t1 - horizons_t0:.1f} s")
        summary_lines.append(f"Horizons columns loaded : {', '.join(eph.colnames)}")
        summary_lines.append(f"Horizons cache saved    : {cache_file}")

    eph_grid = (
        eph_grid
        .sort_values("datetime_jd")
        .drop_duplicates("datetime_jd")
    )

    return eph_grid


def add_mpc_overview_figure(figures, sso_id, df, alpha_plot, phase_fit_plot):
    fig = make_figure((16, 13))
    axes = fig.subplots(3, 2).ravel()

    axes[0].scatter(
        df["date"],
        df["delta"],
        s=5,
        alpha=0.7
    )

    axes[0].set_xlabel("Date")
    axes[0].set_ylabel("Observer distance Î” [AU]")
    axes[0].set_title(f"{sso_id}: Observer distance")
    axes[0].grid(True)

    axes[1].scatter(
        df["date"],
        df["mag"],
        s=5,
        alpha=0.7
    )

    axes[1].invert_yaxis()
    axes[1].set_xlabel("Date")
    axes[1].set_ylabel("Observed magnitude")
    axes[1].set_title(f"{sso_id}: Observed brightness")
    axes[1].grid(True)

    axes[2].scatter(
        df["date"],
        df["m_red"],
        s=5,
        alpha=0.7
    )

    axes[2].invert_yaxis()
    axes[2].set_xlabel("Date")
    axes[2].set_ylabel("Reduced magnitude")
    axes[2].set_title(
        r"Reduced brightness: $m_{\rm red}=m-5\log_{10}(r\Delta)$"
    )
    axes[2].grid(True)

    axes[3].scatter(
        df["alpha"],
        df["m_red"],
        s=5,
        alpha=0.25,
        label="Data"
    )

    axes[3].plot(
        alpha_plot,
        phase_fit_plot,
        linewidth=3,
        label="Quadratic phase fit"
    )

    axes[3].invert_yaxis()
    axes[3].set_xlabel("Phase angle Î± [deg]")
    axes[3].set_ylabel("Reduced magnitude")
    axes[3].set_title(f"{sso_id}: Phase function")
    axes[3].legend()
    axes[3].grid(True)

    axes[4].scatter(
        df["date"],
        df["H_corr"],
        s=5,
        alpha=0.7
    )

    axes[4].invert_yaxis()
    axes[4].set_xlabel("Date")
    axes[4].set_ylabel("Phase-corrected magnitude")
    axes[4].set_title(f"{sso_id}: Corrected brightness")
    axes[4].grid(True)

    axes[5].scatter(
        df["date"],
        df["phase_correction"],
        s=5,
        alpha=0.7
    )

    axes[5].set_xlabel("Date")
    axes[5].set_ylabel("Applied phase correction [mag]")
    axes[5].set_title(f"{sso_id}: Applied phase correction")
    axes[5].grid(True)

    fig.tight_layout()
    figures.append(("00 MPC/Horizons overview", fig))


def add_mpc_single_plot_figures(figures, sso_id, df, alpha_plot, phase_fit_plot):
    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.scatter(df["date"], df["delta"], s=5, alpha=0.7)
    ax.set_xlabel("Date")
    ax.set_ylabel("Observer distance Î” [AU]")
    ax.set_title(f"{sso_id}: Observer distance")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("01 Observer distance", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.scatter(df["date"], df["mag"], s=5, alpha=0.7)
    ax.invert_yaxis()
    ax.set_xlabel("Date")
    ax.set_ylabel("Observed magnitude")
    ax.set_title(f"{sso_id}: Observed brightness")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("02 Observed brightness", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.scatter(df["date"], df["m_red"], s=5, alpha=0.7)
    ax.invert_yaxis()
    ax.set_xlabel("Date")
    ax.set_ylabel("Reduced magnitude")
    ax.set_title(r"Reduced brightness: $m_{\rm red}=m-5\log_{10}(r\Delta)$")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("03 Reduced brightness", fig))

    fig = make_figure((9, 7))
    ax = fig.add_subplot(111)
    ax.scatter(df["alpha"], df["m_red"], s=5, alpha=0.25, label="Data")
    ax.plot(alpha_plot, phase_fit_plot, linewidth=3, label="Quadratic phase fit")
    ax.invert_yaxis()
    ax.set_xlabel("Phase angle Î± [deg]")
    ax.set_ylabel("Reduced magnitude")
    ax.set_title(f"{sso_id}: Phase function")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("04 Phase function", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.scatter(df["date"], df["H_corr"], s=5, alpha=0.7)
    ax.invert_yaxis()
    ax.set_xlabel("Date")
    ax.set_ylabel("Phase-corrected magnitude")
    ax.set_title(f"{sso_id}: Corrected brightness")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("05 Phase-corrected brightness", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.scatter(df["date"], df["phase_correction"], s=5, alpha=0.7)
    ax.set_xlabel("Date")
    ax.set_ylabel("Applied phase correction [mag]")
    ax.set_title(f"{sso_id}: Applied phase correction")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("06 Applied phase correction", fig))


def compute_heliocentric_activity_metrics(df, sigma_threshold=-3.0, n_bins=10):
    mask = (
        np.isfinite(df["r"])
        & np.isfinite(df["residual_sigma"])
    )

    if np.sum(mask) < 5:
        return None

    work = df.loc[mask, ["r", "residual_sigma"]].copy()
    r_values = work["r"].to_numpy(dtype=float)
    sigma_values = work["residual_sigma"].to_numpy(dtype=float)

    global_slope = np.polyfit(r_values, sigma_values, 1)[0]
    global_corr = np.corrcoef(r_values, sigma_values)[0, 1]

    r_min = float(np.nanmin(r_values))
    r_max = float(np.nanmax(r_values))
    if r_min < 1.5:
        near_limit = 1.5
    else:
        near_limit = r_min + 0.35 * (r_max - r_min)
    far_limit = max(WATER_SNOWLINE_AU, r_min + 0.70 * (r_max - r_min))

    near = work[work["r"] <= near_limit]
    far = work[work["r"] >= far_limit]

    def fraction_active(frame):
        if len(frame) == 0:
            return np.nan
        return float(np.mean(frame["residual_sigma"].to_numpy(dtype=float) < sigma_threshold))

    def median_sigma(frame):
        if len(frame) == 0:
            return np.nan
        return float(np.nanmedian(frame["residual_sigma"].to_numpy(dtype=float)))

    near_active_fraction = fraction_active(near)
    far_active_fraction = fraction_active(far)
    near_median_sigma = median_sigma(near)
    far_median_sigma = median_sigma(far)

    bin_rows = []
    if r_max > r_min:
        bins = np.linspace(r_min, r_max, n_bins + 1)
        work["r_bin"] = pd.cut(work["r"], bins=bins, include_lowest=True)
        grouped = work.groupby("r_bin", observed=True)

        for interval, group in grouped:
            if len(group) < 3:
                continue
            center = 0.5 * (float(interval.left) + float(interval.right))
            bin_rows.append({
                "r_center": center,
                "median_sigma": float(np.nanmedian(group["residual_sigma"])),
                "active_fraction": fraction_active(group),
                "count": int(len(group)),
            })

    bin_df = pd.DataFrame(bin_rows)
    if len(bin_df) >= 3:
        binned_median_slope = np.polyfit(
            bin_df["r_center"].to_numpy(dtype=float),
            bin_df["median_sigma"].to_numpy(dtype=float),
            1
        )[0]
    else:
        binned_median_slope = np.nan

    return {
        "points": int(np.sum(mask)),
        "global_slope": float(global_slope),
        "global_corr": float(global_corr),
        "near_limit": float(near_limit),
        "far_limit": float(far_limit),
        "near_count": int(len(near)),
        "far_count": int(len(far)),
        "near_active_fraction": near_active_fraction,
        "far_active_fraction": far_active_fraction,
        "active_fraction_lift": near_active_fraction - far_active_fraction
        if np.isfinite(near_active_fraction) and np.isfinite(far_active_fraction)
        else np.nan,
        "near_median_sigma": near_median_sigma,
        "far_median_sigma": far_median_sigma,
        "median_sigma_shift": near_median_sigma - far_median_sigma
        if np.isfinite(near_median_sigma) and np.isfinite(far_median_sigma)
        else np.nan,
        "binned_median_slope": float(binned_median_slope)
        if np.isfinite(binned_median_slope)
        else np.nan,
        "bin_df": bin_df,
    }


def add_requested_deep_analysis_figures(
    figures,
    sso_id,
    df,
    alpha_plot,
    phase_fit_plot,
    H0=None,
    H=None,
    G=None,
    eph_grid=None,
    include_period_plots=False
):
    def model_date_series(column):
        if eph_grid is None or column not in eph_grid.columns or "datetime_jd" not in eph_grid.columns:
            return None, None
        model_df = eph_grid[["datetime_jd", column]].copy()
        model_df[column] = pd.to_numeric(model_df[column], errors="coerce")
        model_df["datetime_jd"] = pd.to_numeric(model_df["datetime_jd"], errors="coerce")
        model_df = model_df[np.isfinite(model_df["datetime_jd"]) & np.isfinite(model_df[column])]
        if len(model_df) == 0:
            return None, None
        dates = pd.to_datetime(model_df["datetime_jd"] - 2440587.5, unit="D", origin="unix", utc=True)
        return dates, model_df[column].to_numpy(dtype=float)

    def phase_fit_label():
        parts = []
        for name, value in (("Hfit", H0), ("H", H), ("G", G)):
            try:
                number = float(value)
            except (TypeError, ValueError):
                continue
            if np.isfinite(number):
                parts.append(f"{name}={number:.3f}")
        suffix = f" ({', '.join(parts)})" if parts else ""
        return "Quadratic phase fit" + suffix

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "H_corr", size=6, alpha=0.7)
    ax.invert_yaxis()
    ax.set_title(f"Absolute Magnitude - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Absolute magnitude")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("00 Absolute magnitude", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "residual_mag", size=7, alpha=0.75)
    ax.axhline(0, color="black", linestyle="--", linewidth=1)
    ax.invert_yaxis()
    ax.set_title(f"Phase-Corrected Residual Magnitude - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Residual magnitude")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("01 Residual magnitude", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "residual_sigma", size=7, alpha=0.75)
    ax.axhline(0, color="black", linestyle="--", linewidth=1)
    ax.axhline(-3, color="orange", linestyle="--", linewidth=1, label="-3 sigma")
    ax.axhline(-5, color="red", linestyle="--", linewidth=1, label="-5 sigma")
    ax.axhline(-7, color="purple", linestyle="--", linewidth=1, label="-7 sigma")
    ax.set_title(f"Residual Significance - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Residual sigma")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("02 Residual significance", fig))

    fig = make_figure((9, 6))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "r", "residual_sigma", size=8, alpha=0.75)
    helio_metrics = compute_heliocentric_activity_metrics(
        df,
        sigma_threshold=DEFAULT_THRESHOLDS["anomaly_sigma_weak"],
    )
    ax.axhline(0, color="black", linestyle="--", linewidth=1)
    ax.axhline(-3, color="orange", linestyle="--", linewidth=1, label="-3 sigma")
    ax.axhline(-5, color="red", linestyle="--", linewidth=1, label="-5 sigma")
    ax.axhline(-7, color="purple", linestyle="--", linewidth=1, label="-7 sigma")
    ax.axvline(
        2.7,
        color="tab:cyan",
        linestyle=":",
        linewidth=2,
        label="Water snowline ~2.7 AU"
    )
    if helio_metrics is not None and len(helio_metrics["bin_df"]) > 0:
        bin_df = helio_metrics["bin_df"]
        ax.plot(
            bin_df["r_center"],
            bin_df["median_sigma"],
            color="tab:orange",
            marker="o",
            linewidth=2.2,
            label="Binned median sigma",
        )
        ax2 = ax.twinx()
        ax2.plot(
            bin_df["r_center"],
            bin_df["active_fraction"] * 100.0,
            color="tab:green",
            marker="s",
            linewidth=1.8,
            alpha=0.85,
            label="Active fraction (< -3 sigma)",
        )
        ax2.set_ylabel("Active fraction [%]")
        active_percent = bin_df["active_fraction"].to_numpy(dtype=float) * 100.0
        if np.any(np.isfinite(active_percent)):
            y2_max = max(5, min(100, np.nanmax(active_percent) * 1.25))
        else:
            y2_max = 5
        ax2.set_ylim(0, y2_max)
        ax2.tick_params(axis="y", colors="tab:green")

        handles1, labels1 = ax.get_legend_handles_labels()
        handles2, labels2 = ax2.get_legend_handles_labels()
        ax.legend(handles1 + handles2, labels1 + labels2, loc="best")
    else:
        ax.legend()
    ax.invert_xaxis()
    ax.set_title(f"Residual Significance vs Heliocentric Distance - SSO {sso_id}")
    ax.set_xlabel("Heliocentric distance r [AU]")
    ax.set_ylabel("Residual sigma")
    ax.grid(True)
    fig.tight_layout()
    figures.append(("03 Residual sigma vs r", fig))

    fig = make_figure((14, 5))
    ax = fig.add_subplot(111)

    for source in sorted(df["source"].dropna().unique()):
        source_counts = (
            pd.DataFrame({"date": df.loc[df["source"] == source, "date"]})
            .set_index("date")
            .resample("ME")
            .size()
        )

        ax.bar(
            source_counts.index,
            source_counts.values,
            width=20,
            alpha=0.65,
            color=source_color(source),
            label=str(source)
        )

    ax.set_title(f"Observations per Month - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Number of Observations")
    ax.legend()
    ax.grid(axis="y")
    fig.tight_layout()
    figures.append(("04 Observations per month", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "r", size=6, alpha=0.7)
    model_dates, model_values = model_date_series("r")
    if model_dates is not None:
        ax.plot(model_dates, model_values, color="tab:cyan", linewidth=2.0, alpha=0.9, label="Horizons model")
    ax.set_title(f"Heliocentric Distance - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Heliocentric distance r [AU]")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("05 Heliocentric distance", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "delta", size=6, alpha=0.7)
    model_dates, model_values = model_date_series("delta")
    if model_dates is not None:
        ax.plot(model_dates, model_values, color="tab:cyan", linewidth=2.0, alpha=0.9, label="Horizons model")
    ax.set_title(f"Observer Distance - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Dobs [AU]")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("06 Observer distance", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "mag", size=6, alpha=0.7)
    ax.invert_yaxis()
    ax.set_title(f"Raw Lightcurve - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Magnitude")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("07 Raw lightcurve", fig))

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "date", "m_red", size=6, alpha=0.7)
    ax.invert_yaxis()
    ax.set_title(f"Reduced Magnitude - SSO {sso_id}")
    ax.set_xlabel("Date")
    ax.set_ylabel("Reduced magnitude")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("08 Reduced magnitude", fig))

    fig = make_figure((9, 7))
    ax = fig.add_subplot(111)
    scatter_by_source(ax, df, "alpha", "m_red", size=6, alpha=0.35)
    ax.plot(alpha_plot, phase_fit_plot, linewidth=3, label=phase_fit_label())
    ax.invert_yaxis()
    ax.set_title(f"HG1G2 Phase Fit - SSO {sso_id}")
    ax.set_xlabel("Phase Angle [deg]")
    ax.set_ylabel("Reduced magnitude")
    ax.legend()
    ax.grid(True)
    fig.tight_layout()
    figures.append(("09 HG1G2 phase fit", fig))

    if not include_period_plots:
        return

    if "mag_err" not in df.columns:
        df["mag_err"] = np.nan

    valid_period_mask = (
        np.isfinite(df["epoch"].to_numpy(dtype=float))
        & np.isfinite(df["residual_mag"].to_numpy(dtype=float))
    )

    t = df.loc[valid_period_mask, "epoch"].to_numpy(dtype=float)
    y = df.loc[valid_period_mask, "residual_mag"].to_numpy(dtype=float)
    dy = pd.to_numeric(
        df.loc[valid_period_mask, "mag_err"],
        errors="coerce"
    ).to_numpy(dtype=float)

    if len(t) < 10 or np.nanstd(y) <= 0:
        figures.append((
            "10 Lomb-Scargle diagnostic",
            make_text_figure(
                "Lomb-Scargle diagnostic",
                "Not enough valid phase-corrected residual points for a period search.\n"
                f"Valid points: {len(t)}"
            )
        ))
        return

    order = np.argsort(t)
    t = t[order]
    y = y[order]
    dy = dy[order]

    y = y - np.nanmedian(y)
    scatter = np.nanstd(y)

    if not np.isfinite(scatter) or scatter <= 0:
        figures.append((
            "10 Lomb-Scargle diagnostic",
            make_text_figure(
                "Lomb-Scargle diagnostic",
                "Cannot compute a useful period search because the residual scatter is invalid."
            )
        ))
        return

    good = np.isfinite(t) & np.isfinite(y) & (np.abs(y) < 4 * scatter)
    dy_good = np.isfinite(dy) & (dy > 0) & (dy < 2.0)

    if np.sum(dy_good & good) >= 10:
        good &= dy_good
        dy_clean = dy[good]
    else:
        dy_clean = None

    t = t[good]
    y = y[good]

    if len(t) < 10 or np.nanstd(y) <= 0:
        figures.append((
            "10 Lomb-Scargle diagnostic",
            make_text_figure(
                "Lomb-Scargle diagnostic",
                "Not enough points remain after the 4-sigma residual outlier cut.\n"
                f"Remaining points: {len(t)}"
            )
        ))
        return

    t0 = np.nanmin(t)
    t_rel = t - t0

    period_grid_hours = np.geomspace(
        ANALYSIS_MIN_PERIOD_HOURS,
        ANALYSIS_MAX_PERIOD_HOURS,
        ANALYSIS_LS_FREQUENCY_GRID_SIZE
    )

    frequency = 24.0 / period_grid_hours

    ls = LombScargle(
        t_rel,
        y,
        dy_clean,
        nterms=2,
        center_data=True
    )

    power = ls.power(frequency)
    period_days = period_grid_hours / 24.0

    bad_periods = np.array([1.0, 0.5, 1 / 3, 0.25, 2.0])
    alias_width = 0.01
    good_mask = np.ones_like(period_days, dtype=bool)

    for bad_period in bad_periods:
        good_mask &= np.abs(period_days - bad_period) > alias_width

    period_clean = period_days[good_mask]
    power_clean = power[good_mask]

    if len(power_clean) == 0:
        return

    best_idx = np.argmax(power_clean)
    best_period = period_clean[best_idx]
    rotation_period = 2 * best_period
    best_power = power_clean[best_idx]

    try:
        fap = ls.false_alarm_probability(best_power)
    except Exception:
        fap = np.nan

    fig = make_figure((12, 5))
    ax = fig.add_subplot(111)
    ax.plot(period_clean * 24, power_clean, color="black", linewidth=1)
    ax.axvline(
        best_period * 24,
        color="red",
        linestyle="--",
        label=f"LS peak = {best_period * 24:.2f} h"
    )
    ax.axvline(
        rotation_period * 24,
        color="blue",
        linestyle="--",
        label=f"candidate rotation = {rotation_period * 24:.2f} h"
    )
    ax.set_xlabel("Period [hours]")
    ax.set_ylabel("Lomb-Scargle power")
    ax.set_title(f"Lomb-Scargle Periodogram - SSO {sso_id}")
    if np.isfinite(fap):
        ax.text(
            0.02,
            0.96,
            f"points={len(t)}, min={ANALYSIS_MIN_PERIOD_HOURS:.1f} h, FAP~{fap:.2g}",
            transform=ax.transAxes,
            ha="left",
            va="top",
            bbox={"facecolor": "white", "alpha": 0.75, "edgecolor": "none"},
        )
    ax.legend()
    ax.grid(True)
    ax.set_xscale("log")
    tick_values = [2, 4, 6, 8, 12, 24, 48]
    ax.set_xticks(tick_values, [f"{value} h" for value in tick_values])
    ax.xaxis.set_major_formatter(ScalarFormatter())
    fig.tight_layout()
    figures.append(("10 Lomb-Scargle periodogram", fig))

    if not np.isfinite(rotation_period) or rotation_period == 0:
        return

    phase_fold = ((t - t0) / rotation_period) % 1.0
    sort_idx = np.argsort(phase_fold)

    fig = make_figure((10, 5))
    ax = fig.add_subplot(111)
    ax.scatter(
        phase_fold[sort_idx],
        y[sort_idx],
        s=12,
        alpha=0.7
    )
    ax.axhline(0, color="black", linestyle="--")
    ax.invert_yaxis()
    ax.set_xlabel("Phase")
    ax.set_ylabel("Phase-corrected residual magnitude")
    ax.set_title(
        f"Phase-Folded Lightcurve - SSO {sso_id}\n"
        f"candidate P = {rotation_period * 24:.3f} h"
    )
    ax.grid(True)
    fig.tight_layout()
    figures.append(("11 Phase-folded lightcurve", fig))


# ============================================================
# Deep analysis: compute summary + in-memory figures
# ============================================================

def fmt_summary_value(value, ndigits=6, unit=""):
    try:
        value = float(value)
    except (TypeError, ValueError):
        return "n/a"

    if not np.isfinite(value):
        return "n/a"

    text = f"{value:.{ndigits}f}"

    if unit:
        text += f" {unit}"

    return text


def fmt_percent_value(value, ndigits=2):
    try:
        value = float(value)
    except (TypeError, ValueError):
        return "n/a"

    if not np.isfinite(value):
        return "n/a"

    return f"{value * 100:.{ndigits}f}%"


def classify_orbit_from_elements(a, e, q, Q):
    try:
        a = float(a)
        e = float(e)
        q = float(q)
        Q = float(Q)
    except (TypeError, ValueError):
        return "unknown"

    if not all(np.isfinite(x) for x in [a, e, q, Q]):
        return "unknown"

    if q < 1.3:
        if a < 1.0 and Q >= 0.983:
            return "Near-Earth asteroid: Aten"
        if a >= 1.0 and q <= 1.017:
            return "Near-Earth asteroid: Apollo"
        if 1.017 < q < 1.3:
            return "Near-Earth asteroid: Amor"
        if Q < 0.983:
            return "Near-Earth asteroid: Atira"

        return "Near-Earth asteroid"

    if 1.8 <= a <= 3.5 and q > 1.666:
        return "Main-belt asteroid"

    if 3.0 <= a <= 5.5 and 0.2 <= e <= 0.4:
        return "Jupiter-family / outer-belt candidate"

    if 5.0 <= a <= 5.4:
        return "Jupiter Trojan candidate"

    if a > 5.5 and q > 5.0:
        return "Distant small body candidate"

    return "small Solar System body"


def compute_tisserand_jupiter(a, e, incl_deg):
    try:
        a = float(a)
        e = float(e)
        incl_deg = float(incl_deg)
    except (TypeError, ValueError):
        return np.nan

    if not all(np.isfinite(x) for x in [a, e, incl_deg]):
        return np.nan

    if a <= 0 or e < 0 or e >= 1:
        return np.nan

    a_jupiter = 5.204
    incl_rad = math.radians(incl_deg)

    return (
        a_jupiter / a
        + 2 * math.cos(incl_rad)
        * math.sqrt((a / a_jupiter) * (1 - e ** 2))
    )


def classify_tisserand_jupiter(t_j):
    if not np.isfinite(t_j):
        return "unknown"

    if t_j > 3:
        return "asteroidal / main-belt-like"

    if 2 < t_j <= 3:
        return "Jupiter-family-comet-like"

    return "Halley-type / long-period-comet-like"


def latest_measured_position(injected_alerts):
    if not injected_alerts:
        return None

    candidates = []
    for alert in injected_alerts:
        if not isinstance(alert, dict):
            continue

        ra = to_float(alert.get("ra"))
        dec = to_float(alert.get("dec"))
        if ra is None or dec is None:
            continue

        jd = to_float(alert.get("jd"))
        received = str(alert.get("received_utc") or "")
        sort_key = jd if jd is not None else received
        candidates.append((sort_key, {"ra": ra, "dec": dec, "jd": jd, "received_utc": received}))

    if not candidates:
        return None

    return sorted(candidates, key=lambda item: item[0])[-1][1]


def append_horizons_scientific_summary(summary_lines, sso_id, measured_position=None):
    summary_lines.append("Object and Orbital Parameters")
    summary_lines.append("-" * 40)
    values = {}

    if measured_position:
        summary_lines.append(f"Last measured RA       : {fmt_summary_value(measured_position.get('ra'), 6, 'deg')}")
        summary_lines.append(f"Last measured Dec      : {fmt_summary_value(measured_position.get('dec'), 6, 'deg')}")
        if measured_position.get("received_utc"):
            summary_lines.append(f"Last measured UTC      : {fmt_utc_time(measured_position.get('received_utc'))}")

    try:
        elements = get_horizons_elements_cached(sso_id)

        a = elements["a"][0] if "a" in elements.colnames else np.nan
        e = elements["e"][0] if "e" in elements.colnames else np.nan
        incl = elements["incl"][0] if "incl" in elements.colnames else np.nan
        Omega = elements["Omega"][0] if "Omega" in elements.colnames else np.nan
        w = elements["w"][0] if "w" in elements.colnames else np.nan
        nu = elements["nu"][0] if "nu" in elements.colnames else np.nan
        q = elements["q"][0] if "q" in elements.colnames else np.nan
        Q = elements["Q"][0] if "Q" in elements.colnames else np.nan
        P = elements["P"][0] if "P" in elements.colnames else np.nan
        n = elements["n"][0] if "n" in elements.colnames else np.nan
        M = elements["M"][0] if "M" in elements.colnames else np.nan
        H = elements["H"][0] if "H" in elements.colnames else np.nan
        G = elements["G"][0] if "G" in elements.colnames else np.nan
        values.update({"H": H, "G": G})

        classification = classify_orbit_from_elements(a, e, q, Q)
        t_j = compute_tisserand_jupiter(a, e, incl)
        t_j_class = classify_tisserand_jupiter(t_j)

        summary_lines.append(f"Classification        : {classification}")
        summary_lines.append(f"Tisserand T_J         : {fmt_summary_value(t_j, 4)}")
        summary_lines.append(f"T_J interpretation    : {t_j_class}")
        summary_lines.append(f"Semi-major axis a     : {fmt_summary_value(a, 6, 'AU')}")
        summary_lines.append(f"Eccentricity e        : {fmt_summary_value(e, 6)}")
        summary_lines.append(f"Inclination i         : {fmt_summary_value(incl, 6, 'deg')}")
        summary_lines.append(f"Ascending node Omega  : {fmt_summary_value(Omega, 6, 'deg')}")
        summary_lines.append(f"Arg. perihelion omega : {fmt_summary_value(w, 6, 'deg')}")
        summary_lines.append(f"True anomaly nu       : {fmt_summary_value(nu, 6, 'deg')}")
        summary_lines.append(f"Mean anomaly M        : {fmt_summary_value(M, 6, 'deg')}")
        summary_lines.append(f"Perihelion q          : {fmt_summary_value(q, 6, 'AU')}")
        summary_lines.append(f"Aphelion Q            : {fmt_summary_value(Q, 6, 'AU')}")
        summary_lines.append(f"Orbital period        : {fmt_summary_value(P, 3, 'days')}")
        summary_lines.append(f"Mean motion n         : {fmt_summary_value(n, 8, 'deg/day')}")
        summary_lines.append(f"Absolute magnitude H  : {fmt_summary_value(H, 3)}")
        summary_lines.append(f"Slope parameter G     : {fmt_summary_value(G, 3)}")

    except Exception as exc:
        summary_lines.append(f"Could not retrieve orbital elements: {exc}")

    summary_lines.append("")
    return values


def analyze_sso_deep(sso_id, include_period_plots=False, injected_alerts=None):
    analysis_ids = resolve_analysis_ids(sso_id)
    sso_id = analysis_ids["display"]
    mpc_sso_id = analysis_ids["mpc"]
    horizons_sso_id = analysis_ids["horizons"]
    fink_sso_id = analysis_ids["fink"]

    if not sso_id:
        raise ValueError("No SSO ID provided.")

    t0 = time.perf_counter()

    figures = []
    summary_lines = []

    summary_lines.append("=" * 60)
    summary_lines.append(f"SSO {sso_id}")
    summary_lines.append("=" * 60)
    summary_lines.append("Object / Setup")
    summary_lines.append("-" * 40)
    summary_lines.append("Analysis source        : MPC + Fink history + JPL Horizons")
    summary_lines.append(f"Horizons location      : {MPC_ANALYSIS_LOCATION}")
    summary_lines.append(f"MPC start-date filter  : {MPC_ANALYSIS_START_DATE_FILTER}")
    summary_lines.append(f"Horizons grid step     : {MPC_ANALYSIS_GRID_STEP}")
    summary_lines.append("")

    horizons_sso_id = resolve_horizons_smallbody_id(
        horizons_sso_id,
        mpc_id=mpc_sso_id,
        summary_lines=summary_lines
    )

    summary_lines.append("Data Queries and Position Check")
    summary_lines.append("-" * 40)
    summary_lines.append(f"MPC query ID           : {mpc_sso_id}")
    summary_lines.append(f"Horizons query ID      : {horizons_sso_id}")
    summary_lines.append(f"Fink query ID          : {fink_sso_id}")

    orbit_summary = []
    assignment_summary = []
    mpc_summary = []
    fink_ztf_summary = []
    fink_lsst_summary = []
    with ThreadPoolExecutor(max_workers=5) as pool:
        orbit_future = pool.submit(
            append_horizons_scientific_summary,
            orbit_summary,
            horizons_sso_id,
            latest_measured_position(injected_alerts),
        )
        assignment_future = pool.submit(
            append_alert_assignment_verification,
            assignment_summary,
            horizons_sso_id,
            injected_alerts,
        )
        mpc_future = pool.submit(
            load_mpc_observations_dataframe,
            mpc_sso_id,
            mpc_summary,
        )
        fink_ztf_future = pool.submit(
            load_fink_sso_history_dataframe,
            fink_sso_id,
            FINK_ZTF_SSO_API_URL,
            "Fink/ZTF",
            fink_ztf_summary,
        )
        fink_lsst_future = pool.submit(
            load_fink_sso_history_dataframe,
            fink_sso_id,
            FINK_LSST_SSO_API_URL,
            "Fink/LSST",
            fink_lsst_summary,
        )
        mpc_df = mpc_future.result()
        fink_ztf_df = fink_ztf_future.result()
        fink_lsst_df = fink_lsst_future.result()
        orbit_values = orbit_future.result() or {}
        assignment_future.result()

    summary_lines.extend(assignment_summary)
    summary_lines.extend(orbit_summary)
    summary_lines.extend(mpc_summary)
    summary_lines.extend(fink_ztf_summary)
    summary_lines.extend(fink_lsst_summary)

    live_alert_df = build_live_alert_dataframe(
        injected_alerts=injected_alerts,
        summary_lines=summary_lines
    )

    df = combine_observation_sources(
        mpc_df,
        [fink_ztf_df, fink_lsst_df, live_alert_df],
        summary_lines
    )
    jd_obs = df["epoch"].to_numpy(dtype=float)

    summary_lines.append(f"Observations           : {len(df)}")
    summary_lines.append(f"Time range             : {df['date'].min().date()} to {df['date'].max().date()}")
    summary_lines.append("")

    summary_lines.append("Horizons Ephemerides / Geometry")
    summary_lines.append("-" * 40)

    eph_grid = load_horizons_grid_for_mpc_analysis(
        sso_id=horizons_sso_id,
        jd_obs=jd_obs,
        summary_lines=summary_lines
    )

    summary_lines.append(f"Horizons grid points   : {len(eph_grid)}")
    summary_lines.append("")

    summary_lines.append("Geometry Interpolation")
    summary_lines.append("-" * 40)

    jd_grid = eph_grid["datetime_jd"].to_numpy(dtype=float)
    r_grid = eph_grid["r"].to_numpy(dtype=float)
    delta_grid = eph_grid["delta"].to_numpy(dtype=float)
    alpha_grid = eph_grid["alpha"].to_numpy(dtype=float)

    df["r"] = np.interp(jd_obs, jd_grid, r_grid)
    df["delta"] = np.interp(jd_obs, jd_grid, delta_grid)
    df["alpha"] = np.interp(jd_obs, jd_grid, alpha_grid)

    summary_lines.append("Interpolation completed.")
    summary_lines.append("")

    summary_lines.append("Reduced Magnitude")
    summary_lines.append("-" * 40)

    df["m_red"] = (
        df["mag"]
        - 5 * np.log10(df["r"] * df["delta"])
    )

    df = df[
        np.isfinite(df["mag"]) &
        np.isfinite(df["m_red"]) &
        np.isfinite(df["alpha"]) &
        np.isfinite(df["delta"])
    ].copy()

    if len(df) == 0:
        raise RuntimeError("No valid data points remain after filtering.")

    summary_lines.append(f"Valid data points      : {len(df)}")
    summary_lines.append("")

    summary_lines.append("Phase Function Fit")
    summary_lines.append("-" * 40)

    alpha_fit = df["alpha"].to_numpy(dtype=float)
    m_red_fit = df["m_red"].to_numpy(dtype=float)
    n_unique_alpha = len(np.unique(np.round(alpha_fit, decimals=8)))
    fit_model_name = "quadratic"

    if len(df) >= 3 and n_unique_alpha >= 3:
        try:
            popt, pcov = curve_fit(
                mpc_phase_model,
                alpha_fit,
                m_red_fit,
                p0=[np.median(m_red_fit), 0.03, 0.0],
                maxfev=20000
            )
            H0, a, b = popt
        except Exception as exc:
            summary_lines.append(f"Quadratic phase fit failed; falling back to simpler fit: {exc}")
            fit_model_name = "fallback"

    else:
        fit_model_name = "fallback"

    if fit_model_name == "fallback":
        if len(df) >= 2 and n_unique_alpha >= 2:
            a, H0 = np.polyfit(alpha_fit, m_red_fit, deg=1)
            b = 0.0
            fit_model_name = "linear fallback"
        else:
            H0 = float(np.nanmedian(m_red_fit))
            a = 0.0
            b = 0.0
            fit_model_name = "constant fallback"

    df["phase_fit"] = mpc_phase_model(df["alpha"], H0, a, b)

    df["H_corr"] = (
        df["m_red"]
        - (df["phase_fit"] - H0)
    )

    df["phase_correction"] = df["phase_fit"] - H0
    df["residual_mag"] = df["m_red"] - df["phase_fit"]

    if "mag_err" not in df.columns:
        df["mag_err"] = np.nan

    mag_err = pd.to_numeric(df["mag_err"], errors="coerce").fillna(0.30)
    residual_sigma_denominator = np.sqrt(
        mag_err.to_numpy(dtype=float) ** 2
        + DEFAULT_THRESHOLDS["model_sigma"] ** 2
        + DEFAULT_THRESHOLDS["rotation_sigma"] ** 2
    )
    df["residual_sigma"] = df["residual_mag"] / residual_sigma_denominator

    residual_anomalous_mask = (
        np.isfinite(df["residual_sigma"])
        & (df["residual_sigma"] < DEFAULT_THRESHOLDS["anomaly_sigma_weak"])
    )
    residual_anomalous_entries = df[residual_anomalous_mask]
    residual_anomalous_nights = {
        jd_to_night_key(row["epoch"], row["date"])
        for _, row in residual_anomalous_entries.iterrows()
    }

    summary_lines.append(f"Phase fit ({fit_model_name}):")
    summary_lines.append(f"H0 = {H0:.4f}")
    summary_lines.append(f"a  = {a:.6f} mag/deg")
    summary_lines.append(f"b  = {b:.8f} mag/deg^2")
    summary_lines.append("")

    summary_lines.append("Phase-corrected Residual Activity")
    summary_lines.append("-" * 40)
    summary_lines.append(f"Residual sigma threshold : {DEFAULT_THRESHOLDS['anomaly_sigma_weak']:.2f}")
    summary_lines.append(f"Anomalous residuals      : {len(residual_anomalous_entries)}")
    summary_lines.append(f"Anomalous nights         : {len(residual_anomalous_nights)}")

    if len(df) > 0 and np.any(np.isfinite(df["residual_sigma"])):
        summary_lines.append(f"Best residual sigma      : {np.nanmin(df['residual_sigma']):.3f}")
        summary_lines.append(f"Median residual mag      : {np.nanmedian(df['residual_mag']):.3f}")

    summary_lines.append("")

    helio_metrics = compute_heliocentric_activity_metrics(
        df,
        sigma_threshold=DEFAULT_THRESHOLDS["anomaly_sigma_weak"],
    )

    if helio_metrics is not None:
        summary_lines.append("Heliocentric-Distance Trend")
        summary_lines.append("-" * 40)
        summary_lines.append(f"Points with r/residual  : {helio_metrics['points']}")
        summary_lines.append(
            f"Near-Sun bin             : r <= {helio_metrics['near_limit']:.2f} AU "
            f"({helio_metrics['near_count']} points)"
        )
        summary_lines.append(
            f"Far bin                  : r >= {helio_metrics['far_limit']:.2f} AU "
            f"({helio_metrics['far_count']} points)"
        )
        summary_lines.append(
            f"Near active fraction     : {fmt_percent_value(helio_metrics['near_active_fraction'])}"
        )
        summary_lines.append(
            f"Far active fraction      : {fmt_percent_value(helio_metrics['far_active_fraction'])}"
        )
        summary_lines.append(
            f"Active fraction lift     : {fmt_percent_value(helio_metrics['active_fraction_lift'])}"
        )
        summary_lines.append(
            f"Near median sigma        : {fmt_summary_value(helio_metrics['near_median_sigma'], 3)}"
        )
        summary_lines.append(
            f"Far median sigma         : {fmt_summary_value(helio_metrics['far_median_sigma'], 3)}"
        )
        summary_lines.append(
            f"Median sigma shift       : {fmt_summary_value(helio_metrics['median_sigma_shift'], 3)}"
        )
        summary_lines.append(
            f"Binned median slope      : {fmt_summary_value(helio_metrics['binned_median_slope'], 4, 'sigma/AU')}"
        )
        summary_lines.append(f"Global slope dSigma/dr  : {helio_metrics['global_slope']:.4f} sigma/AU")
        summary_lines.append(f"Global correlation       : {helio_metrics['global_corr']:.4f}")
        summary_lines.append(
            "Interpretation          : active-fraction lift and near/far median shift are usually more robust than global slope."
        )
        summary_lines.append("")

    summary_lines.append("Output Figures")
    summary_lines.append("-" * 40)

    alpha_plot = np.linspace(
        df["alpha"].min(),
        df["alpha"].max(),
        500
    )

    phase_fit_plot = mpc_phase_model(alpha_plot, H0, a, b)

    add_requested_deep_analysis_figures(
        figures=figures,
        sso_id=sso_id,
        df=df,
        alpha_plot=alpha_plot,
        phase_fit_plot=phase_fit_plot,
        H0=H0,
        H=orbit_values.get("H"),
        G=orbit_values.get("G"),
        eph_grid=eph_grid,
        include_period_plots=include_period_plots
    )

    summary_lines.append(f"Figures created        : {len(figures)}")
    summary_lines.append("")

    t1 = time.perf_counter()

    summary_lines.append("Statistics")
    summary_lines.append("-" * 40)
    summary_lines.append(f"Observed magnitude std        : {df['mag'].std():.4f}")
    summary_lines.append(f"Reduced magnitude std         : {df['m_red'].std():.4f}")
    summary_lines.append(f"Phase-corrected magnitude std : {df['H_corr'].std():.4f}")
    summary_lines.append(f"Residual magnitude std        : {df['residual_mag'].std():.4f}")
    summary_lines.append(f"Residual sigma std            : {df['residual_sigma'].std():.4f}")
    summary_lines.append(f"Final data points             : {len(df)}")
    summary_lines.append(f"Total runtime                 : {t1 - t0:.1f} s")

    summary_text = "\n".join(summary_lines)

    return {
        "sso_id": sso_id,
        "summary_text": summary_text,
        "figures": figures,
    }

CATEGORY_DEFINITIONS = [
    {
        "key": "all",
        "label": "All live alerts",
        "subtitle": "complete recent stream buffer",
        "predicate": "1=1",
    },
    {
        "key": "urgent",
        "label": "Urgent",
        "subtitle": "strong pattern, check now",
        "predicate": "activity_class = 'urgent'",
    },
    {
        "key": "interesting",
        "label": "Interesting",
        "subtitle": "credible activity candidate",
        "predicate": "activity_class IN ('urgent', 'interesting', 'good_candidate', 'weak_candidate')",
    },
    {
        "key": "review",
        "label": "Review",
        "subtitle": "one suspicious category",
        "predicate": "activity_class = 'review'",
    },
    {
        "key": "photometric",
        "label": "Photometric",
        "subtitle": "brightness anomaly / delta-mag",
        "predicate": "primary_category IN ('photometric_extreme', 'photometric_strong', 'photometric_weak', 'fallback_brightening', 'single_anomaly')",
    },
    {
        "key": "matched_lsst",
        "label": "Matched LSST SSO",
        "subtitle": "Rubin alert with MPC designation",
        "predicate": "survey = 'lsst' AND mpc_designation IS NOT NULL",
    },
    {
        "key": "unmatched_lsst",
        "label": "Unmatched LSST",
        "subtitle": "pending, ambiguous or missing MPC match",
        "predicate": "survey = 'lsst' AND mpc_designation IS NULL",
    },
    {
        "key": "persistence",
        "label": "Persistence",
        "subtitle": "repeated anomaly pattern",
        "predicate": "primary_category IN ('multi_night_activity', 'repeated_same_night')",
    },
    {
        "key": "near_snowline",
        "label": "Near snowline",
        "subtitle": "anomaly near heliocentric threshold",
        "predicate": "primary_category = 'near_snowline_activity'",
    },
    {
        "key": "contamination",
        "label": "Contamination",
        "subtitle": "likely star/galaxy/blend issue",
        "predicate": "primary_category = 'possible_contamination'",
    },
    {
        "key": "quality_rejected",
        "label": "Quality rejected",
        "subtitle": "failed hard quality gate",
        "predicate": "primary_category = 'quality_rejected' OR activity_class = 'rejected' OR rejected = 1",
    },
    {
        "key": "normal",
        "label": "Normal",
        "subtitle": "no special activity tag",
        "predicate": "coalesce(activity_class, 'normal') = 'normal'",
    },
]

CATEGORY_BY_KEY = {category["key"]: category for category in CATEGORY_DEFINITIONS}

DEFAULT_THRESHOLDS = {
    "min_interesting_score": 2,
    "max_sigmag": 0.50,
    "min_rb": 0.50,
    "min_drb": 0.50,
    "model_sigma": 0.30,
    "rotation_sigma": 0.40,
    "anomaly_sigma_weak": -3.0,
    "anomaly_sigma_strong": -5.0,
    "anomaly_sigma_extreme": -7.0,
    "delta_mag_bright": -0.2,
    "delta_mag_very_bright": -0.7,
    "delta_mag_extreme": -1.2,
    "heliocentric_near_limit_au": 2.7,
}

THRESHOLD_LABELS = {
    "min_interesting_score": "Minimum activity score for saved candidate",
    "max_sigmag": "Reject if sigmapsf >",
    "min_rb": "Reject if rb <",
    "min_drb": "Reject if drb <",
    "model_sigma": "Model uncertainty sigma",
    "rotation_sigma": "Rotation variability sigma",
    "anomaly_sigma_weak": "Weak anomaly sigma threshold",
    "anomaly_sigma_strong": "Strong anomaly sigma threshold",
    "anomaly_sigma_extreme": "Extreme anomaly sigma threshold",
    "delta_mag_bright": "Fallback bright delta_mag",
    "delta_mag_very_bright": "Fallback very bright delta_mag",
    "delta_mag_extreme": "Fallback extreme delta_mag",
    "heliocentric_near_limit_au": "Near-snowline heliocentric limit [AU]",
}

DEFAULT_ACTIVE_FILTERS = {
    "reject_bad_sigmag": True,
    "reject_nbad": True,
    "reject_low_rb": True,
    "reject_low_drb": True,
    "score_photometric_activity": True,
    "score_persistence": True,
    "score_morphology": True,
    "score_orbit_context": True,
    "score_heliocentric_trend": True,
    "apply_penalties": False,
}

FILTER_LABELS = {
    "reject_bad_sigmag": "Reject bad photometry using sigmapsf",
    "reject_nbad": "Reject problematic detections using nbad",
    "reject_low_rb": "Reject low real-bogus rb",
    "reject_low_drb": "Reject low deep-learning real-bogus drb",
    "score_photometric_activity": "Score photometric activity",
    "score_persistence": "Score object persistence",
    "score_morphology": "Score morphology / contamination placeholder",
    "score_orbit_context": "Score orbit context",
    "score_heliocentric_trend": "Score heliocentric-distance context",
    "apply_penalties": "Apply penalties",
}


COLUMNS = [
    "id",
    "sso_id",
    "mpc_designation",
    "rubin_ssobject_id",
    "sso_match_status",
    "match_method",
    "match_confidence",
    "match_separation_arcsec",
    "match_candidate_count",
    "match_checked_utc",
    "object_id",
    "received_utc",
    "received_local",
    "survey",
    "observer",
    "activity_score",
    "activity_class",
    "primary_category",
    "object_class",
    "phase_corrected_residual_sigma",
    "magpsf",
    "delta_mag",
    "anomaly_sigma",
    "main_reason",
]

LOCAL_TABLE_COLUMNS = COLUMNS
STREAM_COLUMNS = COLUMNS
STREAM_DEFAULT_VISIBLE = [
    "received_local",
    "survey",
    "activity_score",
    "primary_category",
    "object_class",
    "phase_corrected_residual_sigma",
    "sso_id",
    "object_id",
    "magpsf",
    "anomaly_sigma",
]
STREAM_THRESHOLDS = DEFAULT_THRESHOLDS

_LEGACY_GUI_PATH = Path(__file__).with_name("fink_sso_combined_gui.pre-reference-analysis.py")
_LEGACY_EXPORTS = [
    "FinkStreamWorker",
    "categorize_alerts",
    "extract_alert_fields",
    "format_value",
    "get_root_schema_columns",
    "list_parquet_files",
    "load_raw_alerts_fast",
    "flatten_alerts",
    "make_ranked_table",
    "score_alert_fields",
    "to_str_or_na",
]
if _LEGACY_GUI_PATH.exists():
    _legacy_spec = importlib.util.spec_from_file_location("_astroprak_legacy_gui", _LEGACY_GUI_PATH)
    if _legacy_spec is not None and _legacy_spec.loader is not None:
        _legacy_gui = importlib.util.module_from_spec(_legacy_spec)
        _legacy_spec.loader.exec_module(_legacy_gui)
        for _name in _LEGACY_EXPORTS:
            if _name not in globals() and hasattr(_legacy_gui, _name):
                globals()[_name] = getattr(_legacy_gui, _name)
        for _name in ("LOCAL_TABLE_COLUMNS", "STREAM_COLUMNS", "STREAM_DEFAULT_VISIBLE", "STREAM_THRESHOLDS"):
            if hasattr(_legacy_gui, _name):
                globals()[_name] = getattr(_legacy_gui, _name)

COLUMN_HEADINGS = {
    "id": "ID",
    "received_utc": "UTC time",
    "received_local": "German time",
    "survey": "survey",
    "observer": "observer",
    "activity_score": "priority",
    "activity_class": "review level",
    "primary_category": "reason category",
    "object_class": "object class",
    "phase_corrected_residual_sigma": "resid sigma",
    "sso_id": "SSO",
    "mpc_designation": "MPC designation",
    "rubin_ssobject_id": "Rubin ssObjectId",
    "sso_match_status": "SSO match",
    "match_method": "Match method",
    "match_confidence": "Confidence",
    "match_separation_arcsec": "Separation [arcsec]",
    "match_candidate_count": "MPC candidates",
    "match_checked_utc": "Match checked UTC",
    "object_id": "objectId",
    "magpsf": "mag",
    "delta_mag": "delta mag",
    "anomaly_sigma": "sigma",
    "main_reason": "main reason",
}

COLUMN_WIDTHS = {
    "id": 70,
    "received_utc": 180,
    "received_local": 180,
    "survey": 80,
    "observer": 95,
    "activity_score": 80,
    "activity_class": 130,
    "primary_category": 170,
    "object_class": 180,
    "phase_corrected_residual_sigma": 95,
    "sso_id": 120,
    "mpc_designation": 145,
    "rubin_ssobject_id": 145,
    "sso_match_status": 130,
    "match_method": 120,
    "match_confidence": 90,
    "match_separation_arcsec": 120,
    "match_candidate_count": 95,
    "match_checked_utc": 180,
    "object_id": 165,
    "magpsf": 80,
    "delta_mag": 95,
    "anomaly_sigma": 90,
    "main_reason": 700,
}


def run_ssh(command: str, timeout: int = 30) -> str:
    ssh_args = [
        "ssh",
        "-C",
        "-o",
        "BatchMode=yes",
        "-o",
        "ConnectTimeout=8",
        "-o",
        "ServerAliveInterval=5",
        "-o",
        "ServerAliveCountMax=1",
        SERVER_TARGET,
        command,
    ]
    try:
        with SSH_SEMAPHORE:
            result = subprocess.run(
                ssh_args,
                text=True,
                capture_output=True,
                timeout=timeout,
                check=False,
            )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"SSH timed out after {exc.timeout:g}s") from exc

    if result.returncode != 0:
        error = result.stderr.strip() or result.stdout.strip()
        raise RuntimeError(error or f"SSH command failed with code {result.returncode}")

    return result.stdout


def sqlite_json(sql: str, timeout: int = 30) -> list[dict]:
    timeout_seconds = max(5, int(timeout))
    command = (
        f"timeout {timeout_seconds}s "
        f"sqlite3 -readonly -cmd {shlex.quote('.timeout 5000')} "
        f"-json {shlex.quote(DB_PATH)} {shlex.quote(sql)}"
    )
    output = run_ssh(command, timeout=timeout_seconds + 5).strip()

    if not output:
        return []

    try:
        data = json.loads(output)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Server returned invalid JSON:\n{output[:1000]}") from exc

    if not isinstance(data, list):
        raise RuntimeError("Unexpected SQLite JSON response.")

    return data


def safe_sql_text(value: str) -> str:
    return value.replace("'", "''")


def fmt_float(value, digits=3) -> str:
    if value is None:
        return ""

    try:
        return f"{float(value):.{digits}f}"
    except (TypeError, ValueError):
        return str(value)


def fmt_int(value) -> str:
    try:
        return f"{int(float(value)):,}".replace(",", ".")
    except (TypeError, ValueError):
        return "0"


def parse_utc_datetime(value):
    if value is None:
        return None

    text = str(value).strip()
    if not text:
        return None

    try:
        dt = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        return None

    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)

    return dt.astimezone(timezone.utc)


def fmt_utc_time(value) -> str:
    dt = parse_utc_datetime(value)
    if dt is None:
        return str(value or "")[:19]

    return dt.strftime("%Y-%m-%d %H:%M:%S")


def fmt_german_time(value) -> str:
    dt = parse_utc_datetime(value)
    if dt is None:
        return ""

    return dt.astimezone(ZoneInfo("Europe/Berlin")).strftime("%Y-%m-%d %H:%M:%S")


def parse_systemd_timestamp(value: str):
    text = str(value or "").strip()
    if not text:
        return None

    if text.endswith(" UTC"):
        text = text[:-4]

    try:
        return datetime.strptime(text, "%a %Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def fmt_systemd_start_time(value: str) -> str:
    if "Command [" in str(value) or "timed out" in str(value).lower():
        return "stream start unknown"

    dt = parse_systemd_timestamp(value)
    if dt is None:
        return f"started: {value}" if value else "stream start unknown"

    german = dt.astimezone(ZoneInfo("Europe/Berlin")).strftime("%Y-%m-%d %H:%M:%S")
    utc = dt.strftime("%Y-%m-%d %H:%M:%S")
    return f"started: {german} DE / {utc} UTC"


def fmt_value(column: str, value) -> str:
    if value is None:
        return ""

    if column in {"magpsf", "delta_mag", "anomaly_sigma", "phase_corrected_residual_sigma"}:
        return fmt_float(value, 3)

    if column == "activity_score":
        return fmt_float(value, 0)

    if column == "received_utc":
        return fmt_utc_time(value)

    if column == "received_local":
        return fmt_german_time(value)

    return str(value)


def make_text_figure(title: str, message: str) -> Figure:
    fig = Figure(figsize=(9, 5), dpi=100)
    ax = fig.add_subplot(111)
    ax.axis("off")
    ax.set_title(title)
    ax.text(
        0.5,
        0.5,
        message,
        ha="center",
        va="center",
        wrap=True,
        transform=ax.transAxes,
    )
    fig.tight_layout()
    return fig


def first_nested_image_array(value):
    if isinstance(value, np.ndarray) and value.ndim == 2:
        return value.astype(float)

    if isinstance(value, list):
        try:
            arr = np.asarray(value, dtype=float)
            if arr.ndim == 2 and arr.size > 0:
                return arr
        except (TypeError, ValueError):
            pass
        for item in value:
            found = first_nested_image_array(item)
            if found is not None:
                return found

    if isinstance(value, dict):
        preferred = [
            "array",
            "data",
            "stampData",
            "stamp_data",
            "cutout",
            "b:cutoutScience_stampData",
            "b:cutoutTemplate_stampData",
            "b:cutoutDifference_stampData",
        ]
        for key in preferred:
            if key in value:
                found = first_nested_image_array(value[key])
                if found is not None:
                    return found
        for item in value.values():
            found = first_nested_image_array(item)
            if found is not None:
                return found

    return None


def fits_array_from_bytes(raw: bytes):
    try:
        from astropy.io import fits
    except Exception:
        return None

    try:
        with fits.open(io.BytesIO(raw), ignore_missing_simple=True) as hdul:
            for hdu in hdul:
                data = getattr(hdu, "data", None)
                if data is None:
                    continue
                arr = np.asarray(data, dtype=float)
                if arr.ndim == 2 and arr.size > 0:
                    return arr
    except Exception:
        return None

    return None


def image_array_from_cutout_response(response):
    content_type = response.headers.get("content-type", "").lower()
    raw = response.content

    if "image/" in content_type or raw[:8] == b"\x89PNG\r\n\x1a\n" or raw[:3] == b"\xff\xd8\xff":
        try:
            from PIL import Image
            image = Image.open(io.BytesIO(raw)).convert("L")
            return np.asarray(image, dtype=float)
        except Exception:
            if "image/" in content_type:
                return None

    arr = fits_array_from_bytes(raw)
    if arr is not None:
        return arr

    try:
        payload = response.json()
    except ValueError:
        payload = None

    if payload is not None:
        arr = first_nested_image_array(payload)
        if arr is not None:
            return arr

        def walk_strings(value):
            if isinstance(value, str):
                yield value
            elif isinstance(value, list):
                for item in value:
                    yield from walk_strings(item)
            elif isinstance(value, dict):
                for item in value.values():
                    yield from walk_strings(item)

        for text in walk_strings(payload):
            if len(text) < 100:
                continue
            try:
                decoded = base64.b64decode(text, validate=False)
            except Exception:
                continue
            if decoded[:2] == b"\x1f\x8b":
                try:
                    decoded = gzip.decompress(decoded)
                except Exception:
                    pass
            arr = fits_array_from_bytes(decoded)
            if arr is not None:
                return arr

    return None


def image_array_from_embedded_cutout(value):
    if value is None:
        return None

    if isinstance(value, dict):
        for key in ("stampData", "stamp_data", "data", "array", "b:stampData"):
            if key in value:
                arr = image_array_from_embedded_cutout(value[key])
                if arr is not None:
                    return arr
        return first_nested_image_array(value)

    arr = first_nested_image_array(value)
    if arr is not None:
        return arr

    if isinstance(value, str) and len(value) > 100:
        decoded = None
        if value.startswith(("b'", 'b"')):
            try:
                literal = ast.literal_eval(value)
                if isinstance(literal, bytes):
                    decoded = literal
            except (SyntaxError, ValueError):
                pass
        try:
            if decoded is None:
                decoded = base64.b64decode(value, validate=False)
        except Exception:
            return None
        if decoded[:2] == b"\x1f\x8b":
            try:
                decoded = gzip.decompress(decoded)
            except Exception:
                pass
        return fits_array_from_bytes(decoded)

    return None


def cached_fink_cutout_array(object_id, candid, kind="Science"):
    object_text = str(object_id or "").strip()
    candid_text = str(candid or "").strip()
    if not object_text or not candid_text:
        return None
    safe_kind = re.sub(r"[^A-Za-z0-9_-]+", "_", str(kind))
    cache_path = CUTOUT_HISTORY_CACHE_DIR / f"{candid_text}_{safe_kind}.npz"
    try:
        if cache_path.exists():
            with np.load(cache_path) as payload:
                array = np.asarray(payload["array"], dtype=float)
            if array.ndim == 2 and array.size:
                return array
    except Exception:
        pass

    payload = {
        "objectId": object_text,
        "candid": candid,
        "kind": kind,
        "output-format": "FITS",
    }
    try:
        response = requests.post(
            FINK_ZTF_CUTOUT_API_URL,
            json=payload,
            timeout=CUTOUT_REQUEST_TIMEOUT,
        )
        response.raise_for_status()
        array = image_array_from_cutout_response(response)
    except Exception:
        return None
    if array is None:
        return None

    try:
        CUTOUT_HISTORY_CACHE_DIR.mkdir(parents=True, exist_ok=True)
        temp_path = cache_path.with_suffix(".tmp.npz")
        np.savez_compressed(temp_path, array=np.asarray(array, dtype=np.float32))
        temp_path.replace(cache_path)
    except Exception:
        pass
    return np.asarray(array, dtype=float)


def _cached_cutout_array(cache_key, kind):
    safe_key = re.sub(r"[^A-Za-z0-9_-]+", "_", str(cache_key))
    safe_kind = re.sub(r"[^A-Za-z0-9_-]+", "_", str(kind))
    cache_path = CUTOUT_HISTORY_CACHE_DIR / f"{safe_key}_{safe_kind}.npz"
    try:
        if cache_path.exists():
            with np.load(cache_path) as payload:
                array = np.asarray(payload["array"], dtype=float)
            if array.ndim == 2 and array.size:
                return array
    except Exception:
        pass
    return None


def _store_cached_cutout_array(cache_key, kind, array):
    if array is None:
        return
    safe_key = re.sub(r"[^A-Za-z0-9_-]+", "_", str(cache_key))
    safe_kind = re.sub(r"[^A-Za-z0-9_-]+", "_", str(kind))
    cache_path = CUTOUT_HISTORY_CACHE_DIR / f"{safe_key}_{safe_kind}.npz"
    try:
        CUTOUT_HISTORY_CACHE_DIR.mkdir(parents=True, exist_ok=True)
        temp_path = cache_path.with_suffix(".tmp.npz")
        np.savez_compressed(temp_path, array=np.asarray(array, dtype=np.float32))
        temp_path.replace(cache_path)
    except Exception:
        pass


def cached_fink_cutout_triplet(row):
    source = str(row.get("survey") or row.get("observer") or "").lower()
    dia_source_id = str(
        row.get("dia_source_id") or row.get("diaSourceId") or ""
    ).strip()
    is_lsst = source == "lsst" or bool(dia_source_id)
    if is_lsst:
        if not dia_source_id:
            return {}
        cache_key = f"lsst_{dia_source_id}"
        endpoint = FINK_LSST_CUTOUT_API_URL
        payload = {
            "diaSourceId": dia_source_id,
            "kind": "All",
            "output-format": "array",
        }
        response_keys = {
            "Difference": "b:cutoutDifference",
            "Science": "b:cutoutScience",
            "Template": "b:cutoutTemplate",
        }
    else:
        object_id = str(row.get("object_id") or "").strip()
        candid = row.get("candid")
        if not object_id or candid in (None, ""):
            return {}
        cache_key = f"ztf_{candid}"
        endpoint = FINK_ZTF_CUTOUT_API_URL
        payload = {
            "objectId": object_id,
            "candid": candid,
            "kind": "All",
            "output-format": "array",
        }
        response_keys = {
            "Difference": "b:cutoutDifference_stampData",
            "Science": "b:cutoutScience_stampData",
            "Template": "b:cutoutTemplate_stampData",
        }

    arrays = {
        kind: _cached_cutout_array(cache_key, kind)
        for kind in ("Difference", "Science", "Template")
    }
    if all(array is not None for array in arrays.values()):
        return arrays
    try:
        response = requests.post(
            endpoint,
            json=payload,
            timeout=CUTOUT_REQUEST_TIMEOUT,
        )
        response.raise_for_status()
        response_data = response.json()
    except Exception:
        return {kind: array for kind, array in arrays.items() if array is not None}

    for kind, response_key in response_keys.items():
        array = image_array_from_embedded_cutout(response_data.get(response_key))
        if array is not None:
            arrays[kind] = np.asarray(array, dtype=float)
            _store_cached_cutout_array(cache_key, kind, arrays[kind])
    return {kind: array for kind, array in arrays.items() if array is not None}


def evenly_spaced_rows(rows: list[dict], limit: int) -> list[dict]:
    if limit <= 0:
        return []
    if len(rows) <= limit:
        return rows
    indices = np.linspace(0, len(rows) - 1, num=limit)
    unique_indices = sorted({int(round(index)) for index in indices})
    return [rows[index] for index in unique_indices]


def cutout_geometry_score(row: dict, reference: dict) -> float | None:
    row_candid = str(row.get("candid") or row.get("i:candid") or "").strip()
    ref_candid = str(reference.get("candid") or reference.get("i:candid") or "").strip()
    row_jd = to_float(row.get("jd") or row.get("i:jd"))
    ref_jd = to_float(reference.get("jd") or reference.get("i:jd"))
    same_alert = bool(row_candid and ref_candid and row_candid == ref_candid)
    if not same_alert and row_jd is not None and ref_jd is not None:
        same_alert = abs(row_jd - ref_jd) <= 1e-6

    row_fid = str(row.get("fid") or row.get("i:fid") or "").strip()
    ref_fid = str(reference.get("fid") or reference.get("i:fid") or "").strip()
    if row_fid and ref_fid and row_fid != ref_fid:
        return None
    if same_alert:
        return 0.0

    row_r = to_float(row.get("Dhelio"))
    row_delta = to_float(row.get("Dobs"))
    row_phase = to_float(row.get("Phase"))
    ref_r = to_float(reference.get("Dhelio"))
    ref_delta = to_float(reference.get("Dobs"))
    ref_phase = to_float(reference.get("Phase"))
    if (
        row_r is None or row_r <= 0
        or row_delta is None or row_delta <= 0
        or row_phase is None or row_phase < 0
        or ref_r is None or ref_r <= 0
        or ref_delta is None or ref_delta <= 0
        or ref_phase is None or ref_phase < 0
    ):
        return None

    r_fraction = abs(row_r - ref_r) / ref_r
    delta_fraction = abs(row_delta - ref_delta) / ref_delta
    phase_difference = abs(row_phase - ref_phase)
    phase_tolerance = max(
        CUTOUT_PHASE_MIN_TOLERANCE_DEG,
        abs(ref_phase) * CUTOUT_PHASE_REL_TOLERANCE,
    )
    if (
        r_fraction > CUTOUT_GEOMETRY_REL_TOLERANCE
        or delta_fraction > CUTOUT_GEOMETRY_REL_TOLERANCE
        or phase_difference > phase_tolerance
    ):
        return None

    return (
        r_fraction / CUTOUT_GEOMETRY_REL_TOLERANCE
        + delta_fraction / CUTOUT_GEOMETRY_REL_TOLERANCE
        + phase_difference / phase_tolerance
    )


def is_same_cutout_alert(row: dict, reference: dict) -> bool:
    row_candid = str(row.get("candid") or row.get("i:candid") or "").strip()
    ref_candid = str(reference.get("candid") or reference.get("i:candid") or "").strip()
    if row_candid and ref_candid and row_candid == ref_candid:
        return True
    row_jd = to_float(row.get("jd") or row.get("i:jd"))
    ref_jd = to_float(reference.get("jd") or reference.get("i:jd"))
    return (
        row_jd is not None
        and ref_jd is not None
        and abs(row_jd - ref_jd) <= 1e-6
    )


def select_general_cutout_epochs(
    rows: list[dict],
    reference: dict,
    limit: int = CUTOUT_HISTORY_MAX_EPOCHS,
) -> list[dict]:
    limit = max(1, int(limit))
    reference_jd = to_float(reference.get("jd") or reference.get("i:jd"))
    historical = []
    current = None
    for row in rows:
        if is_same_cutout_alert(row, reference):
            current = row
            continue
        row_jd = to_float(row.get("jd") or row.get("i:jd"))
        if (
            reference_jd is not None
            and row_jd is not None
            and row_jd > reference_jd + 1e-6
        ):
            continue
        historical.append(row)

    historical.sort(key=lambda row: (
        to_float(row.get("jd") or row.get("i:jd")) or float("inf"),
        str(row.get("received_utc") or ""),
    ))
    historical_limit = limit - 1 if current is not None else limit
    selected = evenly_spaced_rows(historical, max(0, historical_limit))
    if current is not None:
        selected.append(current)
    selected.sort(key=lambda row: (
        to_float(row.get("jd") or row.get("i:jd")) or float("inf"),
        str(row.get("received_utc") or ""),
    ))
    return selected


def merge_cutout_histories(*histories: list[dict]) -> list[dict]:
    def is_empty_value(value) -> bool:
        if value is None:
            return True
        if isinstance(value, str):
            return not value.strip()
        if isinstance(value, (list, tuple, dict, set)):
            return len(value) == 0
        return False

    merged = {}
    for history in histories:
        for row in history or []:
            candid = str(row.get("candid") or row.get("i:candid") or "").strip()
            jd = to_float(row.get("jd") or row.get("i:jd"))
            if jd is not None:
                key = ("jd", round(jd, 6))
            elif candid:
                key = ("candid", candid)
            else:
                key = (
                    "received",
                    str(row.get("received_utc") or ""),
                    str(row.get("object_id") or row.get("objectId") or ""),
                )
            existing = merged.get(key)
            if existing is None:
                merged[key] = dict(row)
                continue
            combined = dict(existing)
            for field, value in row.items():
                if is_empty_value(combined.get(field)):
                    combined[field] = value
            existing_cutouts = combined.get("alert_cutouts")
            new_cutouts = row.get("alert_cutouts")
            if isinstance(new_cutouts, dict):
                if not isinstance(existing_cutouts, dict):
                    combined["alert_cutouts"] = new_cutouts
                else:
                    cutouts = dict(existing_cutouts)
                    for kind, value in new_cutouts.items():
                        if cutouts.get(kind) is None:
                            cutouts[kind] = value
                    combined["alert_cutouts"] = cutouts
            merged[key] = combined
    return sorted(
        merged.values(),
        key=lambda row: (
            to_float(row.get("jd") or row.get("i:jd")) or float("inf"),
            str(row.get("received_utc") or ""),
        ),
    )


def normalize_fink_cutout_candidates(rows, identity) -> list[dict]:
    candidates = []
    if isinstance(rows, dict):
        rows = rows.get("records") or rows.get("data") or []
    if not isinstance(rows, list):
        return candidates
    for row in rows:
        if not isinstance(row, dict):
            continue
        object_id = row.get("i:objectId") or row.get("objectId")
        candid = row.get("i:candid") or row.get("candid")
        jd = to_float(row.get("i:jd") or row.get("jd"))
        if not object_id or candid in (None, "") or jd is None:
            continue
        try:
            received_utc = Time(
                jd,
                format="jd",
            ).to_datetime(timezone=timezone.utc).isoformat()
        except Exception:
            continue
        candidates.append({
            "received_utc": received_utc,
            "survey": "ztf",
            "observer": "ZTF",
            "object_id": str(object_id),
            "sso_id": str(identity or "").strip(),
            "candid": candid,
            "jd": jd,
            "fid": row.get("i:fid") or row.get("fid"),
            "magpsf": to_float(row.get("i:magpsf") or row.get("magpsf")),
            "sigmapsf": to_float(row.get("i:sigmapsf") or row.get("sigmapsf")),
            "Dhelio": to_float(row.get("Dhelio") or row.get("r")),
            "Dobs": to_float(row.get("Dobs") or row.get("delta")),
            "Phase": to_float(row.get("Phase") or row.get("alpha")),
            "magpsf_red": to_float(
                row.get("i:magpsf_red") or row.get("magpsf_red")
            ),
        })
    return sorted(candidates, key=lambda row: row["jd"])


def normalize_fink_lsst_cutout_candidates(rows, identity) -> list[dict]:
    candidates = []
    if isinstance(rows, dict):
        rows = rows.get("records") or rows.get("data") or []
    if not isinstance(rows, list):
        return candidates
    for row in rows:
        if not isinstance(row, dict):
            continue
        dia_source_id = row.get("r:diaSourceId") or row.get("diaSourceId")
        mjd = to_float(
            row.get("r:midpointMjdTai") or row.get("midpointMjdTai")
        )
        if dia_source_id in (None, "") or mjd is None:
            continue
        try:
            observed = Time(mjd, format="mjd", scale="tai")
            received_utc = observed.utc.to_datetime(
                timezone=timezone.utc
            ).isoformat()
            jd = float(observed.utc.jd)
        except Exception:
            continue
        flux = to_float(row.get("r:psfFlux") or row.get("psfFlux"))
        flux_error = to_float(
            row.get("r:psfFluxErr") or row.get("psfFluxErr")
        )
        magnitude = (
            31.4 - 2.5 * float(np.log10(flux))
            if flux is not None and flux > 0
            else None
        )
        magnitude_error = (
            2.5 * flux_error / (flux * float(np.log(10)))
            if (
                flux is not None
                and flux > 0
                and flux_error is not None
                and flux_error >= 0
            )
            else None
        )
        candidates.append({
            "received_utc": received_utc,
            "survey": "lsst",
            "observer": "LSST",
            "object_id": str(row.get("r:diaObjectId") or "0"),
            "dia_source_id": str(dia_source_id),
            "sso_id": str(identity or "").strip(),
            "jd": jd,
            "fid": row.get("r:band") or row.get("band"),
            "magpsf": magnitude,
            "sigmapsf": magnitude_error,
        })
    return sorted(candidates, key=lambda row: row["jd"])


def load_cutouts_for_candidates(candidates: list[dict]) -> list[dict]:
    candidates = merge_cutout_histories(candidates)
    if not candidates:
        return []

    cutout_sets = {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {
            pool.submit(
                cached_fink_cutout_triplet,
                row,
            ): index
            for index, row in enumerate(candidates)
            if (
                row.get("dia_source_id")
                or (
                    row.get("object_id")
                    and row.get("candid") not in (None, "")
                )
            )
        }
        for future, index in futures.items():
            try:
                cutout_sets[index] = future.result()
            except Exception:
                cutout_sets[index] = {}

    successful = [
        index for index, arrays in cutout_sets.items()
        if arrays.get("Science") is not None
    ]
    loaded = []
    for index in successful:
        row = dict(candidates[index])
        row["alert_cutouts"] = cutout_sets[index]
        loaded.append(row)
    return loaded


def fetch_fink_lsst_cutout_candidates(sso_id: str) -> list[dict]:
    identity = str(sso_id or "").strip()
    if not identity:
        return []
    try:
        response = requests.post(
            FINK_LSST_SSO_API_URL,
            json={
                "n_or_d": identity,
                "columns": (
                    "r:diaSourceId,r:midpointMjdTai,r:band,"
                    "r:psfFlux,r:psfFluxErr"
                ),
                "output-format": "json",
            },
            timeout=FINK_HISTORY_TIMEOUT,
        )
        response.raise_for_status()
        return normalize_fink_lsst_cutout_candidates(
            response.json(),
            identity,
        )
    except Exception:
        return []


def fetch_fink_cutout_candidates(
    sso_id: str = "",
    object_id: str = "",
) -> list[dict]:
    sso_text = str(sso_id or "").strip()
    object_text = str(object_id or "").strip()
    requests_to_try = []
    if sso_text:
        requests_to_try.append((
            FINK_ZTF_SSO_API_URL,
            build_fink_sso_payload(
                sso_text,
                with_ephem=True,
                with_residuals=False,
            ),
            sso_text,
        ))
    if object_text:
        requests_to_try.append((
            FINK_ZTF_OBJECT_API_URL,
            {"objectId": object_text, "output-format": "json"},
            sso_text or object_text,
        ))
    for url, payload, identity in requests_to_try:
        try:
            if url == FINK_ZTF_SSO_API_URL and sso_text:
                status_code, content, _from_cache = fetch_fink_history_response(
                    url,
                    sso_text,
                )
                if status_code == 404:
                    continue
                raw_rows = json.loads(content.decode("utf-8"))
            else:
                response = requests.post(
                    url,
                    json=payload,
                    timeout=FINK_HISTORY_TIMEOUT,
                )
                response.raise_for_status()
                raw_rows = response.json()
            candidates = normalize_fink_cutout_candidates(
                raw_rows,
                identity,
            )
            if candidates:
                return candidates
        except Exception:
            continue
    return []


def select_general_with_required(
    loaded_rows: list[dict],
    required_rows: list[dict],
    reference: dict,
    limit: int = CUTOUT_GENERAL_MAX_EPOCHS,
) -> list[dict]:
    required = merge_cutout_histories(required_rows)
    required_keys = {
        (
            round(to_float(row.get("jd")) or -1.0, 6),
            str(row.get("candid") or ""),
        )
        for row in required
    }
    extras = [
        row for row in merge_cutout_histories(loaded_rows)
        if (
            round(to_float(row.get("jd")) or -1.0, 6),
            str(row.get("candid") or ""),
        ) not in required_keys
    ]
    extra_limit = max(0, int(limit) - len(required))
    selected_extras = select_general_cutout_epochs(
        extras,
        reference,
        extra_limit,
    )
    return sorted(
        merge_cutout_histories(required, selected_extras),
        key=lambda row: (
            to_float(row.get("jd")) or float("inf"),
            str(row.get("received_utc") or ""),
        ),
    )


def select_cutout_geometry_matches(
    rows: list[dict],
    reference: dict,
    limit: int = CUTOUT_HISTORY_MAX_EPOCHS,
) -> list[dict]:
    reference_jd = to_float(reference.get("jd"))
    scored = []
    for row in rows:
        row_jd = to_float(row.get("jd"))
        if (
            reference_jd is not None
            and row_jd is not None
            and row_jd > reference_jd + 1e-6
        ):
            continue
        score = cutout_geometry_score(row, reference)
        if score is not None:
            scored.append((score, row))

    scored.sort(key=lambda item: (
        item[0],
        -(to_float(item[1].get("jd")) or 0.0),
    ))
    selected = [row for _score, row in scored[:max(1, int(limit))]]
    selected.sort(key=lambda row: (
        to_float(row.get("jd")) or float("inf"),
        str(row.get("received_utc") or ""),
    ))
    return selected


def build_fink_cutout_history(
    rows,
    identity,
    max_epochs=CUTOUT_HISTORY_MAX_EPOCHS,
    reference=None,
):
    if not isinstance(rows, list):
        return []

    candidates = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        object_id = row.get("i:objectId") or row.get("objectId")
        candid = row.get("i:candid") or row.get("candid")
        jd = to_float(row.get("i:jd") or row.get("jd"))
        if not object_id or candid in (None, "") or jd is None:
            continue
        candidates.append({
            "received_utc": Time(jd, format="jd").to_datetime(timezone=timezone.utc).isoformat(),
            "object_id": str(object_id),
            "sso_id": str(identity or "").strip(),
            "candid": candid,
            "jd": jd,
            "fid": row.get("i:fid") or row.get("fid"),
            "magpsf": to_float(row.get("i:magpsf") or row.get("magpsf")),
            "sigmapsf": to_float(row.get("i:sigmapsf") or row.get("sigmapsf")),
            "Dhelio": to_float(row.get("Dhelio") or row.get("r")),
            "Dobs": to_float(row.get("Dobs") or row.get("delta")),
            "Phase": to_float(row.get("Phase") or row.get("alpha")),
            "magpsf_red": to_float(row.get("i:magpsf_red") or row.get("magpsf_red")),
        })
    candidates.sort(key=lambda row: row["jd"])
    if isinstance(reference, dict):
        matching_pool_size = min(
            len(candidates),
            max(int(max_epochs) * 4, int(max_epochs)),
        )
        selected = select_cutout_geometry_matches(
            candidates,
            reference,
            max(1, matching_pool_size),
        )
    else:
        target_count = max(1, int(max_epochs))
        cached_candidates = []
        for row in candidates:
            candid_text = str(row.get("candid") or "").strip()
            if not candid_text:
                continue
            science_cache = CUTOUT_HISTORY_CACHE_DIR / f"{candid_text}_Science.npz"
            if science_cache.exists():
                cached_candidates.append(row)
        candidate_pool = evenly_spaced_rows(
            candidates,
            min(len(candidates), max(target_count * 3, target_count)),
        )
        pooled = {}
        for row in cached_candidates + candidate_pool:
            pooled[str(row.get("candid"))] = row
        selected = sorted(
            pooled.values(),
            key=lambda row: row["jd"],
        )
    arrays = {}
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = {}
        for index, row in enumerate(selected):
            for kind in ("Science", "Difference"):
                future = pool.submit(
                    cached_fink_cutout_array,
                    row["object_id"],
                    row["candid"],
                    kind,
                )
                futures[future] = (index, kind)
        for future, key in futures.items():
            try:
                arrays[key] = future.result()
            except Exception:
                arrays[key] = None

    history = []
    for index, row in enumerate(selected):
        science = arrays.get((index, "Science"))
        if science is None:
            continue
        difference = arrays.get((index, "Difference"))
        row["alert_cutouts"] = {
            "Science": science,
            "Difference": difference,
        }
        history.append(row)
    if isinstance(reference, dict):
        history = select_cutout_geometry_matches(
            history,
            reference,
            max(1, int(max_epochs)),
        )
    else:
        history = evenly_spaced_rows(
            history,
            max(1, int(max_epochs)),
        )
    return history


def load_fink_ztf_cutout_history(
    sso_id,
    max_epochs=CUTOUT_HISTORY_MAX_EPOCHS,
    reference=None,
):
    sso_text = str(sso_id or "").strip()
    if not sso_text:
        return []
    try:
        response = requests.post(
            FINK_ZTF_SSO_API_URL,
            json=build_fink_sso_payload(sso_text, with_ephem=True, with_residuals=False),
            timeout=FINK_HISTORY_TIMEOUT,
        )
        response.raise_for_status()
        rows = response.json()
    except Exception:
        return []
    return build_fink_cutout_history(
        rows,
        sso_text,
        max_epochs,
        reference=reference,
    )


def load_fink_ztf_object_cutout_history(
    object_id,
    max_epochs=CUTOUT_HISTORY_MAX_EPOCHS,
    reference=None,
):
    object_text = str(object_id or "").strip()
    if not object_text:
        return []
    try:
        response = requests.post(
            FINK_ZTF_OBJECT_API_URL,
            json={"objectId": object_text, "output-format": "json"},
            timeout=FINK_HISTORY_TIMEOUT,
        )
        response.raise_for_status()
        rows = response.json()
    except Exception:
        return []
    return build_fink_cutout_history(
        rows,
        object_text,
        max_epochs,
        reference=reference,
    )


def enrich_cutout_history_with_horizons(sso_id, history):
    missing_rows = [
        row for row in history
        if to_float(row.get("jd")) is not None
        and (
            to_float(row.get("Dhelio")) is None
            or to_float(row.get("Dobs")) is None
            or to_float(row.get("Phase")) is None
        )
    ]
    if not missing_rows:
        return history
    try:
        analysis_ids = resolve_analysis_ids(sso_id)
        horizons_id = resolve_horizons_smallbody_id(
            analysis_ids["horizons"],
            mpc_id=analysis_ids["mpc"],
        )
        epochs = [float(row["jd"]) for row in missing_rows]
        ephemerides = Horizons(
            id=horizons_id,
            id_type="smallbody",
            location=MPC_ANALYSIS_LOCATION,
            epochs=epochs,
        ).ephemerides(quantities="19,20,24", cache=True)
        r_values = get_horizons_column(ephemerides, ["r"])
        delta_values = get_horizons_column(ephemerides, ["delta"])
        phase_values = get_horizons_column(ephemerides, ["alpha", "S-T-O", "STO", "phi"])
        for row, r_au, delta_au, phase_deg in zip(
            missing_rows,
            r_values,
            delta_values,
            phase_values,
        ):
            row["Dhelio"] = float(r_au)
            row["Dobs"] = float(delta_au)
            row["Phase"] = float(phase_deg)
    except Exception:
        pass
    return history


def build_alert_cutout_figure(alert: dict) -> tuple[str, Figure] | None:
    object_id = str(
        alert.get("object_id")
        or alert.get("objectId")
        or alert.get("i:objectId")
        or ""
    ).strip()

    if not object_id:
        return None

    candid = (
        alert.get("candid")
        or alert.get("i:candid")
        or alert.get("candidate.candid")
    )

    if not object_id.upper().startswith("ZTF"):
        fig = make_text_figure(
            "Alert cutouts",
            f"No automatic cutout request for objectId={object_id}.\n"
            "The current cutout helper is configured for ZTF/Fink cutouts.",
        )
        return "01 Alert cutouts", fig

    embedded_cutouts = alert.get("alert_cutouts")
    if isinstance(embedded_cutouts, dict):
        cutouts = [
            (kind, image_array_from_embedded_cutout(embedded_cutouts.get(kind)))
            for kind in ("Science", "Template", "Difference")
        ]
        if any(arr is not None for _kind, arr in cutouts):
            fig = Figure(figsize=(11, 4), dpi=100)
            for idx, (kind, arr) in enumerate(cutouts, start=1):
                ax = fig.add_subplot(1, 3, idx)
                ax.set_title(kind)
                ax.axis("off")
                if arr is None:
                    ax.text(0.5, 0.5, "not available", ha="center", va="center", transform=ax.transAxes)
                    continue
                finite = arr[np.isfinite(arr)]
                if finite.size:
                    vmin, vmax = np.percentile(finite, [1, 99])
                else:
                    vmin, vmax = None, None
                ax.imshow(arr, cmap="gray", origin="lower", vmin=vmin, vmax=vmax)
                add_cutout_angular_scale(
                    ax,
                    arr.shape,
                    ZTF_PIXEL_SCALE_ARCSEC,
                )
            fig.suptitle(f"Embedded live-alert cutouts - {object_id}")
            fig.tight_layout()
            return "01 Alert cutouts", fig

    cutouts = []
    errors = []
    for kind in ("Science", "Template", "Difference"):
        payload_variants = []
        if candid not in (None, ""):
            payload_variants.append({"objectId": object_id, "kind": kind, "candid": candid})
        payload_variants.extend([
            {"objectId": object_id, "kind": kind},
            {"objectId": object_id, "kind": kind, "output-format": "array"},
            {"objectId": object_id, "kind": kind, "output-format": "FITS"},
        ])
        arr = None
        for payload in payload_variants:
            try:
                response = requests.post(
                    FINK_ZTF_CUTOUT_API_URL,
                    json=payload,
                    timeout=18,
                )
                response.raise_for_status()
                arr = image_array_from_cutout_response(response)
            except Exception as exc:
                if len(errors) < 6:
                    errors.append(f"{kind}: {exc}")
                arr = None
            if arr is not None:
                break
        cutouts.append((kind, arr))

    if not any(arr is not None for _kind, arr in cutouts):
        fig = make_text_figure(
            "Alert cutouts",
            f"No cutout image available for {object_id}.\n"
            "For very fresh live alerts the Fink image API can lag behind the stream.\n"
            + "\n".join(errors[-4:]),
        )
        return "01 Alert cutouts", fig

    fig = Figure(figsize=(11, 4), dpi=100)
    for idx, (kind, arr) in enumerate(cutouts, start=1):
        ax = fig.add_subplot(1, 3, idx)
        ax.set_title(kind)
        ax.axis("off")
        if arr is None:
            ax.text(0.5, 0.5, "not available", ha="center", va="center", transform=ax.transAxes)
            continue
        finite = arr[np.isfinite(arr)]
        if finite.size:
            vmin, vmax = np.percentile(finite, [1, 99])
        else:
            vmin, vmax = None, None
        ax.imshow(arr, cmap="gray", origin="lower", vmin=vmin, vmax=vmax)
        add_cutout_angular_scale(
            ax,
            arr.shape,
            ZTF_PIXEL_SCALE_ARCSEC,
        )
    fig.suptitle(f"Selected alert cutouts - {object_id}")
    fig.tight_layout()
    return "01 Alert cutouts", fig


def ensure_alert_cutouts_for_history(alert: dict) -> None:
    embedded = alert.get("alert_cutouts")
    if isinstance(embedded, dict):
        science = image_array_from_embedded_cutout(embedded.get("Science"))
        if science is not None:
            return

    object_id = str(
        alert.get("object_id")
        or alert.get("objectId")
        or alert.get("i:objectId")
        or ""
    ).strip()
    candid = (
        alert.get("candid")
        or alert.get("i:candid")
        or alert.get("candidate.candid")
    )
    if not object_id or candid in (None, ""):
        return

    science = cached_fink_cutout_array(object_id, candid, "Science")
    if science is None:
        return
    difference = cached_fink_cutout_array(object_id, candid, "Difference")
    alert["alert_cutouts"] = {
        "Science": science,
        "Difference": difference,
    }


def shift_image_without_wrap(image: np.ndarray, shift_y: int, shift_x: int) -> np.ndarray:
    result = np.full_like(image, np.nan, dtype=float)
    height, width = image.shape
    source_y0 = max(0, -shift_y)
    source_y1 = min(height, height - shift_y)
    source_x0 = max(0, -shift_x)
    source_x1 = min(width, width - shift_x)
    target_y0 = max(0, shift_y)
    target_y1 = min(height, height + shift_y)
    target_x0 = max(0, shift_x)
    target_x1 = min(width, width + shift_x)
    if source_y1 > source_y0 and source_x1 > source_x0:
        result[target_y0:target_y1, target_x0:target_x1] = image[
            source_y0:source_y1,
            source_x0:source_x1,
        ]
    return result


def center_cutout_pair(science: np.ndarray, difference: np.ndarray | None):
    reference = difference if difference is not None else science
    height, width = reference.shape
    half_window = max(5, min(height, width) // 5)
    center_y = height // 2
    center_x = width // 2
    y0, y1 = max(0, center_y - half_window), min(height, center_y + half_window + 1)
    x0, x1 = max(0, center_x - half_window), min(width, center_x + half_window + 1)
    window = np.asarray(reference[y0:y1, x0:x1], dtype=float)
    finite = np.isfinite(window)
    if not finite.any():
        return science, difference
    background = float(np.nanmedian(window))
    signal = np.where(finite, window - background, -np.inf)
    peak_y, peak_x = np.unravel_index(np.nanargmax(signal), signal.shape)
    shift_y = center_y - (y0 + int(peak_y))
    shift_x = center_x - (x0 + int(peak_x))
    if abs(shift_y) > half_window or abs(shift_x) > half_window:
        return science, difference
    centered_science = shift_image_without_wrap(science, shift_y, shift_x)
    centered_difference = (
        shift_image_without_wrap(difference, shift_y, shift_x)
        if difference is not None
        else None
    )
    return centered_science, centered_difference


def cutout_pixel_scale_arcsec(row=None):
    if isinstance(row, dict):
        for key in (
            "pixel_scale_arcsec",
            "pixelScaleArcsec",
            "arcsec_per_pixel",
        ):
            value = to_float(row.get(key))
            if value is not None and value > 0:
                return value
    # Sandbox7 obtains these evolution images from the Fink/ZTF cutout API.
    return ZTF_PIXEL_SCALE_ARCSEC


def add_cutout_angular_scale(
    ax,
    image_shape,
    pixel_scale_arcsec,
    bar_arcsec=CUTOUT_SCALE_BAR_ARCSEC,
):
    if (
        pixel_scale_arcsec is None
        or pixel_scale_arcsec <= 0
        or not image_shape
    ):
        return
    height, width = image_shape
    bar_pixels = float(bar_arcsec) / float(pixel_scale_arcsec)
    bar_pixels = min(bar_pixels, width * 0.42)
    displayed_arcsec = bar_pixels * float(pixel_scale_arcsec)
    x0 = width * 0.08
    y0 = height * 0.09
    ax.plot(
        [x0, x0 + bar_pixels],
        [y0, y0],
        color="white",
        linewidth=2.2,
        solid_capstyle="butt",
        path_effects=None,
        zorder=20,
    )
    ax.text(
        x0 + bar_pixels / 2.0,
        y0 + height * 0.035,
        f'{displayed_arcsec:.0f}"',
        color="white",
        fontsize=7,
        ha="center",
        va="bottom",
        zorder=20,
        bbox={
            "facecolor": "black",
            "edgecolor": "none",
            "alpha": 0.45,
            "pad": 1.0,
        },
    )


def build_cutout_evolution_figure(
    history: list[dict],
    reference: dict | None = None,
    similar_parameters: bool = False,
) -> tuple[str, Figure] | None:
    if similar_parameters and isinstance(reference, dict):
        history = select_cutout_geometry_matches(
            history,
            reference,
            CUTOUT_HISTORY_MAX_EPOCHS,
        )
    plot_name = (
        "03 Cutout evolution - similar parameters"
        if similar_parameters
        else "02 Cutout evolution"
    )
    plot_title = (
        "Cutout evolution - similar parameters"
        if similar_parameters
        else "Cutout evolution"
    )
    epochs = []
    for row in history:
        cutouts = row.get("alert_cutouts")
        if not isinstance(cutouts, dict):
            continue
        science = image_array_from_embedded_cutout(cutouts.get("Science"))
        difference = image_array_from_embedded_cutout(cutouts.get("Difference"))
        if science is None:
            continue
        if difference is not None and difference.shape != science.shape:
            difference = None
        science, difference = center_cutout_pair(science, difference)
        epochs.append({**row, "science_array": science, "difference_array": difference})

    if not epochs:
        return (
            plot_name,
            make_text_figure(
                plot_title,
                "The selected alert has no loadable Science cutout yet.\n"
                "The plot will appear when the embedded image or Fink cutout API is available.",
            ),
        )

    epochs.sort(key=lambda row: (to_float(row.get("jd")) or float("inf"), str(row.get("received_utc") or "")))
    shape_counts = {}
    for row in epochs:
        shape = row["science_array"].shape
        shape_counts[shape] = shape_counts.get(shape, 0) + 1
    common_shape = max(shape_counts, key=shape_counts.get)
    epochs = [row for row in epochs if row["science_array"].shape == common_shape]
    display_limit = (
        CUTOUT_HISTORY_MAX_EPOCHS
        if similar_parameters
        else CUTOUT_GENERAL_MAX_EPOCHS
    )
    epochs = epochs[-display_limit:]
    if not epochs:
        return (
            plot_name,
            make_text_figure(
                plot_title,
                "Cutouts were found, but none share a compatible image shape.",
            ),
        )

    science_chunks = [
        row["science_array"][np.isfinite(row["science_array"])]
        for row in epochs
        if np.isfinite(row["science_array"]).any()
    ]
    if not science_chunks:
        return (
            plot_name,
            make_text_figure(
                plot_title,
                "Cutout arrays contain no finite Science pixels.",
            ),
        )
    science_display_arrays = [
        row["science_array"] - float(np.nanmedian(row["science_array"]))
        for row in epochs
    ]
    science_values = np.concatenate([
        array[np.isfinite(array)]
        for array in science_display_arrays
        if np.isfinite(array).any()
    ])
    science_vmin, science_vmax = np.percentile(science_values, [1, 99.7])

    columns = len(epochs)
    first_mag = to_float(epochs[0].get("magpsf"))
    object_label = epochs[-1].get("sso_id") or epochs[-1].get("object_id") or "selected object"
    if columns == 1:
        row = epochs[0]
        fig = Figure(figsize=(9, 6.6), dpi=100)
        fig._astroprak_preserve_layout = True
        ax = fig.add_subplot(111)
        ax.imshow(
            science_display_arrays[0],
            cmap="gray",
            origin="lower",
            vmin=science_vmin,
            vmax=science_vmax,
        )
        center_y, center_x = np.array(row["science_array"].shape) / 2.0
        ax.add_patch(Circle(
            (center_x - 0.5, center_y - 0.5),
            radius=5,
            fill=False,
            edgecolor="#22d3ee",
            linewidth=1.4,
        ))
        pixel_scale = cutout_pixel_scale_arcsec(row)
        add_cutout_angular_scale(
            ax,
            row["science_array"].shape,
            pixel_scale,
        )
        timestamp = fmt_german_time(row.get("received_utc"))
        filter_label = str(row.get("fid") or "?")
        current_mag = to_float(row.get("magpsf"))
        title = f"{timestamp} | filter {filter_label}"
        if current_mag is not None:
            title += f" | mag {current_mag:.3f}"
        r_au = to_float(row.get("Dhelio"))
        delta_au = to_float(row.get("Dobs"))
        phase_deg = to_float(row.get("Phase"))
        if r_au is not None or delta_au is not None:
            distances = []
            if r_au is not None:
                distances.append(f"Sonne {r_au:.2f} AU")
            if delta_au is not None:
                distances.append(f"Erde {delta_au:.2f} AU")
            title += "\n" + " | ".join(distances)
        if phase_deg is not None:
            title += f"\nPhase {phase_deg:.1f} deg"
        if similar_parameters and isinstance(reference, dict):
            ref_r = to_float(reference.get("Dhelio"))
            ref_delta = to_float(reference.get("Dobs"))
            ref_phase = to_float(reference.get("Phase"))
            deviations = []
            if r_au is not None and ref_r is not None and ref_r > 0:
                deviations.append(f"Î”Sonne {(r_au - ref_r) / ref_r * 100:+.1f}%")
            if delta_au is not None and ref_delta is not None and ref_delta > 0:
                deviations.append(f"Î”Erde {(delta_au - ref_delta) / ref_delta * 100:+.1f}%")
            if phase_deg is not None and ref_phase is not None:
                deviations.append(f"Î”Phase {phase_deg - ref_phase:+.1f}Â°")
            if deviations:
                title += "\n" + " | ".join(deviations)
        ax.set_title(title, fontsize=10, pad=10)
        ax.axis("off")
        fig.suptitle(f"{plot_title}: {object_label}", fontsize=12, y=0.98)
        fig.text(
            0.5,
            0.925,
            (
                "No earlier cutout with matching filter, distances, and phase angle is currently available."
                if similar_parameters
                else "Only one cutout epoch is currently available."
            ),
            ha="center",
            va="top",
            fontsize=9,
        )
        fig.subplots_adjust(left=0.12, right=0.88, bottom=0.06, top=0.82)
        return plot_name, fig

    difference_arrays = []
    for row in epochs:
        difference = row.get("difference_array")
        if difference is None:
            difference = row["science_array"] - float(np.nanmedian(row["science_array"]))
        difference_arrays.append(difference)
    residual_chunks = [
        np.abs(array[np.isfinite(array)])
        for array in difference_arrays
        if np.isfinite(array).any()
    ]
    residual_values = np.concatenate(residual_chunks) if residual_chunks else np.array([])
    residual_limit = float(np.percentile(residual_values, 99)) if residual_values.size else 1.0
    residual_limit = max(residual_limit, 1e-6)

    fig = Figure(figsize=(max(11, 2.45 * columns), 5.9), dpi=100)
    fig._astroprak_preserve_layout = True
    grid = fig.add_gridspec(
        2,
        columns,
        height_ratios=(1.0, 1.0),
        hspace=0.10,
        wspace=0.10,
    )
    science_axes = []
    difference_axes = []
    science_image = None
    difference_image = None
    for index, (row, science_display, difference_display) in enumerate(
        zip(epochs, science_display_arrays, difference_arrays)
    ):
        science_ax = fig.add_subplot(grid[0, index])
        science_axes.append(science_ax)
        science_image = science_ax.imshow(
            science_display,
            cmap="gray",
            origin="lower",
            vmin=science_vmin,
            vmax=science_vmax,
        )
        center_y, center_x = np.array(row["science_array"].shape) / 2.0
        science_ax.add_patch(Circle(
            (center_x - 0.5, center_y - 0.5),
            radius=5,
            fill=False,
            edgecolor="#22d3ee",
            linewidth=1.3,
        ))
        pixel_scale = cutout_pixel_scale_arcsec(row)
        add_cutout_angular_scale(
            science_ax,
            row["science_array"].shape,
            pixel_scale,
        )
        current_mag = to_float(row.get("magpsf"))
        delta_mag = current_mag - first_mag if current_mag is not None and first_mag is not None else None
        timestamp = fmt_german_time(row.get("received_utc"))
        filter_label = str(row.get("fid") or "?")
        r_au = to_float(row.get("Dhelio"))
        delta_au = to_float(row.get("Dobs"))
        phase_deg = to_float(row.get("Phase"))
        parsed_time = parse_utc_datetime(row.get("received_utc"))
        short_date = (
            parsed_time.astimezone(ZoneInfo("Europe/Berlin")).strftime("%d.%m.%y")
            if parsed_time
            else timestamp[:10]
        )
        title = f"{short_date} | Filter {filter_label}"
        if current_mag is not None:
            title += f"\nMag {current_mag:.2f}"
        if delta_mag is not None:
            title += f" | Ã„nderung {delta_mag:+.2f}"
        distances = []
        if r_au is not None:
            distances.append(f"Sonne {r_au:.2f}")
        if delta_au is not None:
            distances.append(f"Erde {delta_au:.2f}")
        if distances:
            title += "\n" + " | ".join(distances) + " AU"
        if phase_deg is not None:
            title += f"\nPhase {phase_deg:.1f} deg"
        if similar_parameters and isinstance(reference, dict):
            ref_r = to_float(reference.get("Dhelio"))
            ref_delta = to_float(reference.get("Dobs"))
            ref_phase = to_float(reference.get("Phase"))
            deviations = []
            if r_au is not None and ref_r is not None and ref_r > 0:
                deviations.append(f"Î”S {(r_au - ref_r) / ref_r * 100:+.0f}%")
            if delta_au is not None and ref_delta is not None and ref_delta > 0:
                deviations.append(f"Î”E {(delta_au - ref_delta) / ref_delta * 100:+.0f}%")
            if phase_deg is not None and ref_phase is not None:
                deviations.append(f"Î”P {phase_deg - ref_phase:+.1f}Â°")
            if deviations:
                title += "\n" + " | ".join(deviations)
        science_ax.set_title(title, fontsize=5.8, rotation=0, pad=7, ha="center")
        science_ax.axis("off")

        difference_ax = fig.add_subplot(grid[1, index])
        difference_axes.append(difference_ax)
        difference_image = difference_ax.imshow(
            difference_display,
            cmap="coolwarm",
            origin="lower",
            vmin=-residual_limit,
            vmax=residual_limit,
        )
        difference_ax.axhline(center_y - 0.5, color="white", alpha=0.25, linewidth=0.6)
        difference_ax.axvline(center_x - 0.5, color="white", alpha=0.25, linewidth=0.6)
        add_cutout_angular_scale(
            difference_ax,
            difference_display.shape,
            pixel_scale,
        )
        difference_ax.axis("off")

    if science_image is not None:
        science_cax = fig.add_axes([0.925, 0.535, 0.009, 0.245])
        science_cbar = fig.colorbar(
            science_image, cax=science_cax, orientation="vertical",
        )
        science_cbar.set_label("Science [ADU]", fontsize=7)
        science_cbar.ax.tick_params(labelsize=7)
    if difference_image is not None:
        difference_cax = fig.add_axes([0.925, 0.14, 0.009, 0.245])
        difference_cbar = fig.colorbar(
            difference_image, cax=difference_cax, orientation="vertical",
        )
        difference_cbar.set_label("Difference [ADU]", fontsize=7)
        difference_cbar.ax.tick_params(labelsize=7)

    fig.suptitle(f"{plot_title}: {object_label}", fontsize=12, y=0.99)
    fig.text(
        0.5,
        0.945,
        (
            "Nur gleicher Filter sowie Ã¤hnliche Sonnen-/Erddistanz (Â±50 %) und Phase (Â±50 %, mindestens Â±1Â°)."
            if similar_parameters
            else "Zeitlich verteilte Cutout-Epochen; Bahngeometrie und Filter dÃ¼rfen unterschiedlich sein."
        ),
        ha="center",
        va="top",
        fontsize=9,
    )
    field_width_arcsec = common_shape[1] * cutout_pixel_scale_arcsec(
        epochs[-1]
    )
    fig.text(
        0.5,
        0.915,
        (
            f'WeiÃŸe Skala: {CUTOUT_SCALE_BAR_ARCSEC:.0f}" Â· '
            f'Bildbreite etwa {field_width_arcsec:.0f}" '
            f'({cutout_pixel_scale_arcsec(epochs[-1]):.2f}"/Pixel)'
        ),
        ha="center",
        va="top",
        fontsize=8,
    )
    fig.subplots_adjust(left=0.035, right=0.90, bottom=0.07, top=0.80)
    return plot_name, fig


class ServerAlertDashboard:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("AstroPrak Server Dashboard")
        self.root.geometry("1700x950")
        self.root.minsize(1200, 760)

        self.result_queue: queue.Queue[tuple[str, object]] = queue.Queue()
        self.rows_by_id: dict[str, dict] = {}
        self.notifications_by_id: dict[str, dict] = {}
        self.current_chart_rows: list[dict] = []
        self.current_sky_rows: list[dict] = []
        self.sky_hover_points: list[dict] = []
        self.latest_selected_row: dict | None = None
        self.current_alert_table = "recent_alerts"
        self.cached_saved_alerts: dict[str, list[dict]] = {}

        self.limit_var = tk.StringVar(value=str(DEFAULT_LIMIT))
        self.view_mode_var = tk.StringVar(value="recent live")
        self.class_filter_var = tk.StringVar(value="all")
        self.category_filter_var = tk.StringVar(value="all")
        self.live_enabled = tk.BooleanVar(value=True)
        self.show_all_days = tk.BooleanVar(value=False)
        self.sky_time_filter_var = tk.StringVar(value="last 30 days")
        self.sky_view_mode_var = tk.StringVar(value="pointings")
        self.sky_show_selected_var = tk.BooleanVar(value=True)
        self.analysis_sso_var = tk.StringVar(value="")
        self.analysis_status_var = tk.StringVar(value="No deep analysis running.")
        self.analysis_progress_var = tk.DoubleVar(value=0.0)
        self.analysis_progress_text_var = tk.StringVar(value="0 %")
        self.include_period_plots_var = tk.BooleanVar(value=False)

        self.connection_var = tk.StringVar(value="Connecting to server...")
        self.service_var = tk.StringVar(value="Collector: unknown")
        self.total_var = tk.StringVar(value="0")
        self.stream_started_var = tk.StringVar(value="stream start unknown")
        self.candidates_var = tk.StringVar(value="0")
        self.unread_notifications_var = tk.StringVar(value="0")
        self.candidate_inbox_var = tk.StringVar(value="0")
        self.candidate_inbox_subtitle_var = tk.StringVar(value="0 saved total")
        self.latest_german_var = tk.StringVar(value="none yet")
        self.latest_utc_var = tk.StringVar(value="")
        self.table_status_var = tk.StringVar(value="Live table not loaded yet.")
        self.category_count_vars = {
            category["key"]: tk.StringVar(value="0")
            for category in CATEGORY_DEFINITIONS
        }
        self.category_badge_vars = {
            category["key"]: tk.StringVar(value="")
            for category in CATEGORY_DEFINITIONS
        }
        self.category_cards: dict[str, tk.Frame] = {}
        self.category_badge_widgets: dict[str, tk.Label] = {}
        self.seen_state = self.load_seen_state()
        self.threshold_vars = {
            key: tk.StringVar(value=str(value))
            for key, value in DEFAULT_THRESHOLDS.items()
        }
        self.filter_vars = {
            key: tk.BooleanVar(value=value)
            for key, value in DEFAULT_ACTIVE_FILTERS.items()
        }
        self.column_vars = {
            column: tk.BooleanVar(value=True)
            for column in COLUMNS
        }
        self.scoring_config_status_var = tk.StringVar(value="Server scoring config not loaded yet.")

        self.dashboard_loading = False
        self.live_loading = False
        self.alert_refresh_pending = False
        self.saved_alert_cache_last_refresh = 0.0
        self.sky_loading = False
        self.notifications_loading = False
        self.calibration_loading = False
        self.detail_loading_ids: set[str] = set()
        self.notifications_loaded_once = False
        self.calibration_loaded_once = False
        self.scoring_config_loaded_once = False
        self.analysis_loading = False
        self.analysis_module = None
        self.current_figures = []
        self.current_canvas = None
        self.current_toolbar = None
        self.preferred_plot_index = 0
        self.preferred_plot_name = None
        self.details_plot_ratio_applied = False

        self.configure_style()
        self.create_widgets()
        self.root.after(50, self.load_recent_alert_cache)
        self.root.after(900, self.refresh_dashboard)
        self.root.after(STARTUP_LIVE_REFRESH_DELAY_MS, self.live_tick)
        self.root.after(STARTUP_SKY_REFRESH_DELAY_MS, self.refresh_sky_coverage)
        self.root.after(250, self.process_result_queue)
        self.root.after(DASHBOARD_POLL_MS, self.dashboard_tick)

    def configure_style(self):
        style = ttk.Style()

        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        self.bg = "#08111f"
        self.panel = "#101b2d"
        self.panel_2 = "#162235"
        self.info_panel = "#13243a"
        self.header = "#1f2c42"
        self.text = "#e5edf7"
        self.muted = "#9fb0c5"
        self.accent = "#3b82f6"
        self.good = "#22c55e"
        self.warn = "#f59e0b"
        self.danger = "#ef4444"

        self.root.configure(bg=self.bg)
        style.configure(".", background=self.bg, foreground=self.text, fieldbackground=self.panel)
        style.configure("TFrame", background=self.bg)
        style.configure("Panel.TFrame", background=self.panel)
        style.configure("Card.TFrame", background=self.panel_2)
        style.configure("InfoPanel.TFrame", background=self.info_panel, relief=tk.SOLID, borderwidth=1)
        style.configure("TLabel", background=self.bg, foreground=self.text, font=("Segoe UI", 11))
        style.configure("InfoPanel.TLabel", background=self.info_panel, foreground=self.text, font=("Segoe UI", 11))
        style.configure("InfoPanelTitle.TLabel", background=self.info_panel, foreground="#f8fafc", font=("Segoe UI", 12, "bold"))
        style.configure("Muted.TLabel", background=self.bg, foreground=self.muted, font=("Segoe UI", 10))
        style.configure("Title.TLabel", background=self.bg, foreground="#f8fafc", font=("Segoe UI", 24, "bold"))
        style.configure("Subtitle.TLabel", background=self.bg, foreground=self.muted, font=("Segoe UI", 12))
        style.configure("CardTitle.TLabel", background=self.panel_2, foreground=self.muted, font=("Segoe UI", 11, "bold"))
        style.configure("CardValue.TLabel", background=self.panel_2, foreground="#f8fafc", font=("Segoe UI", 24, "bold"))
        style.configure("CardSmall.TLabel", background=self.panel_2, foreground=self.muted, font=("Segoe UI", 10))
        style.configure("TButton", font=("Segoe UI", 11, "bold"), padding=(14, 9))
        style.configure("Primary.TButton", font=("Segoe UI", 12, "bold"), padding=(18, 11))
        style.configure("TCheckbutton", background=self.bg, foreground=self.text, font=("Segoe UI", 11))
        style.configure("TEntry", fieldbackground=self.panel, foreground=self.text, insertcolor=self.text)
        style.configure(
            "TCombobox",
            fieldbackground=self.panel,
            background=self.panel_2,
            foreground=self.text,
            arrowcolor=self.text,
            selectbackground=self.panel,
            selectforeground=self.text,
            bordercolor=self.header,
            lightcolor=self.header,
            darkcolor=self.header,
        )
        style.map(
            "TCombobox",
            fieldbackground=[("readonly", self.panel), ("!disabled", self.panel)],
            foreground=[("readonly", self.text), ("!disabled", self.text)],
            selectbackground=[("readonly", self.panel)],
            selectforeground=[("readonly", self.text)],
        )
        self.root.option_add("*TCombobox*Listbox.background", self.panel)
        self.root.option_add("*TCombobox*Listbox.foreground", self.text)
        self.root.option_add("*TCombobox*Listbox.selectBackground", self.accent)
        self.root.option_add("*TCombobox*Listbox.selectForeground", "white")
        style.configure("TNotebook", background=self.bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=self.panel, foreground=self.text, padding=(16, 9), font=("Segoe UI", 11))
        style.map("TNotebook.Tab", background=[("selected", self.accent)])

        style.configure(
            "Treeview",
            background="#06101f",
            fieldbackground="#06101f",
            foreground=self.text,
            rowheight=32,
            font=("Segoe UI", 10),
        )
        style.configure(
            "Treeview.Heading",
            background=self.header,
            foreground="#f8fafc",
            font=("Segoe UI", 10, "bold"),
        )

    def create_widgets(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.start_tab = ttk.Frame(self.notebook, padding=18)
        self.live_tab = ttk.Frame(self.notebook, padding=10)
        self.details_tab = ttk.Frame(self.notebook, padding=10)
        self.notifications_tab = ttk.Frame(self.notebook, padding=10)
        self.calibration_tab = ttk.Frame(self.notebook, padding=10)
        self.thresholds_tab = ttk.Frame(self.notebook, padding=10)
        self.filters_tab = ttk.Frame(self.notebook, padding=10)
        self.visible_data_tab = ttk.Frame(self.notebook, padding=10)
        self.filter_info_tab = ttk.Frame(self.notebook, padding=10)

        self.notebook.add(self.start_tab, text="Start")
        self.notebook.add(self.live_tab, text="Live alerts")
        self.notebook.add(self.details_tab, text="Details / Deep Analysis")
        self.notebook.add(self.notifications_tab, text="Notifications")
        self.notebook.add(self.calibration_tab, text="Calibration")
        self.notebook.add(self.thresholds_tab, text="Thresholds")
        self.notebook.add(self.filters_tab, text="Active filters")
        self.notebook.add(self.visible_data_tab, text="Visible data")
        self.notebook.add(self.filter_info_tab, text="Filter info")

        self.create_start_tab()
        self.create_live_tab()
        self.create_details_tab()
        self.create_notifications_tab()
        self.create_calibration_tab()
        self.create_thresholds_tab()
        self.create_filters_tab()
        self.create_visible_data_tab()
        self.create_filter_info_tab()
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_changed)

    def load_seen_state(self) -> dict[str, int]:
        try:
            data = json.loads(SEEN_PATH.read_text(encoding="utf-8"))
        except (FileNotFoundError, json.JSONDecodeError, OSError):
            return {}

        if not isinstance(data, dict):
            return {}

        cleaned = {}
        for key, value in data.items():
            try:
                cleaned[str(key)] = int(value)
            except (TypeError, ValueError):
                continue

        return cleaned

    def save_seen_state(self):
        try:
            SEEN_PATH.write_text(
                json.dumps(self.seen_state, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
        except OSError:
            self.connection_var.set(f"Could not save seen-state file: {SEEN_PATH}")

    def on_tab_changed(self, _event=None):
        selected = self.notebook.select()

        if selected == str(self.details_tab):
            self.root.after(80, self.set_details_plot_ratio)
            self.root.after(350, self.set_details_plot_ratio)
            return

        if selected == str(self.notifications_tab) and not self.notifications_loaded_once:
            self.notifications_loaded_once = True
            self.refresh_notifications()
            return

        if selected == str(self.calibration_tab) and not self.calibration_loaded_once:
            self.calibration_loaded_once = True
            self.refresh_calibration()
            return

        scoring_tabs = {
            str(self.thresholds_tab),
            str(self.filters_tab),
            str(self.filter_info_tab),
        }
        if selected in scoring_tabs and not self.scoring_config_loaded_once:
            self.scoring_config_loaded_once = True
            self.load_server_scoring_config()

    def create_start_tab(self):
        start_canvas = tk.Canvas(
            self.start_tab,
            bg=self.bg,
            highlightthickness=0,
        )
        start_scroll = ttk.Scrollbar(
            self.start_tab,
            orient=tk.VERTICAL,
            command=start_canvas.yview,
        )
        start_canvas.configure(yscrollcommand=start_scroll.set)
        start_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        start_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        start_content = ttk.Frame(start_canvas)
        self.start_canvas_window = start_canvas.create_window(
            (0, 0),
            window=start_content,
            anchor="nw",
        )
        self.start_canvas = start_canvas

        start_content.bind(
            "<Configure>",
            lambda _event: start_canvas.configure(scrollregion=start_canvas.bbox("all")),
        )
        start_canvas.bind(
            "<Configure>",
            lambda event: start_canvas.itemconfigure(self.start_canvas_window, width=event.width),
        )
        start_canvas.bind("<MouseWheel>", self.on_start_mousewheel)
        start_content.bind("<MouseWheel>", self.on_start_mousewheel)

        header = ttk.Frame(start_content)
        header.pack(side=tk.TOP, fill=tk.X, pady=(0, 18))

        title_block = ttk.Frame(header)
        title_block.pack(side=tk.LEFT, fill=tk.X, expand=True)

        ttk.Label(
            title_block,
            text="AstroPrak Server Monitor",
            style="Title.TLabel",
        ).pack(anchor="w")
        ttk.Label(
            title_block,
            text=f"Server: {SERVER_TARGET}  |  database: {DB_PATH}",
            style="Subtitle.TLabel",
        ).pack(anchor="w", pady=(4, 0))
        ttk.Label(
            title_block,
            textvariable=self.connection_var,
            style="Muted.TLabel",
        ).pack(anchor="w", pady=(4, 0))

        header_actions = ttk.Frame(header)
        header_actions.pack(side=tk.RIGHT, padx=(12, 0))
        ttk.Button(
            header_actions,
            text="Refresh / reconnect",
            style="Primary.TButton",
            command=self.refresh_from_server,
        ).pack(side=tk.TOP, fill=tk.X)

        card_row = ttk.Frame(start_content)
        card_row.pack(side=tk.TOP, fill=tk.X, pady=(0, 18))

        self.create_card(card_row, "Total processed", self.total_var, self.stream_started_var)
        self.create_card(card_row, "Candidate inbox", self.candidate_inbox_var, self.candidate_inbox_subtitle_var)
        self.create_latest_card(card_row)

        category_header = ttk.Frame(start_content)
        category_header.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))
        ttk.Label(
            category_header,
            text="Alert categories",
            font=("Segoe UI", 15, "bold"),
        ).pack(side=tk.LEFT)
        ttk.Label(
            category_header,
            text="Interesting and Photometric use saved candidates; other counts use the recent buffer. Red badges show newly seen rows.",
            style="Muted.TLabel",
        ).pack(side=tk.RIGHT)

        category_grid = ttk.Frame(start_content)
        category_grid.pack(side=tk.TOP, fill=tk.X, pady=(0, 12))

        visible_categories = [
            "urgent",
            "interesting",
            "review",
            "photometric",
            "matched_lsst",
            "unmatched_lsst",
            "persistence",
            "near_snowline",
            "contamination",
            "quality_rejected",
            "normal",
        ]

        for idx, key in enumerate(visible_categories):
            row = idx // 3
            col = idx % 3
            self.create_category_card(category_grid, key, row, col)

        chart_header = ttk.Frame(start_content)
        chart_header.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))
        ttk.Label(
            chart_header,
            text="Alerts per day",
            font=("Segoe UI", 15, "bold"),
        ).pack(side=tk.LEFT)
        ttk.Checkbutton(
            chart_header,
            text="Expand to all days",
            variable=self.show_all_days,
            command=self.refresh_dashboard,
        ).pack(side=tk.RIGHT)

        chart_frame = ttk.Frame(start_content, style="Panel.TFrame", padding=12)
        chart_frame.pack(side=tk.TOP, fill=tk.X)

        self.chart_canvas = tk.Canvas(
            chart_frame,
            bg=self.panel,
            highlightthickness=0,
            height=280,
        )
        self.chart_canvas.pack(fill=tk.X)
        self.chart_canvas.bind("<Configure>", lambda _event: self.draw_chart())
        self.chart_canvas.bind("<MouseWheel>", self.on_start_mousewheel)

        sky_header = ttk.Frame(start_content)
        sky_header.pack(side=tk.TOP, fill=tk.X, pady=(18, 8))
        ttk.Label(
            sky_header,
            text="Sky Coverage",
            font=("Segoe UI", 15, "bold"),
        ).pack(side=tk.LEFT)

        sky_controls = ttk.Frame(sky_header)
        sky_controls.pack(side=tk.RIGHT)
        ttk.Label(sky_controls, text="Range:").pack(side=tk.LEFT, padx=(0, 4))
        sky_range_combo = ttk.Combobox(
            sky_controls,
            textvariable=self.sky_time_filter_var,
            state="readonly",
            values=["last night", "last 7 days", "last 30 days", "all data"],
            width=14,
        )
        sky_range_combo.pack(side=tk.LEFT, padx=(0, 10))
        sky_range_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_sky_coverage())

        ttk.Label(sky_controls, text="View:").pack(side=tk.LEFT, padx=(0, 4))
        sky_mode_combo = ttk.Combobox(
            sky_controls,
            textvariable=self.sky_view_mode_var,
            state="readonly",
            values=["pointings", "heatmap"],
            width=11,
        )
        sky_mode_combo.pack(side=tk.LEFT, padx=(0, 10))
        sky_mode_combo.bind("<<ComboboxSelected>>", lambda _event: self.draw_sky_coverage())

        ttk.Checkbutton(
            sky_controls,
            text="Selected alert",
            variable=self.sky_show_selected_var,
            command=self.draw_sky_coverage,
        ).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(sky_controls, text="Refresh", command=self.refresh_sky_coverage).pack(side=tk.LEFT)

        sky_frame = ttk.Frame(start_content, style="Panel.TFrame", padding=12)
        sky_frame.pack(side=tk.TOP, fill=tk.X)
        self.sky_status_var = tk.StringVar(value="Sky coverage not loaded yet.")
        ttk.Label(sky_frame, textvariable=self.sky_status_var, style="Muted.TLabel").pack(anchor="w", pady=(0, 6))

        self.sky_figure = Figure(figsize=(12, 5.4), dpi=100)
        self.sky_canvas = FigureCanvasTkAgg(self.sky_figure, master=sky_frame)
        self.sky_toolbar = NavigationToolbar2Tk(self.sky_canvas, sky_frame, pack_toolbar=False)
        self.sky_toolbar.update()
        self.sky_toolbar.pack(side=tk.TOP, fill=tk.X)
        self.sky_canvas.get_tk_widget().pack(side=tk.TOP, fill=tk.X)
        self.sky_canvas.mpl_connect("motion_notify_event", self.on_sky_mouseover)

        footer = ttk.Frame(start_content)
        footer.pack(side=tk.TOP, fill=tk.X, pady=(12, 0))
        ttk.Label(footer, textvariable=self.service_var, style="Muted.TLabel").pack(side=tk.LEFT)
        ttk.Button(footer, text="Refresh dashboard", command=self.refresh_dashboard).pack(side=tk.RIGHT)
        self.bind_mousewheel_to_children(start_content, self.on_start_mousewheel)

    def bind_mousewheel_to_children(self, widget, callback):
        widget.bind("<MouseWheel>", callback)
        for child in widget.winfo_children():
            self.bind_mousewheel_to_children(child, callback)

    def create_card(self, parent, title, value_var, subtitle):
        card = ttk.Frame(parent, style="Card.TFrame", padding=16)
        card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 12))
        ttk.Label(card, text=title, style="CardTitle.TLabel").pack(anchor="w")
        ttk.Label(card, textvariable=value_var, style="CardValue.TLabel").pack(anchor="w", pady=(8, 2))
        if isinstance(subtitle, tk.Variable):
            ttk.Label(card, textvariable=subtitle, style="CardSmall.TLabel").pack(anchor="w")
        else:
            ttk.Label(card, text=subtitle, style="CardSmall.TLabel").pack(anchor="w")

    def create_latest_card(self, parent):
        card = ttk.Frame(parent, style="Card.TFrame", padding=16)
        card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 12))
        ttk.Label(card, text="Latest alert", style="CardTitle.TLabel").pack(anchor="w")
        ttk.Label(
            card,
            textvariable=self.latest_german_var,
            style="CardValue.TLabel",
            font=("Segoe UI", 22, "bold"),
        ).pack(anchor="w", pady=(8, 2))
        ttk.Label(
            card,
            textvariable=self.latest_utc_var,
            style="CardSmall.TLabel",
        ).pack(anchor="w")
        ttk.Label(
            card,
            text="German time above, UTC below",
            style="CardSmall.TLabel",
        ).pack(anchor="w", pady=(4, 0))

    def create_category_card(self, parent, key: str, row: int, column: int):
        definition = CATEGORY_BY_KEY[key]
        card = tk.Frame(parent, bg=self.panel_2, padx=10, pady=8, cursor="hand2")
        card.grid(row=row, column=column, sticky="nsew", padx=5, pady=5)
        parent.columnconfigure(column, weight=1)

        top = tk.Frame(card, bg=self.panel_2)
        top.pack(side=tk.TOP, fill=tk.X)

        title = tk.Label(
            top,
            text=definition["label"],
            bg=self.panel_2,
            fg=self.text,
            font=("Segoe UI", 10, "bold"),
            anchor="w",
        )
        title.pack(side=tk.LEFT)

        badge = tk.Label(
            top,
            textvariable=self.category_badge_vars[key],
            bg=self.panel_2,
            fg=self.panel_2,
            font=("Segoe UI", 9, "bold"),
            padx=7,
            pady=2,
        )
        badge.pack(side=tk.RIGHT)

        value = tk.Label(
            card,
            textvariable=self.category_count_vars[key],
            bg=self.panel_2,
            fg="#f8fafc",
            font=("Segoe UI", 16, "bold"),
            anchor="w",
        )
        value.pack(side=tk.TOP, fill=tk.X, pady=(5, 0))

        subtitle = tk.Label(
            card,
            text=definition["subtitle"],
            bg=self.panel_2,
            fg=self.muted,
            font=("Segoe UI", 9),
            anchor="w",
        )
        subtitle.pack(side=tk.TOP, fill=tk.X)

        for widget in (card, top, title, badge, value, subtitle):
            widget.bind("<Button-1>", lambda _event, category_key=key: self.open_category(category_key))

        self.category_cards[key] = card
        self.category_badge_widgets[key] = badge

    def open_category(self, category_key: str):
        self.class_filter_var.set("all")
        self.category_filter_var.set(category_key)
        if category_key == "matched_lsst":
            self.view_mode_var.set("LSST SSO matched")
        elif category_key == "unmatched_lsst":
            self.view_mode_var.set("LSST SSO all")
        elif category_key in {"urgent", "interesting", "photometric"}:
            self.view_mode_var.set("interesting saved")
        else:
            self.view_mode_var.set("recent live")
        latest_id = self.get_category_latest_id(category_key)
        self.seen_state[category_key] = max(self.seen_state.get(category_key, 0), latest_id)
        if hasattr(self, "category_unseen_counts"):
            self.category_unseen_counts[category_key] = 0
        self.save_seen_state()
        self.update_category_badges()
        self.notebook.select(self.live_tab)
        self.table_status_var.set(f"Opening {category_key} alerts...")
        if category_key in self.cached_saved_alerts:
            request = {
                "limit": self.get_limit(),
                "class_filter": "all",
                "category_filter": category_key,
                "table_name": self.table_name_for_view(),
            }
            cached_rows = self.cached_saved_alerts[category_key][: request["limit"]]
            self.current_alert_table = request["table_name"]
            self.current_alert_request = request
            self.apply_alert_rows(cached_rows)
            self.table_status_var.set(
                f"Showing {len(cached_rows)} cached {category_key} alerts while refreshing from server..."
            )
        self.root.after_idle(self.refresh_alerts)

    def create_live_tab(self):
        top_frame = ttk.Frame(self.live_tab)
        top_frame.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))

        action_row = ttk.Frame(top_frame)
        action_row.pack(side=tk.TOP, fill=tk.X)
        filter_row = ttk.Frame(top_frame)
        filter_row.pack(side=tk.TOP, fill=tk.X, pady=(6, 0))

        ttk.Button(action_row, text="Refresh / reconnect", command=self.refresh_from_server).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(action_row, text="Refresh now", command=self.refresh_alerts).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(action_row, text="Reset filters", command=self.reset_live_filters).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Checkbutton(
            action_row,
            text="Live polling",
            variable=self.live_enabled,
        ).pack(side=tk.LEFT, padx=10)
        ttk.Label(action_row, textvariable=self.table_status_var, style="Muted.TLabel").pack(side=tk.RIGHT)

        ttk.Label(filter_row, text="Limit:").pack(side=tk.LEFT, padx=(0, 4))
        ttk.Entry(filter_row, textvariable=self.limit_var, width=8).pack(side=tk.LEFT, padx=(0, 18))

        ttk.Label(filter_row, text="View:").pack(side=tk.LEFT, padx=(0, 4))
        view_combo = ttk.Combobox(
            filter_row,
            textvariable=self.view_mode_var,
            state="readonly",
            values=["recent live", "interesting saved", "LSST SSO matched", "LSST SSO all"],
            width=18,
        )
        view_combo.pack(side=tk.LEFT, padx=(0, 18))
        view_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_alerts())

        ttk.Label(filter_row, text="Review level:").pack(side=tk.LEFT, padx=(0, 4))
        class_combo = ttk.Combobox(
            filter_row,
            textvariable=self.class_filter_var,
            state="readonly",
            values=["all", "urgent", "interesting", "review", "normal", "rejected"],
            width=16,
        )
        class_combo.pack(side=tk.LEFT, padx=(0, 18))
        class_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_alerts())

        ttk.Label(filter_row, text="Reason category:").pack(side=tk.LEFT, padx=(0, 4))
        category_combo = ttk.Combobox(
            filter_row,
            textvariable=self.category_filter_var,
            state="readonly",
            values=[category["key"] for category in CATEGORY_DEFINITIONS],
            width=20,
        )
        category_combo.pack(side=tk.LEFT)
        category_combo.bind("<<ComboboxSelected>>", lambda _event: self.refresh_alerts())

        table_frame = ttk.Frame(self.live_tab)
        table_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.tree = ttk.Treeview(
            table_frame,
            columns=COLUMNS,
            show="headings",
            selectmode="browse",
        )

        for column in COLUMNS:
            self.tree.heading(column, text=COLUMN_HEADINGS.get(column, column))
            self.tree.column(
                column,
                width=COLUMN_WIDTHS.get(column, 100),
                anchor=tk.W,
                stretch=False,
            )

        y_scroll = ttk.Scrollbar(table_frame, orient=tk.VERTICAL, command=self.tree.yview)
        x_scroll = ttk.Scrollbar(table_frame, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=y_scroll.set, xscrollcommand=x_scroll.set)

        self.tree.grid(row=0, column=0, sticky="nsew")
        y_scroll.grid(row=0, column=1, sticky="ns")
        x_scroll.grid(row=1, column=0, sticky="ew")
        table_frame.rowconfigure(0, weight=1)
        table_frame.columnconfigure(0, weight=1)

        self.tree.tag_configure("urgent", background="#7f1d1d", foreground="#fff7ed")
        self.tree.tag_configure("interesting", background="#78350f", foreground="#fff7ed")
        self.tree.tag_configure("review", background="#365314", foreground="#f7fee7")
        self.tree.tag_configure("photometric_extreme", background="#7f1d1d", foreground="#fff7ed")
        self.tree.tag_configure("photometric_strong", background="#92400e", foreground="#fff7ed")
        self.tree.tag_configure("photometric_weak", background="#365314", foreground="#f7fee7")
        self.tree.tag_configure("fallback_brightening", background="#1e3a8a", foreground="#dbeafe")
        self.tree.tag_configure("persistent_multi_night", background="#701a75", foreground="#fae8ff")
        self.tree.tag_configure("persistent_repeat", background="#581c87", foreground="#f3e8ff")
        self.tree.tag_configure("near_snowline_activity", background="#0f766e", foreground="#ccfbf1")
        self.tree.tag_configure("possible_contamination", background="#4b5563", foreground="#f9fafb")
        self.tree.tag_configure("quality_rejected", background="#450a0a", foreground="#fecaca")
        self.tree.tag_configure("normal", background="#06101f", foreground=self.text)
        self.tree.tag_configure("rejected", background="#1f2937", foreground="#cbd5e1")
        self.tree.bind("<<TreeviewSelect>>", self.on_select_row)
        self.tree.bind("<Double-1>", self.open_details_from_table)
        self.tree.bind("<MouseWheel>", self.on_tree_mousewheel)
        self.tree.bind("<Shift-MouseWheel>", self.on_tree_shift_mousewheel)

    def create_details_tab(self):
        top = ttk.Frame(self.details_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))

        ttk.Label(
            top,
            text="Selected alert details",
            font=("Segoe UI", 15, "bold"),
        ).pack(side=tk.LEFT)
        ttk.Button(
            top,
            text="Back to live alerts",
            command=lambda: self.notebook.select(self.live_tab),
        ).pack(side=tk.RIGHT)

        analysis_controls = ttk.Frame(self.details_tab)
        analysis_controls.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))

        ttk.Label(analysis_controls, text="SSO ID:").pack(side=tk.LEFT)
        ttk.Entry(
            analysis_controls,
            textvariable=self.analysis_sso_var,
            width=18,
        ).pack(side=tk.LEFT, padx=(6, 8))
        ttk.Button(
            analysis_controls,
            text="Use selected",
            command=self.use_selected_for_analysis,
        ).pack(side=tk.LEFT, padx=4)
        ttk.Button(
            analysis_controls,
            text="Run Deep Analysis",
            command=self.start_deep_analysis,
        ).pack(side=tk.LEFT, padx=4)
        ttk.Button(
            analysis_controls,
            text="Retry MPC match",
            command=self.retry_selected_mpc_match,
        ).pack(side=tk.LEFT, padx=4)
        ttk.Checkbutton(
            analysis_controls,
            text="Show Lomb-Scargle",
            variable=self.include_period_plots_var,
        ).pack(side=tk.LEFT, padx=12)
        ttk.Label(
            analysis_controls,
            textvariable=self.analysis_status_var,
            style="Muted.TLabel",
        ).pack(side=tk.LEFT, padx=12)

        analysis_progress_row = ttk.Frame(self.details_tab)
        self.analysis_progress_row = analysis_progress_row
        self.analysis_progress_bar = ttk.Progressbar(
            analysis_progress_row,
            variable=self.analysis_progress_var,
            maximum=100.0,
            mode="determinate",
        )
        self.analysis_progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Label(
            analysis_progress_row,
            textvariable=self.analysis_progress_text_var,
            width=7,
            anchor=tk.E,
            style="Muted.TLabel",
        ).pack(side=tk.LEFT, padx=(10, 0))

        details_pane = ttk.PanedWindow(self.details_tab, orient=tk.HORIZONTAL)
        details_pane.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        self.details_pane = details_pane

        left_info_frame = ttk.Frame(details_pane)
        plot_area = ttk.Frame(details_pane)
        details_pane.add(left_info_frame, weight=2)
        details_pane.add(plot_area, weight=5)
        self.root.after(250, self.set_details_plot_ratio)
        self.root.after(900, self.set_details_plot_ratio)

        left_vertical_pane = ttk.PanedWindow(left_info_frame, orient=tk.VERTICAL)
        left_vertical_pane.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        alert_frame = ttk.Frame(left_vertical_pane, style="InfoPanel.TFrame", padding=8)
        analysis_summary_frame = ttk.Frame(left_vertical_pane, style="InfoPanel.TFrame", padding=8)
        left_vertical_pane.add(alert_frame, weight=3)
        left_vertical_pane.add(analysis_summary_frame, weight=2)

        ttk.Label(
            alert_frame,
            text="Alert details",
            style="InfoPanelTitle.TLabel",
        ).pack(anchor="w", pady=(0, 4))

        self.detail_text = tk.Text(
            alert_frame,
            wrap=tk.WORD,
            bg=self.info_panel,
            fg=self.text,
            insertbackground=self.text,
            selectbackground=self.accent,
            font=("Consolas", 11),
            relief=tk.FLAT,
            padx=12,
            pady=12,
        )
        detail_scroll = ttk.Scrollbar(alert_frame, orient=tk.VERTICAL, command=self.detail_text.yview)
        self.detail_text.configure(yscrollcommand=detail_scroll.set)
        self.detail_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        detail_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.detail_text.bind("<MouseWheel>", self.on_detail_mousewheel)
        self.detail_text.bind("<Button-1>", lambda _event: self.detail_text.focus_set())

        ttk.Label(
            analysis_summary_frame,
            text="Scientific summary",
            style="InfoPanelTitle.TLabel",
        ).pack(anchor="w", pady=(0, 4))

        self.analysis_text = tk.Text(
            analysis_summary_frame,
            wrap=tk.WORD,
            bg=self.info_panel,
            fg=self.text,
            insertbackground=self.text,
            selectbackground=self.accent,
            font=("Consolas", 10),
            relief=tk.FLAT,
            padx=12,
            pady=12,
        )
        analysis_summary_scroll = ttk.Scrollbar(
            analysis_summary_frame,
            orient=tk.VERTICAL,
            command=self.analysis_text.yview,
        )
        self.analysis_text.configure(yscrollcommand=analysis_summary_scroll.set)
        self.analysis_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        analysis_summary_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.analysis_text.bind("<MouseWheel>", self.on_analysis_text_mousewheel)
        self.analysis_text.bind("<Button-1>", lambda _event: self.analysis_text.focus_set())

        plot_top = ttk.Frame(plot_area)
        plot_top.pack(side=tk.TOP, fill=tk.X, pady=(0, 6))
        ttk.Label(plot_top, text="Plot:").pack(side=tk.LEFT)
        self.plot_combo = ttk.Combobox(plot_top, state="readonly", width=48)
        self.plot_combo.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(6, 0))
        self.plot_combo.bind("<<ComboboxSelected>>", self.on_plot_select)

        self.plot_frame = ttk.Frame(plot_area)
        self.plot_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.set_detail_text("Select a row in Live alerts to see its full scoring details here.")
        self.set_analysis_text("Select an alert with an SSO ID, then run Deep Analysis.")

    def set_details_plot_ratio(self):
        if not hasattr(self, "details_pane"):
            return

        try:
            width = self.details_pane.winfo_width()
            if width > 500:
                self.details_pane.sashpos(0, int(width / 3))
                self.details_plot_ratio_applied = True
        except Exception:
            pass

    def create_notifications_tab(self):
        top = ttk.Frame(self.notifications_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))
        ttk.Button(top, text="Refresh notifications", command=self.refresh_notifications).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Mark all reviewed", command=self.mark_notifications_reviewed).pack(side=tk.LEFT, padx=8)

        columns = ["id", "created_utc", "severity", "primary_category", "activity_score", "sso_id", "object_id", "message"]
        self.notifications_tree = ttk.Treeview(
            self.notifications_tab,
            columns=columns,
            show="headings",
            selectmode="browse",
        )
        widths = {
            "id": 70,
            "created_utc": 170,
            "severity": 90,
            "primary_category": 170,
            "activity_score": 80,
            "sso_id": 110,
            "object_id": 150,
            "message": 620,
        }
        for column in columns:
            heading = {
                "created_utc": "UTC time",
                "primary_category": "reason category",
                "activity_score": "priority",
                "sso_id": "SSO",
                "object_id": "objectId",
            }.get(column, column)
            self.notifications_tree.heading(column, text=heading)
            self.notifications_tree.column(column, width=widths.get(column, 100), anchor=tk.W, stretch=False)
        scroll_y = ttk.Scrollbar(self.notifications_tab, orient=tk.VERTICAL, command=self.notifications_tree.yview)
        scroll_x = ttk.Scrollbar(self.notifications_tab, orient=tk.HORIZONTAL, command=self.notifications_tree.xview)
        self.notifications_tree.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        self.notifications_tree.bind("<Double-1>", self.open_notification_for_analysis)
        self.notifications_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        scroll_x.pack(side=tk.BOTTOM, fill=tk.X)

    def create_calibration_tab(self):
        top = ttk.Frame(self.calibration_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 8))
        ttk.Button(top, text="Refresh calibration stats", command=self.refresh_calibration).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Label(
            top,
            text="These are live sanity-check distributions by reason category, review level and known reference labels.",
            style="Muted.TLabel",
        ).pack(side=tk.LEFT, padx=12)

        columns = ["key", "count", "interesting_count", "best_score", "last_seen_utc"]
        self.calibration_tree = ttk.Treeview(
            self.calibration_tab,
            columns=columns,
            show="headings",
            selectmode="browse",
        )
        widths = {
            "key": 300,
            "count": 100,
            "interesting_count": 140,
            "best_score": 100,
            "last_seen_utc": 190,
        }
        for column in columns:
            self.calibration_tree.heading(column, text=column)
            self.calibration_tree.column(column, width=widths.get(column, 120), anchor=tk.W, stretch=False)
        scroll_y = ttk.Scrollbar(self.calibration_tab, orient=tk.VERTICAL, command=self.calibration_tree.yview)
        scroll_x = ttk.Scrollbar(self.calibration_tab, orient=tk.HORIZONTAL, command=self.calibration_tree.xview)
        self.calibration_tree.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
        self.calibration_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll_y.pack(side=tk.RIGHT, fill=tk.Y)
        scroll_x.pack(side=tk.BOTTOM, fill=tk.X)

    def create_thresholds_tab(self):
        top = ttk.Frame(self.thresholds_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 10))
        ttk.Button(top, text="Load from server", command=self.load_server_scoring_config).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Apply to server + restart collector", command=self.apply_server_scoring_config).pack(side=tk.LEFT, padx=8)
        ttk.Button(top, text="Reset defaults", command=self.reset_threshold_defaults).pack(side=tk.LEFT, padx=8)
        ttk.Label(top, textvariable=self.scoring_config_status_var, style="Muted.TLabel").pack(side=tk.RIGHT)

        frame = ttk.Frame(self.thresholds_tab, style="Panel.TFrame", padding=12)
        frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        for row, (key, label) in enumerate(THRESHOLD_LABELS.items()):
            ttk.Label(frame, text=label).grid(row=row, column=0, sticky="w", padx=6, pady=5)
            ttk.Entry(frame, textvariable=self.threshold_vars[key], width=14).grid(
                row=row,
                column=1,
                sticky="w",
                padx=6,
                pady=5,
            )
            ttk.Label(frame, text=key, style="Muted.TLabel").grid(row=row, column=2, sticky="w", padx=12, pady=5)

        frame.columnconfigure(2, weight=1)

    def create_filters_tab(self):
        top = ttk.Frame(self.filters_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 10))
        ttk.Button(top, text="Load from server", command=self.load_server_scoring_config).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Apply to server + restart collector", command=self.apply_server_scoring_config).pack(side=tk.LEFT, padx=8)
        ttk.Button(top, text="Enable all", command=self.enable_all_filters).pack(side=tk.LEFT, padx=8)
        ttk.Button(top, text="Reset defaults", command=self.reset_filter_defaults).pack(side=tk.LEFT, padx=8)

        frame = ttk.Frame(self.filters_tab, style="Panel.TFrame", padding=12)
        frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        for row, (key, label) in enumerate(FILTER_LABELS.items()):
            ttk.Checkbutton(
                frame,
                text=f"{label}  ({key})",
                variable=self.filter_vars[key],
            ).grid(row=row, column=0, sticky="w", padx=6, pady=5)

    def create_visible_data_tab(self):
        top = ttk.Frame(self.visible_data_tab)
        top.pack(side=tk.TOP, fill=tk.X, pady=(0, 10))
        ttk.Button(top, text="Show all columns", command=self.show_all_columns).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(top, text="Minimal columns", command=self.show_minimal_columns).pack(side=tk.LEFT, padx=8)
        ttk.Button(top, text="Apply columns", command=self.apply_column_selection).pack(side=tk.LEFT, padx=8)

        frame = ttk.Frame(self.visible_data_tab, style="Panel.TFrame", padding=12)
        frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        for row, column in enumerate(COLUMNS):
            ttk.Checkbutton(
                frame,
                text=f"{COLUMN_HEADINGS.get(column, column)}  ({column})",
                variable=self.column_vars[column],
                command=self.apply_column_selection,
            ).grid(row=row, column=0, sticky="w", padx=6, pady=4)

    def create_filter_info_tab(self):
        self.filter_info_text = tk.Text(
            self.filter_info_tab,
            wrap=tk.WORD,
            bg="#06101f",
            fg=self.text,
            insertbackground=self.text,
            font=("Consolas", 11),
            relief=tk.FLAT,
            padx=12,
            pady=12,
        )
        scroll = ttk.Scrollbar(self.filter_info_tab, orient=tk.VERTICAL, command=self.filter_info_text.yview)
        self.filter_info_text.configure(yscrollcommand=scroll.set)
        self.filter_info_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.filter_info_text.bind("<MouseWheel>", self.on_filter_info_mousewheel)
        self.update_filter_info_text()

    def set_detail_text(self, text: str):
        self.detail_text.configure(state=tk.NORMAL)
        self.detail_text.delete("1.0", tk.END)
        self.detail_text.insert(tk.END, text)
        self.detail_text.configure(state=tk.DISABLED)

    def set_analysis_text(self, text: str):
        self.analysis_text.configure(state=tk.NORMAL)
        self.analysis_text.delete("1.0", tk.END)
        self.analysis_text.insert(tk.END, text)
        self.analysis_text.configure(state=tk.DISABLED)

    def set_filter_info_text(self, text: str):
        self.filter_info_text.configure(state=tk.NORMAL)
        self.filter_info_text.delete("1.0", tk.END)
        self.filter_info_text.insert(tk.END, text)
        self.filter_info_text.configure(state=tk.DISABLED)

    def read_server_scoring_config(self) -> dict:
        command = f"cat {shlex.quote(SCORING_CONFIG_PATH)}"
        output = run_ssh(command, timeout=20)
        return json.loads(output)

    def write_server_scoring_config(self, config: dict):
        payload = json.dumps(config, indent=2, sort_keys=True)
        command = f"cat > {shlex.quote(SCORING_CONFIG_PATH)}"
        subprocess.run(
            [
                "ssh",
                "-o",
                "BatchMode=yes",
                "-o",
                "ConnectTimeout=8",
                SERVER_TARGET,
                command,
            ],
            input=payload,
            text=True,
            capture_output=True,
            timeout=30,
            check=True,
        )

    def load_server_scoring_config(self):
        self.scoring_config_status_var.set("Loading server scoring config...")
        self.start_worker(self.worker_load_server_scoring_config)

    def worker_load_server_scoring_config(self):
        try:
            config = self.read_server_scoring_config()
            self.result_queue.put(("scoring_config", config))
        except Exception as exc:
            self.result_queue.put(("scoring_config", {"error": str(exc)}))

    def apply_loaded_scoring_config(self, config: dict):
        if config.get("error"):
            self.scoring_config_status_var.set(f"Could not load config: {config.get('error')}")
            return

        thresholds = config.get("thresholds", {})
        active_filters = config.get("active_filters", {})

        for key, default in DEFAULT_THRESHOLDS.items():
            self.threshold_vars[key].set(str(thresholds.get(key, default)))

        for key, default in DEFAULT_ACTIVE_FILTERS.items():
            self.filter_vars[key].set(bool(active_filters.get(key, default)))

        self.scoring_config_status_var.set("Loaded server scoring config.")
        self.update_filter_info_text()

    def collect_scoring_config(self) -> dict:
        thresholds = {}
        for key, default in DEFAULT_THRESHOLDS.items():
            raw = self.threshold_vars[key].get()
            try:
                value = int(float(raw)) if isinstance(default, int) else float(raw)
            except ValueError:
                value = default
                self.threshold_vars[key].set(str(default))
            thresholds[key] = value

        active_filters = {
            key: bool(var.get())
            for key, var in self.filter_vars.items()
        }

        return {
            "thresholds": thresholds,
            "active_filters": active_filters,
        }

    def apply_server_scoring_config(self):
        try:
            config = self.collect_scoring_config()
            self.write_server_scoring_config(config)
            run_ssh(f"systemctl restart {shlex.quote(SERVICE_NAME)}", timeout=30)
            self.scoring_config_status_var.set("Applied config and restarted collector.")
            self.update_filter_info_text()
            self.refresh_dashboard()
        except Exception as exc:
            self.scoring_config_status_var.set(f"Could not apply config: {exc}")

    def reset_threshold_defaults(self):
        for key, value in DEFAULT_THRESHOLDS.items():
            self.threshold_vars[key].set(str(value))
        self.update_filter_info_text()

    def reset_filter_defaults(self):
        for key, value in DEFAULT_ACTIVE_FILTERS.items():
            self.filter_vars[key].set(value)
        self.update_filter_info_text()

    def enable_all_filters(self):
        for var in self.filter_vars.values():
            var.set(True)
        self.update_filter_info_text()

    def get_visible_columns(self):
        columns = [column for column in COLUMNS if self.column_vars[column].get()]
        return columns or ["id"]

    def apply_column_selection(self):
        visible_columns = self.get_visible_columns()
        self.tree["columns"] = visible_columns
        for column in visible_columns:
            self.tree.heading(column, text=COLUMN_HEADINGS.get(column, column))
            self.tree.column(
                column,
                width=COLUMN_WIDTHS.get(column, 100),
                anchor=tk.W,
                stretch=False,
            )
        self.refresh_alerts()

    def show_all_columns(self):
        for var in self.column_vars.values():
            var.set(True)
        self.apply_column_selection()

    def show_minimal_columns(self):
        minimal = {
            "received_local",
            "survey",
            "activity_score",
            "primary_category",
            "object_class",
            "phase_corrected_residual_sigma",
            "sso_id",
            "object_id",
            "magpsf",
            "anomaly_sigma",
        }
        for column, var in self.column_vars.items():
            var.set(column in minimal)
        self.apply_column_selection()

    def update_filter_info_text(self):
        config = self.collect_scoring_config()
        thresholds = config["thresholds"]
        active_filters = config["active_filters"]
        lines = [
            "Server scoring logic",
            "=" * 60,
            "",
            "Quality Gate",
            "-" * 40,
            f"- magpsf must exist and be physically plausible.",
            f"- reject_bad_sigmag: {active_filters['reject_bad_sigmag']} | sigmapsf > {thresholds['max_sigmag']}",
            f"- reject_nbad: {active_filters['reject_nbad']} | nbad > 0",
            f"- reject_low_rb: {active_filters['reject_low_rb']} | rb < {thresholds['min_rb']}",
            f"- reject_low_drb: {active_filters['reject_low_drb']} | drb < {thresholds['min_drb']}",
            "",
            "Photometric Activity",
            "-" * 40,
            "delta_mag = magpsf - ssmagnr",
            "anomaly_sigma = delta_mag / sqrt(sigmapsf^2 + model_sigma^2 + rotation_sigma^2)",
            f"- model_sigma = {thresholds['model_sigma']}",
            f"- rotation_sigma = {thresholds['rotation_sigma']}",
            f"- mild category: anomaly_sigma < {thresholds['anomaly_sigma_weak']}",
            f"- strong category: anomaly_sigma < {thresholds['anomaly_sigma_strong']}",
            f"- extreme category: anomaly_sigma < {thresholds['anomaly_sigma_extreme']}",
            "",
            "Category Flags",
            "-" * 40,
            f"- persistence enabled: {active_filters['score_persistence']} -> repeated_same_night / multi_night_activity",
            f"- morphology enabled: {active_filters['score_morphology']} -> morphology_extended / possible_contamination",
            f"- orbit context enabled: {active_filters['score_orbit_context']} -> known_sso tag only, no priority by itself",
            f"- heliocentric context enabled: {active_filters['score_heliocentric_trend']} -> near_snowline_activity if r <= {thresholds['heliocentric_near_limit_au']} AU",
            f"- penalties enabled: {active_filters['apply_penalties']} -> reasons only; final decision is category-based",
            "",
            "Final Review Level",
            "-" * 40,
            "normal: no activity category triggered",
            "review: one suspicious category, but weak confirmation or possible contamination",
            "interesting: strong photometric/persistence/morphology/context evidence",
            "urgent: strong anomaly plus persistence or heliocentric context",
            "Legacy priority is stored as activity_score only for sorting: normal=0, review=1, interesting=2, urgent=3.",
            "Saved candidates are interesting/urgent, not just known SSO matches.",
        ]
        if hasattr(self, "filter_info_text"):
            self.set_filter_info_text("\n".join(lines))

    def process_result_queue(self):
        try:
            while True:
                kind, payload = self.result_queue.get_nowait()

                if kind == "alerts":
                    request = payload.get("request", {})
                    if self.alert_request_matches_current(request):
                        self.current_alert_table = str(request.get("table_name") or "recent_alerts")
                        self.current_alert_request = dict(request)
                        rows = payload.get("rows", [])
                        self.apply_alert_rows(rows)
                        if self.is_default_recent_request(request):
                            self.start_worker(self.save_recent_alert_cache, rows)
                elif kind == "alerts_complete":
                    self.live_loading = False
                    if self.alert_refresh_pending:
                        self.alert_refresh_pending = False
                        self.root.after_idle(self.refresh_alerts)
                elif kind == "dashboard":
                    self.apply_dashboard(payload)
                elif kind == "saved_alerts":
                    self.apply_saved_alert_cache(payload)
                elif kind == "analysis_result":
                    self.apply_analysis_result(payload)
                elif kind == "notifications":
                    self.apply_notifications(payload)
                elif kind == "calibration":
                    self.apply_calibration(payload)
                elif kind == "detail_row":
                    self.apply_detail_row(payload)
                elif kind == "scoring_config":
                    self.apply_loaded_scoring_config(payload)
                elif kind == "sky_coverage":
                    self.apply_sky_coverage(payload)
                elif kind == "status":
                    self.connection_var.set(str(payload))
                elif kind == "table_status":
                    self.table_status_var.set(str(payload))
                elif kind == "analysis_status":
                    self.analysis_status_var.set(str(payload))
                elif kind == "analysis_progress":
                    self.apply_analysis_progress(payload)
                elif kind == "analysis_error":
                    self.analysis_loading = False
                    self.analysis_progress_var.set(0.0)
                    self.analysis_progress_text_var.set("Fehler")
                    self.hide_analysis_progress()
                    self.analysis_status_var.set("Deep Analysis failed.")
                    self.set_analysis_text(str(payload))
                elif kind == "error":
                    self.connection_var.set(f"Dashboard update delayed: {payload}  |  Live alerts may still be available.")

        except queue.Empty:
            pass

        self.root.after(250, self.process_result_queue)

    def start_worker(self, target, *args):
        thread = threading.Thread(target=target, args=args, daemon=True)
        thread.start()

    def apply_analysis_progress(self, payload):
        if isinstance(payload, dict):
            percent = to_float(payload.get("percent"))
            message = str(payload.get("message") or "").strip()
        else:
            percent = to_float(payload)
            message = ""
        if percent is not None:
            percent = max(0.0, min(100.0, percent))
            self.analysis_progress_var.set(percent)
            self.analysis_progress_text_var.set(f"{percent:.0f} %")
        if message:
            self.analysis_status_var.set(message)

    def queue_analysis_progress(self, percent: float, message: str):
        self.result_queue.put((
            "analysis_progress",
            {"percent": percent, "message": message},
        ))

    def show_analysis_progress(self):
        if not self.analysis_progress_row.winfo_manager():
            self.analysis_progress_row.pack(
                side=tk.TOP,
                fill=tk.X,
                pady=(0, 8),
                before=self.details_pane,
            )

    def hide_analysis_progress(self):
        if self.analysis_progress_row.winfo_manager():
            self.analysis_progress_row.pack_forget()

    def load_analysis_module(self):
        # Sandbox7 is standalone: Deep Analysis lives in this file.
        return None

    def use_selected_for_analysis(self):
        if self.latest_selected_row is None:
            self.analysis_status_var.set("No selected alert.")
            return

        survey = str(self.latest_selected_row.get("survey") or "").lower()
        match_status = str(self.latest_selected_row.get("sso_match_status") or "")
        confidence = to_float(self.latest_selected_row.get("match_confidence"))
        if survey == "lsst" and (
            not self.latest_selected_row.get("mpc_designation")
            or match_status not in {"known_mpc", "known_catalog", "mpc_matched"}
            or (match_status == "mpc_matched" and (confidence is None or confidence < 0.90))
        ):
            self.analysis_status_var.set(
                "No sufficiently secure MPC match yet. Retry the MPC match before Deep Analysis."
            )
            return

        sso_id = (
            self.latest_selected_row.get("mpc_designation")
            or self.latest_selected_row.get("sso_id")
        )
        if sso_id is None or str(sso_id).strip() == "":
            self.analysis_status_var.set("Selected alert has no SSO ID.")
            return

        self.analysis_sso_var.set(str(sso_id))

    def retry_selected_mpc_match(self):
        row = self.latest_selected_row
        if not row or str(row.get("survey") or "").lower() != "lsst":
            self.analysis_status_var.set("Select an LSST alert first.")
            return
        try:
            alert_id = int(row.get("id"))
        except (TypeError, ValueError):
            self.analysis_status_var.set("Selected LSST alert has no valid database ID.")
            return
        self.analysis_status_var.set(f"Scheduling MPC retry for LSST alert {alert_id}...")
        self.start_worker(self.worker_retry_mpc_match, alert_id)

    def worker_retry_mpc_match(self, alert_id: int):
        timestamp = datetime.now(timezone.utc).isoformat()
        safe_timestamp = safe_sql_text(timestamp)
        sql = (
            "BEGIN IMMEDIATE; "
            "UPDATE lsst_sso_alerts SET mpc_designation=NULL, "
            "sso_id=CASE WHEN rubin_ssobject_id IS NOT NULL THEN rubin_ssobject_id ELSE NULL END, "
            "sso_match_status='mpc_pending', match_method=NULL, match_confidence=NULL, "
            "match_separation_arcsec=NULL, match_candidate_count=NULL, match_checked_utc=NULL, "
            "match_error=NULL WHERE id={alert_id}; "
            "INSERT INTO mpc_crossmatch_queue(lsst_alert_id,status,attempts,next_attempt_utc,last_error,created_utc,updated_utc) "
            "VALUES({alert_id},'pending',0,'{timestamp}',NULL,'{timestamp}','{timestamp}') "
            "ON CONFLICT(lsst_alert_id) DO UPDATE SET status='pending',attempts=0,"
            "next_attempt_utc=excluded.next_attempt_utc,last_error=NULL,updated_utc=excluded.updated_utc; "
            "COMMIT;"
        ).format(alert_id=alert_id, timestamp=safe_timestamp)
        command = f"sqlite3 {shlex.quote(DB_PATH)} {shlex.quote(sql)}"
        try:
            run_ssh(command, timeout=20)
            self.result_queue.put(("analysis_status", f"MPC retry queued for LSST alert {alert_id}."))
            self.root.after(2000, self.refresh_alerts)
        except Exception as exc:
            self.result_queue.put(("analysis_status", f"Could not queue MPC retry: {exc}"))

    def start_deep_analysis(self):
        if self.analysis_loading:
            self.analysis_status_var.set("Deep Analysis is already running.")
            return

        sso_id = self.analysis_sso_var.get().strip()
        if not sso_id:
            self.use_selected_for_analysis()
            sso_id = self.analysis_sso_var.get().strip()

        if not sso_id:
            self.analysis_status_var.set("Enter an SSO ID first.")
            return

        selected = self.latest_selected_row
        if selected and str(selected.get("survey") or "").lower() == "lsst":
            selected_ids = {
                comparable_sso_id(selected.get("sso_id")),
                comparable_sso_id(selected.get("mpc_designation")),
            }
            if comparable_sso_id(sso_id) in selected_ids:
                status = str(selected.get("sso_match_status") or "")
                confidence = to_float(selected.get("match_confidence"))
                if (
                    not selected.get("mpc_designation")
                    or status not in {"known_mpc", "known_catalog", "mpc_matched"}
                    or (status == "mpc_matched" and (confidence is None or confidence < 0.90))
                ):
                    self.analysis_status_var.set(
                        "Deep Analysis blocked: selected LSST alert has no secure MPC match."
                    )
                    return

        self.analysis_loading = True
        self.show_analysis_progress()
        self.analysis_progress_var.set(2.0)
        self.analysis_progress_text_var.set("2 %")
        self.current_figures = []
        self.plot_combo["values"] = []
        self.clear_plot()
        self.set_analysis_text(f"Running Deep Analysis for {sso_id}...")
        self.analysis_status_var.set(f"Running Deep Analysis for {sso_id}...")
        injected_alerts = self.build_injected_alerts_for_analysis(sso_id)
        self.start_worker(
            self.worker_deep_analysis,
            sso_id,
            self.include_period_plots_var.get(),
            injected_alerts,
        )

    def build_injected_alerts_for_analysis(self, sso_id: str) -> list[dict]:
        if self.latest_selected_row is None:
            return []

        row = dict(self.latest_selected_row)
        row_json = row.get("row_json")

        try:
            full = json.loads(row_json) if row_json else row
        except json.JSONDecodeError:
            full = row

        if not isinstance(full, dict):
            return []

        for key, value in row.items():
            full.setdefault(key, value)
        full["_source_table"] = self.current_alert_table

        selected_sso = str(full.get("sso_id") or "").strip()
        if selected_sso and comparable_sso_id(selected_sso) != comparable_sso_id(sso_id):
            return []

        if full.get("jd") is None or full.get("magpsf") is None:
            return []

        return [full]

    def load_embedded_cutouts_for_analysis(self, alert: dict) -> None:
        if isinstance(alert.get("alert_cutouts"), dict):
            return
        table_name = str(alert.get("_source_table") or "")
        if table_name not in {"recent_alerts", "alerts", "lsst_sso_alerts"}:
            return
        try:
            row_id = int(alert.get("id"))
        except (TypeError, ValueError):
            return
        sql = f"""
            SELECT json_extract(row_json, '$.alert_cutouts') AS alert_cutouts
            FROM {table_name}
            WHERE id = {row_id}
            LIMIT 1;
        """
        try:
            rows = sqlite_json(sql, timeout=20)
            raw_cutouts = rows[0].get("alert_cutouts") if rows else None
            if isinstance(raw_cutouts, str):
                raw_cutouts = json.loads(raw_cutouts)
            if isinstance(raw_cutouts, dict):
                alert["alert_cutouts"] = raw_cutouts
        except Exception:
            return

    def load_cutout_history_for_analysis(
        self,
        alert: dict,
        max_epochs: int = 8,
        similar_parameters: bool = False,
        include_remote: bool = True,
    ) -> list[dict]:
        sso_id = str(alert.get("sso_id") or "").strip()
        object_id = str(alert.get("object_id") or "").strip()
        if sso_id:
            predicate = f"sso_id = '{safe_sql_text(sso_id)}'"
        elif object_id:
            predicate = f"object_id = '{safe_sql_text(object_id)}'"
        else:
            return []
        limit = max(
            1,
            min(int(max_epochs), CUTOUT_GENERAL_CANDIDATE_POOL),
        )
        candidate_limit = max(200, limit * 25)
        sql = f"""
            SELECT received_utc, object_id, sso_id, jd, fid, magpsf, sigmapsf,
                   Dhelio, Dobs, Phase, alert_cutouts
            FROM (
                SELECT
                    received_utc, object_id, sso_id, jd, fid, magpsf, sigmapsf,
                    json_extract(row_json, '$.Dhelio') AS Dhelio,
                    json_extract(row_json, '$.Dobs') AS Dobs,
                    json_extract(row_json, '$.Phase') AS Phase,
                    json_extract(row_json, '$.alert_cutouts') AS alert_cutouts
                FROM recent_alerts
                WHERE {predicate}
                  AND json_type(row_json, '$.alert_cutouts') = 'object'
                UNION
                SELECT
                    received_utc, object_id, sso_id, jd, fid, magpsf, sigmapsf,
                    json_extract(row_json, '$.Dhelio') AS Dhelio,
                    json_extract(row_json, '$.Dobs') AS Dobs,
                    json_extract(row_json, '$.Phase') AS Phase,
                    json_extract(row_json, '$.alert_cutouts') AS alert_cutouts
                FROM alerts
                WHERE {predicate}
                  AND json_type(row_json, '$.alert_cutouts') = 'object'
            )
            ORDER BY coalesce(jd, 0) DESC, received_utc DESC
            LIMIT {candidate_limit};
        """
        try:
            rows = sqlite_json(sql, timeout=35)
        except Exception:
            return []
        history = []
        for row in reversed(rows):
            raw_cutouts = row.get("alert_cutouts")
            if isinstance(raw_cutouts, str):
                try:
                    raw_cutouts = json.loads(raw_cutouts)
                except json.JSONDecodeError:
                    continue
            if isinstance(raw_cutouts, dict):
                row["alert_cutouts"] = raw_cutouts
                history.append(row)

        survey = str(alert.get("survey") or "").lower()
        is_ztf = survey == "ztf" or object_id.upper().startswith("ZTF")
        if include_remote and is_ztf and sso_id:
            remote_history = load_fink_ztf_cutout_history(
                sso_id,
                max_epochs=max(2, limit),
                reference=alert if similar_parameters else None,
            )
        elif include_remote and is_ztf and object_id:
            remote_history = load_fink_ztf_object_cutout_history(
                object_id,
                max_epochs=max(2, limit),
                reference=alert if similar_parameters else None,
            )
        else:
            remote_history = []

        merged = {}
        source_rows = remote_history + history
        if isinstance(alert.get("alert_cutouts"), dict):
            source_rows.append(dict(alert))
        for row in source_rows:
            jd = to_float(row.get("jd"))
            if jd is not None:
                key = ("jd", round(jd, 6))
            else:
                key = (
                    "received",
                    str(row.get("received_utc") or ""),
                    str(row.get("object_id") or ""),
                )
            merged[key] = row
        combined = sorted(
            merged.values(),
            key=lambda row: (
                to_float(row.get("jd")) or float("inf"),
                str(row.get("received_utc") or ""),
            ),
        )
        if similar_parameters:
            return select_cutout_geometry_matches(combined, alert, limit)
        return select_general_cutout_epochs(combined, alert, limit)

    def load_shared_cutout_histories_for_analysis(
        self,
        alert: dict,
        sso_id: str,
    ) -> tuple[list[dict], list[dict]]:
        object_id = str(alert.get("object_id") or "").strip()
        stored_history = self.load_cutout_history_for_analysis(
            alert,
            max_epochs=CUTOUT_GENERAL_CANDIDATE_POOL,
            similar_parameters=False,
            include_remote=False,
        )

        survey = str(alert.get("survey") or "").lower()
        is_ztf = survey == "ztf" or object_id.upper().startswith("ZTF")
        remote_metadata = (
            fetch_fink_cutout_candidates(
                sso_id=sso_id if is_ztf else "",
                object_id=object_id if is_ztf else "",
            )
            if is_ztf
            else []
        )

        master = merge_cutout_histories(
            remote_metadata,
            stored_history,
            [dict(alert)],
        )
        master = enrich_cutout_history_with_horizons(sso_id, master)

        # Merge remote metadata back into the selected alert. This supplies the
        # candid and Fink geometry when the cached dashboard row only contains
        # object_id, jd, and photometry.
        for row in master:
            if is_same_cutout_alert(row, alert):
                for field in (
                    "candid", "fid", "Dhelio", "Dobs", "Phase",
                    "object_id", "received_utc",
                ):
                    if alert.get(field) in (None, "") and row.get(field) not in (None, ""):
                        alert[field] = row.get(field)
                if not isinstance(alert.get("alert_cutouts"), dict):
                    if isinstance(row.get("alert_cutouts"), dict):
                        alert["alert_cutouts"] = row["alert_cutouts"]
                break

        general_pool = select_general_cutout_epochs(
            master,
            alert,
            CUTOUT_GENERAL_CANDIDATE_POOL,
        )
        similar_pool = select_cutout_geometry_matches(
            master,
            alert,
            CUTOUT_SIMILAR_CANDIDATE_POOL,
        )
        cached_pool = []
        for row in master:
            candid = str(row.get("candid") or "").strip()
            if not candid:
                continue
            cache_path = CUTOUT_HISTORY_CACHE_DIR / f"{candid}_Science.npz"
            if cache_path.exists():
                cached_pool.append(row)
        cached_pool = evenly_spaced_rows(
            cached_pool,
            CUTOUT_GENERAL_CANDIDATE_POOL,
        )

        download_pool = merge_cutout_histories(
            cached_pool,
            general_pool,
            similar_pool,
        )
        already_loaded = []
        need_download = []
        for row in download_pool:
            cutouts = row.get("alert_cutouts")
            science = (
                image_array_from_embedded_cutout(cutouts.get("Science"))
                if isinstance(cutouts, dict)
                else None
            )
            if science is not None:
                already_loaded.append(row)
            elif row.get("object_id") and row.get("candid") not in (None, ""):
                need_download.append(row)

        downloaded = load_cutouts_for_candidates(need_download)
        loaded_master = merge_cutout_histories(
            already_loaded,
            downloaded,
        )
        for row in loaded_master:
            if is_same_cutout_alert(row, alert):
                if isinstance(row.get("alert_cutouts"), dict):
                    current_cutouts = dict(row["alert_cutouts"])
                    if (
                        current_cutouts.get("Difference") is None
                        and row.get("object_id")
                        and row.get("candid") not in (None, "")
                    ):
                        current_cutouts["Difference"] = cached_fink_cutout_array(
                            row.get("object_id"),
                            row.get("candid"),
                            "Difference",
                        )
                    row["alert_cutouts"] = current_cutouts
                    alert["alert_cutouts"] = current_cutouts
                if alert.get("candid") in (None, "") and row.get("candid") not in (None, ""):
                    alert["candid"] = row.get("candid")
                break

        similar_history = select_cutout_geometry_matches(
            loaded_master,
            alert,
            CUTOUT_HISTORY_MAX_EPOCHS,
        )
        general_history = select_general_with_required(
            loaded_master,
            similar_history,
            alert,
            CUTOUT_GENERAL_MAX_EPOCHS,
        )
        return general_history, similar_history

    def worker_deep_analysis(self, sso_id: str, include_period_plots: bool, injected_alerts: list[dict]):
        try:
            self.queue_analysis_progress(5, f"Preparing Deep Analysis for {sso_id}...")
            cutout_history = []
            similar_cutout_history = []
            if injected_alerts:
                self.queue_analysis_progress(12, "Loading selected alert and cutouts...")
                self.load_embedded_cutouts_for_analysis(injected_alerts[0])
            self.queue_analysis_progress(
                22,
                "Loading photometry, ephemerides, and cutouts in parallel...",
            )
            with ThreadPoolExecutor(max_workers=2) as pool:
                analysis_future = pool.submit(
                    analyze_sso_deep,
                    sso_id,
                    include_period_plots,
                    injected_alerts,
                )
                cutout_future = (
                    pool.submit(
                        self.load_shared_cutout_histories_for_analysis,
                        injected_alerts[0],
                        sso_id,
                    )
                    if injected_alerts
                    else None
                )
                if cutout_future is not None:
                    cutout_history, similar_cutout_history = cutout_future.result()
                self.queue_analysis_progress(
                    65,
                    "Cutouts ready; finishing scientific analysis...",
                )
                result = analysis_future.result()
            self.queue_analysis_progress(82, "Preparing analysis plots...")
            if injected_alerts:
                self.queue_analysis_progress(87, "Rendering alert cutouts...")
                cutout_figure = build_alert_cutout_figure(injected_alerts[0])
                self.queue_analysis_progress(90, "Rendering general cutout evolution...")
                evolution_figure = build_cutout_evolution_figure(
                    cutout_history,
                    reference=injected_alerts[0],
                    similar_parameters=False,
                )
                self.queue_analysis_progress(94, "Rendering similar-parameter cutouts...")
                similar_evolution_figure = build_cutout_evolution_figure(
                    similar_cutout_history,
                    reference=injected_alerts[0],
                    similar_parameters=True,
                )
                figures = list(result.get("figures", []))
                insert_at = 1 if figures else 0
                if cutout_figure is not None:
                    figures.insert(insert_at, cutout_figure)
                    insert_at += 1
                if evolution_figure is not None:
                    figures.insert(insert_at, evolution_figure)
                    insert_at += 1
                if similar_evolution_figure is not None:
                    figures.insert(insert_at, similar_evolution_figure)
                if (
                    cutout_figure is not None
                    or evolution_figure is not None
                    or similar_evolution_figure is not None
                ):
                    result["figures"] = figures
            self.queue_analysis_progress(98, "Finalizing Deep Analysis...")
            self.result_queue.put(("analysis_result", result))
        except Exception:
            self.result_queue.put(("analysis_error", traceback.format_exc()))
        finally:
            self.analysis_loading = False

    def apply_analysis_result(self, result: dict):
        self.analysis_loading = False
        self.analysis_progress_var.set(100.0)
        self.analysis_progress_text_var.set("100 %")
        self.hide_analysis_progress()
        self.current_figures = result.get("figures", [])
        self.set_analysis_text(result.get("summary_text", "No summary returned."))
        self.analysis_status_var.set(f"Deep Analysis complete for {result.get('sso_id')}.")

        plot_names = [name for name, _figure in self.current_figures]
        self.plot_combo["values"] = plot_names
        if plot_names:
            selected_idx = 0

            if self.preferred_plot_name in plot_names:
                selected_idx = plot_names.index(self.preferred_plot_name)
            elif 0 <= self.preferred_plot_index < len(plot_names):
                selected_idx = self.preferred_plot_index

            self.plot_combo.current(selected_idx)
            self.show_plot_by_index(selected_idx)

    def on_plot_select(self, _event=None):
        idx = self.plot_combo.current()
        if idx >= 0:
            self.show_plot_by_index(idx)

    def clear_plot(self):
        if self.current_toolbar is not None:
            self.current_toolbar.destroy()
            self.current_toolbar = None

        if self.current_canvas is not None:
            self.current_canvas.get_tk_widget().destroy()
            self.current_canvas = None

        for child in self.plot_frame.winfo_children():
            child.destroy()

    def style_live_markers_in_figure(self, figure):
        """
        Style injected live-alert points locally in this viewer.

        The deep-analysis function returns Matplotlib figures. If the selected
        live alert was injected, it is plotted with label "Live". We restyle that
        artist here so this file controls the visual highlight.
        """
        for ax in figure.axes:
            changed = False
            reference_size = None

            for collection in ax.collections:
                if str(collection.get_label()) == "Live":
                    continue

                try:
                    sizes = collection.get_sizes()
                except Exception:
                    continue

                if sizes is not None and len(sizes) > 0:
                    reference_size = float(sizes[0])
                    break

            for collection in ax.collections:
                if str(collection.get_label()) != "Live":
                    continue

                try:
                    collection.set_facecolor("red")
                    collection.set_edgecolor("none")
                    collection.set_zorder(30)
                    if reference_size is not None:
                        offsets = collection.get_offsets()
                        n_points = len(offsets) if offsets is not None else 1
                        collection.set_sizes([reference_size] * max(n_points, 1))
                    changed = True
                except Exception:
                    continue

            if changed:
                handles, labels = ax.get_legend_handles_labels()
                if labels:
                    ax.legend(handles, labels)

    def prepare_figure_for_display(self, figure):
        frame_width = max(self.plot_frame.winfo_width(), 1000)
        frame_height = max(self.plot_frame.winfo_height() - 70, 620)
        dpi = figure.get_dpi() or 100
        figure.set_size_inches(frame_width / dpi, frame_height / dpi, forward=True)
        if getattr(figure, "_astroprak_preserve_layout", False):
            return

        for ax in figure.axes:
            title = ax.get_title()
            if title:
                ax.set_title(title, fontsize=13, pad=12)

            ax.xaxis.label.set_size(11)
            ax.yaxis.label.set_size(11)
            ax.tick_params(axis="both", which="major", labelsize=10, pad=4)
            ax.tick_params(axis="both", which="minor", labelsize=9, pad=3)

            legend = ax.get_legend()
            if legend is not None:
                for text in legend.get_texts():
                    text.set_fontsize(10)
                try:
                    legend.set_frame_alpha(0.82)
                except Exception:
                    pass

        try:
            figure.subplots_adjust(
                left=0.098,
                right=0.985,
                bottom=0.13,
                top=0.917,
                wspace=0.25,
                hspace=0.28,
            )
        except Exception:
            try:
                figure.tight_layout(pad=2.4)
            except Exception:
                pass

    def show_plot_by_index(self, idx: int):
        if idx < 0 or idx >= len(self.current_figures):
            return

        name, figure = self.current_figures[idx]
        self.preferred_plot_index = idx
        self.preferred_plot_name = name
        self.clear_plot()
        self.set_details_plot_ratio()
        self.style_live_markers_in_figure(figure)
        self.plot_frame.update_idletasks()
        self.prepare_figure_for_display(figure)

        canvas = FigureCanvasTkAgg(figure, master=self.plot_frame)
        canvas.draw()
        toolbar = NavigationToolbar2Tk(canvas, self.plot_frame, pack_toolbar=False)
        toolbar.update()
        toolbar.pack(side=tk.TOP, fill=tk.X)
        canvas.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.current_canvas = canvas
        self.current_toolbar = toolbar

    def refresh_dashboard(self):
        if self.dashboard_loading:
            return
        self.dashboard_loading = True
        now = time.monotonic()
        refresh_saved_alert_cache = (
            now - self.saved_alert_cache_last_refresh
            >= SAVED_ALERT_CACHE_REFRESH_SECONDS
        )
        if refresh_saved_alert_cache:
            self.saved_alert_cache_last_refresh = now
        show_all_days = self.show_all_days.get()
        self.start_worker(self.worker_dashboard, show_all_days, refresh_saved_alert_cache)

    def default_recent_request(self) -> dict:
        return {
            "limit": self.get_limit(),
            "class_filter": "all",
            "category_filter": "all",
            "table_name": "recent_alerts",
        }

    def table_name_for_view(self) -> str:
        mode = self.view_mode_var.get()
        if mode == "interesting saved":
            return "alerts"
        if mode in {"LSST SSO matched", "LSST SSO all"}:
            return "lsst_sso_alerts"
        return "recent_alerts"

    @staticmethod
    def is_default_recent_request(request: dict) -> bool:
        return (
            request.get("table_name") == "recent_alerts"
            and request.get("class_filter") == "all"
            and request.get("category_filter") == "all"
        )

    def load_recent_alert_cache(self):
        try:
            with gzip.open(RECENT_ALERT_CACHE_PATH, "rt", encoding="utf-8") as handle:
                payload = json.load(handle)
            rows = payload.get("rows", []) if isinstance(payload, dict) else []
            stats = payload.get("stats", {}) if isinstance(payload, dict) else {}
            saved_alerts = payload.get("saved_alerts", {}) if isinstance(payload, dict) else {}
            if not isinstance(rows, list):
                rows = []
            if isinstance(saved_alerts, dict):
                self.cached_saved_alerts = {
                    key: value[:DEFAULT_LIMIT]
                    for key, value in saved_alerts.items()
                    if key in {"interesting", "photometric", "matched_lsst"} and isinstance(value, list)
                }
                if self.cached_saved_alerts:
                    self.saved_alert_cache_last_refresh = time.monotonic()
            if not rows and not stats and not self.cached_saved_alerts:
                return
            if rows:
                request = self.default_recent_request()
                self.current_alert_table = "recent_alerts"
                self.current_alert_request = request
                self.apply_alert_rows(rows[: request["limit"]])
                self.table_status_var.set(
                    f"Showing {min(len(rows), request['limit'])} cached alerts. Live server refresh starts after startup."
                )
            if isinstance(stats, dict) and stats:
                self.apply_dashboard_stats(stats)
                saved_utc = str(payload.get("saved_utc") or "")
                cached_at = fmt_german_time(saved_utc) if saved_utc else "earlier"
                self.connection_var.set(f"Showing cached server data from {cached_at}; reconnecting...")
            elif rows:
                fallback_counts = {
                    row["category"]: row["count"]
                    for row in self.compute_category_rows(rows)
                    if row["category"] in {"interesting", "photometric"}
                }
                for key, count in fallback_counts.items():
                    self.category_count_vars[key].set(fmt_int(count))
        except (FileNotFoundError, OSError, json.JSONDecodeError, TypeError):
            return

    @staticmethod
    def merge_recent_alert_cache(updates: dict):
        temp_path = RECENT_ALERT_CACHE_PATH.with_suffix(RECENT_ALERT_CACHE_PATH.suffix + ".tmp")
        try:
            with RECENT_ALERT_CACHE_LOCK:
                payload = {}
                try:
                    with gzip.open(RECENT_ALERT_CACHE_PATH, "rt", encoding="utf-8") as handle:
                        existing = json.load(handle)
                    if isinstance(existing, dict):
                        payload.update(existing)
                except (FileNotFoundError, OSError, json.JSONDecodeError, TypeError):
                    pass
                payload.update(updates)
                payload["saved_utc"] = datetime.now(timezone.utc).isoformat()
                with gzip.open(temp_path, "wt", encoding="utf-8", compresslevel=5) as handle:
                    json.dump(
                        payload,
                        handle,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    )
                temp_path.replace(RECENT_ALERT_CACHE_PATH)
        except OSError:
            try:
                temp_path.unlink(missing_ok=True)
            except OSError:
                pass

    @staticmethod
    def save_recent_alert_cache(rows: list[dict]):
        ServerAlertDashboard.merge_recent_alert_cache({"rows": rows[:DEFAULT_LIMIT]})

    @staticmethod
    def save_dashboard_cache(stats: dict):
        ServerAlertDashboard.merge_recent_alert_cache({"stats": stats})

    @staticmethod
    def save_saved_alert_cache(saved_alerts: dict[str, list[dict]]):
        ServerAlertDashboard.merge_recent_alert_cache({"saved_alerts": saved_alerts})

    def refresh_alerts(self, queue_if_busy=True):
        if self.live_loading:
            if queue_if_busy:
                self.alert_refresh_pending = True
            return
        request = {
            "limit": self.get_limit(),
            "class_filter": self.class_filter_var.get(),
            "category_filter": self.category_filter_var.get(),
            "table_name": self.table_name_for_view(),
        }
        self.live_loading = True
        self.start_worker(self.worker_alerts, request)

    def refresh_from_server(self):
        self.connection_var.set("Refreshing server connection...")
        self.table_status_var.set("Refreshing live alerts...")
        self.refresh_dashboard()
        self.refresh_alerts()
        self.refresh_sky_coverage()
        self.refresh_notifications()
        self.refresh_calibration()
        self.load_server_scoring_config()

    def refresh_notifications(self):
        if self.notifications_loading:
            return
        self.notifications_loading = True
        self.start_worker(self.worker_notifications)

    def refresh_calibration(self):
        if self.calibration_loading:
            return
        self.calibration_loading = True
        self.start_worker(self.worker_calibration)

    def refresh_sky_coverage(self):
        if self.sky_loading:
            return
        self.sky_loading = True
        self.sky_status_var.set("Loading sky coverage from server...")
        where = self.sky_time_where_clause()
        self.start_worker(self.worker_sky_coverage, where)

    def sky_time_where_clause(self) -> str:
        value = self.sky_time_filter_var.get()
        if value == "last night":
            return "WHERE julianday(replace(substr(received_utc, 1, 19), 'T', ' ')) >= julianday('now', '-1 day')"
        elif value == "last 7 days":
            return "WHERE julianday(replace(substr(received_utc, 1, 19), 'T', ' ')) >= julianday('now', '-7 days')"
        elif value == "last 30 days":
            return "WHERE julianday(replace(substr(received_utc, 1, 19), 'T', ' ')) >= julianday('now', '-30 days')"
        else:
            return ""

    def worker_sky_coverage(self, where: str):
        try:
            sql = f"""
                SELECT *
                FROM (
                    SELECT
                        id,
                        received_utc,
                        survey,
                        observer,
                        coalesce(ra, json_extract(row_json, '$.ra')) AS ra,
                        coalesce(dec, json_extract(row_json, '$.dec')) AS dec,
                        sso_id,
                        object_id,
                        activity_class,
                        primary_category,
                        'recent_alerts' AS source_table
                    FROM recent_alerts
                    WHERE coalesce(ra, json_extract(row_json, '$.ra')) IS NOT NULL
                      AND coalesce(dec, json_extract(row_json, '$.dec')) IS NOT NULL
                    UNION ALL
                    SELECT
                        id,
                        received_utc,
                        survey,
                        observer,
                        coalesce(ra, json_extract(row_json, '$.ra')) AS ra,
                        coalesce(dec, json_extract(row_json, '$.dec')) AS dec,
                        sso_id,
                        object_id,
                        activity_class,
                        primary_category,
                        'alerts' AS source_table
                    FROM alerts
                    WHERE coalesce(ra, json_extract(row_json, '$.ra')) IS NOT NULL
                      AND coalesce(dec, json_extract(row_json, '$.dec')) IS NOT NULL
                )
                {where}
                ORDER BY received_utc DESC
                LIMIT 8000;
            """
            rows = sqlite_json(sql, timeout=25)
            note = ""
            if not rows and where:
                fallback_sql = """
                    SELECT
                        id,
                        received_utc,
                        survey,
                        observer,
                        coalesce(ra, json_extract(row_json, '$.ra')) AS ra,
                        coalesce(dec, json_extract(row_json, '$.dec')) AS dec,
                        sso_id,
                        object_id,
                        activity_class,
                        primary_category,
                        'recent_alerts' AS source_table
                    FROM recent_alerts
                    WHERE coalesce(ra, json_extract(row_json, '$.ra')) IS NOT NULL
                      AND coalesce(dec, json_extract(row_json, '$.dec')) IS NOT NULL
                    ORDER BY received_utc DESC
                    LIMIT 8000;
                """
                rows = sqlite_json(fallback_sql, timeout=25)
                note = " | time filter returned no rows; showing recent buffer"
            self.result_queue.put(("sky_coverage", {"rows": rows, "note": note}))
        except Exception as exc:
            self.result_queue.put(("sky_coverage", {"error": str(exc)}))
        finally:
            self.sky_loading = False

    def apply_sky_coverage(self, payload):
        if isinstance(payload, dict) and payload.get("error"):
            self.sky_status_var.set(f"Could not load sky coverage: {payload.get('error')}")
            return

        if isinstance(payload, dict):
            self.current_sky_rows = list(payload.get("rows") or [])
            self.sky_status_note = str(payload.get("note") or "")
        else:
            self.current_sky_rows = list(payload or [])
            self.sky_status_note = ""
        self.draw_sky_coverage()

    @staticmethod
    def ra_to_aitoff_x(ra_deg):
        ra = np.asarray(ra_deg, dtype=float)
        wrapped = (ra + 180.0) % 360.0 - 180.0
        return -np.radians(wrapped)

    @staticmethod
    def dec_to_aitoff_y(dec_deg):
        return np.radians(np.asarray(dec_deg, dtype=float))

    @staticmethod
    def aitoff_x_to_ra(x_rad):
        deg = -np.degrees(float(x_rad))
        return (deg + 360.0) % 360.0

    @staticmethod
    def aitoff_y_to_dec(y_rad):
        return np.degrees(float(y_rad))

    def draw_sky_coverage(self):
        if not hasattr(self, "sky_figure"):
            return

        self.sky_figure.clear()
        ax = self.sky_figure.add_subplot(111, projection="aitoff")
        ax.set_facecolor("#f8fafc")
        self.sky_hover_points = []

        rows = self.current_sky_rows
        valid_rows = []
        for row in rows:
            ra = to_float(row.get("ra"))
            dec = to_float(row.get("dec"))
            if ra is None or dec is None or dec < -90 or dec > 90:
                continue
            valid_rows.append(row)

        if not valid_rows:
            ax.text(0.5, 0.5, "No RA/Dec rows available for this filter.", ha="center", va="center", transform=ax.transAxes)
            ax.grid(True, alpha=0.35)
            self.sky_canvas.draw_idle()
            self.sky_status_var.set("Sky coverage: no coordinate rows for current filter.")
            return

        ra = np.array([float(row.get("ra")) for row in valid_rows])
        dec = np.array([float(row.get("dec")) for row in valid_rows])
        x = self.ra_to_aitoff_x(ra)
        y = self.dec_to_aitoff_y(dec)
        surveys = np.array([str(row.get("survey") or row.get("observer") or "unknown").lower() for row in valid_rows])
        timestamps = pd.to_datetime(
            [row.get("received_utc") for row in valid_rows],
            errors="coerce",
            utc=True,
        )
        valid_times = timestamps[~pd.isna(timestamps)]
        if len(valid_times):
            newest = valid_times.max()
            ages_days = np.array([
                max(0.0, (newest - ts).total_seconds() / 86400.0) if not pd.isna(ts) else 999.0
                for ts in timestamps
            ])
            age_span = max(float(np.nanmax(ages_days)), 1.0)
            age_alpha = 0.18 + 0.72 * (1.0 - np.clip(ages_days / age_span, 0.0, 1.0))
        else:
            age_alpha = np.full(len(valid_rows), 0.6)

        mode = self.sky_view_mode_var.get()
        if mode == "heatmap":
            hb = ax.hexbin(
                x,
                y,
                gridsize=55,
                cmap="viridis",
                mincnt=1,
                linewidths=0,
                alpha=0.88,
            )
            cbar = self.sky_figure.colorbar(hb, ax=ax, orientation="horizontal", pad=0.08, fraction=0.05)
            cbar.set_label("Number of stored pointings / alert centers")
            ztf_mask = np.array(["ztf" in survey for survey in surveys])
            lsst_mask = np.array(["lsst" in survey for survey in surveys])
            if np.any(ztf_mask):
                ax.scatter(x[ztf_mask], y[ztf_mask], s=3, color="#60a5fa", alpha=0.18, label="ZTF centers")
            if np.any(lsst_mask):
                ax.scatter(x[lsst_mask], y[lsst_mask], s=3, color="#fb923c", alpha=0.18, label="LSST centers")
        else:
            ztf_mask = np.array(["ztf" in survey for survey in surveys])
            lsst_mask = np.array(["lsst" in survey for survey in surveys])
            other_mask = ~(ztf_mask | lsst_mask)
            if np.any(ztf_mask):
                ax.scatter(x[ztf_mask], y[ztf_mask], s=12, color="#2563eb", alpha=age_alpha[ztf_mask], label=f"ZTF ({np.sum(ztf_mask)})")
            if np.any(lsst_mask):
                ax.scatter(x[lsst_mask], y[lsst_mask], s=16, color="#f97316", alpha=age_alpha[lsst_mask], label=f"LSST ({np.sum(lsst_mask)})")
            if np.any(other_mask):
                ax.scatter(x[other_mask], y[other_mask], s=10, color="#6b7280", alpha=age_alpha[other_mask], label=f"Other ({np.sum(other_mask)})")

        if self.sky_show_selected_var.get() and self.latest_selected_row is not None:
            selected_ra = to_float(self.latest_selected_row.get("ra"))
            selected_dec = to_float(self.latest_selected_row.get("dec"))
            if selected_ra is not None and selected_dec is not None:
                sx = self.ra_to_aitoff_x([selected_ra])[0]
                sy = self.dec_to_aitoff_y([selected_dec])[0]
                ax.scatter([sx], [sy], s=90, marker="*", color="red", edgecolors="black", linewidths=0.8, label="Selected alert")

        for row, xx, yy in zip(valid_rows, x, y):
            self.sky_hover_points.append({
                "x": float(xx),
                "y": float(yy),
                "ra": float(row.get("ra")),
                "dec": float(row.get("dec")),
                "time": row.get("received_utc"),
                "survey": row.get("survey") or row.get("observer"),
                "object_id": row.get("object_id"),
                "sso_id": row.get("sso_id"),
            })

        ax.grid(True, alpha=0.38)
        ax.set_title("Sky Coverage: stored ZTF/LSST pointing centers (older points fade out)", pad=14)
        ax.set_xlabel("Right Ascension")
        ax.set_ylabel("Declination")
        ax.set_xticklabels(["10h", "8h", "6h", "4h", "2h", "0h", "22h", "20h", "18h", "16h", "14h"])
        ax.legend(loc="lower center", bbox_to_anchor=(0.5, -0.18), ncol=4)
        self.sky_figure.subplots_adjust(left=0.04, right=0.98, top=0.88, bottom=0.20)
        self.sky_canvas.draw_idle()

        ztf_count = int(np.sum(["ztf" in survey for survey in surveys]))
        lsst_count = int(np.sum(["lsst" in survey for survey in surveys]))
        self.sky_status_var.set(
            f"Sky coverage: {len(valid_rows)} stored centers | ZTF {ztf_count} | LSST {lsst_count} | {self.sky_time_filter_var.get()} | older centers are faded"
            + str(getattr(self, "sky_status_note", ""))
        )

    def on_sky_mouseover(self, event):
        if event.inaxes is None or event.xdata is None or event.ydata is None:
            return

        ra = self.aitoff_x_to_ra(event.xdata)
        dec = self.aitoff_y_to_dec(event.ydata)
        message = f"RA {ra:.2f} deg | Dec {dec:.2f} deg"

        if self.sky_hover_points:
            dx_scale = np.cos(event.ydata)
            distances = [
                ((point["x"] - event.xdata) * dx_scale) ** 2 + (point["y"] - event.ydata) ** 2
                for point in self.sky_hover_points
            ]
            idx = int(np.argmin(distances))
            if distances[idx] < 0.0025:
                point = self.sky_hover_points[idx]
                message = (
                    f"{point['survey']} | {fmt_german_time(point['time'])} DE | "
                    f"RA {point['ra']:.3f} deg, Dec {point['dec']:.3f} deg | "
                    f"SSO {point.get('sso_id') or ''} {point.get('object_id') or ''}"
                )

        self.sky_status_var.set(message)

    def worker_notifications(self):
        try:
            sql = """
                SELECT id, created_utc, severity, primary_category,
                       activity_score, sso_id, object_id, message
                FROM notifications
                ORDER BY id DESC
                LIMIT 300;
            """
            self.result_queue.put(("notifications", sqlite_json(sql, timeout=20)))
        except Exception as exc:
            self.result_queue.put(("table_status", f"Could not load notifications: {exc}"))
        finally:
            self.notifications_loading = False

    def worker_calibration(self):
        try:
            sql = """
                SELECT key, count, interesting_count, best_score, last_seen_utc
                FROM calibration_stats
                ORDER BY count DESC, key ASC
                LIMIT 500;
            """
            self.result_queue.put(("calibration", sqlite_json(sql, timeout=20)))
        except Exception as exc:
            self.result_queue.put(("table_status", f"Could not load calibration stats: {exc}"))
        finally:
            self.calibration_loading = False

    def worker_detail_row(self, table_name: str, row_id: str):
        try:
            safe_table = (
                table_name
                if table_name in {"alerts", "recent_alerts", "lsst_sso_alerts"}
                else "recent_alerts"
            )
            safe_id = int(row_id)
            if safe_table == "lsst_sso_alerts":
                match_columns = """
                    mpc_designation,
                    rubin_ssobject_id,
                    sso_match_status,
                    match_method,
                    match_confidence,
                    match_separation_arcsec,
                    match_candidate_count,
                    match_checked_utc,
                    match_error,
                """
            else:
                match_columns = """
                    NULL AS mpc_designation,
                    NULL AS rubin_ssobject_id,
                    NULL AS sso_match_status,
                    NULL AS match_method,
                    NULL AS match_confidence,
                    NULL AS match_separation_arcsec,
                    NULL AS match_candidate_count,
                    NULL AS match_checked_utc,
                    NULL AS match_error,
                """
            sql = f"""
                SELECT
                    id,
                    received_utc,
                    survey,
                    observer,
                    object_id,
                    sso_id,
                    {match_columns}
                    jd,
                    ra,
                    dec,
                    fid,
                    magpsf,
                    sigmapsf,
                    ssmagnr,
                    delta_mag,
                    anomaly_sigma,
                    activity_score,
                    activity_class,
                    primary_category,
                    alert_tags,
                    interesting,
                    rejected,
                    main_reason,
                    CASE
                        WHEN json_valid(row_json)
                        THEN json_remove(row_json, '$.alert_cutouts')
                        ELSE row_json
                    END AS row_json
                FROM {safe_table}
                WHERE id = {safe_id}
                LIMIT 1;
            """
            rows = sqlite_json(sql, timeout=12)
            self.result_queue.put(("detail_row", {"id": str(row_id), "rows": rows}))
        except Exception as exc:
            self.result_queue.put(("table_status", f"Could not load alert details: {str(exc)[:500]}"))
        finally:
            self.detail_loading_ids.discard(str(row_id))

    def apply_detail_row(self, payload: dict):
        row_id = str(payload.get("id"))
        rows = payload.get("rows") or []
        if not rows:
            return

        row = self.rows_by_id.get(row_id)
        if row is None:
            return

        row.update(rows[0])
        selected = self.tree.selection()
        if selected and selected[0] == row_id:
            self.show_row_details(row)

    def mark_notifications_reviewed(self):
        try:
            run_ssh(
                "sqlite3 /var/lib/astroprak/alerts.sqlite \"UPDATE notifications SET reviewed=1 WHERE reviewed=0;\"",
                timeout=20,
            )
            self.refresh_notifications()
            self.refresh_dashboard()
        except Exception as exc:
            self.connection_var.set(f"Could not mark notifications reviewed: {exc}")

    def reset_live_filters(self):
        self.view_mode_var.set("recent live")
        self.class_filter_var.set("all")
        self.category_filter_var.set("all")
        self.limit_var.set(str(DEFAULT_LIMIT))
        self.refresh_alerts()

    def open_details_from_table(self, _event=None):
        self.use_selected_for_analysis()
        self.notebook.select(self.details_tab)
        self.detail_text.focus_set()

    def open_notification_for_analysis(self, _event=None):
        selected = self.notifications_tree.selection()
        if not selected:
            return

        notification = self.notifications_by_id.get(str(selected[0]))
        if not notification:
            return

        sso_id = str(notification.get("sso_id") or "").strip()
        if not sso_id:
            self.analysis_status_var.set("Selected notification has no SSO ID.")
            return

        self.latest_selected_row = {
            "id": notification.get("id"),
            "received_utc": notification.get("created_utc"),
            "sso_id": sso_id,
            "object_id": notification.get("object_id"),
            "activity_score": notification.get("activity_score"),
            "primary_category": notification.get("primary_category"),
            "main_reason": notification.get("message"),
        }
        self.analysis_sso_var.set(sso_id)
        self.set_detail_text(
            "Notification selected for Deep Analysis.\n\n"
            f"SSO ID: {sso_id}\n"
            f"Object ID: {notification.get('object_id') or ''}\n"
            f"Reason category: {notification.get('primary_category') or ''}\n"
            f"Priority: {fmt_float(notification.get('activity_score'), 0)}\n\n"
            f"{notification.get('message') or ''}"
        )
        self.notebook.select(self.details_tab)
        self.analysis_status_var.set(f"Ready for Deep Analysis: {sso_id}")

    def on_detail_mousewheel(self, event):
        self.detail_text.yview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def on_analysis_text_mousewheel(self, event):
        self.analysis_text.yview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def on_filter_info_mousewheel(self, event):
        self.filter_info_text.yview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def on_start_mousewheel(self, event):
        if hasattr(self, "start_canvas"):
            self.start_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def on_tree_mousewheel(self, event):
        self.tree.yview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def on_tree_shift_mousewheel(self, event):
        self.tree.xview_scroll(int(-1 * (event.delta / 120)), "units")
        return "break"

    def get_limit(self) -> int:
        try:
            limit = int(float(self.limit_var.get()))
        except ValueError:
            limit = DEFAULT_LIMIT
            self.limit_var.set(str(limit))

        return max(1, min(limit, 5000))

    def get_category_predicate(self, category_key: str) -> str:
        definition = CATEGORY_BY_KEY.get(category_key, CATEGORY_BY_KEY["all"])
        return definition["predicate"]

    def get_category_latest_id(self, category_key: str) -> int:
        key = str(category_key)
        if not hasattr(self, "category_latest_ids"):
            return 0

        try:
            return int(self.category_latest_ids.get(key, 0))
        except (TypeError, ValueError):
            return 0

    def update_category_badges(self):
        if not hasattr(self, "category_unseen_counts"):
            return

        for category in CATEGORY_DEFINITIONS:
            key = category["key"]
            new_count = int(self.category_unseen_counts.get(key, 0))
            if new_count > 99:
                text = "99+"
            elif new_count > 0:
                text = str(new_count)
            else:
                text = ""
            self.category_badge_vars[key].set(text)
            badge = self.category_badge_widgets.get(key)
            if badge is not None:
                if text:
                    badge.configure(bg=self.danger, fg="white")
                else:
                    badge.configure(bg=self.panel_2, fg=self.panel_2)

    def worker_dashboard(self, show_all_days: bool, refresh_saved_alert_cache: bool = False):
        try:
            stats_sql = """
                SELECT
                    coalesce((SELECT value FROM collector_stats WHERE key='total_processed'), '0') AS total_processed,
                    coalesce((SELECT value FROM collector_stats WHERE key='latest_received_utc'), '') AS latest_received_utc,
                    (SELECT count(*) FROM recent_alerts) AS recent_alerts,
                    (SELECT count(*) FROM alerts) AS saved_candidates,
                    (
                        SELECT count(*)
                        FROM alerts
                        WHERE activity_class IN ('urgent', 'interesting', 'good_candidate', 'weak_candidate')
                    ) AS interesting_alerts,
                    (
                        SELECT count(*)
                        FROM alerts
                        WHERE primary_category IN (
                            'photometric_extreme',
                            'photometric_strong',
                            'photometric_weak',
                            'fallback_brightening',
                            'single_anomaly'
                        )
                    ) AS photometric_alerts,
                    (SELECT count(*) FROM lsst_sso_alerts WHERE mpc_designation IS NOT NULL) AS matched_lsst_alerts,
                    (SELECT count(*) FROM lsst_sso_alerts WHERE mpc_designation IS NULL) AS unmatched_lsst_alerts,
                    (SELECT count(*) FROM mpc_crossmatch_queue WHERE status IN ('pending', 'running', 'error', 'not_found')) AS mpc_queue_alerts,
                    (SELECT count(*) FROM notifications WHERE reviewed=0) AS unread_notifications;
            """
            if show_all_days:
                chart_sql = """
                    SELECT day, total, ztf, lsst, interesting
                    FROM alert_daily_counts
                    ORDER BY day;
                """
            else:
                chart_sql = """
                    SELECT day, total, ztf, lsst, interesting
                    FROM alert_daily_counts
                    WHERE day >= date('now', '-30 day')
                    ORDER BY day;
                """

            def load_status():
                status_command = (
                    f"timeout 4s systemctl is-active {shlex.quote(SERVICE_NAME)}; "
                    f"timeout 4s systemctl show {shlex.quote(SERVICE_NAME)} -p ActiveEnterTimestamp --value; "
                    f"timeout 4s journalctl -u {shlex.quote(SERVICE_NAME)} -n 1 --no-pager"
                )
                try:
                    return run_ssh(status_command, timeout=8)
                except Exception as status_exc:
                    return f"status check delayed\n\n{status_exc}"

            def future_result(future, fallback, label: str):
                try:
                    return future.result()
                except Exception as exc:
                    self.result_queue.put(("status", f"{label} delayed: {exc}"))
                    return fallback

            with ThreadPoolExecutor(max_workers=3) as pool:
                stats_future = pool.submit(sqlite_json, stats_sql, 20)
                chart_future = pool.submit(sqlite_json, chart_sql, 20)
                status_future = pool.submit(load_status)

                stats = future_result(stats_future, None, "Dashboard stats")
                chart_rows = future_result(chart_future, None, "Dashboard chart")
                status_output = future_result(status_future, "status check delayed", "Collector status")
                self.result_queue.put((
                    "dashboard",
                    {
                        "stats": stats[0] if stats else None,
                        "chart_rows": chart_rows,
                        "category_rows": [],
                        "status_output": status_output,
                    },
                ))

            if not refresh_saved_alert_cache:
                return

            saved_requests = {
                category_key: {
                    "limit": DEFAULT_LIMIT,
                    "class_filter": "all",
                    "category_filter": category_key,
                    "table_name": "alerts",
                }
                for category_key in ("interesting", "photometric", "matched_lsst")
            }
            saved_requests["matched_lsst"]["table_name"] = "lsst_sso_alerts"
            saved_alerts = {}
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = {
                    category_key: pool.submit(
                        sqlite_json,
                        self.build_alert_rows_sql(request),
                        18,
                    )
                    for category_key, request in saved_requests.items()
                }
                for category_key, future in futures.items():
                    try:
                        saved_alerts[category_key] = future.result()
                    except Exception as exc:
                        self.result_queue.put(("table_status", f"Cached {category_key} list refresh delayed: {exc}"))
                        continue
            if saved_alerts:
                self.result_queue.put(("saved_alerts", saved_alerts))
        except Exception as exc:
            self.result_queue.put(("error", exc))
        finally:
            self.dashboard_loading = False

    def category_matches_row(self, category_key: str, row: dict) -> bool:
        activity_class = str(row.get("activity_class") or "normal")
        primary_category = str(row.get("primary_category") or "normal")
        rejected = int(row.get("rejected") or 0)

        if category_key == "all":
            return True
        if category_key == "urgent":
            return activity_class == "urgent"
        if category_key == "interesting":
            return activity_class in {"urgent", "interesting", "good_candidate", "weak_candidate"}
        if category_key == "review":
            return activity_class == "review"
        if category_key == "photometric":
            return (
                primary_category.startswith("photometric_")
                or primary_category in {"fallback_brightening", "single_anomaly"}
            )
        if category_key == "matched_lsst":
            return str(row.get("survey") or "").lower() == "lsst" and bool(row.get("mpc_designation"))
        if category_key == "unmatched_lsst":
            return str(row.get("survey") or "").lower() == "lsst" and not row.get("mpc_designation")
        if category_key == "persistence":
            return primary_category in {"multi_night_activity", "repeated_same_night"}
        if category_key == "near_snowline":
            return primary_category == "near_snowline_activity"
        if category_key == "contamination":
            return primary_category == "possible_contamination"
        if category_key == "quality_rejected":
            return primary_category == "quality_rejected" or activity_class == "rejected" or rejected == 1
        if category_key == "normal":
            return activity_class == "normal"

        return False

    def category_rows_from_aggregate(self, aggregate_row: dict) -> list[dict]:
        category_rows = []

        for category in CATEGORY_DEFINITIONS:
            key = category["key"]
            category_rows.append({
                "category": key,
                "count": int(aggregate_row.get(f"{key}_count") or 0),
                "latest_id": int(aggregate_row.get(f"{key}_latest_id") or 0),
                "unseen": int(aggregate_row.get(f"{key}_unseen") or 0),
            })

        return category_rows

    def compute_category_rows(self, rows: list[dict]) -> list[dict]:
        category_rows = []

        for category in CATEGORY_DEFINITIONS:
            key = category["key"]
            seen_id = int(self.seen_state.get(key, 0))
            matching_ids = [
                int(row.get("id") or 0)
                for row in rows
                if self.category_matches_row(key, row)
            ]
            latest_id = max(matching_ids) if matching_ids else 0
            unseen = sum(1 for row_id in matching_ids if row_id > seen_id)
            category_rows.append({
                "category": key,
                "count": len(matching_ids),
                "latest_id": latest_id,
                "unseen": unseen,
            })

        return category_rows

    def alert_request_matches_current(self, request: dict) -> bool:
        current = {
            "limit": self.get_limit(),
            "class_filter": self.class_filter_var.get(),
            "category_filter": self.category_filter_var.get(),
            "table_name": self.table_name_for_view(),
        }
        return request == current

    def build_alert_rows_sql(self, request: dict) -> str:
        limit = int(request["limit"])
        class_filter = str(request["class_filter"])
        category_filter = str(request["category_filter"])
        table_name = str(request["table_name"])
        where_parts = []

        if class_filter != "all":
            where_parts.append(f"activity_class = '{safe_sql_text(class_filter)}'")

        if category_filter != "all":
            where_parts.append(f"({self.get_category_predicate(category_filter)})")

        where = "WHERE " + " AND ".join(where_parts) if where_parts else ""
        if table_name == "lsst_sso_alerts":
            mpc_columns = """
                mpc_designation,
                rubin_ssobject_id,
                sso_match_status,
                match_method,
                match_confidence,
                match_separation_arcsec,
                match_candidate_count,
                match_checked_utc,
            """
        else:
            mpc_columns = """
                NULL AS mpc_designation,
                NULL AS rubin_ssobject_id,
                NULL AS sso_match_status,
                NULL AS match_method,
                NULL AS match_confidence,
                NULL AS match_separation_arcsec,
                NULL AS match_candidate_count,
                NULL AS match_checked_utc,
            """

        return f"""
            SELECT
                id,
                received_utc,
                survey,
                observer,
                activity_score,
                activity_class,
                primary_category,
                sso_id,
                {mpc_columns}
                object_id,
                jd,
                ra,
                dec,
                fid,
                magpsf,
                sigmapsf,
                ssmagnr,
                delta_mag,
                anomaly_sigma,
                NULL AS object_class,
                NULL AS phase_corrected_residual_sigma,
                NULL AS photometric_score,
                NULL AS persistence_score,
                NULL AS morphology_score,
                NULL AS orbital_context_score,
                NULL AS heliocentric_trend_score,
                NULL AS penalty_score,
                NULL AS n_anomalous_recent,
                NULL AS n_anomalous_nights,
                NULL AS median_delta_mag_recent,
                NULL AS best_anomaly_sigma_recent,
                NULL AS alert_tags,
                NULL AS reasons,
                main_reason
            FROM {table_name}
            {where}
            ORDER BY id DESC
            LIMIT {limit};
        """

    def worker_alerts(self, request: dict):
        try:
            sql = self.build_alert_rows_sql(request)
            rows = sqlite_json(sql, timeout=18)
            self.result_queue.put(("alerts", {"request": request, "rows": rows}))
        except Exception as exc:
            self.result_queue.put(("table_status", f"Could not load live alerts: {exc}"))
        finally:
            self.result_queue.put(("alerts_complete", None))

    def apply_dashboard_stats(self, stats: dict):
        total = stats.get("total_processed", 0)
        latest = stats.get("latest_received_utc") or "none yet"
        candidates = stats.get("saved_candidates", 0)
        unread_notifications = stats.get("unread_notifications", 0)
        mpc_queue_alerts = stats.get("mpc_queue_alerts", 0)

        self.total_var.set(fmt_int(total))
        if latest and latest != "none yet":
            self.latest_german_var.set(fmt_german_time(latest))
            self.latest_utc_var.set(f"{fmt_utc_time(latest)} UTC")
        else:
            self.latest_german_var.set("none yet")
            self.latest_utc_var.set("")
        self.candidates_var.set(fmt_int(candidates))
        self.unread_notifications_var.set(fmt_int(unread_notifications))
        self.candidate_inbox_var.set(fmt_int(unread_notifications))
        self.candidate_inbox_subtitle_var.set(
            f"{fmt_int(candidates)} saved total | {fmt_int(mpc_queue_alerts)} MPC checks queued"
        )
        self.category_count_vars["all"].set(fmt_int(stats.get("recent_alerts", 0)))
        self.category_count_vars["interesting"].set(fmt_int(stats.get("interesting_alerts", 0)))
        self.category_count_vars["photometric"].set(fmt_int(stats.get("photometric_alerts", 0)))
        self.category_count_vars["matched_lsst"].set(fmt_int(stats.get("matched_lsst_alerts", 0)))
        self.category_count_vars["unmatched_lsst"].set(fmt_int(stats.get("unmatched_lsst_alerts", 0)))

    def apply_dashboard(self, payload: dict):
        stats = payload.get("stats")
        chart_rows = payload.get("chart_rows")
        category_rows = payload.get("category_rows", [])
        status_output = str(payload.get("status_output", "")).strip()
        status_lines = [line.strip() for line in status_output.splitlines() if line.strip()]

        if isinstance(stats, dict) and stats:
            self.apply_dashboard_stats(stats)
            self.start_worker(self.save_dashboard_cache, stats)

        if status_lines:
            self.service_var.set(f"Collector: {status_lines[0]}")
            started_raw = status_lines[1] if len(status_lines) > 1 else ""
            self.stream_started_var.set(fmt_systemd_start_time(started_raw))
            self.connection_var.set("Latest service log: " + " | ".join(status_lines[2:])[:240])
        else:
            self.service_var.set("Collector: unknown")
            self.stream_started_var.set("stream start unknown")

        if category_rows:
            self.apply_category_rows(category_rows)
        if isinstance(chart_rows, list):
            self.current_chart_rows = chart_rows
            self.draw_chart()

    def apply_saved_alert_cache(self, saved_alerts: dict):
        changed = False
        for category_key in ("interesting", "photometric", "matched_lsst"):
            rows = saved_alerts.get(category_key)
            if isinstance(rows, list):
                self.cached_saved_alerts[category_key] = rows[:DEFAULT_LIMIT]
                changed = True
        if changed:
            self.start_worker(self.save_saved_alert_cache, dict(self.cached_saved_alerts))

    def apply_category_rows(self, category_rows: list[dict]):
        self.category_latest_ids = {}
        self.category_unseen_counts = {}
        for row in category_rows:
            key = str(row.get("category") or "")
            count = row.get("count", 0)
            latest_id = row.get("latest_id", 0)
            unseen = row.get("unseen", 0)

            if key in self.category_count_vars:
                self.category_count_vars[key].set(fmt_int(count))
                self.category_unseen_counts[key] = int(unseen or 0)

            try:
                self.category_latest_ids[key] = int(latest_id or 0)
            except (TypeError, ValueError):
                self.category_latest_ids[key] = 0

        self.update_category_badges()

    def apply_notifications(self, rows: list[dict]):
        for item in self.notifications_tree.get_children():
            self.notifications_tree.delete(item)
        self.notifications_by_id.clear()
        for row in rows:
            item_id = str(row.get("id"))
            self.notifications_by_id[item_id] = row
            values = (
                row.get("id"),
                fmt_utc_time(row.get("created_utc")),
                row.get("severity"),
                row.get("primary_category"),
                fmt_float(row.get("activity_score"), 0),
                row.get("sso_id") or "",
                row.get("object_id") or "",
                row.get("message") or "",
            )
            self.notifications_tree.insert("", tk.END, iid=item_id, values=values)

    def apply_calibration(self, rows: list[dict]):
        for item in self.calibration_tree.get_children():
            self.calibration_tree.delete(item)
        for row in rows:
            values = (
                row.get("key"),
                fmt_int(row.get("count")),
                fmt_int(row.get("interesting_count")),
                fmt_float(row.get("best_score"), 1),
                fmt_utc_time(row.get("last_seen_utc")),
            )
            self.calibration_tree.insert("", tk.END, values=values)

    def draw_chart(self):
        canvas = self.chart_canvas
        canvas.delete("all")

        width = max(canvas.winfo_width(), 400)
        height = max(canvas.winfo_height(), 250)
        rows = self.current_chart_rows

        margin_left = 58
        margin_right = 24
        margin_top = 24
        margin_bottom = 58
        plot_w = width - margin_left - margin_right
        plot_h = height - margin_top - margin_bottom

        canvas.create_rectangle(0, 0, width, height, fill=self.panel, outline="")

        if not rows:
            canvas.create_text(
                width / 2,
                height / 2,
                text="No daily count data yet. It will appear as the server processes alerts.",
                fill=self.muted,
                font=("Segoe UI", 12),
            )
            return

        max_total = max(int(row.get("total") or 0) for row in rows)
        max_total = max(max_total, 1)

        canvas.create_line(margin_left, margin_top, margin_left, margin_top + plot_h, fill="#334155")
        canvas.create_line(margin_left, margin_top + plot_h, margin_left + plot_w, margin_top + plot_h, fill="#334155")

        for i in range(5):
            y = margin_top + plot_h - (plot_h * i / 4)
            value = int(max_total * i / 4)
            canvas.create_line(margin_left, y, margin_left + plot_w, y, fill="#1e293b")
            canvas.create_text(margin_left - 10, y, text=str(value), fill=self.muted, anchor="e", font=("Segoe UI", 9))

        n = len(rows)
        gap = 3 if n <= 45 else 1
        bar_w = max(2, (plot_w - gap * max(n - 1, 0)) / max(n, 1))

        for idx, row in enumerate(rows):
            total = int(row.get("total") or 0)
            ztf = int(row.get("ztf") or 0)
            lsst = int(row.get("lsst") or 0)
            other = max(0, total - ztf - lsst)
            interesting = int(row.get("interesting") or 0)
            x0 = margin_left + idx * (bar_w + gap)
            x1 = x0 + bar_w
            y1 = margin_top + plot_h

            cursor_y = y1
            for value, color in ((ztf, "#2563eb"), (lsst, "#f97316"), (other, "#64748b")):
                if value <= 0:
                    continue
                segment_h = max(1, (value / max_total) * plot_h)
                y0 = cursor_y - segment_h
                canvas.create_rectangle(x0, y0, x1, cursor_y, fill=color, outline="")
                cursor_y = y0

            if interesting > 0:
                ih = max(2, (interesting / max_total) * plot_h)
                canvas.create_rectangle(x0, cursor_y - ih - 1, x1, cursor_y - 1, fill="#facc15", outline="")

            if n <= 35 or idx in {0, n - 1} or idx % max(1, n // 8) == 0:
                day = str(row.get("day") or "")
                label = day[5:] if len(day) >= 10 else day
                canvas.create_text(
                    x0 + bar_w / 2,
                    margin_top + plot_h + 18,
                    text=label,
                    fill=self.muted,
                    angle=35 if n > 18 else 0,
                    font=("Segoe UI", 8),
                )

        mode = "all days" if self.show_all_days.get() else "last 30 days"
        canvas.create_text(
            margin_left,
            8,
            text=f"{mode} | blue = ZTF, orange = LSST, gray = other, yellow = interesting candidates",
            fill=self.muted,
            anchor="nw",
            font=("Segoe UI", 10),
        )

    def apply_alert_rows(self, rows: list[dict]):
        selected_id = None
        selected = self.tree.selection()
        if selected:
            selected_id = selected[0]
        previous_yview = self.tree.yview()
        had_existing_rows = bool(self.tree.get_children())

        for item in self.tree.get_children():
            self.tree.delete(item)

        self.rows_by_id.clear()

        for row in rows:
            item_id = str(row.get("id"))
            self.rows_by_id[item_id] = row
            visible_columns = self.get_visible_columns()
            values = tuple(
                fmt_value(
                    column,
                    row.get("received_utc") if column == "received_local" else row.get(column),
                )
                for column in visible_columns
            )
            tag = str(row.get("primary_category") or row.get("activity_class") or "normal")
            self.tree.insert("", tk.END, iid=item_id, values=values, tags=(tag,))

        request = getattr(self, "current_alert_request", {})
        if (
            request.get("table_name") == "recent_alerts"
            and request.get("class_filter") == "all"
            and request.get("category_filter") == "all"
        ):
            category_rows = [
                row
                for row in self.compute_category_rows(rows)
                if row.get("category") not in {"all", "interesting", "photometric", "matched_lsst"}
            ]
            self.apply_category_rows(category_rows)

        if selected_id in self.rows_by_id:
            self.tree.selection_set(selected_id)
            if had_existing_rows:
                self.tree.yview_moveto(previous_yview[0])
        elif rows:
            first_id = str(rows[0].get("id"))
            if had_existing_rows:
                self.tree.yview_moveto(previous_yview[0])
            else:
                self.tree.see(first_id)
                self.set_detail_text("Select an alert to load its full details.")
        else:
            self.set_detail_text(
                "No rows found for the current view/filter.\n\n"
                "Use 'recent live' to see the rotating live buffer. "
                "'interesting saved' can stay empty until a candidate passes the score threshold."
            )

        if rows:
            latest = rows[0].get("received_utc", "")
            self.table_status_var.set(
                f"Live polling every {LIVE_POLL_MS / 1000:.1f}s | {len(rows)} rows | newest: {fmt_german_time(latest)} DE / {fmt_utc_time(latest)} UTC"
            )
        else:
            self.table_status_var.set(f"Live polling every {LIVE_POLL_MS / 1000:.1f}s | no rows")

    def on_select_row(self, _event):
        selected = self.tree.selection()
        if not selected:
            return

        row = self.rows_by_id.get(selected[0])
        if row is not None:
            self.show_row_details(row)

    def show_row_details(self, row: dict):
        self.latest_selected_row = row
        if hasattr(self, "sky_figure") and self.sky_show_selected_var.get():
            self.draw_sky_coverage()
        row_json = row.get("row_json")
        row_id = str(row.get("id") or "")

        if not row_json and row_id and row_id not in self.detail_loading_ids:
            self.detail_loading_ids.add(row_id)
            self.start_worker(self.worker_detail_row, self.current_alert_table, row_id)

        try:
            full = json.loads(row_json) if row_json else row
        except json.JSONDecodeError:
            full = row

        if isinstance(full, dict):
            for key, value in row.items():
                full.setdefault(key, value)

        alert_tags = full.get("alert_tags")
        if isinstance(alert_tags, str):
            try:
                alert_tags = json.loads(alert_tags)
            except json.JSONDecodeError:
                pass

        reasons = full.get("reasons")
        if isinstance(reasons, str):
            try:
                reasons = json.loads(reasons)
            except json.JSONDecodeError:
                pass

        if isinstance(reasons, list):
            reasons_text = "\n".join(f"- {reason}" for reason in reasons)
        else:
            reasons_text = str(reasons or full.get("main_reason") or "")

        summary_lines = [
            f"ID: {row.get('id')}",
            f"UTC: {fmt_utc_time(row.get('received_utc'))}",
            f"German time: {fmt_german_time(row.get('received_utc'))}",
            f"Survey / observer: {row.get('survey')} / {row.get('observer')}",
            f"SSO ID: {row.get('sso_id')}",
            f"MPC designation: {row.get('mpc_designation')}",
            f"Rubin ssObjectId: {row.get('rubin_ssobject_id')}",
            f"SSO match status: {row.get('sso_match_status')}",
            f"Match method: {row.get('match_method')}",
            f"Match confidence: {row.get('match_confidence')}",
            f"Match separation: {row.get('match_separation_arcsec')} arcsec",
            f"MPC candidates: {row.get('match_candidate_count')}",
            f"Match checked UTC: {row.get('match_checked_utc')}",
            f"Match error: {full.get('match_error') or row.get('match_error')}",
            f"Object ID: {row.get('object_id')}",
            "",
            "Review classification",
            "-" * 40,
            f"review_level: {full.get('review_level') or full.get('activity_class')}",
            f"review_reason: {full.get('review_reason') or full.get('main_reason')}",
            f"reason_category: {full.get('primary_category')}",
            f"alert_tags: {alert_tags}",
            f"legacy_priority/activity_score: {full.get('activity_score')}",
            "",
            "Diagnostic components",
            "-" * 40,
            f"photometric_score: {full.get('photometric_score')}",
            f"persistence_score: {full.get('persistence_score')}",
            f"morphology_score: {full.get('morphology_score')}",
            f"orbital_context_score: {full.get('orbital_context_score')}",
            f"heliocentric_trend_score: {full.get('heliocentric_trend_score')}",
            f"penalty_score: {full.get('penalty_score')}",
            "",
            "Photometry",
            "-" * 40,
            f"magpsf: {full.get('magpsf')}",
            f"ssmagnr: {full.get('ssmagnr')}",
            f"delta_mag: {full.get('delta_mag')}",
            f"anomaly_sigma: {full.get('anomaly_sigma')}",
            "",
            "Persistence",
            "-" * 40,
            f"n_anomalous_recent: {full.get('n_anomalous_recent')}",
            f"n_anomalous_nights: {full.get('n_anomalous_nights')}",
            f"median_delta_mag_recent: {full.get('median_delta_mag_recent')}",
            f"best_anomaly_sigma_recent: {full.get('best_anomaly_sigma_recent')}",
            "",
            "Reasons",
            "-" * 40,
            reasons_text,
            "",
            "Raw stored row",
            "-" * 40,
            (
                json.dumps(full, indent=2, ensure_ascii=False, default=str)
                if row_json
                else "Full row_json is loading in the background..."
            ),
        ]

        self.set_detail_text("\n".join(summary_lines))

    def live_tick(self):
        if self.live_enabled.get():
            self.refresh_alerts(queue_if_busy=False)

        self.root.after(LIVE_POLL_MS, self.live_tick)

    def dashboard_tick(self):
        self.refresh_dashboard()
        self.root.after(DASHBOARD_POLL_MS, self.dashboard_tick)


def main():
    root = tk.Tk()
    ServerAlertDashboard(root)
    root.mainloop()


if __name__ == "__main__":
    main()

