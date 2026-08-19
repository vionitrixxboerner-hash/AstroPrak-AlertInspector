from __future__ import annotations

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse
from zoneinfo import ZoneInfo
import argparse
import base64
import csv
import gzip
import math
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError, as_completed
from datetime import date, datetime, timedelta, timezone
import io
import json
import os
import sqlite3
import subprocess
import threading
import time
import traceback
import uuid

import numpy as np
import requests
from astropy.io import fits
from astropy.time import Time
from astroquery.jplhorizons import Horizons
from matplotlib.figure import Figure
from matplotlib.patches import Circle
from scipy import ndimage, signal

from fink_sso_combined_gui import (
    CUTOUT_GENERAL_CANDIDATE_POOL,
    CUTOUT_GENERAL_MAX_EPOCHS,
    CUTOUT_GALLERY_MAX_EPOCHS,
    CUTOUT_GALLERY_PAGE_SIZE,
    CUTOUT_HISTORY_MAX_EPOCHS,
    CUTOUT_SIMILAR_CANDIDATE_POOL,
    build_alert_cutout_figure,
    build_cutout_evolution_figure,
    add_cutout_angular_scale,
    center_cutout_pair,
    cutout_pixel_scale_arcsec,
    evenly_spaced_rows,
    enrich_cutout_history_with_horizons,
    fetch_fink_cutout_candidates,
    fetch_fink_lsst_cutout_candidates,
    image_array_from_embedded_cutout,
    is_same_cutout_alert,
    load_cutouts_for_candidates,
    merge_cutout_histories,
    select_cutout_geometry_matches,
    select_general_cutout_epochs,
    select_general_with_required,
    fmt_german_time,
    resolve_analysis_ids,
    resolve_horizons_smallbody_id,
    to_float,
    analyze_sso_deep,
)


DEFAULT_DB_PATH = "/var/lib/astroprak/alerts.sqlite"
DEFAULT_CONFIG_PATH = "/opt/astroprak/scoring_config.json"
DEFAULT_SERVICE_NAME = "astroprak-collector"
DEFAULT_WEEKLY_STATUS_PATH = "/opt/astroprak/weekly_review_status.json"
DEFAULT_LIMIT = 200
MAX_LIMIT = 1000
ZTF_IRSA_SCI_SEARCH_URL = "https://irsa.ipac.caltech.edu/ibe/search/ztf/products/sci"
ZTF_IRSA_SCI_DATA_ROOT = "https://irsa.ipac.caltech.edu/ibe/data/ztf/products/sci"
ZTF_ARCHIVE_SEARCH_EPOCHS = 8
ZTF_ARCHIVE_LOOKBACK_DAYS = 730
ZTF_ARCHIVE_QUERY_HALF_WINDOW_DAYS = 3.0
ZTF_ARCHIVE_QUERY_SIZE_DEG = 0.05
ZTF_ARCHIVE_CUTOUT_SIZE = "60arcsec"
ZTF_ARCHIVE_MAX_WORKERS = 4
ZTF_ARCHIVE_TOTAL_TIMEOUT = 35
WEEKLY_REVIEW_DAYS = 7
WEEKLY_REVIEW_TOP_LIMIT = 10

COLUMNS = [
    "received_local", "observer", "sso_id", "object_id", "anomaly_level",
    "anomaly_sigma", "delta_mag", "magpsf", "ssmagnr", "main_reason",
]
MINIMAL_COLUMNS = [
    "received_local", "observer", "sso_id", "object_id", "anomaly_level",
    "anomaly_sigma", "magpsf",
]
ALERT_DETAIL_FIELDS = [
    "id", "received_utc", "received_local", "observer", "survey", "topic",
    "object_id", "dia_source_id", "sso_id", "ra", "dec", "jd", "fid",
    "magpsf", "sigmapsf", "ssmagnr", "delta_mag", "anomaly_sigma", "anomaly_level",
    "mpc_designation", "rubin_ssobject_id", "match_confidence", "match_separation_arcsec",
]
FILTER_DEFAULTS = {
    "reject_bad_sigmag": True, "reject_nbad": True, "reject_low_rb": True,
    "reject_low_drb": True, "score_delta_mag": True,
    "score_known_unknown_sso": True, "score_ssdistnr": True,
    "score_brightness": True, "score_ndethist": True,
}

STATE = {
    "db_path": DEFAULT_DB_PATH,
    "config_path": DEFAULT_CONFIG_PATH,
    "weekly_status_path": os.environ.get("ASTROPRAK_WEEKLY_STATUS_PATH", DEFAULT_WEEKLY_STATUS_PATH),
    "service": DEFAULT_SERVICE_NAME,
    "jobs": {},
    "dashboard_cache": {},
}
STATE_LOCK = threading.RLock()


def ensure_database_schema(db_path):
    path = Path(db_path)
    if str(path) != ":memory:":
        path.parent.mkdir(parents=True, exist_ok=True)
    con = sqlite3.connect(path)
    try:
        con.execute("PRAGMA busy_timeout = 8000")
        con.executescript(
            """
            CREATE TABLE IF NOT EXISTS collector_stats (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL DEFAULT ''
            );

            CREATE TABLE IF NOT EXISTS alert_daily_counts (
                day TEXT PRIMARY KEY,
                total INTEGER NOT NULL DEFAULT 0,
                ztf INTEGER NOT NULL DEFAULT 0,
                lsst INTEGER NOT NULL DEFAULT 0,
                interesting INTEGER NOT NULL DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS recent_alerts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                received_utc TEXT,
                survey TEXT,
                topic TEXT,
                observer TEXT,
                object_id TEXT,
                sso_id TEXT,
                jd REAL,
                ra REAL,
                dec REAL,
                fid TEXT,
                magpsf REAL,
                sigmapsf REAL,
                ssmagnr REAL,
                delta_mag REAL,
                anomaly_sigma REAL,
                activity_score REAL,
                activity_class TEXT,
                interesting INTEGER NOT NULL DEFAULT 0,
                rejected INTEGER NOT NULL DEFAULT 0,
                main_reason TEXT,
                primary_category TEXT,
                alert_tags TEXT,
                row_json TEXT
            );

            CREATE TABLE IF NOT EXISTS alerts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                received_utc TEXT,
                survey TEXT,
                topic TEXT,
                observer TEXT,
                object_id TEXT,
                sso_id TEXT,
                jd REAL,
                ra REAL,
                dec REAL,
                fid TEXT,
                magpsf REAL,
                sigmapsf REAL,
                ssmagnr REAL,
                delta_mag REAL,
                anomaly_sigma REAL,
                activity_score REAL,
                activity_class TEXT,
                interesting INTEGER NOT NULL DEFAULT 0,
                rejected INTEGER NOT NULL DEFAULT 0,
                main_reason TEXT,
                primary_category TEXT,
                alert_tags TEXT,
                row_json TEXT
            );

            CREATE TABLE IF NOT EXISTS lsst_sso_alerts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                received_utc TEXT,
                survey TEXT,
                topic TEXT,
                observer TEXT,
                object_id TEXT,
                sso_id TEXT,
                jd REAL,
                ra REAL,
                dec REAL,
                fid TEXT,
                magpsf REAL,
                sigmapsf REAL,
                ssmagnr REAL,
                delta_mag REAL,
                anomaly_sigma REAL,
                activity_score REAL,
                activity_class TEXT,
                interesting INTEGER NOT NULL DEFAULT 0,
                rejected INTEGER NOT NULL DEFAULT 0,
                main_reason TEXT,
                primary_category TEXT,
                alert_tags TEXT,
                row_json TEXT,
                mpc_designation TEXT,
                rubin_ssobject_id TEXT,
                sso_match_status TEXT,
                match_method TEXT,
                match_confidence REAL,
                match_separation_arcsec REAL,
                match_candidate_count INTEGER,
                match_checked_utc TEXT
            );

            CREATE TABLE IF NOT EXISTS notifications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_utc TEXT,
                severity TEXT,
                primary_category TEXT,
                activity_score REAL,
                sso_id TEXT,
                object_id TEXT,
                message TEXT,
                reviewed INTEGER NOT NULL DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS calibration_stats (
                key TEXT PRIMARY KEY,
                count INTEGER NOT NULL DEFAULT 0,
                interesting_count INTEGER NOT NULL DEFAULT 0,
                best_score REAL,
                last_seen_utc TEXT
            );

            CREATE TABLE IF NOT EXISTS mpc_crossmatch_queue (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                lsst_alert_id INTEGER NOT NULL,
                status TEXT,
                attempts INTEGER NOT NULL DEFAULT 0,
                next_attempt_utc TEXT,
                last_error TEXT,
                created_utc TEXT,
                updated_utc TEXT
            );

            CREATE UNIQUE INDEX IF NOT EXISTS idx_mpc_crossmatch_queue_alert
                ON mpc_crossmatch_queue(lsst_alert_id);
            CREATE INDEX IF NOT EXISTS idx_recent_alerts_received_utc
                ON recent_alerts(received_utc);
            CREATE INDEX IF NOT EXISTS idx_recent_alerts_sso_id
                ON recent_alerts(sso_id);
            CREATE INDEX IF NOT EXISTS idx_alerts_received_utc
                ON alerts(received_utc);
            CREATE INDEX IF NOT EXISTS idx_alerts_sso_id
                ON alerts(sso_id);
            CREATE INDEX IF NOT EXISTS idx_lsst_sso_alerts_received_utc
                ON lsst_sso_alerts(received_utc);
            CREATE INDEX IF NOT EXISTS idx_lsst_sso_alerts_sso_id
                ON lsst_sso_alerts(sso_id);
            """
        )
        con.execute(
            "INSERT OR IGNORE INTO collector_stats (key, value) VALUES ('total_processed', '0')"
        )
        con.execute(
            "INSERT OR IGNORE INTO collector_stats (key, value) VALUES ('latest_received_utc', '')"
        )
        con.commit()
    finally:
        con.close()


def json_safe(value):
    if value is None:
        return None
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def db_rows(sql, params=()):
    with STATE_LOCK:
        db_path = STATE["db_path"]
    con = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True, timeout=8)
    con.row_factory = sqlite3.Row
    try:
        con.execute("PRAGMA busy_timeout = 8000")
        con.execute("PRAGMA query_only = ON")
        return [{key: json_safe(value) for key, value in dict(row).items()} for row in con.execute(sql, params)]
    finally:
        con.close()


def db_write(sql, params=()):
    with STATE_LOCK:
        db_path = STATE["db_path"]
    con = sqlite3.connect(db_path)
    try:
        con.execute(sql, params)
        con.commit()
    finally:
        con.close()


def read_weekly_statuses():
    with STATE_LOCK:
        path = Path(STATE["weekly_status_path"])
    try:
        if not path.exists():
            return {}
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def write_weekly_status(payload):
    key = str(payload.get("key") or "").strip()
    status = str(payload.get("status") or "new").strip()
    allowed = {"new", "reviewed", "follow-up candidate"}
    if not key:
        return {"ok": False, "error": "Missing candidate key."}
    if status not in allowed:
        return {"ok": False, "error": "Invalid review status."}
    with STATE_LOCK:
        path = Path(STATE["weekly_status_path"])
        statuses = read_weekly_statuses()
        statuses[key] = status
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(statuses, indent=2, sort_keys=True), encoding="utf-8")
            STATE["dashboard_cache"].clear()
        except Exception as exc:
            return {"ok": False, "error": f"Could not save weekly status: {exc}"}
    return {"ok": True, "status": status}


def scalar(sql, params=(), default=0):
    rows = db_rows(sql, params)
    if not rows:
        return default
    return next(iter(rows[0].values()), default)


def fmt_local_time(value):
    text = str(value or "").strip()
    if not text:
        return ""
    try:
        iso = text if text.endswith("Z") or "+" in text[-6:] else text + "+00:00"
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(ZoneInfo("Europe/Berlin")).strftime("%d.%m.%Y %H:%M:%S")
    except Exception:
        return text.split(".")[0].replace("T", " ")


def category_predicate(key):
    predicates = {
        "urgent": "activity_class = 'urgent'",
        "interesting": "activity_class IN ('urgent','interesting','good_candidate','weak_candidate')",
        "review": "activity_class = 'review'",
        "photometric": "primary_category LIKE 'photometric_%' OR primary_category IN ('fallback_brightening','single_anomaly')",
        "persistence": "primary_category IN ('multi_night_activity','repeated_same_night')",
        "near_snowline": "primary_category = 'near_snowline_activity'",
        "contamination": "primary_category = 'possible_contamination'",
        "quality_rejected": "primary_category = 'quality_rejected' OR activity_class = 'rejected' OR rejected = 1",
        "normal": "activity_class = 'normal'",
    }
    return predicates.get(key, "1=1")


def weekly_anomaly_level(sigma):
    value = to_float(sigma)
    if value is None:
        return "unknown"
    if value < -7:
        return "sigma < -7"
    if value < -5:
        return "sigma < -5"
    if value < -3:
        return "sigma < -3"
    return "normal"


def weekly_source(row):
    text = str(row.get("survey") or row.get("observer") or row.get("object_id") or "").lower()
    if "lsst" in text:
        return "LSST"
    if "ztf" in text:
        return "ZTF"
    return str(row.get("observer") or row.get("survey") or "Other")


def parse_iso_day(value):
    try:
        return date.fromisoformat(str(value or "")[:10])
    except ValueError:
        return None


def week_start_for(day):
    return day - timedelta(days=day.weekday())


def iso_week_label(day):
    iso = day.isocalendar()
    return f"Week {iso.week}, {iso.year}"


def week_date_range(start, latest=None):
    end = start + timedelta(days=6)
    if latest:
        end = min(end, latest)
    return f"{start.isoformat()} to {end.isoformat()}"


def weekly_options(latest_day):
    rows = db_rows("SELECT day FROM alert_daily_counts WHERE day IS NOT NULL AND day != '' ORDER BY day DESC LIMIT 120")
    seen, options = set(), []
    latest = parse_iso_day(latest_day.get("day"))
    latest_week = week_start_for(latest) if latest else None
    for row in rows:
        day = parse_iso_day(row.get("day"))
        if not day:
            continue
        start = week_start_for(day)
        key = start.isoformat()
        if key in seen:
            continue
        seen.add(key)
        label = iso_week_label(start)
        if latest_week and start == latest_week:
            label += " | week so far"
        options.append({"start_day": key, "label": label})
        if len(options) >= 12:
            break
    return options


def weekly_review_payload(latest_day, selected_week_start=None):
    end_day = str(latest_day.get("day") or "").strip()
    if not end_day:
        return {"rows": []}
    latest = parse_iso_day(end_day)
    latest_week_start = week_start_for(latest) if latest else None
    try:
        day_rows = db_rows(
            """
            SELECT day,total,ztf,lsst
            FROM alert_daily_counts
            WHERE day IS NOT NULL AND day != ''
            ORDER BY day DESC
            LIMIT 120
            """
        )
    except sqlite3.Error:
        day_rows = []
    try:
        sigma_rows = db_rows(
            """
            SELECT
                substr(received_utc, 1, 10) AS day,
                SUM(CASE WHEN anomaly_sigma < -3 THEN 1 ELSE 0 END) AS sigma_3,
                SUM(CASE WHEN anomaly_sigma < -5 THEN 1 ELSE 0 END) AS sigma_5,
                SUM(CASE WHEN anomaly_sigma < -7 THEN 1 ELSE 0 END) AS sigma_7
            FROM recent_alerts
            WHERE received_utc IS NOT NULL AND received_utc != ''
            GROUP BY substr(received_utc, 1, 10)
            ORDER BY day DESC
            LIMIT 120
            """
        )
    except sqlite3.Error:
        sigma_rows = []
    weeks = {}
    for row in day_rows:
        day = parse_iso_day(row.get("day"))
        if not day:
            continue
        start = week_start_for(day)
        key = start.isoformat()
        week = weeks.setdefault(key, {
            "start_day": key,
            "end_day": min(start + timedelta(days=6), latest).isoformat() if latest else (start + timedelta(days=6)).isoformat(),
            "label": "Week so far" if latest_week_start and start == latest_week_start else f"Week {start.isocalendar().week}",
            "date_range": week_date_range(start, latest if latest_week_start and start == latest_week_start else None),
            "total": 0,
            "ztf": 0,
            "lsst": 0,
            "sigma_3": 0,
            "sigma_5": 0,
            "sigma_7": 0,
        })
        for name in ("total", "ztf", "lsst", "sigma_3", "sigma_5", "sigma_7"):
            week[name] += int(row.get(name) or 0)
    for row in sigma_rows:
        day = parse_iso_day(row.get("day"))
        if not day:
            continue
        start = week_start_for(day)
        key = start.isoformat()
        if key not in weeks:
            continue
        for name in ("sigma_3", "sigma_5", "sigma_7"):
            weeks[key][name] += int(row.get(name) or 0)
    return {"rows": [weeks[key] for key in sorted(weeks.keys(), reverse=True)[:12]]}


def dashboard_payload(all_days=False, week_start=None):
    cache_key = f"{'all' if all_days else 'recent'}:{str(week_start or '')[:10]}"
    now = time.time()
    with STATE_LOCK:
        cached = STATE["dashboard_cache"].get(cache_key)
        if cached and now - cached["time"] < 15:
            return cached["payload"]
    stat_rows = db_rows("SELECT key, value FROM collector_stats WHERE key IN ('total_processed','latest_received_utc')")
    stat_map = {row["key"]: row["value"] for row in stat_rows}
    limit_sql = "" if all_days else "LIMIT 30"
    chart = db_rows(f"SELECT day,total,ztf,lsst,interesting FROM alert_daily_counts ORDER BY day DESC {limit_sql}")
    chart.reverse()
    latest_day = chart[-1] if chart else {}
    today_total = int(latest_day.get("total") or 0)
    today_ztf = int(latest_day.get("ztf") or 0)
    today_lsst = int(latest_day.get("lsst") or 0)
    today_interesting = int(latest_day.get("interesting") or 0)
    try:
        interesting_total = int((db_rows(
            "SELECT COALESCE(SUM(interesting), 0) AS n FROM alert_daily_counts"
        ) or [{"n": today_interesting}])[0].get("n") or 0)
    except sqlite3.Error:
        interesting_total = today_interesting
    try:
        lsst_counts = (db_rows(
            """
            SELECT
                COUNT(*) AS total,
                SUM(CASE WHEN mpc_designation IS NOT NULL AND mpc_designation != '' THEN 1 ELSE 0 END) AS matched,
                SUM(CASE WHEN mpc_designation IS NULL OR mpc_designation = '' THEN 1 ELSE 0 END) AS unmatched
            FROM lsst_sso_alerts
            """
        ) or [{"total": 0, "matched": 0, "unmatched": 0}])[0]
    except sqlite3.Error:
        lsst_counts = {"total": 0, "matched": 0, "unmatched": 0}
    try:
        priority_counts = (db_rows(
            """
            SELECT
                SUM(CASE WHEN anomaly_sigma < -3 THEN 1 ELSE 0 END) AS sigma_3,
                SUM(CASE WHEN anomaly_sigma < -5 THEN 1 ELSE 0 END) AS sigma_5,
                SUM(CASE WHEN anomaly_sigma < -7 THEN 1 ELSE 0 END) AS sigma_7
            FROM recent_alerts
            """
        ) or [{"sigma_3": 0, "sigma_5": 0, "sigma_7": 0}])[0]
    except sqlite3.Error:
        priority_counts = {"sigma_3": 0, "sigma_5": 0, "sigma_7": 0}
    try:
        today_priority_counts = (db_rows(
            """
            SELECT
                SUM(CASE WHEN anomaly_sigma < -3 THEN 1 ELSE 0 END) AS sigma_3,
                SUM(CASE WHEN anomaly_sigma < -5 THEN 1 ELSE 0 END) AS sigma_5,
                SUM(CASE WHEN anomaly_sigma < -7 THEN 1 ELSE 0 END) AS sigma_7
            FROM recent_alerts
            WHERE substr(received_utc, 1, 10) = ?
            """,
            [str(latest_day.get("day") or "")],
        ) or [{"sigma_3": 0, "sigma_5": 0, "sigma_7": 0}])[0]
    except sqlite3.Error:
        today_priority_counts = {"sigma_3": 0, "sigma_5": 0, "sigma_7": 0}
    try:
        anomaly_by_day = db_rows(
            """
            SELECT
                substr(received_utc, 1, 10) AS day,
                COUNT(*) AS total,
                SUM(CASE WHEN anomaly_sigma < -3 THEN 1 ELSE 0 END) AS sigma_3,
                SUM(CASE WHEN anomaly_sigma < -5 THEN 1 ELSE 0 END) AS sigma_5,
                SUM(CASE WHEN anomaly_sigma < -7 THEN 1 ELSE 0 END) AS sigma_7
            FROM recent_alerts
            WHERE received_utc IS NOT NULL AND received_utc != ''
            GROUP BY substr(received_utc, 1, 10)
            ORDER BY day DESC
            LIMIT 14
            """
        )
    except sqlite3.Error:
        anomaly_by_day = []
    lsst_total = int(lsst_counts.get("total") or 0)
    lsst_matched = int(lsst_counts.get("matched") or 0)
    lsst_unmatched = int(lsst_counts.get("unmatched") or 0)
    try:
        lsst_today_counts = (db_rows(
            """
            SELECT
                SUM(CASE WHEN mpc_designation IS NOT NULL AND mpc_designation != '' THEN 1 ELSE 0 END) AS matched,
                SUM(CASE WHEN mpc_designation IS NULL OR mpc_designation = '' THEN 1 ELSE 0 END) AS unmatched
            FROM lsst_sso_alerts
            WHERE substr(received_utc, 1, 10) = ?
            """,
            [str(latest_day.get("day") or "")],
        ) or [{"matched": 0, "unmatched": 0}])[0]
    except sqlite3.Error:
        lsst_today_counts = {"matched": 0, "unmatched": 0}
    lsst_today_matched = int(lsst_today_counts.get("matched") or 0)
    lsst_today_unmatched = int(lsst_today_counts.get("unmatched") or 0)
    stats = {
        "total_processed": stat_map.get("total_processed", "0"),
        "latest_received_utc": stat_map.get("latest_received_utc", latest_day.get("latest_received_utc", "")),
        "recent_alerts": today_total,
        "saved_candidates": interesting_total,
        "ztf_today": today_ztf,
        "lsst_today": lsst_today_matched,
        "lsst_today_all": today_lsst,
        "lsst_today_matched": lsst_today_matched,
        "lsst_today_unmatched": lsst_today_unmatched,
        "interesting_today": today_interesting,
        "interesting_total": interesting_total,
        "sigma_3_alerts": int(priority_counts.get("sigma_3") or 0),
        "sigma_5_alerts": int(priority_counts.get("sigma_5") or 0),
        "sigma_7_alerts": int(priority_counts.get("sigma_7") or 0),
        "sigma_3_today": int(today_priority_counts.get("sigma_3") or 0),
        "sigma_5_today": int(today_priority_counts.get("sigma_5") or 0),
        "sigma_7_today": int(today_priority_counts.get("sigma_7") or 0),
        "lsst_total_alerts": lsst_total,
        "matched_lsst_alerts": lsst_matched,
        "unmatched_lsst_alerts": lsst_unmatched,
        "mpc_queue_alerts": 0,
        "unread_notifications": today_total,
    }
    categories = {
        "normal": today_total,
        "ztf_today": today_ztf,
        "lsst_today": today_lsst,
        "lsst_all": lsst_total,
        "matched_lsst": lsst_matched,
        "unmatched_lsst": lsst_unmatched,
        "interesting": today_interesting,
    }
    try:
        service = subprocess.run(["systemctl", "is-active", STATE["service"]], text=True, capture_output=True, timeout=4).stdout.strip()
    except Exception:
        service = "unknown"
    payload = {
        "ok": True,
        "stats": stats,
        "categories": categories,
        "chart": chart,
        "anomaly_by_day": anomaly_by_day,
        "weekly_review": weekly_review_payload(latest_day, week_start),
        "service": service,
    }
    with STATE_LOCK:
        STATE["dashboard_cache"][cache_key] = {"time": now, "payload": payload}
    return payload


def alert_table(view):
    return {"recent live": "recent_alerts", "interesting saved": "alerts", "LSST SSO matched": "lsst_sso_alerts", "LSST SSO all": "lsst_sso_alerts"}.get(view, "recent_alerts")


def display_identifier(*values):
    for value in values:
        text = str(value or "").strip()
        if text and text.lower() not in {"0", "none", "null", "nan"}:
            return text
    return ""


def anomaly_level(row):
    sigma = to_float(row.get("anomaly_sigma"))
    if sigma is not None:
        if sigma < -7:
            return "sigma < -7"
        if sigma < -5:
            return "sigma < -5"
        if sigma < -3:
            return "sigma < -3"
        return "normal"
    return "unknown"


def normalize_activity_for_display(row):
    survey = str(row.get("survey") or row.get("observer") or "").lower()
    if survey != "lsst":
        return row
    primary = str(row.get("primary_category") or "").lower()
    score = to_float(row.get("activity_score"))
    has_activity_measurement = any(to_float(row.get(key)) is not None for key in ("delta_mag", "anomaly_sigma", "ssmagnr"))
    if score == 1 and primary == "unmatched_lsst" and not has_activity_measurement:
        row["activity_score"] = 0
        row["activity_class"] = "normal"
        row["primary_category"] = "normal"
        row["main_reason"] = "normal alert: LSST unmatched status alone is not an activity signal"
    return row


def alert_rows(payload):
    show = str(payload.get("show") or "").strip()
    show_map = {
        "latest": ("recent live", "all", "all"),
        "interesting": ("recent live", "all", "all"),
        "urgent": ("recent live", "all", "all"),
        "review": ("recent live", "all", "all"),
        "ztf_all": ("recent live", "all", "all"),
        "photometric": ("interesting saved", "all", "photometric"),
        "persistence": ("recent live", "all", "persistence"),
        "contamination": ("recent live", "all", "contamination"),
        "quality": ("recent live", "all", "quality_rejected"),
        "lsst_matched": ("LSST SSO matched", "all", "all"),
        "lsst_unmatched": ("LSST SSO all", "all", "all"),
        "lsst_all": ("LSST SSO all", "all", "all"),
    }
    if show in show_map:
        view, review, category = show_map[show]
    else:
        view = str(payload.get("view") or "recent live")
        review = str(payload.get("review") or "all")
        category = str(payload.get("category") or "all")
    table = alert_table(view)
    try:
        limit = max(1, min(MAX_LIMIT, int(payload.get("limit") or DEFAULT_LIMIT)))
    except (TypeError, ValueError):
        limit = DEFAULT_LIMIT
    conditions, params = [], []
    if review in {"urgent", "interesting", "review", "normal", "rejected"}:
        conditions.append("activity_class = ?")
        params.append(review)
    if category in {"urgent", "interesting", "review", "photometric", "persistence", "near_snowline", "contamination", "quality_rejected", "normal"}:
        conditions.append("(" + category_predicate(category) + ")")
    sigma_filters = {"review": -3, "interesting": -5, "urgent": -7}
    if show in sigma_filters:
        conditions.append("anomaly_sigma < ?")
        params.append(sigma_filters[show])
    if show == "ztf_all":
        conditions.append("LOWER(COALESCE(survey, observer, object_id, '')) LIKE ?")
        params.append("%ztf%")
    if view == "LSST SSO matched" or show == "lsst_all":
        conditions.append("mpc_designation IS NOT NULL AND mpc_designation != ''")
    if show == "lsst_unmatched":
        conditions.append("mpc_designation IS NULL")
    day = str(payload.get("day") or "").strip()
    if len(day) == 10 and day[4] == "-" and day[7] == "-":
        conditions.append("substr(received_utc, 1, 10) = ?")
        params.append(day)
    week_start = str(payload.get("weekStart") or "").strip()
    if len(week_start) == 10 and week_start[4] == "-" and week_start[7] == "-":
        conditions.append("substr(received_utc, 1, 10) BETWEEN ? AND date(?, '+6 day')")
        params.extend([week_start, week_start])
    search = str(payload.get("search") or "").strip()
    if search:
        like = f"%{search}%"
        if table == "lsst_sso_alerts":
            conditions.append("(object_id LIKE ? OR sso_id LIKE ? OR mpc_designation LIKE ? OR rubin_ssobject_id LIKE ?)")
            params.extend([like, like, like, like])
        else:
            conditions.append("(object_id LIKE ? OR sso_id LIKE ?)")
            params.extend([like, like])
    where = "WHERE " + " AND ".join(conditions) if conditions else ""
    lsst_fields = "mpc_designation, rubin_ssobject_id, sso_match_status, match_method, match_confidence, match_separation_arcsec, match_candidate_count, match_checked_utc"
    common_nulls = ", ".join(f"NULL AS {name}" for name in lsst_fields.split(", "))
    match_fields = lsst_fields if table == "lsst_sso_alerts" else common_nulls
    sql = f"""
        SELECT id,received_utc,survey,topic,observer,object_id,sso_id,jd,ra,dec,fid,magpsf,sigmapsf,ssmagnr,
               delta_mag,anomaly_sigma,activity_score,activity_class,interesting,rejected,main_reason,
               primary_category,alert_tags,{match_fields}
        FROM {table} {where} ORDER BY id DESC LIMIT ?
    """
    rows = db_rows(sql, [*params, limit])
    for row in rows:
        row["received_local"] = fmt_local_time(row.get("received_utc"))
        row["_source_table"] = table
        normalize_activity_for_display(row)
        row["anomaly_level"] = anomaly_level(row)
        row["object_id"] = display_identifier(row.get("object_id"), row.get("mpc_designation"), row.get("rubin_ssobject_id"))
    return {"ok": True, "table": table, "rows": rows, "columns": COLUMNS}


def alert_detail(payload):
    table = str(payload.get("table") or "recent_alerts")
    if table not in {"recent_alerts", "alerts", "lsst_sso_alerts"}:
        return {"ok": False, "error": "Invalid alert table."}
    try:
        row_id = int(payload.get("id"))
    except (TypeError, ValueError):
        return {"ok": False, "error": "Invalid alert id."}
    rows = db_rows(f"SELECT * FROM {table} WHERE id = ?", [row_id])
    if rows:
        normalize_activity_for_display(rows[0])
        rows[0]["received_local"] = fmt_local_time(rows[0].get("received_utc"))
        rows[0]["anomaly_level"] = anomaly_level(rows[0])
        rows[0]["object_id"] = display_identifier(
            rows[0].get("object_id"),
            rows[0].get("mpc_designation"),
            rows[0].get("rubin_ssobject_id"),
        )
        # FITS cutouts and the original raw alert payload can be many megabytes.
        rows[0].pop("row_json", None)
        rows[0].pop("alert_cutouts", None)
        rows[0] = {key: rows[0].get(key) for key in ALERT_DETAIL_FIELDS if rows[0].get(key) not in (None, "")}
    return {"ok": bool(rows), "row": rows[0] if rows else None}


def retry_mpc_match(payload):
    if str(payload.get("table") or "") != "lsst_sso_alerts":
        return {"ok": False, "error": "MPC matching is only available for an LSST SSO alert."}
    try:
        alert_id = int(payload.get("id"))
    except (TypeError, ValueError):
        return {"ok": False, "error": "Invalid LSST alert id."}
    if not db_rows("SELECT id FROM lsst_sso_alerts WHERE id = ?", [alert_id]):
        return {"ok": False, "error": "LSST alert not found."}
    now = datetime.now(timezone.utc).isoformat()
    db_write(
        """INSERT INTO mpc_crossmatch_queue
           (lsst_alert_id,status,attempts,next_attempt_utc,last_error,created_utc,updated_utc)
           VALUES (?, 'pending', 0, NULL, NULL, ?, ?)
           ON CONFLICT(lsst_alert_id) DO UPDATE SET
             status='pending', attempts=0, next_attempt_utc=NULL,
             last_error=NULL, updated_utc=excluded.updated_utc""",
        [alert_id, now, now],
    )
    return {"ok": True, "message": "MPC retry queued for this LSST alert."}


def notifications():
    return {"ok": True, "rows": db_rows("SELECT id,created_utc,severity,primary_category,activity_score,sso_id,object_id,message,reviewed FROM notifications ORDER BY id DESC LIMIT 300")}


def calibration():
    return {"ok": True, "rows": db_rows("SELECT key,count,interesting_count,best_score,last_seen_utc FROM calibration_stats ORDER BY count DESC,key ASC LIMIT 500")}


def read_config():
    with STATE_LOCK:
        path = Path(STATE["config_path"])
    if not path.exists():
        return {"thresholds": {}, "active_filters": dict(FILTER_DEFAULTS)}
    return json.loads(path.read_text(encoding="utf-8"))


def write_config(payload):
    old = read_config()
    thresholds = payload.get("thresholds") if isinstance(payload.get("thresholds"), dict) else old.get("thresholds", {})
    filters = payload.get("active_filters") if isinstance(payload.get("active_filters"), dict) else old.get("active_filters", FILTER_DEFAULTS)
    safe = {"thresholds": thresholds, "active_filters": {key: bool(filters.get(key, value)) for key, value in FILTER_DEFAULTS.items()}}
    with STATE_LOCK:
        path = Path(STATE["config_path"])
        service = STATE["service"]
    path.write_text(json.dumps(safe, indent=2, sort_keys=True), encoding="utf-8")
    subprocess.run(["systemctl", "restart", service], check=True, timeout=30)
    return {"ok": True, "config": safe, "message": "Applied config and restarted collector."}


def sky_rows(payload):
    ranges = {"last night": "-1 day", "last 7 days": "-7 day", "last 30 days": "-30 day", "all data": None}
    selection = ranges.get(str(payload.get("range") or "last 7 days"), "-7 day")
    source_sql = """
        SELECT id,received_utc,survey,observer,ra,dec,sso_id,object_id,activity_class,primary_category,'recent_alerts' AS source_table
        FROM recent_alerts WHERE ra IS NOT NULL AND dec IS NOT NULL
        UNION ALL
        SELECT id,received_utc,survey,observer,ra,dec,sso_id,object_id,activity_class,primary_category,'alerts' AS source_table
        FROM alerts WHERE ra IS NOT NULL AND dec IS NOT NULL
    """
    where, params = "", []
    if selection:
        where = "WHERE julianday(replace(substr(received_utc, 1, 19), 'T', ' ')) >= julianday('now', ?)"
        params.append(selection)
    rows = db_rows(f"SELECT * FROM ({source_sql}) {where} ORDER BY received_utc DESC LIMIT 8000", params)
    note = ""
    if not rows and selection:
        rows = db_rows(f"SELECT * FROM ({source_sql}) ORDER BY received_utc DESC LIMIT 8000")
        note = "Time filter returned no rows; showing the recent stored buffer."
    return {"ok": True, "rows": rows, "note": note}


def figure_url(fig):
    buffer = io.BytesIO()
    fig.savefig(buffer, format="png", dpi=120, bbox_inches="tight")
    return "data:image/png;base64," + base64.b64encode(buffer.getvalue()).decode("ascii")


def analysis_error_message(exc):
    text = str(exc).strip()
    if "No data found for SSO" in text:
        return text + " Try another SSO ID or choose an alert that has Fink SSO observations."
    if "Missing columns in Fink SSO response" in text:
        return text + " The remote Fink response is incomplete for this object."
    if "Fink SSO API failed" in text or "network/timeout error" in text:
        return "Fink SSO API did not return usable data right now. Please retry later."
    if "No SSO ID provided" in text:
        return "Enter an SSO ID first."
    return "Candidate analysis failed. Technical details are available in debug."


def full_alert_for_analysis(alert):
    if not isinstance(alert, dict):
        return None
    full = dict(alert)
    table = str(full.get("_source_table") or full.get("source_table") or "")
    if table not in {"recent_alerts", "alerts", "lsst_sso_alerts"}:
        table = str(full.get("table") or "")
    row_id = full.get("id")
    if table in {"recent_alerts", "alerts", "lsst_sso_alerts"} and row_id is not None:
        try:
            rows = db_rows(
                f"SELECT *, json_extract(row_json, '$.alert_cutouts') AS alert_cutouts_json FROM {table} WHERE id = ? LIMIT 1",
                [int(row_id)],
            )
        except Exception:
            rows = []
        if rows:
            db_row = rows[0]
            row_json = db_row.get("row_json")
            if isinstance(row_json, str) and row_json.strip():
                try:
                    parsed = json.loads(row_json)
                    if isinstance(parsed, dict):
                        full.update(parsed)
                except json.JSONDecodeError:
                    pass
            for key, value in db_row.items():
                if key not in {"row_json", "alert_cutouts_json"}:
                    full.setdefault(key, value)
            raw_cutouts = db_row.get("alert_cutouts_json") or db_row.get("alert_cutouts")
            if isinstance(raw_cutouts, str):
                try:
                    raw_cutouts = json.loads(raw_cutouts)
                except json.JSONDecodeError:
                    raw_cutouts = None
            if isinstance(raw_cutouts, dict):
                full["alert_cutouts"] = raw_cutouts
    if table:
        full["_source_table"] = table
    return full


def table_columns(table):
    if table not in {"recent_alerts", "alerts", "lsst_sso_alerts"}:
        return set()
    try:
        return {str(row.get("name")) for row in db_rows(f"PRAGMA table_info({table})")}
    except sqlite3.Error:
        return set()


def normalize_stored_alert(row, table):
    full = dict(row)
    row_json = full.pop("row_json", None)
    if isinstance(row_json, str) and row_json.strip():
        try:
            parsed = json.loads(row_json)
            if isinstance(parsed, dict):
                for key, value in parsed.items():
                    full.setdefault(key, value)
        except json.JSONDecodeError:
            pass
    raw_cutouts = full.pop("alert_cutouts_json", None) or full.get("alert_cutouts")
    if isinstance(raw_cutouts, str):
        try:
            raw_cutouts = json.loads(raw_cutouts)
        except json.JSONDecodeError:
            raw_cutouts = None
    if isinstance(raw_cutouts, dict):
        full["alert_cutouts"] = raw_cutouts
    full["_source_table"] = table
    return full


def alert_identity_key(alert):
    candid = (
        alert.get("candid")
        or alert.get("candidate.candid")
        or alert.get("dia_source_id")
        or alert.get("diaSourceId")
    )
    if candid not in (None, ""):
        return ("candid", str(candid))
    table = str(alert.get("_source_table") or alert.get("source_table") or "")
    row_id = alert.get("id")
    if table and row_id not in (None, ""):
        return ("db", table, str(row_id))
    jd = to_float(alert.get("jd"))
    if jd is not None:
        return (
            "obs",
            round(jd, 8),
            str(alert.get("object_id") or ""),
            str(alert.get("fid") or ""),
            str(alert.get("magpsf") or ""),
        )
    return ("fallback", json.dumps(alert, sort_keys=True, default=str)[:200])


def stored_alerts_for_analysis(sso_id, selected_alerts=None, limit=80):
    identifiers = {str(sso_id or "").strip()}
    for alert in selected_alerts or []:
        if not isinstance(alert, dict):
            continue
        for key in ("sso_id", "mpc_designation"):
            value = str(alert.get(key) or "").strip()
            if value:
                identifiers.add(value)
    identifiers = {value for value in identifiers if value}
    if not identifiers:
        return list(selected_alerts or [])

    selected = [alert for alert in (selected_alerts or []) if isinstance(alert, dict)]
    found = []
    for table in ("recent_alerts", "alerts", "lsst_sso_alerts"):
        cols = table_columns(table)
        if not cols:
            continue
        conditions, params = [], []
        if "sso_id" in cols:
            conditions.append(f"sso_id IN ({','.join('?' for _ in identifiers)})")
            params.extend(sorted(identifiers))
        if "mpc_designation" in cols:
            conditions.append(f"mpc_designation IN ({','.join('?' for _ in identifiers)})")
            params.extend(sorted(identifiers))
        if not conditions:
            continue
        json_cutouts = ", json_extract(row_json, '$.alert_cutouts') AS alert_cutouts_json" if "row_json" in cols else ""
        order_col = "jd" if "jd" in cols else "id"
        try:
            rows = db_rows(
                f"""
                SELECT *{json_cutouts}
                FROM {table}
                WHERE {' OR '.join(f'({condition})' for condition in conditions)}
                ORDER BY {order_col} ASC
                LIMIT ?
                """,
                [*params, int(limit)],
            )
        except sqlite3.Error:
            rows = []
        found.extend(normalize_stored_alert(row, table) for row in rows)

    merged, seen = [], set()
    for alert in [*selected, *found]:
        key = alert_identity_key(alert)
        if key in seen:
            continue
        seen.add(key)
        merged.append(alert)
    return merged


def db_cutout_history(alert, limit=24):
    sso_id = str(alert.get("sso_id") or "").strip()
    object_id = str(alert.get("object_id") or "").strip()
    if not sso_id and not object_id:
        return []
    candidate_limit = max(20, min(80, int(limit) * 4))
    rows = []
    try:
        if sso_id:
            for table in ("recent_alerts", "alerts"):
                rows.extend(db_rows(
                    f"""
                    SELECT received_utc, object_id, sso_id, jd, fid, magpsf, sigmapsf, row_json
                    FROM {table}
                    WHERE sso_id = ?
                    ORDER BY id DESC
                    LIMIT ?
                    """,
                    [sso_id, candidate_limit],
                ))
        elif object_id:
            for table in ("recent_alerts", "alerts"):
                rows.extend(db_rows(
                    f"""
                    SELECT received_utc, object_id, sso_id, jd, fid, magpsf, sigmapsf, row_json
                    FROM {table}
                    WHERE object_id = ?
                    ORDER BY id DESC
                    LIMIT ?
                    """,
                    [object_id, candidate_limit],
                ))
    except sqlite3.Error:
        rows = []
    history = []
    for row in reversed(rows):
        raw_cutouts = None
        row_json = row.pop("row_json", None)
        if isinstance(row_json, str) and row_json.strip():
            try:
                parsed = json.loads(row_json)
                if isinstance(parsed, dict):
                    raw_cutouts = parsed.get("alert_cutouts")
                    for key in ("observer", "survey", "dia_source_id", "Dhelio", "Dobs", "Phase"):
                        if key in parsed:
                            row[key] = parsed.get(key)
            except json.JSONDecodeError:
                continue
        expected_source = str(
            alert.get("survey") or alert.get("observer") or ""
        ).lower()
        row_source = str(row.get("survey") or row.get("observer") or "").lower()
        if (
            isinstance(raw_cutouts, dict)
            and (not expected_source or not row_source or expected_source == row_source)
        ):
            row["alert_cutouts"] = raw_cutouts
            history.append(row)
    return history


def ztf_irsa_science_url(row):
    try:
        filefracday = str(int(float(row["filefracday"]))).zfill(14)
        year = filefracday[:4]
        mmdd = filefracday[4:8]
        frac = filefracday[8:]
        field = int(float(row["field"]))
        ccdid = int(float(row["ccdid"]))
        qid = int(float(row["qid"]))
        filtercode = str(row.get("filtercode") or "").strip()
    except Exception:
        return None
    if not filtercode:
        return None
    filename = f"ztf_{filefracday}_{field:06d}_{filtercode}_c{ccdid:02d}_o_q{qid}_sciimg.fits"
    return f"{ZTF_IRSA_SCI_DATA_ROOT}/{year}/{mmdd}/{frac}/{filename}"


def ztf_irsa_search_science(ra, dec, jd):
    params = {
        "POS": f"{ra:.7f},{dec:.7f}",
        "SIZE": str(ZTF_ARCHIVE_QUERY_SIZE_DEG),
        "WHERE": (
            f"obsjd between {jd - ZTF_ARCHIVE_QUERY_HALF_WINDOW_DAYS:.6f} "
            f"and {jd + ZTF_ARCHIVE_QUERY_HALF_WINDOW_DAYS:.6f}"
        ),
        "RESPONSEFORMAT": "CSV",
    }
    response = requests.get(ZTF_IRSA_SCI_SEARCH_URL, params=params, timeout=8)
    response.raise_for_status()
    text = response.text
    if text.lstrip().startswith("<"):
        return []
    rows = list(csv.DictReader(io.StringIO(text)))
    rows.sort(key=lambda row: (
        abs((to_float(row.get("obsjd")) or jd) - jd),
        -(to_float(row.get("maglimit")) or 0.0),
    ))
    return rows


def fits_cutout_array_from_url(url, ra, dec):
    response = requests.get(
        url,
        params={"center": f"{ra:.7f},{dec:.7f}", "size": ZTF_ARCHIVE_CUTOUT_SIZE},
        timeout=12,
    )
    response.raise_for_status()
    content = response.content
    if content.startswith(b"\x1f\x8b"):
        content = gzip.decompress(content)
    with fits.open(io.BytesIO(content), memmap=False) as hdul:
        data = np.array(hdul[0].data, dtype=float)
    if data.ndim != 2 or not np.isfinite(data).any():
        return None
    return data


def ztf_archive_epoch_rows_from_horizons(sso_id, alert):
    alert_jd = to_float(alert.get("jd"))
    if alert_jd is None:
        return []
    start_jd = max(2458200.5, alert_jd - ZTF_ARCHIVE_LOOKBACK_DAYS)
    if start_jd >= alert_jd:
        return []
    epochs = np.linspace(start_jd, alert_jd, ZTF_ARCHIVE_SEARCH_EPOCHS)
    try:
        ids = resolve_analysis_ids(sso_id)
        horizons_id = resolve_horizons_smallbody_id(ids["horizons"], mpc_id=ids["mpc"])
        eph = Horizons(
            id=horizons_id,
            id_type="smallbody",
            location="I41",
            epochs=list(epochs),
        ).ephemerides(quantities="1,19,20,24", cache=True)
    except Exception:
        return []
    rows = []
    for row in eph:
        ra = to_float(row["RA"] if "RA" in eph.colnames else None)
        dec = to_float(row["DEC"] if "DEC" in eph.colnames else None)
        jd = to_float(row["datetime_jd"] if "datetime_jd" in eph.colnames else None)
        if ra is None or dec is None or jd is None:
            continue
        rows.append({
            "ra": ra,
            "dec": dec,
            "jd": jd,
            "Dhelio": to_float(row["r"] if "r" in eph.colnames else None),
            "Dobs": to_float(row["delta"] if "delta" in eph.colnames else None),
            "Phase": to_float(row["alpha"] if "alpha" in eph.colnames else None),
        })
    return rows


def load_one_ztf_archive_cutout(seed):
    ra = to_float(seed.get("ra"))
    dec = to_float(seed.get("dec"))
    jd = to_float(seed.get("jd"))
    if ra is None or dec is None or jd is None:
        return None
    try:
        matches = ztf_irsa_search_science(ra, dec, jd)
        if not matches:
            return None
        match = matches[0]
        url = ztf_irsa_science_url(match)
        if not url:
            return None
        image = fits_cutout_array_from_url(url, ra, dec)
        if image is None:
            return None
        obsjd = to_float(match.get("obsjd")) or jd
        try:
            received_utc = Time(obsjd, format="jd").to_datetime(timezone=timezone.utc).isoformat()
        except Exception:
            received_utc = str(match.get("obsdate") or "")
        return {
            "survey": "ztf",
            "observer": "ZTF",
            "object_id": seed.get("object_id") or "ZTF archive",
            "sso_id": seed.get("sso_id"),
            "jd": obsjd,
            "received_utc": received_utc,
            "ra": ra,
            "dec": dec,
            "fid": match.get("fid"),
            "filtercode": match.get("filtercode"),
            "magpsf": None,
            "archive_source": "ZTF IRSA science archive",
            "archive_id": str(match.get("pid") or match.get("filefracday") or url),
            "Science": image,
            "Difference": None,
            "Template": None,
            "Dhelio": seed.get("Dhelio"),
            "Dobs": seed.get("Dobs"),
            "Phase": seed.get("Phase"),
        }
    except Exception:
        return None


def load_ztf_archive_cutouts(sso_id, alert, existing_rows, max_new):
    if max_new <= 0:
        return []
    existing_keys = {
        round(to_float(row.get("jd")) or -1, 4)
        for row in existing_rows
    }
    seeds = list(ztf_archive_epoch_rows_from_horizons(sso_id, alert))
    filtered = []
    seen_seed = set()
    for seed in sorted(seeds, key=lambda row: to_float(row.get("jd")) or 0):
        jd = to_float(seed.get("jd"))
        if jd is None:
            continue
        key = round(jd, 1)
        if key in seen_seed or round(jd, 4) in existing_keys:
            continue
        seen_seed.add(key)
        next_seed = dict(seed)
        next_seed["sso_id"] = sso_id
        next_seed["object_id"] = alert.get("object_id")
        filtered.append(next_seed)
    if not filtered:
        return []
    selected = evenly_spaced_rows(filtered, min(len(filtered), max(ZTF_ARCHIVE_SEARCH_EPOCHS, max_new * 2)))
    rows = []
    seen_archive = set()
    pool = ThreadPoolExecutor(max_workers=ZTF_ARCHIVE_MAX_WORKERS)
    try:
        futures = [pool.submit(load_one_ztf_archive_cutout, seed) for seed in selected]
        try:
            for future in as_completed(futures, timeout=ZTF_ARCHIVE_TOTAL_TIMEOUT):
                row = future.result()
                if not row:
                    continue
                archive_id = row.get("archive_id")
                if archive_id in seen_archive:
                    continue
                seen_archive.add(archive_id)
                rows.append(row)
                if len(rows) >= max_new:
                    break
        except FuturesTimeoutError:
            pass
    finally:
        pool.shutdown(wait=False, cancel_futures=True)
    return sorted(rows, key=lambda row: to_float(row.get("jd")) or float("inf"))


def cutout_history_for_alert(sso_id, alert, limit=CUTOUT_GALLERY_PAGE_SIZE):
    alert = full_alert_for_analysis(alert)
    if not alert:
        return [], 0
    try:
        requested_limit = max(
            CUTOUT_GALLERY_PAGE_SIZE,
            min(CUTOUT_GALLERY_MAX_EPOCHS, int(limit or CUTOUT_GALLERY_PAGE_SIZE)),
        )
        object_id = str(alert.get("object_id") or "").strip()
        is_ztf = str(alert.get("survey") or alert.get("observer") or "").lower() == "ztf" or object_id.upper().startswith("ZTF")
        source = "ztf" if is_ztf else "lsst"
        stored = db_cutout_history(alert, requested_limit)
        if is_ztf:
            remote = fetch_fink_cutout_candidates(
                sso_id=str(sso_id or alert.get("sso_id") or "").strip(),
                object_id=object_id,
            )
        else:
            remote = fetch_fink_lsst_cutout_candidates(
                str(
                    alert.get("mpc_designation")
                    or sso_id
                    or alert.get("sso_id")
                    or ""
                ).strip()
            )
        for row in remote:
            row["survey"] = source
            row["observer"] = source.upper()
        master = merge_cutout_histories(remote, stored, [dict(alert)])
        available_rows = select_general_cutout_epochs(
            master,
            alert,
            CUTOUT_GALLERY_MAX_EPOCHS,
        )
        total_available = len(available_rows)
        download_pool = select_general_cutout_epochs(
            available_rows,
            alert,
            requested_limit,
        )
        already_loaded, need_download = [], []
        for row in download_pool:
            cutouts = row.get("alert_cutouts")
            arrays = {
                kind: image_array_from_embedded_cutout(cutouts.get(kind))
                if isinstance(cutouts, dict)
                else None
                for kind in ("Difference", "Science", "Template")
            }
            if all(array is not None for array in arrays.values()):
                already_loaded.append(row)
            elif (
                row.get("dia_source_id")
                or (
                    row.get("object_id")
                    and row.get("candid") not in (None, "")
                )
            ):
                need_download.append(row)
        loaded = merge_cutout_histories(
            already_loaded,
            load_cutouts_for_candidates(need_download),
        )
        if is_ztf and len(loaded) < requested_limit:
            archive_rows = load_ztf_archive_cutouts(
                str(sso_id or alert.get("sso_id") or "").strip(),
                alert,
                merge_cutout_histories(loaded, master),
                requested_limit - len(loaded),
            )
            loaded = merge_cutout_histories(loaded, archive_rows)
            total_available = max(total_available, len(loaded))
        loaded = enrich_cutout_history_with_horizons(str(sso_id or alert.get("sso_id") or "").strip(), loaded)
        return loaded, total_available
    except Exception:
        return [{"gallery_error": traceback.format_exc()}], 0


def cutout_label(row, idx, total):
    stamp = fmt_german_time(row.get("received_utc"))[:16]
    label = f"{idx}/{total}"
    if stamp:
        label += f" - {stamp}"
    fid = row.get("fid")
    absolute_mag = cutout_absolute_magnitude(row)
    if fid not in (None, ""):
        label += f" | F{fid}"
    if absolute_mag is not None:
        label += f" | H {absolute_mag:.2f}"
    if row.get("archive_source"):
        label += " | archive"
    geometry = []
    dhelio = to_float(row.get("Dhelio") or row.get("heliocentric_distance") or row.get("heliocentricDistance") or row.get("heliodist") or row.get("r"))
    dobs = to_float(row.get("Dobs") or row.get("topocentric_distance") or row.get("topocentricDistance") or row.get("observer_distance") or row.get("delta"))
    phase = to_float(row.get("Phase") or row.get("phase_angle") or row.get("phaseAngle") or row.get("alpha"))
    if dhelio is not None:
        geometry.append(f"r {dhelio:.2f} AU")
    if dobs is not None:
        geometry.append(f"Delta {dobs:.2f} AU")
    if phase is not None:
        geometry.append(f"phase {phase:.1f} deg")
    if geometry:
        label += " | " + " | ".join(geometry)
    return label


def cutout_absolute_magnitude(row):
    mag = to_float(row.get("magpsf"))
    if mag is None:
        return None
    reduced = to_float(row.get("magpsf_red"))
    r_au = to_float(row.get("Dhelio") or row.get("heliocentric_distance") or row.get("heliocentricDistance") or row.get("heliodist") or row.get("r"))
    delta_au = to_float(row.get("Dobs") or row.get("topocentric_distance") or row.get("topocentricDistance") or row.get("observer_distance") or row.get("delta"))
    phase_deg = to_float(row.get("Phase") or row.get("phase_angle") or row.get("phaseAngle") or row.get("alpha"))
    if reduced is None and r_au is not None and delta_au is not None and r_au > 0 and delta_au > 0:
        reduced = mag - 5.0 * math.log10(r_au * delta_au)
    if reduced is None:
        return None
    if phase_deg is None or phase_deg < 0:
        return reduced
    slope_g = to_float(row.get("G") or row.get("slope") or row.get("slope_parameter"))
    if slope_g is None:
        slope_g = 0.15
    phase_rad = math.radians(max(0.0, min(180.0, phase_deg)) / 2.0)
    tan_half = math.tan(phase_rad)
    phi1 = math.exp(-3.33 * (tan_half ** 0.63))
    phi2 = math.exp(-1.87 * (tan_half ** 1.22))
    phase_function = (1.0 - slope_g) * phi1 + slope_g * phi2
    if not math.isfinite(phase_function) or phase_function <= 0:
        return reduced
    return reduced + 2.5 * math.log10(phase_function)


def make_single_cutout_figure(array, title, kind, row, vmin=None, vmax=None):
    fig = Figure(figsize=(5.8, 5.2), dpi=120)
    ax = fig.add_subplot(111)
    cmap = "coolwarm" if kind == "Difference" else "gray"
    image = ax.imshow(array, cmap=cmap, origin="lower", vmin=vmin, vmax=vmax)
    center_y, center_x = np.array(array.shape) / 2.0
    mark_color = "#22d3ee" if kind == "Difference" else "white"
    ax.axhline(center_y - 0.5, color=mark_color, alpha=0.45, linewidth=0.8)
    ax.axvline(center_x - 0.5, color=mark_color, alpha=0.45, linewidth=0.8)
    ax.add_patch(Circle((center_x - 0.5, center_y - 0.5), radius=5, fill=False, edgecolor=mark_color, linewidth=1.2))
    add_cutout_angular_scale(ax, array.shape, cutout_pixel_scale_arcsec(row))
    ax.axis("off")
    fig.suptitle(title, fontsize=11, y=0.98)
    if kind == "Difference":
        cbar = fig.colorbar(image, ax=ax, orientation="vertical", fraction=0.04, pad=0.02)
        cbar.ax.tick_params(labelsize=7)
    fig.subplots_adjust(left=0.02, right=0.93 if kind == "Difference" else 0.98, bottom=0.02, top=0.90)
    return fig


def normalized_registration_image(array):
    image = np.array(array, dtype=float, copy=True)
    finite = np.isfinite(image)
    if not finite.any():
        return None
    median = float(np.nanmedian(image[finite]))
    image[~finite] = median
    p1, p99 = np.percentile(image, [1, 99])
    if not np.isfinite(p1) or not np.isfinite(p99) or p1 == p99:
        return None
    image = np.clip(image, p1, p99)
    image = image - float(np.mean(image))
    std = float(np.std(image))
    if not np.isfinite(std) or std <= 0:
        return None
    return image / std


def estimate_integer_shift(reference, moving, max_shift=8):
    if reference is None or moving is None or reference.shape != moving.shape:
        return None
    ref = normalized_registration_image(reference)
    mov = normalized_registration_image(moving)
    if ref is None or mov is None:
        return None
    corr = signal.correlate2d(ref, mov, mode="same", boundary="fill", fillvalue=0)
    cy, cx = np.array(corr.shape) // 2
    y0, y1 = max(0, cy - max_shift), min(corr.shape[0], cy + max_shift + 1)
    x0, x1 = max(0, cx - max_shift), min(corr.shape[1], cx + max_shift + 1)
    window = corr[y0:y1, x0:x1]
    if window.size == 0:
        return None
    peak_index = np.unravel_index(int(np.nanargmax(window)), window.shape)
    peak_y = y0 + peak_index[0]
    peak_x = x0 + peak_index[1]
    shift_y = int(cy - peak_y)
    shift_x = int(cx - peak_x)
    peak = float(corr[peak_y, peak_x])
    background = np.delete(window.ravel(), peak_index[0] * window.shape[1] + peak_index[1])
    if background.size:
        bg_std = float(np.nanstd(background))
        bg_med = float(np.nanmedian(background))
        if bg_std > 0 and (peak - bg_med) / bg_std < 4.0:
            return None
    if abs(shift_y) > max_shift or abs(shift_x) > max_shift:
        return None
    return shift_y, shift_x


def align_template_to_science(science, template, row):
    shift = estimate_integer_shift(science, template)
    if shift is None or shift == (0, 0):
        return template
    fill = float(np.nanmedian(template[np.isfinite(template)])) if np.isfinite(template).any() else 0.0
    aligned = ndimage.shift(
        template,
        shift=shift,
        order=1,
        mode="constant",
        cval=fill,
        prefilter=False,
    )
    row["template_display_shift"] = f"{shift[0]},{shift[1]} px"
    return aligned


def shift_cutout_without_wrap(image, shift_y, shift_x):
    if image is None:
        return None
    array = np.asarray(image, dtype=float)
    result = np.full(array.shape, np.nan, dtype=float)
    height, width = array.shape
    source_y0 = max(0, -int(shift_y))
    source_y1 = min(height, height - int(shift_y))
    source_x0 = max(0, -int(shift_x))
    source_x1 = min(width, width - int(shift_x))
    target_y0 = max(0, int(shift_y))
    target_y1 = min(height, height + int(shift_y))
    target_x0 = max(0, int(shift_x))
    target_x1 = min(width, width + int(shift_x))
    if source_y1 > source_y0 and source_x1 > source_x0:
        result[target_y0:target_y1, target_x0:target_x1] = array[
            source_y0:source_y1,
            source_x0:source_x1,
        ]
    return result


def science_peak_center_shift(science):
    if science is None:
        return 0, 0
    array = np.asarray(science, dtype=float)
    if array.ndim != 2:
        return 0, 0
    finite = np.isfinite(array)
    if not finite.any():
        return 0, 0
    height, width = array.shape
    center_y = height // 2
    center_x = width // 2
    half_window = max(5, min(height, width) // 4)
    y0, y1 = max(0, center_y - half_window), min(height, center_y + half_window + 1)
    x0, x1 = max(0, center_x - half_window), min(width, center_x + half_window + 1)
    window = array[y0:y1, x0:x1]
    finite_window = np.isfinite(window)
    if not finite_window.any():
        return 0, 0
    background = float(np.nanmedian(window[finite_window]))
    signal_image = np.where(finite_window, window - background, -np.inf)
    peak_y, peak_x = np.unravel_index(int(np.nanargmax(signal_image)), signal_image.shape)
    shift_y = center_y - (y0 + int(peak_y))
    shift_x = center_x - (x0 + int(peak_x))
    if abs(shift_y) > half_window or abs(shift_x) > half_window:
        return 0, 0
    return int(shift_y), int(shift_x)


def center_cutout_triplet_on_science(science, difference=None, template=None, row=None):
    shift_y, shift_x = science_peak_center_shift(science)
    if shift_y == 0 and shift_x == 0:
        return science, difference, template
    centered_science = shift_cutout_without_wrap(science, shift_y, shift_x)
    centered_difference = (
        shift_cutout_without_wrap(difference, shift_y, shift_x)
        if difference is not None
        else None
    )
    centered_template = (
        shift_cutout_without_wrap(template, shift_y, shift_x)
        if template is not None
        else None
    )
    if isinstance(row, dict):
        row["science_display_shift"] = f"{shift_y},{shift_x} px"
    return centered_science, centered_difference, centered_template


def cutout_gallery_for_alert(sso_id, alert, limit=CUTOUT_GALLERY_PAGE_SIZE):
    history, total_available = cutout_history_for_alert(sso_id, alert, limit)
    if history and history[0].get("gallery_error"):
        fig = make_cutout_error_figure(history[0]["gallery_error"])
        return {
            "items": [{"kind": "Difference", "name": "Cutout history error", "label": "error", "url": figure_url(fig)}],
            "available": 0,
            "limit": limit,
            "hasMore": False,
        }
    epochs = []
    for row in history:
        cutouts = row.get("alert_cutouts")
        has_direct_array = any(isinstance(row.get(kind), np.ndarray) for kind in ("Science", "Difference", "Template"))
        if not isinstance(cutouts, dict) and not has_direct_array:
            continue
        science = (
            row.get("Science")
            if isinstance(row.get("Science"), np.ndarray)
            else image_array_from_embedded_cutout((cutouts or {}).get("Science"))
        )
        difference = (
            row.get("Difference")
            if isinstance(row.get("Difference"), np.ndarray)
            else image_array_from_embedded_cutout((cutouts or {}).get("Difference"))
        )
        template = (
            row.get("Template")
            if isinstance(row.get("Template"), np.ndarray)
            else image_array_from_embedded_cutout((cutouts or {}).get("Template"))
        )
        if science is None:
            continue
        if difference is not None and difference.shape != science.shape:
            difference = None
        if template is not None:
            if template.shape != science.shape:
                template = None
        science, difference, template = center_cutout_triplet_on_science(science, difference, template, row)
        epochs.append({**row, "Science": science, "Difference": difference, "Template": template})
    if not epochs:
        return {
            "items": [],
            "available": total_available,
            "limit": limit,
            "hasMore": total_available > int(limit),
        }
    epochs.sort(key=lambda row: (to_float(row.get("jd")) or float("inf"), str(row.get("received_utc") or "")))
    diff_samples = [
        np.abs(row["Difference"][np.isfinite(row["Difference"])])
        for row in epochs
        if row.get("Difference") is not None and np.isfinite(row["Difference"]).any()
    ]
    diff_values = np.concatenate(diff_samples) if diff_samples else np.array([])
    diff_limit = max(float(np.percentile(diff_values, 99)) if diff_values.size else 1.0, 1e-6)
    items = []
    kinds = ("Difference", "Science", "Template")
    total = len(epochs)
    for kind in kinds:
        for idx, row in enumerate(epochs, start=1):
            array = row.get(kind)
            if array is None:
                continue
            label = cutout_label(row, idx, total)
            source = str(row.get("survey") or row.get("observer") or "unknown").upper()
            source_label = f"[{source}] {label}"
            if kind in {"Science", "Template"} and row.get("science_display_shift"):
                source_label += " | science-centered"
            if kind == "Difference":
                vmin, vmax = -diff_limit, diff_limit
            else:
                values = array[np.isfinite(array)]
                if values.size:
                    vmin, vmax = np.percentile(values, [1, 99])
                    if not np.isfinite(vmin) or not np.isfinite(vmax) or vmin == vmax:
                        vmin, vmax = None, None
                else:
                    vmin, vmax = None, None
            fig = make_single_cutout_figure(array, f"{kind} cutout: {source_label}", kind, row, vmin=vmin, vmax=vmax)
            items.append({
                "kind": kind,
                "name": f"{kind} {source_label}",
                "label": source_label,
                "epoch": idx,
                "epochKey": str(row.get("dia_source_id") or row.get("candid") or row.get("jd") or idx),
                "total": total,
                "source": source,
                "url": figure_url(fig),
            })
    loaded_limit = max(CUTOUT_GALLERY_PAGE_SIZE, int(limit or CUTOUT_GALLERY_PAGE_SIZE))
    return {
        "items": items,
        "available": total_available,
        "limit": loaded_limit,
        "hasMore": total_available > loaded_limit,
    }


def build_difference_gallery_figure(history, reference=None, similar_parameters=False):
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
        if difference is None:
            difference = science - float(np.nanmedian(science))
        epochs.append({**row, "science_array": science, "difference_array": difference})
    if not epochs:
        return build_cutout_evolution_figure(history, reference=reference, similar_parameters=similar_parameters)
    epochs.sort(key=lambda row: (to_float(row.get("jd")) or float("inf"), str(row.get("received_utc") or "")))
    shape_counts = {}
    for row in epochs:
        shape = row["difference_array"].shape
        shape_counts[shape] = shape_counts.get(shape, 0) + 1
    common_shape = max(shape_counts, key=shape_counts.get)
    epochs = [row for row in epochs if row["difference_array"].shape == common_shape][-8:]
    values = np.concatenate([
        np.abs(row["difference_array"][np.isfinite(row["difference_array"])])
        for row in epochs
        if np.isfinite(row["difference_array"]).any()
    ]) if epochs else np.array([])
    residual_limit = float(np.percentile(values, 99)) if values.size else 1.0
    residual_limit = max(residual_limit, 1e-6)
    columns = max(1, len(epochs))
    fig = Figure(figsize=(max(11, 2.25 * columns), 4.4), dpi=100)
    fig._astroprak_preserve_layout = True
    axes = fig.subplots(1, columns, squeeze=False)[0]
    image = None
    for ax, row in zip(axes, epochs):
        diff = row["difference_array"]
        image = ax.imshow(diff, cmap="coolwarm", origin="lower", vmin=-residual_limit, vmax=residual_limit)
        center_y, center_x = np.array(diff.shape) / 2.0
        ax.axhline(center_y - 0.5, color="white", alpha=0.3, linewidth=0.7)
        ax.axvline(center_x - 0.5, color="white", alpha=0.3, linewidth=0.7)
        ax.add_patch(Circle((center_x - 0.5, center_y - 0.5), radius=5, fill=False, edgecolor="#22d3ee", linewidth=1.1))
        add_cutout_angular_scale(ax, diff.shape, cutout_pixel_scale_arcsec(row))
        title = fmt_german_time(row.get("received_utc"))[:16]
        absolute_mag = cutout_absolute_magnitude(row)
        fid = row.get("fid")
        if fid not in (None, ""):
            title += f"\nFilter {fid}"
        if absolute_mag is not None:
            title += f" | H {absolute_mag:.2f}"
        ax.set_title(title, fontsize=7)
        ax.axis("off")
    object_label = (epochs[-1].get("sso_id") or epochs[-1].get("object_id") or "selected object") if epochs else "selected object"
    fig.suptitle(f"Cutout evolution - Difference images: {object_label}", fontsize=12, y=0.98)
    fig.text(0.5, 0.91, f"{len(epochs)} Difference cutouts across available epochs", ha="center", fontsize=9)
    if image is not None:
        cax = fig.add_axes([0.925, 0.20, 0.010, 0.55])
        cbar = fig.colorbar(image, cax=cax, orientation="vertical")
        cbar.set_label("Difference [ADU]", fontsize=7)
        cbar.ax.tick_params(labelsize=7)
    fig.subplots_adjust(left=0.03, right=0.91, bottom=0.08, top=0.82, wspace=0.08)
    return "02 Cutout evolution", fig


def build_difference_epoch_figures(history, reference=None):
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
        if difference is None:
            difference = science - float(np.nanmedian(science))
        epochs.append({**row, "difference_array": difference})
    if not epochs:
        fallback = build_cutout_evolution_figure(history, reference=reference, similar_parameters=False)
        return [fallback] if fallback is not None else []
    epochs.sort(key=lambda row: (to_float(row.get("jd")) or float("inf"), str(row.get("received_utc") or "")))
    shape_counts = {}
    for row in epochs:
        shape = row["difference_array"].shape
        shape_counts[shape] = shape_counts.get(shape, 0) + 1
    common_shape = max(shape_counts, key=shape_counts.get)
    epochs = [row for row in epochs if row["difference_array"].shape == common_shape][-10:]
    values = np.concatenate([
        np.abs(row["difference_array"][np.isfinite(row["difference_array"])])
        for row in epochs
        if np.isfinite(row["difference_array"]).any()
    ]) if epochs else np.array([])
    residual_limit = float(np.percentile(values, 99)) if values.size else 1.0
    residual_limit = max(residual_limit, 1e-6)
    figures = []
    total = len(epochs)
    for idx, row in enumerate(epochs, start=1):
        diff = row["difference_array"]
        fig = Figure(figsize=(7.2, 6.2), dpi=120)
        ax = fig.add_subplot(111)
        image = ax.imshow(diff, cmap="coolwarm", origin="lower", vmin=-residual_limit, vmax=residual_limit)
        center_y, center_x = np.array(diff.shape) / 2.0
        ax.axhline(center_y - 0.5, color="white", alpha=0.35, linewidth=0.8)
        ax.axvline(center_x - 0.5, color="white", alpha=0.35, linewidth=0.8)
        ax.add_patch(Circle((center_x - 0.5, center_y - 0.5), radius=5, fill=False, edgecolor="#22d3ee", linewidth=1.2))
        add_cutout_angular_scale(ax, diff.shape, cutout_pixel_scale_arcsec(row))
        ax.axis("off")
        object_label = row.get("sso_id") or row.get("object_id") or "selected object"
        stamp = fmt_german_time(row.get("received_utc"))[:16]
        absolute_mag = cutout_absolute_magnitude(row)
        fid = row.get("fid")
        subtitle = stamp
        if fid not in (None, ""):
            subtitle += f" | Filter {fid}"
        if absolute_mag is not None:
            subtitle += f" | H {absolute_mag:.2f}"
        fig.suptitle(f"Cutout evolution - Difference image: {object_label}", fontsize=12, y=0.97)
        fig.text(0.5, 0.925, f"{idx} / {total}   {subtitle}", ha="center", fontsize=10)
        cbar = fig.colorbar(image, ax=ax, orientation="vertical", fraction=0.035, pad=0.02)
        cbar.set_label("Difference [ADU]", fontsize=8)
        cbar.ax.tick_params(labelsize=8)
        fig.subplots_adjust(left=0.02, right=0.90, bottom=0.03, top=0.88)
        name = f"02 Cutout evolution {idx}/{total}"
        if stamp:
            name += f" - {stamp}"
        figures.append((name, fig))
    return figures


def make_cutout_error_figure(message):
    fig = Figure(figsize=(10, 4), dpi=100)
    ax = fig.add_subplot(111)
    ax.axis("off")
    ax.text(0.02, 0.95, "Cutout history could not be loaded.", va="top", ha="left", fontsize=12, weight="bold")
    ax.text(0.02, 0.82, message[:1200], va="top", ha="left", family="monospace", fontsize=8, wrap=True)
    fig.tight_layout()
    return fig


def cutout_gallery_payload(payload):
    alert = payload.get("alert")
    sso_id = str(payload.get("sso") or "").strip()
    if not isinstance(alert, dict) or not sso_id:
        return {"ok": False, "error": "Selected alert and SSO ID are required."}
    try:
        limit = int(payload.get("limit") or CUTOUT_GALLERY_PAGE_SIZE)
    except (TypeError, ValueError):
        limit = CUTOUT_GALLERY_PAGE_SIZE
    gallery = cutout_gallery_for_alert(sso_id, alert, limit=limit)
    return {"ok": True, **gallery}


def start_analysis(sso_id, injected_alerts=None):
    if not sso_id:
        return {"ok": False, "error": "Enter an SSO ID first."}
    injected_alerts = [alert for alert in (injected_alerts or []) if isinstance(alert, dict)]
    injected_alerts = stored_alerts_for_analysis(sso_id, injected_alerts)
    job_id = uuid.uuid4().hex
    with STATE_LOCK:
                STATE["jobs"][job_id] = {"status": "running", "message": f"Running candidate analysis for {sso_id}."}

    def worker():
        try:
            result = analyze_sso_deep(sso_id, injected_alerts=injected_alerts)
            gallery = (
                cutout_gallery_for_alert(sso_id, injected_alerts[0])
                if injected_alerts
                else {"items": [], "available": 0, "limit": CUTOUT_GALLERY_PAGE_SIZE, "hasMore": False}
            )
            payload = {
                "summary": result["summary_text"],
                "figures": [{"name": name, "url": figure_url(fig)} for name, fig in result["figures"]],
                "cutouts": gallery["items"],
                "cutoutMeta": {
                    key: gallery[key]
                    for key in ("available", "limit", "hasMore")
                },
            }
            with STATE_LOCK:
                STATE["jobs"][job_id] = {"status": "complete", "result": payload, "message": "Analysis complete."}
        except Exception as exc:
            with STATE_LOCK:
                STATE["jobs"][job_id] = {
                    "status": "error",
                    "error": analysis_error_message(exc),
                    "debug": traceback.format_exc(),
                    "message": "Analysis failed.",
                }

    threading.Thread(target=worker, daemon=True).start()
    return {"ok": True, "jobId": job_id, "message": "Candidate analysis started."}


INDEX_HTML = r'''<!doctype html><html><head><meta charset="utf-8"><title>AstroPrak Server Dashboard</title><style>
:root{--bg:#08111f;--panel:#17243a;--panel2:#22314d;--line:#31425f;--text:#f8fbff;--muted:#c4d4ef;--accent:#4f7ff0;--accent2:#6b8ff5;--green:#63c76d;--orange:#e37b33;--yellow:#f0d84b;--danger:#ef4444;--detail-left:26vw;--detail-top:52%}
*{box-sizing:border-box}
html,body{margin:0;min-height:100%;background:var(--bg);color:var(--text);font-family:Arial,Helvetica,sans-serif;font-size:16px;letter-spacing:0}
body.dragging{user-select:none;cursor:col-resize}
button,select,input{font:inherit}
button,select,input[type=text],input:not([type]){background:#071120;color:var(--text);border:1px solid #c7d3e8;padding:10px 14px;border-radius:0}
input,select{background:#fff;color:#000}
button{cursor:pointer}
button:hover{border-color:#fff;background:#10213a}
button.active,.tabs button.active{background:var(--accent);color:#fff;border-color:#6fa0ff}
.tabs{display:flex;align-items:stretch;background:#071120;border-bottom:2px solid #9fb0c7;position:sticky;top:0;z-index:50}
.tabs button{background:#071120;color:#fff;border:0;border-right:1px solid #9fb0c7;border-radius:0;padding:16px 26px}
.page{display:none;padding:32px}
.page.active{display:block}
.header,.toolbar{display:flex;align-items:center;gap:14px;margin-bottom:20px;flex-wrap:wrap}
.header{justify-content:space-between}
h1,h2,h3{margin:0 0 14px;font-weight:700;color:#fff}
h1{font-size:40px}
h2{font-size:34px}
h3{font-size:26px}
p{line-height:1.45}
.muted{color:var(--muted)}
.cards{display:grid;grid-template-columns:repeat(2,minmax(320px,1fr));gap:26px;margin:18px 0 54px}
.card,.overview-block,.method-section,.follow-box{background:var(--panel);border:1px solid #253752;padding:26px}
.card .value{font-size:64px;font-weight:700;margin:44px 0 34px;line-height:1.05}
.overview-card{display:grid;grid-template-columns:minmax(220px,.95fr) minmax(240px,1fr);gap:28px;align-items:start}
.overview-card .value{margin:36px 0 30px}
.overview-card .subsection{border-left:1px solid #2c3c55;padding-left:28px}
.overview-card .subsection .value{font-size:44px;margin:26px 0 24px}
.overview-card .latest-value{font-size:28px}
.card-breakdown{width:100%;border-collapse:collapse;color:var(--muted);margin-top:-16px}
.card-breakdown td{padding:6px 0;border:0}
.card-breakdown td:last-child{text-align:right;color:#fff;font-weight:700}
.score-mini,.overview-table,.glossary{width:100%;border-collapse:collapse}
.score-mini td,.overview-table td,.glossary td,.glossary th{padding:10px 0;border-bottom:1px solid #2c3c55}
.overview-table th{color:var(--muted);font-size:15px;font-weight:700;padding:8px 0;border-bottom:1px solid #2c3c55}
.score-mini td:last-child,.overview-table td:last-child{text-align:right;font-weight:700}
.score-mini tr,.overview-table tr{cursor:pointer}
.score-mini tr:hover,.overview-table tr:hover{background:#223454}
.block-head{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-bottom:10px}
.block-head h3{margin:0}
.block-head button{padding:8px 10px;font-size:15px}
.anomaly-days th:not(:first-child),.anomaly-days td:not(:first-child){text-align:right;cursor:pointer}
.anomaly-days td:first-child{color:var(--muted);font-weight:700}
.categories{display:grid;grid-template-columns:1fr 1fr;gap:22px}
.weekly-review{margin:0 0 34px}
.weekly-review .overview-block{padding:22px 24px}
.weekly-table{width:100%;border-collapse:collapse}
.weekly-table th,.weekly-table td{padding:9px 12px}
.weekly-table th{position:static}
.weekly-table td:not(:first-child),.weekly-table th:not(:first-child){text-align:right}
.weekly-table tbody tr{cursor:pointer}
.weekly-table tbody td.clickable{color:#fff;font-weight:700}
.week-label{font-weight:700}
.week-range{display:block;color:var(--muted);font-size:15px;margin-top:2px}
.chart{background:var(--panel);border:1px solid #253752;padding:24px;margin-top:8px}
.chart-legend{display:flex;gap:22px;color:var(--muted);font-size:22px;margin:0 0 10px}
.chart-legend span::before{content:"";display:inline-block;width:15px;height:15px;margin-right:8px;vertical-align:middle}
.chart-legend .ztf::before,.bar-segment.ztf{background:#4c66df}
.chart-legend .lsst::before,.bar-segment.lsst{background:#df7a34}
.chart-legend .other::before,.bar-segment.other{background:#7f8aa0}
.chart-grid{display:grid;grid-template-columns:112px 1fr;grid-template-rows:285px 42px;gap:0 10px;align-items:stretch}
.y-axis{grid-row:1;display:flex;align-items:stretch;color:var(--muted);border-right:1px solid #8291aa;position:relative}
.y-title{writing-mode:vertical-rl;transform:rotate(180deg);align-self:center;margin-right:20px}
.y-ticks{display:flex;flex-direction:column;justify-content:space-between;text-align:right;width:72px;padding-right:14px}
.bar-row{display:flex;align-items:flex-end;gap:4px;border-bottom:1px solid #8291aa;overflow:hidden}
.bar-group{height:100%;flex:1;min-width:18px;display:flex;flex-direction:column-reverse;justify-content:flex-start}
.bar-segment{width:100%}
.x-title{grid-column:1;color:var(--muted);align-self:center;text-align:right;padding-right:14px}
.x-axis{grid-column:2;display:flex;gap:4px;color:var(--muted)}
.x-tick{flex:1;min-width:18px;text-align:center;font-size:16px;padding-top:10px}
.table-panel{background:var(--panel);border:1px solid #253752;overflow:auto;max-height:calc(100vh - 210px)}
table{border-collapse:collapse}
#alerts{width:100%;min-width:1380px}
th,td{text-align:left;padding:14px 16px;border-bottom:1px solid #2b3c56;white-space:nowrap}
th{font-weight:700;background:#1b2943;position:sticky;top:0;z-index:1}
tbody tr{cursor:pointer}
tbody tr:hover,tbody tr.selected{background:#263a5d}
tbody tr.sigma3{background:#1d3044}
tbody tr.sigma5{background:#332b28}
tbody tr.sigma7{background:#42242a}
tbody tr.sigma3:hover,tbody tr.sigma5:hover,tbody tr.sigma7:hover{filter:brightness(1.18)}
.follow-box{display:flex;align-items:center;gap:16px;margin:4px 0 20px;font-size:23px}
.follow-badge{display:inline-block;padding:10px 16px;font-weight:700;color:#071120;background:#cbd5e1}
.follow-badge.yes{background:var(--green)}
.follow-badge.no{background:#94a3b8}
.follow-text{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.detail-grid{display:grid;grid-template-columns:var(--detail-left) 18px 1fr;height:calc(100vh - 300px);min-height:560px;background:#0d1728}
.details-side{display:grid;grid-template-rows:var(--detail-top) 22px 1fr;min-width:220px;min-height:0}
.splitter{background:#2f4367;border:1px solid #8aa0c0;z-index:20}
.v-splitter{cursor:col-resize}
.h-splitter{cursor:row-resize}
.v-splitter:hover,.h-splitter:hover{background:#5272a6}
details{background:var(--panel);min-height:0;overflow:auto}
summary{cursor:pointer;font-weight:700;padding:12px 16px;border-bottom:1px solid #26364d}
details>pre,details>div{height:calc(100% - 45px)}
pre{margin:0;padding:22px;white-space:pre-wrap;color:#fff;font-family:Consolas,"Courier New",monospace;font-weight:700;line-height:1.25}
.figure-panel{background:var(--panel);min-width:0;display:grid;grid-template-rows:auto auto minmax(0,1fr) 160px;overflow:hidden}
.figure-panel.cutout-view{grid-template-rows:auto 0 minmax(0,1fr) 150px}
.figure-tools{grid-row:1;display:flex;align-items:center;gap:10px;padding:12px;background:#101b2e;flex-wrap:wrap}
.kind-tools{display:flex;gap:10px}
.spacer{flex:1}
#figureSelect{grid-row:2;width:100%;border:0;border-top:1px solid #233451}
.figure-stage{grid-row:3;background:#fff;min-height:0;display:flex;align-items:center;justify-content:center;overflow:auto}
.figure-panel.cutout-view .figure-stage{overflow:hidden;padding:10px}
#figure{max-width:100%;max-height:100%;object-fit:contain}
.figure-placeholder{color:#0f172a;padding:28px;text-align:center}
.thumb-strip{grid-row:4;display:none;gap:12px;overflow-x:auto;overflow-y:hidden;background:#0e1728;border-top:3px solid #33435e;padding:10px 14px;align-items:center}
.thumb{width:190px;height:132px;flex:0 0 190px;padding:0;background:#0b1322;border:3px solid #26364d;position:relative;overflow:hidden}
.thumb.active{border-color:var(--accent2)}
.thumb img{width:100%;height:100%;object-fit:cover;display:block;background:#fff}
.thumb span{position:absolute;left:0;right:0;bottom:0;background:rgba(7,17,32,.9);color:#fff;font-size:15px;padding:4px 6px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.method-layout{display:grid;grid-template-columns:minmax(0,1fr) 380px;gap:24px;align-items:start}
.method-section{margin-bottom:20px}
.method-section h3{font-size:28px}
.method-section li{margin:9px 0;line-height:1.35}
.method-side{position:sticky;top:92px}
.glossary th{color:var(--muted)}
.workflow{padding-left:26px}
.callout{background:#20314f;border-left:6px solid var(--accent);padding:18px 20px;line-height:1.4}
@media (max-width:1100px){.cards,.categories,.method-layout,.overview-card{grid-template-columns:1fr}.overview-card .subsection{border-left:0;border-top:1px solid #2c3c55;padding-left:0;padding-top:22px}.detail-grid{grid-template-columns:1fr;height:auto}.v-splitter{display:none}.figure-panel{min-height:620px}.details-side{height:520px}.method-side{position:static}}
</style></head><body>
<nav class="tabs"><button class="active" data-page="start">Start</button><button data-page="live">Live alerts</button><button data-page="details">Details</button><button data-page="method">Data & method</button></nav>
<section id="start" class="page active"><div class="header"><div><h1>AstroPrak Server Monitor</h1><div class="muted">%%SERVER_INFO%%</div><p id="connection" class="muted">Connecting...</p></div><button onclick="refreshAll()">Refresh / reconnect</button></div><div class="header"><h2>Total overview</h2></div><div class="cards"><div class="card overview-card"><div><h3>Total processed</h3><div id="total" class="value">-</div><div id="service" class="muted"></div></div><div class="subsection"><h3>Anomaly levels</h3><table class="score-mini"><tr onclick="openCategory('review')"><td>sigma &lt; -3</td><td id="sigma3">-</td></tr><tr onclick="openCategory('interesting')"><td>sigma &lt; -5</td><td id="sigma5">-</td></tr><tr onclick="openCategory('urgent')"><td>sigma &lt; -7</td><td id="sigma7">-</td></tr></table><div class="muted">current anomaly thresholds</div></div></div><div class="card overview-card"><div><h3>Latest alert</h3><div id="latest" class="value latest-value">-</div><div id="latestSub" class="muted">Europe/Berlin</div></div><div class="subsection"><h3>Today alerts</h3><div id="inbox" class="value">-</div><div id="inboxSub" class="muted"></div></div></div></div><div id="weeklyReview" class="weekly-review"></div><div class="header" style="margin-top:32px"><h2>Alerts per day</h2><label><input id="allDays" type="checkbox" onchange="loadDashboard()"> Expand to all days</label></div><div class="chart"><div id="chartGrid" class="chart-grid"><div id="yAxis" class="y-axis"></div><div id="chart" class="bar-row"></div><div class="x-title">Datum</div><div id="xAxis" class="x-axis"></div></div></div></section>
<section id="method" class="page"><div class="header"><div><h1>Data & method</h1><p class="muted">How the website finds and checks unusual Solar System Object alerts.</p></div></div><div class="method-layout"><div><div class="method-section"><h3>Goal</h3><p>This website helps to find unusual SSO or asteroid alerts from ZTF and LSST-style alert data, then quickly check whether a candidate is scientifically interesting or probably caused by measurement problems, image artifacts, or an uncertain association.</p><p>The follow-up planning itself happens outside this website: after a promising candidate is identified, the next step is to check on external telescope planning tools which observatories could observe the object soon.</p></div><div class="method-section"><h3>Data sources</h3><ul><li><b>ZTF/Fink alerts:</b> new ZTF alerts arrive through the Fink Kafka live stream, are written by the collector into the local database, and are then shown by this website.</li><li><b>Fink API:</b> used later during candidate analysis to load SSO history, object history, and alert cutouts; it is not the main way new alerts enter the dashboard.</li><li><b>ZTF/IRSA archive:</b> if only few ZTF alert cutouts are available, Horizons positions are used to search the public ZTF image archive for additional Science cutouts near earlier epochs.</li><li><b>LSST/Rubin-style alerts:</b> Rubin alerts would enter through LSST/Rubin broker or alert-stream access, which requires an approved account/request; the Live alerts LSST filter only shows LSST alerts with a known MPC/SSO assignment, because candidate analysis needs an object ID that MPC and JPL Horizons can resolve.</li><li><b>MPC references:</b> known Solar System Object identifiers and observation history.</li><li><b>JPL Horizons:</b> predicted position, heliocentric distance r, observer distance Delta, and phase angle.</li></ul></div><div class="method-section"><h3>What is an alert?</h3><p>An alert is one detection of an object in one image. It contains the observing time, sky position, filter, measured brightness, object identifiers, survey information, and sometimes contextual information such as the expected magnitude or Solar System match.</p></div><div class="method-section"><h3>What is being searched for?</h3><p>The automatic search is mainly a brightness-anomaly check: alerts are prioritized when the measured brightness is stronger than expected from the available model or history.</p><ul><li><b>Main automatic signal:</b> brightness deviation, especially delta_mag and anomaly_sigma.</li><li><b>After selection:</b> Difference cutouts are inspected to check whether the signal looks real or like an image/subtraction artifact.</li><li><b>Context checks:</b> MPC and JPL Horizons are used to verify the object association, position, distance to Sun/Earth, and phase angle.</li><li><b>Goal:</b> find candidates that may be worth short-term follow-up observations with other telescopes.</li></ul></div><div class="method-section"><h3>Anomaly levels</h3><p>The website no longer uses a separate scoring system for candidate selection. Alerts are grouped directly by <b>anomaly_sigma</b>, meaning how strongly the measured brightness deviates from the expected brightness.</p><table class="glossary"><tr><th>anomaly_sigma</th><th>Level</th><th>Meaning</th></tr><tr><td>&gt;= -3</td><td>normal</td><td>not selected by anomaly filters</td></tr><tr><td>&lt; -3</td><td>sigma &lt; -3</td><td>brightness anomaly, worth checking</td></tr><tr><td>&lt; -5</td><td>sigma &lt; -5</td><td>strong brightness anomaly</td></tr><tr><td>&lt; -7</td><td>sigma &lt; -7</td><td>very strong brightness anomaly</td></tr></table><p>More negative values mean the object appears brighter or more unusual than expected. Cutouts, MPC, and Horizons are used afterwards to check whether the candidate is real and scientifically useful.</p></div><div class="method-section"><h3>Live alerts</h3><p>The table lists incoming alerts with object IDs, brightness values, delta_mag, anomaly_sigma, and the derived anomaly level. The LSST filter only shows alerts with a known MPC/SSO assignment, because candidate analysis needs an object that MPC and JPL Horizons can resolve.</p><p>Clicking an alert opens the detail view and starts the candidate analysis automatically.</p></div><div class="method-section"><h3>Dashboard summaries</h3><p>The start page also shows database summaries for orientation: total processed alerts, current anomaly-level counts, the latest alert time, today's alert counts, and a weekly overview.</p><p>In the weekly overview, each row represents one calendar week with its date range. Clicking a week opens the Live alerts table filtered to that week; clicking one of the sigma columns additionally applies the matching anomaly-level filter.</p><p>These dashboard summaries are not additional scientific tests. They only aggregate alerts that are already stored in the local database.</p></div><div class="method-section"><h3>Candidate analysis</h3><ul><li>Loads the selected alert details.</li><li>Queries MPC, Fink history, and JPL Horizons context.</li><li>Checks whether the alert position agrees with the Horizons prediction.</li><li>Builds light curves, residual plots, and phase/context plots.</li><li>Shows cutouts as Difference, Science, and Template images.</li></ul></div><div class="method-section"><h3>Cutouts</h3><p><b>Science</b> is the current image. <b>Template</b> is the reference image. <b>Difference</b> is Science minus Template and is usually the most useful view for spotting changes.</p><p>The gallery first retrieves original ZTF or LSST alert cutouts from Fink. For ZTF candidates with only few alert cutouts, it also uses Horizons positions to fetch additional Science cutouts from the public ZTF/IRSA archive. These extra images are marked as archive. Difference and Template views only show images when real alert cutouts provide them.</p></div><div class="method-section"><h3>Limitations</h3><ul><li>The anomaly level is a prioritization aid, not proof of activity.</li><li>Cutouts can contain artifacts, bad subtraction, nearby sources, or image-edge effects.</li><li>A position match can be uncertain if the alert position and Horizons prediction differ by several arcseconds.</li><li>Additional ZTF archive cutouts are Science images, not broker subtraction images.</li><li>Missing fields can reduce how confidently ZTF and LSST alerts can be compared.</li></ul></div></div><aside class="method-side"><div class="method-section"><h3>Important quantities</h3><table class="glossary"><tr><th>Quantity</th><th>Meaning</th></tr><tr><td>magpsf</td><td>Measured point-source magnitude.</td></tr><tr><td>delta_mag</td><td>Difference from expected brightness.</td></tr><tr><td>anomaly_sigma</td><td>Statistical brightness anomaly.</td></tr><tr><td>r</td><td>Distance from the Sun in AU.</td></tr><tr><td>Delta</td><td>Distance from Earth/observer in AU.</td></tr><tr><td>phase</td><td>Sun-object-observer phase angle.</td></tr><tr><td>position separation</td><td>Angular distance between alert position and Horizons prediction.</td></tr></table></div><div class="method-section"><h3>Typical workflow</h3><ol class="workflow"><li>Use the weekly overview or anomaly-level counts to choose a time range or priority level.</li><li>Open the filtered Live alerts table.</li><li>Select one candidate alert.</li><li>Check the follow-up summary.</li><li>Inspect Difference cutouts over time.</li><li>Check light curve and analysis plots.</li><li>Decide whether external follow-up planning is worthwhile.</li></ol></div><div class="callout">The website supports finding and checking candidates. Telescope scheduling and observability planning are the next step on external tools.</div></aside></div></section>
<section id="live" class="page"><div class="toolbar"><button onclick="loadAlerts()">Refresh now</button><button onclick="resetLiveFilters()">Reset filters</button><label><input id="livePoll" type="checkbox" checked> Live polling</label><span id="tableStatus" class="muted"></span></div><div class="toolbar"><label>Show <select id="showFilter" onchange="loadAlerts()"><option value="latest">All recent alerts</option><option value="review">sigma &lt; -3</option><option value="interesting">sigma &lt; -5</option><option value="urgent">sigma &lt; -7</option><option value="ztf_all">ZTF alerts</option><option value="lsst_all">LSST alerts</option></select></label><label>Week <input id="weekFilter" type="date" onchange="loadAlerts()"></label><label>Day <input id="dayFilter" type="date" onchange="loadAlerts()"></label><button onclick="clearDateFilters()">Clear dates</button><label>Search <input id="searchFilter" size="14" onchange="loadAlerts()"></label><label>Limit <input id="limit" value="200" size="6"></label></div><div class="table-panel"><table id="alerts"></table></div></section>
<section id="details" class="page"><div class="toolbar"><h2 style="flex:1">Selected alert details</h2><button onclick="showPage('live')">Back to live alerts</button></div><div class="toolbar"><label>SSO ID <input id="analysisSso" size="18"></label><button onclick="useSelected()">Use selected</button><button onclick="runAnalysis()">Analyze candidate</button><button onclick="copyCandidateSummary()">Copy summary</button></div><div id="candidateSummary" class="follow-box"><span id="followBadge" class="follow-badge no">Follow-up: maybe</span><span id="followText" class="follow-text">Select a candidate to see a short follow-up assessment.</span><span id="copyStatus" class="muted"></span></div><div class="detail-grid"><div class="details-side"><details open><summary>Alert details</summary><pre id="detail">Select an alert to load its full details.</pre></details><div class="splitter h-splitter" data-splitter="horizontal"></div><details open><summary>Candidate analysis</summary><pre id="analysis">Select an alert with an SSO ID and run candidate analysis.</pre></details></div><div class="splitter v-splitter" data-splitter="vertical"></div><div class="figure-panel"><div class="figure-tools"><button id="plotMode" class="active" onclick="showPlotMode()">Plots</button><button id="cutoutMode" onclick="showCutoutMode()">Cutouts</button><div id="kindTools" class="kind-tools"><button id="kindDifference" onclick="setCutoutKind('Difference')">Difference</button><button id="kindScience" onclick="setCutoutKind('Science')">Science</button><button id="kindTemplate" onclick="setCutoutKind('Template')">Template</button></div><span class="spacer"></span><button id="prevCutout" onclick="stepCutout(-1)">Previous</button><span id="cutoutCounter" class="muted"></span><button id="nextCutout" onclick="stepCutout(1)">Next</button><button id="moreCutouts" onclick="loadMoreCutouts()">Load more</button></div><select id="figureSelect" onchange="showFigure()"></select><div class="figure-stage"><img id="figure" style="display:none"><div id="figurePlaceholder" class="figure-placeholder">Run candidate analysis to show light curves and cutouts.</div></div><div id="thumbStrip" class="thumb-strip"></div></div></div></section>
<script>
const COLUMNS=%%COLUMNS%%, MINIMAL_COLUMNS=%%MINIMAL_COLUMNS%%, FILTER_DEFAULTS=%%FILTER_DEFAULTS%%;let rows=[],selected=null,figures=[],plotFigures=[],cutoutItems=[],cutoutMeta={available:0,limit:12,hasMore:false},cutoutKind='Difference',figureMode='plots',cutoutIndex=0,config={thresholds:{},active_filters:{...FILTER_DEFAULTS}},visible=[...COLUMNS],activeTable='recent_alerts',dashboardLoading=false,alertsLoading=false,hasDashboardData=false,showPreviousAnomalyDays=false,weeklyCandidates=[],selectedWeeklyStart='';
const labels={};
function api(path,payload={},timeoutMs=60000){const ctrl=new AbortController(),timer=setTimeout(()=>ctrl.abort(),timeoutMs);return fetch(path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload),signal:ctrl.signal}).then(async r=>{const d=await r.json();if(!d.ok)throw Error(d.error||'Request failed');return d}).catch(error=>{if(error.name==='AbortError')throw Error('Request timed out. Please refresh.');throw error}).finally(()=>clearTimeout(timer))}
function setDetailWidth(value){const v=Math.max(14,Math.min(50,Number(value)||26));document.documentElement.style.setProperty('--detail-left',v+'vw');localStorage.setItem('astroprakDetailWidth',String(v))}
function setDetailTop(value){const v=Math.max(25,Math.min(75,Number(value)||52));document.documentElement.style.setProperty('--detail-top',v+'%');localStorage.setItem('astroprakDetailTop',String(v))}
function initSplitters(){setDetailWidth(localStorage.getItem('astroprakDetailWidth')||26);setDetailTop(localStorage.getItem('astroprakDetailTop')||52);document.querySelectorAll('[data-splitter]').forEach(handle=>{handle.onpointerdown=event=>{event.preventDefault();const type=handle.dataset.splitter;document.body.classList.add('dragging');handle.setPointerCapture(event.pointerId);const move=e=>{if(type==='vertical'){const grid=document.querySelector('.detail-grid').getBoundingClientRect();setDetailWidth((e.clientX-grid.left)/grid.width*100)}else{const side=document.querySelector('.details-side').getBoundingClientRect();setDetailTop((e.clientY-side.top)/side.height*100)}};const up=()=>{document.body.classList.remove('dragging');handle.removeEventListener('pointermove',move);handle.removeEventListener('pointerup',up);handle.removeEventListener('pointercancel',up)};handle.addEventListener('pointermove',move);handle.addEventListener('pointerup',up);handle.addEventListener('pointercancel',up)}})}
function candidateAssessment(row,analysisText=''){row=row||{};const sigma=Number(row.anomaly_sigma),delta=Number(row.delta_mag),level=String(row.anomaly_level||'').trim(),klass=String(row.activity_class||''),reason=String(row.main_reason||row.primary_category||'').trim();let label='maybe',title='Follow-up: maybe',why=[];if(Number.isFinite(sigma)&&sigma<-7){label='yes';title='Follow-up: yes'}else if(klass==='normal'||klass==='rejected'||row.rejected){label='no';title='Follow-up: no'}if(Number.isFinite(delta)&&delta<=-2){label='yes';title='Follow-up: yes';why.push(`brightened by ${Math.abs(delta).toFixed(1)} mag`)}else if(Number.isFinite(delta)&&delta<=-1){why.push(`brightened by ${Math.abs(delta).toFixed(1)} mag`)}if(Number.isFinite(sigma))why.push(`sigma ${sigma.toFixed(2)}`);if(level)why.push(level);if(reason)why.push(reason);if(analysisText&&/UNSICHER|uncertain|maybe/i.test(analysisText))why.push('analysis uncertain');return{label,title,text:why.slice(0,4).join(' | ')||'Run candidate analysis for a stronger assessment.'}}
function renderCandidateSummary(analysisText=''){const a=candidateAssessment(selected,analysisText);const badge=document.getElementById('followBadge'),text=document.getElementById('followText');badge.className='follow-badge '+a.label;badge.textContent=a.title;text.textContent=a.text;return `${a.title}\nSSO ID: ${document.getElementById('analysisSso').value||selected?.sso_id||''}\n${a.text}`}
async function copyCandidateSummary(){const text=renderCandidateSummary(document.getElementById('analysis').textContent);let ok=false;try{if(navigator.clipboard&&window.isSecureContext){await navigator.clipboard.writeText(text);ok=true}}catch(e){}if(!ok){const ta=document.createElement('textarea');ta.value=text;ta.style.position='fixed';ta.style.left='-9999px';ta.style.top='0';document.body.appendChild(ta);ta.focus();ta.select();try{ok=document.execCommand('copy')}catch(e){ok=false}document.body.removeChild(ta)}document.getElementById('copyStatus').textContent=ok?'copied':'copy failed';setTimeout(()=>document.getElementById('copyStatus').textContent='',1800)}
function splitFigures(){plotFigures=figures.filter(f=>!/similar parameters/i.test(f.name||''))}
function activeCutouts(){return cutoutItems.filter(f=>f.kind===cutoutKind)}
function currentCutout(){return activeCutouts()[cutoutIndex]}
function cutoutEpochOf(item,index){return Number(item?.epoch)||index+1}
function cutoutTotalOf(item,items){return Number(item?.total)||items.length}
function nearestCutoutIndex(items,epoch){if(!items.length)return 0;let best=0,bestDist=Infinity;items.forEach((item,i)=>{const dist=Math.abs(cutoutEpochOf(item,i)-epoch);if(dist<bestDist){best=i;bestDist=dist}});return best}
function updateThumbs(){const strip=document.getElementById('thumbStrip'),items=activeCutouts();if(!strip)return;strip.style.display=figureMode==='cutouts'&&items.length?'flex':'none';strip.innerHTML=items.map((f,i)=>`<button class="thumb ${i===cutoutIndex?'active':''}" onclick="selectCutout(${i})" title="${f.label||f.name}"><img src="${f.url}" alt=""><span>${f.label||f.name}</span></button>`).join('');const active=strip.querySelector('.thumb.active');if(active)active.scrollIntoView({block:'nearest',inline:'nearest'})}
function updateFigureControls(){const items=activeCutouts(),item=items[cutoutIndex],more=document.getElementById('moreCutouts'),panel=document.querySelector('.figure-panel');if(panel)panel.classList.toggle('cutout-view',figureMode==='cutouts');document.getElementById('plotMode').classList.toggle('active',figureMode==='plots');document.getElementById('cutoutMode').classList.toggle('active',figureMode==='cutouts');document.getElementById('kindTools').style.display=figureMode==='cutouts'?'flex':'none';['Difference','Science','Template'].forEach(k=>document.getElementById('kind'+k).classList.toggle('active',cutoutKind===k));document.getElementById('prevCutout').style.display=figureMode==='cutouts'?'inline-block':'none';document.getElementById('nextCutout').style.display=figureMode==='cutouts'?'inline-block':'none';document.getElementById('cutoutCounter').style.display=figureMode==='cutouts'?'inline':'none';document.getElementById('cutoutCounter').textContent=item?`${cutoutEpochOf(item,cutoutIndex)} / ${cutoutTotalOf(item,items)}`:'';more.style.display=figureMode==='cutouts'&&cutoutMeta.hasMore?'inline-block':'none';more.textContent=cutoutMeta.hasMore?`Load more (${Math.min(Number(cutoutMeta.limit)||items.length,Number(cutoutMeta.available)||items.length)}/${cutoutMeta.available})`:'Load more';updateThumbs()}
function showPlotMode(){figureMode='plots';const sel=document.getElementById('figureSelect');sel.style.display='block';sel.innerHTML=plotFigures.map((f,i)=>`<option value="${i}">${f.name}</option>`).join('');updateFigureControls();showFigure()}
function showCutoutMode(){figureMode='cutouts';cutoutIndex=Math.max(0,Math.min(cutoutIndex,activeCutouts().length-1));const sel=document.getElementById('figureSelect');sel.style.display='none';updateFigureControls();showFigure()}
function setCutoutKind(kind){const oldItems=activeCutouts(),oldItem=oldItems[cutoutIndex],epoch=cutoutEpochOf(oldItem,cutoutIndex);cutoutKind=kind;cutoutIndex=nearestCutoutIndex(activeCutouts(),epoch);showCutoutMode()}
function selectCutout(index){cutoutIndex=Math.max(0,Math.min(Number(index)||0,activeCutouts().length-1));showFigure()}
function stepCutout(delta){const items=activeCutouts();if(!items.length)return;cutoutIndex=(cutoutIndex+delta+items.length)%items.length;updateFigureControls();showFigure()}
async function loadMoreCutouts(){if(!selected||!cutoutMeta.hasMore)return;const button=document.getElementById('moreCutouts'),oldItem=currentCutout(),oldKey=oldItem?.epochKey,oldEpoch=cutoutEpochOf(oldItem,cutoutIndex);button.disabled=true;button.textContent='Loading...';try{const s=document.getElementById('analysisSso').value.trim(),nextLimit=Math.min(48,(Number(cutoutMeta.limit)||12)+12);const d=await api('/api/cutouts',{sso:s,limit:nextLimit,alert:{...selected,_source_table:activeTable}},120000);cutoutItems=d.items||[];cutoutMeta={available:Number(d.available)||0,limit:Number(d.limit)||nextLimit,hasMore:Boolean(d.hasMore)};const items=activeCutouts();let nextIndex=oldKey?items.findIndex(item=>item.epochKey===oldKey):-1;if(nextIndex<0)nextIndex=nearestCutoutIndex(items,oldEpoch);cutoutIndex=Math.max(0,nextIndex);showCutoutMode()}catch(error){document.getElementById('figurePlaceholder').textContent='Could not load more cutouts: '+error.message}finally{button.disabled=false;updateFigureControls()}}
function showPage(id){document.querySelectorAll('.page').forEach(x=>x.classList.remove('active'));document.getElementById(id).classList.add('active');document.querySelectorAll('[data-page]').forEach(x=>x.classList.toggle('active',x.dataset.page===id))}
document.querySelectorAll('[data-page]').forEach(x=>x.onclick=()=>showPage(x.dataset.page));
initSplitters();
function esc(v){return String(v).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;')}
function fmt(v){return v==null?'':String(v)}
function fmtCell(col,v){if(v==null)return '';const n=Number(v);if(Number.isFinite(n)){if(['magpsf','sigmapsf','ssmagnr','delta_mag','anomaly_sigma'].includes(col))return n.toFixed(2);if(['ra','dec'].includes(col))return n.toFixed(6);if(col==='jd')return n.toFixed(5);if(['match_confidence','match_separation_arcsec'].includes(col))return n.toFixed(3)}return String(v)}
function anomalyRowClass(row){const sigma=Number(row?.anomaly_sigma);if(!Number.isFinite(sigma))return '';if(sigma<-7)return 'sigma7';if(sigma<-5)return 'sigma5';if(sigma<-3)return 'sigma3';return ''}
function render(id,cols,data,onClick){const t=document.getElementById(id);t.innerHTML='<thead><tr>'+cols.map(c=>`<th>${c}</th>`).join('')+'</tr></thead><tbody>'+data.map((r,i)=>`<tr data-i="${i}" class="${anomalyRowClass(r)}">${cols.map(c=>{const shown=fmtCell(c,r[c]);return `<td title="${esc(shown)}">${esc(shown)}</td>`}).join('')}</tr>`).join('')+'</tbody>';if(onClick)t.querySelectorAll('tbody tr').forEach(tr=>tr.onclick=()=>onClick(data[+tr.dataset.i],tr))}
function dateObj(v){const text=fmt(v);if(!text)return null;const iso=/(?:Z|[+-]\d\d:\d\d)$/.test(text)?text:text+'Z';const d=new Date(iso);return Number.isNaN(d.getTime())?null:d}
function berlin(v){const d=dateObj(v);return d?new Intl.DateTimeFormat('de-DE',{day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit',second:'2-digit',timeZone:'Europe/Berlin'}).format(d):fmt(v)}
function latestFriendly(v){const d=dateObj(v);if(!d)return fmt(v)||'-';return new Intl.DateTimeFormat('de-DE',{weekday:'short',day:'2-digit',month:'2-digit',year:'numeric',hour:'2-digit',minute:'2-digit',second:'2-digit',timeZone:'Europe/Berlin'}).format(d)}
function shortDay(value){const parts=String(value||'').split('-');return parts.length===3?`${parts[2]}.${parts[1]}`:String(value||'')}
function sigmaDayRows(days){const shown=(days||[]).slice(0,showPreviousAnomalyDays?14:1);if(!shown.length)return '<tr><td>No days</td><td></td><td></td><td></td></tr>';return shown.map(day=>`<tr><td>${esc(day.day||'')}</td><td onclick="openDayCategory('review','${esc(day.day||'')}')">${Number(day.sigma_3||0).toLocaleString('de-DE')}</td><td onclick="openDayCategory('interesting','${esc(day.day||'')}')">${Number(day.sigma_5||0).toLocaleString('de-DE')}</td><td onclick="openDayCategory('urgent','${esc(day.day||'')}')">${Number(day.sigma_7||0).toLocaleString('de-DE')}</td></tr>`).join('')}
function renderAnomalyDayTable(days){return `<div class="overview-block"><div class="block-head"><h3>${showPreviousAnomalyDays?'Anomaly levels by day':'Today by anomaly level'}</h3><button onclick="showPreviousAnomalyDays=!showPreviousAnomalyDays;loadDashboard()">${showPreviousAnomalyDays?'Show today only':'Load previous days'}</button></div><table class="overview-table anomaly-days"><thead><tr><th>Day</th><th>sigma &lt; -3</th><th>sigma &lt; -5</th><th>sigma &lt; -7</th></tr></thead><tbody>${sigmaDayRows(days)}</tbody></table></div>`}
function renderWeeklyReview(w){const box=document.getElementById('weeklyReview');if(!box)return;const rows=(w&&w.rows)||[];const body=rows.length?rows.map(row=>`<tr onclick="openWeeklyOverview('${esc(row.start_day)}','latest')"><td><span class="week-label">${esc(row.label||'')}</span><span class="week-range">${esc(row.date_range||'')}</span></td><td>${Number(row.total||0).toLocaleString('de-DE')}</td><td>${Number(row.ztf||0).toLocaleString('de-DE')}</td><td>${Number(row.lsst||0).toLocaleString('de-DE')}</td><td class="clickable" onclick="event.stopPropagation();openWeeklyOverview('${esc(row.start_day)}','review')">${Number(row.sigma_3||0).toLocaleString('de-DE')}</td><td class="clickable" onclick="event.stopPropagation();openWeeklyOverview('${esc(row.start_day)}','interesting')">${Number(row.sigma_5||0).toLocaleString('de-DE')}</td><td class="clickable" onclick="event.stopPropagation();openWeeklyOverview('${esc(row.start_day)}','urgent')">${Number(row.sigma_7||0).toLocaleString('de-DE')}</td></tr>`).join(''):'<tr><td colspan="7" class="muted">No weekly alert data available.</td></tr>';box.innerHTML=`<div class="overview-block"><h2>Weekly overview</h2><table class="weekly-table"><thead><tr><th>Week</th><th>Total alerts</th><th>ZTF</th><th>LSST</th><th>sigma &lt; -3</th><th>sigma &lt; -5</th><th>sigma &lt; -7</th></tr></thead><tbody>${body}</tbody></table></div>`}
function renderDailyChart(items){const chart=document.getElementById('chart'),xAxis=document.getElementById('xAxis'),yAxis=document.getElementById('yAxis');const max=Math.max(1,...items.map(x=>Number(x.total)||0)),mid=Math.round(max/2);if(!document.querySelector('.chart-legend'))document.getElementById('chartGrid').insertAdjacentHTML('beforebegin','<div class="chart-legend"><span class="ztf">ZTF</span><span class="lsst">LSST</span><span class="other">Other</span></div>');yAxis.innerHTML=`<span class="y-title">Anzahl</span><div class="y-ticks"><span>${max}</span><span>${mid}</span><span>0</span></div>`;chart.innerHTML=items.map(x=>{const total=Number(x.total)||0,ztf=Math.max(0,Number(x.ztf)||0),lsst=Math.max(0,Number(x.lsst)||0),other=Math.max(0,total-ztf-lsst),title=`${x.day}: total ${total} | ZTF ${ztf} | LSST ${lsst} | other ${other}`;const segment=(kind,value)=>value?`<div class="bar-segment ${kind}" style="height:${Math.max(.5,value/max*100)}%"></div>`:'';return `<div class="bar-group" title="${title}">${segment('ztf',ztf)}${segment('lsst',lsst)}${segment('other',other)}</div>`}).join('');const step=Math.max(1,Math.ceil(items.length/8));xAxis.innerHTML=items.map((x,i)=>`<div class="x-tick" title="${x.day}">${i%step===0||i===items.length-1?shortDay(x.day):''}</div>`).join('')}
async function loadDashboard(){if(dashboardLoading)return;dashboardLoading=true;const connection=document.getElementById('connection');if(connection&&!hasDashboardData)connection.textContent='Loading live server data...';try{const d=await api('/api/dashboard',{allDays:document.getElementById('allDays').checked,weekStart:selectedWeeklyStart});const s=d.stats;document.getElementById('total').textContent=Number(s.total_processed||0).toLocaleString('de-DE');document.getElementById('service').textContent='Collector: '+d.service;document.getElementById('sigma3').textContent=Number(s.sigma_3_alerts||0).toLocaleString('de-DE');document.getElementById('sigma5').textContent=Number(s.sigma_5_alerts||0).toLocaleString('de-DE');document.getElementById('sigma7').textContent=Number(s.sigma_7_alerts||0).toLocaleString('de-DE');document.getElementById('inbox').textContent=Number(s.recent_alerts||0).toLocaleString('de-DE');document.getElementById('inboxSub').innerHTML=`<table class="card-breakdown"><tr><td>ZTF today</td><td>${Number(s.ztf_today||0).toLocaleString('de-DE')}</td></tr><tr><td>LSST today total</td><td>${Number(s.lsst_today_all||0).toLocaleString('de-DE')}</td></tr><tr><td>LSST matched</td><td>${Number(s.lsst_today_matched||0).toLocaleString('de-DE')}</td></tr><tr><td>LSST unmatched</td><td>${Number(s.lsst_today_unmatched||0).toLocaleString('de-DE')}</td></tr></table>`;document.getElementById('latest').textContent=berlin(s.latest_received_utc)||'-';document.getElementById('latestSub').textContent='Europe/Berlin';hasDashboardData=true;document.getElementById('connection').textContent='Showing live server data; refreshed '+new Date().toLocaleTimeString('de-DE');renderWeeklyReview(d.weekly_review);renderDailyChart(d.chart)}catch(error){if(connection&&!hasDashboardData)connection.textContent='Connection problem: '+error.message;else if(connection)connection.textContent='Showing last loaded data; refresh failed at '+new Date().toLocaleTimeString('de-DE')}finally{dashboardLoading=false}}
function openWeeklyOverview(weekStart,show){showPage('live');document.getElementById('showFilter').value=show||'latest';document.getElementById('weekFilter').value=weekStart||'';document.getElementById('dayFilter').value='';document.getElementById('searchFilter').value='';loadAlerts()}
function openCategory(k){showPage('live');const map={latest:'latest',matched_lsst:'lsst_all',unmatched_lsst:'lsst_all',lsst_all:'lsst_all',lsst_today:'lsst_all',ztf_today:'ztf_all',review:'review',interesting:'interesting',urgent:'urgent'};document.getElementById('showFilter').value=map[k]||'latest';document.getElementById('weekFilter').value='';document.getElementById('dayFilter').value='';document.getElementById('searchFilter').value='';loadAlerts()}
function openDayCategory(k,day){showPage('live');const map={review:'review',interesting:'interesting',urgent:'urgent'};document.getElementById('showFilter').value=map[k]||'latest';document.getElementById('weekFilter').value='';document.getElementById('dayFilter').value=day||'';document.getElementById('searchFilter').value='';loadAlerts()}
function clearDateFilters(){document.getElementById('weekFilter').value='';document.getElementById('dayFilter').value='';loadAlerts()}
async function loadAlerts(){if(alertsLoading)return;alertsLoading=true;const status=document.getElementById('tableStatus');if(status)status.textContent='Loading alerts...';try{const day=document.getElementById('dayFilter').value,weekStart=document.getElementById('weekFilter').value,search=document.getElementById('searchFilter').value;const d=await api('/api/alerts',{limit:document.getElementById('limit').value,show:document.getElementById('showFilter').value,day,weekStart,search});rows=d.rows;activeTable=d.table;render('alerts',visible,rows,(row,tr)=>selectAlert(row,tr));document.getElementById('tableStatus').textContent=`${rows.length} rows${weekStart&&!day?' | week: '+weekStart:''}${day?' | day: '+day:''}${search?' | search: '+search:''} | newest: ${rows[0]?berlin(rows[0].received_utc):'none'}`}catch(error){if(status)status.textContent='Could not load alerts: '+error.message}finally{alertsLoading=false}}
async function selectAlert(row,tr){document.querySelectorAll('#alerts tr').forEach(x=>x.classList.remove('selected'));tr.classList.add('selected');selected=row;document.getElementById('analysisSso').value=row.sso_id||row.mpc_designation||'';document.getElementById('analysis').textContent='Loading alert details...';figures=[];plotFigures=[];cutoutItems=[];cutoutMeta={available:0,limit:12,hasMore:false};cutoutKind='Difference';figureMode='plots';cutoutIndex=0;document.getElementById('figureSelect').innerHTML='';updateFigureControls();document.getElementById('figure').removeAttribute('src');document.getElementById('figure').style.display='none';document.getElementById('figurePlaceholder').style.display='block';renderCandidateSummary();showPage('details');try{const d=await api('/api/alert-detail',{table:activeTable,id:row.id});selected=d.row||row;document.getElementById('detail').textContent=JSON.stringify(selected,null,2)}catch(error){document.getElementById('detail').textContent=JSON.stringify(row,null,2)+'\n\nAlert details could not be loaded: '+error.message}runAnalysis()}
function useSelected(){if(selected)document.getElementById('analysisSso').value=selected.sso_id||selected.mpc_designation||''}
async function runAnalysis(){const s=document.getElementById('analysisSso').value.trim();if(!s){document.getElementById('analysis').textContent='Select an alert or enter an SSO ID first.';return}figures=[];plotFigures=[];cutoutItems=[];cutoutMeta={available:0,limit:12,hasMore:false};cutoutKind='Difference';figureMode='plots';cutoutIndex=0;document.getElementById('figureSelect').innerHTML='';updateFigureControls();document.getElementById('figure').removeAttribute('src');document.getElementById('figure').style.display='none';document.getElementById('figurePlaceholder').style.display='block';document.getElementById('figurePlaceholder').textContent='Candidate analysis is running...';document.getElementById('analysis').textContent='Starting candidate analysis...';renderCandidateSummary('running');const payload={sso:s};if(selected)payload.alert={...selected,_source_table:activeTable};try{const d=await api('/api/analyze/start',payload);const timer=setInterval(async()=>{try{const q=await api('/api/analyze/status',{jobId:d.jobId});document.getElementById('analysis').textContent=q.message||'';if(q.status==='complete'){clearInterval(timer);document.getElementById('analysis').textContent=q.result.summary;figures=q.result.figures||[];cutoutItems=q.result.cutouts||[];cutoutMeta=q.result.cutoutMeta||{available:0,limit:12,hasMore:false};splitFigures();figureMode=cutoutItems.length?'cutouts':'plots';cutoutKind='Difference';cutoutIndex=0;renderCandidateSummary(q.result.summary||'');if(figureMode==='cutouts')showCutoutMode();else showPlotMode()}if(q.status==='error'){clearInterval(timer);document.getElementById('analysis').textContent=q.error||'Analysis failed.';document.getElementById('figurePlaceholder').textContent='No figures available.'}}catch(error){clearInterval(timer);document.getElementById('analysis').textContent='Analysis status could not be loaded: '+error.message;document.getElementById('figurePlaceholder').textContent='No figures available.'}},2500)}catch(error){document.getElementById('analysis').textContent='Could not start candidate analysis: '+error.message;document.getElementById('figurePlaceholder').textContent='No figures available.'}}
function showFigure(){const fig=figureMode==='cutouts'?activeCutouts()[cutoutIndex]:plotFigures[+document.getElementById('figureSelect').value||0];updateFigureControls();const img=document.getElementById('figure'),placeholder=document.getElementById('figurePlaceholder'),stage=document.querySelector('.figure-stage');if(stage){stage.scrollTop=0;stage.scrollLeft=0}if(fig&&fig.url){img.src=fig.url;img.style.display='block';placeholder.style.display='none'}else{img.removeAttribute('src');img.style.display='none';placeholder.style.display='block';placeholder.textContent=figureMode==='cutouts'?'No cutouts available.':'No plot available.'}}async function loadNotifications(){const d=await api('/api/notifications');render('notificationsTable',['id','created_utc','severity','primary_category','activity_score','sso_id','object_id','message','reviewed'],d.rows)}async function markReviewed(){await api('/api/notifications/review');loadNotifications();loadDashboard()}async function loadCalibration(){const d=await api('/api/calibration');render('calibrationTable',['key','count','interesting_count','best_score','last_seen_utc'],d.rows)}
let skyRows=[];
function initSky(){const old=document.getElementById('sky');if(!old)return;old.outerHTML='<div><div class="toolbar"><label>View <select id="skyMode" onchange="drawSky()"><option value="pointings">pointings</option><option value="heatmap">heatmap</option></select></label><label><input id="skySelected" type="checkbox" onchange="drawSky()"> Selected alert</label></div><canvas id="skyCanvas" class="sky-canvas"></canvas><div id="skyStatus" class="sky-status">Sky coverage not loaded yet.</div></div>';window.addEventListener('resize',drawSky)}
function skyPoint(ra,dec){ra=Number(ra);dec=Number(dec);if(!Number.isFinite(ra)||!Number.isFinite(dec)||dec<-90||dec>90)return null;const lon=-(((ra+180)%360)-180)*Math.PI/180,lat=dec*Math.PI/180,den=Math.sqrt(1+Math.cos(lat)*Math.cos(lon/2));if(!den)return null;return{x:2*Math.SQRT2*Math.cos(lat)*Math.sin(lon/2)/den,y:Math.SQRT2*Math.sin(lat)/den,ra,dec}}
function drawSky(){const canvas=document.getElementById('skyCanvas'),status=document.getElementById('skyStatus');if(!canvas||!status)return;const rect=canvas.getBoundingClientRect(),scale=window.devicePixelRatio||1,w=Math.max(1,Math.round(rect.width*scale)),h=Math.max(1,Math.round(rect.height*scale));if(canvas.width!==w||canvas.height!==h){canvas.width=w;canvas.height=h}const ctx=canvas.getContext('2d'),cx=w/2,cy=h/2,rx=w*.47,ry=h*.42,toCanvas=p=>({x:cx+p.x/(2*Math.SQRT2)*rx,y:cy-p.y/Math.SQRT2*ry});ctx.clearRect(0,0,w,h);ctx.fillStyle='#0b1728';ctx.fillRect(0,0,w,h);ctx.save();ctx.beginPath();ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2);ctx.clip();ctx.strokeStyle='#38506d';ctx.lineWidth=scale;for(let dec=-60;dec<=60;dec+=30){const y=toCanvas(skyPoint(0,dec)).y;ctx.beginPath();ctx.moveTo(cx-rx,y);ctx.lineTo(cx+rx,y);ctx.stroke()}for(let ra=0;ra<360;ra+=30){ctx.beginPath();for(let dec=-89;dec<=89;dec+=2){const p=toCanvas(skyPoint(ra,dec));if(dec===-89)ctx.moveTo(p.x,p.y);else ctx.lineTo(p.x,p.y)}ctx.stroke()}const points=skyRows.map(r=>({...r,p:skyPoint(r.ra,r.dec)})).filter(r=>r.p);if(!points.length){ctx.restore();ctx.strokeStyle='#718096';ctx.beginPath();ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2);ctx.stroke();status.textContent='Sky coverage: no RA/Dec rows for this range.';return}const mode=document.getElementById('skyMode').value,newest=Math.max(...points.map(r=>Date.parse(r.received_utc)||0));if(mode==='heatmap'){const bins=new Map(),size=Math.max(12,Math.round(w/55));for(const r of points){const q=toCanvas(r.p),key=`${Math.floor(q.x/size)},${Math.floor(q.y/size)}`;bins.set(key,(bins.get(key)||0)+1)}const max=Math.max(...bins.values());for(const [key,count] of bins){const [ix,iy]=key.split(',').map(Number),alpha=.16+.74*count/max;ctx.fillStyle=`rgba(34,197,94,${alpha})`;ctx.fillRect(ix*size,iy*size,size-1,size-1)}}for(const r of points){const q=toCanvas(r.p),survey=String(r.survey||r.observer||'').toLowerCase(),age=Math.max(0,(newest-(Date.parse(r.received_utc)||newest))/86400000),alpha=Math.max(.18,.88-Math.min(.65,age/30*.65));ctx.fillStyle=survey.includes('ztf')?`rgba(96,165,250,${mode==='heatmap'?'.25':alpha})`:survey.includes('lsst')?`rgba(251,146,60,${mode==='heatmap'?'.25':alpha})`:`rgba(148,163,184,${mode==='heatmap'?'.22':alpha})`;ctx.beginPath();ctx.arc(q.x,q.y,mode==='heatmap'?1.5*scale:2.4*scale,0,Math.PI*2);ctx.fill()}if(document.getElementById('skySelected').checked&&selected){const p=skyPoint(selected.ra,selected.dec);if(p){const q=toCanvas(p);ctx.fillStyle='#ef4444';ctx.font=`${18*scale}px sans-serif`;ctx.fillText('★',q.x-8*scale,q.y+6*scale)}}ctx.restore();ctx.strokeStyle='#718096';ctx.lineWidth=scale;ctx.beginPath();ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2);ctx.stroke();const ztf=points.filter(r=>String(r.survey||'').toLowerCase().includes('ztf')).length,lsst=points.filter(r=>String(r.survey||'').toLowerCase().includes('lsst')).length;status.textContent=`Sky coverage: ${points.length.toLocaleString('de-DE')} stored centers | ZTF ${ztf.toLocaleString('de-DE')} | LSST ${lsst.toLocaleString('de-DE')} | ${document.getElementById('skyRange').value}`}
async function loadSky(){const status=document.getElementById('skyStatus');if(status)status.textContent='Loading sky coverage...';const d=await api('/api/sky',{range:document.getElementById('skyRange').value});skyRows=d.rows||[];drawSky();if(d.note)document.getElementById('skyStatus').textContent+=' | '+d.note}
function buildConfig(){const th=document.getElementById('thresholdForm'),fi=document.getElementById('filterForm');th.innerHTML='';fi.innerHTML='';Object.entries(config.thresholds||{}).forEach(([k,v])=>th.insertAdjacentHTML('beforeend',`<label>${k}</label><input data-th="${k}" value="${v}">`));Object.entries(FILTER_DEFAULTS).forEach(([k,v])=>fi.insertAdjacentHTML('beforeend',`<label><input type="checkbox" data-fi="${k}" ${(config.active_filters||{})[k]??v?'checked':''}> ${k}</label>`));document.getElementById('filterInfo').textContent='Server scoring logic\n'+'='.repeat(60)+'\n\n'+JSON.stringify(config,null,2)}async function loadConfig(){config=(await api('/api/config')).config;buildConfig()}function resetConfig(){config={thresholds:{},active_filters:{...FILTER_DEFAULTS}};buildConfig()}function enableAllFilters(){document.querySelectorAll('[data-fi]').forEach(x=>x.checked=true)}async function saveConfig(){document.querySelectorAll('[data-th]').forEach(x=>config.thresholds[x.dataset.th]=Number(x.value));document.querySelectorAll('[data-fi]').forEach(x=>config.active_filters[x.dataset.fi]=x.checked);const d=await api('/api/config/save',config);document.getElementById('configStatus').textContent=d.message;loadDashboard()}
function buildColumns(){const b=document.getElementById('columnForm');b.innerHTML=COLUMNS.map(c=>`<label><input type="checkbox" value="${c}" ${visible.includes(c)?'checked':''} onchange="visible=[...document.querySelectorAll('#columnForm input:checked')].map(x=>x.value)"> ${c}</label>`).join('')}function setColumns(c){visible=[...c];buildColumns();loadAlerts()}
async function refreshAll(){await loadDashboard();if(document.getElementById('live').classList.contains('active'))await loadAlerts()}function resetLiveFilters(){document.getElementById('showFilter').value='latest';document.getElementById('weekFilter').value='';document.getElementById('dayFilter').value='';document.getElementById('searchFilter').value='';document.getElementById('limit').value='200';loadAlerts()}setInterval(()=>{if(document.getElementById('livePoll').checked&&document.getElementById('live').classList.contains('active'))loadAlerts();if(document.getElementById('start').classList.contains('active'))loadDashboard()},30000);refreshAll();
</script></body></html>'''


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        print("[dashboard]", fmt % args, flush=True)

    def send_json(self, payload, status=200):
        data = json.dumps(payload, default=json_safe).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def read_json(self):
        length = int(self.headers.get("Content-Length", "0") or "0")
        return json.loads(self.rfile.read(length).decode("utf-8")) if length else {}

    def do_GET(self):
        if urlparse(self.path).path not in {"/", "/index.html"}:
            return self.send_json({"ok": False, "error": "Not found"}, 404)
        with STATE_LOCK:
            collector_db = STATE["db_path"]
        html = (
            INDEX_HTML
            .replace("%%COLUMNS%%", json.dumps(COLUMNS))
            .replace("%%MINIMAL_COLUMNS%%", json.dumps(MINIMAL_COLUMNS))
            .replace("%%FILTER_DEFAULTS%%", json.dumps(FILTER_DEFAULTS))
            .replace(
                "%%SERVER_INFO%%",
                f"Database: {collector_db}",
            )
            .encode("utf-8")
        )
        self.send_response(200); self.send_header("Content-Type", "text/html; charset=utf-8"); self.send_header("Cache-Control", "no-store"); self.send_header("Content-Length", str(len(html))); self.end_headers(); self.wfile.write(html)

    def do_POST(self):
        try:
            path, payload = urlparse(self.path).path, self.read_json()
            if path == "/api/dashboard": return self.send_json(dashboard_payload(bool(payload.get("allDays")), payload.get("weekStart")))
            if path == "/api/weekly/status": return self.send_json(write_weekly_status(payload))
            if path == "/api/alerts": return self.send_json(alert_rows(payload))
            if path == "/api/alert-detail": return self.send_json(alert_detail(payload))
            if path == "/api/mpc/retry": return self.send_json(retry_mpc_match(payload))
            if path == "/api/notifications": return self.send_json(notifications())
            if path == "/api/notifications/review": db_write("UPDATE notifications SET reviewed=1 WHERE reviewed=0"); return self.send_json({"ok": True})
            if path == "/api/calibration": return self.send_json(calibration())
            if path == "/api/config": return self.send_json({"ok": True, "config": read_config()})
            if path == "/api/config/save": return self.send_json(write_config(payload))
            if path == "/api/sky": return self.send_json(sky_rows(payload))
            if path == "/api/cutouts": return self.send_json(cutout_gallery_payload(payload))
            if path == "/api/analyze/start": return self.send_json(start_analysis(str(payload.get("sso") or "").strip(), [payload.get("alert")] if isinstance(payload.get("alert"), dict) else None))
            if path == "/api/analyze/status":
                with STATE_LOCK: job = STATE["jobs"].get(str(payload.get("jobId")))
                return self.send_json({"ok": bool(job), **(job or {"error": "Unknown job."})}, 200 if job else 404)
            return self.send_json({"ok": False, "error": "Not found"}, 404)
        except Exception as exc:
            traceback.print_exc()
            return self.send_json({"ok": False, "error": str(exc)}, 500)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--collector-db", default=os.environ.get("ASTROPRAK_COLLECTOR_DB", DEFAULT_DB_PATH))
    parser.add_argument("--scoring-config", default=os.environ.get("ASTROPRAK_SCORING_CONFIG", DEFAULT_CONFIG_PATH))
    parser.add_argument("--weekly-status", default=os.environ.get("ASTROPRAK_WEEKLY_STATUS_PATH", DEFAULT_WEEKLY_STATUS_PATH))
    parser.add_argument("--collector-service", default=os.environ.get("ASTROPRAK_COLLECTOR_SERVICE", DEFAULT_SERVICE_NAME))
    parser.add_argument("--data-dir", default=None, help=argparse.SUPPRESS)
    parser.add_argument("--db", default=None, help=argparse.SUPPRESS)
    args = parser.parse_args()
    ensure_database_schema(args.collector_db)
    with STATE_LOCK:
        STATE.update({"db_path": args.collector_db, "config_path": args.scoring_config, "weekly_status_path": args.weekly_status, "service": args.collector_service})
    server = ThreadingHTTPServer((args.host, args.port), Handler)
    print(f"Serving AstroPrak Server Dashboard on http://{args.host}:{args.port}", flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()






