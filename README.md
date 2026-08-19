# AstroPrak Alert Inspector

Web dashboard for inspecting unusual Solar System Object alerts from a live SQLite alert database.

## Runtime Files

The current public website needs only these project files:

- `astroprak_server_dashboard_web.py`
- `fink_sso_combined_gui.py`
- `requirements.txt`
- `.env.example`

`README.md` and `DEPLOYMENT.md` are documentation for handover and deployment.

## Data Files

The SQLite database and alert data are runtime data. They are not stored in GitHub.
If the configured SQLite database does not exist yet, the dashboard creates an empty one on startup.
The page will then load normally with zero rows until a collector or import process writes alerts into it.

Typical server paths:

- `/var/lib/astroprak/alerts.sqlite`
- `/opt/astroprak/scoring_config.json`
- `/opt/astroprak/weekly_review_status.json`

## Setup

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
```

## Run

```bash
python astroprak_server_dashboard_web.py --host 127.0.0.1 --port 8765 --collector-db /var/lib/astroprak/alerts.sqlite
```

For public hosting, run this Python service behind the university web server or reverse proxy.
