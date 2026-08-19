# Deployment Notes

This repository contains only the source code needed to run the current AstroPrak server dashboard.
Runtime data and server credentials must stay outside GitHub.

## Handover Flow

1. Clone the repository on the university server.
2. Create a Python virtual environment.
3. Install `requirements.txt`.
4. Either put the existing SQLite alert database on the server or let the dashboard create an empty database on first start.
5. Start `astroprak_server_dashboard_web.py` on a local port.
6. Expose the local port through the university web server with HTTPS.
7. Test the university URL.
8. Cancel the old paid server only after the university version works.

## Server Requirements

- Python 3.12 or newer.
- Disk space for the SQLite alert database.
- Network access to Fink, MPC, JPL Horizons, and ZTF/IRSA endpoints.
- Write permission for the configured database directory, for example `/var/lib/astroprak`.
- A reverse proxy such as nginx or Apache.
- A process manager such as systemd, supervisor, or the university hosting platform's native service runner.

If no existing database is copied over, the website starts with empty tables. It will show zero alerts until a collector or import process writes new alert rows into the database.

## Example systemd Service

Adjust paths, user names, and ports to the university server.

```ini
[Unit]
Description=AstroPrak Alert Inspector
After=network.target

[Service]
Type=simple
User=astroprak
Group=astroprak
WorkingDirectory=/opt/astroprak/app
ExecStart=/opt/astroprak/app/.venv/bin/python /opt/astroprak/app/astroprak_server_dashboard_web.py --host 127.0.0.1 --port 8765 --collector-db /var/lib/astroprak/alerts.sqlite
Restart=on-failure
RestartSec=5

[Install]
WantedBy=multi-user.target
```

## Example nginx Reverse Proxy

Adjust the domain and port to the university setup.

```nginx
server {
    listen 443 ssl http2;
    server_name astroprak.example.uni.de;

    location / {
        proxy_pass http://127.0.0.1:8765;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

## Questions for the University Side

- Which final public URL should be used?
- Can the university server run a persistent Python process?
- Is the dashboard public or restricted to the university network?
- Where should the SQLite database live?
- Who maintains the service after handover?
