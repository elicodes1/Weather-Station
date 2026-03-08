from flask import Flask, request, jsonify, Response
import sqlite3
from datetime import datetime, timedelta
import io
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

DB_PATH = "weather.db"

app = Flask(__name__)


def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    conn = db()
    conn.execute("""
    CREATE TABLE IF NOT EXISTS readings (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        station_id TEXT NOT NULL,
        ts TEXT NOT NULL,
        air_temp_c REAL NOT NULL DEFAULT 0,
        humidity_pct REAL NOT NULL DEFAULT 0,
        soil_moisture_pct REAL NOT NULL DEFAULT 0,
        soil_moisture_1_pct REAL NOT NULL DEFAULT 0,
        soil_moisture_2_pct REAL NOT NULL DEFAULT 0,
        soil_raw_1 REAL NOT NULL DEFAULT 0,
        soil_raw_2 REAL NOT NULL DEFAULT 0,
        eco2_ppm REAL NOT NULL DEFAULT 0
    )
    """)
    conn.commit()

    existing = {row["name"] for row in conn.execute("PRAGMA table_info(readings)").fetchall()}
    needed = {
        "soil_moisture_1_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_2_pct": "REAL NOT NULL DEFAULT 0",
        "soil_raw_1": "REAL NOT NULL DEFAULT 0",
        "soil_raw_2": "REAL NOT NULL DEFAULT 0",
    }

    for col, coltype in needed.items():
        if col not in existing:
            conn.execute(f"ALTER TABLE readings ADD COLUMN {col} {coltype}")

    conn.commit()
    conn.close()


def safe_num(v):
    try:
        if v is None:
            return 0.0
        return float(v)
    except Exception:
        return 0.0


@app.route("/ingest", methods=["POST"])
def ingest():
    payload = request.get_json(force=True, silent=True) or {}
    station_id = str(payload.get("station_id", "unknown"))
    ts = datetime.utcnow().isoformat()

    air_temp_c = safe_num(payload.get("air_temp_c", 0))
    humidity_pct = safe_num(payload.get("humidity_pct", 0))
    eco2_ppm = safe_num(payload.get("eco2_ppm", 0))

    soil_moisture_pct = safe_num(payload.get("soil_moisture_pct", 0))
    soil_moisture_1_pct = safe_num(payload.get("soil_moisture_1_pct", 0))
    soil_moisture_2_pct = safe_num(payload.get("soil_moisture_2_pct", 0))
    soil_raw_1 = safe_num(payload.get("soil_raw_1", 0))
    soil_raw_2 = safe_num(payload.get("soil_raw_2", 0))

    if soil_moisture_pct == 0 and (soil_moisture_1_pct or soil_moisture_2_pct):
        soil_moisture_pct = (soil_moisture_1_pct + soil_moisture_2_pct) / 2.0

    conn = db()
    conn.execute("""
        INSERT INTO readings (
            station_id, ts, air_temp_c, humidity_pct,
            soil_moisture_pct, soil_moisture_1_pct, soil_moisture_2_pct,
            soil_raw_1, soil_raw_2, eco2_ppm
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        station_id, ts, air_temp_c, humidity_pct,
        soil_moisture_pct, soil_moisture_1_pct, soil_moisture_2_pct,
        soil_raw_1, soil_raw_2, eco2_ppm
    ))
    conn.commit()
    conn.close()

    return jsonify({"ok": True})


@app.route("/api/latest")
def latest():
    conn = db()
    rows = conn.execute("""
        SELECT r1.*
        FROM readings r1
        JOIN (
            SELECT station_id, MAX(ts) AS max_ts
            FROM readings
            GROUP BY station_id
        ) r2
        ON r1.station_id = r2.station_id AND r1.ts = r2.max_ts
        ORDER BY r1.station_id
    """).fetchall()
    conn.close()
    return jsonify([dict(r) for r in rows])


@app.route("/plot/<station_id>.svg")
def plot_station(station_id):
    hours = request.args.get("hours", default=168, type=int)
    since = (datetime.utcnow() - timedelta(hours=hours)).isoformat()

    conn = db()
    rows = conn.execute("""
        SELECT ts, air_temp_c, humidity_pct, soil_moisture_pct,
               soil_moisture_1_pct, soil_moisture_2_pct, eco2_ppm
        FROM readings
        WHERE station_id = ? AND ts >= ?
        ORDER BY ts ASC
    """, (station_id, since)).fetchall()
    conn.close()

    times = [r["ts"] for r in rows]
    soil_avg = [r["soil_moisture_pct"] for r in rows]
    soil1 = [r["soil_moisture_1_pct"] for r in rows]
    soil2 = [r["soil_moisture_2_pct"] for r in rows]

    fig, ax = plt.subplots(figsize=(10, 4))
    ax.plot(times, soil_avg, label="Soil avg %")
    ax.plot(times, soil1, label="Probe 1 %")
    ax.plot(times, soil2, label="Probe 2 %")
    ax.set_title(f"Station {station_id} - last {hours}h")
    ax.set_xlabel("Timestamp")
    ax.set_ylabel("Soil moisture %")
    ax.set_ylim(0, 100)
    ax.legend()
    ax.grid(True)
    fig.autofmt_xdate()

    buf = io.StringIO()
    fig.savefig(buf, format="svg", bbox_inches="tight")
    plt.close(fig)
    return Response(buf.getvalue(), mimetype="image/svg+xml")


@app.route("/")
def home():
    return """
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <title>Weather Station Host</title>
  <meta http-equiv="refresh" content="60">
  <style>
    body {
      font-family: Arial, sans-serif;
      margin: 24px;
      background: #f6f7f9;
    }
    .card {
      background: white;
      padding: 16px;
      margin-bottom: 16px;
      border-radius: 12px;
      box-shadow: 0 1px 6px rgba(0,0,0,0.08);
    }
    .row {
      display: flex;
      gap: 16px;
      flex-wrap: wrap;
    }
    .mini {
      min-width: 220px;
      background: #fafafa;
      border-radius: 10px;
      padding: 10px;
      border: 1px solid #e5e7eb;
    }
    .ok {
      background: #e8f5e9;
      border-color: #81c784;
    }
    .warn {
      background: #fff8e1;
      border-color: #ffb74d;
    }
    .bad {
      background: #ffebee;
      border-color: #e57373;
    }
    img {
      max-width: 100%;
      border-radius: 8px;
      background: white;
    }
  </style>
</head>
<body>
  <h1>Weather Station Host</h1>
  <div id="content">Loading...</div>

  <script>
    function moistureClass(v) {
      v = Number(v);
      if (v < 20) return "bad";
      if (v < 35) return "warn";
      if (v > 85) return "warn";
      return "ok";
    }

    async function load() {
      const res = await fetch('/api/latest');
      const data = await res.json();

      let html = '';
      for (const s of data) {
        html += `
          <div class="card">
            <h2>Station ${s.station_id}</h2>
            <div class="row">
              <div class="mini"><strong>Timestamp:</strong><br>${s.ts}</div>
              <div class="mini ${moistureClass(s.soil_moisture_1_pct)}">
                <strong>Probe 1:</strong><br>${Number(s.soil_moisture_1_pct).toFixed(1)} %
              </div>
              <div class="mini ${moistureClass(s.soil_moisture_2_pct)}">
                <strong>Probe 2:</strong><br>${Number(s.soil_moisture_2_pct).toFixed(1)} %
              </div>
              <div class="mini ${moistureClass(s.soil_moisture_pct)}">
                <strong>Average:</strong><br>${Number(s.soil_moisture_pct).toFixed(1)} %
              </div>
              <div class="mini">
                <strong>Raw 1:</strong><br>${Number(s.soil_raw_1).toFixed(0)}
              </div>
              <div class="mini">
                <strong>Raw 2:</strong><br>${Number(s.soil_raw_2).toFixed(0)}
              </div>
            </div>
            <div style="margin-top: 16px;">
              <img src="/plot/${encodeURIComponent(s.station_id)}.svg?hours=168">
            </div>
          </div>
        `;
      }

      if (!data.length) {
        html = '<div class="card">No data received yet.</div>';
      }
      document.getElementById('content').innerHTML = html;
    }

    load();
    setInterval(load, 60000);
  </script>
</body>
</html>
"""


if __name__ == "__main__":
    init_db()
    app.run(host="0.0.0.0", port=5000)
