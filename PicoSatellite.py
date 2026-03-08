from flask import Flask, request, jsonify, Response
import sqlite3
from datetime import datetime, timedelta, timezone
import io
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

DB_PATH = "weather.db"

app = Flask(__name__)

# Change these to fit each station and plant setup
# For bog plants, you probably want much wetter targets than a normal bed.
STATION_RULES = {
    "default": {
        "label": "General zone",
        "danger_low": 20,
        "warn_low": 35,
        "target_low": 40,
        "target_high": 85,
        "warn_high": 95,
    },
    "soil_sat_1": {
        "label": "Bog zone",
        "danger_low": 55,
        "warn_low": 70,
        "target_low": 75,
        "target_high": 95,
        "warn_high": 99,
    },
}

DEFAULT_HOURS = 24
ALLOWED_WINDOWS = [1, 24, 168]


def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def utc_now_iso():
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_iso(ts):
    # Handles strings like 2026-03-08T02:30:20Z
    return datetime.fromisoformat(ts.replace("Z", "+00:00"))


def get_rules(station_id):
    return STATION_RULES.get(station_id, STATION_RULES["default"])


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

    existing = {row["name"] for row in conn.execute("PRAGMA table_info(readings)").fetchall()}
    needed = {
        "soil_moisture_1_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_2_pct": "REAL NOT NULL DEFAULT 0",
        "soil_raw_1": "REAL NOT NULL DEFAULT 0",
        "soil_raw_2": "REAL NOT NULL DEFAULT 0",
        "eco2_ppm": "REAL NOT NULL DEFAULT 0",
        "air_temp_c": "REAL NOT NULL DEFAULT 0",
        "humidity_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_pct": "REAL NOT NULL DEFAULT 0",
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
    ts = utc_now_iso()

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


@app.route("/api/stations")
def api_stations():
    hours = request.args.get("hours", default=DEFAULT_HOURS, type=int)
    if hours not in ALLOWED_WINDOWS:
        hours = DEFAULT_HOURS

    since = (datetime.now(timezone.utc) - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()

    latest_rows = conn.execute("""
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

    results = []
    for row in latest_rows:
        station_id = row["station_id"]

        stats = conn.execute("""
            SELECT
                COUNT(*) AS points,
                AVG(soil_moisture_pct) AS avg_station,
                AVG(soil_moisture_1_pct) AS avg_probe1,
                AVG(soil_moisture_2_pct) AS avg_probe2
            FROM readings
            WHERE station_id = ? AND ts >= ?
        """, (station_id, since)).fetchone()

        item = dict(row)
        item["window_hours"] = hours
        item["window_points"] = int(stats["points"] or 0)
        item["avg_station_window"] = safe_num(stats["avg_station"])
        item["avg_probe1_window"] = safe_num(stats["avg_probe1"])
        item["avg_probe2_window"] = safe_num(stats["avg_probe2"])
        item["rules"] = get_rules(station_id)
        results.append(item)

    conn.close()
    return jsonify(results)


@app.route("/plot/<station_id>.svg")
def plot_station(station_id):
    hours = request.args.get("hours", default=DEFAULT_HOURS, type=int)
    if hours not in ALLOWED_WINDOWS:
        hours = DEFAULT_HOURS

    since = (datetime.now(timezone.utc) - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()
    rows = conn.execute("""
        SELECT ts, soil_moisture_pct, soil_moisture_1_pct, soil_moisture_2_pct
        FROM readings
        WHERE station_id = ? AND ts >= ?
        ORDER BY ts ASC
    """, (station_id, since)).fetchall()
    conn.close()

    fig, ax = plt.subplots(figsize=(10, 3.8))

    if rows:
        times = [parse_iso(r["ts"]) for r in rows]
        soil_avg = [safe_num(r["soil_moisture_pct"]) for r in rows]
        soil1 = [safe_num(r["soil_moisture_1_pct"]) for r in rows]
        soil2 = [safe_num(r["soil_moisture_2_pct"]) for r in rows]

        ax.plot(times, soil_avg, label="Avg %", linewidth=2.3)
        ax.plot(times, soil1, label="Probe 1 %", linewidth=1.7)
        ax.plot(times, soil2, label="Probe 2 %", linewidth=1.7)

        rules = get_rules(station_id)
        ax.axhspan(rules["target_low"], rules["target_high"], alpha=0.08)
    else:
        ax.text(0.5, 0.5, "No data in selected window", ha="center", va="center", transform=ax.transAxes)

    ax.set_title(f"{station_id} · last {hours}h")
    ax.set_ylabel("Soil moisture %")
    ax.set_ylim(0, 100)
    ax.grid(True, alpha=0.35)
    ax.legend(loc="upper left")

    if hours <= 1:
        locator = mdates.MinuteLocator(interval=10)
    elif hours <= 24:
        locator = mdates.HourLocator(interval=2)
    else:
        locator = mdates.DayLocator(interval=1)

    ax.xaxis.set_major_locator(locator)
    ax.xaxis.set_major_formatter(mdates.ConciseDateFormatter(locator))
    fig.tight_layout()

    buf = io.StringIO()
    fig.savefig(buf, format="svg", bbox_inches="tight")
    plt.close(fig)
    return Response(buf.getvalue(), mimetype="image/svg+xml")


@app.route("/")
def home():
    html = """
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <title>Weather Station Host</title>
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <style>
    :root {
      --bg: #f4f6f8;
      --panel: #ffffff;
      --text: #17212b;
      --muted: #5b6573;
      --border: #d9e0e7;
      --shadow: 0 8px 24px rgba(19, 33, 48, 0.07);
      --ok-bg: #e9f8ee;
      --ok-border: #7bc693;
      --warn-bg: #fff6df;
      --warn-border: #e6b44a;
      --bad-bg: #fdecec;
      --bad-border: #de7878;
      --accent: #2f6fed;
    }

    * { box-sizing: border-box; }

    body {
      margin: 0;
      font-family: Arial, sans-serif;
      background: var(--bg);
      color: var(--text);
    }

    .wrap {
      max-width: 1180px;
      margin: 0 auto;
      padding: 20px;
    }

    .topbar {
      display: flex;
      justify-content: space-between;
      align-items: center;
      gap: 16px;
      flex-wrap: wrap;
      margin-bottom: 18px;
    }

    h1 {
      margin: 0;
      font-size: 2rem;
    }

    .toolbar {
      display: flex;
      gap: 10px;
      align-items: center;
      flex-wrap: wrap;
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 10px 12px;
      box-shadow: var(--shadow);
    }

    .toolbar label {
      font-weight: 700;
      color: var(--muted);
    }

    .toolbar select {
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 8px 10px;
      background: white;
      font-size: 0.95rem;
    }

    .hint {
      color: var(--muted);
      font-size: 0.92rem;
    }

    .station-card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 18px;
      margin-bottom: 18px;
      box-shadow: var(--shadow);
    }

    .station-head {
      display: flex;
      justify-content: space-between;
      align-items: start;
      gap: 12px;
      flex-wrap: wrap;
      margin-bottom: 16px;
    }

    .station-title {
      margin: 0;
      font-size: 1.35rem;
    }

    .station-sub {
      color: var(--muted);
      margin-top: 4px;
      font-size: 0.95rem;
    }

    .pill {
      display: inline-block;
      padding: 8px 12px;
      border-radius: 999px;
      font-weight: 700;
      border: 1px solid var(--border);
      background: #f7f9fb;
    }

    .pill.ok {
      background: var(--ok-bg);
      border-color: var(--ok-border);
    }

    .pill.warn {
      background: var(--warn-bg);
      border-color: var(--warn-border);
    }

    .pill.bad {
      background: var(--bad-bg);
      border-color: var(--bad-border);
    }

    .stats {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(170px, 1fr));
      gap: 12px;
      margin-bottom: 16px;
    }

    .stat {
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 12px;
      background: #fcfdff;
    }

    .stat.ok {
      background: var(--ok-bg);
      border-color: var(--ok-border);
    }

    .stat.warn {
      background: var(--warn-bg);
      border-color: var(--warn-border);
    }

    .stat.bad {
      background: var(--bad-bg);
      border-color: var(--bad-border);
    }

    .label {
      color: var(--muted);
      font-size: 0.85rem;
      margin-bottom: 6px;
      font-weight: 700;
      text-transform: uppercase;
      letter-spacing: 0.03em;
    }

    .value {
      font-size: 1.35rem;
      font-weight: 700;
    }

    .value.small {
      font-size: 1rem;
    }

    .meter-wrap {
      margin-top: 10px;
    }

    .meter {
      width: 100%;
      height: 10px;
      border-radius: 999px;
      background: #e9eef4;
      overflow: hidden;
      border: 1px solid #d8e0e9;
    }

    .meter > span {
      display: block;
      height: 100%;
      background: var(--accent);
    }

    .plot-box {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px;
      background: #fbfcfe;
    }

    .plot-box img {
      width: 100%;
      display: block;
      border-radius: 10px;
    }

    .empty {
      background: white;
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 24px;
      box-shadow: var(--shadow);
    }

    @media (max-width: 700px) {
      .wrap {
        padding: 14px;
      }

      h1 {
        font-size: 1.6rem;
      }

      .value {
        font-size: 1.15rem;
      }
    }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="topbar">
      <div>
        <h1>Weather Station Host</h1>
        <div class="hint">Auto-refreshes every 60 seconds</div>
      </div>

      <div class="toolbar">
        <label for="rangeSelect">Graph range</label>
        <select id="rangeSelect">
          <option value="1">Last 1 hour</option>
          <option value="24" selected>Last 24 hours</option>
          <option value="168">Last 7 days</option>
        </select>
      </div>
    </div>

    <div id="content" class="empty">Loading...</div>
  </div>

  <script>
    const STATION_RULES = __RULES_JSON__;
    const DEFAULT_HOURS = __DEFAULT_HOURS__;

    function stationRules(stationId) {
      return STATION_RULES[stationId] || STATION_RULES.default;
    }

    function moistureState(value, rules) {
      value = Number(value);

      if (value < rules.danger_low) {
        return { cls: "bad", text: "Too dry" };
      }
      if (value < rules.warn_low) {
        return { cls: "warn", text: "Dry side" };
      }
      if (value <= rules.target_high) {
        return { cls: "ok", text: "On target" };
      }
      if (value <= rules.warn_high) {
        return { cls: "warn", text: "Very wet" };
      }
      return { cls: "bad", text: "Extreme wet" };
    }

    function fmtPct(v) {
      return Number(v || 0).toFixed(1) + " %";
    }

    function fmtRaw(v) {
      return Number(v || 0).toFixed(0);
    }

    function fmtTimestamp(ts) {
      const d = new Date(ts);
      if (Number.isNaN(d.getTime())) return ts;
      return new Intl.DateTimeFormat(undefined, {
        dateStyle: "medium",
        timeStyle: "short"
      }).format(d);
    }

    function barWidth(v) {
      const n = Math.max(0, Math.min(100, Number(v || 0)));
      return n.toFixed(1) + "%";
    }

    async function load() {
      const hours = Number(document.getElementById("rangeSelect").value || DEFAULT_HOURS);
      const res = await fetch("/api/stations?hours=" + hours);
      const data = await res.json();

      if (!data.length) {
        document.getElementById("content").innerHTML =
          '<div class="empty">No data received yet.</div>';
        return;
      }

      let html = "";

      for (const s of data) {
        const rules = stationRules(s.station_id);
        const state = moistureState(s.soil_moisture_pct, rules);

        html += `
          <div class="station-card">
            <div class="station-head">
              <div>
                <h2 class="station-title">${s.station_id}</h2>
                <div class="station-sub">
                  ${rules.label} · target ${rules.target_low}%–${rules.target_high}% · updated ${fmtTimestamp(s.ts)}
                </div>
              </div>
              <div class="pill ${state.cls}">${state.text}</div>
            </div>

            <div class="stats">
              <div class="stat ${state.cls}">
                <div class="label">Current average</div>
                <div class="value">${fmtPct(s.soil_moisture_pct)}</div>
                <div class="meter-wrap">
                  <div class="meter"><span style="width:${barWidth(s.soil_moisture_pct)}"></span></div>
                </div>
              </div>

              <div class="stat ${moistureState(s.soil_moisture_1_pct, rules).cls}">
                <div class="label">Probe 1 now</div>
                <div class="value">${fmtPct(s.soil_moisture_1_pct)}</div>
              </div>

              <div class="stat ${moistureState(s.soil_moisture_2_pct, rules).cls}">
                <div class="label">Probe 2 now</div>
                <div class="value">${fmtPct(s.soil_moisture_2_pct)}</div>
              </div>

              <div class="stat">
                <div class="label">Probe 1 avg (${hours}h)</div>
                <div class="value">${fmtPct(s.avg_probe1_window)}</div>
              </div>

              <div class="stat">
                <div class="label">Probe 2 avg (${hours}h)</div>
                <div class="value">${fmtPct(s.avg_probe2_window)}</div>
              </div>

              <div class="stat">
                <div class="label">Overall avg (${hours}h)</div>
                <div class="value">${fmtPct(s.avg_station_window)}</div>
              </div>

              <div class="stat">
                <div class="label">Raw 1</div>
                <div class="value small">${fmtRaw(s.soil_raw_1)}</div>
              </div>

              <div class="stat">
                <div class="label">Raw 2</div>
                <div class="value small">${fmtRaw(s.soil_raw_2)}</div>
              </div>

              <div class="stat">
                <div class="label">Points in window</div>
                <div class="value small">${Number(s.window_points || 0)}</div>
              </div>
            </div>

            <div class="plot-box">
              <img src="/plot/${encodeURIComponent(s.station_id)}.svg?hours=${hours}&_=${Date.now()}" alt="Plot for ${s.station_id}">
            </div>
          </div>
        `;
      }

      document.getElementById("content").innerHTML = html;
    }

    document.getElementById("rangeSelect").addEventListener("change", load);
    load();
    setInterval(load, 60000);
  </script>
</body>
</html>
"""
    html = html.replace("__RULES_JSON__", json.dumps(STATION_RULES))
    html = html.replace("__DEFAULT_HOURS__", str(DEFAULT_HOURS))
    return Response(html, mimetype="text/html")


if __name__ == "__main__":
    init_db()
    app.run(host="0.0.0.0", port=5000, debug=False)
