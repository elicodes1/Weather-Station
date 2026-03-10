from flask import Flask, request, jsonify, Response
import sqlite3
from datetime import datetime, timedelta, timezone
import io
import json
import math
import time
from statistics import median

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

try:
    import board
    import busio
    import adafruit_ads1x15.ads1115 as ADS
    from adafruit_ads1x15.analog_in import AnalogIn
except Exception as exc:
    board = None
    busio = None
    ADS = None
    AnalogIn = None
    ADS_IMPORT_ERROR = str(exc)
else:
    ADS_IMPORT_ERROR = None


DB_PATH = "weather.db"
app = Flask(__name__)

DEFAULT_HOURS = 24
ALLOWED_WINDOWS = [1, 24, 168]
ONLINE_AFTER_MINUTES = 5
STALE_AFTER_MINUTES = 30

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

PROBES = [
    {"key": "soil_moisture_1_pct", "raw_key": "soil_raw_1", "default_name": "Probe 1"},
    {"key": "soil_moisture_2_pct", "raw_key": "soil_raw_2", "default_name": "Probe 2"},
]
PROBE_INDEX = {p["key"]: p for p in PROBES}

# ----------------------------
# pH / ADS1115 settings
# ----------------------------
PH_ENABLED = True
PH_NAME = "Bench pH Probe"
PH_DESCRIPTION = "Atlas Surveyor live read directly on Raspberry Pi"
PH_CHANNEL_INDEX = 0          # ADS1115 A0
PH_ADC_GAIN = 1               # +/- 4.096 V range
PH_SAMPLES = 9
PH_SAMPLE_DELAY = 0.03
PH_LOG_EVERY_SECONDS = 15
PH_DEFAULT_HOURS = 1

# Atlas Surveyor transfer function:
# pH = (-5.6548 * voltage) + 15.509
PH_VOLTS_MIN = 0.265
PH_VOLTS_MAX = 3.000
PH_SLOPE = -5.6548
PH_INTERCEPT = 15.509

# Optional trim after checking with buffers
PH_CAL_SCALE = 1.0
PH_CAL_OFFSET = 0.0

_ph_ads = None
_ph_chan = None
_ph_error = ADS_IMPORT_ERROR
_ph_last_logged = None


def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def utc_now():
    return datetime.now(timezone.utc)


def utc_now_iso():
    return utc_now().replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_iso(ts):
    return datetime.fromisoformat(str(ts).replace("Z", "+00:00"))


def safe_num(v, default=0.0):
    try:
        if v is None or v == "":
            return float(default)
        return float(v)
    except Exception:
        return float(default)


def get_base_rules(station_id):
    return STATION_RULES.get(station_id, STATION_RULES["default"]).copy()


def clamp_hours(v):
    v = int(v or DEFAULT_HOURS)
    return v if v in ALLOWED_WINDOWS else DEFAULT_HOURS


def clamp_percent(v, fallback):
    try:
        num = float(v)
    except Exception:
        return float(fallback)
    return max(0.0, min(100.0, num))


def age_text(ts):
    delta = utc_now() - parse_iso(ts)
    seconds = max(0, int(delta.total_seconds()))
    if seconds < 60:
        return f"{seconds}s ago"
    minutes = seconds // 60
    if minutes < 60:
        return f"{minutes}m ago"
    hours = minutes // 60
    if hours < 48:
        return f"{hours}h ago"
    days = hours // 24
    return f"{days}d ago"


def connectivity_meta(ts):
    minutes = (utc_now() - parse_iso(ts)).total_seconds() / 60.0
    if minutes <= ONLINE_AFTER_MINUTES:
        return {"state": "online", "label": "Online"}
    if minutes <= STALE_AFTER_MINUTES:
        return {"state": "stale", "label": "Stale"}
    return {"state": "offline", "label": "Offline"}


def current_value_from_row(row, probe_key):
    probe = PROBE_INDEX[probe_key]
    raw = safe_num(row[probe["raw_key"]], 65535)
    val = safe_num(row[probe_key], 0)
    if raw >= 65535 or val < 0 or val > 100:
        return None
    return val


def station_value_from_row(row):
    vals = []
    for probe in PROBES:
        val = current_value_from_row(row, probe["key"])
        if val is not None:
            vals.append(val)
    if vals:
        return sum(vals) / len(vals)
    return None


def value_state(value, rules):
    if value is None:
        return {"cls": "nodata", "text": "No live data"}
    if value < rules["danger_low"]:
        return {"cls": "bad", "text": "Too dry"}
    if value < rules["warn_low"]:
        return {"cls": "warn", "text": "Dry side"}
    if value <= rules["target_high"]:
        return {"cls": "ok", "text": "On target"}
    if value <= rules["warn_high"]:
        return {"cls": "warn", "text": "Very wet"}
    return {"cls": "bad", "text": "Extreme wet"}


def probe_value_sql(probe_key):
    if probe_key not in PROBE_INDEX:
        raise ValueError("unknown probe")
    raw_key = PROBE_INDEX[probe_key]["raw_key"]
    return f"CASE WHEN {raw_key} >= 65535 OR {probe_key} < 0 OR {probe_key} > 100 THEN NULL ELSE {probe_key} END"


def ensure_station_defaults(conn, station_id):
    base = get_base_rules(station_id)
    conn.execute("""
        INSERT INTO station_config (station_id, display_name, description, default_hours, is_collapsed)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(station_id) DO NOTHING
    """, (station_id, station_id, base["label"], DEFAULT_HOURS, 0))

    for probe in PROBES:
        conn.execute("""
            INSERT INTO probe_config (
                station_id, probe_key, display_name, location_name,
                danger_low, warn_low, target_low, target_high, warn_high, enabled
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 1)
            ON CONFLICT(station_id, probe_key) DO NOTHING
        """, (
            station_id,
            probe["key"],
            probe["default_name"],
            "",
            base["danger_low"],
            base["warn_low"],
            base["target_low"],
            base["target_high"],
            base["warn_high"],
        ))


def get_station_config(conn, station_id):
    ensure_station_defaults(conn, station_id)
    row = conn.execute("""
        SELECT station_id, display_name, description, default_hours, is_collapsed
        FROM station_config
        WHERE station_id = ?
    """, (station_id,)).fetchone()
    return dict(row)


def get_probe_configs(conn, station_id):
    ensure_station_defaults(conn, station_id)
    rows = conn.execute("""
        SELECT station_id, probe_key, display_name, location_name,
               danger_low, warn_low, target_low, target_high, warn_high, enabled
        FROM probe_config
        WHERE station_id = ?
        ORDER BY probe_key
    """, (station_id,)).fetchall()
    return {row["probe_key"]: dict(row) for row in rows}


# ----------------------------
# pH helpers
# ----------------------------
def init_ph_hardware():
    global _ph_ads, _ph_chan, _ph_error

    if not PH_ENABLED:
        _ph_error = "pH disabled"
        return

    if _ph_chan is not None:
        return

    if ADS is None or board is None or busio is None or AnalogIn is None:
        _ph_error = ADS_IMPORT_ERROR or "ADS1115 libraries not available"
        return

    try:
        i2c = busio.I2C(board.SCL, board.SDA)
        ads = ADS.ADS1115(i2c)
        ads.gain = PH_ADC_GAIN

        channel_map = {
            0: ADS.P0,
            1: ADS.P1,
            2: ADS.P2,
            3: ADS.P3,
        }

        _ph_ads = ads
        _ph_chan = AnalogIn(ads, channel_map[PH_CHANNEL_INDEX])
        _ph_error = None
    except Exception as exc:
        _ph_ads = None
        _ph_chan = None
        _ph_error = str(exc)


def surveyor_voltage_to_ph(voltage):
    raw_ph = (PH_SLOPE * float(voltage)) + PH_INTERCEPT
    return (raw_ph * PH_CAL_SCALE) + PH_CAL_OFFSET


def ph_state_from_reading(voltage, ph_value):
    if voltage is None or ph_value is None:
        return {"cls": "nodata", "text": "No valid reading"}

    if voltage < (PH_VOLTS_MIN - 0.10) or voltage > (PH_VOLTS_MAX + 0.10):
        return {"cls": "warn", "text": "Check probe / wiring"}

    return {"cls": "ok", "text": "Live"}


def read_live_ph(samples=PH_SAMPLES, sample_delay=PH_SAMPLE_DELAY):
    init_ph_hardware()

    if _ph_chan is None:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": _ph_error or "ADS1115 unavailable",
            "state": {"cls": "nodata", "text": "Unavailable"},
        }

    voltages = []
    try:
        for _ in range(max(3, int(samples))):
            voltages.append(float(_ph_chan.voltage))
            time.sleep(sample_delay)
    except Exception as exc:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": len(voltages),
            "error": str(exc),
            "state": {"cls": "nodata", "text": "Read failed"},
        }

    if not voltages:
        return {
            "ok": False,
            "ph": None,
            "voltage": None,
            "samples": 0,
            "error": "No ADC samples returned",
            "state": {"cls": "nodata", "text": "No samples"},
        }

    voltage = round(median(voltages), 4)
    ph_value = surveyor_voltage_to_ph(voltage)

    if ph_value < -0.5 or ph_value > 14.5:
        ph_value = None
    else:
        ph_value = round(max(0.0, min(14.0, ph_value)), 2)

    return {
        "ok": True,
        "ph": ph_value,
        "voltage": voltage,
        "samples": len(voltages),
        "error": None,
        "state": ph_state_from_reading(voltage, ph_value),
    }


def maybe_log_ph(ph_data):
    global _ph_last_logged

    if not ph_data.get("ok") or ph_data.get("ph") is None:
        return

    now = utc_now()
    if _ph_last_logged and (now - _ph_last_logged).total_seconds() < PH_LOG_EVERY_SECONDS:
        return

    ts = now.replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()
    conn.execute("""
        INSERT INTO ph_readings (ts, ph_voltage, ph_value)
        VALUES (?, ?, ?)
    """, (ts, ph_data["voltage"], ph_data["ph"]))
    conn.commit()
    conn.close()

    _ph_last_logged = now


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
        soil_raw_1 REAL NOT NULL DEFAULT 65535,
        soil_raw_2 REAL NOT NULL DEFAULT 65535,
        eco2_ppm REAL NOT NULL DEFAULT 0
    )
    """)

    existing = {row["name"] for row in conn.execute("PRAGMA table_info(readings)").fetchall()}
    needed = {
        "soil_moisture_1_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_2_pct": "REAL NOT NULL DEFAULT 0",
        "soil_raw_1": "REAL NOT NULL DEFAULT 65535",
        "soil_raw_2": "REAL NOT NULL DEFAULT 65535",
        "eco2_ppm": "REAL NOT NULL DEFAULT 0",
        "air_temp_c": "REAL NOT NULL DEFAULT 0",
        "humidity_pct": "REAL NOT NULL DEFAULT 0",
        "soil_moisture_pct": "REAL NOT NULL DEFAULT 0",
    }
    for col, coltype in needed.items():
        if col not in existing:
            conn.execute(f"ALTER TABLE readings ADD COLUMN {col} {coltype}")

    conn.execute("""
    CREATE TABLE IF NOT EXISTS station_config (
        station_id TEXT PRIMARY KEY,
        display_name TEXT NOT NULL DEFAULT '',
        description TEXT NOT NULL DEFAULT '',
        default_hours INTEGER NOT NULL DEFAULT 24,
        is_collapsed INTEGER NOT NULL DEFAULT 0
    )
    """)

    conn.execute("""
    CREATE TABLE IF NOT EXISTS probe_config (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        station_id TEXT NOT NULL,
        probe_key TEXT NOT NULL,
        display_name TEXT NOT NULL DEFAULT '',
        location_name TEXT NOT NULL DEFAULT '',
        danger_low REAL NOT NULL,
        warn_low REAL NOT NULL,
        target_low REAL NOT NULL,
        target_high REAL NOT NULL,
        warn_high REAL NOT NULL,
        enabled INTEGER NOT NULL DEFAULT 1,
        UNIQUE(station_id, probe_key)
    )
    """)

    conn.execute("""
    CREATE TABLE IF NOT EXISTS ph_readings (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        ts TEXT NOT NULL,
        ph_voltage REAL,
        ph_value REAL
    )
    """)

    conn.execute("""
    CREATE INDEX IF NOT EXISTS idx_ph_readings_ts
    ON ph_readings(ts)
    """)

    conn.commit()
    conn.close()


@app.route("/ingest", methods=["POST"])
def ingest():
    payload = request.get_json(force=True, silent=True) or {}
    station_id = str(payload.get("station_id", "unknown")).strip() or "unknown"
    ts = utc_now_iso()

    air_temp_c = safe_num(payload.get("air_temp_c", 0))
    humidity_pct = safe_num(payload.get("humidity_pct", 0))
    eco2_ppm = safe_num(payload.get("eco2_ppm", 0))

    soil_raw_1 = safe_num(payload.get("soil_raw_1", 65535), 65535)
    soil_raw_2 = safe_num(payload.get("soil_raw_2", 65535), 65535)
    soil_1 = safe_num(payload.get("soil_moisture_1_pct", 0), 0)
    soil_2 = safe_num(payload.get("soil_moisture_2_pct", 0), 0)

    valid = []
    if soil_raw_1 < 65535:
        valid.append(soil_1)
    if soil_raw_2 < 65535:
        valid.append(soil_2)

    if valid:
        soil_avg = sum(valid) / len(valid)
    else:
        soil_avg = safe_num(payload.get("soil_moisture_pct", 0), 0)

    conn = db()
    ensure_station_defaults(conn, station_id)
    conn.execute("""
        INSERT INTO readings (
            station_id, ts, air_temp_c, humidity_pct,
            soil_moisture_pct, soil_moisture_1_pct, soil_moisture_2_pct,
            soil_raw_1, soil_raw_2, eco2_ppm
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        station_id, ts, air_temp_c, humidity_pct,
        soil_avg, soil_1, soil_2,
        soil_raw_1, soil_raw_2, eco2_ppm
    ))
    conn.commit()
    conn.close()
    return jsonify({"ok": True})


@app.route("/api/dashboard")
def api_dashboard():
    conn = db()
    latest_rows = conn.execute("""
        SELECT r1.*
        FROM readings r1
        JOIN (
            SELECT station_id, MAX(ts) AS max_ts
            FROM readings
            GROUP BY station_id
        ) r2
          ON r1.station_id = r2.station_id
         AND r1.ts = r2.max_ts
        ORDER BY r1.station_id
    """).fetchall()

    results = []
    for row in latest_rows:
        station_id = row["station_id"]
        station_cfg = get_station_config(conn, station_id)
        probe_cfgs = get_probe_configs(conn, station_id)
        station_current = station_value_from_row(row)

        probes = []
        alert_count = 0
        for probe in PROBES:
            probe_cfg = probe_cfgs[probe["key"]]
            current = current_value_from_row(row, probe["key"])
            rules = {
                "danger_low": probe_cfg["danger_low"],
                "warn_low": probe_cfg["warn_low"],
                "target_low": probe_cfg["target_low"],
                "target_high": probe_cfg["target_high"],
                "warn_high": probe_cfg["warn_high"],
            }
            state = value_state(current, rules)
            if state["cls"] in ("warn", "bad"):
                alert_count += 1
            probes.append({
                "probe_key": probe["key"],
                "raw_key": probe["raw_key"],
                "display_name": probe_cfg["display_name"] or probe["default_name"],
                "location_name": probe_cfg["location_name"] or "",
                "current": current,
                "raw": safe_num(row[probe["raw_key"]], 65535),
                "enabled": bool(probe_cfg["enabled"]),
                "rules": rules,
                "state": state,
            })

        results.append({
            "station_id": station_id,
            "display_name": station_cfg["display_name"] or station_id,
            "description": station_cfg["description"] or "",
            "default_hours": clamp_hours(station_cfg["default_hours"]),
            "is_collapsed": bool(station_cfg["is_collapsed"]),
            "updated_at": row["ts"],
            "updated_ago": age_text(row["ts"]),
            "connectivity": connectivity_meta(row["ts"]),
            "station_state": value_state(station_current, get_base_rules(station_id)),
            "probe_count": len(probes),
            "alert_count": alert_count,
            "probes": probes,
        })

    conn.close()
    return jsonify(results)


@app.route("/api/probe-metrics/<station_id>/<probe_key>")
def api_probe_metrics(station_id, probe_key):
    if probe_key not in PROBE_INDEX:
        return jsonify({"error": "Unknown probe"}), 404

    hours = clamp_hours(request.args.get("hours", DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    expr = probe_value_sql(probe_key)

    conn = db()
    stats = conn.execute(f"""
        SELECT
            COUNT({expr}) AS points,
            AVG({expr}) AS avg_value,
            MIN({expr}) AS min_value,
            MAX({expr}) AS max_value
        FROM readings
        WHERE station_id = ? AND ts >= ?
    """, (station_id, since)).fetchone()
    conn.close()

    return jsonify({
        "hours": hours,
        "points": int(stats["points"] or 0),
        "avg": None if stats["avg_value"] is None else float(stats["avg_value"]),
        "min": None if stats["min_value"] is None else float(stats["min_value"]),
        "max": None if stats["max_value"] is None else float(stats["max_value"]),
    })


@app.route("/api/config/<station_id>", methods=["POST"])
def api_save_config(station_id):
    payload = request.get_json(force=True, silent=True) or {}
    station = payload.get("station", {}) or {}
    probes = payload.get("probes", {}) or {}

    conn = db()
    ensure_station_defaults(conn, station_id)
    current_station = get_station_config(conn, station_id)

    display_name = str(station.get("display_name", current_station["display_name"])).strip() or station_id
    description = str(station.get("description", current_station["description"])).strip()
    default_hours = clamp_hours(station.get("default_hours", current_station["default_hours"]))
    is_collapsed = 1 if bool(station.get("is_collapsed", current_station["is_collapsed"])) else 0

    conn.execute("""
        INSERT INTO station_config (station_id, display_name, description, default_hours, is_collapsed)
        VALUES (?, ?, ?, ?, ?)
        ON CONFLICT(station_id) DO UPDATE SET
            display_name = excluded.display_name,
            description = excluded.description,
            default_hours = excluded.default_hours,
            is_collapsed = excluded.is_collapsed
    """, (station_id, display_name, description, default_hours, is_collapsed))

    current_probes = get_probe_configs(conn, station_id)
    for probe_key, probe_data in probes.items():
        if probe_key not in PROBE_INDEX:
            continue
        old = current_probes[probe_key]
        display_name = str(probe_data.get("display_name", old["display_name"])).strip() or PROBE_INDEX[probe_key]["default_name"]
        location_name = str(probe_data.get("location_name", old["location_name"])).strip()
        enabled = 1 if bool(probe_data.get("enabled", old["enabled"])) else 0

        danger_low = clamp_percent(probe_data.get("danger_low"), old["danger_low"])
        warn_low = clamp_percent(probe_data.get("warn_low"), old["warn_low"])
        target_low = clamp_percent(probe_data.get("target_low"), old["target_low"])
        target_high = clamp_percent(probe_data.get("target_high"), old["target_high"])
        warn_high = clamp_percent(probe_data.get("warn_high"), old["warn_high"])

        if not (danger_low <= warn_low <= target_low <= target_high <= warn_high):
            return jsonify({"error": f"Bad threshold order for {probe_key}"}), 400

        conn.execute("""
            INSERT INTO probe_config (
                station_id, probe_key, display_name, location_name,
                danger_low, warn_low, target_low, target_high, warn_high, enabled
            )
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(station_id, probe_key) DO UPDATE SET
                display_name = excluded.display_name,
                location_name = excluded.location_name,
                danger_low = excluded.danger_low,
                warn_low = excluded.warn_low,
                target_low = excluded.target_low,
                target_high = excluded.target_high,
                warn_high = excluded.warn_high,
                enabled = excluded.enabled
        """, (
            station_id, probe_key, display_name, location_name,
            danger_low, warn_low, target_low, target_high, warn_high, enabled
        ))

    conn.commit()
    conn.close()
    return jsonify({"ok": True})


@app.route("/api/ph-live")
def api_ph_live():
    data = read_live_ph()
    if data.get("ok"):
        maybe_log_ph(data)
        data["updated_at"] = utc_now_iso()
    return jsonify(data)


@app.route("/api/ph-metrics")
def api_ph_metrics():
    hours = clamp_hours(request.args.get("hours", PH_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()
    stats = conn.execute("""
        SELECT
            COUNT(ph_value) AS points,
            AVG(ph_value) AS avg_value,
            MIN(ph_value) AS min_value,
            MAX(ph_value) AS max_value,
            AVG(ph_voltage) AS avg_voltage
        FROM ph_readings
        WHERE ts >= ?
    """, (since,)).fetchone()
    conn.close()

    return jsonify({
        "hours": hours,
        "points": int(stats["points"] or 0),
        "avg": None if stats["avg_value"] is None else float(stats["avg_value"]),
        "min": None if stats["min_value"] is None else float(stats["min_value"]),
        "max": None if stats["max_value"] is None else float(stats["max_value"]),
        "avg_voltage": None if stats["avg_voltage"] is None else float(stats["avg_voltage"]),
    })


@app.route("/plot/<station_id>/<probe_key>.svg")
def plot_probe(station_id, probe_key):
    if probe_key not in PROBE_INDEX:
        return Response("Unknown probe", status=404)

    hours = clamp_hours(request.args.get("hours", DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    probe = PROBE_INDEX[probe_key]

    conn = db()
    ensure_station_defaults(conn, station_id)
    probe_cfgs = get_probe_configs(conn, station_id)
    cfg = probe_cfgs[probe_key]
    rows = conn.execute(f"""
        SELECT ts, {probe_key} AS probe_value, {probe['raw_key']} AS raw_value
        FROM readings
        WHERE station_id = ? AND ts >= ?
        ORDER BY ts ASC
    """, (station_id, since)).fetchall()
    conn.close()

    fig, ax = plt.subplots(figsize=(10, 3.3))
    values = []
    times = []

    for row in rows:
        times.append(parse_iso(row["ts"]))
        raw = safe_num(row["raw_value"], 65535)
        val = safe_num(row["probe_value"], 0)
        if raw >= 65535 or val < 0 or val > 100:
            values.append(math.nan)
        else:
            values.append(val)

    valid_points = sum(0 if math.isnan(v) else 1 for v in values)

    if valid_points:
        ax.axhspan(cfg["target_low"], cfg["target_high"], alpha=0.10)
        ax.axhline(cfg["warn_low"], linewidth=1.0, alpha=0.35, linestyle="--")
        ax.axhline(cfg["warn_high"], linewidth=1.0, alpha=0.35, linestyle="--")
        ax.plot(times, values, linewidth=2.4)
        ax.set_ylim(0, 100)
        ax.set_ylabel("Soil moisture %")
        ax.grid(True, alpha=0.28)
        if hours <= 1:
            locator = mdates.MinuteLocator(interval=10)
        elif hours <= 24:
            locator = mdates.HourLocator(interval=2)
        else:
            locator = mdates.DayLocator(interval=1)
        ax.xaxis.set_major_locator(locator)
        ax.xaxis.set_major_formatter(mdates.ConciseDateFormatter(locator))
    else:
        ax.text(0.5, 0.54, "No valid data in selected window", ha="center", va="center", transform=ax.transAxes)
        ax.text(0.5, 0.40, "Live status still uses the most recent reading.", ha="center", va="center", fontsize=9, transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_visible(False)

    ax.set_title(f"{cfg['display_name']} · last {hours}h")
    fig.tight_layout()

    buf = io.StringIO()
    fig.savefig(buf, format="svg", bbox_inches="tight")
    plt.close(fig)
    return Response(buf.getvalue(), mimetype="image/svg+xml")


@app.route("/plot/ph.svg")
def plot_ph():
    hours = clamp_hours(request.args.get("hours", PH_DEFAULT_HOURS, type=int))
    since = (utc_now() - timedelta(hours=hours)).replace(microsecond=0).isoformat().replace("+00:00", "Z")

    conn = db()
    rows = conn.execute("""
        SELECT ts, ph_value
        FROM ph_readings
        WHERE ts >= ?
        ORDER BY ts ASC
    """, (since,)).fetchall()
    conn.close()

    fig, ax = plt.subplots(figsize=(10, 3.3))
    values = []
    times = []

    for row in rows:
        times.append(parse_iso(row["ts"]))
        values.append(safe_num(row["ph_value"], math.nan))

    valid_points = sum(0 if math.isnan(v) else 1 for v in values)

    if valid_points:
        ax.axhline(7.0, linewidth=1.0, alpha=0.25, linestyle="--")
        ax.plot(times, values, linewidth=2.4)
        ax.set_ylim(0, 14)
        ax.set_ylabel("pH")
        ax.grid(True, alpha=0.28)

        if hours <= 1:
            locator = mdates.MinuteLocator(interval=10)
        elif hours <= 24:
            locator = mdates.HourLocator(interval=2)
        else:
            locator = mdates.DayLocator(interval=1)

        ax.xaxis.set_major_locator(locator)
        ax.xaxis.set_major_formatter(mdates.ConciseDateFormatter(locator))
    else:
        ax.text(0.5, 0.54, "No valid pH data in selected window", ha="center", va="center", transform=ax.transAxes)
        ax.text(0.5, 0.40, "Open the page and let the live logger collect a few samples.", ha="center", va="center", fontsize=9, transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_visible(False)

    ax.set_title(f"{PH_NAME} · last {hours}h")
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
      --bg: #eef2f5;
      --panel: #ffffff;
      --panel-soft: #f8fafc;
      --text: #16202a;
      --muted: #667281;
      --border: #d7dee6;
      --shadow: 0 12px 32px rgba(17, 28, 40, 0.08);
      --ok-bg: #eaf8ef;
      --ok-border: #8ac89d;
      --warn-bg: #fff5de;
      --warn-border: #e3b454;
      --bad-bg: #fdeaea;
      --bad-border: #de7b7b;
      --nodata-bg: #f2f5f8;
      --nodata-border: #cbd5df;
      --accent: #2d6cdf;
      --accent-soft: #e7efff;
      --online: #37b24d;
      --stale: #f59f00;
      --offline: #e03131;
      --radius: 18px;
    }

    * { box-sizing: border-box; }

    body {
      margin: 0;
      font-family: Arial, sans-serif;
      background: linear-gradient(180deg, #f6f8fb 0%, #eef2f5 100%);
      color: var(--text);
    }

    .wrap {
      max-width: 1180px;
      margin: 0 auto;
      padding: 20px;
    }

    .topbar {
      display: flex;
      align-items: end;
      justify-content: space-between;
      gap: 16px;
      flex-wrap: wrap;
      margin-bottom: 20px;
    }

    h1 {
      margin: 0 0 6px;
      font-size: 2.1rem;
      line-height: 1.05;
    }

    .subhead {
      color: var(--muted);
      font-size: 1rem;
    }

    .global-note {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px 14px;
      box-shadow: var(--shadow);
      color: var(--muted);
      font-size: 0.95rem;
    }

    .empty, .loading {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: var(--radius);
      padding: 24px;
      box-shadow: var(--shadow);
    }

    #ph-live-slot {
      margin-bottom: 18px;
    }

    .station {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 22px;
      box-shadow: var(--shadow);
      margin-bottom: 18px;
      overflow: hidden;
    }

    .station summary {
      list-style: none;
      cursor: pointer;
      padding: 16px 18px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 14px;
      background: linear-gradient(180deg, #ffffff 0%, #fbfcfd 100%);
    }

    .station summary::-webkit-details-marker { display: none; }

    .summary-left {
      min-width: 0;
      display: flex;
      align-items: center;
      gap: 12px;
      flex: 1;
    }

    .status-dot {
      width: 12px;
      height: 12px;
      border-radius: 999px;
      flex: 0 0 12px;
      box-shadow: 0 0 0 3px rgba(0,0,0,0.04);
    }

    .status-dot.online { background: var(--online); }
    .status-dot.stale { background: var(--stale); }
    .status-dot.offline { background: var(--offline); }

    .summary-text {
      min-width: 0;
      flex: 1;
    }

    .station-name {
      font-size: 1.2rem;
      font-weight: 800;
      margin: 0 0 3px;
      line-height: 1.15;
    }

    .station-meta {
      color: var(--muted);
      font-size: 0.95rem;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }

    .summary-right {
      display: flex;
      align-items: center;
      gap: 10px;
      flex-wrap: wrap;
      justify-content: flex-end;
    }

    .pill {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      border-radius: 999px;
      padding: 8px 12px;
      border: 1px solid var(--border);
      background: var(--panel-soft);
      font-size: 0.92rem;
      font-weight: 700;
    }

    .pill.ok { background: var(--ok-bg); border-color: var(--ok-border); }
    .pill.warn { background: var(--warn-bg); border-color: var(--warn-border); }
    .pill.bad { background: var(--bad-bg); border-color: var(--bad-border); }
    .pill.nodata { background: var(--nodata-bg); border-color: var(--nodata-border); }

    .count-badge {
      background: var(--accent-soft);
      color: var(--accent);
      border-color: #cddcff;
    }

    .station-body {
      padding: 0 18px 18px;
      border-top: 1px solid var(--border);
      background: #fbfcfd;
    }

    .station-info {
      display: flex;
      flex-wrap: wrap;
      justify-content: space-between;
      gap: 10px 16px;
      padding: 14px 0 8px;
      color: var(--muted);
      font-size: 0.95rem;
    }

    .section-card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 14px;
    }

    .settings {
      margin: 8px 0 16px;
    }

    .settings summary {
      padding: 0;
      background: transparent;
      border: none;
      box-shadow: none;
      display: inline-flex;
      justify-content: flex-start;
      gap: 8px;
      font-weight: 700;
      color: var(--accent);
    }

    .settings summary::-webkit-details-marker { display: none; }

    .settings-wrap {
      margin-top: 14px;
      display: grid;
      gap: 14px;
    }

    .fields {
      display: grid;
      gap: 12px;
      grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
    }

    .field {
      display: grid;
      gap: 6px;
    }

    .field span {
      color: var(--muted);
      font-size: 0.84rem;
      font-weight: 700;
      text-transform: uppercase;
      letter-spacing: 0.03em;
    }

    .field input, .field select {
      width: 100%;
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 10px 12px;
      background: #fff;
      font-size: 0.95rem;
      color: var(--text);
    }

    .probe-settings {
      display: grid;
      gap: 12px;
    }

    .probe-settings-card {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 12px;
      background: #fcfdff;
    }

    .probe-settings-title {
      margin: 0 0 10px;
      font-size: 1rem;
      font-weight: 800;
    }

    .settings-actions {
      display: flex;
      justify-content: flex-end;
      align-items: center;
      gap: 10px;
      flex-wrap: wrap;
    }

    .save-msg {
      color: var(--muted);
      font-size: 0.92rem;
    }

    button {
      border: 0;
      border-radius: 12px;
      background: var(--accent);
      color: white;
      padding: 10px 14px;
      font-size: 0.95rem;
      font-weight: 700;
      cursor: pointer;
    }

    button.secondary {
      background: #eef4ff;
      color: var(--accent);
      border: 1px solid #d5e2ff;
    }

    .probe-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
      gap: 14px;
    }

    .probe-card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 18px;
      padding: 14px;
      display: grid;
      gap: 12px;
    }

    .probe-card.ok { border-color: var(--ok-border); background: linear-gradient(180deg, #ffffff 0%, #f7fcf9 100%); }
    .probe-card.warn { border-color: var(--warn-border); background: linear-gradient(180deg, #ffffff 0%, #fffaf0 100%); }
    .probe-card.bad { border-color: var(--bad-border); background: linear-gradient(180deg, #ffffff 0%, #fff5f5 100%); }
    .probe-card.nodata { border-color: var(--nodata-border); background: linear-gradient(180deg, #ffffff 0%, #f7f9fb 100%); }

    .probe-head {
      display: flex;
      justify-content: space-between;
      gap: 10px;
      align-items: start;
      flex-wrap: wrap;
    }

    .probe-name {
      margin: 0 0 4px;
      font-size: 1.12rem;
      font-weight: 800;
    }

    .probe-sub {
      color: var(--muted);
      font-size: 0.95rem;
    }

    .probe-toolbar {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 10px;
      flex-wrap: wrap;
    }

    .range-wrap {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      background: #f7f9fb;
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 8px 10px;
    }

    .range-wrap label {
      color: var(--muted);
      font-size: 0.88rem;
      font-weight: 700;
    }

    .range-wrap select {
      border: 0;
      background: transparent;
      font-size: 0.95rem;
      color: var(--text);
      outline: none;
    }

    .metrics {
      display: grid;
      grid-template-columns: repeat(3, minmax(0, 1fr));
      gap: 10px;
    }

    .metric {
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 12px;
      background: #fcfdff;
    }

    .metric-label {
      color: var(--muted);
      font-size: 0.80rem;
      margin-bottom: 6px;
      text-transform: uppercase;
      letter-spacing: 0.04em;
      font-weight: 800;
    }

    .metric-value {
      font-size: 1.18rem;
      font-weight: 800;
      line-height: 1.1;
    }

    .metric-note {
      margin-top: 4px;
      color: var(--muted);
      font-size: 0.82rem;
    }

    .target-band {
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 12px;
      background: #f8fbff;
    }

    .plot-box {
      border: 1px solid var(--border);
      border-radius: 16px;
      padding: 10px;
      background: #fbfcfe;
      min-height: 180px;
    }

    .plot-box img {
      width: 100%;
      display: block;
      border-radius: 10px;
    }

    .tech summary {
      padding: 0;
      background: transparent;
      border: none;
      box-shadow: none;
      font-weight: 700;
      color: var(--muted);
      display: inline-flex;
      gap: 8px;
      justify-content: flex-start;
    }

    .tech summary::-webkit-details-marker { display: none; }

    .tech-grid {
      margin-top: 10px;
      display: grid;
      gap: 10px;
      grid-template-columns: repeat(auto-fit, minmax(130px, 1fr));
    }

    .tech-item {
      border: 1px solid var(--border);
      border-radius: 12px;
      padding: 10px;
      background: #fcfdff;
    }

    .tiny {
      color: var(--muted);
      font-size: 0.82rem;
    }

    @media (max-width: 760px) {
      .wrap { padding: 14px; }
      h1 { font-size: 1.65rem; }
      .metrics { grid-template-columns: 1fr; }
      .station summary { padding: 14px; align-items: flex-start; }
      .summary-right { justify-content: flex-start; }
    }
  </style>
</head>
<body>
  <div class="wrap">
    <div class="topbar">
      <div>
        <h1>Weather Station Host</h1>
        <div class="subhead">Station probes refresh every 60 seconds · bench pH is live</div>
      </div>
      <div class="global-note">Tip: open a unit, rename probes, and adjust thresholds live from the settings panel.</div>
    </div>

    <div id="ph-live-slot"></div>
    <div id="content" class="loading">Loading dashboard…</div>
  </div>

  <script>
    const DEFAULT_HOURS = __DEFAULT_HOURS__;
    const ALLOWED_WINDOWS = __ALLOWED_WINDOWS__;
    const PH_DEFAULT_HOURS = __PH_DEFAULT_HOURS__;

    function escapeHtml(value) {
      return String(value ?? "")
        .replaceAll("&", "&amp;")
        .replaceAll("<", "&lt;")
        .replaceAll(">", "&gt;")
        .replaceAll('"', "&quot;")
        .replaceAll("'", "&#39;");
    }

    function fmtPct(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(1) + " %";
    }

    function fmtPH(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(2) + " pH";
    }

    function fmtVoltage(value) {
      if (value === null || value === undefined || Number.isNaN(Number(value))) return "—";
      return Number(value).toFixed(3) + " V";
    }

    function fmtRaw(value) {
      if (value === null || value === undefined) return "—";
      const n = Number(value);
      if (!Number.isFinite(n) || n >= 65535) return "No reading";
      return n.toFixed(0);
    }

    function fmtRange(rules) {
      return `${Number(rules.target_low).toFixed(0)}%–${Number(rules.target_high).toFixed(0)}%`;
    }

    function formatWindow(hours) {
      if (Number(hours) === 1) return "1h";
      if (Number(hours) === 24) return "24h";
      return "7d";
    }

    function stateClass(state) {
      return state?.cls || "nodata";
    }

    function loadExpandedState(stationId, fallbackCollapsed) {
      const key = `station-open:${stationId}`;
      const saved = localStorage.getItem(key);
      if (saved !== null) return saved === "1";
      return !fallbackCollapsed;
    }

    function saveExpandedState(stationId, open) {
      localStorage.setItem(`station-open:${stationId}`, open ? "1" : "0");
    }

    function getProbeHours(stationId, probeKey, fallback) {
      const key = `probe-hours:${stationId}:${probeKey}`;
      const saved = Number(localStorage.getItem(key));
      if (ALLOWED_WINDOWS.includes(saved)) return saved;
      return fallback;
    }

    function setProbeHours(stationId, probeKey, hours) {
      localStorage.setItem(`probe-hours:${stationId}:${probeKey}`, String(hours));
    }

    function getPhHours() {
      const saved = Number(localStorage.getItem("ph-hours"));
      if (ALLOWED_WINDOWS.includes(saved)) return saved;
      return PH_DEFAULT_HOURS;
    }

    function setPhHours(hours) {
      localStorage.setItem("ph-hours", String(hours));
    }

    function renderProbeSettings(station) {
      return station.probes.map((probe) => `
        <div class="probe-settings-card">
          <div class="probe-settings-title">${escapeHtml(probe.display_name || probe.probe_key)}</div>
          <div class="fields">
            <label class="field">
              <span>Probe name</span>
              <input type="text" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="display_name" value="${escapeHtml(probe.display_name)}">
            </label>
            <label class="field">
              <span>Location / note</span>
              <input type="text" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="location_name" value="${escapeHtml(probe.location_name || "")}">
            </label>
            <label class="field">
              <span>Danger low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="danger_low" value="${escapeHtml(probe.rules.danger_low)}">
            </label>
            <label class="field">
              <span>Warn low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="warn_low" value="${escapeHtml(probe.rules.warn_low)}">
            </label>
            <label class="field">
              <span>Target low</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="target_low" value="${escapeHtml(probe.rules.target_low)}">
            </label>
            <label class="field">
              <span>Target high</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="target_high" value="${escapeHtml(probe.rules.target_high)}">
            </label>
            <label class="field">
              <span>Warn high</span>
              <input type="number" step="0.1" min="0" max="100" data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="warn_high" value="${escapeHtml(probe.rules.warn_high)}">
            </label>
            <label class="field">
              <span>Enabled</span>
              <select data-probe-key="${escapeHtml(probe.probe_key)}" data-probe-field="enabled">
                <option value="true" ${probe.enabled ? "selected" : ""}>Visible</option>
                <option value="false" ${probe.enabled ? "" : "selected"}>Hidden</option>
              </select>
            </label>
          </div>
        </div>
      `).join("");
    }

    function renderProbeCard(station, probe) {
      const hours = getProbeHours(station.station_id, probe.probe_key, station.default_hours || DEFAULT_HOURS);
      return `
        <div class="probe-card ${escapeHtml(stateClass(probe.state))}" data-station-id="${escapeHtml(station.station_id)}" data-probe-key="${escapeHtml(probe.probe_key)}">
          <div class="probe-head">
            <div>
              <h3 class="probe-name">${escapeHtml(probe.display_name)}</h3>
              <div class="probe-sub">
                ${escapeHtml(probe.location_name || "No location label yet")} · target ${escapeHtml(fmtRange(probe.rules))}
              </div>
            </div>
            <div class="pill ${escapeHtml(stateClass(probe.state))}">${escapeHtml(probe.state?.text || "No data")}</div>
          </div>

          <div class="probe-toolbar">
            <div class="tiny">Latest reading stays active even if this graph window is empty.</div>
            <div class="range-wrap">
              <label>Graph range</label>
              <select class="probe-range">
                <option value="1" ${hours === 1 ? "selected" : ""}>Last 1 hour</option>
                <option value="24" ${hours === 24 ? "selected" : ""}>Last 24 hours</option>
                <option value="168" ${hours === 168 ? "selected" : ""}>Last 7 days</option>
              </select>
            </div>
          </div>

          <div class="metrics">
            <div class="metric">
              <div class="metric-label">Current</div>
              <div class="metric-value">${escapeHtml(fmtPct(probe.current))}</div>
              <div class="metric-note">Live reading</div>
            </div>
            <div class="metric">
              <div class="metric-label">Average</div>
              <div class="metric-value js-avg">Loading…</div>
              <div class="metric-note js-window-label">Window ${escapeHtml(formatWindow(hours))}</div>
            </div>
            <div class="metric target-band">
              <div class="metric-label">Target band</div>
              <div class="metric-value">${escapeHtml(fmtRange(probe.rules))}</div>
              <div class="metric-note">Editable in settings</div>
            </div>
          </div>

          <div class="plot-box">
            <img class="probe-plot" alt="Graph for ${escapeHtml(probe.display_name)}">
          </div>

          <details class="tech">
            <summary>Technical data</summary>
            <div class="tech-grid">
              <div class="tech-item">
                <div class="tiny">Raw</div>
                <div><strong>${escapeHtml(fmtRaw(probe.raw))}</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Valid points</div>
                <div><strong class="js-points">Loading…</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Minimum</div>
                <div><strong class="js-min">Loading…</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Maximum</div>
                <div><strong class="js-max">Loading…</strong></div>
              </div>
            </div>
          </details>
        </div>
      `;
    }

    function renderStation(station) {
      const open = loadExpandedState(station.station_id, station.is_collapsed);
      const shownProbes = station.probes.filter(p => p.enabled);
      return `
        <details class="station" data-station-id="${escapeHtml(station.station_id)}" ${open ? "open" : ""}>
          <summary>
            <div class="summary-left">
              <span class="status-dot ${escapeHtml(station.connectivity.state)}"></span>
              <div class="summary-text">
                <div class="station-name">${escapeHtml(station.display_name)}</div>
                <div class="station-meta">
                  ${escapeHtml(station.description || "No unit description")} · ${escapeHtml(station.connectivity.label)} · updated ${escapeHtml(station.updated_ago)}
                </div>
              </div>
            </div>
            <div class="summary-right">
              <div class="pill ${escapeHtml(stateClass(station.station_state))}">${escapeHtml(station.station_state.text)}</div>
              <div class="pill count-badge">${shownProbes.length} probes${station.alert_count ? ` · ${station.alert_count} alert${station.alert_count > 1 ? "s" : ""}` : ""}</div>
            </div>
          </summary>

          <div class="station-body">
            <div class="station-info">
              <div><strong>Station ID:</strong> ${escapeHtml(station.station_id)}</div>
              <div><strong>Updated:</strong> ${escapeHtml(station.updated_at)}</div>
            </div>

            <details class="settings section-card">
              <summary>Edit names and thresholds</summary>
              <div class="settings-wrap" data-config-station="${escapeHtml(station.station_id)}">
                <div class="fields">
                  <label class="field">
                    <span>Unit name</span>
                    <input type="text" data-station-field="display_name" value="${escapeHtml(station.display_name)}">
                  </label>
                  <label class="field">
                    <span>Unit description</span>
                    <input type="text" data-station-field="description" value="${escapeHtml(station.description || "")}">
                  </label>
                  <label class="field">
                    <span>Default graph range</span>
                    <select data-station-field="default_hours">
                      <option value="1" ${Number(station.default_hours) === 1 ? "selected" : ""}>Last 1 hour</option>
                      <option value="24" ${Number(station.default_hours) === 24 ? "selected" : ""}>Last 24 hours</option>
                      <option value="168" ${Number(station.default_hours) === 168 ? "selected" : ""}>Last 7 days</option>
                    </select>
                  </label>
                  <label class="field">
                    <span>Collapsed by default</span>
                    <select data-station-field="is_collapsed">
                      <option value="false" ${station.is_collapsed ? "" : "selected"}>Expanded</option>
                      <option value="true" ${station.is_collapsed ? "selected" : ""}>Collapsed</option>
                    </select>
                  </label>
                </div>

                <div class="probe-settings">
                  ${renderProbeSettings(station)}
                </div>

                <div class="settings-actions">
                  <div class="save-msg" data-save-msg="${escapeHtml(station.station_id)}"></div>
                  <button type="button" data-save-station="${escapeHtml(station.station_id)}">Save settings</button>
                </div>
              </div>
            </details>

            <div class="probe-grid">
              ${shownProbes.map(probe => renderProbeCard(station, probe)).join("")}
            </div>
          </div>
        </details>
      `;
    }

    function renderPhPanel() {
      const hours = getPhHours();

      return `
        <div class="probe-card nodata" id="ph-card">
          <div class="probe-head">
            <div>
              <h3 class="probe-name">${escapeHtml("Bench pH Probe")}</h3>
              <div class="probe-sub">${escapeHtml("Atlas Surveyor live read from Raspberry Pi")}</div>
            </div>
            <div class="pill nodata js-ph-state">Starting…</div>
          </div>

          <div class="probe-toolbar">
            <div class="tiny js-ph-updated">Waiting for first live sample…</div>
            <div class="range-wrap">
              <label>Graph range</label>
              <select id="ph-range">
                <option value="1" ${hours === 1 ? "selected" : ""}>Last 1 hour</option>
                <option value="24" ${hours === 24 ? "selected" : ""}>Last 24 hours</option>
                <option value="168" ${hours === 168 ? "selected" : ""}>Last 7 days</option>
              </select>
            </div>
          </div>

          <div class="metrics">
            <div class="metric">
              <div class="metric-label">Current</div>
              <div class="metric-value js-ph-current">Loading…</div>
              <div class="metric-note js-ph-voltage">Voltage —</div>
            </div>
            <div class="metric">
              <div class="metric-label">Average</div>
              <div class="metric-value js-ph-avg">Loading…</div>
              <div class="metric-note js-ph-window">Window ${formatWindow(hours)}</div>
            </div>
            <div class="metric target-band">
              <div class="metric-label">Mode</div>
              <div class="metric-value">Live</div>
              <div class="metric-note">Direct Pi read</div>
            </div>
          </div>

          <div class="plot-box">
            <img id="ph-plot" alt="Graph for bench pH probe">
          </div>

          <details class="tech">
            <summary>Technical data</summary>
            <div class="tech-grid">
              <div class="tech-item">
                <div class="tiny">Samples / read</div>
                <div><strong class="js-ph-samples">—</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Valid points</div>
                <div><strong class="js-ph-points">—</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Minimum</div>
                <div><strong class="js-ph-min">—</strong></div>
              </div>
              <div class="tech-item">
                <div class="tiny">Maximum</div>
                <div><strong class="js-ph-max">—</strong></div>
              </div>
            </div>
            <div class="tiny js-ph-error" style="margin-top:8px;"></div>
          </details>
        </div>
      `;
    }

    async function refreshProbeCard(card) {
      const stationId = card.dataset.stationId;
      const probeKey = card.dataset.probeKey;
      const hours = Number(card.querySelector(".probe-range").value || DEFAULT_HOURS);
      setProbeHours(stationId, probeKey, hours);

      const metrics = await fetch(`/api/probe-metrics/${encodeURIComponent(stationId)}/${encodeURIComponent(probeKey)}?hours=${hours}`);
      const data = await metrics.json();

      card.querySelector(".js-avg").textContent = data.avg === null ? "—" : fmtPct(data.avg);
      card.querySelector(".js-window-label").textContent = `Window ${formatWindow(hours)}`;
      card.querySelector(".js-points").textContent = String(Number(data.points || 0));
      card.querySelector(".js-min").textContent = data.min === null ? "—" : fmtPct(data.min);
      card.querySelector(".js-max").textContent = data.max === null ? "—" : fmtPct(data.max);

      const img = card.querySelector(".probe-plot");
      img.src = `/plot/${encodeURIComponent(stationId)}/${encodeURIComponent(probeKey)}.svg?hours=${hours}&_=${Date.now()}`;
    }

    function gatherStationPayload(stationId) {
      const root = document.querySelector(`[data-config-station="${CSS.escape(stationId)}"]`);
      const station = {};
      root.querySelectorAll("[data-station-field]").forEach(el => {
        const field = el.dataset.stationField;
        let value = el.value;
        if (field === "default_hours") value = Number(value);
        if (field === "is_collapsed") value = value === "true";
        station[field] = value;
      });

      const probes = {};
      root.querySelectorAll("[data-probe-key]").forEach(el => {
        const probeKey = el.dataset.probeKey;
        const field = el.dataset.probeField;
        if (!probes[probeKey]) probes[probeKey] = {};
        let value = el.value;
        if (["danger_low", "warn_low", "target_low", "target_high", "warn_high"].includes(field)) value = Number(value);
        if (field === "enabled") value = value === "true";
        probes[probeKey][field] = value;
      });

      return { station, probes };
    }

    async function saveStationConfig(stationId) {
      const msg = document.querySelector(`[data-save-msg="${CSS.escape(stationId)}"]`);
      msg.textContent = "Saving…";
      const payload = gatherStationPayload(stationId);

      const res = await fetch(`/api/config/${encodeURIComponent(stationId)}`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload)
      });

      const data = await res.json();
      if (!res.ok) {
        msg.textContent = data.error || "Save failed";
        return;
      }

      msg.textContent = "Saved";
      await loadDashboard();
    }

    function mountPhPanel() {
      const slot = document.getElementById("ph-live-slot");
      if (!slot) return;

      slot.innerHTML = renderPhPanel();

      document.getElementById("ph-range").addEventListener("change", async (event) => {
        setPhHours(Number(event.target.value));
        await refreshPhPanel(true);
      });
    }

    async function refreshPhPanel(full = false) {
      const card = document.getElementById("ph-card");
      if (!card) return;

      const liveRes = await fetch("/api/ph-live");
      const live = await liveRes.json();

      const cls = stateClass(live.state);
      card.classList.remove("ok", "warn", "bad", "nodata");
      card.classList.add(cls);

      const pill = card.querySelector(".js-ph-state");
      pill.className = `pill ${cls} js-ph-state`;
      pill.textContent = live.state?.text || "Unavailable";

      card.querySelector(".js-ph-current").textContent = fmtPH(live.ph);
      card.querySelector(".js-ph-voltage").textContent = live.voltage === null ? "Voltage —" : `Voltage ${fmtVoltage(live.voltage)}`;
      card.querySelector(".js-ph-samples").textContent = String(Number(live.samples || 0));
      card.querySelector(".js-ph-updated").textContent = live.ok ? "Live ADS1115 read" : "Live read unavailable";
      card.querySelector(".js-ph-error").textContent = live.error ? `Reader error: ${live.error}` : "";

      if (!full) return;

      const hours = getPhHours();
      const metricsRes = await fetch(`/api/ph-metrics?hours=${hours}`);
      const metrics = await metricsRes.json();

      card.querySelector(".js-ph-avg").textContent = metrics.avg === null ? "—" : fmtPH(metrics.avg);
      card.querySelector(".js-ph-window").textContent = `Window ${formatWindow(hours)}`;
      card.querySelector(".js-ph-points").textContent = String(Number(metrics.points || 0));
      card.querySelector(".js-ph-min").textContent = metrics.min === null ? "—" : fmtPH(metrics.min);
      card.querySelector(".js-ph-max").textContent = metrics.max === null ? "—" : fmtPH(metrics.max);

      const plot = document.getElementById("ph-plot");
      plot.src = `/plot/ph.svg?hours=${hours}&_=${Date.now()}`;
    }

    async function attachDynamicHandlers() {
      document.querySelectorAll(".station").forEach(stationEl => {
        stationEl.addEventListener("toggle", () => {
          saveExpandedState(stationEl.dataset.stationId, stationEl.open);
        });
      });

      document.querySelectorAll(".probe-range").forEach(select => {
        select.addEventListener("change", async (event) => {
          const card = event.target.closest(".probe-card");
          await refreshProbeCard(card);
        });
      });

      document.querySelectorAll("[data-save-station]").forEach(btn => {
        btn.addEventListener("click", async () => {
          await saveStationConfig(btn.dataset.saveStation);
        });
      });

      for (const card of document.querySelectorAll(".probe-card[data-station-id]")) {
        await refreshProbeCard(card);
      }
    }

    async function loadDashboard() {
      const content = document.getElementById("content");
      const res = await fetch("/api/dashboard");
      const stations = await res.json();

      if (!stations.length) {
        content.className = "empty";
        content.innerHTML = "No station data received yet.";
        return;
      }

      content.className = "";
      content.innerHTML = stations.map(renderStation).join("");
      await attachDynamicHandlers();
    }

    mountPhPanel();
    refreshPhPanel(true);
    loadDashboard();

    setInterval(loadDashboard, 60000);
    setInterval(() => refreshPhPanel(false), 5000);
    setInterval(() => refreshPhPanel(true), 30000);
  </script>
</body>
</html>
"""
    html = html.replace("__DEFAULT_HOURS__", json.dumps(DEFAULT_HOURS))
    html = html.replace("__ALLOWED_WINDOWS__", json.dumps(ALLOWED_WINDOWS))
    html = html.replace("__PH_DEFAULT_HOURS__", json.dumps(PH_DEFAULT_HOURS))
    return Response(html, mimetype="text/html")


if __name__ == "__main__":
    init_db()
    init_ph_hardware()
    app.run(host="0.0.0.0", port=5000, debug=False)
