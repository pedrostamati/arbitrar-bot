import asyncio
import aiohttp
import json
import time
from datetime import datetime

# ═══════════════════════════════════════════
# CONFIGURACIÓN
# ═══════════════════════════════════════════
BOT_TOKEN = "8535999247:AAFTUBTxStAe9OS_VE-1gbffvVb5H4ZGzxI"
CHAT_ID   = "6561621265"

# Parámetros de arbitraje (modificables)
CAPITAL_USD   = 1000    # Capital en USD
NETWORK_FEE   = 0.5     # Fee de red en USDT (TRC-20)
ALERT_PCT     = 0.3     # Umbral mínimo de ganancia neta %
CHECK_INTERVAL = 15     # Segundos entre consultas

# ═══════════════════════════════════════════
# EXCHANGES
# ═══════════════════════════════════════════
EXCHANGES = {
    "binance_p2p":  {"name": "Binance P2P",  "short": "Binance",   "cyKey": "binance"},
    "buenbit":      {"name": "BuenBit",       "short": "BuenBit",   "cyKey": "buenbit"},
    "letsbit":      {"name": "LetsBit",       "short": "LetsBit",   "cyKey": "letsbit"},
    "ripio":        {"name": "Ripio",         "short": "Ripio",     "cyKey": "ripio"},
    "satoshitango": {"name": "SatoshiTango",  "short": "SatoshiT",  "cyKey": "satoshitango"},
    "lemon":        {"name": "Lemon Cash",    "short": "Lemon",     "cyKey": "lemoncash"},
    "fiwind":       {"name": "Fiwind",        "short": "Fiwind",    "cyKey": "fiwind"},
    "astropay":     {"name": "AstroPay",      "short": "AstroPay",  "cyKey": "astropay"},
}

# URLs de los exchanges para el mensaje
EXCHANGE_URLS = {
    "binance_p2p":  "https://p2p.binance.com/trade/buy/USDT?fiat=ARS",
    "buenbit":      "https://buenbit.com",
    "letsbit":      "https://letsbit.io",
    "ripio":        "https://exchange.ripio.com",
    "satoshitango": "https://satoshitango.com",
    "lemon":        "https://lemon.me",
    "fiwind":       "https://fiwind.io",
    "astropay":     "https://astropay.com/wallet/exchange",
}

# ═══════════════════════════════════════════
# ESTADO
# ═══════════════════════════════════════════
alerted_keys = {}  # key -> timestamp de última alerta
ALERT_COOLDOWN = 120  # segundos entre alertas del mismo par

# ═══════════════════════════════════════════
# TELEGRAM
# ═══════════════════════════════════════════
async def send_telegram(session, message):
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": CHAT_ID,
        "text": message,
        "parse_mode": "HTML",
        "disable_web_page_preview": True,
    }
    try:
        async with session.post(url, json=payload, timeout=aiohttp.ClientTimeout(total=10)) as r:
            return r.status == 200
    except Exception as e:
        print(f"[Telegram error] {e}")
        return False

# ═══════════════════════════════════════════
# FETCH DATOS
# ═══════════════════════════════════════════
async def fetch_json(session, url):
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=10)) as r:
            if r.status == 200:
                return await r.json(content_type=None)
    except Exception as e:
        print(f"[Fetch error] {url}: {e}")
    return None

async def fetch_all(session):
    results = await asyncio.gather(
        fetch_json(session, "https://dolarapi.com/v1/dolares"),
        fetch_json(session, "https://criptoya.com/api/usdt/ars/1"),
        fetch_json(session, "https://criptoya.com/api/dai/ars/1"),
        fetch_json(session, "https://criptoya.com/api/btc/ars/1"),
    )
    return results

# ═══════════════════════════════════════════
# MOTOR DE ARBITRAJE
# ═══════════════════════════════════════════
def parse_prices(cy_data, asset):
    """Extrae bid/ask para cada exchange desde respuesta de CriptoYa"""
    prices = {}
    if not cy_data:
        return prices
    for ex_id, ex in EXCHANGES.items():
        key = ex["cyKey"]
        if key in cy_data and isinstance(cy_data[key], dict):
            d = cy_data[key]
            bid = d.get("totalBid") or d.get("bid")
            ask = d.get("totalAsk") or d.get("ask")
            if bid and ask:
                prices[ex_id] = {"bid": float(bid), "ask": float(ask), "asset": asset}
    return prices

def fmt_ars(n):
    return f"${n:,.0f}".replace(",", ".")

def fmt_pct(n):
    sign = "+" if n >= 0 else ""
    return f"{sign}{n:.2f}%"

def calc_usdt(prices_usdt, b_id, s_id, cap, usd_ars, net_fee):
    pb = prices_usdt.get(b_id)
    ps = prices_usdt.get(s_id)
    if not pb or not ps:
        return None
    cap_ars = cap * usd_ars
    units = cap_ars / pb["ask"]
    units_net = units - net_fee
    if units_net <= 0:
        return None
    p_ars = units_net * ps["bid"] - cap_ars
    p_pct = (p_ars / cap_ars) * 100
    return {
        "type": "USDT",
        "b_id": b_id, "s_id": s_id,
        "p_pct": p_pct, "p_ars": p_ars, "p_usd": p_ars / usd_ars,
        "ask": pb["ask"], "bid": ps["bid"],
        "desc": f"USDT: {EXCHANGES[b_id]['short']} → {EXCHANGES[s_id]['short']}",
        "units_net": units_net,
    }

def calc_stable(prices_usdt, prices_dai, ex_id, cap, usd_ars):
    pu = prices_usdt.get(ex_id)
    pd = prices_dai.get(ex_id)
    if not pu or not pd:
        return None
    cap_ars = cap * usd_ars
    # Ruta A: comprar USDT, vender DAI
    un_a = cap_ars / pu["ask"]
    p_a = un_a * pd["bid"] - cap_ars
    pct_a = (p_a / cap_ars) * 100
    # Ruta B: comprar DAI, vender USDT
    un_b = cap_ars / pd["ask"]
    p_b = un_b * pu["bid"] - cap_ars
    pct_b = (p_b / cap_ars) * 100
    if pct_a >= pct_b:
        return {"type": "USDT/DAI", "b_id": ex_id, "s_id": ex_id,
                "p_pct": pct_a, "p_ars": p_a, "p_usd": p_a / usd_ars,
                "ask": pu["ask"], "bid": pd["bid"],
                "desc": f"USDT→DAI en {EXCHANGES[ex_id]['short']}",
                "detail": f"Comprás USDT @ {fmt_ars(pu['ask'])} · Vendés DAI @ {fmt_ars(pd['bid'])}"}
    else:
        return {"type": "USDT/DAI", "b_id": ex_id, "s_id": ex_id,
                "p_pct": pct_b, "p_ars": p_b, "p_usd": p_b / usd_ars,
                "ask": pd["ask"], "bid": pu["bid"],
                "desc": f"DAI→USDT en {EXCHANGES[ex_id]['short']}",
                "detail": f"Comprás DAI @ {fmt_ars(pd['ask'])} · Vendés USDT @ {fmt_ars(pu['bid'])}"}

def calc_btc(prices_btc, b_id, s_id, cap, usd_ars):
    pb = prices_btc.get(b_id)
    ps = prices_btc.get(s_id)
    if not pb or not ps:
        return None
    cap_ars = cap * usd_ars
    btc = cap_ars / pb["ask"]
    p_ars = btc * ps["bid"] - cap_ars
    p_pct = (p_ars / cap_ars) * 100
    return {
        "type": "BTC", "b_id": b_id, "s_id": s_id,
        "p_pct": p_pct, "p_ars": p_ars, "p_usd": p_ars / usd_ars,
        "ask": pb["ask"], "bid": ps["bid"],
        "desc": f"BTC: {EXCHANGES[b_id]['short']} → {EXCHANGES[s_id]['short']}",
    }

def compute_all(prices_usdt, prices_dai, prices_btc, usd_ars, cap, net_fee):
    opps = []
    ids = list(EXCHANGES.keys())
    # USDT entre exchanges
    for b in ids:
        for s in ids:
            if b == s: continue
            r = calc_usdt(prices_usdt, b, s, cap, usd_ars, net_fee)
            if r: opps.append(r)
    # Stablecoins mismo exchange
    for ex in ids:
        r = calc_stable(prices_usdt, prices_dai, ex, cap, usd_ars)
        if r: opps.append(r)
    # BTC entre exchanges
    for b in ids:
        for s in ids:
            if b == s: continue
            r = calc_btc(prices_btc, b, s, cap, usd_ars)
            if r: opps.append(r)
    opps.sort(key=lambda x: x["p_pct"], reverse=True)
    return opps

# ═══════════════════════════════════════════
# MENSAJE DE ALERTA
# ═══════════════════════════════════════════
def build_alert_message(opp, cap, usd_ars):
    now = datetime.now().strftime("%H:%M:%S")
    b_name = EXCHANGES[opp["b_id"]]["name"]
    s_name = EXCHANGES[opp["s_id"]]["name"]
    b_url  = EXCHANGE_URLS.get(opp["b_id"], "")
    s_url  = EXCHANGE_URLS.get(opp["s_id"], "")
    p_usd  = abs(opp["p_usd"])
    sign   = "+" if opp["p_pct"] >= 0 else "−"

    lines = [
        f"🚨 <b>ARBITRAJE DETECTADO — ArbitrAR</b>",
        f"",
        f"📊 <b>Tipo:</b> {opp['type']}",
        f"📍 <b>Ruta:</b> {opp['desc']}",
        f"",
        f"💹 <b>P&L neto: {sign}{abs(opp['p_pct']):.2f}%</b>",
        f"💰 Ganancia: {sign}{fmt_ars(abs(opp['p_ars']))} ARS",
        f"💵 Ganancia: {sign}U$D {p_usd:.2f}",
        f"",
        f"📥 <b>Paso 1 — COMPRAR en {b_name}</b>",
        f"   Precio ask: {fmt_ars(opp['ask'])} ARS/USDT",
        f"   🔗 {b_url}",
    ]
    if opp.get("detail"):
        lines.append(f"")
        lines.append(f"🔄 {opp['detail']}")
    lines += [
        f"",
        f"📤 <b>Paso 2 — VENDER en {s_name}</b>" if opp["b_id"] != opp["s_id"] else f"📤 <b>Paso 2 — VENDER</b>",
        f"   Precio bid: {fmt_ars(opp['bid'])} ARS/USDT",
    ]
    if opp["b_id"] != opp["s_id"]:
        lines.append(f"   🔗 {s_url}")
    lines += [
        f"",
        f"💼 Capital: U$D {cap:,}",
        f"🕐 Hora: {now}",
        f"",
        f"⚠️ <i>Verificar precios antes de operar. No es asesoramiento financiero.</i>",
    ]
    return "\n".join(lines)

# ═══════════════════════════════════════════
# LOOP PRINCIPAL
# ═══════════════════════════════════════════
async def main():
    print(f"🤖 ArbitrAR Bot iniciado")
    print(f"   Capital: U$D {CAPITAL_USD}")
    print(f"   Umbral alerta: {ALERT_PCT}%")
    print(f"   Intervalo: {CHECK_INTERVAL}s")
    print(f"   Chat ID: {CHAT_ID}")
    print()

    async with aiohttp.ClientSession() as session:
        # Mensaje de inicio
        await send_telegram(session,
            "🤖 <b>ArbitrAR Bot activo</b>\n\n"
            f"Monitoreando arbitraje USDT/DAI/BTC en {len(EXCHANGES)} exchanges.\n"
            f"Capital: U$D {CAPITAL_USD:,} · Umbral: {ALERT_PCT}% · Cada {CHECK_INTERVAL}s\n\n"
            "Te aviso cuando encuentre una oportunidad rentable 🚀"
        )

        usd_ars = 1550  # fallback

        while True:
            try:
                dolar_data, usdt_data, dai_data, btc_data = await fetch_all(session)

                # Actualizar tipo de cambio
                if dolar_data:
                    blue = next((d for d in dolar_data if d.get("casa") == "blue"), None)
                    if blue:
                        usd_ars = (blue["compra"] + blue["venta"]) / 2

                prices_usdt = parse_prices(usdt_data, "USDT")
                prices_dai  = parse_prices(dai_data,  "DAI")
                prices_btc  = parse_prices(btc_data,  "BTC")

                opps = compute_all(prices_usdt, prices_dai, prices_btc, usd_ars, CAPITAL_USD, NETWORK_FEE)

                now_ts = time.time()
                profitable = [o for o in opps if o["p_pct"] >= ALERT_PCT]

                for opp in profitable:
                    key = f"{opp['type']}-{opp['b_id']}-{opp['s_id']}-{int(opp['p_pct']*10)}"
                    last = alerted_keys.get(key, 0)
                    if now_ts - last < ALERT_COOLDOWN:
                        continue
                    alerted_keys[key] = now_ts
                    msg = build_alert_message(opp, CAPITAL_USD, usd_ars)
                    ok = await send_telegram(session, msg)
                    status = "✓ enviada" if ok else "✗ error"
                    print(f"[{datetime.now().strftime('%H:%M:%S')}] ALERTA {status}: {opp['desc']} {opp['p_pct']:.2f}%")

                best = opps[0] if opps else None
                print(f"[{datetime.now().strftime('%H:%M:%S')}] "
                      f"USD/ARS={usd_ars:.0f} "
                      f"exchanges={len(prices_usdt)} "
                      f"rutas={len(opps)} "
                      f"con ganancia={len(profitable)} "
                      f"mejor={best['p_pct']:.2f}% ({best['desc']})" if best else "sin datos")

            except Exception as e:
                print(f"[{datetime.now().strftime('%H:%M:%S')}] Error en ciclo: {e}")

            await asyncio.sleep(CHECK_INTERVAL)

if __name__ == "__main__":
    asyncio.run(main())
