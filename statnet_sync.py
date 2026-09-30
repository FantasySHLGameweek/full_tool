#!/usr/bin/env python3
"""Statnet -> Fantasy SHL-poäng (bara Pythons standardbibliotek).

Hämtar SHL:s officiella matchstatistik (Statnet AB via shl.se) och räknar fram Fantasy SHL-poäng
per spelare och match enligt den officiella regelboken (fantasy.shl.se/prizes-and-rules).
Verifierat 2026-09-28: 45 av 45 spelare i 5 matcher (inkl. övertid, straffar och målvakter)
gav exakt samma poäng per kategori som Fantasy SHL.

Används av
  * GitHub Actions (statnet.yml): skriver data/statnet.json bredvid webbsidan, eftersom shl.se
    inte tillåter anrop direkt från webbläsaren (CORS).
  * fantasy_rinken.py: /statnet.json direkt (live) när appen körs lokalt.

  python statnet_sync.py --out data/statnet.json      hämta och skriv
  python statnet_sync.py --selftest                   testa poängmotorn

Bara GET, högst ett anrop per sekund, bara öppen matchstatistik (inga lag, koder eller personuppgifter).
"""
import argparse
import datetime as dt
import json
import os
import ssl
import sys
import time
import urllib.request

SHL = "https://www.shl.se/api"
SCHEDULE = SHL + "/sports-v2/game-schedule?seasonUuid=ndcf81nlb3&seriesUuid=qQ9-bb0bzEWUk&gameTypeUuid=qQ9-af37Ti40B&gamePlace=all&played=all"
MIN_GAP_S = 1.1
DAYS_BACK = 9          # täcker en hel matchvecka bakåt
REFRESH_AFTER_H = 14   # färdiga matcher hämtas om tills statistiken är fastställd (natten efter matchen)

# ---------------------------------------------------------------- officiella regler (fantasy.shl.se)
RULES = {
    "skater": [
        ("TOI", "Istid", "1 p för 00:01–09:59, 2 p för 10:00–19:59, 3 p för 20:00+"),
        ("G", "Mål", "4 p per mål"),
        ("A", "Assist", "3 p per assist"),
        ("Hits", "Tacklingar", "1 p per två tacklingar"),
        ("BkS", "Blockerade skott", "1 p per två blockerade skott"),
        ("SOG", "Skott på mål", "1 p per fyra skott på mål"),
        ("FOW", "Tekningar", "+1 p per 3 vunna fler än förlorade, −1 p per 3 förlorade fler än vunna"),
        ("GWG", "Matchavgörande mål", "2 p bonus"),
        ("SHG", "Mål i numerärt underläge", "3 p bonus"),
        ("POP", "Plus", "+2 p per pluspoäng"),
        ("NEP", "Minus", "−2 p per minuspoäng"),
        ("PIM", "Utvisningar", "−1 p per två utvisningsminuter (max −5 per match)"),
    ],
    "goalie": [
        ("GPI", "Spelat match", "1 p"),
        ("TOI", "Istid över 40:00", "1 p för 40:01 eller mer"),
        ("W", "Vinst", "3 p vid vinst under full tid"),
        ("OTW", "Vinst efter förl./straffar", "2 p"),
        ("OTL", "Förlust efter förl./straffar", "1 p"),
        ("SVS", "Räddningar", "1 p per fem räddningar"),
        ("SO", "Hållen nolla", "4 p vid vinst utan insläppta mål (inkl. övertid)"),
        ("GA", "Insläppta mål", "−1 p per insläppt mål (vid förlust på straffar räknas det avgörande straffmålet)"),
        ("G", "Mål", "10 p per mål"),
        ("A", "Assist", "3 p per assist"),
        ("PIM", "Utvisningar", "−1 p per två utvisningsminuter (max −5 per match)"),
    ],
}


def secs(t):
    s = str(t or "")
    if ":" not in s:
        return 0
    m, sec = s.split(":")[:2]
    return int(m) * 60 + int(sec)


def pnum(e):
    v = str(e.get("period") or 0)
    return 5 if v == "shootout" else int(v) if v.isdigit() else 0


def at(e):
    """Sekunder sedan matchstart (period 1–3 à 20 min, övertid = period 4, straffar = period 5)."""
    return (pnum(e) - 1) * 1200 + secs(e.get("time"))


def skater_points(s, is_gwg):
    t = secs(s.get("TOI"))
    pts = {
        "TOI": (1 if t < 600 else 2 if t < 1200 else 3) if t > 0 else 0,
        "G": 4 * s.get("G", 0), "A": 3 * s.get("A", 0),
        "Hits": s.get("Hits", 0) // 2, "BkS": s.get("BkS", 0) // 2, "SOG": s.get("SOG", 0) // 4,
        "SHG": 3 * s.get("SHG", 0), "POP": 2 * s.get("POP", 0), "NEP": -2 * s.get("NEP", 0),
        "PIM": -min(5, s.get("PIM", 0) // 2),
    }
    d = s.get("FOW", 0) - s.get("FOL", 0)
    pts["FOW"] = d // 3 if d > 0 else -((-d) // 3)
    if is_gwg:
        pts["GWG"] = 2
    return {k: v for k, v in pts.items() if v}


def game_points(ps, pbp, home_code=None, away_code=None):
    """Poäng per spelare för en match ur player-stats + play-by-play. Returnerar en dict för datafilen."""
    names = {pid: n.get("fullName") for key in ("players", "goalkeepers")
             for side in ("homeTeamValue", "awayTeamValue") for pid, n in ((ps.get(key) or {}).get(side) or {}).items()}
    ev = sorted([e for e in pbp if e.get("type") in ("goal", "goalkeeper")],
                key=lambda e: (at(e), 0 if e.get("type") == "goalkeeper" and e.get("isEntering") else 1, e.get("eventId", 0)))
    heads = [e for e in pbp if isinstance(e.get("homeTeam"), dict)]
    head = heads[0] if heads else {}
    home_code = home_code or (head.get("homeTeam") or {}).get("teamCode")
    away_code = away_code or (head.get("awayTeam") or {}).get("teamCode")
    goals = [e for e in ev if e["type"] == "goal" and pnum(e) <= 4]          # straffmål räknas inte som mål
    rh = goals[-1]["homeTeam"]["score"] if goals else 0
    ra = goals[-1]["awayTeam"]["score"] if goals else 0
    fin = max(heads, key=lambda e: (pnum(e), at(e), (e["homeTeam"].get("score") or 0) + (e["awayTeam"].get("score") or 0))) if heads else {}
    hf = (fin.get("homeTeam") or {}).get("score", rh) or 0
    af = (fin.get("awayTeam") or {}).get("score", ra) or 0
    max_period = max([pnum(e) for e in pbp] or [0])
    ended = any(e.get("gameState") == "GameEnded" for e in pbp) or any(e.get("type") == "period" and e.get("finished") and pnum(e) >= 3 for e in pbp)
    ot, so = max_period >= 4, max_period >= 5
    winner = ("home" if hf > af else "away") if hf != af else None
    gwg = None
    if winner and rh != ra:  # avgjort på straffar: inget matchavgörande mål
        n, loser_final = 0, min(rh, ra)
        for g in goals:
            if g["eventTeam"]["place"] == winner:
                n += 1
                if n == loser_final + 1:
                    gwg = g
    end = at(goals[-1]) if (ot and goals and pnum(goals[-1]) == 4 and rh != ra) else (3900 if ot else 3600)
    if not ended:
        end = max([at(e) for e in pbp if e.get("time")] or [0])  # pågående match: istid hittills
    gk_toi, on = {}, {}
    for e in ev:
        if e["type"] != "goalkeeper":
            continue
        pid = str(e["player"]["playerId"])
        if e.get("isEntering"):
            on[pid] = at(e)
        elif pid in on:
            gk_toi[pid] = gk_toi.get(pid, 0) + at(e) - on.pop(pid)
    for pid, t0 in on.items():
        gk_toi[pid] = gk_toi.get(pid, 0) + max(0, end - t0)

    def in_net(place, t):
        cur = None
        for e in ev:
            if e["type"] != "goalkeeper" or e["eventTeam"]["place"] != place or at(e) > t:
                continue
            pid = str(e["player"]["playerId"])
            if e.get("isEntering"):
                cur = pid
            elif cur == pid and at(e) < t:  # ut samma sekund som målet: stod kvar i mål
                cur = None
        return cur

    win_gk = lose_gk = None
    if winner and ended:
        t_dec = at(gwg) if gwg else end
        win_gk = in_net(winner, t_dec)
        lose_gk = in_net("away" if winner == "home" else "home", t_dec)
    gwg_pid = str(gwg["player"]["playerId"]) if gwg else None
    # Målvakternas mål, assist och utvisningar finns inte i gkStats: räknas ur händelselistan.
    gk_g, gk_a, gk_pim = {}, {}, {}
    for g in goals:
        sc = str((g.get("player") or {}).get("playerId") or "")
        gk_g[sc] = gk_g.get(sc, 0) + 1
        for k in ("first", "second"):
            a = str(((g.get("assists") or {}).get(k) or {}).get("playerId") or "")
            if a:
                gk_a[a] = gk_a.get(a, 0) + 1
    for e in pbp:
        if e.get("type") == "penalty" and isinstance(e.get("player"), dict):
            v = e.get("variant") or {}
            mins = sum(int(v.get(k) or 0) for k in ("minorTime", "doubleMinorTime", "majorTime", "misconductTime", "gMTime", "mPTime") if str(v.get(k) or "0").isdigit())
            pid = str(e["player"].get("playerId") or "")
            gk_pim[pid] = gk_pim.get(pid, 0) + mins
    players = []
    for side, place in (("homeTeamValue", "home"), ("awayTeamValue", "away")):
        code = home_code if place == "home" else away_code
        for s in (ps.get("stats") or {}).get(side) or []:
            pid = str(s["info"]["playerId"])
            raw = {k: s.get(k, 0) for k in ("G", "A", "Hits", "BkS", "SOG", "FOW", "FOL", "PIM", "POP", "NEP", "SHG", "PPG")}
            raw["PM"] = s.get("+/-", 0)
            raw["TOI"] = secs(s.get("TOI"))
            raw["GWG"] = 1 if pid == gwg_pid else 0
            pts = skater_points(s, pid == gwg_pid)
            players.append({"id": pid, "name": names.get(pid), "team": code, "pos": s.get("POS"), "nr": s.get("NR"),
                            "raw": raw, "pts": pts, "total": sum(pts.values())})
        for s in (ps.get("gkStats") or {}).get(side) or []:
            pid = str(s["info"]["playerId"])
            t = gk_toi.get(pid, 0)
            ga = s.get("GA", 0)
            so_goal = 1 if (so and pid == lose_gk) else 0  # Fantasy SHL räknar det avgörande straffmålet som insläppt
            raw = {"TOI": t, "GA": ga + so_goal, "SVS": s.get("SVS", 0), "SOGA": s.get("SOGA", 0), "SOGOAL": so_goal,
                   "G": gk_g.get(pid, 0), "A": gk_a.get(pid, 0), "PIM": gk_pim.get(pid, 0)}
            pts = {}
            if t > 0:
                pts = {"GPI": 1, "TOI": 1 if t > 2400 else 0, "SVS": s.get("SVS", 0) // 5, "GA": -(ga + so_goal),
                       "G": 10 * raw["G"], "A": 3 * raw["A"], "PIM": -min(5, raw["PIM"] // 2)}
                if pid == win_gk:
                    pts["OTW" if ot else "W"] = 2 if ot else 3
                    if (ra if winner == "home" else rh) == 0:
                        pts["SO"] = 4
                if pid == lose_gk and ot:
                    pts["OTL"] = 1
                pts = {k: v for k, v in pts.items() if v}
            players.append({"id": pid, "name": names.get(pid), "team": code, "pos": "GK", "nr": s.get("NR"), "gk": True,
                            "raw": raw, "pts": pts, "total": sum(pts.values())})
    return {"gameId": head.get("gameId"), "home": home_code, "away": away_code, "hs": hf, "as": af,
            "ot": ot, "so": so, "ended": bool(ended), "players": players}


# ---------------------------------------------------------------- hämtning
class Fetcher:
    def __init__(self):
        self.last = 0.0
        self.calls = 0

    def __call__(self, url, tries=2):
        for attempt in range(tries):  # ett nytt försök vid tillfälliga nätverksfel
            w = self.last + MIN_GAP_S * (1 + 2 * attempt) - time.time()
            if w > 0:
                time.sleep(w)
            self.last = time.time()
            self.calls += 1
            try:
                req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "fantasy-shl-gameweek (privat, lasande)"})
                with urllib.request.urlopen(req, timeout=30, context=ssl.create_default_context()) as r:
                    return json.loads(r.read().decode("utf-8"))
            except (OSError, ValueError):
                if attempt == tries - 1:
                    raise


def build(fetch, prev=None, now=None, days_back=DAYS_BACK):
    """Bygger datafilen: alla matcher de senaste days_back dagarna som har startat. Oförändrade färdiga matcher återanvänds."""
    now = now or dt.datetime.now(dt.timezone.utc)
    prev_games = (prev or {}).get("games") or {}
    sched = fetch(SCHEDULE).get("gameInfo") or []
    out = {}
    for g in sched:
        try:
            start = dt.datetime.fromisoformat(str(g["rawStartDateTime"]).replace("Z", "+00:00"))
        except (KeyError, ValueError):
            continue
        if start > now or start < now - dt.timedelta(days=days_back) or g.get("state") == "pre-game":
            continue
        uuid = g["uuid"]
        old = next((v for v in prev_games.values() if v.get("uuid") == uuid), None)
        if old and old.get("ended") and g.get("state") == "post-game" and now - start > dt.timedelta(hours=REFRESH_AFTER_H):
            out[str(old.get("gameId"))] = old  # fastställd statistik: inget nytt anrop
            continue
        try:
            ps = fetch(f"{SHL}/gameday/player-stats/{uuid}")
            pbp = fetch(f"{SHL}/gameday/play-by-play/{uuid}")
            res = game_points(ps, pbp, (g.get("homeTeamInfo") or {}).get("code"), (g.get("awayTeamInfo") or {}).get("code"))
        except (OSError, ValueError, KeyError, TypeError):
            if old:  # tillfälligt fel: behåll senaste data för matchen, fortsätt med resten
                out[str(old.get("gameId"))] = old
            continue
        res.update({"uuid": uuid, "start": g["rawStartDateTime"], "state": g.get("state")})
        if res.get("gameId") is not None:
            out[str(res["gameId"])] = res
    return {"version": 1, "source": "Statnet AB via shl.se", "updated": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
            "live": any(v.get("state") not in ("post-game", "pre-game") for v in out.values()),
            "rules": RULES, "games": out}


# ---------------------------------------------------------------- självtest
def selftest():
    def ev(t, period, time_, place, pid, **kw):
        d = {"type": t, "period": period, "time": time_, "eventTeam": {"place": place}, "player": {"playerId": pid},
             "homeTeam": {"teamCode": "AAA", "score": kw.pop("hs", 0)}, "awayTeam": {"teamCode": "BBB", "score": kw.pop("as_", 0)},
             "gameId": 1, "gameState": "GameEnded"}
        d.update(kw)
        return d

    def sk(pid, **kw):
        s = {"NR": 1, "POS": "CE", "G": 0, "A": 0, "SHG": 0, "PPG": 0, "PIM": 0, "SOG": 0, "NEP": 0, "POP": 0, "+/-": 0, "TOI": "15:00",
             "Hits": 0, "FOW": 0, "FOL": 0, "BkS": 0, "info": {"playerId": pid}}
        s.update(kw)
        return s

    ps = {"players": {"homeTeamValue": {"1": {"fullName": "A Anfall"}, "2": {"fullName": "B Back"}}, "awayTeamValue": {"3": {"fullName": "C Center"}}},
          "goalkeepers": {"homeTeamValue": {"10": {"fullName": "H Mv"}}, "awayTeamValue": {"20": {"fullName": "B Mv"}, "21": {"fullName": "B Reserv"}}},
          "stats": {"homeTeamValue": [sk("1", G=2, A=1, SOG=5, Hits=3, BkS=1, FOW=10, FOL=3, POP=2, TOI="20:00"),
                                      sk("2", PIM=14, NEP=1, TOI="09:59", FOW=1, FOL=5)],
                    "awayTeamValue": [sk("3", G=1, SHG=1, TOI="00:00")]},
          "gkStats": {"homeTeamValue": [{"GA": 1, "SVS": 27, "SOGA": 28, "info": {"playerId": "10"}}],
                      "awayTeamValue": [{"GA": 2, "SVS": 9, "SOGA": 11, "info": {"playerId": "20"}}, {"GA": 0, "SVS": 0, "info": {"playerId": "21"}}]}}
    # Hemmalaget vinner 2–1 i övertid; målvakterna går ut samma sekund som övertidsmålet (som hos Statnet).
    pbp = [ev("goalkeeper", 1, "00:00", "home", "10", isEntering=True), ev("goalkeeper", 1, "00:00", "away", "20", isEntering=True),
           ev("goal", 2, "05:00", "away", "3", as_=1), ev("goal", 3, "10:00", "home", "1", hs=1, as_=1),
           ev("goal", "4", "01:52", "home", "1", hs=2, as_=1),
           ev("goalkeeper", "4", "01:52", "home", "10", isEntering=False), ev("goalkeeper", "4", "01:52", "away", "20", isEntering=False)]
    r = game_points(ps, list(reversed(pbp)))
    by = {p["id"]: p for p in r["players"]}
    res = []

    def t(name, got, want):
        res.append((got == want, name, "" if got == want else f"fick {got!r}, väntade {want!r}"))

    t("övertid upptäcks, slutresultat 2–1", (r["ot"], r["hs"], r["as"]), (True, 2, 1))
    t("anfallare: istid 20:00=3, 2 mål, assist, skott 5→1, tacklingar 3→1, block 1→0, tekningar +7→2, plus 2→4, GWG",
      by["1"]["pts"], {"TOI": 3, "G": 8, "A": 3, "SOG": 1, "Hits": 1, "FOW": 2, "POP": 4, "GWG": 2})
    t("back: istid 09:59=1, utvisningar max −5, minus −2, tekningar −4→−1", by["2"]["pts"], {"TOI": 1, "PIM": -5, "NEP": -2, "FOW": -1})
    t("spelare utan istid: inga istidspoäng, mål + SHG räknas", by["3"]["pts"], {"G": 4, "SHG": 3})
    t("vinnande målvakt i övertid: spelat, 40:01+, OTW, räddningar 27→5, insläppt −1", by["10"]["pts"], {"GPI": 1, "TOI": 1, "OTW": 2, "SVS": 5, "GA": -1})
    t("förlorande målvakt i övertid: OTL", by["20"]["pts"], {"GPI": 1, "TOI": 1, "OTL": 1, "SVS": 1, "GA": -2})
    t("reservmålvakt som inte spelat: 0 p", by["21"]["total"], 0)
    # Straffläggning 2–1 till borta efter 1–1; hemmamålvaktens assist och 2 min utvisning (verkligt fall: FHC–FBK 23008/23016).
    ps2 = {"players": {}, "goalkeepers": {"homeTeamValue": {"10": {"fullName": "H Mv"}}, "awayTeamValue": {"20": {"fullName": "B Mv"}}},
           "stats": {"homeTeamValue": [sk("1", G=1)], "awayTeamValue": [sk("3", G=1)]},
           "gkStats": {"homeTeamValue": [{"GA": 1, "SVS": 19, "SOGA": 20, "info": {"playerId": "10"}}],
                       "awayTeamValue": [{"GA": 1, "SVS": 31, "SOGA": 32, "info": {"playerId": "20"}}]}}
    pbp2 = [ev("goalkeeper", 1, "00:00", "home", "10", isEntering=True), ev("goalkeeper", 1, "00:00", "away", "20", isEntering=True),
            ev("goal", 1, "05:00", "home", "1", hs=1, assists={"first": {"playerId": "10"}}),
            ev("penalty", 2, "03:00", "home", "10", variant={"minorTime": "2", "doubleMinorTime": "0", "majorTime": "0"}),
            ev("goal", 3, "10:00", "away", "3", hs=1, as_=1),
            ev("goal", "shootout", "00:00", "away", "3", hs=1, as_=2)]
    r2 = game_points(ps2, pbp2)
    by2 = {p["id"]: p for p in r2["players"]}
    t("straffförlust: det avgörande straffmålet räknas som insläppt (GA −2)", by2["10"]["pts"].get("GA"), -2)
    t("målvakt: assist 3 p och 2 min utvisning −1 p", (by2["10"]["pts"].get("A"), by2["10"]["pts"].get("PIM")), (3, -1))
    t("straffvinnare: bara insläppta under matchen (GA −1), OTW", (by2["20"]["pts"].get("GA"), by2["20"]["pts"].get("OTW")), (-1, 2))
    for ok, name, detail in res:
        print(("OK   " if ok else "FEL  ") + name + (f" – {detail}" if detail else ""))
    bad = sum(not x[0] for x in res)
    print(f"\n{len(res) - bad}/{len(res)} OK")
    return 1 if bad else 0


def main():
    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass
    ap = argparse.ArgumentParser(description="Statnet -> Fantasy SHL-poäng")
    ap.add_argument("--out", default="data/statnet.json")
    ap.add_argument("--days", type=int, default=DAYS_BACK)
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(selftest())
    prev = None
    if os.path.exists(a.out):
        try:
            prev = json.load(open(a.out, encoding="utf-8"))
        except ValueError:
            prev = None
    f = Fetcher()
    data = build(f, prev, days_back=a.days)
    os.makedirs(os.path.dirname(a.out) or ".", exist_ok=True)
    new = json.dumps(data, ensure_ascii=False, separators=(",", ":"))
    old_games = json.dumps((prev or {}).get("games"), ensure_ascii=False, separators=(",", ":")) if prev else None
    if old_games == json.dumps(data["games"], ensure_ascii=False, separators=(",", ":")):
        print(f"Oförändrat ({len(data['games'])} matcher, {f.calls} anrop).")
        return
    with open(a.out, "w", encoding="utf-8") as fh:
        fh.write(new)
    print(f"Skrev {a.out}: {len(data['games'])} matcher, live={data['live']}, {f.calls} anrop.")


if __name__ == "__main__":
    main()
