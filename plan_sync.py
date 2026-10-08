"""Fantasy Rinken – planeringsdata (fullversionen, 2.2.0).

Läser SHL:s öppna matchdata (Statnet via shl.se, samma källa som statnet_sync.py) och skriver:
  data/plan-cache.json  kompakta skott och spelarrader per färdig match (sparas, hämtas en gång per match)
  data/season.json      säsongs- och formvärden per lag och spelare: Corsi, Fenwick, xG, PDO, GSAx, fantasypoäng
  data/model.json       xG-tabell, lagstyrka och sannolikheter för kommande matcher (egen modell)
  data/odds.json        (bara med --odds och miljövariabeln ODDS_API_KEY) spelbolagens sannolikheter

Regler: bara GET, högst ett anrop per sekund mot shl.se, bara Pythons standardbibliotek, inga nycklar i koden.
Spelare på isen anges bara vid mål hos Statnet, så Corsi/xG "på isen" räknas inte (se fantasy-shl-api-rapport.md).

  python plan_sync.py                  hämta nya matcher, skriv season.json och model.json
  python plan_sync.py --odds           hämta odds (kräver ODDS_API_KEY) och skriv odds.json
  python plan_sync.py --selftest       självtest utan nät
"""
import argparse
import datetime as dt
import json
import math
import os
import ssl
import sys
import unicodedata
import urllib.parse
import urllib.request

import statnet_sync as sn

VERSION = 1
MAX_NEW = 160            # högst så många nya matcher per körning (resten tas nästa gång)
REFRESH_AFTER_H = 14     # färdiga matcher hämtas om tills statistiken är fastställd
HALF_LIFE_D = 60         # äldre matcher väger mindre i lagstyrkan
PRIOR_GAMES = 5          # lag med få matcher dras mot ligasnittet
XG_WEIGHT = 0.7          # lagstyrka: 70 % xG, 30 % faktiska mål
HORIZON_DAYS = 45        # matcher så här långt fram får sannolikheter (Fantasy SHL:s omgångar har flera SHL-omgångar)
REBOUND_S = 3            # skott inom 3 s efter lagets förra skott = retur
DIST_B = [3, 6, 9, 12, 15, 20, 30]   # meter
ANG_B = [20, 40, 60]                 # grader från mittlinjen
ODDS_BASE = "https://api.the-odds-api.com/v4"


def other(place):
    return "away" if place == "home" else "home"


def num(v, k):
    s = str((v or {}).get(k) or "0")
    return int(s) if s.isdigit() else 0


# ---------------------------------------------------------------- spelstyrka och målvakter
def timeline(pbp):
    """Utvisningar (med PP-mål som avbryter mindre straff) och målvakter i mål. Returnerar state(place, t) och ev_secs."""
    pens = []
    for e in pbp:
        if e.get("type") != "penalty":
            continue
        place = (e.get("eventTeam") or {}).get("place")
        if place not in ("home", "away"):
            continue
        v, t = e.get("variant") or {}, sn.at(e)
        mi, dm, mj = num(v, "minorTime") + num(v, "benchTime"), num(v, "doubleMinorTime"), num(v, "majorTime") + num(v, "mPTime")
        if mi:
            pens.append([place, t, t + 60 * mi, True])
        if dm:
            pens.append([place, t, t + 120, True])
            pens.append([place, t + 120, t + 240, True])
        if mj:
            pens.append([place, t, t + 60 * mj, False])

    def count(place, t):
        return min(2, sum(1 for p in pens if p[0] == place and p[1] <= t < p[2]))

    for g in sorted((e for e in pbp if e.get("type") == "goal" and sn.pnum(e) <= 4), key=sn.at):
        t, sc = sn.at(g), (g.get("eventTeam") or {}).get("place")
        if sc not in ("home", "away"):
            continue
        if count(other(sc), t) > count(sc, t):
            act = [p for p in pens if p[0] == other(sc) and p[3] and p[1] <= t < p[2]]
            if act:
                min(act, key=lambda p: p[2])[2] = t
    gk = {"home": [], "away": []}
    on = {}
    for e in sorted((e for e in pbp if e.get("type") == "goalkeeper"), key=lambda e: (sn.at(e), 0 if e.get("isEntering") else 1)):
        place = (e.get("eventTeam") or {}).get("place")
        pid = str((e.get("player") or {}).get("playerId") or "")
        if place not in gk or not pid:
            continue
        if e.get("isEntering"):
            on[(place, pid)] = sn.at(e)
        elif (place, pid) in on:
            gk[place].append([pid, on.pop((place, pid)), sn.at(e)])
    end = max([sn.at(e) for e in pbp if e.get("time")] or [3600])
    for (place, pid), t0 in on.items():
        gk[place].append([pid, t0, max(end, t0) + 1])

    def goalie(place, t):
        if not gk[place]:
            return "?"  # okänt: anta att målvakten står i mål
        for pid, t0, t1 in gk[place]:
            if t0 <= t < t1:
                return pid
        return None

    def state(place, t):
        """Spelstyrka för laget som skjuter vid tiden t: EV (lika många), PP, SH, EN (motståndarens mål tomt), OT."""
        if goalie(other(place), t) is None:
            return "EN"
        if t >= 3600:
            return "OT"
        own, opp = count(place, t), count(other(place), t)
        return "EV" if own == opp else ("PP" if own < opp else "SH")

    ev_secs = sum(1 for t in range(0, min(end, 3600)) if count("home", t) == count("away", t)
                  and goalie("home", t) is not None and goalie("away", t) is not None)
    return state, goalie, gk, ev_secs


def parse_game(g, ps, pbp):
    """En färdig match -> kompakt post för cachen."""
    home, away = (g.get("homeTeamInfo") or {}).get("code"), (g.get("awayTeamInfo") or {}).get("code")
    pts = sn.game_points(ps, pbp, home, away)
    state, goalie, gk, ev_secs = timeline(pbp)
    shots = []
    for e in pbp:
        typ = e.get("type")
        if typ not in ("shot", "goal") or e.get("isPenaltyShot") or sn.pnum(e) >= 5:
            continue
        place = (e.get("eventTeam") or {}).get("place")
        if place not in ("home", "away"):
            continue
        sec = e.get("goalSection")
        res = "G" if typ == "goal" else ("B" if sec == -3 else "M" if sec == 0 else "S")
        t = sn.at(e)
        st = state(place, t)
        if typ == "goal":
            st = state(place, max(t - 1, 0))  # PP-målet avslutar utvisningen samma sekund: styrkan strax före gäller
            gs = str(e.get("goalStatus") or "").upper()  # Statnets egen märkning går före
            if e.get("isEmptyNetGoal"):
                st = "EN"
            elif gs.startswith("PP"):
                st = "PP"
            elif gs.startswith("SH"):
                st = "SH"
            elif gs.startswith("EQ") and st in ("PP", "SH"):
                st = "EV"
        gd = goalie(other(place), t)
        shots.append([0 if place == "home" else 1, str((e.get("player") or {}).get("playerId") or ""),
                      e.get("locationX"), e.get("locationY"), res, st, t, gd if gd not in (None, "?") else ""])
    shots.sort(key=lambda s: s[6])
    pl = [[p["id"], p.get("name") or "", p.get("team") or "", p.get("pos") or "", (p.get("raw") or {}).get("TOI", 0),
           p.get("total", 0), (p.get("raw") or {}).get("G", 0), (p.get("raw") or {}).get("A", 0)] for p in pts["players"]]
    return {"uuid": g.get("uuid"), "id": pts.get("gameId"), "start": g.get("rawStartDateTime"), "round": g.get("roundNumber"),
            "home": home, "away": away, "hs": (g.get("homeTeamInfo") or {}).get("score"), "as": (g.get("awayTeamInfo") or {}).get("score"),
            "ot": bool(g.get("overtime")), "so": bool(g.get("shootout")), "ev": ev_secs,
            "gk": [[0 if pl_ == "home" else 1] + iv for pl_ in ("home", "away") for iv in gk[pl_]],
            "shots": shots, "pl": pl, "fetched": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}


def build_cache(fetch, prev, now=None):
    now = now or dt.datetime.now(dt.timezone.utc)
    sched = fetch(sn.SCHEDULE).get("gameInfo") or []
    old = {g["uuid"]: g for g in (prev or {}).get("games", []) if g.get("uuid")}
    out, new = [], 0
    for g in sched:
        if g.get("state") != "post-game":
            continue
        try:
            start = dt.datetime.fromisoformat(str(g["rawStartDateTime"]).replace("Z", "+00:00"))
        except (KeyError, ValueError):
            continue
        o = old.get(g.get("uuid"))
        fetched = dt.datetime.fromisoformat(o["fetched"].replace("Z", "+00:00")) if o and o.get("fetched") else None
        if o and fetched and fetched - start > dt.timedelta(hours=REFRESH_AFTER_H):
            out.append(o)  # fastställd: inget nytt anrop
            continue
        if new >= MAX_NEW:
            if o:
                out.append(o)
            continue
        try:
            ps = fetch(f"{sn.SHL}/gameday/player-stats/{g['uuid']}")
            pbp = fetch(f"{sn.SHL}/gameday/play-by-play/{g['uuid']}")
            out.append(parse_game(g, ps, pbp))
            new += 1
        except (OSError, ValueError, KeyError, TypeError):
            if o:
                out.append(o)
    out.sort(key=lambda g: g.get("start") or "")
    return {"version": VERSION, "games": out}, sched, new


# ---------------------------------------------------------------- xG
def geo(x, y):
    x, y = float(x or 0), float(y or 0)
    x = max(x, 0.5)  # bakom målet räknas som från mållinjen
    return math.hypot(x, y) / 10.0, math.degrees(math.atan2(abs(y), x))


def bucket(d, a):
    di = next((i for i, b in enumerate(DIST_B) if d < b), len(DIST_B))
    ai = next((i for i, b in enumerate(ANG_B) if a < b), len(ANG_B))
    return di, ai


def mark_rebounds(shots):
    """Retur = oblockerat skott inom REBOUND_S sekunder efter samma lags förra skottförsök."""
    last = {0: -99, 1: -99}
    out = []
    for s in shots:
        rb = s[4] != "B" and s[6] - last[s[0]] <= REBOUND_S
        last[s[0]] = s[6]
        out.append(rb)
    return out


def fit_xg(games):
    """Målprocent per avstånd × vinkel för oblockerade skott, dragen mot avståndssnittet. Plus faktorer för PP, SH och retur."""
    nd, ad = len(DIST_B) + 1, len(ANG_B) + 1
    n = [[0] * ad for _ in range(nd)]
    gl = [[0] * ad for _ in range(nd)]
    en_n = en_g = 0
    rows = []
    for g in games:
        for s, rb in zip(g["shots"], mark_rebounds(g["shots"])):
            if s[4] == "B":
                continue
            if s[5] == "EN":
                en_n += 1
                en_g += s[4] == "G"
                continue
            di, ai = bucket(*geo(s[2], s[3]))
            n[di][ai] += 1
            gl[di][ai] += s[4] == "G"
            rows.append((di, ai, s[5], rb, s[4] == "G"))
    tot_n, tot_g = sum(map(sum, n)), sum(map(sum, gl))
    overall = (tot_g + 1) / (tot_n + 12)
    k = 30.0
    base = []
    for di in range(nd):
        dn, dg = sum(n[di]), sum(gl[di])
        prior = (dg + k * overall) / (dn + k)
        base.append([round((gl[di][ai] + k * prior) / (n[di][ai] + k), 4) for ai in range(ad)])

    def factor(pred):
        g_ = sum(1 for r in rows if pred(r) and r[4])
        x_ = sum(base[r[0]][r[1]] for r in rows if pred(r))
        return round((g_ + 20) / (x_ + 20), 3) if x_ else 1.0  # dras mot 1,0 när det finns få skott

    mult = {"PP": factor(lambda r: r[2] == "PP"), "SH": factor(lambda r: r[2] == "SH"), "RB": factor(lambda r: r[3])}
    return {"db": DIST_B, "ab": ANG_B, "base": base, "mult": mult, "en": round((en_g + 5 * 0.4) / (en_n + 5), 3),
            "n": tot_n + en_n, "goals": tot_g + en_g}


def xg_of(s, rb, t):
    if s[4] == "B":
        return 0.0
    if s[5] == "EN":
        return t["en"]
    di, ai = bucket(*geo(s[2], s[3]))
    v = t["base"][min(di, len(t["base"]) - 1)][min(ai, len(t["base"][0]) - 1)]
    if s[5] in ("PP", "SH"):
        v *= t["mult"].get(s[5], 1)
    if rb:
        v *= t["mult"].get("RB", 1)
    return min(v, 0.95)


# ---------------------------------------------------------------- säsongsvärden
def team_block(rows):
    """rows: lista med per-match-dictar för ett lag -> CF%, FF%, xGF%, per 60 (5 mot 5) och PDO."""
    s = {k: sum(r[k] for r in rows) for k in ("cf", "ca", "ff", "fa", "sf", "sa", "gf", "ga", "xgf", "xga", "ev",
                                               "cf_a", "xgf_a", "xga_a", "gf_a", "ga_a")}
    ev_h = s["ev"] / 3600 or 1e-9
    pct = lambda a, b: round(100 * a / (a + b), 1) if a + b else None
    return {"gp": len(rows), "cf": pct(s["cf"], s["ca"]), "ff": pct(s["ff"], s["fa"]), "xgf": pct(s["xgf"], s["xga"]),
            "xgf60": round(s["xgf"] / ev_h, 2), "xga60": round(s["xga"] / ev_h, 2), "sf60": round(s["sf"] / ev_h, 1),
            "cf60": round(s["cf"] / ev_h, 1),
            "pdo": round(100 * ((s["gf"] / s["sf"] if s["sf"] else 0) + (1 - (s["ga"] / s["sa"] if s["sa"] else 0))), 1) if s["sf"] and s["sa"] else None,
            "gfg": round(s["gf_a"] / len(rows), 2) if rows else None, "gag": round(s["ga_a"] / len(rows), 2) if rows else None,
            "xgfg": round(s["xgf_a"] / len(rows), 2) if rows else None, "xgag": round(s["xga_a"] / len(rows), 2) if rows else None}


def season(games, xgt):
    teams, players, goalies = {}, {}, {}
    for g in games:
        codes = [g["home"], g["away"]]
        tr = [dict.fromkeys(("cf", "ca", "ff", "fa", "sf", "sa", "gf", "ga", "xgf", "xga", "cf_a", "xgf_a", "xga_a", "gf_a", "ga_a"), 0.0) for _ in (0, 1)]
        for side in (0, 1):
            tr[side]["ev"] = g.get("ev") or 0
            tr[side]["gf_a"] = (g["hs"] if side == 0 else g["as"]) or 0
            tr[side]["ga_a"] = (g["as"] if side == 0 else g["hs"]) or 0
            if g.get("so") and tr[side]["gf_a"] > tr[side]["ga_a"]:
                tr[side]["gf_a"] -= 1  # straffläggningens "mål" räknas inte
            elif g.get("so") and tr[side]["ga_a"] > tr[side]["gf_a"]:
                tr[side]["ga_a"] -= 1
        ind = {}
        for s, rb in zip(g["shots"], mark_rebounds(g["shots"])):
            side, opp, x = s[0], 1 - s[0], xg_of(s, rb, xgt)
            tr[side]["cf_a"] += 1
            tr[side]["xgf_a"] += x
            tr[opp]["xga_a"] += x
            if s[5] == "EV":
                tr[side]["cf"] += 1; tr[opp]["ca"] += 1
                if s[4] != "B":
                    tr[side]["ff"] += 1; tr[opp]["fa"] += 1
                if s[4] in ("S", "G"):
                    tr[side]["sf"] += 1; tr[opp]["sa"] += 1
                if s[4] == "G":
                    tr[side]["gf"] += 1; tr[opp]["ga"] += 1
                tr[side]["xgf"] += x; tr[opp]["xga"] += x
            if s[1]:
                d = ind.setdefault(s[1], {"icf": 0, "iff": 0, "isog": 0, "ixg": 0.0})
                d["icf"] += 1
                d["iff"] += s[4] != "B"
                d["isog"] += s[4] in ("S", "G")
                d["ixg"] += x
            if s[7] and s[5] != "EN":  # målvakten som stod i mål
                gd = goalies.setdefault(s[7], {"sa": 0, "ga": 0, "xga": 0.0, "gp": set()})
                gd["gp"].add(g["uuid"])
                if s[4] in ("S", "G"):
                    gd["sa"] += 1
                gd["ga"] += s[4] == "G"
                gd["xga"] += x
        for side in (0, 1):
            teams.setdefault(codes[side], []).append(tr[side])
        for pid, name, team, pos, toi, total, gl, a in g["pl"]:
            p = players.setdefault(pid, {"id": pid, "n": name, "t": team, "p": pos, "games": []})
            p["n"], p["t"], p["p"] = name or p["n"], team or p["t"], pos or p["p"]
            if pos == "GK" and not toi:
                continue  # reservmålvakt utan istid
            d = ind.get(pid, {"icf": 0, "iff": 0, "isog": 0, "ixg": 0.0})
            p["games"].append({"toi": toi, "pts": total, "g": gl, "a": a, **d})
    out_t = {c: {"s": team_block(r), "f": team_block(r[-5:])} for c, r in teams.items()}

    def pblock(gs):
        toi = sum(x["toi"] for x in gs)
        h = toi / 3600 or 1e-9
        icf, ixg, gl = sum(x["icf"] for x in gs), sum(x["ixg"] for x in gs), sum(x["g"] for x in gs)
        return {"gp": len(gs), "toi": toi, "pts": sum(x["pts"] for x in gs), "ppg": round(sum(x["pts"] for x in gs) / len(gs), 2) if gs else 0,
                "g": gl, "a": sum(x["a"] for x in gs), "icf": icf, "isog": sum(x["isog"] for x in gs), "ixg": round(ixg, 2),
                "icf60": round(icf / h, 1) if toi else None, "ixg60": round(ixg / h, 2) if toi else None,
                "ixgg": round(ixg / len(gs), 3) if gs else None, "gax": round(gl - ixg, 2)}
    out_p = []
    for p in players.values():
        if not p["games"]:
            continue
        row = {"id": p["id"], "n": p["n"], "t": p["t"], "p": p["p"], "s": pblock(p["games"]), "f": pblock(p["games"][-5:])}
        if p["p"] == "GK" and p["id"] in goalies:
            gd = goalies[p["id"]]
            row["gk"] = {"sa": gd["sa"], "ga": gd["ga"], "xga": round(gd["xga"], 2),
                         "sv": round(100 * (1 - gd["ga"] / gd["sa"]), 1) if gd["sa"] else None, "gsax": round(gd["xga"] - gd["ga"], 2)}
        out_p.append(row)
    out_p.sort(key=lambda r: -r["s"]["pts"])
    return out_t, out_p


# ---------------------------------------------------------------- matchmodell
def poisson(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k)


def match_probs(lh, la, maxg=12):
    """Sannolikheter under full tid (Poisson) + förlängning/straffar fördelat efter styrka."""
    ph = [poisson(i, lh) for i in range(maxg + 1)]
    pa = [poisson(i, la) for i in range(maxg + 1)]
    pH = sum(ph[i] * pa[j] for i in range(maxg + 1) for j in range(maxg + 1) if i > j)
    pA = sum(ph[i] * pa[j] for i in range(maxg + 1) for j in range(maxg + 1) if j > i)
    pD = max(0.0, 1 - pH - pA)
    oth = 0.5 + 0.25 * (lh - la) / (lh + la) if lh + la else 0.5
    p00 = ph[0] * pa[0]
    return {"pH": round(pH, 4), "pA": round(pA, 4), "pOT": round(pD, 4), "otH": round(oth, 3),
            "soH": round(pa[0] * (1 - ph[0]) + p00 * oth, 4), "soA": round(ph[0] * (1 - pa[0]) + p00 * (1 - oth), 4)}


def model(games, sched, xgt, tstats, now=None):
    now = now or dt.datetime.now(dt.timezone.utc)
    n = len(games)
    tot_g = sum(((g["hs"] or 0) + (g["as"] or 0) - (1 if g.get("so") else 0)) for g in games)
    tot_x = sum(xg_of(s, rb, xgt) for g in games for s, rb in zip(g["shots"], mark_rebounds(g["shots"])))
    mu = tot_g / (2 * n) if n else 2.8
    scale = tot_g / tot_x if tot_x else 1.0
    hg = sum((g["hs"] or 0) for g in games)
    ag = sum((g["as"] or 0) for g in games)
    home = max(0.9, min(1.25, (hg + 20 * 1.05) / (ag + 20))) if n else 1.05
    mu_s = (sum(len([s for s in g["shots"] if s[4] in ("S", "G")]) for g in games) / (2 * n)) if n else 28.0
    acc = {}
    for g in games:
        try:
            age = (now - dt.datetime.fromisoformat(g["start"].replace("Z", "+00:00"))).days
        except (KeyError, ValueError, AttributeError):
            age = 0
        w = 0.5 ** (max(age, 0) / HALF_LIFE_D)
        xs = [0.0, 0.0]
        sog = [0, 0]
        for s, rb in zip(g["shots"], mark_rebounds(g["shots"])):
            xs[s[0]] += xg_of(s, rb, xgt) * scale
            sog[s[0]] += s[4] in ("S", "G")
        gls = [(g["hs"] or 0), (g["as"] or 0)]
        if g.get("so"):
            gls[0 if gls[0] > gls[1] else 1] -= 1
        for side, code in ((0, g["home"]), (1, g["away"])):
            a = acc.setdefault(code, {"w": 0.0, "f": 0.0, "a": 0.0, "sf": 0.0, "sa": 0.0})
            a["w"] += w
            a["f"] += w * (XG_WEIGHT * xs[side] + (1 - XG_WEIGHT) * gls[side])
            a["a"] += w * (XG_WEIGHT * xs[1 - side] + (1 - XG_WEIGHT) * gls[1 - side])
            a["sf"] += w * sog[side]
            a["sa"] += w * sog[1 - side]
    rate = {}
    for code, a in acc.items():
        k = PRIOR_GAMES
        rate[code] = {"att": round((a["f"] + k * mu) / (a["w"] + k) / mu, 3), "def": round((a["a"] + k * mu) / (a["w"] + k) / mu, 3),
                      "sf": round((a["sf"] + k * mu_s) / (a["w"] + k) / mu_s, 3), "sa": round((a["sa"] + k * mu_s) / (a["w"] + k) / mu_s, 3)}
    up = []
    sq = math.sqrt(home)
    for g in sched:
        if g.get("state") == "post-game":
            continue
        try:
            start = dt.datetime.fromisoformat(str(g.get("rawStartDateTime")).replace("Z", "+00:00"))
        except ValueError:
            continue
        if not (now - dt.timedelta(hours=6) <= start <= now + dt.timedelta(days=HORIZON_DAYS)):
            continue
        h, a_ = (g.get("homeTeamInfo") or {}).get("code"), (g.get("awayTeamInfo") or {}).get("code")
        rh, ra = rate.get(h, {"att": 1, "def": 1, "sf": 1, "sa": 1}), rate.get(a_, {"att": 1, "def": 1, "sf": 1, "sa": 1})
        lh, la = mu * rh["att"] * ra["def"] * sq, mu * ra["att"] * rh["def"] / sq
        row = {"start": g.get("rawStartDateTime"), "round": g.get("roundNumber"), "home": h, "away": a_,
               "lH": round(lh, 3), "lA": round(la, 3), "sH": round(mu_s * rh["sf"] * ra["sa"], 1), "sA": round(mu_s * ra["sf"] * rh["sa"], 1)}
        row.update(match_probs(lh, la))
        up.append(row)
    return {"version": VERSION, "updated": now.strftime("%Y-%m-%dT%H:%M:%SZ"), "games": n, "mu": round(mu, 3), "muShots": round(mu_s, 1),
            "home": round(home, 3), "xgScale": round(scale, 3), "xgTable": xgt, "teams": rate, "upcoming": up}


# ---------------------------------------------------------------- odds (valfritt, nyckel bara via miljövariabel)
def implied(prices):
    """Decimalodds -> sannolikheter med spelbolagets marginal borttagen (proportionellt)."""
    inv = [1.0 / p for p in prices if p and p > 1]
    if len(inv) != len(prices):
        return None
    s = sum(inv)
    return [v / s for v in inv]


def poisson_total(point, p_over):
    """Väntat antal mål ur över/under-oddset (Poisson på totalen)."""
    lo, hi = 0.5, 12.0
    for _ in range(60):
        mid = (lo + hi) / 2
        over = 1 - sum(poisson(k, mid) for k in range(int(math.floor(point)) + 1))
        lo, hi = (mid, hi) if over < p_over else (lo, mid)
    return round((lo + hi) / 2, 2)


def norm_name(s):
    """Gemener, utan accenter (Örebro = Orebro) och utan mellanslag och tecken."""
    s = unicodedata.normalize("NFKD", (s or "").lower())
    return "".join(ch for ch in s if ch.isalnum() and not unicodedata.combining(ch))


def match_team(name, teams):
    """Oddstjänstens lagnamn -> SHL-kod via shl.se:s namn (lång, kort, full)."""
    n = norm_name(name)
    best = None
    for code, names in teams.items():
        for v in names:
            v = norm_name(v)
            if v and (v == n or v in n or n in v):
                if not best or len(v) > best[1]:
                    best = (code, len(v))
    return best[0] if best else None


def parse_odds(events, teams):
    out = []
    for ev in events or []:
        h, a = match_team(ev.get("home_team"), teams), match_team(ev.get("away_team"), teams)
        if not h or not a:
            continue
        p3, p2, tot, nb = [], [], [], 0
        for bk in ev.get("bookmakers") or []:
            nb += 1
            for m in bk.get("markets") or []:
                oc = {o.get("name"): o for o in m.get("outcomes") or []}
                if m.get("key") == "h2h":
                    hn, an = ev.get("home_team"), ev.get("away_team")
                    if "Draw" in oc and hn in oc and an in oc:
                        p = implied([oc[hn].get("price"), oc["Draw"].get("price"), oc[an].get("price")])
                        if p:
                            p3.append(p)
                    elif hn in oc and an in oc:
                        p = implied([oc[hn].get("price"), oc[an].get("price")])
                        if p:
                            p2.append(p)
                elif m.get("key") == "totals" and "Over" in oc and "Under" in oc and oc["Over"].get("point") is not None:
                    p = implied([oc["Over"].get("price"), oc["Under"].get("price")])
                    if p:
                        tot.append(poisson_total(float(oc["Over"]["point"]), p[0]))
        if not (p3 or p2):
            continue
        row = {"start": ev.get("commence_time"), "home": h, "away": a, "books": nb}
        avg = lambda L, i: round(sum(x[i] for x in L) / len(L), 4)
        if p3:
            row.update({"pH": avg(p3, 0), "pOT": avg(p3, 1), "pA": avg(p3, 2)})
        if p2:
            row.update({"winH": avg(p2, 0), "winA": avg(p2, 1)})
        if tot:
            row["total"] = round(sum(tot) / len(tot), 2)
        out.append(row)
    return out


def odds_get(path, params, key):
    q = dict(params, apiKey=key)
    req = urllib.request.Request(ODDS_BASE + path + "?" + urllib.parse.urlencode(q), headers={"Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=30, context=ssl.create_default_context()) as r:
        return json.loads(r.read().decode("utf-8"))


def fetch_odds(key, teams):
    """Använder bara en sport som oddstjänsten själv listar som SHL. Annars available=false."""
    sports = odds_get("/sports", {}, key)
    cand = [s for s in sports if "hockey" in (s.get("group", "") + s.get("key", "")).lower()
            and ("shl" in (s.get("title", "") + s.get("description", "")).lower() or "sweden" in s.get("key", "").lower())]
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    if not cand:
        return {"version": VERSION, "available": False, "updated": now, "reason": "oddstjänsten listar ingen SHL"}
    sport = cand[0]["key"]
    events = odds_get(f"/sports/{sport}/odds", {"regions": "eu", "markets": "h2h,totals", "oddsFormat": "decimal"}, key)
    return {"version": VERSION, "available": True, "updated": now, "sport": sport, "games": parse_odds(events, teams)}


# ---------------------------------------------------------------- självtest
def selftest():
    res = []

    def t(name, got, want):
        res.append((got == want, name, "" if got == want else f"fick {got!r}, väntade {want!r}"))

    def ev(typ, period, time_, place, pid="1", **kw):
        d = {"type": typ, "period": period, "time": time_, "eventTeam": {"place": place, "teamCode": "AAA" if place == "home" else "BBB"},
             "player": {"playerId": pid}, "homeTeam": {"teamCode": "AAA", "score": 0}, "awayTeam": {"teamCode": "BBB", "score": 0}, "gameId": 1}
        d.update(kw)
        return d
    pen = lambda period, time_, place: ev("penalty", period, time_, place, variant={"minorTime": "2"})
    pbp = [ev("goalkeeper", 1, "00:00", "home", "10", isEntering=True), ev("goalkeeper", 1, "00:00", "away", "20", isEntering=True),
           pen(1, "05:00", "away"),
           ev("shot", 1, "05:30", "home", "1", locationX=50, locationY=0, goalSection=1),      # PP
           ev("goal", 1, "06:00", "home", "1", locationX=40, locationY=10, goalSection=2, goalStatus="PP"),  # PP-mål avbryter utvisningen
           ev("shot", 1, "06:30", "home", "2", locationX=100, locationY=60, goalSection=-3),  # EV, blockerat
           ev("shot", 1, "06:32", "home", "1", locationX=30, locationY=5, goalSection=0),     # EV, utanför, retur
           ev("shot", 2, "01:00", "away", "3", locationX=200, locationY=0, goalSection=3),    # EV
           ev("goalkeeper", 3, "19:00", "away", "20", isEntering=False),
           ev("shot", 3, "19:10", "home", "2", locationX=300, locationY=0, goalSection=4),    # EN
           ev("goalkeeper", 3, "20:00", "home", "10", isEntering=False)]
    state, goalie, gk, evs = timeline(pbp)
    t("utvisning: PP för hemmalaget", state("home", sn.at(pbp[3])), "PP")
    t("PP-mål avbryter den mindre utvisningen", state("home", 6 * 60 + 30), "EV")
    t("tom bur när målvakten gått ut", state("home", 2400 + 19 * 60 + 10), "EN")
    t("tid i lika styrka (60 min − 60 s PP − 60 s tom bur)", evs, 3600 - 60 - 60)
    g = parse_game({"uuid": "u1", "rawStartDateTime": "2026-10-01T17:00:00Z", "roundNumber": 3, "overtime": False, "shootout": False,
                    "homeTeamInfo": {"code": "AAA", "score": 1}, "awayTeamInfo": {"code": "BBB", "score": 0}},
                   {"stats": {}, "gkStats": {}}, list(reversed(pbp)))
    res_types = [(s[4], s[5]) for s in g["shots"]]
    t("skott: resultat och styrka", res_types, [("S", "PP"), ("G", "PP"), ("B", "EV"), ("M", "EV"), ("S", "EV"), ("S", "EN")])
    t("retur markeras (2 s efter blockerat skott)", mark_rebounds(g["shots"])[3], True)
    t("målvakt i mål vid skottet", g["shots"][4][7], "10")
    xgt = fit_xg([g] * 30)
    near, far = xg_of(["0", "", 20, 0, "S", "EV", 0, ""], False, xgt), xg_of(["0", "", 250, 0, "S", "EV", 0, ""], False, xgt)
    t("xG: nära målet värt mer än långt ut", near > far, True)
    t("xG: blockerat skott = 0", xg_of(["0", "", 20, 0, "B", "EV", 0, ""], False, xgt), 0.0)
    teams, players = season([g], xgt)
    t("Corsi 5 mot 5: hemma 2 försök (blockerat + utanför), borta 1", (teams["AAA"]["s"]["cf"], teams["BBB"]["s"]["cf"]), (66.7, 33.3))
    pr = match_probs(3.2, 2.4)
    t("matchsannolikheter summerar till 1", round(pr["pH"] + pr["pA"] + pr["pOT"], 6), 1.0)
    t("starkare lag vinner oftare", pr["pH"] > pr["pA"], True)
    t("marginalen tas bort ur oddsen", [round(x, 3) for x in implied([1.8, 2.0])], [0.526, 0.474])
    lam = poisson_total(5.5, 0.5)
    t("totalmål ur över/under 5,5 vid 50 %", 5.6 <= lam <= 6.0, True)
    names = {"OHK": ["Örebro Hockey", "Örebro"], "SAIK": ["Skellefteå AIK", "Skellefteå"], "FBK": ["Färjestad BK"]}
    t("lagnamn från oddstjänsten -> SHL-kod (Örebro, Skellefteå)", (match_team("Orebro HK", names) or match_team("Örebro HK", names), match_team("Skelleftea AIK", names) or match_team("Skellefteå AIK", names)), ("OHK", "SAIK"))
    od = parse_odds([{"home_team": "Färjestad BK", "away_team": "Örebro Hockey", "commence_time": "2026-10-10T17:00:00Z",
                      "bookmakers": [{"markets": [{"key": "h2h", "outcomes": [{"name": "Färjestad BK", "price": 2.1}, {"name": "Draw", "price": 4.2}, {"name": "Örebro Hockey", "price": 3.0}]}]}]}], names)
    t("tre-vägs odds (full tid) tolkas", (od[0]["home"], od[0]["away"], round(od[0]["pH"] + od[0]["pOT"] + od[0]["pA"], 6)), ("FBK", "OHK", 1.0))
    for ok, name, detail in res:
        print(("OK   " if ok else "FEL  ") + name + (f" – {detail}" if detail else ""))
    bad = sum(not x[0] for x in res)
    print(f"\n{len(res) - bad}/{len(res)} OK")
    return 1 if bad else 0


# ---------------------------------------------------------------- huvudprogram
def write(path, data):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(json.dumps(data, ensure_ascii=False, separators=(",", ":")))


def load(path):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def team_names(sched):
    names = {}
    for g in sched:
        for k in ("homeTeamInfo", "awayTeamInfo"):
            ti = g.get(k) or {}
            if ti.get("code"):
                nm = ti.get("names") or {}
                names[ti["code"]] = [nm.get("long"), nm.get("short"), nm.get("full"), nm.get("longSite")]
    return names


def main():
    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(encoding="utf-8")
        except (AttributeError, ValueError):
            pass
    ap = argparse.ArgumentParser(description="Planeringsdata för Fantasy Rinken (fullversionen)")
    ap.add_argument("--dir", default="data")
    ap.add_argument("--odds", action="store_true", help="hämta odds (kräver miljövariabeln ODDS_API_KEY)")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(selftest())
    f = sn.Fetcher()
    if a.odds:
        key = os.environ.get("ODDS_API_KEY", "").strip()
        if not key:
            print("ODDS_API_KEY saknas – inga odds hämtas.")
            return
        sched = f(sn.SCHEDULE).get("gameInfo") or []
        try:
            data = fetch_odds(key, team_names(sched))
        except (OSError, ValueError) as e:
            print("Odds gick inte att hämta:", type(e).__name__)  # nyckeln skrivs aldrig ut
            return
        write(os.path.join(a.dir, "odds.json"), data)
        print("Skrev odds.json:", "tillgängliga" if data.get("available") else data.get("reason"), len(data.get("games", [])), "matcher")
        return
    cache_p = os.path.join(a.dir, "plan-cache.json")
    cache, sched, new = build_cache(f, load(cache_p))
    games = cache["games"]
    xgt = fit_xg(games)
    tstats, pstats = season(games, xgt)
    now = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    write(cache_p, cache)
    write(os.path.join(a.dir, "season.json"), {"version": VERSION, "updated": now, "source": "Statnet AB via shl.se", "games": len(games),
                                               "teams": tstats, "players": pstats})
    write(os.path.join(a.dir, "model.json"), model(games, sched, xgt, tstats))
    xg_sum = sum(xg_of(s, rb, xgt) for g in games for s, rb in zip(g["shots"], mark_rebounds(g["shots"])))
    print(f"{len(games)} matcher ({new} nya, {f.calls} anrop). xG {xg_sum:.1f} mot {xgt['goals']} mål.")


if __name__ == "__main__":
    main()
