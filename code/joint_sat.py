"""joint_sat.py: "no XAG with t ANDs" as a SAT instance with a strictly checked LRAT refutation.

Circuit model (Section 2 of the paper): AND gate j = L_j * R_j, where L_j, R_j are XORs of
inputs and earlier AND gates; every target is an XOR of inputs, AND gates and a constant.

Normal form used by the encoder (sound: no circuit is lost):
  (N1) L_j, R_j have NO constant term.  [(L+a)(R+b) = LR + bL + aR + ab, and bL + aR + ab is an XOR of
       inputs, earlier gates and a constant, so every later form and every output can absorb it.]
Optional (flag "span"), valid ONLY when t = rank of the targets modulo affine functions (checked here by
Gaussian elimination before it is used):
  (N2) every gate g_j is itself  (XOR of targets) + (affine function of the inputs).
       [The targets lie in Aff + span(g_1..g_t); if the t targets are independent modulo Aff then
        span(targets) + Aff = span(g) + Aff, so each g_j is in span(targets) + Aff.]
  (N3) flag "extra=E", valid ONLY when t = rank + 1: Aff + span(g) contains Aff + span(targets) with
       codimension <= 1, so for E := the least index with g_E not in Aff + span(targets) (or E = t-1 if
       there is none): g_j is in Aff + span(targets) for j < E and in Aff + span(targets) + <g_E> for j > E.
       "No t-AND circuit" = the instances E = 0..t-1 are ALL unsatisfiable.
(N1) and (N2) hold simultaneously: N2 is a property of the gate functions of any t-AND circuit, and the
N1 rewrite changes each gate only by an element of Aff + span(earlier gates) -- apply N2's argument to the
rewritten circuit, which is again a t-AND circuit for the same targets.

usage: joint_sat.py SPEC T [span | extra=E] [timeout_s]
  SAT   -> circuit decoded and re-simulated on all inputs (an upper bound, independent of the encoder)
  UNSAT -> LRAT proof checked by verifier/lrat_check.py (strict RUP).  The statement proven is the
           unsatisfiability of THIS CNF; that the CNF encodes "a t-AND XAG exists" is this file's claim.
"""
import os, sys, subprocess, hashlib, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))
from jmc import parse, targets


def rank_mod_affine(n, tts):
    """rank of the truth tables modulo affine functions (GF(2) elimination on ANF, degree >= 2 monomials)."""
    rows = []
    for tt in tts:
        a = list(tt)
        for i in range(n):
            for r in range(1 << n):
                if (r >> i) & 1: a[r] ^= a[r ^ (1 << i)]
        v = 0
        for r in range(1 << n):
            if a[r] and bin(r).count("1") >= 2: v |= 1 << r
        rows.append(v)
    rank = 0
    for i in range(len(rows)):
        if rows[i] == 0: continue
        rank += 1
        low = rows[i] & -rows[i]
        for j in range(i + 1, len(rows)):
            if rows[j] & low: rows[j] ^= rows[i]
    return rank


def encode(n, tts, t, span, extra=None):
    nv = [0]; cls = []
    def var():
        nv[0] += 1; return nv[0]
    def xor_list(lits):
        cur = None
        for l in lits:
            if cur is None: cur = l
            else:
                o = var()
                cls.extend(([-o, cur, l], [-o, -cur, -l], [o, -cur, l], [o, cur, -l]))
                cur = o
        return cur
    def and2(a, b):
        o = var(); cls.extend(([-o, a], [-o, b], [o, -a, -b])); return o
    T = 1 << n
    false = var(); cls.append([-false])
    coef, gv = [], []
    for g in range(t):
        cg = [[var() for _ in range(n + g)] for _ in (0, 1)]      # (N1): no constant coefficient
        coef.append(cg)
        vals = []
        for r in range(T):
            sides = []
            for sd in (0, 1):
                terms = [cg[sd][i] for i in range(n) if (r >> i) & 1]
                terms += [and2(cg[sd][n + h], gv[h][r]) for h in range(g)]
                sides.append(xor_list(terms) if terms else false)
            vals.append(and2(sides[0], sides[1]))
        gv.append(vals)
    ocoef = []
    for tt in tts:
        co = [var() for _ in range(n + t + 1)]
        ocoef.append(co)
        for r in range(T):
            terms = [co[i] for i in range(n) if (r >> i) & 1]
            terms += [and2(co[n + h], gv[h][r]) for h in range(t)]
            terms.append(co[n + t])
            l = xor_list(terms)
            cls.append([l] if tt[r] else [-l])
    if span or extra is not None:                                  # (N2) / (N3)
        for g in range(t):
            if g == extra: continue
            sc = [var() for _ in range(len(tts))]; ac = [var() for _ in range(n + 1)]
            eps = var() if (extra is not None and g > extra) else None
            for r in range(T):
                terms = [sc[k] for k in range(len(tts)) if tts[k][r]]
                terms += [ac[i] for i in range(n) if (r >> i) & 1] + [ac[n]]
                if eps is not None: terms.append(and2(eps, gv[extra][r]))
                l = xor_list(terms)                                # == g_g(r)
                cls.extend(([-l, gv[g][r]], [l, -gv[g][r]]))
    return nv[0], cls, coef, ocoef


def simulate(n, tts, t, coef, ocoef, model):
    T = 1 << n
    for r in range(T):
        x = [(r >> i) & 1 for i in range(n)]; g = []
        for cg in coef:
            s = []
            for side in cg:
                v = 0
                for i, c in enumerate(side):
                    if c in model: v ^= (x + g)[i]
                s.append(v)
            g.append(s[0] & s[1])
        for tt, co in zip(tts, ocoef):
            v = 1 if co[-1] in model else 0
            for i, c in enumerate(co[:-1]):
                if c in model: v ^= (x + g)[i]
            if v != tt[r]: return False
    return True


if __name__ == "__main__":
    spec = sys.argv[1]; t = int(sys.argv[2])
    span = "span" in sys.argv[3:]
    extra = [int(a.split("=")[1]) for a in sys.argv[3:] if a.startswith("extra=")]
    extra = extra[0] if extra else None
    to = [int(a) for a in sys.argv[3:] if a.isdigit()]
    to = to[0] if to else 3600
    cols, nsum, kap = parse(spec)
    n, tts = targets(cols, nsum, kap)
    rk = rank_mod_affine(n, tts)
    if span and rk != t:
        print(f"span constraints need t == rank mod affine ({rk}); refusing"); sys.exit(2)
    if extra is not None and rk != t - 1:
        print(f"extra= needs t == rank + 1 (rank {rk}); refusing"); sys.exit(2)
    nv, cls, coef, ocoef = encode(n, tts, t, span, extra)
    out = os.path.join(os.environ.get("OUTDIR", os.path.join(HERE, "out")), "mcproofs"); os.makedirs(out, exist_ok=True)
    tag = spec.replace("/", "_").replace(",", "").replace(":", "k") + f"_t{t}" + ("_span" if span else "") + (f"_extra{extra}" if extra is not None else "")
    cnf = os.path.join(out, tag + ".cnf"); proof = os.path.join(out, tag + ".lrat")
    with open(cnf, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
    t0 = time.time()
    try:
        r = subprocess.run(["cadical", "--plain", "--lrat=true", "--binary=false", "-w", os.path.join(out, tag + ".model"),
                            cnf, proof], capture_output=True, text=True, timeout=to)
        code = r.returncode
    except subprocess.TimeoutExpired:
        code = -1
    res = {"spec": spec, "t": t, "span": span, "extra": extra, "rank_mod_affine": rk, "vars": nv, "clauses": len(cls),
           "cnf_sha256": hashlib.sha256(open(cnf, "rb").read()).hexdigest(), "solve_s": round(time.time() - t0, 1)}
    if code == 10:
        model = set()
        for ln in open(os.path.join(out, tag + ".model")):
            if ln.startswith("v"):
                model |= {int(v) for v in ln.split()[1:] if int(v) > 0}
        res["result"] = "sat"; res["circuit_checked_by_simulation"] = simulate(n, tts, t, coef, ocoef, model)
        res["and"] = [[[int(v in model) for v in side] for side in cg] for cg in coef]
        res["out"] = [[int(v in model) for v in co] for co in ocoef]
    elif code == 20:
        import lrat_check
        t1 = time.time()
        ok, msg = lrat_check.check(cnf, proof)
        res["result"] = "unsat"; res["lrat_strict_check"] = bool(ok); res["lrat_msg"] = str(msg)[:200]
        res["proof_sha256"] = hashlib.sha256(open(proof, "rb").read()).hexdigest()
        res["proof_bytes"] = os.path.getsize(proof); res["check_s"] = round(time.time() - t1, 1)
    else:
        res["result"] = "unknown"
    for p in (os.path.join(out, tag + ".model"),):
        if os.path.exists(p): os.remove(p)
    if res["result"] != "unsat" or res.get("proof_bytes", 0) > 50_000_000:
        if os.path.exists(proof): os.remove(proof)         # keep only small proofs; hash recorded
    json.dump(res, open(os.path.join(out, tag + ".json"), "w"), indent=1)
    print(json.dumps(res))
