"""mcsat.py: exact-MC upper bounds by SAT (own encoder): is there an XAG with <= t ANDs (XOR free) computing the
given functions?  AND j = (affine form over inputs and earlier ANDs) & (affine form ...); every output is an
affine form over inputs and all ANDs.  A SAT answer is decoded and CHECKED by exhaustive simulation
(so an upper bound never rests on the encoder); UNSAT answers are NOT used as proofs here (lower bounds come
from affine_tree.c and from the theorems of the paper).

  python3 mcsat.py addk COUNTS KAPPA TMAX   carries C_1..C_m of the bit-heap COUNTS (e.g. 2222) plus constant
                                            KAPPA: prints the least t <= TMAX with a verified circuit.
"""
import os
import subprocess
import sys
import tempfile


def solve(n, targets, t, timeout=600):
    """targets: list of truth tables (lists of 0/1 over 2^n rows). returns circuit or None/'unknown'."""
    nv = [0]
    cls = []

    def var():
        nv[0] += 1
        return nv[0]

    def xor_list(lits):
        cur = None
        for l in lits:
            if cur is None:
                cur = l
            else:
                o = var()
                cls.extend(([-o, cur, l], [-o, -cur, -l], [o, -cur, l], [o, cur, -l]))
                cur = o
        return cur

    def and2(a, b):
        o = var()
        cls.extend(([-o, a], [-o, b], [o, -a, -b]))
        return o

    T = 1 << n
    true = var()
    cls.append([true])
    coef = []
    gv = []
    for g in range(t):
        cg = [[var() for _ in range(n + g + 1)] for _ in (0, 1)]
        coef.append(cg)
        vals = []
        for r in range(T):
            sides = []
            for sd in (0, 1):
                terms = [cg[sd][i] for i in range(n) if (r >> i) & 1]
                terms += [and2(cg[sd][n + h], gv[h][r]) for h in range(g)]
                terms.append(cg[sd][n + g])
                sides.append(xor_list(terms))
            vals.append(and2(sides[0], sides[1]))
        gv.append(vals)
    ocoef = []
    for tt in targets:
        co = [var() for _ in range(n + t + 1)]
        ocoef.append(co)
        for r in range(T):
            terms = [co[i] for i in range(n) if (r >> i) & 1]
            terms += [and2(co[n + h], gv[h][r]) for h in range(t)]
            terms.append(co[n + t])
            l = xor_list(terms)
            cls.append([l] if tt[r] else [-l])
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "f.cnf")
        with open(p, "w") as f:
            f.write(f"p cnf {nv[0]} {len(cls)}\n")
            for c in cls:
                f.write(" ".join(map(str, c)) + " 0\n")
        r = subprocess.run(["cadical", "-q", "--plain", "-t", str(timeout), p], capture_output=True, text=True)
    if r.returncode == 20:
        return None
    if r.returncode != 10:
        return "unknown"
    model = set()
    seen = set()
    for ln in r.stdout.splitlines():
        if ln.startswith("v"):
            for x in ln.split()[1:]:
                seen.add(abs(int(x)))
                if int(x) > 0:
                    model.add(int(x))
    # CaDiCaL 3.1.0 can omit variables from the printed witness (seen with preprocessing on); --plain is
    # used and every coefficient variable must be present, else refuse to decode.
    need = [v for cg in coef for side in cg for v in side] + [v for co in ocoef for v in co]
    assert all(v in seen for v in need), "witness incomplete"
    circ = {"and": [[[int(v in model) for v in side] for side in cg] for cg in coef],
            "out": [[int(v in model) for v in co] for co in ocoef]}
    # independent check by simulation
    for r in range(T):
        x = [(r >> i) & 1 for i in range(n)]
        g = []
        for cg in circ["and"]:
            s = []
            for side in cg:
                v = side[-1]
                for i, c in enumerate(side[:-1]):
                    if c:
                        v ^= (x + g)[i]
                s.append(v)
            g.append(s[0] & s[1])
        for tt, co in zip(targets, circ["out"]):
            v = co[-1]
            for i, c in enumerate(co[:-1]):
                if c:
                    v ^= (x + g)[i]
            assert v == tt[r], "decoded circuit is wrong"
    return circ


def carry_targets(counts, kappa):
    m = len(counts)
    off = [sum(counts[:j]) for j in range(m + 1)]
    n = off[m]
    tts = [[0] * (1 << n) for _ in range(m)]
    for r in range(1 << n):
        Tsum = 0
        for i in range(1, m + 1):
            Tsum += bin((r >> off[i - 1]) & ((1 << counts[i - 1]) - 1)).count("1") << (i - 1)
            Tk = Tsum + (kappa & ((1 << i) - 1))
            tts[i - 1][r] = (Tk >> i) & 1
    return n, tts


if __name__ == "__main__":
    if sys.argv[1] == "addk":
        counts = [int(c) for c in sys.argv[2]]
        kappa = int(sys.argv[3], 0)
        tmax = int(sys.argv[4])
        n, tts = carry_targets(counts, kappa)
        for t in range(0, tmax + 1):
            c = solve(n, tts, t)
            if c == "unknown":
                print(f"counts={sys.argv[2]} kappa={kappa} t={t}: unknown")
                break
            if c is not None:
                print(f"counts={sys.argv[2]} kappa={kappa}: verified circuit with {t} ANDs (smaller t: solver UNSAT, unchecked)")
                break
        else:
            print(f"counts={sys.argv[2]} kappa={kappa}: no circuit with <= {tmax} ANDs found (solver)")
