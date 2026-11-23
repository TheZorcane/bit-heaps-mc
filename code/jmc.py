"""jmc.py: joint multiplicative complexity of several sums sharing operands ("membership heaps"), by SAT.

A membership heap: variables v with a column col(v) (weight 2^col) and a membership mask (bit s set iff the
variable is an addend of sum s).  Targets: for each sum s and i = 1..m, the carry parity
C^s_i = bit i of sum_{v in s, col(v) < i} 2^col(v) v  (+ constant kappa_s).  These are exactly the nonlinear
parts of the output bits of the sums mod 2^(m+1) (the top column enters linearly and is omitted).

Upper bounds: SAT model decoded and re-simulated (mcsat.solve).
UNSAT answers are solver-only (no proof kept) and are reported as such.

usage: jmc.py SPEC TMAX [timeout]      SPEC = per column a comma list of masks, columns separated by '/'
   e.g. pair (x+y+z, x+y+w) mod 8:  3,3,1,2/3,3,1,2       optional ":kA,kE" constants appended
"""
import sys
from mcsat import solve


def parse(spec):
    kap = None
    if ":" in spec:
        spec, ks = spec.split(":")
        kap = [int(k, 0) for k in ks.split(",")]
    cols = [[int(t) for t in c.split(",") if t != ""] for c in spec.split("/")]
    nsum = max(max(c) for c in cols if c).bit_length()
    return cols, nsum, kap or [0] * nsum


def targets(cols, nsum, kap):
    m = len(cols)
    vars_ = [(j, mk) for j, c in enumerate(cols) for mk in c]
    n = len(vars_)
    tts = []
    for s in range(nsum):
        tt = [[0] * (1 << n) for _ in range(m)]
        for r in range(1 << n):
            T = 0
            idx = 0
            for i in range(1, m + 1):
                while idx < n and vars_[idx][0] < i:
                    if (vars_[idx][1] >> s) & 1 and (r >> idx) & 1:
                        T += 1 << vars_[idx][0]
                    idx += 1
                tt[i - 1][r] = ((T + (kap[s] & ((1 << i) - 1))) >> i) & 1
        tts += tt
    return n, tts


if __name__ == "__main__":
    cols, nsum, kap = parse(sys.argv[1])
    tmax = int(sys.argv[2]); to = int(sys.argv[3]) if len(sys.argv) > 3 else 600
    tmin = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    n, tts = targets(cols, nsum, kap)
    for t in range(tmin, tmax + 1):
        c = solve(n, tts, t, to)
        if c == "unknown":
            print(f"{sys.argv[1]}: t={t} unknown (timeout {to}s)", flush=True); continue
        if c is not None:
            print(f"{sys.argv[1]}: verified circuit with {t} ANDs (smaller t: solver UNSAT, unchecked)", flush=True)
            print(c); break
        print(f"{sys.argv[1]}: t={t} UNSAT (solver-only)", flush=True)
