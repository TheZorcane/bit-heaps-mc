"""joint_pair_circuit.py (Proposition 11.1): the pair (x+y+z, x+y+w) mod 2^n with 3n-4 ANDs (n >= 2); shared-T1 needs 3n-3.

  column 0     : kA = maj(x0,y0,z0), kE = maj(x0,y0,w0)                (2 ANDs, nothing shared)
  column 1     : c = x1 y1, p = x1^y1, dA = maj(p,z1,kA), dE = maj(p,w1,kE)        (3 ANDs)
  column j >= 2: t = xj^yj^c, c' = maj(xj,yj,c), dA' = maj(t,zj,dA), dE' = maj(t,wj,dE)   (3 ANDs)
  column n-1   : XORs only.
The carry into column j of the first sum is the integer c + dA (two bits), of the second c + dE.

usage: joint_pair_circuit.py      exhaustive check n = 2..4, AND counts, then n = 32 equivalence proof
                                  (verifier/equiv.py, LRAT checked by verifier/lrat_check.py + vendored lrat-check)
"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))
from xag import XAG, write_xag
import cost


def maj(x, a, b, c):          # (a^c)(b^c)^c : 1 AND
    return x.XOR(x.AND(x.XOR(a, c), x.XOR(b, c)), c)


def pair(n):
    """inputs: x, y, z, w (n bits each, LSB first, in this order); outputs A bits then E bits (LSB first)."""
    x = XAG(4 * n)
    X = [x.input(i) for i in range(n)]; Y = [x.input(n + i) for i in range(n)]
    Z = [x.input(2 * n + i) for i in range(n)]; W = [x.input(3 * n + i) for i in range(n)]
    A, E = [], []
    p = x.XOR(X[0], Y[0])
    A.append(x.XOR(p, Z[0])); E.append(x.XOR(p, W[0]))
    if n == 1:
        x.outputs = A + E; return x
    kA, kE = maj(x, X[0], Y[0], Z[0]), maj(x, X[0], Y[0], W[0])
    p = x.XOR(X[1], Y[1])
    A.append(x.XOR(x.XOR(p, Z[1]), kA)); E.append(x.XOR(x.XOR(p, W[1]), kE))
    if n > 2:
        c = x.AND(X[1], Y[1]); dA = maj(x, p, Z[1], kA); dE = maj(x, p, W[1], kE)
    for j in range(2, n):
        t = x.XOR(x.XOR(X[j], Y[j]), c)
        A.append(x.XOR(x.XOR(t, Z[j]), dA)); E.append(x.XOR(x.XOR(t, W[j]), dE))
        if j < n - 1:
            c2 = maj(x, X[j], Y[j], c); dA = maj(x, t, Z[j], dA); dE = maj(x, t, W[j], dE); c = c2
    x.outputs = A + E
    return x


def ripple(x, a, b):
    c, out = 0, []
    for j in range(len(a)):
        q = x.XOR(a[j], b[j]); out.append(x.XOR(q, c))
        c = x.XOR(x.AND(a[j], b[j]), x.AND(c, q))
    return out


def reference(n):             # textbook: T = x + y, A = T + z, E = T + w (ripple adders)
    x = XAG(4 * n)
    X = [x.input(i) for i in range(n)]; Y = [x.input(n + i) for i in range(n)]
    Z = [x.input(2 * n + i) for i in range(n)]; W = [x.input(3 * n + i) for i in range(n)]
    T = ripple(x, X, Y)
    x.outputs = ripple(x, T, Z) + ripple(x, T, W)
    return x


if __name__ == "__main__":
    import sim
    for n in (2, 3, 4):
        c = pair(n); N = 1 << (4 * n); m = (1 << n) - 1
        lns_ = [sum(((v >> i) & 1) << v for v in range(N)) for i in range(4 * n)]
        outs = sim.simulate(c, lns_, N)
        bad = 0
        for v in range(N):
            xv, yv, zv, wv = v & m, (v >> n) & m, (v >> 2 * n) & m, (v >> 3 * n) & m
            a = sum(((outs[i] >> v) & 1) << i for i in range(n)); e = sum(((outs[n + i] >> v) & 1) << i for i in range(n))
            bad += (a != (xv + yv + zv) & m) or (e != (xv + yv + wv) & m)
        print(f"n={n}: {cost.canonicalize(c).counts()} (3n-4 = {3*n-4}), exhaustive mismatches {bad} / {N}")
    import equiv
    a = cost.canonicalize(pair(32)); b = reference(32)
    out = os.environ.get("OUTDIR", os.path.join(HERE, "out")); os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "pair32.xag"), "w").write(write_xag(a))
    print("n=32:", a.counts(), "reference", cost.canonicalize(b).counts())
    m = equiv.check(a, b, os.path.join(out, "proof_pair32"), name="pair32", timeout=600)
    print(json.dumps({k: m.get(k) for k in ("status", "result", "proof_check", "cnf_sha256", "proof_sha256")}))
    for ext in (".lrat", ".cnf"):
        lr = os.path.join(out, "proof_pair32", "pair32" + ext)
        if os.path.exists(lr) and os.path.getsize(lr) > 20_000_000: os.remove(lr)
