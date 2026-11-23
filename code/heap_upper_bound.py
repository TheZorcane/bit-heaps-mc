"""heap_upper_bound.py: upper-bound construction for k-operand addition mod 2^n ("bit-heap" full/half-adder network with
truncation) and its verification.

AND count = sum_{i=1}^{n-1} M_i with M_i = k - ceil(k / 2^i) (max carry into column i):
column j (< n-1) holds k operand bits + M_j unary carry bits and is reduced to one sum bit with
floor((k + M_j)/2) = M_{j+1} adders (1 AND each: FA = maj via (a^c)(b^c)^c, HA = ab); the top column is XOR only.

  python3 heap_upper_bound.py small            exhaustive check for all (k, n) with k*n <= 16
  python3 heap_upper_bound.py prove K N [t]    build ADD_K mod 2^N, write .xag + cost, prove == reference chain of ripple
                                   adders with verifier/equiv.py (status must be "equivalent")
Inputs: operand i bit b = input index i*n + b (LSB first).  Outputs: sum bits LSB first.
"""
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
# VERIFIER_DIR may point at a checkout whose verifier/vendor binaries are compiled (sources identical)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))
from xag import XAG, write_xag  # noqa: E402
import cost  # noqa: E402
import sim  # noqa: E402

RES = os.environ.get("OUTDIR", os.path.join(HERE, "out"))


def formula(k, n):
    return sum(k - -(-k // (1 << i)) for i in range(1, n))


def heap_adder(k, n):
    x = XAG(k * n)
    carries = []
    for j in range(n):
        bits = [x.input(i * n + j) for i in range(k)] + carries
        carries = []
        if j == n - 1:                       # top column: parity only
            s = bits[0]
            for b in bits[1:]:
                s = x.XOR(s, b)
            x.outputs.append(s)
            break
        while len(bits) >= 3:                # full adder: sum = a^b^c, carry = (a^c)(b^c)^c
            a, b, c = bits[0], bits[1], bits[2]
            ac = x.XOR(a, c)
            bc = x.XOR(b, c)
            carries.append(x.XOR(x.AND(ac, bc), c))
            bits = bits[3:] + [x.XOR(ac, b)]
        if len(bits) == 2:                   # half adder
            a, b = bits
            carries.append(x.AND(a, b))
            bits = [x.XOR(a, b)]
        x.outputs.append(bits[0])
    return x


def ripple_chain(k, n):
    """reference: ((x1 + x2) + x3) + ... with plain ripple adders (textbook maj carries)."""
    x = XAG(k * n)
    acc = [x.input(b) for b in range(n)]
    for i in range(1, k):
        op = [x.input(i * n + b) for b in range(n)]
        c = 0
        out = []
        for b in range(n):
            p = x.XOR(acc[b], op[b])
            out.append(x.XOR(p, c) if c else p)
            if b < n - 1:
                g = x.AND(acc[b], op[b])
                c = x.XOR(g, x.AND(p, c)) if c else g
        acc = out
    x.outputs = acc
    return x


def exhaustive(x, k, n):
    nin = k * n
    N = 1 << nin
    lns_ = []
    for j in range(nin):
        blk = 1 << j
        v = ((1 << blk) - 1) << blk
        cur = 2 * blk
        while cur < N:
            v |= v << cur
            cur *= 2
        lns_.append(v)
    outs = sim.simulate(x, lns_, N)
    m = (1 << n) - 1
    exp = [0] * n
    for t in range(N):
        s = sum((t >> (i * n)) & m for i in range(k)) & m
        for b in range(n):
            if (s >> b) & 1:
                exp[b] |= 1 << t
    return all(outs[b] == exp[b] for b in range(n))


def random_check(x, k, n, trials=20000, seed=11):
    rnd = random.Random(seed)
    m = (1 << n) - 1
    for _ in range(trials):
        ops = [rnd.getrandbits(n) for _ in range(k)]
        bits = []
        for o in ops:
            bits += [(o >> b) & 1 for b in range(n)]
        got = sim.eval_bits(x, bits)
        s = sum(ops) & m
        if [(s >> b) & 1 for b in range(n)] != list(got):
            return False
    return True


if __name__ == "__main__":
    os.makedirs(RES, exist_ok=True)
    if sys.argv[1] == "small":
        lines = []
        for k in range(2, 9):
            for n in range(1, 9):
                if k * n > 16:
                    continue
                x = heap_adder(k, n)
                ok = exhaustive(x, k, n)
                c = x.counts()
                lines.append(f"k={k} n={n}: AND={c['AND']} formula={formula(k, n)} XOR={c['XOR']} exhaustive={'OK' if ok else 'FAIL'}")
                assert ok and c["AND"] == formula(k, n)
                print(lines[-1], flush=True)
        open(os.path.join(RES, "heap_small.txt"), "w").write("\n".join(lines) + "\n")
    elif sys.argv[1] == "prove":
        import equiv
        k, n = int(sys.argv[2]), int(sys.argv[3])
        to = float(sys.argv[4]) if len(sys.argv) > 4 else 1800
        x = cost.canonicalize(heap_adder(k, n))
        ref = cost.canonicalize(ripple_chain(k, n))
        assert random_check(x, k, n) and random_check(ref, k, n), "random smoke failed"
        name = f"add{k}_{n}_heap"
        p = os.path.join(RES, name + ".xag")
        open(p, "w").write(write_xag(x))
        rep = cost.report_xag(x)
        json.dump(rep, open(p + ".cost.json", "w"), indent=2)
        m = equiv.check(x, ref, os.path.join(RES, "proofs", name), name=name + "_vs_ripple_chain", timeout=to)
        print(name, "AND", rep["AND"], "formula", formula(k, n), "XOR", rep["XOR"], "total", rep["total"],
              "depth", rep["depth"], "sha256", rep["sha256"], "status", m["status"], m.get("total_wall_s"))
