"""round_sum_dp.py: abstract AND-only DP for the joint (a', e') round sums in the full-adder ("membership heap") model.

Bits of a column are shared (in both sums), A-only or E-only.  FA: 3 bits -> 1 bit + carry (1 AND);
HA: 2 -> 1 + carry (1 AND); with a constant 1: HAK (bit,1) -> bit + carry (0 AND), FAK (2 bits,1) -> bit +
carry (1 AND).  A shared op needs shared inputs; shared bits left over ("remainder" r) are copied to both
private columns for free.  Private columns are reduced to one bit.
Constants: shared constant cS (free choice), private constant C = K - cS (same in both sums).
State: (cs, ca, ce, borrow).  joint=False forces r <= 1 (T1 resolved in every column).
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))
import sha256_ref as sref
N = 32

def priv(m, k):            # reduce m bits (+const k) to one bit: (ANDs, carries)
    return m // 2, (m + k) // 2

def shared_opts(m, k, joint):
    """yield (r, kpass, ands, carries): reduce m shared bits (+const k) to r bits, const passed down or not."""
    res = {}
    def put(r, kp, a, c):
        key = (r, kp)
        if key not in res or (a, c) < res[key]: res[key] = (a, c)
    for r in range(0, m + 1):
        if m > 0 and r == 0: continue
        if not joint and r > 1: continue
        d = m - r
        put(r, k, (d + 1) // 2, (d + 1) // 2)            # constant (if any) passed to the private columns
        if k:
            if d % 2: put(r, 0, (d + 1) // 2, (d + 1) // 2)      # FAK + FAs
            elif m >= 1: put(r, 0, d // 2, d // 2 + 1)           # HAK + FAs
    return [(r, kp, a, c) for (r, kp), (a, c) in res.items()]

def plan(vS, vA, vE, K, joint=True, ka=0, ke=0, n=N, fixC=None):
    """vS/vA/vE: number of variable bits per column (lists); private constants K-cS+ka, K-cS+ke."""
    # state: (cs, ca, ce, bA, bE) with bA/bE = borrow of (K+ka - cS), (K+ke - cS)
    KA, KE = (K + ka) & (2**n - 1), (K + ke) & (2**n - 1)
    st = {(0, 0, 0, 0, 0): (0, ())}
    for i in range(n):
        new = {}
        last = (i == n - 1)
        for (cs, ca, ce, bA, bE), (cost, hist) in st.items():
            for kS in (0, 1):
                if fixC is not None and kS != ((K - fixC) >> i) & 1: continue
                tA = ((KA >> i) & 1) - kS - bA; kA = tA & 1; nbA = 1 if tA < 0 else 0
                tE = ((KE >> i) & 1) - kS - bE; kE = tE & 1; nbE = 1 if tE < 0 else 0
                if last:
                    key = (0, 0, 0, 0, 0)
                    if key not in new or cost < new[key][0]: new[key] = (cost, hist + ((kS, None),))
                    continue
                for (r, kp, a, c) in shared_opts(vS[i] + cs, kS, joint):
                    if kp and (kA or kE): continue
                    aA, cA = priv(r + vA[i] + ca, kA or kp)
                    aE, cE = priv(r + vE[i] + ce, kE or kp)
                    key = (c, cA, cE, nbA, nbE); tot = cost + a + aA + aE
                    if key not in new or tot < new[key][0]: new[key] = (tot, hist + ((kS, r),))
        st = new
    return min(st.values())

if __name__ == "__main__":
    # sanity: pair (x+y+z, x+y+w): 3n-4 joint, 3n-3 shared-T
    for n in (2, 3, 4, 8, 32):
        print("pair n", n, plan([2]*n, [1]*n, [1]*n, 0, True, n=n)[0], plan([2]*n, [1]*n, [1]*n, 0, False, n=n)[0])
    tj = ts = t0 = 0
    for t in range(64):
        K = sref.K[t]
        j = plan([4]*N, [2]*N, [1]*N, K, True); s = plan([4]*N, [2]*N, [1]*N, K, False)
        z = plan([4]*N, [2]*N, [1]*N, K, False, fixC=0)
        tj += j[0]; ts += s[0]; t0 += z[0]
        print(t, hex(K), "joint", j[0], "sharedT1", s[0], "C=0", z[0], "r:", [h[1] for h in j[1]][:8])
    print("total joint", tj, "sharedT1 best C", ts, "C=0", t0)
