#!/usr/bin/env python3
"""tight_certificates.py -- certificates  v_2(W) = N - U(kappa, K)  for ALL heaps with a constant in a grid.

For every profile (k_0..k_{m-1}), k_j <= MAXK, and every constant K < 2^m, searches a pair (u, e) with
   v_2( sum_x (-1)^(l.x) f_u(T(x) + K) ) = N - U(kappa, K)
(e_j = number of bits of column j in the support of l; u != 0 a mask over the output bits 1..m of T + K).
By Theorem 3.1 such a coefficient proves MC(heap + K) >= U; the FA network with the constant consumed last has U
ANDs; so MC = U exactly.  Every Walsh coefficient met on the way is also checked to be divisible by 2^(N-U)
(consistency of Theorem 3.1 with the upper bound).  Output: one line per m and a certificate file.
usage: tight_certificates.py MAXM MAXK [OUTFILE]
"""
import sys, itertools

def U(prof, K, m):
    """AND count of the full-adder network with the constant consumed last (Lemma 4.1):
       v_j = k_j + c_j, c_{j+1} = floor((v_j + K_j)/2), U = sum_{j<m} floor(v_j/2)."""
    v = 0; c = 0; tot = 0
    for j in range(m):
        v = prof[j] + c; tot += v // 2; c = (v + ((K >> j) & 1)) // 2
    return tot

def pairing_ok(prof, K, m):
    """hypothesis of Theorem 6.1: the carry counts c_1 <= c_2 <= ... <= c_m of the FA network are non-decreasing"""
    c = 0
    for j in range(m):
        c2 = (prof[j] + c + ((K >> j) & 1)) // 2
        if c2 < c: return False
        c = c2
    return True

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def colpolys(j, k, L):
    """list over e = 0..k of (1+X)^(k-e) (1-X)^e mod E^L - 1, X = E^(2^j)"""
    s = (1 << j) % L; res = []
    for e in range(k + 1):
        p = [0] * L; p[0] = 1
        for i in range(k):
            sign = -1 if i < e else 1; q = [0] * L
            for t, c in enumerate(p):
                if c: q[t] += c; q[(t + s) % L] += sign * c
            p = q
        res.append(p)
    return res

def mul(a, b, L):
    out = [0] * L
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[(i + j) % L] += x * y
    return out

def run(MAXM, MAXK, outfile=None):
    out = open(outfile, 'w') if outfile else None
    for m in range(1, MAXM + 1):
        L = 1 << (m + 1); n = 0; nopair = 0; fail = []
        fu = {u: [1 - 2 * (bin((i >> 1) & u).count('1') & 1) for i in range(L)] for u in range(1, 1 << m)}
        cps = {(j, k): colpolys(j, k, L) for j in range(m) for k in range(MAXK + 1)}
        for prof in itertools.product(range(MAXK + 1), repeat=m):
            N = sum(prof)
            if N == 0: continue
            target = {K: N - U(prof, K, m) for K in range(1 << m)}; todo = set(target); cert = {}
            for e in itertools.product(*[range(k + 1) for k in prof]):
                p = [0] * L; p[0] = 1
                for j in range(m):
                    if prof[j]: p = mul(p, cps[(j, prof[j])][e[j]], L)
                for K in range(1 << m):
                    for u, f in fu.items():
                        w = sum(c * f[(i + K) % L] for i, c in enumerate(p) if c)
                        if w == 0: continue
                        v = v2(w); assert v >= target[K], ('Theorem 3.1 contradicts the upper bound?!', prof, K, e, u, w)
                        if v == target[K] and K in todo: todo.discard(K); cert[K] = (u, e, w)
                if not todo: break
            for K in range(1 << m):
                n += 1; nopair += not pairing_ok(prof, K, m)
                if K in cert:
                    if out: out.write('%s K=%d m=%d N=%d U=%d  u=%d e=%s W=%d\n' % (','.join(map(str, prof)), K, m, N, N - target[K], cert[K][0], ','.join(map(str, cert[K][1])), cert[K][2]))
                else: fail.append((prof, K))
        print('m=%d k_j<=%d: %d heaps-with-constant (%d outside Theorem 6.1): %d without a tight Walsh coefficient %s' % (m, MAXK, n, nopair, len(fail), fail[:10]), flush=True)
if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3] if len(sys.argv) > 3 else None)
