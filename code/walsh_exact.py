#!/usr/bin/env python3
"""walsh_exact.py -- exact Walsh coefficients of heap outputs by operator calculus; checks of Theorem 3.1 and Theorem 6.1.

For a heap with k_j bits of weight 2^j (j < m), T(x) = sum_j 2^j |x_j|, and  f_u(T) = (-1)^(sum_{i=1..m} u_i bit_i(T)),
  W_u(e) = sum_x (-1)^(l.x) f_u(T(x)) = sum_i p_i f_u(i),   P(E) = prod_j (1+E^(2^j))^(k_j-e_j) (1-E^(2^j))^(e_j)
(e_j = number of bits of column j on which the linear form l is 1), P reduced mod E^(2^(m+1)) - 1.

modes:
  walsh_exact.py selftest                random XAGs: every Walsh coefficient divisible by 2^(N-t)  (Theorem 3.1)
  walsh_exact.py monotone                Theorem 6.1: for monotone heaps the sign pattern e_j = M_{j+1} - M_j gives
                                         W_top = 2^(N - sum M) exactly; checked on all profiles of a grid and ADD_k(n)
  walsh_exact.py scan NB MAXM TRIALS     random heaps: min over (u, e) of v_2(W) == N - sum M ?   (Conjecture 9.1)
  walsh_exact.py one K0,K1,.. M          all (u, e) attaining the minimum for one heap
"""
import sys, random, itertools

def v2(x):
    if x == 0: return None
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def Ms(prof, m):
    M = [0]
    for j in range(m): M.append((M[-1] + (prof[j] if j < len(prof) else 0)) // 2)
    return M          # M[0..m]

def polymul_cyc(a, b, L):
    out = [0] * L
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[(i + j) % L] += x * y
    return out

def colpoly(j, k, e, L):
    """(1+X)^(k-e) (1-X)^e with X = E^(2^j), mod E^L - 1 (as dict-free dense list)"""
    p = [0] * L; p[0] = 1; s = (1 << j) % L
    for i in range(k):
        sign = -1 if i < e else 1
        q = [0] * L
        for t, c in enumerate(p):
            if c: q[t] += c; q[(t + s) % L] += sign * c
        p = q
    return p

def W_all_u(prof, m, e):
    """returns dict u -> W_u(e) for all u with top bit set (u is a mask over bits 1..m, bit i-1 of u = u_i)"""
    L = 1 << (m + 1); p = [0] * L; p[0] = 1
    for j in range(m):
        k = prof[j] if j < len(prof) else 0
        if k: p = polymul_cyc(p, colpoly(j, k, e[j], L), L)
    res = {}
    for u in range(1 << (m - 1), 1 << m):
        res[u] = sum(c * (1 - 2 * (bin((i >> 1) & u).count('1') & 1)) for i, c in enumerate(p) if c)
    return res

def tight(prof, m):
    M = Ms(prof, m); N = sum(prof[:m]); target = N - sum(M[1:])
    best = None; wit = []
    ks = [(prof[j] if j < len(prof) else 0) for j in range(m)]
    for e in itertools.product(*[range(k + 1) for k in ks]):
        for u, w in W_all_u(prof, m, e).items():
            v = v2(w)
            if v is None: continue
            assert v >= target, ('SPECTRAL BOUND EXCEEDS UPPER BOUND?!', prof, m, e, u, w)
            if best is None or v < best: best = v; wit = []
            if v == best: wit.append((u, e, w))
    return target, best, wit

def selftest(trials=300):
    rnd = random.Random(1)
    for _ in range(trials):
        n = rnd.randint(2, 8); t = rnd.randint(0, 5)
        vals = [[(x >> i) & 1 for x in range(1 << n)] for i in range(n)]
        for g in range(t):
            ops = []
            for side in range(2):
                c = rnd.randint(0, 1); sel = [rnd.randint(0, 1) for _ in vals]
                ops.append([c ^ (sum(s & v[x] for s, v in zip(sel, vals)) & 1) for x in range(1 << n)])
            vals.append([a & b for a, b in zip(*ops)])
        sel = [rnd.randint(0, 1) for _ in vals]; sel[-1] = 1
        f = [sum(s & v[x] for s, v in zip(sel, vals)) & 1 for x in range(1 << n)]
        a = [1 - 2 * b for b in f]; h = 1
        while h < (1 << n):
            for i in range(0, 1 << n, h << 1):
                for k in range(i, i + h): a[k], a[k + h] = a[k] + a[k + h], a[k] - a[k + h]
            h <<= 1
        for c in a: assert c % (1 << max(0, n - t)) == 0, (n, t, c)
    print('selftest: %d random XAGs, every Walsh coefficient divisible by 2^(n-t): OK' % trials)

def monotone():
    cnt = 0
    def check(prof):
        nonlocal cnt
        m = len(prof); M = Ms(prof, m)
        if any(M[j + 1] < M[j] for j in range(m)): return
        e = [M[j + 1] - M[j] for j in range(m)]
        w = W_all_u(prof, m, e)[1 << (m - 1)]
        assert w == 1 << (sum(prof) - sum(M[1:])), (prof, e, w)
        cnt += 1
    for m in range(1, 6):
        for prof in itertools.product(range(0, 7), repeat=m): check(list(prof))
    for k in range(2, 17):
        for n in range(2, 11): check([k] * (n - 1))
    for k in (3, 4, 5, 6, 7, 8): check([k] * 13)
    print('monotone: W_top(e_j = M_{j+1} - M_j) == 2^(N - sum M) on %d monotone heaps (grid k_j <= 6, m <= 5; ADD_k(n), k <= 16, n <= 10; k <= 8, n = 14): OK' % cnt)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'selftest': selftest()
    elif mode == 'monotone': monotone()
    elif mode == 'one':
        prof = [int(x) for x in sys.argv[2].split(',')]; m = int(sys.argv[3])
        t, b, wit = tight(prof, m); print('heap', prof, 'm', m, 'N - sumM =', t, 'min v2 =', b, 'TIGHT' if t == b else 'GAP', 'witnesses (u, e, W):', wit[:12], '... %d total' % len(wit))
    elif mode == 'scan':
        NB, MAXM, TR = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); rnd = random.Random(7); bad = 0; seen = set(); nonmono = 0
        for _ in range(TR):
            m = rnd.randint(2, MAXM); prof = [rnd.randint(0, NB) for _ in range(m)]
            if tuple(prof) in seen or sum(prof) == 0: continue
            seen.add(tuple(prof)); M = Ms(prof, m); nm = any(M[j + 1] < M[j] for j in range(m)); nonmono += nm
            t, b, wit = tight(prof, m)
            if t != b: bad += 1; print('GAP', prof, m, t, b, flush=True)
        print('scan: %d heaps (%d non-monotone), k_j <= %d, m <= %d: %d gaps' % (len(seen), nonmono, NB, MAXM, bad))
