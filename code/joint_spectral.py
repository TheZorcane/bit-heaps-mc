#!/usr/bin/env python3
"""joint_spectral.py -- the spectral bound (Theorem 3.1) by brute force for arbitrary small multi-output functions.
  bound(F) = N - min over u != 0 of min_l v_2(W_u(l))   [max over u of (N - min_l v_2)]
modes:
  joint_spectral.py pair n          joint pair (x+y+z, x+y+w) mod 2^n   (Conjecture 11.5: 3n-4)
  joint_spectral.py addc k n K      x_1+..+x_k + K mod 2^n             (constants, Theorem 2)
  joint_spectral.py wtc n c m       weight of n bits + c, bits 1..m
  joint_spectral.py share1 n        (u+z, u+w) mod 2^n                 (Proposition 11.2: 2n-2)
"""
import sys, itertools

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def fwt(a):
    n = len(a); h = 1
    while h < n:
        for i in range(0, n, h << 1):
            for k in range(i, i + h): a[k], a[k + h] = a[k] + a[k + h], a[k] - a[k + h]
        h <<= 1
    return a

def bound(N, outs, names=None):
    """outs: list of truth tables (lists of 0/1 of length 2^N).  returns (best bound, mask u)"""
    r = len(outs); best = (-1, 0)
    for u in range(1, 1 << r):
        f = [0] * (1 << N)
        for i in range(r):
            if u >> i & 1: f = [a ^ b for a, b in zip(f, outs[i])]
        a = fwt([1 - 2 * b for b in f]); v = min(v2(c) for c in a if c)
        if N - v > best[0]: best = (N - v, u)
    return best

def words(N, n, k):
    """split x (N = k*n bits) into k words, bit j of word i = variable i + k*j (column major)"""
    def w(x, i): return sum(((x >> (i + k * j)) & 1) << j for j in range(n))
    return w

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'pair' or mode == 'share1':
        n = int(sys.argv[2]); k = 4 if mode == 'pair' else 3; m = n - 1; N = k * m; w = words(N, m, k); outs = []
        for i in range(1, m + 1):
            if mode == 'pair':
                outs.append([((w(x, 0) + w(x, 1) + w(x, 2)) >> i) & 1 for x in range(1 << N)])
                outs.append([((w(x, 0) + w(x, 1) + w(x, 3)) >> i) & 1 for x in range(1 << N)])
            else:
                outs.append([((w(x, 0) + w(x, 1)) >> i) & 1 for x in range(1 << N)])
                outs.append([((w(x, 0) + w(x, 2)) >> i) & 1 for x in range(1 << N)])
        b, u = bound(N, outs)
        print('%s n=%d: N=%d carry-parity outputs=%d  spectral bound %d (u=%s)  FA/conjectured %d' % (mode, n, N, len(outs), b, bin(u), 3 * n - 4 if mode == 'pair' else 2 * n - 2), flush=True)
    elif mode == 'addc':
        k, n, K = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); m = n - 1; N = k * m; w = words(N, m, k)
        outs = [[((sum(w(x, i) for i in range(k)) + K) >> i) & 1 for x in range(1 << N)] for i in range(1, m + 1)]
        b, u = bound(N, outs)
        v = [k] ; U = 0; carry = 0
        for j in range(m):
            vj = k + carry; U += vj // 2 if j < m else 0; carry = (vj + ((K >> j) & 1)) // 2
        print('add %d operands + K=%d mod 2^%d: N=%d spectral bound %d  U(K)=%d' % (k, K, n, N, b, U), flush=True)
    elif mode == 'wtc':
        n, c, m = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        outs = [[((bin(x).count('1') + c) >> i) & 1 for x in range(1 << n)] for i in range(1, m + 1)]
        b, u = bound(n, outs); print('wt(%d bits)+%d bits 1..%d: spectral bound %d (u=%s)' % (n, c, m, b, bin(u)), flush=True)
