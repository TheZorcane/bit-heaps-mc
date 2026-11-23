#!/usr/bin/env python3
"""mc_tables.py -- reproduces every numeric table of the paper from the closed formulas (pure Python 3).

Prints, and asserts where a statement is checkable:
  T1  MC(x_1+...+x_k mod 2^n) = sum_{i=1}^{n-1} (k - ceil(k/2^i)) for k = 2..8, small n and n = 32,
      with the closed forms in n, and the degree lower bound deg - 1 for comparison.
  T2  identity U(k, n) == T(k, n) = (k-1)(n-1) - sum_{r=1}^{n-1} floor((k-1)/2^r)  (the published upper bound,
      see Related work) for 1 <= k <= 300, 1 <= n <= 64.
  T3  addition of a constant: U(K) for x + y + K mod 2^n (closed form (n-1) + max(0, n-2-b)) checked for n <= 12,
      all K; and the cost of the 64 SHA-256 round constants inside k-operand sums at n = 32.
  T4  MC(weight of n bits mod 8) = floor(n/2) + floor(n/4), n = 1..40 (= U of the heap [n, 0]).
  T5  the block-model AND counts of the SHA-256 compression sums (stand-alone blocks only).
usage: python3 mc_tables.py            (about 1 s)
"""
import sys
from math import comb


def U_heap(profile, K=0):
    """AND count of the full-adder network with the constant consumed last (Lemma 4.1)."""
    c = 0; U = 0
    for j, kj in enumerate(profile):
        v = kj + c
        U += v // 2
        c = (v + ((K >> j) & 1)) // 2
    return U


def mc_add(k, n, K=0):
    if n <= 1:
        return 0
    return U_heap([k] * (n - 1), K & ((1 << (n - 1)) - 1))


def formula(k, n):
    return sum(k - -(-k // (1 << i)) for i in range(1, n))


def T_pub(k, n):
    return (k - 1) * (n - 1) - sum((k - 1) >> r for r in range(1, n))


def degree_top(k, n):
    """algebraic degree of the top sum bit of x_1+..+x_k mod 2^n:
    max sum c_j subject to sum c_j 2^j = 2^(n-1), 0 <= c_j <= k  (greedy from the lowest column)."""
    # DP over the carry q_j = (sum_{i<j} c_i 2^i) / 2^j: columns j < n-1 need c_j + q_j even,
    # column n-1 needs c_{n-1} + q_{n-1} = 1.
    dp = {0: 0}
    for j in range(n - 1):
        nd = {}
        for q, cnt in dp.items():
            for c in range(k + 1):
                if (c + q) % 2 == 0:
                    q2 = (c + q) // 2
                    if nd.get(q2, -1) < cnt + c:
                        nd[q2] = cnt + c
        dp = nd
    best = 0
    for q, cnt in dp.items():
        c = 1 - q
        if 0 <= c <= k:
            best = max(best, cnt + c)
    return best


def sha256_K():
    """the 64 SHA-256 round constants: first 32 bits of the fractional parts of the cube roots of the
    first 64 primes (integer arithmetic)."""
    primes = []; p = 2
    while len(primes) < 64:
        if all(p % q for q in primes if q * q <= p):
            primes.append(p)
        p += 1
    out = []
    for p in primes:
        # floor(cbrt(p) * 2^32) by integer Newton on x^3 <= p * 2^96
        t = p << 96; x = 1 << ((t.bit_length() + 2) // 3)
        while True:
            y = (2 * x + t // (x * x)) // 3
            if y >= x:
                break
            x = y
        while (x + 1) ** 3 <= t:
            x += 1
        while x ** 3 > t:
            x -= 1
        out.append(x & 0xffffffff)
    assert out[0] == 0x428a2f98 and out[63] == 0xc67178f2
    return out


IV = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]


def main():
    ok = True
    print('T1  exact MC of k-operand addition mod 2^n  (Theorem 1)')
    print('     n:' + ''.join('%6d' % n for n in range(1, 9)) + '    n=32   closed form       degree-1 at n=32')
    closed = {2: 'n-1', 3: '2n-3', 4: '3n-4', 5: '4n-7 (n>=3)', 6: '5n-8 (n>=3)', 7: '6n-10 (n>=3)', 8: '7n-11 (n>=4)'}
    for k in range(2, 9):
        row = [mc_add(k, n) for n in range(1, 9)]
        for n in range(1, 40):
            assert mc_add(k, n) == formula(k, n)
        print('  k=%d:' % k + ''.join('%6d' % v for v in row) + '%8d   %-16s %6d' % (formula(k, 32), closed[k], degree_top(k, 32) - 1))
    # closed forms
    cf = {2: lambda n: n - 1, 3: lambda n: 2 * n - 3, 4: lambda n: 3 * n - 4, 5: lambda n: 4 * n - 7,
          6: lambda n: 5 * n - 8, 7: lambda n: 6 * n - 10, 8: lambda n: 7 * n - 11}
    lo = {2: 1, 3: 2, 4: 2, 5: 3, 6: 3, 7: 3, 8: 4}
    for k, f in cf.items():
        for n in range(lo[k], 200):
            assert formula(k, n) == f(n), (k, n)
    vals32 = [formula(k, 32) for k in range(2, 9)]
    assert vals32 == [31, 61, 92, 121, 152, 182, 213], vals32
    print('     n = 32, k = 2..8: %s   [asserted]' % vals32)
    print('     MF-109 open cases: A(6,3) = %d, A(9,3) = %d' % (formula(6, 3), formula(9, 3)))

    bad = [(k, n) for k in range(1, 301) for n in range(1, 65) if formula(k, n) != T_pub(k, n)]
    print('\nT2  U(k,n) == T(k,n) for 1<=k<=300, 1<=n<=64: %s' % ('PASS' if not bad else 'FAIL %s' % bad[:5]))
    ok &= not bad

    print('\nT3  constants')
    bad = 0
    for n in range(2, 13):
        for K in range(1 << n):
            Kr = K & ((1 << (n - 1)) - 1)
            bits = [i for i in range(1, n - 1) if (Kr >> i) & 1]
            cfK = (n - 1) + (max(0, n - 2 - bits[0]) if bits else 0)
            if mc_add(2, n, K) != cfK:
                bad += 1
    print('     x + y + K mod 2^n: U(K) = (n-1) + max(0, n-2-b), b = lowest set bit of K in 1..n-2, all K, n <= 12: %s' % ('PASS' if not bad else 'FAIL'))
    ok &= not bad
    Ks = sha256_K()
    for k in (1, 2, 3, 4, 5):
        per = [mc_add(k, 32, Kt) for Kt in Ks]
        base = mc_add(k, 32)
        print('     %d variable operand(s) + K_t mod 2^32: sum over 64 rounds = %5d, per round %d..%d, without constant %d, constant costs %d..%d'
              % (k, sum(per), min(per), max(per), base, min(per) - base, max(per) - base))
    exp = {2: 3778, 3: 5677, 4: 7623, 5: 9494}
    for k, v in exp.items():
        assert sum(mc_add(k, 32, Kt) for Kt in Ks) == v

    print('\nT4  MC(weight of n bits mod 8) = floor(n/2) + floor(n/4)  (Theorem 4)')
    row = []
    for n in range(1, 41):
        v = U_heap([n, 0])
        assert v == n // 2 + n // 4
        row.append(v)
    print('     n = 1..40: %s' % row)
    print('     n = 16: %d (e_4 on 16 bits: weight of truth table = %d = 2^3 * %d)' % (U_heap([16, 0]),
          sum(comb(16, w) for w in range(17) if comb(w, 4) & 1), sum(comb(16, w) for w in range(17) if comb(w, 4) & 1) // 8))

    print('\nT5  SHA-256 compression: AND counts of the multi-operand sums as stand-alone blocks (n = 32)')
    sched = 48 * mc_add(4, 32)
    t1 = sum(mc_add(4, 32, Kt) for Kt in Ks)           # h + Sigma1 + Ch + W_t + K_t
    ap = 64 * mc_add(3, 32)                             # T1 + Sigma0 + Maj
    ep = 64 * mc_add(2, 32)                             # d + T1
    ff = sum(mc_add(1, 32, v) for v in IV)              # feed-forward x + IV_k
    print('     message schedule, 48 words x 4 operands     : %d' % sched)
    print('     T1 = h+S1+Ch+W_t+K_t, 64 rounds             : %d' % t1)
    print("     a' = T1+S0+Maj (3 operands), 64 rounds      : %d" % ap)
    print("     e' = d+T1 (2 operands), 64 rounds           : %d" % ep)
    print('     feed-forward x + IV_k, 8 words              : %d' % ff)
    print('     total of the sums as separate blocks         : %d   (Ch and Maj add 1 AND per bit each: %d)' % (sched + t1 + ap + ep + ff, 2 * 64 * 32))
    print('\n%s' % ('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
