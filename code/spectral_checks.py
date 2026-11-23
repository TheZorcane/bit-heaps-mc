#!/usr/bin/env python3
"""spectral_checks.py -- reproducible checks for Sections 6, 7 and 12 of the paper.  Prints PASS lines; exits non-zero on failure.

 1. wt16: explicit 12-AND XAG for (weight of 16 bits mod 8), exhaustive check over all 2^16 inputs;
          weight of the truth table of e_4 (bit 2) = 28152 = 2^3 * 3519  ->  MC(e_4 on 16 bits) >= 16-1-3 = 12.
 2. ADD_k(n): the Walsh coefficient of the proof of Theorem 6.1 computed by BRUTE FORCE (no operator calculus) for
          small (k, n) equals 2^(N - sum M).
 3. constants: same for x_1+..+x_k + K (brute force), all K, small (k, n).
 4. SHA-256: exact MC of the block-model sums at n = 32 (formula values, proved by Theorem 6.1).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

# ---------------------------------------------------------------- 1. wt16 circuit
def wt16_circuit():
    """returns (gates, outs): wires 0..15 inputs; gate = ('x', a, b) | ('a', a, b) | ('n', a); FA = 1 AND."""
    g = []; n = [16]
    def new(op, *a): g.append((op,) + a); n[0] += 1; return n[0] - 1
    def fa(a, b, c):                      # maj = (a+c)(b+c)+c
        ac = new('x', a, c); bc = new('x', b, c); p = new('a', ac, bc); cy = new('x', p, c); s = new('x', ac, b); return s, cy
    def ha(a, b): return new('x', a, b), new('a', a, b)
    def column(bits):
        carries = []
        while len(bits) >= 3:
            s, c = fa(bits.pop(), bits.pop(), bits.pop()); bits.insert(0, s); carries.append(c)
        if len(bits) == 2:
            s, c = ha(bits.pop(), bits.pop()); bits.append(s); carries.append(c)
        return bits[0], carries
    s0, c1 = column(list(range(16))); s1, c2 = column(c1)
    s2 = c2[0]
    for c in c2[1:]: s2 = new('x', s2, c)
    return g, (s0, s1, s2)

def sim(g, outs, x):
    w = [(x >> i) & 1 for i in range(16)]
    for op in g:
        if op[0] == 'x': w.append(w[op[1]] ^ w[op[2]])
        elif op[0] == 'a': w.append(w[op[1]] & w[op[2]])
    return [w[o] for o in outs]

def check1():
    g, outs = wt16_circuit(); ands = sum(1 for op in g if op[0] == 'a'); bad = 0; wt_e4 = 0
    for x in range(1 << 16):
        w = bin(x).count('1'); r = sim(g, outs, x)
        if r != [w & 1, (w >> 1) & 1, (w >> 2) & 1]: bad += 1
        # e_4 straight from the definition: C(w, 4) mod 2
        e4 = (w * (w - 1) * (w - 2) * (w - 3) // 24) & 1
        assert e4 == (w >> 2) & 1
        wt_e4 += e4
    assert bad == 0 and ands == 12, (bad, ands)
    assert wt_e4 == 28152 and v2(wt_e4) == 3
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(os.environ.get('OUTDIR', here), 'wt16_mod8_12and.xag.txt'), 'w') as f:
        f.write('# spectral method: weight of 16 bits mod 8, 12 AND gates.  wires 0..15 = inputs; then one gate per line\n')
        for i, op in enumerate(g): f.write('%d = %s %s\n' % (16 + i, {'x': 'XOR', 'a': 'AND'}[op[0]], ' '.join(map(str, op[1:]))))
        f.write('outputs (bit0, bit1, bit2): %d %d %d\n' % outs)
    print('PASS 1: 12-AND XAG for wt16 mod 8 correct on all 65536 inputs; wt(e_4) = %d = 2^3 * %d  =>  MC >= 16 - 1 - 3 = 12' % (wt_e4, wt_e4 >> 3))

# ---------------------------------------------------------------- 2/3. brute-force Walsh coefficient of the proof
def Uc(k, m, K):
    v = 0; c = 0; tot = 0
    for j in range(m):
        v = k + c; tot += v // 2; c = (v + ((K >> j) & 1)) // 2
    return tot

def proof_signs(k, m, K):
    """signs of the proof of Theorem 6.1: e_j = c_{j+1} - c_j bits of column j are in the support of l, where c_j is
    the number of carries into column j of the FA network with the constant (c_0 = 0, c_{j+1} = floor((k_j + c_j + K_j)/2))."""
    e = []; c = 0
    for j in range(m):
        c2 = (k + c + ((K >> j) & 1)) // 2; assert 0 <= c2 - c <= k
        e.append(c2 - c); c = c2
    return e

def check23(cases):
    cnt = 0
    for k, n in cases:
        m = n - 1; N = k * m
        for K in range(1 << m):
            e = proof_signs(k, m, K)
            # variables: bit index = column * k + i ; sign-1 bits: the first e[j] of each column
            lmask = 0
            for j in range(m):
                for i in range(e[j]): lmask |= 1 << (j * k + i)
            W = 0
            for x in range(1 << N):
                T = K
                for j in range(m): T += bin((x >> (j * k)) & ((1 << k) - 1)).count('1') << j
                W += 1 - 2 * ((bin(x & lmask).count('1') + (T >> m)) & 1)
            target = N - Uc(k, m, K)
            assert abs(W) == 1 << target, (k, n, K, e, W, target)
            cnt += 1
    print('PASS 2/3: brute-force Walsh coefficient of the top sum bit of x_1+..+x_k+K at the proof\'s linear form is +-2^(N-U(K)) in all %d cases %s (all K)' % (cnt, cases))

def check4():
    from sha256_ref import K as SHA_K
    def M(k, n): return sum(k - -(-k // (1 << i)) for i in range(1, n))
    print('PASS 4: exact MC(ADD_k(32)) = sum_i (k - ceil(k/2^i)):', {k: M(k, 32) for k in range(2, 9)})
    for k in (1, 2, 3, 4, 5):
        tot = sum(Uc(k, 31, Kt & 0x7fffffff) for Kt in SHA_K); tot0 = 64 * Uc(k, 31, 0)
        vals = sorted(set(Uc(k, 31, Kt & 0x7fffffff) for Kt in SHA_K))
        print('        MC(x_1+..+x_%d + K_t mod 2^32): sum over the 64 SHA-256 round constants = %d (per round %s; without constant %d)' % (k, tot, vals, tot0 // 64))

if __name__ == '__main__':
    check1(); check23([(2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (4, 3), (4, 4), (5, 3), (6, 3), (7, 3)]); check4()
