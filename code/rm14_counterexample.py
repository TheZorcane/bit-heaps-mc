#!/usr/bin/env python3
"""rm14_counterexample.py -- explicit flats through the all-ones point that violate the Fiber Lemma (F) of Section 10
and the flat bound (Theorem 10.7).  No SAT, no search: the codes are written down and the definition is checked by
brute force (codesat.check, plus a direct weight computation here).

(1) heap [16], m = 2 (weight of 16 bits mod 8):  D = RM(1,4), dim 5 > 16 - (8+4) = 4.
(2) ADD_16(3) = heap [16,16], m = 2:  D = RM(1,4) (column 0) x E (column 1), E = e8+e8 doubly even
    self-dual [16,8]; dim 13 > 32 - (8+12) = 12.  T(1+z) = 48 - w(a) - 2 w(b) = 0 mod 8 on the whole flat.
Nothing about circuits is claimed: only that Lemma 10.1 at the point 1 cannot prove MC >= sum M here.
Also prints flat method's quantities at level j = 1 of (1), showing (F) itself is violated."""
from codesat import check, M_sum
import itertools
pts = list(itertools.product([0, 1], repeat=4))
rm14 = [[1] * 16] + [[p[i] for p in pts] for i in range(4)]
e8 = [[1,1,1,1,0,0,0,0],[0,0,1,1,1,1,0,0],[0,0,0,0,1,1,1,1],[1,0,1,0,1,0,1,0]]
E = [r + [0] * 8 for r in e8] + [[0] * 8 + r for r in e8]
def span(B):
    out = []
    for a in range(1 << len(B)):
        v = [0] * len(B[0])
        for i in range(len(B)):
            if (a >> i) & 1: v = [x ^ y for x, y in zip(v, B[i])]
        out.append(v)
    return out
assert sorted(set(sum(v) for v in span(rm14))) == [0, 8, 16]
assert all(sum(v) % 4 == 0 for v in span(E)) and len(set(map(tuple, span(E)))) == 256
ok, d = check([16], 2, rm14)
print('(1) heap [16], m=2: RM(1,4) valid =', ok, 'dim', d, ' conjectured max', 16 - M_sum([16], 2),
      ' codim', 16 - d, '< sumM =', M_sum([16], 2))
assert ok and d == 5
B = [r + [0] * 16 for r in rm14] + [[0] * 16 + r for r in E]
ok, d = check([16, 16], 2, B)
print('(2) ADD_16(3) = heap [16,16], m=2: valid =', ok, 'dim', d, ' conjectured max', 32 - M_sum([16, 16], 2),
      ' codim', 32 - d, '< sumM =', M_sum([16, 16], 2))
assert ok and d == 13
assert all((48 - sum(v[:16]) - 2 * sum(v[16:])) % 8 == 0 for v in span(B))
print('    T = 0 mod 8 on all 2^13 points of the flat')
# (F) at level j = 1 of (1): heap [16, 0]; U_1 = U_2 = RM(1,4), K_1 = floor(w/2)
U = span(rm14); K = {tuple(v): sum(v) // 2 for v in U}
inv = [v for v in U if all(K[tuple(x ^ y for x, y in zip(u, v))] == K[tuple(u)] for u in U)]
r1 = 5 - (len(inv).bit_length() - 1)
print('(F) at j=1 for (1): d_1 = 0, k_1 = 0, M_1 = 8, M_2 = 4, r_1 =', r1,
      ': bound k_1 - M_2 + max(0, M_1 - r_1) =', 0 - 4 + max(0, 8 - r1), '< d_1 = 0  -> (F) fails')
