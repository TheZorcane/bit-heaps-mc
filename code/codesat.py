#!/usr/bin/env python3
"""codesat.py -- flats through the all-ones point of a bit heap, as a SAT problem.

Question decided:  is there a linear code D of dimension d in F_2^(k_0+...+k_{L-1}) such that all bits
0..m of   T(1+z) = c + sum_i 2^i * (k_i - w(z_i))   are affine functions of z in D ?
(U = 1 + D is then a flat through the all-ones point on which the heap outputs s_0..s_{m-1}, C_m are affine;
 hypothesis P_m of Section 10.  Flat statement: d <= sum k_i - (M_1+..+M_m).)

usage: codesat.py PROFILE m d [offset] [--nosym] [--timeout S] [--proof FILE]
  PROFILE = k0,k1,...   (columns of weight 1,2,4,..), m = number of affine output bits minus 1
SAT  -> prints a basis, re-verified by brute force straight from the definition (function check()).
UNSAT-> evidence only unless --proof is given and the LRAT file is checked with verifier/lrat_check.py.
The CNF adds two sound symmetry breakers (unless --nosym): coordinates inside a heap column are sorted
(the heap is invariant under permuting a column), nothing else.
"""
import sys, subprocess, itertools, os, tempfile, time

class CNF:
    def __init__(s): s.n = 0; s.cl = []
    def new(s): s.n += 1; return s.n
    def add(s, *lits): s.cl.append(lits)
    def xor(s, a, b):
        o = s.new(); s.add(-a, -b, -o); s.add(a, b, -o); s.add(a, -b, o); s.add(-a, b, o); return o
    def fa(s, a, b, c):
        sm = s.xor(s.xor(a, b), c); cy = s.new()
        s.add(-a, -b, cy); s.add(-a, -c, cy); s.add(-b, -c, cy); s.add(a, b, -cy); s.add(a, c, -cy); s.add(b, c, -cy)
        return sm, cy
    def ha(s, a, b):
        sm = s.xor(a, b); cy = s.new(); s.add(-a, -b, cy); s.add(a, -cy); s.add(b, -cy); return sm, cy

def build(prof, m, d, off=0, sym=True, sig=None, notop=False):
    L = len(prof); cols = [(i, j) for i in range(L) for j in range(prof[i])]; nc = len(cols)
    F = CNF(); TRUE = F.new(); F.add(TRUE)
    b = [[F.new() for _ in cols] for _ in range(d)]
    z = {0: None}; u = {}
    piv = set()
    if sig:
        # Normal form (sound, see header of sweep.py): D^(g) = {z in D : columns < g are zero}; rho_g =
        # dim of the projection of D^(g) on column g.  Basis = groups g = 0..L-1 of rho_g vectors; a vector
        # of group g is zero in columns < g; after permuting the coordinates of column g and row reduction,
        # group g restricted to the first rho_g coordinates of column g is the identity and the groups
        # g' < g are zero there.
        assert sum(sig) == d and len(sig) == L
        grp = [g for g in range(L) for _ in range(sig[g])]; first = {}
        for r, g in enumerate(grp): first.setdefault(g, r)
        for r, g in enumerate(grp):
            for c, (i, j) in enumerate(cols):
                if i < g: F.add(-b[r][c])
                elif j < sig[i]:
                    piv.add(c)
                    if i == g: F.add(b[r][c] if j == r - first[g] else -b[r][c])
                    elif grp[r] < i: F.add(-b[r][c])
    def tbits(zv):  # bits 0..m of off + sum 2^i * #(zeros of z in column i); zv None = zero vector
        heap = [[] for _ in range(width + 1)]
        for t in range(width):
            if (off >> t) & 1: heap[t].append(TRUE)
        for idx, (i, j) in enumerate(cols):
            if i < width: heap[i].append(TRUE if zv is None else -zv[idx])
        out = []
        for t in range(width):
            h = heap[t]
            while len(h) >= 3:
                a, bb, c = h.pop(), h.pop(), h.pop(); sm, cy = F.fa(a, bb, c); h.append(sm); heap[t + 1].append(cy)
            if len(h) == 2:
                a, bb = h.pop(), h.pop(); sm, cy = F.ha(a, bb); h.append(sm); heap[t + 1].append(cy)
            out.append(h[0] if h else -TRUE)
        return out
    T0 = sum((1 << i) * prof[i] for i in range(L)) + off
    width = max(m + 1, T0.bit_length()) if notop else m + 1
    for a in range(1, 1 << d):
        low = (a & -a).bit_length() - 1; rest = a & (a - 1)
        if rest == 0: z[a] = b[low]
        else: z[a] = [F.xor(z[rest][c], b[low][c]) for c in range(nc)]
        F.add(*z[a])                                   # independence: every combination is non-zero
        t = tbits(z[a])
        u[a] = [t[j] if not (T0 >> j) & 1 else -t[j] for j in range(m + 1)]   # u = bit xor bit(T0)
        if notop:   # K_m(1+z) < M_m for every z != 0 in D: the bits m.. of T differ from those of T0
            F.add(*[(-t[j] if (T0 >> j) & 1 else t[j]) for j in range(m, width)])
        if rest:
            for j in range(m + 1):
                x, y, o = u[rest][j], u[1 << low][j], u[a][j]
                F.add(-x, -y, -o); F.add(x, y, -o); F.add(x, -y, o); F.add(-x, y, o)
    if sym:   # coordinates of one heap column in non-increasing lexicographic order (as d-bit columns)
        for c in range(nc - 1):
            if cols[c][0] != cols[c + 1][0] or c in piv or (c + 1) in piv: continue
            eq = TRUE
            for i in range(d):
                x, y = b[i][c], b[i][c + 1]
                F.add(-eq, x, -y)                      # while equal so far: x >= y
                if i < d - 1:
                    ne = F.new()                       # ne <-> eq and (x == y)
                    F.add(-ne, eq); F.add(-ne, x, -y); F.add(-ne, -x, y); F.add(ne, -eq, -x, -y); F.add(ne, -eq, x, y)
                    eq = ne
    return F, b, cols

def check(prof, m, basis, off=0):
    """brute force from the definition; basis = list of 0/1 lists.  Returns (ok, dim)."""
    L = len(prof); cols = [(i, j) for i in range(L) for j in range(prof[i])]
    d = len(basis); mask = (1 << (m + 1)) - 1
    def T(zv): return (off + sum((1 << i) * (1 - zv[c]) for c, (i, j) in enumerate(cols))) & mask
    T0 = T([0] * len(cols)); seen = set()
    lam = [T(bv) ^ T0 for bv in basis]
    for a in range(1 << d):
        zv = [0] * len(cols); l = 0
        for i in range(d):
            if (a >> i) & 1: zv = [p ^ q for p, q in zip(zv, basis[i])]; l ^= lam[i]
        if a and not any(zv): return False, d
        if T(zv) ^ T0 != l: return False, d
    return True, d

def M_sum(prof, m, off=0):
    M = off; tot = 0
    for j in range(m):
        M = (M + (prof[j] if j < len(prof) else 0)) // 2; tot += M
    return tot

def solve(prof, m, d, off=0, sym=True, timeout=None, proof=None, keep=None, sig=None, notop=False):
    F, b, cols = build(prof, m, d, off, sym, sig, notop)
    fn = keep or tempfile.mktemp(suffix='.cnf')
    with open(fn, 'w') as f:
        f.write('p cnf %d %d\n' % (F.n, len(F.cl)))
        f.write('\n'.join(' '.join(map(str, c)) + ' 0' for c in F.cl) + '\n')
    cmd = ['cadical', '-q']
    if timeout: cmd += ['-t', str(int(timeout))]
    if proof: cmd += ['--plain', '--lrat=true', '--binary=false', fn, proof]
    else: cmd += [fn]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if not keep: os.unlink(fn)
    if r.returncode == 20: return 'unsat', None
    if r.returncode != 10: return 'unknown', None
    val = {}
    for line in r.stdout.splitlines():
        if line.startswith('v'):
            for t in line.split()[1:]:
                v = int(t); val[abs(v)] = v > 0
    basis = [[1 if val.get(x, False) else 0 for x in row] for row in b]  # cadical may omit a variable; model is re-checked below
    ok, _ = check(prof, m, basis, off); assert ok, 'model failed brute-force check'
    return 'sat', basis

if __name__ == '__main__':
    raw = sys.argv[1:]; args = []; i = 0
    while i < len(raw):
        if raw[i] in ('--timeout', '--proof'): i += 2
        elif raw[i].startswith('--'): i += 1
        else: args.append(raw[i]); i += 1
    prof = [int(x) for x in args[0].split(',')]; m = int(args[1]); d = int(args[2]); off = int(args[3]) if len(args) > 3 else 0
    opt = sys.argv[1:]
    to = int(opt[opt.index('--timeout') + 1]) if '--timeout' in opt else None
    pf = opt[opt.index('--proof') + 1] if '--proof' in opt else None
    t0 = time.time(); res, basis = solve(prof, m, d, off, '--nosym' not in opt, to, pf, pf and pf.replace('.lrat', '.cnf'))
    nv = sum(prof); bound = nv - M_sum(prof, m, off)
    print('profile %s m=%d offset=%d: vars=%d sumM=%d conjectured max dim=%d; dim %d: %s (%.1fs)' %
          (prof, m, off, nv, M_sum(prof, m, off), bound, d, res, time.time() - t0))
    if basis:
        for row in basis: print('  ', ''.join(map(str, row)))
