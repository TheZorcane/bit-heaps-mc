#!/usr/bin/env python3
"""fsat.py -- the Fiber Lemma (F) at one level, as a finite SAT problem (real or abstracted from below).

Setting: Proposition 10.5 and Appendix B of the paper.  Concrete columns c = 0..t-1 with k_c bits; the carry entering
column 0 is K' with maximum Min.  Min = 0 and K' = 0: a real heap, column 0 is column 0 of the heap.
Min > 0: K' is an ABSTRACT carry: any function on the space with
   (a) 0 <= K' <= Min, K'(0) = Min;   (b) K' mod 2 affine;
   (c) dK(a+b) <= dK(a) + dK(b) + 1, dK = Min - K'            (Appendix B.2: true for every real carry K_i under P_i).
Unknowns: r 'lower' vectors (parts in all columns, values of K' on their span) and d 'fibre' vectors
supported in the top column only (on which K' and all lower columns are invariant).
Constraints: s-bit of every column and bit 1 of the top N are affine on the whole (r+d)-dim space (P_{j+1});
the fibre vectors are independent; K_top(a) < M_top for all a != 0 of the lower span (trivial top level set).
By Appendix B.4, (F) fails at a level  <=>  such a configuration exists for a real heap with (d, r) =
(d0 + i, M_top - i), d0 = k_top - M_next + 1, some i >= 0; and every real configuration at level j >= t + i0
restricts to an abstract one with Min = M_{i0}.  So UNSAT for all patterns => (F) at those levels.
usage: fsat.py Min k0,k1,..,k_top d r [--proof FILE.lrat] [--timeout S] [--fibre v1,v2,..] [--nosym]"""
import sys, subprocess, os, tempfile, time, itertools

def build(Min, ks, d, r, fibre=None, sym=True, greedy=False):
    t = len(ks); cl = []; nv = [0]
    def new(): nv[0] += 1; return nv[0]
    def add(*l): cl.append(l)
    def xor(a, b):
        o = new(); add(-a, -b, -o); add(a, b, -o); add(a, -b, o); add(-a, b, o); return o
    def onehot(n):
        h = [new() for _ in range(n)]; add(*h)
        for i in range(n):
            for j in range(i + 1, n): add(-h[i], -h[j])
        return h
    R = 1 << r; Dm = 1 << d
    g = [[[new() for _ in range(ks[c])] for _ in range(r)] for c in range(t)]
    fb = [[new() for _ in range(ks[t - 1])] for _ in range(d)]
    def spanvec(basis, n, width):
        out = [None] * (1 << n)
        for a in range(1, 1 << n):
            low = (a & -a).bit_length() - 1; rest = a & (a - 1)
            out[a] = basis[low] if rest == 0 else [xor(out[rest][i], basis[low][i]) for i in range(width)]
        return out
    if fibre:   # fix the fibre (list of 0/1 strings); used with the classification of isotropic fibres
        for i in range(d):
            for b in range(ks[t - 1]): add(fb[i][b] if fibre[i][b] == '1' else -fb[i][b])
    if sym:     # sound: coordinates of a column may be permuted; sort them (lower columns always, the top
                # column only when the fibre is not fixed) by their incidence vectors, non-increasing
        fibnf = bool(os.environ.get('FSAT_FIBNF')) and not fibre and d <= ks[t - 1]
        if fibnf:
            # Sound fibre normal form: the fibre F (dim d) has an information set; permute it to the first d
            # coordinates of the top column and row-reduce (only the span of the fibre vectors matters):
            # fibre = [I_d | *].  The lower vectors are arbitrary lifts, so fibre vectors may be added to
            # them: their top parts vanish on the first d coordinates.  The other k-d coordinates of the top
            # column may still be permuted, so they are sorted below.
            for i in range(d):
                for b in range(d): add(fb[i][b] if b == i else -fb[i][b])
            for i in range(r):
                for b in range(d): add(-g[t - 1][i][b])
        for c in range(t):
            if c == t - 1 and fibre: continue
            rows = [g[c][i] for i in range(r)] + (fb if c == t - 1 else [])
            for b in range(ks[c] - 1):
                if c == t - 1 and fibnf and b < d: continue
                eq = None
                for i, row in enumerate(rows):
                    x, y = row[b], row[b + 1]
                    if eq is None: add(x, -y)
                    else: add(-eq, x, -y)
                    if i < len(rows) - 1:
                        ne = new()
                        if eq is None: add(-ne, x, -y); add(-ne, -x, y); add(ne, -x, -y); add(ne, x, y)
                        else: add(-ne, eq); add(-ne, x, -y); add(-ne, -x, y); add(ne, -eq, -x, -y); add(ne, -eq, x, y)
                        eq = ne
    gz = [spanvec(g[c], r, ks[c]) for c in range(t)]; fz = spanvec(fb, d, ks[t - 1])
    def weight_onehot(bits, k):   # one-hot of the number of ONES of y = 1 + z, i.e. zeros of z; bits None => z = 0
        h = onehot(k + 1)
        if bits is None: add(h[k]); return h
        for pat in range(1 << k):
            add(*([(-bits[i] if (pat >> i) & 1 else bits[i]) for i in range(k)] + [h[k - bin(pat).count('1')]]))
        return h
    def affine(f, n):   # f: list of literals indexed by a in [0, 2^n): constrain a -> f(a) to be affine
        u = [None] * (1 << n)
        for a in range(1, 1 << n): u[a] = xor(f[a], f[0])
        for a in range(1, 1 << n):
            rest = a & (a - 1)
            if rest:
                x, y, o = u[rest], u[a & -a], u[a]
                add(-x, -y, -o); add(x, y, -o); add(x, -y, o); add(-x, y, o)
    # abstract / zero carry into column 0
    hK = [onehot(Min + 1) for _ in range(R)]; add(hK[0][Min])
    if Min > 0:
        par = []
        for a in range(R):
            p = new(); par.append(p)
            for v in range(Min + 1): add(-hK[a][v], p if v & 1 else -p)
        affine(par, r)
        for a in range(R):
            for b in range(a + 1, R):
                for va in range(Min + 1):
                    for vb in range(Min + 1):
                        for vc in range(Min + 1):
                            if (Min - vc) > (Min - va) + (Min - vb) + 1: add(-hK[a][va], -hK[b][vb], -hK[a ^ b][vc])
    M = Min
    for c in range(t - 1):   # lower concrete columns: depend on the lower span only
        k = ks[c]; Nmax = M + k; hN = []; sb = []
        for a in range(R):
            hw = weight_onehot(gz[c][a], k); h = onehot(Nmax + 1); s = new()
            for v in range(M + 1):
                for w in range(k + 1): add(-hK[a][v], -hw[w], h[v + w])
            for n in range(Nmax + 1): add(-h[n], s if n & 1 else -s)
            hN.append(h); sb.append(s)
        affine(sb, r)
        Mn = Nmax // 2; hK2 = []
        for a in range(R):
            h = onehot(Mn + 1)
            for n in range(Nmax + 1): add(-hN[a][n], h[n >> 1])
            hK2.append(h)
        hK = hK2; M = Mn
    for a in range(1, R): add(-hK[a][M])            # trivial top level set on the lower span
    if greedy:
        # Sound basis normalisation: the constraints only depend on the span L of the lower vectors, so the
        # basis may be chosen greedily: e_0 maximises K_top on L minus 0, e_i maximises K_top on L minus
        # span(e_0..e_{i-1}).  (K_top is invariant under the coordinate permutations used for sorting, so
        # both normal forms can be imposed together.)
        for i in range(r):
            for a in range(1 << i, R):              # a not in span(e_0..e_{i-1})  <=>  a >= 2^i
                if a == (1 << i): continue
                for v in range(M + 1):
                    for u in range(v + 1, M + 1): add(-hK[1 << i][v], -hK[a][u])
    for a in range(1, Dm): add(*fz[a])              # fibre vectors independent
    k = ks[t - 1]; Nmax = M + k; S = [None] * (R * Dm); C = [None] * (R * Dm)
    for a in range(R):
        for b in range(Dm):
            if a == 0 and b == 0: bits = None
            elif a == 0: bits = fz[b]
            elif b == 0: bits = gz[t - 1][a]
            else: bits = [xor(gz[t - 1][a][i], fz[b][i]) for i in range(k)]
            hw = weight_onehot(bits, k); s = new(); cc = new()
            for v in range(M + 1):
                for w in range(k + 1):
                    n = v + w
                    add(-hK[a][v], -hw[w], s if n & 1 else -s); add(-hK[a][v], -hw[w], cc if (n >> 1) & 1 else -cc)
            S[a | (b << r)] = s; C[a | (b << r)] = cc
    affine(S, r + d); affine(C, r + d)
    return nv[0], cl, dict(g=g, fb=fb, M_top=M, Nmax=Nmax)

def run(Min, ks, d, r, proof=None, timeout=None, fibre=None, sym=True, greedy=None):
    if greedy is None: greedy = bool(os.environ.get('FSAT_GREEDY'))
    n, cl, info = build(Min, ks, d, r, fibre, sym, greedy)
    fn = proof.replace('.lrat', '.cnf') if proof else tempfile.mktemp(suffix='.cnf')
    with open(fn, 'w') as f:
        f.write('p cnf %d %d\n' % (n, len(cl))); f.write('\n'.join(' '.join(map(str, c)) + ' 0' for c in cl) + '\n')
    cmd = ['cadical', '-q'] + (['-t', str(timeout)] if timeout else [])
    plain = [] if os.environ.get('FSAT_NOPLAIN') else ['--plain']   # the strict checker is the trust anchor either way
    cmd += plain + ['--lrat=true', '--binary=false', fn, proof] if proof else [fn]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if not proof: os.unlink(fn)
    out = {10: 'sat', 20: 'unsat'}.get(res.returncode, 'unknown'); model = None
    if out == 'sat':
        val = {}
        for line in res.stdout.splitlines():
            if line.startswith('v'):
                for tk in line.split()[1:]: val[abs(int(tk))] = int(tk) > 0
        model = dict(lower=[[''.join('1' if val.get(x) else '0' for x in info['g'][c][i]) for c in range(len(ks))] for i in range(r)],
                     fibre=[''.join('1' if val.get(x) else '0' for x in row) for row in info['fb']])
    return out, model, info

if __name__ == '__main__':
    raw = sys.argv[1:]; args = []; i = 0; proof = None; to = None; fibre = None
    while i < len(raw):
        if raw[i] == '--proof': proof = raw[i + 1]; i += 2
        elif raw[i] == '--timeout': to = int(raw[i + 1]); i += 2
        elif raw[i] == '--fibre': fibre = raw[i + 1].split(','); i += 2
        elif raw[i].startswith('--'): i += 1
        else: args.append(raw[i]); i += 1
    Min = int(args[0]); ks = [int(x) for x in args[1].split(',')]; d = int(args[2]); r = int(args[3])
    t0 = time.time(); out, model, info = run(Min, ks, d, r, proof, to, fibre, '--nosym' not in raw)
    print('Min=%d columns=%s  M_top=%d Nmax_top=%d  pattern (d=%d, r=%d)%s: %s (%.1fs)' % (Min, ks, info['M_top'], info['Nmax'], d, r, ' fibre=%s' % fibre if fibre else '', out, time.time() - t0))
    if model: print('   lower vectors (per column):', model['lower'], ' fibre:', model['fibre'])
