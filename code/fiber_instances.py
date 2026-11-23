#!/usr/bin/env python3
"""fiber_instances.py -- all SAT instances needed for "the Fiber Lemma (F) holds at every level of the uniform
heap with k bits per column" (=> MC(ADD_k(n)) = sum_j M_j for all n, Proposition 10.3 of the paper).

Levels and instances (t = number of concrete columns, default 2):
  level j, 1 <= j <= t-1 : real heap, columns k^(j+1), Min = 0;
  level j >= t           : carry K_{j-t+1} abstract, Min = M_{j-t+1}, columns k^t.  M_i is constant (= k-1) for
                           i >= i* = ceil(log2 k), so the levels j >= i* + t - 1 are ONE instance family.
  (level 0 needs nothing: d_0 <= ceil(k/2) = k - M_1 by isotropy, condition (c1) of Appendix A.)
Patterns at a level with carry maximum M_j:  (d, r) = (d0 + i, M_j - i), d0 = k - M_{j+1} + 1, i >= 0,
  d <= ceil(k/2), r >= 0  (Appendix B.4).
usage: fiber_instances.py k [--t T] [--cert OUTDIR] [--timeout S]
  without --cert: plain cadical runs (evidence).  With --cert: CaDiCaL --plain + LRAT, checked by the strict
  verifier/lrat_check.py; proofs are deleted after checking, hashes are kept in OUTDIR/fproof_k<k>.json."""
import sys, os, json, hashlib, time
sys.dont_write_bytecode = True
import fsat

def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for blk in iter(lambda: f.read(1 << 20), b''): h.update(blk)
    return h.hexdigest()

def instances(k, t):
    M = [0]
    while len(M) < 3 or M[-1] != M[-2]: M.append((M[-1] + k) // 2)
    istar = len(M) - 2            # M_i = k-1 for i >= istar
    out = []; j = 1
    while True:
        i0 = max(0, j - t + 1); cols = [k] * (j - i0 + 1)
        Mi = lambda i: M[min(i, len(M) - 1)]
        Min = Mi(i0) if i0 > 0 else 0; Mj = Mi(j); d0 = k - Mi(j + 1) + 1
        pats = [(d0 + i, Mj - i) for i in range(0, Mj + 1) if d0 + i <= (k + 1) // 2]
        stable = i0 >= istar
        out.append(dict(level=('>=%d' % j) if stable else str(j), Min=Min, cols=cols, pats=pats))
        if stable: break
        j += 1
    return out, M

if __name__ == '__main__':
    raw = sys.argv[1:]; k = int(raw[0])
    t = int(raw[raw.index('--t') + 1]) if '--t' in raw else 2
    cert = raw[raw.index('--cert') + 1] if '--cert' in raw else None
    to = int(raw[raw.index('--timeout') + 1]) if '--timeout' in raw else None
    inst, M = instances(k, t); print('k=%d  M_j = %s (then constant)  t=%d' % (k, M[1:-1], t), flush=True)
    if cert:
        os.makedirs(cert, exist_ok=True)
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "verifier"))
        import lrat_check
    rec = []; allok = True
    for it in inst:
        for (d, r) in it['pats']:
            t0 = time.time(); e = dict(level=it['level'], Min=it['Min'], cols=it['cols'], d=d, r=r)
            if cert:
                pf = os.path.join(cert, 'f_k%d_Min%d_c%d_d%d_r%d.lrat' % (k, it['Min'], len(it['cols']), d, r)); cnf = pf.replace('.lrat', '.cnf')
                res, model, info = fsat.run(it['Min'], it['cols'], d, r, pf, to)
                e.update(result=res, solve_s=round(time.time() - t0, 1))
                if res == 'unsat':
                    ok, msg = lrat_check.check(cnf, pf)
                    e.update(lrat_strict_check=bool(ok), lrat_msg=msg, cnf_sha256=sha(cnf), proof_sha256=sha(pf), proof_bytes=os.path.getsize(pf))
                    allok &= bool(ok)
                else: allok = False
                for p in (cnf, pf):
                    if os.path.exists(p): os.unlink(p)
            else:
                res, model, info = fsat.run(it['Min'], it['cols'], d, r, None, to)
                e.update(result=res, solve_s=round(time.time() - t0, 1)); allok &= (res == 'unsat')
                if model: e['model'] = model
            rec.append(e); print(e, flush=True)
    print('k=%d: %s' % (k, 'ALL INSTANCES UNSAT' + (' AND LRAT-CHECKED' if cert else ' (solver verdicts only)') if allok else 'NOT ALL UNSAT'))
    if cert:
        with open(os.path.join(cert, 'fproof_k%d_t%d.json' % (k, t)), 'w') as f: json.dump(dict(k=k, t=t, M=M, all_ok=allok, instances=rec), f, indent=1)
