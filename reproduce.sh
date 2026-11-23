#!/bin/sh
# Reproduce the computations of "Exact multiplicative complexity of multi-operand modular addition"
# (Section 16 of the paper lists which computations are reproduced here and which are not).
#   sh reproduce.sh          quick mode (about 75 seconds on a laptop, 1 thread)
#   sh reproduce.sh full     also the k = 6 instance list (strict LRAT check) and the tightness certificates
# Requirements: Python 3 (standard library only), a C compiler (cc), CaDiCaL 3.x on PATH as `cadical`
# (only for the SAT/LRAT steps).  Outputs go to ./out ; a summary with PASS/FAIL per step is printed at the end.
set -u
MODE=${1:-quick}
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE"
OUT="$HERE/out"; mkdir -p "$OUT" "$OUT/bin"
export PYTHONPATH="$HERE/verifier" VERIFIER_DIR="$HERE/verifier" OUTDIR="$OUT" PYTHONDONTWRITEBYTECODE=1
SUMMARY="$OUT/summary.txt"; : > "$SUMMARY"
step() {  # step NAME EXPECTED_PATTERN COMMAND...
  name=$1; pat=$2; shift 2
  t0=$(date +%s)
  if "$@" > "$OUT/$name.log" 2>&1 && grep -q -- "$pat" "$OUT/$name.log"; then r=PASS; else r=FAIL; fi
  t1=$(date +%s)
  printf '%-28s %s  (%ss)\n' "$name" "$r" $((t1 - t0)) | tee -a "$SUMMARY"
}

cc -O2 -o "$OUT/bin/walsh"  code/mc_addition_walsh_check.c
cc -O2 -o "$OUT/bin/flats"  code/flat_enumerator.c
cc -O2 -o "$OUT/bin/jtree"  code/joint_tree_bound.c
cc -O2 -o verifier/vendor/lrat-check verifier/vendor/lrat-check.c 2>/dev/null
cc -O2 -o verifier/vendor/drat-trim  verifier/vendor/drat-trim.c 2>/dev/null

# 1. tables (Theorem 1 values, identity with the published upper bound, constants, weight mod 8, SHA-256 blocks)
step tables "ALL CHECKS PASS" python3 code/mc_tables.py

# 2. exact Walsh spectra: spectral lower bound == full-adder upper bound (Theorems 1-4, MF-109 cases)
walsh_all() {
  B="$OUT/bin/walsh"; fail=0
  for kn in "2 2" "2 3" "2 6" "2 12" "3 2" "3 3" "3 5" "3 8" "4 3" "4 5" "4 7" "5 3" "5 4" "5 5" \
            "6 3" "6 4" "7 3" "7 4" "8 3" "9 3" "10 3" "11 3" "12 3"; do
    $B add $kn -t || fail=1
  done
  for K in 0 1 2 3 4 5 6 7; do $B add 3 4 $K -t || fail=1; $B add 2 4 $K -t || fail=1; done
  for K in 0 5 10 15 21 27 31; do $B add 2 6 $K -t || fail=1; done
  for n in 4 7 8 10 14 15 16 17 18 20 22; do $B heap $n,0 || fail=1; done
  $B heap 7,0 1 || fail=1; $B heap 15,0 1 || fail=1
  $B heap 14,1 || fail=1; $B heap 5,5,5,5 || fail=1; $B heap 3,3,3,3,3 || fail=1
  [ $fail = 0 ] && echo "WALSH ALL MATCH"
}
step walsh_spectra "WALSH ALL MATCH" walsh_all

# 2b. Theorem 8.1: every two-column heap (k_0, k_1) with k_0, k_1 <= 12; weight of n bits mod 16 for n <= 21
twolevel_all() {
  B="$OUT/bin/walsh"; fail=0; cnt=0
  for a in 0 1 2 3 4 5 6 7 8 9 10 11 12; do for b in 0 1 2 3 4 5 6 7 8 9 10 11 12; do
    [ $((a + b)) -gt 0 ] || continue
    $B heap $a,$b || fail=1; cnt=$((cnt + 1))
  done; done
  [ $fail = 0 ] && echo "TWO-LEVEL GRID: $cnt heaps, ALL MATCH"
}
step twolevel_grid "TWO-LEVEL GRID: 168 heaps, ALL MATCH" twolevel_all
wt16_all() {
  B="$OUT/bin/walsh"; fail=0
  for n in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21; do $B heap $n,0,0 || fail=1; done
  [ $fail = 0 ] && echo "WEIGHT MOD 16 n<=21 ALL MATCH"
}
step weight_mod16 "WEIGHT MOD 16 n<=21 ALL MATCH" wt16_all

# 3. proof's explicit Walsh coefficient by brute force, 12-AND circuit for weight of 16 bits mod 8, round constants
step spectral_checks "PASS 4" python3 code/spectral_checks.py
step walsh_selftest "OK" python3 code/walsh_exact.py selftest
step monotone_heaps "OK" python3 code/walsh_exact.py monotone

# 4. independent cross-check for small parameters: exhaustive enumeration of flats through the all-ones point
flats_all() {
  B="$OUT/bin/flats"
  for a in "2 5 3" "2 5 4" "3 3 2" "3 3 3" "3 4 4" "3 4 5" "3 5 6" "3 5 7" "4 3 4" "4 3 5" "4 4 7" "4 4 8" "5 3 4" "5 3 5"; do
    $B mc $a
  done
}
step flat_enumeration "flats_counted=" flats_all

# 5. flat method: finite reduction, SAT instances with strictly checked LRAT (k = 3, 4, 5)
fiber_q() {
  python3 code/fiber_instances.py 3 --cert "$OUT/cert" && python3 code/fiber_instances.py 4 --cert "$OUT/cert" \
  && FSAT_GREEDY=1 python3 code/fiber_instances.py 5 --cert "$OUT/cert"
}
step fiber_k3_k4_k5 "k=5: ALL INSTANCES UNSAT AND LRAT-CHECKED" fiber_q
cnf_cmp() {
  python3 - "$OUT/cert" data/original_certificates <<'EOF'
import json, sys
new, old = sys.argv[1], sys.argv[2]
ok = True
for k, ref in ((3, old + '/fproof_k3_t2.json'), (4, old + '/fproof_k4_t2.json'), (5, old + '/greedy/fproof_k5_t2.json')):
    a = [i['cnf_sha256'] for i in json.load(open(new + '/fproof_k%d_t2.json' % k))['instances']]
    b = [i['cnf_sha256'] for i in json.load(open(ref))['instances']]
    print('k=%d: %d instances, CNF hashes %s' % (k, len(a), 'identical' if a == b else 'DIFFER'))
    ok &= a == b
print('CNF HASHES MATCH' if ok else 'CNF HASH MISMATCH')
EOF
}
step cnf_hashes_vs_original "CNF HASHES MATCH" cnf_cmp

# 6. the flat method fails at 16 operands (n = 3): RM(1,4) counterexample to the Fiber Lemma
step rm14_counterexample "(F) fails" python3 code/rm14_counterexample.py

# 7. upper-bound circuits (exhaustive small cases; 32-bit 3/4/5-operand adders proved equivalent to ripple chains)
heap_q() { python3 code/heap_upper_bound.py small && for k in 3 4 5; do python3 code/heap_upper_bound.py prove $k 32; done; }
step heap_circuits "add5_32_heap AND 121 formula 121.*status equivalent" heap_q

# 8. joint sums: 3n-4 pair circuit (n = 32 proof), n = 3 exact value (LRAT), n = 4 lower bound 7 (tree search)
step joint_pair_circuit '"status": "equivalent"' python3 code/joint_pair_circuit.py
step joint_n3_no_4and '"result": "unsat", "lrat_strict_check": true' python3 code/joint_sat.py 3,3,1,2/3,3,1,2 4 span
step joint_n4_lower7 ": none" "$OUT/bin/jtree" 3,3,1,2/3,3,1,2/3,3,1,2 6
# spectral bound for the pair P_n is only 1, 3, 6 for n = 2, 3, 4 (Section 11, "Limit of the spectral bound")
spec_weak() {
  python3 code/joint_spectral.py pair 2 && python3 code/joint_spectral.py pair 3 && python3 code/joint_spectral.py pair 4
}
spec_weak_check() {
  spec_weak > "$OUT/joint_spectral_weak.raw" 2>&1 || return 1
  cat "$OUT/joint_spectral_weak.raw"
  grep -q "pair n=2: .*spectral bound 1 " "$OUT/joint_spectral_weak.raw" && \
  grep -q "pair n=3: .*spectral bound 3 " "$OUT/joint_spectral_weak.raw" && \
  grep -q "pair n=4: .*spectral bound 6 " "$OUT/joint_spectral_weak.raw" && echo "SPECTRAL BOUNDS 1 3 6 AS STATED"
}
step joint_spectral_weak "SPECTRAL BOUNDS 1 3 6 AS STATED" spec_weak_check

if [ "$MODE" = full ]; then
  # k = 6 needs abstraction depth 3; both sound normal forms on; CaDiCaL without --plain (strict checker anyway)
  step fiber_k6_t3 "k=6: ALL INSTANCES UNSAT AND LRAT-CHECKED" env FSAT_GREEDY=1 FSAT_FIBNF=1 FSAT_NOPLAIN=1 \
       python3 code/fiber_instances.py 6 --t 3 --cert "$OUT/cert6"
  tight_full() {
    python3 code/tight_certificates.py 4 6 "$OUT/tight_certs_m4_k6.txt" && \
    python3 code/tight_certificates.py 5 3 "$OUT/tight_certs_m5_k3.txt" && \
    gzip -dc data/tight_certs_m4_k6.txt.gz | cmp - "$OUT/tight_certs_m4_k6.txt" && \
    gzip -dc data/tight_certs_m5_k3.txt.gz | cmp - "$OUT/tight_certs_m5_k3.txt" && echo "CERTS IDENTICAL"
  }
  step tight_certificates "CERTS IDENTICAL" tight_full
fi
echo; echo "summary ($MODE mode):"; cat "$SUMMARY"
grep -q FAIL "$SUMMARY" && exit 1 || exit 0
