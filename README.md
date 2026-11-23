# Supplementary material: Exact multiplicative complexity of bit heaps and multi-operand addition

Ido Rosenbaum, 2026. License: see `LICENSE` (CC BY 4.0 for documentation and data; MIT for the code; the
vendored drat-trim sources in `verifier/vendor/` keep their own license).

- Paper: Ido Rosenbaum, *Exact multiplicative complexity of bit heaps and multi-operand addition*, IACR
  Cryptology ePrint Archive 2026/EPRINT_ID.
- Archived version of these files: https://doi.org/10.5281/zenodo.24474108

These files accompany the paper. They contain the Lean 4 formalization of the results for addition and
scripts that reproduce most of the computations in the paper. Section 15 of the paper lists what is
reproduced; the computations that are NOT reproduced here are listed at the end of this file.

## What is where

| path | content |
|---|---|
| `lean/` | Lean 4 + Mathlib formalization: Walsh divisibility (Thm 3.1), the explicit Walsh coefficient, the full-adder upper bound, `MC((x_1+...+x_k) mod 2^n) = sum_{i=1}^{n-1} (k - ceil(k/2^i))` for all k, n (Thm 2, `Mcadd.MC_ADD`, `Mcadd.isLeast_ADD`) the top-bit result (`Mcadd.MC_topBit`), and the same with an added constant K (Thm 2: `Mcadd.MC_ADDK`, `Mcadd.isLeast_ADDK`, `Mcadd.MC_topBit_const`). No `sorry`; `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`. See `lean/README.md`. |
| `code/completion_check.py` | Theorem 9.1 checks: the completion identities on 197,661 random heap/constant instances, and the best spectral bound equal to the full-adder count on all 1,088 small heaps with constants (about 2 s; run separately: `python3 code/completion_check.py`) |
| `reproduce.sh` | runs every check and prints PASS/FAIL per step (`quick` default, `full`) |
| `expected/` | expected outputs of the quick run (`summary.txt` and the per-step logs) |
| `code/mc_tables.py` | all numeric tables of the paper from the closed formulas |
| `code/mc_addition_walsh_check.c` | exact Walsh spectra (64-bit integer fast Walsh transform) of heap outputs with a constant; compares the spectral lower bound with the full-adder upper bound |
| `code/spectral_checks.py` | brute-force evaluation of the explicit coefficient of Thm 6.1 (all K, small k, n); the 12-AND circuit for the weight of 16 bits mod 8; round-constant costs |
| `code/walsh_exact.py` | Thm 3.1 self-test on random XAGs; Thm 6.1 on 4,604 heaps by exact polynomial arithmetic; random-heap scans |
| `code/tight_certificates.py` | regenerates the tightness certificates of Section 9 (Theorem 9.1; `data/tight_certs_*.txt.gz`: 41,340 + 37,386 lines, 74,076 distinct heaps with a constant; the two files share the 4,650 heaps with m <= 4, k_j <= 3) |
| `code/flat_enumerator.c` | small-n exhaustive enumeration of flats through the all-ones point (earlier proof route for k <= 6; not used by the current paper) |
| `code/fiber_instances.py`, `code/fsat.py` | instance lists and CNF encoder of the finite reduction (earlier proof route for k <= 6; not used by the current paper), certification with the strict LRAT checker |
| `code/rm14_counterexample.py`, `code/codesat.py`, `code/rm_cosets.py` | the RM(1,4) obstruction to the flat method (Theorem 10.2) |
| `code/heap_upper_bound.py` | the full-adder construction; exhaustive small checks; 32-bit equivalence proofs |
| `code/joint_*.py`, `code/joint_tree_bound.c`, `code/jmc.py`, `code/mcsat.py`, `code/round_sum_dp.py` | joint sums (Section 11): pair circuit, n = 3 SAT refutation, n = 4 tree search (an earlier computed result, not in the current paper), weakness of the spectral bound, the full-adder-model dynamic program for SHA-256 rounds |
| `code/affine_tree.c` | exhaustive affine-decision-tree depth search (small exact values) |
| `verifier/` | XAG library, canonical cost, simulator, SAT-miter harness, strict RUP-only LRAT checker (`lrat_check.py`), and the drat-trim `lrat-check` source used as a secondary check |
| `data/` | tightness certificates; hashes and checker messages of the original k = 5, 6 certificate runs |

## Dependencies
- Python 3 (standard library only; tested with 3.12 and 3.15).
- A C compiler (`cc`; tested with Apple clang and gcc).
- CaDiCaL 3.x on `PATH` as `cadical` (tested with 3.1.0), only for the SAT/LRAT steps. LRAT proofs are
  checked by `verifier/lrat_check.py`, a strict RUP checker written independently of the solver; the solver is
  not trusted.
- For the formalization: elan, Lean 4 v4.36.0 and Mathlib v4.36.0 (`lean/lake-manifest.json` pins the
  revisions). `lake exe cache get` downloads the prebuilt Mathlib cache (several GB).

## Quick start
```sh
sh reproduce.sh          # quick mode, about 75 seconds, 1 thread, < 200 MB disk
sh reproduce.sh full     # adds the k = 6 instance list and the certificate regeneration (about 6 more minutes, < 3 GB disk)
cd lean && lake exe cache get && lake build     # Lean formalization (under a minute after the cache download)
```
Compare `out/summary.txt` with `expected/summary.txt`; every step should print PASS.

## Individual commands
Run from this directory with `export PYTHONPATH=$PWD/verifier VERIFIER_DIR=$PWD/verifier`.

| claim | command | time |
|---|---|---|
| tables | `python3 code/mc_tables.py` | < 1 s |
| exact spectra | `cc -O2 -o walsh code/mc_addition_walsh_check.c; ./walsh add 3 5; ./walsh add 6 3; ./walsh add 9 3; ./walsh heap 16,0; ./walsh add 2 6 21 -t` | seconds |
| heap grid, weight mod 16 (Theorem 9.1) | `./walsh heap 12,12` (and every `a,b <= 12`); `./walsh heap 21,0,0` | seconds |
| Thm 6.1 brute force, 12-AND circuit | `python3 code/spectral_checks.py` | < 1 s |
| Thm 3.1 self-test / heaps | `python3 code/walsh_exact.py selftest` / `python3 code/walsh_exact.py monotone` | < 1 s / 30 s |
| flats through the all-ones point | `cc -O2 -o flats code/flat_enumerator.c; ./flats mc 3 5 6; ./flats mc 3 5 7` | < 1 s |
| k = 3, 4, 5 certificates | `python3 code/fiber_instances.py 3 --cert out/c`; the same with 4; `FSAT_GREEDY=1 python3 code/fiber_instances.py 5 --cert out/c` | 10 s total |
| k = 6 certificate | `FSAT_GREEDY=1 FSAT_FIBNF=1 FSAT_NOPLAIN=1 python3 code/fiber_instances.py 6 --t 3 --cert out/c6` | about 5 min (largest LRAT about 1 GB) |
| RM(1,4) obstruction | `python3 code/rm14_counterexample.py` | < 1 s |
| upper-bound circuits | `python3 code/heap_upper_bound.py small`; `python3 code/heap_upper_bound.py prove 5 32` | 1 s each |
| pair circuit (n = 32 proof) | `python3 code/joint_pair_circuit.py` | 2 s |
| MC(P_3) = 5 | `python3 code/joint_sat.py 3,3,1,2/3,3,1,2 4 span` | 3 s |
| MC(P_4) >= 7 | `cc -O2 -o jtree code/joint_tree_bound.c; ./jtree 3,3,1,2/3,3,1,2/3,3,1,2 6` | 20 s |
| spectral bound of P_n | `python3 code/joint_spectral.py pair 2` (also 3, 4): 1, 3, 6 | < 1 s |
| tightness certificates | `python3 code/tight_certificates.py 4 6 out/a.txt; python3 code/tight_certificates.py 5 3 out/b.txt` (byte-identical to `data/`) | 40 s |

## Notes
- The main theorem does not depend on any SAT computation. The SAT/LRAT material supports only the
  earlier proof route for k <= 6 (an independent cross-check, not used by the current paper) and Proposition 11.3(b).
- The original k = 5, 6 runs recorded CNF and proof hashes (`data/original_certificates/`); the step
  `cnf_hashes_vs_original` checks that the regenerated CNFs for k = 3, 4 and 5 (k = 5 with the greedy normal
  form) are byte-identical to the originals. LRAT proofs are not included; they are regenerated in seconds to
  minutes.
- Code comments may refer to "the flat method", "the finite reduction" and "the spectral method", which
  refer to the earlier proof route for k <= 6 ("the flat method", "the finite reduction") and to Sections 3 to 9 of the paper ("the spectral method").

## Not reproduced by these files
The programs or data for the following computations reported in the paper were not kept in reproducible form:
- the independent recomputation of 935,152 Walsh coefficients (Theorem 8.1);
- the 952 classes of base points / hyperplanes for the weight of 16 bits mod 8 (Section 10);
- the 400-line spot check of the certificate files (superseded by the byte-identical regeneration in full mode).
