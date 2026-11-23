# Verifier library: cost model and verification vocabulary

This file describes the conventions of the small verifier library in `verifier/`, as it is used by the
scripts of this supplementary material (upper-bound circuits of Section 4 and Section 11, and the strict LRAT
checking of the SAT steps of Sections 10 and 11).

## Circuits

* Basis: 2-input AND and 2-input XOR nodes; NOT is a free complemented edge; constants and wires are free;
  unrestricted fanout. This is the XAG model of the paper (Section 2).
* Native format: `.xag` text (`verifier/xag.py`, `write_xag` / `read_xag`).
* `verifier/cost.py canonicalize` performs constant propagation, trivial identities, XOR complement
  normalisation, structural hashing and dead-node removal (no other rewriting). The AND count of a circuit,
  which is the quantity the paper is about, is reported after this canonicalisation. The canonical hash is
  the sha256 of `write_xag(canonicalize(x))`.
* `verifier/sim.py` evaluates circuits on packed bit vectors (bit-parallel simulation).
* `verifier/sha256_ref.py` is a FIPS 180-4 reference; the scripts use it only for the SHA-256 round
  constants K_t (Table 3 and the round-constant costs of Section 12).

## Bit order of the SHA-256 helpers

`sha256_ref.py` and `sim.py` also contain SHA-256 helpers (`words_to_bits`, `bits_to_words`, and the
compression-function targets `primary` = compress(IV, W), 512 -> 256 bits, and `secondary` =
compress(CV, W), 768 -> 256 bits) that the paper does not use. Their bit order: a sequence of 32-bit words
`w[0], w[1], ...` is the bit vector `v[i] = bit (31 - i % 32) of w[i // 32]` (words in order, each word most
significant bit first; bit 0 is the least significant bit).

## Verification status vocabulary

* `equivalent`: SAT miter UNSAT **and** the text-LRAT proof accepted by `verifier/lrat_check.py`, a strict
  RUP-only checker (every hint must be unit or falsified, in order). Trust boundary: the miter / Tseitin
  code in `equiv.py`, the XAG translation in `xag.py`, and `lrat_check.py`; the SAT solver is not trusted.
* `unsat_unchecked`: UNSAT without an accepted proof.
* `not_equivalent`: SAT, counterexample confirmed by simulation.
* `unverified`: timeout or error. Never a pass.
* Random-vector simulation is a **smoke test only**.

The CNF encoders of Sections 10 and 11 (`code/fsat.py`, `code/joint_sat.py`) use the same strict checker
for their UNSAT certificates.
