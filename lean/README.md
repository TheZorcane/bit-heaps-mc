# mcadd — Lean 4 formalization: exact multiplicative complexity of multi-operand modular addition

Lean 4 `v4.36.0` with Mathlib `v4.36.0`.

**Status: everything below is fully proved.** There is no `sorry`, no custom axiom and no
`native_decide`. `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for every
main theorem (output below).

## Main theorems

For all `k` and `n` (in particular `k ≥ 2`, `n ≥ 1`):

    MC((x_1 + … + x_k) mod 2^n) = Σ_{i=1}^{n-1} (k − ⌈k/2^i⌉)

Lean: `Mcadd.MC_ADD (k n : ℕ) : MC (ADD k n) = U k n` in `Mcadd/Main.lean`.

With an added constant `K` (Theorem 2 of the paper, with its top-bit statement), for all `k`, `n`, `K`:

    MC((x_1 + … + x_k + K) mod 2^n) = FA(k, n, K) = Σ_{j<n-1} ⌊(k + c_j)/2⌋,
    c_0 = 0,  c_{j+1} = ⌊(k + c_j + K_j)/2⌋,  K_j = bit j of K

Lean: `Mcadd.MC_ADDK (k n K : ℕ) : MC (ADDK k n K) = FA k n K` in `Mcadd/Const.lean`.
For `K = 0` this is the first theorem (`ADDK_zero : ADDK k n 0 = ADD k n`,
`FA_zero : FA k n 0 = U k n`).

## What is formalized

### Definitions (`Mcadd/Basic.lean`) — these are what a reader has to audit

| Math | Lean |
|---|---|
| Literal: constant 0, input `i`, or output of gate `j`; optionally complemented (free NOT) | `Src`, `Lit` |
| Gate: 2-input AND or XOR of literals | `Gate` |
| Evaluation of a gate list in order; gate `j` sees only gates `0..j-1` | `run`, `Gate.eval`, `Lit.eval` |
| Circuit with inputs `ι`, outputs `κ`: gate list + one literal per output | `Circuit`, `Circuit.eval` |
| Number of AND gates | `andCount`, `Circuit.andCount` |
| `C` computes `F : (ι → Bool) → κ → Bool` | `Computes C F` |
| `MC(F)` = least AND count of a circuit computing `F` | `MC F := sInf (MCSet F)` |
| `l·x` over 𝔽₂ | `dot l x` |
| `W_f(l) = Σ_x (−1)^(f(x) ⊕ l·x)`, an integer | `walsh f l` |
| `ADD_{k,n}`: input `x (i, b)` is bit `b` of word `i`; output `j` is bit `j` of `(Σ_i Σ_b 2^b x(i,b)) mod 2^n` | `ADD k n` |
| `U(k,n) = Σ_{i=1}^{n-1} (k − ⌈k/2^i⌉)` (ceiling taken in ℚ) | `U k n` |
| `ADDK_{k,n,K}`: inputs as for `ADD k n`; output `j` is bit `j` of `(Σ_i Σ_b 2^b x(i,b) + K) mod 2^n`, `K : ℕ` | `ADDK k n K` |
| Carries with a constant: `c_0 = 0`, `c_{j+1} = ⌊(k + c_j + (⌊K/2^j⌋ mod 2))/2⌋` | `cK k K j` |
| `FA(k,n,K) = Σ_{j<n-1} ⌊(k + c_j)/2⌋` | `FA k n K` |

Notes on the model:
- Constant 1 is the complemented constant 0. A literal that refers to a gate not yet computed
  reads `false`; this only gives circuits another way to write a constant.
- An integer constant can be replaced by its residue mod `2^n`, so `K : ℕ` loses nothing.
- `MC` is an infimum over ℕ. The main theorems are also stated as
  `IsLeast (MCSet (ADD k n)) (U k n)` and `IsLeast (MCSet (ADDK k n K)) (FA k n K)`, which say a
  circuit with that many ANDs exists and none has fewer; this form does not depend on the
  convention `sInf ∅ = 0`.

### Theorems

| # | Statement | Lean name | File |
|---|---|---|---|
| Thm 3.1 | A circuit with `t` ANDs on `N` inputs: `2^(N−t)` divides `W_{u·F}(l)` for every XOR `u·F` of outputs and every `l` | `theoremS` | `TheoremS.lean` |
| Cor. 3.2 (case W = 2^e) | If `C` computes `F` and `W_{u·F}(l) = 2^e` then `C` has `≥ N − e` ANDs | `andCount_ge_of_walsh` | `TheoremS.lean` |
| Cor. 3.2 (case W = ±2^e) | If `C` computes `F` and `W_{u·F}(l) = (−1)^b 2^e` then `C` has `≥ N − e` ANDs | `andCount_ge_of_walsh_sgn` | `TheoremS.lean` |
| Thm 6.1 (uniform heap, K = 0) | For `ADD k (m+1)` and the explicit linear form `lform k m`: `W_{top bit}(l) = +2^(N−U)`, `N = k(m+1)` | `walsh_top`, `walsh_top_closed` | `Lower.lean`, `Main.lean` |
| LB | Every circuit computing `ADD k n` has `≥ U k n` ANDs (all `k`, `n`) | `lower_bound` | `Lower.lean` |
| UB | The full-adder network `addCircuit k n` computes `ADD k n` on all inputs and has exactly `U k n` ANDs (all `k`, `n`) | `addCircuit_computes`, `addCircuit_andCount`, `upper_bound` | `Upper.lean` |
| Main | `MC(ADD k n) = U k n`; `U k n` is the least element of the set of AND counts | `MC_ADD`, `isLeast_ADD` | `Main.lean` |
| Top bit | The top sum bit alone has `MC = U k n` (`n = m+1`) | `MC_topBit` | `Main.lean` |
| k = 2 | `MC(ADD 2 n) = n − 1` | `MC_ADD_two` | `Main.lean` |
| k = 3 | `MC(ADD 3 n) = 2n − 3` for `n ≥ 2` | `MC_ADD_three` | `Main.lean` |
| k = 4 | `MC(ADD 4 n) = 3n − 4` for `n ≥ 2` | `MC_ADD_four` | `Main.lean` |
| Thm 6.1 with K (uniform heap) | For `ADDK k (m+1) K` and the linear form `lformK k m K`: `W_{top bit}(l) = (−1)^(K_m) 2^(N−FA)`, `K_m` = bit `m` of `K` | `walsh_top_const`, `walsh_top_const_closed` | `Const.lean` |
| LB with K | Every circuit computing `ADDK k n K` has `≥ FA k n K` ANDs (all `k`, `n`, `K`) | `lower_bound_const` | `Const.lean` |
| UB with K | The network `addCircuitK k n K` computes `ADDK k n K` on all inputs and has exactly `FA k n K` ANDs | `addCircuitK_computes`, `addCircuitK_andCount`, `upper_bound_const` | `Const.lean` |
| Thm 2 (uniform heap) | `MC(ADDK k n K) = FA k n K`; `FA k n K` is the least element of the set of AND counts | `MC_ADDK`, `isLeast_ADDK` | `Const.lean` |
| Thm 2, top bit | The top sum bit of `ADDK k (m+1) K` alone has `MC = FA k (m+1) K` | `MC_topBit_const` | `Const.lean` |
| K = 0 | `ADDK k n 0 = ADD k n`, `FA k n 0 = U k n`, `MC(ADDK k n 0) = U k n` | `ADDK_zero`, `FA_zero`, `MC_ADDK_zero` | `Const.lean` |

Supporting facts: `cc k j` is the carry count `c_0 = 0`, `c_{j+1} = ⌊(k + c_j)/2⌋`;
`cc_eq_ceil : cc k i = k − ⌈k/2^i⌉`; `U_eq_UU : U k n = Σ_{j<n-1} c_{j+1}`;
`count_identity : k·m = U + c_m + a` (Lemma 4.1 of the paper). With a constant:
`count_identity_K : k·m = FA + c_m + a` with `a = #{j < m : k + c_j odd and K_j = 0}` (`aK`);
`cK_le : c_j ≤ k`; `cK_zero : cK k 0 j = cc k j`.

Sign of the Walsh coefficient with a constant: it is `+2^(N−FA)` when bit `m` (`= n−1`) of `K`
is `0` and `−2^(N−FA)` when it is `1` (already for `m = 0`: `W = (−1)^(K_0) 2^k`). Only
`|W| = 2^(N−FA)` is needed for the lower bound (`andCount_ge_of_walsh_sgn`).

### How the proofs relate to the paper

- **Theorem S (Theorem 3.1 of the paper).** The paper proves it with a decision tree whose leaves
  are affine flats. The Lean proof uses the equivalent character expansion, by induction over the
  gate list: for every set `S` of inputs and set `m` of gates,
  `2^N` divides `2^t · Σ_x (−1)^(⊕_{i∈S} x_i ⊕ ⊕_{j∈m} g_j(x))`.
  An XOR gate only changes the sets; an AND gate uses
  `2·(−1)^(ab) = 1 + (−1)^a + (−1)^b − (−1)^(a⊕b)`. This is a different (shorter) proof of the
  same statement; the flat partition itself is not formalized.
- **Theorem 6.1 of the paper (uniform constant-free heap).** The paper's signed-sum rules are
  formalized with polynomials in `ℤ[X]`: the Walsh sum equals `Φ(∏_bits (1 ± X^(2^col)))` with
  `Φ(p) = Σ_i p_i·(−1)^(bit_m i)` (`signed_sum_eq_Phi`). Rule R1 is `(1−Y)(1+Y) = 1−Y²`
  (`column_identity`), R2 is `Φ(p·(1−X^(2^m))^c) = 2^c Φ(p)` (`Phi_mul_one_sub`), R4 is
  `Φ(p) = p(1)` for `deg p < 2^m` (`Phi_eq_eval_one`). The linear form takes the first
  `c_{j+1} − c_j` bits of each column `j < m` and all bits of the top column.
- **Theorem 6.1 with a constant (`Const.lean`).** The constant enters as a factor `X^K`:
  `Φ_{s(·+K)}(p) = Φ_s(p·X^K)` (`Phi_shift`). Bit `j < m` of `K` becomes a factor `X^(2^j)` of
  column `j`. Columns `j < m` are removed one at a time by
  `Φ(Q_j · h(X^(2^j))) = 2^(a_j) Φ((1 − X^(2^j))^(c_j) · h(X^(2^j)))` (`invariant`; a polynomial
  in `X^(2^j)` is written `expand ℤ (2^j) h`). Its step (`column_step`) uses R1 and rule R3 in the
  form `Φ(X^(2^j) · g(X^(2^(j+1)))) = Φ(g(X^(2^(j+1))))` for `j < m` (`Phi_expand_X`). In a
  column with `K_j = 1` this moves the constant bit up (`k + c_j` even) or turns the odd bit and
  the constant bit into one more carry (`k + c_j` odd; the paper's rule R5). The top column and
  `⌊K/2^m⌋` are then handled by R2 as for `K = 0`. The linear form `lformK` is built as `lform`,
  with `c_j = cK k K j`.
- **Upper bound.** `addCircuit` processes columns upwards; each column is reduced with full
  adders (`maj(a,b,c) = (a⊕c)(b⊕c)⊕c`, one AND) and at most one half adder; the top column uses
  XOR only. Correctness is proved for all inputs, all `k`, `n` (`addHeap_spec`).
- **Upper bound with a constant.** `addCircuitK` is the same network with bit `j` of `K` folded
  into column `j` without extra ANDs (`procColK`): if the column has an even number of wires,
  the constant `1` is added as one more wire (so the column ends with full adders only); if odd,
  the column is reduced as usual to a sum wire `s` and carries, then the sum is `¬s` and `s` is
  one more carry. In the top column the constant bit is one more XOR input. Correctness for all
  inputs, `k`, `n`, `K`: `addHeapK_spec`. The `K = 0` network `addCircuit` is kept unchanged as a
  separate definition.

### Not formalized

Theorems 1 and 4 (all heaps via the completion argument, Hamming weight), Sections 8–12 of the paper; the general (non-uniform) heap version
of Theorem 6.1 (only the uniform heaps `ADD k n` and `ADDK k n K` are done); the closed
form of `FA` for `k = 2` with a constant is only checked by `#eval`, not proved; the
flat/decision-tree form of Theorem S (the parity-decision-tree lemma).

## How to build

    cd lean
    lake exe cache get     # downloads the prebuilt Mathlib cache (several GB); needs elan
    lake build

Do not run `lake update`. The build prints the sanity `#eval`s and the axioms lines from
`Mcadd/Main.lean`.

## Build output (2026-11-23)

`lake build` (from an empty `.lake/build`) ends with `Build completed successfully (18264 jobs).`
There are no errors, no warnings and no `sorry` warnings. The Mathlib header linter (it asks for
a Mathlib copyright/authors block) is switched off in `lakefile.toml`; all other linters of the
Mathlib standard set are on. `Mcadd/Basic.lean` is a module (`module`, `public import Mathlib`,
`@[expose] public section`); this only changes visibility, not the definitions.

Axioms:

    'Mcadd.theoremS' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.andCount_ge_of_walsh' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.walsh_top' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.walsh_top_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.addCircuit_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.addCircuit_andCount' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.isLeast_ADD' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADD' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_topBit' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADD_two' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADD_three' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADD_four' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.andCount_ge_of_walsh_sgn' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.walsh_top_const' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.walsh_top_const_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.lower_bound_const' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.addCircuitK_computes' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.addCircuitK_andCount' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.upper_bound_const' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.isLeast_ADDK' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADDK' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_topBit_const' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.ADDK_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.FA_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Mcadd.MC_ADDK_zero' depends on axioms: [propext, Classical.choice, Quot.sound]

Sanity checks (computations, not proofs, except the `example`s):

    (addCircuit 3 3).andCount = 3          (16 gates in total)
    (addCircuit 4 4).andCount = 8
    (addCircuit 8 32).andCount = 213
    U(k, 32) for k = 2..8: [31, 61, 92, 121, 152, 182, 213]
    bruteCheck 3 3, 2 4, 4 3, 5 2: true    (circuit = ADD on all inputs)
    example : (addCircuit 3 3).andCount = 3 := by decide
    example : MC (ADD 3 3) = 3
    bruteCheckK 3 3, 2 4, 4 2: true        (addCircuitK = ADDK on all inputs, for all K < 2^n)
    FA 2 n K = (n−1) + max(0, n−2−b) for all n < 10, K < 1024: true
        (b = lowest set bit of K in positions 1..n−2, else n−1; the paper's closed form)
    (addCircuitK 3 4 K).andCount and FA 3 4 K for K = 0..15: both
        [5, 5, 5, 6, 5, 5, 5, 6, 5, 5, 5, 6, 5, 5, 5, 6]
    walsh (top bit of ADDK 2 3 K) (lformK 2 2 K) and (−1)^(K_2) 2^(6 − FA 2 3 K), K = 0..7:
        [(16, 16), (16, 16), (16, 16), (16, 16), (-16, -16), (-16, -16), (-16, -16), (-16, -16)]

Line counts (`wc -l`): `Mcadd.lean` 12, `Basic.lean` 135, `TheoremS.lean` 287, `Lower.lean` 330,
`Upper.lean` 487, `Const.lean` 635, `Main.lean` 197; total 2083.

## Remaining gaps

None in the targets above. See "Not formalized" for the parts of the paper that are outside
this formalization.

## Files

- `Mcadd/Basic.lean` — definitions.
- `Mcadd/TheoremS.lean` — Theorem S and its corollaries.
- `Mcadd/Lower.lean` — carry counts, closed form of `U`, the Walsh coefficient, lower bound.
- `Mcadd/Upper.lean` — full-adder network, correctness, AND count.
- `Mcadd/Const.lean` — addition with a constant: carries, Walsh coefficient, lower bound,
  network, `MC_ADDK`, top bit, agreement with `K = 0`.
- `Mcadd/Main.lean` — main theorem, top bit, `k = 2, 3, 4`, sanity checks, `#print axioms`.
- `Mcadd.lean` — imports all of the above.
