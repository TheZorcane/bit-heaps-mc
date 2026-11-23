import Mcadd.Const

/-!
# Main theorem

`MC((x₁ + ⋯ + x_k) mod 2^n) = Σ_{i=1}^{n-1} (k - ⌈k/2^i⌉)` for all `k` and `n`.
-/

namespace Mcadd

open Finset

/-- **Main theorem**, order-theoretic form: `U k n` is the least AND count of a circuit
computing `ADD k n` (a circuit with `U k n` ANDs exists, and no circuit has fewer). -/
theorem isLeast_ADD (k n : ℕ) : IsLeast (MCSet (ADD k n)) (U k n) :=
  ⟨upper_bound k n, fun _ ⟨C, hC, ht⟩ => ht ▸ lower_bound k n C hC⟩

/-- **Main theorem.** `MC((x₁ + ⋯ + x_k) mod 2^n) = Σ_{i=1}^{n-1} (k - ⌈k/2^i⌉)`,
for all `k` and `n` (in particular for `k ≥ 2`, `n ≥ 1`). -/
theorem MC_ADD (k n : ℕ) : MC (ADD k n) = U k n :=
  (isLeast_ADD k n).csInf_eq

/-- **Theorem 6.1 of the paper for `ADD k (m+1)`**, exponent in closed form: the Walsh
coefficient of the top sum bit at the linear form `lform k m` equals `2^(N - U)` with
`N = k (m+1)` inputs. -/
theorem walsh_top_closed (k m : ℕ) :
    walsh (fun x => ADD k (m + 1) x (Fin.last m)) (lform k m) =
      2 ^ (k * (m + 1) - U k (m + 1)) := by
  rw [walsh_top, U_eq_UU]
  have := count_identity k m
  simp only [add_tsub_cancel_right]
  rw [mul_add, mul_one]
  congr 1
  omega

/-! ## The top sum bit alone (Theorem 3 of the paper) -/

/-- The top sum bit of `ADD k (m+1)`, as a function with one output. -/
def topBit (k m : ℕ) (x : Fin k × Fin (m + 1) → Bool) (_ : Unit) : Bool :=
  ADD k (m + 1) x (Fin.last m)

/-- Every circuit computing the top sum bit of `ADD k (m+1)` has at least `U k (m+1)` ANDs. -/
theorem lower_bound_top (k m : ℕ) (C : Circuit (Fin k × Fin (m + 1)) Unit)
    (hC : Computes C (topBit k m)) : U k (m + 1) ≤ C.andCount := by
  have hdot : ∀ y : Unit → Bool, dot (fun _ => true) y = y () := by
    intro y
    unfold dot
    cases h : y () <;> simp [Finset.univ_unique, h]
  have hW : walsh (fun x => dot (fun _ => true) (topBit k m x))
      (lform k m) = 2 ^ (k + cc k m + aa k m) := by
    simp_rw [hdot]
    exact walsh_top k m
  have h := andCount_ge_of_walsh C _ hC _ _ _ hW
  have hid := count_identity k m
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  rw [mul_add, mul_one] at h
  rw [U_eq_UU]
  simp only [add_tsub_cancel_right]
  omega

/-- The top sum bit alone already has multiplicative complexity `U k n` (`n = m + 1`). -/
theorem MC_topBit (k m : ℕ) : MC (topBit k m) = U k (m + 1) := by
  refine IsLeast.csInf_eq ⟨⟨⟨(addCircuit k (m + 1)).gates,
    fun _ => (addCircuit k (m + 1)).outs (Fin.last m)⟩, ?_, addCircuit_andCount k (m + 1)⟩, ?_⟩
  · intro x
    funext _
    exact congrFun (addCircuit_computes k (m + 1) x) (Fin.last m)
  · rintro _ ⟨C, hC, rfl⟩
    exact lower_bound_top k m C hC

/-! ## Closed forms for small `k` -/

lemma cc_two (j : ℕ) : cc 2 (j + 1) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cc, ih]

lemma cc_three (j : ℕ) : cc 3 (j + 2) = 2 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cc, ih]

lemma cc_four (j : ℕ) : cc 4 (j + 2) = 3 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cc, ih]

lemma UU_two (m : ℕ) : UU 2 m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [UU, sum_range_succ, ← UU, ih, cc_two]

lemma UU_three (m : ℕ) : UU 3 (m + 1) = 2 * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [UU, sum_range_succ, ← UU, ih, cc_three]; ring

lemma UU_four (m : ℕ) : UU 4 (m + 1) = 3 * m + 2 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [UU, sum_range_succ, ← UU, ih, cc_four]; ring

/-- `MC((x + y) mod 2^n) = n - 1`. -/
theorem MC_ADD_two (n : ℕ) : MC (ADD 2 n) = n - 1 := by
  rw [MC_ADD, U_eq_UU, UU_two]

/-- `MC((x + y + z) mod 2^n) = 2n - 3` for `n ≥ 2`. -/
theorem MC_ADD_three (n : ℕ) (hn : 2 ≤ n) : MC (ADD 3 n) = 2 * n - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [MC_ADD, U_eq_UU, show m + 2 - 1 = m + 1 from rfl, UU_three]
  omega

/-- `MC((x + y + z + w) mod 2^n) = 3n - 4` for `n ≥ 2`. -/
theorem MC_ADD_four (n : ℕ) (hn : 2 ≤ n) : MC (ADD 4 n) = 3 * n - 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [MC_ADD, U_eq_UU, show m + 2 - 1 = m + 1 from rfl, UU_four]
  omega

/-! ## Sanity checks (computations, not part of the proofs) -/

/-- Brute-force check that `addCircuit k n` agrees with `ADD k n` on all `2^(k n)` inputs. -/
def bruteCheck (k n : ℕ) : Bool :=
  (List.range (2 ^ (k * n))).all fun v =>
    let x : Fin k × Fin n → Bool := fun p => v.testBit (p.1.val * n + p.2.val)
    (List.finRange n).all fun j => (addCircuit k n).eval x j == ADD k n x j

#eval (addCircuit 3 3).andCount            -- 3
#eval (addCircuit 3 3).gates.length        -- 16 gates in total
#eval (addCircuit 4 4).andCount            -- 8 = 3·4 - 4
#eval (addCircuit 8 32).andCount           -- 213
#eval (List.range 7).map fun i => UU (i + 2) 31   -- [31, 61, 92, 121, 152, 182, 213]
#eval bruteCheck 3 3                       -- true
#eval bruteCheck 2 4                       -- true
#eval bruteCheck 4 3                       -- true
#eval bruteCheck 5 2                       -- true

example : (addCircuit 3 3).andCount = 3 := by decide
example : UU 3 2 = 3 := by decide
example : MC (ADD 3 3) = 3 := MC_ADD_three 3 (by norm_num)

/-! ### With a constant -/

/-- Brute-force check that `addCircuitK k n K` agrees with `ADDK k n K` on all inputs, for all
`K < 2^n`. -/
def bruteCheckK (k n : ℕ) : Bool :=
  (List.range (2 ^ n)).all fun K => (List.range (2 ^ (k * n))).all fun v =>
    let x : Fin k × Fin n → Bool := fun p => v.testBit (p.1.val * n + p.2.val)
    (List.finRange n).all fun j => (addCircuitK k n K).eval x j == ADDK k n K x j

/-- The paper's closed form for `k = 2`: `(n - 1) + max(0, n - 2 - b)`, where `b` is the lowest
set bit of `K` in positions `1, …, n-2`, and `b = n - 1` if there is none. -/
def FA2closed (n K : ℕ) : ℕ :=
  let b := ((List.range (n - 1)).filter fun i => 1 ≤ i ∧ K.testBit i).head?.getD (n - 1)
  (n - 1) + (n - 2 - b)

#eval bruteCheckK 3 3                      -- true
#eval bruteCheckK 2 4                      -- true
#eval bruteCheckK 4 2                      -- true
#eval (List.range 10).all fun n => (List.range 1024).all fun K => FA 2 n K == FA2closed n K
                                           -- true
#eval (List.range 16).map fun K => (addCircuitK 3 4 K).andCount
#eval (List.range 16).map fun K => FA 3 4 K
#eval (List.range 8).map fun K =>
  (walsh (fun x => ADDK 2 3 K x (Fin.last 2)) (lformK 2 2 K),
    sgn (K.testBit 2) * 2 ^ (2 * 3 - FA 2 3 K))

end Mcadd

/-! ## Axioms used by the main results -/

#print axioms Mcadd.theoremS
#print axioms Mcadd.andCount_ge_of_walsh
#print axioms Mcadd.walsh_top
#print axioms Mcadd.walsh_top_closed
#print axioms Mcadd.lower_bound
#print axioms Mcadd.addCircuit_computes
#print axioms Mcadd.addCircuit_andCount
#print axioms Mcadd.upper_bound
#print axioms Mcadd.isLeast_ADD
#print axioms Mcadd.MC_ADD
#print axioms Mcadd.MC_topBit
#print axioms Mcadd.MC_ADD_two
#print axioms Mcadd.MC_ADD_three
#print axioms Mcadd.MC_ADD_four
#print axioms Mcadd.andCount_ge_of_walsh_sgn
#print axioms Mcadd.walsh_top_const
#print axioms Mcadd.walsh_top_const_closed
#print axioms Mcadd.lower_bound_const
#print axioms Mcadd.addCircuitK_computes
#print axioms Mcadd.addCircuitK_andCount
#print axioms Mcadd.upper_bound_const
#print axioms Mcadd.isLeast_ADDK
#print axioms Mcadd.MC_ADDK
#print axioms Mcadd.MC_topBit_const
#print axioms Mcadd.ADDK_zero
#print axioms Mcadd.FA_zero
#print axioms Mcadd.MC_ADDK_zero
