import Mcadd.TheoremS

/-!
# Lower bound: an explicit Walsh coefficient of the top sum bit

For `ADD k (m+1)` we exhibit a linear form `l` with
`W_{top bit}(l) = 2^(N - U)`, `N = k (m+1)`, and deduce that every circuit for `ADD k (m+1)`
has at least `U` AND gates.

The computation follows the paper's signed-sum calculus, written with polynomials:
the Walsh sum is `Φ(∏_bits (1 ± X^(2^col)))`, where `Φ(p) = Σ_i p_i · (-1)^(bit_m i)`;
rule (R1) is `(1 - Y)(1 + Y) = 1 - Y²`, rule (R2) is `Φ(p·(1 - X^(2^m))) = 2 Φ(p)`,
and rule (R4) is `Φ(p) = p(1)` for `deg p < 2^m`.
-/


namespace Mcadd

open Polynomial Finset

/-! ## Carry counts of the full-adder network -/

/-- `cc k j` is the number of carries entering column `j`: `c₀ = 0`, `c_{j+1} = ⌊(k + c_j)/2⌋`. -/
def cc (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (k + cc k j) / 2

/-- Number of AND gates of the full-adder network with `m` carry columns: `Σ_{j<m} c_{j+1}`. -/
def UU (k m : ℕ) : ℕ := ∑ j ∈ range m, cc k (j + 1)

/-- Number of columns `j < m` with an odd number `k + c_j` of wires. -/
def aa (k m : ℕ) : ℕ := ∑ j ∈ range m, (k + cc k j) % 2

lemma cc_le (k j : ℕ) : cc k j ≤ k := by
  induction j with
  | zero => simp [cc]
  | succ j ih => simp only [cc]; omega

/-- `k m = U + c_m + a` (Lemma 4.1 of the paper, uniform heap, no constant). -/
lemma count_identity (k m : ℕ) : k * m = UU k m + cc k m + aa k m := by
  induction m with
  | zero => simp [UU, aa, cc]
  | succ m ih =>
    have h1 : cc k (m + 1) = (k + cc k m) / 2 := rfl
    rw [UU, aa, sum_range_succ, sum_range_succ, ← UU, ← aa, mul_add, mul_one, ih]
    omega

/-! ## Closed form -/

lemma ceil_div_two_pow (k i : ℕ) : ⌈(k : ℚ) / 2 ^ i⌉₊ = (k + 2 ^ i - 1) / 2 ^ i := by
  have hd : 0 < 2 ^ i := by positivity
  apply eq_of_forall_ge_iff
  intro c
  rw [Nat.ceil_le, div_le_iff₀ (by positivity), Nat.div_le_iff_le_mul_add_pred hd]
  have : ((k : ℚ) ≤ c * 2 ^ i) ↔ k ≤ c * 2 ^ i := by exact_mod_cast Iff.rfl
  rw [this, mul_comm c]
  generalize 2 ^ i * c = e
  omega

lemma ceil_succ (k i : ℕ) :
    (k + 2 ^ (i + 1) - 1) / 2 ^ (i + 1) = ((k + 2 ^ i - 1) / 2 ^ i + 1) / 2 := by
  have hd : 0 < 2 ^ i := by positivity
  rw [← Nat.add_div_right _ hd, Nat.div_div_eq_div_mul, pow_succ]
  congr 1
  omega

lemma cc_eq (k i : ℕ) : cc k i = k - (k + 2 ^ i - 1) / 2 ^ i ∧ (k + 2 ^ i - 1) / 2 ^ i ≤ k := by
  induction i with
  | zero => simp [cc]
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [ceil_succ]
    simp only [cc, h1]
    omega

lemma cc_eq_ceil (k i : ℕ) : cc k i = k - ⌈(k : ℚ) / 2 ^ i⌉₊ := by
  rw [ceil_div_two_pow, (cc_eq k i).1]

/-- The full-adder count equals the closed form `Σ_{i=1}^{n-1} (k - ⌈k/2^i⌉)`. -/
lemma U_eq_UU (k n : ℕ) : U k n = UU k (n - 1) := by
  unfold U UU
  generalize n - 1 = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ, cc_eq_ceil]

/-! ## The functional `Φ` -/

/-- `Φ_s(p) = Σ_i p_i · s(i)`. -/
noncomputable def Phi (s : ℕ → ℤ) : ℤ[X] →ₗ[ℤ] ℤ :=
  Polynomial.lsum (fun i => s i • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))

lemma Phi_monomial (s : ℕ → ℤ) (n : ℕ) (a : ℤ) : Phi s (monomial n a) = s n * a := by
  simp [Phi, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

lemma Phi_C_mul_X_pow (s : ℕ → ℤ) (n : ℕ) (a : ℤ) : Phi s (C a * X ^ n) = s n * a := by
  rw [C_mul_X_pow_eq_monomial, Phi_monomial]

lemma Phi_mul_X_pow (s : ℕ → ℤ) (P : ℕ) (hs : ∀ i, s (i + P) = -s i) (p : ℤ[X]) :
    Phi s (p * X ^ P) = - Phi s p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq]; ring
  | monomial n a => rw [monomial_mul_X_pow, Phi_monomial, Phi_monomial, hs]; ring

/-- Rule (R2): a sign-1 bit in the top column doubles the value. -/
lemma Phi_mul_one_sub (s : ℕ → ℤ) (P : ℕ) (hs : ∀ i, s (i + P) = -s i) (p : ℤ[X]) (c : ℕ) :
    Phi s (p * (1 - X ^ P) ^ c) = 2 ^ c * Phi s p := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ, ← mul_assoc, mul_sub, mul_one, map_sub, Phi_mul_X_pow s P hs, ih]
    ring

/-- Rule (R4) in bulk: below the period, `s = 1`, so `Φ(p) = p(1)`. -/
lemma Phi_eq_eval_one (s : ℕ → ℤ) (B : ℕ) (hs : ∀ i, i < B → s i = 1) (p : ℤ[X])
    (hp : p.natDegree < B) : Phi s p = p.eval 1 := by
  rw [Phi, Polynomial.lsum_apply, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  have : i < B := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp i hi) hp
  simp [hs i this]

/-- A signed sum over all `0/1` assignments is `Φ` of a product of binomials. -/
lemma signed_sum_eq_Phi {ι : Type} [Fintype ι] [DecidableEq ι] (s : ℕ → ℤ) (w : ι → ℕ)
    (σ : ι → ℤ) :
    ∑ x : ι → Bool, (∏ b, if x b then σ b else 1) * s (∑ b, if x b then w b else 0) =
      Phi s (∏ b, (1 + C (σ b) * X ^ w b)) := by
  have h : ∀ b, (1 + C (σ b) * X ^ w b : ℤ[X]) =
      ∑ c : Bool, C (if c then σ b else 1) * X ^ (if c then w b else 0) := by
    intro b
    simp [add_comm]
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, Phi_C_mul_X_pow]
  ring

/-! ## The polynomial identity (rule R1, column by column) -/

lemma prod_fin_lt (k e : ℕ) (he : e ≤ k) (A B : ℤ[X]) :
    ∏ i : Fin k, (if i.val < e then A else B) = A ^ e * B ^ (k - e) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < e then A else B) k]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Finset.prod_range_add]
  have h1 : ∏ x ∈ range e, (if x < e then A else B) = A ^ e := by
    rw [← Finset.card_range e, ← Finset.prod_const]
    simp only [Finset.card_range]
    apply Finset.prod_congr rfl
    intro x hx
    simp [Finset.mem_range.mp hx]
  have h2 : ∏ x ∈ range d, (if e + x < e then A else B) = B ^ d := by
    simp
  rw [h1, h2]
  congr 2
  omega

lemma column_identity (k m : ℕ) :
    ∏ j ∈ range m, ((1 - X ^ 2 ^ j : ℤ[X]) ^ (cc k (j + 1) - cc k j) *
        (1 + X ^ 2 ^ j) ^ (k - (cc k (j + 1) - cc k j))) =
      (∏ j ∈ range m, (1 + X ^ 2 ^ j : ℤ[X]) ^ ((k + cc k j) % 2)) *
        (1 - X ^ 2 ^ m) ^ cc k m := by
  induction m with
  | zero => simp [cc]
  | succ m ih =>
    rw [prod_range_succ, ih, prod_range_succ]
    have h1 : cc k (m + 1) = (k + cc k m) / 2 := rfl
    have h2 := cc_le k m
    have hY : (1 - X ^ 2 ^ (m + 1) : ℤ[X]) = (1 - X ^ 2 ^ m) * (1 + X ^ 2 ^ m) := by
      rw [pow_succ, pow_mul]; ring
    have e1 : k - (cc k (m + 1) - cc k m) = cc k (m + 1) + (k + cc k m) % 2 := by omega
    have e2 : (1 - X ^ 2 ^ m : ℤ[X]) ^ cc k (m + 1) =
        (1 - X ^ 2 ^ m) ^ cc k m * (1 - X ^ 2 ^ m) ^ (cc k (m + 1) - cc k m) := by
      rw [← pow_add]; congr 1; omega
    rw [hY, mul_pow, e1, e2, pow_add]
    ring

lemma natDegree_residue (k m : ℕ) :
    (∏ j ∈ range m, (1 + X ^ 2 ^ j : ℤ[X]) ^ ((k + cc k j) % 2)).natDegree < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ]
    have h1 : ((1 + X ^ 2 ^ m : ℤ[X]) ^ ((k + cc k m) % 2)).natDegree ≤ 2 ^ m := by
      have h0 : (1 + X ^ 2 ^ m : ℤ[X]).natDegree ≤ 2 ^ m :=
        (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_X_pow_le _))
      have hτ : (k + cc k m) % 2 ≤ 1 := by omega
      calc ((1 + X ^ 2 ^ m : ℤ[X]) ^ ((k + cc k m) % 2)).natDegree
          ≤ ((k + cc k m) % 2) * (1 + X ^ 2 ^ m : ℤ[X]).natDegree := natDegree_pow_le
        _ ≤ 1 * 2 ^ m := Nat.mul_le_mul hτ h0
        _ = 2 ^ m := one_mul _
    have := natDegree_mul_le (p := ∏ j ∈ range m, (1 + X ^ 2 ^ j : ℤ[X]) ^ ((k + cc k j) % 2))
      (q := (1 + X ^ 2 ^ m : ℤ[X]) ^ ((k + cc k m) % 2))
    rw [pow_succ]
    omega

lemma eval_residue (k m : ℕ) :
    (∏ j ∈ range m, (1 + X ^ 2 ^ j : ℤ[X]) ^ ((k + cc k j) % 2)).eval 1 = 2 ^ aa k m := by
  rw [eval_prod, aa, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  simp

/-! ## The Walsh coefficient -/

/-- `(-1)^(bit_m t)`. -/
def sm (m t : ℕ) : ℤ := sgn (t.testBit m)

lemma sm_add (m i : ℕ) : sm m (i + 2 ^ m) = - sm m i := by
  unfold sm
  rw [add_comm, Nat.testBit_two_pow_add_eq]
  cases i.testBit m <;> simp [sgn]

lemma sm_lt (m i : ℕ) (h : i < 2 ^ m) : sm m i = 1 := by
  unfold sm
  rw [Nat.testBit_lt_two_pow h]
  simp [sgn]

/-- The linear form of Theorem 6.1 of the paper: in column `j < m` it contains `c_{j+1} - c_j` bits
(those of the first words), and it contains all bits of the top column `m`. -/
def lform (k m : ℕ) (p : Fin k × Fin (m + 1)) : Bool :=
  decide (p.1.val < if p.2.val < m then cc k (p.2.val + 1) - cc k p.2.val else k)

lemma dot_single {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) (y : κ → Bool) :
    dot (fun o => decide (o = a)) y = y a := by
  unfold dot
  have : univ.filter (fun o => (decide (o = a) && y o) = true) = if y a then {a} else ∅ := by
    ext o
    by_cases h : o = a <;> cases hy : y a <;> simp [h, hy]
  rw [this]
  cases y a <;> simp

/-- **Theorem 6.1 of the paper for `ADD k (m+1)`.** The Walsh coefficient of the top sum bit
at `lform` is exactly `+2^(k + c_m + a)`, which is `2^(N - U)` by `count_identity`. -/
theorem walsh_top (k m : ℕ) :
    walsh (fun x => ADD k (m + 1) x (Fin.last m)) (lform k m) = 2 ^ (k + cc k m + aa k m) := by
  -- the exponents `e j`
  set e : ℕ → ℕ := fun j => if j < m then cc k (j + 1) - cc k j else k with he
  have hek : ∀ j, e j ≤ k := by
    intro j
    simp only [he]
    split_ifs
    · have := cc_le k (j + 1); omega
    · exact le_rfl
  -- Step 1: the Walsh sum as a signed sum
  have step1 : walsh (fun x => ADD k (m + 1) x (Fin.last m)) (lform k m) =
      ∑ x : Fin k × Fin (m + 1) → Bool,
        (∏ p, if x p then (if lform k m p then (-1 : ℤ) else 1) else 1) *
          sm m (∑ p, if x p then 2 ^ p.2.val else 0) := by
    unfold walsh
    apply Finset.sum_congr rfl
    intro x _
    rw [sgn_xor, sgn_dot, Finset.prod_filter, mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      cases lform k m p <;> cases x p <;> simp [sgn]
    · dsimp only [ADD, sm]
      rw [Nat.testBit_mod_two_pow]
      simp only [Fin.val_last, lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and]
      congr 2
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      cases x (i, b) <;> simp
  -- Step 2: the product of binomials
  have step2 : ∏ p : Fin k × Fin (m + 1),
        (1 + C (if lform k m p then (-1 : ℤ) else 1) * X ^ (2 ^ p.2.val) : ℤ[X]) =
      (∏ j ∈ range m, (1 + X ^ 2 ^ j : ℤ[X]) ^ ((k + cc k j) % 2)) *
        (1 - X ^ 2 ^ m) ^ (cc k m + k) := by
    rw [Fintype.prod_prod_type_right]
    have inner : ∀ j : Fin (m + 1),
        ∏ i : Fin k, (1 + C (if lform k m (i, j) then (-1 : ℤ) else 1) * X ^ (2 ^ j.val) : ℤ[X]) =
          (1 - X ^ 2 ^ j.val) ^ e j.val * (1 + X ^ 2 ^ j.val) ^ (k - e j.val) := by
      intro j
      rw [← prod_fin_lt k (e j.val) (hek _)]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i.val < e j.val
      · have : lform k m (i, j) = true := by simpa [lform, he] using h
        simp [this, h]; ring
      · have : lform k m (i, j) = false := by simpa [lform, he] using h
        simp [this, h]
    simp_rw [inner]
    rw [Fin.prod_univ_eq_prod_range
      (fun j => (1 - X ^ 2 ^ j : ℤ[X]) ^ e j * (1 + X ^ 2 ^ j) ^ (k - e j)) (m + 1),
      prod_range_succ]
    have hlow : ∏ j ∈ range m, ((1 - X ^ 2 ^ j : ℤ[X]) ^ e j * (1 + X ^ 2 ^ j) ^ (k - e j)) =
        ∏ j ∈ range m, ((1 - X ^ 2 ^ j : ℤ[X]) ^ (cc k (j + 1) - cc k j) *
          (1 + X ^ 2 ^ j) ^ (k - (cc k (j + 1) - cc k j))) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [he, Finset.mem_range.mp hj]
    rw [hlow, column_identity]
    simp only [he, lt_irrefl, ↓reduceIte, Nat.sub_self, pow_zero, mul_one]
    rw [mul_assoc, ← pow_add]
  have step3 := signed_sum_eq_Phi (sm m) (fun p : Fin k × Fin (m + 1) => 2 ^ p.2.val)
    (fun p => if lform k m p then (-1 : ℤ) else 1)
  beta_reduce at step3
  rw [step1, step3, step2,
    Phi_mul_one_sub (sm m) (2 ^ m) (sm_add m),
    Phi_eq_eval_one (sm m) (2 ^ m) (sm_lt m) _ (natDegree_residue k m), eval_residue]
  ring

/-- **Lower bound.** Every circuit computing `ADD k (m+1)` has at least `UU k m` AND gates. -/
theorem lower_bound_succ (k m : ℕ) (C : Circuit (Fin k × Fin (m + 1)) (Fin (m + 1)))
    (hC : Computes C (ADD k (m + 1))) : UU k m ≤ C.andCount := by
  have hW : walsh (fun x => dot (fun o => decide (o = Fin.last m)) (ADD k (m + 1) x))
      (lform k m) = 2 ^ (k + cc k m + aa k m) := by
    simp_rw [dot_single]
    exact walsh_top k m
  have h := andCount_ge_of_walsh C _ hC _ _ _ hW
  have hid := count_identity k m
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  rw [mul_add, mul_one] at h
  omega

/-- **Lower bound** in closed form: every circuit computing `ADD k n` has at least
`U k n = Σ_{i=1}^{n-1} (k - ⌈k/2^i⌉)` AND gates. -/
theorem lower_bound (k n : ℕ) (C : Circuit (Fin k × Fin n) (Fin n))
    (hC : Computes C (ADD k n)) : U k n ≤ C.andCount := by
  rw [U_eq_UU]
  cases n with
  | zero => simp [UU]
  | succ m => exact lower_bound_succ k m C hC

end Mcadd
