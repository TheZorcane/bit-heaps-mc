import Mcadd.Upper

/-!
# Addition with a constant

For a constant `K`, `ADDK k n K` outputs `(x₁ + ⋯ + x_k + K) mod 2^n`. With `m = n - 1`,
carries `c₀ = 0`, `c_{j+1} = ⌊(k + c_j + K_j)/2⌋` and `FA k n K = Σ_{j<m} ⌊(k + c_j)/2⌋`:

* the full-adder network with the constant folded in computes `ADDK k n K` with `FA k n K`
  AND gates (`addCircuitK_computes`, `addCircuitK_andCount`);
* the top sum bit has Walsh coefficient `±2^(N - FA)` at an explicit linear form
  (`walsh_top_const`), so every circuit needs `FA k n K` AND gates (`lower_bound_const`);
* hence `MC (ADDK k n K) = FA k n K` (`MC_ADDK`), and the top bit alone has the same `MC`
  (`MC_topBit_const`). For `K = 0` these are the statements for `ADD k n`.

The Walsh computation extends the polynomial encoding of `Lower.lean` by the factor `X^K`.
A column `j < m` is processed by the identity `Φ(Q_j · h(X^(2^j))) = 2^(a_j) Φ((1 - X^(2^j))^(c_j)
· h(X^(2^j)))` (`invariant`), whose step uses rule (R3) of the paper: a monomial `X^(2^j)` next to
a polynomial in `X^(2^(j+1))` does not change `Φ` (`Phi_expand_X`).
-/

namespace Mcadd

open Polynomial Finset

/-! ## Carries with a constant -/

/-- Number of columns `j < m` with `k + c_j` odd and `K_j = 0`. -/
def aK (k m K : ℕ) : ℕ := ∑ j ∈ range m, (k + cK k K j) % 2 * (1 - K / 2 ^ j % 2)

lemma cK_succ (k K j : ℕ) : cK k K (j + 1) = (k + cK k K j + K / 2 ^ j % 2) / 2 := rfl

lemma cK_le (k K j : ℕ) : cK k K j ≤ k := by
  induction j with
  | zero => simp [cK]
  | succ j ih =>
    rw [cK_succ]
    have := Nat.mod_lt (K / 2 ^ j) two_pos
    omega

lemma FA_succ (k m K : ℕ) : FA k (m + 1) K = ∑ j ∈ range m, (k + cK k K j) / 2 := by
  simp [FA]

/-- `k m = FA + c_m + a` (Lemma 4.1 of the paper, uniform heap with a constant). -/
lemma count_identity_K (k m K : ℕ) : k * m = FA k (m + 1) K + cK k K m + aK k m K := by
  induction m with
  | zero => simp [FA, aK, cK]
  | succ m ih =>
    rw [FA_succ] at ih ⊢
    rw [aK, sum_range_succ, sum_range_succ, ← aK, cK_succ, mul_add, mul_one, ih]
    rcases Nat.mod_two_eq_zero_or_one (K / 2 ^ m) with h | h <;> rw [h] <;> omega

/-! ## Rule (R3) and the shift by `X^K` -/

lemma sm_two_pow_mul_add (m j u : ℕ) (hj : j < m) :
    sm m (2 ^ (j + 1) * u + 2 ^ j) = sm m (2 ^ (j + 1) * u) := by
  unfold sm
  rw [Nat.testBit_two_pow_mul_add u (Nat.pow_lt_pow_succ (by norm_num)), Nat.testBit_two_pow_mul]
  simp [show ¬ m < j + 1 by omega, show j + 1 ≤ m by omega]

/-- Rule (R3): next to a polynomial in `X^(2^(j+1))`, the factor `X^(2^j)` does not change `Φ`
(for `j < m`). -/
lemma Phi_expand_X (m j : ℕ) (hj : j < m) (g : ℤ[X]) :
    Phi (sm m) (expand ℤ (2 ^ j) (X * expand ℤ 2 g)) =
      Phi (sm m) (expand ℤ (2 ^ j) (expand ℤ 2 g)) := by
  rw [map_mul, expand_X, expand_expand]
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, map_add, map_add, hp, hq]
  | monomial n a =>
    rw [expand_monomial, X_pow_mul_monomial, Phi_monomial, Phi_monomial]
    have h1 : n * (2 ^ j * 2) = 2 ^ (j + 1) * n := by ring
    rw [h1, sm_two_pow_mul_add m j n hj]

/-- The constant `K` shifts the sign function: `Φ_{s(· + K)}(p) = Φ_s(p · X^K)`. -/
lemma Phi_shift (s : ℕ → ℤ) (K : ℕ) (p : ℤ[X]) :
    Phi (fun t => s (t + K)) p = Phi s (p * X ^ K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, add_mul, map_add]
  | monomial n a => rw [monomial_mul_X_pow, Phi_monomial, Phi_monomial]

/-! ## One column -/

/-- One column `j < m` with `c ≤ k` entering carries, `c'` leaving carries and constant bit `b`. -/
lemma column_step (m j : ℕ) (hj : j < m) (k c c' b : ℕ) (hck : c ≤ k) (hb : b ≤ 1)
    (hc' : c' = (k + c + b) / 2) (h : ℤ[X]) :
    Phi (sm m) (expand ℤ (2 ^ j) ((1 - X) ^ c *
        ((1 - X) ^ (c' - c) * (1 + X) ^ (k - (c' - c)) * X ^ b * expand ℤ 2 h))) =
      2 ^ ((k + c) % 2 * (1 - b)) *
        Phi (sm m) (expand ℤ (2 ^ j) (expand ℤ 2 ((1 - X) ^ c' * h))) := by
  have hL : (1 - X) ^ c * ((1 - X) ^ (c' - c) * (1 + X) ^ (k - (c' - c)) * X ^ b *
      expand ℤ 2 h) = (1 - X) ^ c' * (1 + X) ^ (k + c - c') * X ^ b * expand ℤ 2 h := by
    have h1 : (1 - X : ℤ[X]) ^ c' = (1 - X) ^ c * (1 - X) ^ (c' - c) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, show k - (c' - c) = k + c - c' by omega]
    ring
  rw [hL]
  obtain ⟨p, τ, hτ, hp⟩ : ∃ p τ, τ ≤ 1 ∧ k + c = 2 * p + τ :=
    ⟨(k + c) / 2, (k + c) % 2, by omega, by omega⟩
  have hE : ∀ q : ℤ[X], expand ℤ 2 ((1 - X) ^ p * q) =
      (1 - X) ^ p * (1 + X) ^ p * expand ℤ 2 q := by
    intro q
    simp only [map_mul, map_pow, map_sub, map_one, expand_X]
    rw [show (1 - X ^ 2 : ℤ[X]) = (1 - X) * (1 + X) by ring, mul_pow]
  rw [show (k + c) % 2 = τ by omega]
  interval_cases b <;> interval_cases τ
  · -- `b = 0`, `τ = 0`
    rw [show c' = p by omega, show k + c - p = p by omega, hE]
    simp
  · -- `b = 0`, `τ = 1`: rule (R1) leaves one bit `1 + X^(2^j)`, which doubles `Φ`
    have : (1 - X) ^ c' * (1 + X) ^ (k + c - c') * X ^ 0 * expand ℤ 2 h =
        expand ℤ 2 ((1 - X) ^ c' * h) + X * expand ℤ 2 ((1 - X) ^ c' * h) := by
      rw [show c' = p by omega, show k + c - p = p + 1 by omega, hE]
      ring
    rw [this, map_add, map_add, Phi_expand_X m j hj]
    ring
  · -- `b = 1`, `τ = 0`: the constant bit is moved up by rule (R3)
    have : (1 - X) ^ c' * (1 + X) ^ (k + c - c') * X ^ 1 * expand ℤ 2 h =
        X * expand ℤ 2 ((1 - X) ^ c' * h) := by
      rw [show c' = p by omega, show k + c - p = p by omega, hE]
      ring
    rw [this, Phi_expand_X m j hj]
    ring
  · -- `b = 1`, `τ = 1`: the constant bit and the odd bit give one more carry (rule (R5))
    have : (1 - X) ^ c' * (1 + X) ^ (k + c - c') * X ^ 1 * expand ℤ 2 h =
        X * expand ℤ 2 ((1 - X) ^ p * h) - expand ℤ 2 (X * ((1 - X) ^ p * h)) := by
      rw [show c' = p + 1 by omega, show k + c - (p + 1) = p by omega, map_mul _ X, hE]
      simp only [expand_X]
      ring
    have h2 : (1 - X) ^ c' * h = (1 - X) ^ p * h - X * ((1 - X) ^ p * h) := by
      rw [show c' = p + 1 by omega]; ring
    rw [this, map_sub, map_sub, Phi_expand_X m j hj, h2, map_sub, map_sub, map_sub]
    ring

/-! ## All columns below the top -/

/-- The polynomial of column `j < m`: `e_j = c_{j+1} - c_j` bits with sign `-1`, the other
`k - e_j` bits with sign `+1`, and the constant bit `K_j`, all in the variable `X^(2^j)`
(applied via `expand`). -/
noncomputable def colPoly (k K i : ℕ) : ℤ[X] :=
  (1 - X) ^ (cK k K (i + 1) - cK k K i) * (1 + X) ^ (k - (cK k K (i + 1) - cK k K i)) *
    X ^ (K / 2 ^ i % 2)

lemma invariant (k m K : ℕ) (j : ℕ) (hj : j ≤ m) (h : ℤ[X]) :
    Phi (sm m) ((∏ i ∈ range j, expand ℤ (2 ^ i) (colPoly k K i)) * expand ℤ (2 ^ j) h) =
      2 ^ aK k j K * Phi (sm m) (expand ℤ (2 ^ j) ((1 - X) ^ cK k K j * h)) := by
  induction j generalizing h with
  | zero => simp [aK, cK, expand_one]
  | succ j ih =>
    rw [prod_range_succ, mul_assoc, pow_succ, ← expand_expand, ← map_mul,
      ih (by omega), colPoly,
      column_step m j (by omega) k (cK k K j) (cK k K (j + 1)) (K / 2 ^ j % 2)
        (cK_le k K j) (by omega) rfl, expand_expand]
    simp only [aK, sum_range_succ, pow_add]
    ring

/-! ## The Walsh coefficient -/

/-- The linear form for `ADDK k (m+1) K`: in column `j < m` it contains `c_{j+1} - c_j` bits
(those of the first words), and it contains all bits of the top column `m`. -/
def lformK (k m K : ℕ) (p : Fin k × Fin (m + 1)) : Bool :=
  decide (p.1.val < if p.2.val < m then cK k K (p.2.val + 1) - cK k K p.2.val else k)

lemma prod_X_pow_bits (K m : ℕ) :
    ∏ j ∈ range m, (X : ℤ[X]) ^ (2 ^ j * (K / 2 ^ j % 2)) = X ^ (K % 2 ^ m) := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih => rw [prod_range_succ, ih, ← pow_add, Nat.mod_pow_succ]

/-- **Theorem 6.1 of the paper for `ADDK k (m+1) K`.** The Walsh coefficient of the top sum bit
at `lformK` is `±2^(k + c_m + a)`, with sign `+` iff bit `m` of `K` is `0`; the exponent is
`N - FA` by `count_identity_K`. -/
theorem walsh_top_const (k m K : ℕ) :
    walsh (fun x => ADDK k (m + 1) K x (Fin.last m)) (lformK k m K) =
      sgn (K.testBit m) * 2 ^ (k + cK k K m + aK k m K) := by
  set e : ℕ → ℕ := fun j => if j < m then cK k K (j + 1) - cK k K j else k with he
  have hek : ∀ j, e j ≤ k := by
    intro j
    simp only [he]
    split_ifs
    · have := cK_le k K (j + 1); omega
    · exact le_rfl
  -- Step 1: the Walsh sum as a signed sum
  have step1 : walsh (fun x => ADDK k (m + 1) K x (Fin.last m)) (lformK k m K) =
      ∑ x : Fin k × Fin (m + 1) → Bool,
        (∏ p, if x p then (if lformK k m K p then (-1 : ℤ) else 1) else 1) *
          (fun t => sm m (t + K)) (∑ p, if x p then 2 ^ p.2.val else 0) := by
    unfold walsh
    apply Finset.sum_congr rfl
    intro x _
    rw [sgn_xor, sgn_dot, Finset.prod_filter, mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      cases lformK k m K p <;> cases x p <;> simp [sgn]
    · dsimp only [ADDK, sm]
      rw [Nat.testBit_mod_two_pow]
      simp only [Fin.val_last, lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and]
      congr 3
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      cases x (i, b) <;> simp
  -- Step 2: the product of binomials, column by column
  have step2 : ∏ p : Fin k × Fin (m + 1),
        (1 + C (if lformK k m K p then (-1 : ℤ) else 1) * X ^ (2 ^ p.2.val) : ℤ[X]) =
      (∏ j ∈ range m, ((1 - X ^ 2 ^ j : ℤ[X]) ^ e j * (1 + X ^ 2 ^ j) ^ (k - e j))) *
        (1 - X ^ 2 ^ m) ^ k := by
    rw [Fintype.prod_prod_type_right]
    have inner : ∀ j : Fin (m + 1),
        ∏ i : Fin k,
          (1 + C (if lformK k m K (i, j) then (-1 : ℤ) else 1) * X ^ (2 ^ j.val) : ℤ[X]) =
          (1 - X ^ 2 ^ j.val) ^ e j.val * (1 + X ^ 2 ^ j.val) ^ (k - e j.val) := by
      intro j
      rw [← prod_fin_lt k (e j.val) (hek _)]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i.val < e j.val
      · have : lformK k m K (i, j) = true := by simpa [lformK, he] using h
        simp [this, h]; ring
      · have : lformK k m K (i, j) = false := by simpa [lformK, he] using h
        simp [this, h]
    simp_rw [inner]
    rw [Fin.prod_univ_eq_prod_range
      (fun j => (1 - X ^ 2 ^ j : ℤ[X]) ^ e j * (1 + X ^ 2 ^ j) ^ (k - e j)) (m + 1),
      prod_range_succ]
    simp only [he, lt_irrefl, ↓reduceIte, Nat.sub_self, pow_zero, mul_one]
  -- Step 3: the whole polynomial, with the factor `X^K`, in the form used by `invariant`
  have step3 : (∏ j ∈ range m, ((1 - X ^ 2 ^ j : ℤ[X]) ^ e j * (1 + X ^ 2 ^ j) ^ (k - e j))) *
        (1 - X ^ 2 ^ m) ^ k * X ^ K =
      (∏ i ∈ range m, expand ℤ (2 ^ i) (colPoly k K i)) *
        expand ℤ (2 ^ m) ((1 - X) ^ k * X ^ (K / 2 ^ m)) := by
    have hcol : ∀ i ∈ range m, expand ℤ (2 ^ i) (colPoly k K i) =
        ((1 - X ^ 2 ^ i : ℤ[X]) ^ e i * (1 + X ^ 2 ^ i) ^ (k - e i)) *
          X ^ (2 ^ i * (K / 2 ^ i % 2)) := by
      intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      simp only [colPoly, map_mul, map_pow, map_sub, map_add, map_one, expand_X, he, hi',
        ↓reduceIte, ← pow_mul]
    rw [prod_congr rfl hcol, prod_mul_distrib (s := range m)
      (f := fun i => (1 - X ^ 2 ^ i : ℤ[X]) ^ e i * (1 + X ^ 2 ^ i) ^ (k - e i)),
      prod_X_pow_bits]
    conv_lhs => rw [← Nat.mod_add_div K (2 ^ m)]
    simp only [map_mul, map_pow, map_sub, map_one, expand_X, ← pow_mul, pow_add]
    ring
  have step4 := signed_sum_eq_Phi (fun t => sm m (t + K))
    (fun p : Fin k × Fin (m + 1) => 2 ^ p.2.val) (fun p => if lformK k m K p then (-1 : ℤ) else 1)
  rw [step1, step4, Phi_shift, step2, step3, invariant k m K m le_rfl, ← mul_assoc,
    ← pow_add]
  -- Step 4: the top column, rule (R2)
  have htop : expand ℤ (2 ^ m) ((1 - X) ^ (cK k K m + k) * X ^ (K / 2 ^ m)) =
      X ^ (2 ^ m * (K / 2 ^ m)) * (1 - X ^ 2 ^ m) ^ (cK k K m + k) := by
    simp only [map_mul, map_pow, map_sub, map_one, expand_X, ← pow_mul]
    ring
  rw [htop, Phi_mul_one_sub (sm m) (2 ^ m) (sm_add m), X_pow_eq_monomial, Phi_monomial]
  have hs : sm m (2 ^ m * (K / 2 ^ m)) = sgn (K.testBit m) := by
    simp [sm, Nat.testBit_eq_decide_div_mod_eq]
  rw [hs]
  ring

/-- **Theorem 6.1 of the paper for `ADDK k (m+1) K`**, exponent in closed form:
`W = ±2^(N - FA)` with `N = k (m+1)` inputs. -/
theorem walsh_top_const_closed (k m K : ℕ) :
    walsh (fun x => ADDK k (m + 1) K x (Fin.last m)) (lformK k m K) =
      sgn (K.testBit m) * 2 ^ (k * (m + 1) - FA k (m + 1) K) := by
  rw [walsh_top_const]
  have := count_identity_K k m K
  congr 2
  rw [mul_add, mul_one]
  omega

/-! ## Lower bound -/

/-- **Lower bound with a constant.** Every circuit computing `ADDK k n K` has at least
`FA k n K` AND gates. -/
theorem lower_bound_const (k n K : ℕ) (C : Circuit (Fin k × Fin n) (Fin n))
    (hC : Computes C (ADDK k n K)) : FA k n K ≤ C.andCount := by
  cases n with
  | zero => simp [FA]
  | succ m =>
    have hW : walsh (fun x => dot (fun o => decide (o = Fin.last m)) (ADDK k (m + 1) K x))
        (lformK k m K) = sgn (K.testBit m) * 2 ^ (k + cK k K m + aK k m K) := by
      simp_rw [dot_single]
      exact walsh_top_const k m K
    have h := andCount_ge_of_walsh_sgn C _ hC _ _ _ _ hW
    have hid := count_identity_K k m K
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    rw [mul_add, mul_one] at h
    omega

/-! ## Upper bound: the full-adder network with the constant folded in -/

section Upper

variable {ι : Type}

/-- The constant `true`. -/
def Lit.one : Lit ι := ⟨.const, true⟩

/-- The complement of a literal (free). -/
def Lit.not (l : Lit ι) : Lit ι := ⟨l.src, !l.neg⟩

lemma Lit.WF.not {n : ℕ} {l : Lit ι} (h : l.WF n) : l.not.WF n := h

lemma val_one (x : ι → Bool) (gs : List (Gate ι)) : val x gs Lit.one = true := by
  simp [val, Lit.one, Lit.eval, Src.eval]

lemma val_not (x : ι → Bool) (gs : List (Gate ι)) (l : Lit ι) :
    val x gs l.not = !val x gs l := by
  obtain ⟨src, neg⟩ := l
  cases neg <;> simp [val, Lit.not, Lit.eval]

/-- Process a column below the top with constant bit `b`. With `b = true` and an even number
of wires, the constant `1` is added as one more wire (no extra AND: the wire count becomes odd).
With `b = true` and an odd number of wires, the column is reduced as usual to a sum wire `s`
and carries; then the sum is `¬s` and `s` is one more carry (no AND). -/
def procColK (ls : List (Lit ι)) (gs : List (Gate ι)) (b : Bool) :
    List (Gate ι) × Lit ι × List (Lit ι) :=
  if b then
    if ls.length % 2 = 0 then procCol (ls ++ [Lit.one]) gs
    else ((procCol ls gs).1, (procCol ls gs).2.1.not, (procCol ls gs).2.2 ++ [(procCol ls gs).2.1])
  else procCol ls gs

/-- Specification of a processed column with constant bit `b`. -/
structure ColSpecK (gs : List (Gate ι)) (total : (ι → Bool) → ℕ) (len : ℕ) (b : Bool)
    (r : List (Gate ι) × Lit ι × List (Lit ι)) : Prop where
  pre : gs <+: r.1
  ands : andCount r.1 = andCount gs + len / 2
  wfs : r.2.1.WF r.1.length
  wfc : ∀ c ∈ r.2.2, c.WF r.1.length
  clen : r.2.2.length = (len + b.toNat) / 2
  sem : ∀ x, (val x r.1 r.2.1).toNat + 2 * cnt x r.1 r.2.2 = total x + b.toNat

theorem procColK_spec (ls : List (Lit ι)) (gs : List (Gate ι)) (b : Bool)
    (h : ∀ l ∈ ls, l.WF gs.length) :
    ColSpecK gs (fun x => cnt x gs ls) ls.length b (procColK ls gs b) := by
  cases b with
  | false =>
    have hc := procCol_spec ls gs h
    simp only [procColK, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hc.pre, hc.ands, hc.wfs, hc.wfc, by simpa using hc.clen,
      fun x => by simpa using hc.sem x⟩
  | true =>
    by_cases hev : ls.length % 2 = 0
    · have h' : ∀ l ∈ ls ++ [Lit.one], l.WF gs.length := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact h l hl
        · simp only [List.mem_singleton] at hl; subst hl; simp [Lit.one, Lit.WF]
      have hc := procCol_spec (ls ++ [Lit.one]) gs h'
      simp only [procColK, hev, ↓reduceIte, List.length_append, List.length_singleton] at hc ⊢
      refine ⟨hc.pre, by rw [hc.ands]; omega, hc.wfs, hc.wfc, by rw [hc.clen]; simp, fun x => ?_⟩
      rw [hc.sem x, cnt_append, cnt_cons, cnt_nil, val_one]
      simp
    · have hc := procCol_spec ls gs h
      simp only [procColK, hev, ↓reduceIte]
      refine ⟨hc.pre, hc.ands, ?_, ?_, ?_, fun x => ?_⟩
      · exact Lit.WF.not hc.wfs
      · intro c hc'
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact hc.wfc c hc'
        · simp only [List.mem_singleton] at hc'; subst hc'; exact hc.wfs
      · rw [List.length_append, hc.clen]; simp; omega
      · rw [val_not, cnt_append, cnt_cons, cnt_nil, ← hc.sem x]
        cases val x (procCol ls gs).1 (procCol ls gs).2.1 <;> simp <;> ring

/-- Process the columns (least significant first) with the constant `K` (bit `j` of `K` goes to
column `j`), given the carries `cs` entering the first column. The last column is the top
column; there the constant bit, if `1`, is one more wire of the XOR. -/
def addHeapK : List (List (Lit ι)) → List (Gate ι) → List (Lit ι) → ℕ →
    List (Gate ι) × List (Lit ι)
  | [], gs, _, _ => (gs, [])
  | [top], gs, cs, K =>
    let ls := cs ++ top ++ (if K % 2 = 1 then [Lit.one] else [])
    ((procTop ls gs).1, [(procTop ls gs).2])
  | col :: c2 :: cols, gs, cs, K =>
    let rc := procColK (cs ++ col) gs (decide (K % 2 = 1))
    let r := addHeapK (c2 :: cols) rc.1 rc.2.2 (K / 2)
    (r.1, rc.2.1 :: r.2)

/-- AND count of `addHeapK`, from the number `c` of entering carries, the column sizes and `K`. -/
def heapAndsK : ℕ → List ℕ → ℕ → ℕ
  | _, [], _ => 0
  | _, [_], _ => 0
  | c, v :: w :: rest, K => (c + v) / 2 + heapAndsK ((c + v + K % 2) / 2) (w :: rest) (K / 2)

/-- Specification of `addHeapK`. -/
structure HeapSpecK (gs : List (Gate ι)) (cs : List (Lit ι)) (cols : List (List (Lit ι))) (K : ℕ)
    (r : List (Gate ι) × List (Lit ι)) : Prop where
  pre : gs <+: r.1
  ands : andCount r.1 = andCount gs + heapAndsK cs.length (cols.map List.length) K
  sem : ∀ x j, j < cols.length →
    val x r.1 (r.2.getD j Lit.zero) = (cnt x gs cs + heapVal x gs cols + K).testBit j

lemma toNat_decide_mod_two (K : ℕ) : (decide (K % 2 = 1)).toNat = K % 2 := by
  rcases Nat.mod_two_eq_zero_or_one K with h | h <;> simp [h]

theorem addHeapK_spec :
    ∀ (cols : List (List (Lit ι))) (gs : List (Gate ι)) (cs : List (Lit ι)) (K : ℕ),
    (∀ c ∈ cs, c.WF gs.length) → (∀ col ∈ cols, ∀ l ∈ col, l.WF gs.length) →
    HeapSpecK gs cs cols K (addHeapK cols gs cs K)
  | [], gs, cs, K, _, _ =>
    ⟨List.prefix_refl _, by simp [addHeapK, heapAndsK], fun x j hj => by simp at hj⟩
  | [top], gs, cs, K, hcs, hcols => by
    obtain ⟨ls, hls⟩ : ∃ ls, ls = cs ++ top ++ (if K % 2 = 1 then [Lit.one] else []) :=
      ⟨_, rfl⟩
    have hall : ∀ l ∈ ls, l.WF gs.length := by
      intro l hl
      rw [hls] at hl
      rcases List.mem_append.mp hl with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hcs l h
        · exact hcols top (by simp) l h
      · split_ifs at h
        · simp only [List.mem_singleton] at h; subst h; simp [Lit.one, Lit.WF]
        · simp at h
    have hcnt : ∀ x, cnt x gs ls = cnt x gs cs + cnt x gs top + K % 2 := by
      intro x
      rw [hls, cnt_append, cnt_append]
      split_ifs with hK
      · simp [val_one, hK]
      · simp; omega
    have hr : addHeapK [top] gs cs K = ((procTop ls gs).1, [(procTop ls gs).2]) := by
      rw [hls]; rfl
    obtain ⟨h1, h2, h3⟩ := procTop_spec ls gs hall
    rw [hr]
    refine ⟨h1, by simp [heapAndsK, h2], fun x j hj => ?_⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    have := h3 x
    rw [hcnt] at this
    simp only [heapVal, List.getD_cons_zero, mul_zero, add_zero, Nat.testBit_zero]
    cases hv : val x (procTop ls gs).1 (procTop ls gs).2 <;> simp [hv] at this ⊢ <;> omega
  | col :: c2 :: cols, gs, cs, K, hcs, hcols => by
    have hall : ∀ l ∈ cs ++ col, l.WF gs.length := by
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact hcs l h
      · exact hcols col (by simp) l h
    have hc := procColK_spec (cs ++ col) gs (decide (K % 2 = 1)) hall
    have hcols' : ∀ c ∈ c2 :: cols, ∀ l ∈ c, l.WF gs.length :=
      fun c hc' => hcols c (List.mem_cons_of_mem _ hc')
    have ih := addHeapK_spec (c2 :: cols) (procColK (cs ++ col) gs (decide (K % 2 = 1))).1
      (procColK (cs ++ col) gs (decide (K % 2 = 1))).2.2 (K / 2)
      hc.wfc (fun c hc' l hl => (hcols' c hc' l hl).mono hc.pre.length_le)
    refine ⟨hc.pre.trans ih.pre, ?_, fun x j hj => ?_⟩
    · have h1 := ih.ands
      have h2 := hc.ands
      have h3 := hc.clen
      rw [toNat_decide_mod_two] at h3
      simp only [addHeapK, List.map_cons, heapAndsK, List.length_append] at h1 h2 h3 ⊢
      rw [h1, h2, h3]
      omega
    · have hsem := hc.sem x
      rw [toNat_decide_mod_two] at hsem
      have hT : cnt x gs cs + heapVal x gs (col :: c2 :: cols) + K =
          (val x (procColK (cs ++ col) gs (decide (K % 2 = 1))).1
              (procColK (cs ++ col) gs (decide (K % 2 = 1))).2.1).toNat +
            2 * (cnt x (procColK (cs ++ col) gs (decide (K % 2 = 1))).1
                (procColK (cs ++ col) gs (decide (K % 2 = 1))).2.2 +
              heapVal x (procColK (cs ++ col) gs (decide (K % 2 = 1))).1 (c2 :: cols) +
              K / 2) := by
        rw [heapVal_mono hc.pre x (c2 :: cols) hcols']
        simp only [cnt_append] at hsem
        simp only [heapVal] at hsem ⊢
        omega
      rw [hT]
      cases j with
      | zero =>
        rw [testBit_bit_zero]
        simp only [addHeapK, List.getD_cons_zero]
        exact val_mono ih.pre hc.wfs x
      | succ j =>
        rw [testBit_bit_succ]
        simp only [addHeapK, List.getD_cons_succ]
        exact ih.sem x j (by simpa using hj)

/-- The full-adder network for `ADDK k n K`. -/
def addCircuitK (k n K : ℕ) : Circuit (Fin k × Fin n) (Fin n) where
  gates := (addHeapK (addCols k n) [] [] K).1
  outs := fun j => (addHeapK (addCols k n) [] [] K).2.getD j Lit.zero

lemma heapAndsK_replicate (k K : ℕ) : ∀ (m j : ℕ),
    heapAndsK (cK k K j) (List.replicate (m + 1) k) (K / 2 ^ j) =
      ∑ i ∈ range m, (k + cK k K (j + i)) / 2
  | 0, j => by simp [heapAndsK]
  | m + 1, j => by
    have h1 : (cK k K j + k + K / 2 ^ j % 2) / 2 = cK k K (j + 1) := by
      rw [cK_succ]; congr 1; omega
    have h2 : K / 2 ^ j / 2 = K / 2 ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [List.replicate_succ, List.replicate_succ, heapAndsK, ← List.replicate_succ, h1, h2,
      heapAndsK_replicate k K m (j + 1), Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm, add_comm k]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 3
    omega

theorem addCircuitK_spec (k n K : ℕ) :
    HeapSpecK [] [] (addCols k n) K (addHeapK (addCols k n) [] [] K) :=
  addHeapK_spec (addCols k n) [] [] K (by simp) (by
    intro col hcol l hl
    simp only [addCols, List.mem_ofFn] at hcol
    obtain ⟨j, rfl⟩ := hcol
    simp only [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    simp [Lit.WF])

/-- The full-adder network computes `ADDK k n K`. -/
theorem addCircuitK_computes (k n K : ℕ) : Computes (addCircuitK k n K) (ADDK k n K) := by
  intro x
  funext j
  have h := (addCircuitK_spec k n K).sem x j (by simp [addCols])
  have hval : heapVal x [] (addCols k n) =
      ∑ i : Fin k, ∑ b : Fin n, 2 ^ (b : ℕ) * (x (i, b)).toNat := by
    rw [addCols, heapVal_ofFn, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    congr 1
    simp [cnt, List.sum_ofFn, val, Lit.eval, Src.eval, Function.comp_def]
  unfold Circuit.eval ADDK
  change val x (addCircuitK k n K).gates ((addCircuitK k n K).outs j) = _
  rw [Nat.testBit_mod_two_pow, ← hval]
  simp only [addCircuitK, Fin.is_lt, decide_true, Bool.true_and]
  rw [h]
  simp

/-- The full-adder network for `ADDK k n K` has exactly `FA k n K` AND gates. -/
theorem addCircuitK_andCount (k n K : ℕ) : (addCircuitK k n K).andCount = FA k n K := by
  have h := (addCircuitK_spec k n K).ands
  have hlen : (addCols k n).map List.length = List.replicate n k := by
    simp [addCols, List.map_ofFn, Function.comp_def, List.ofFn_const]
  rw [hlen] at h
  unfold Circuit.andCount
  simp only [addCircuitK]
  rw [h]
  cases n with
  | zero => simp [heapAndsK, FA, andCount]
  | succ m =>
    have := heapAndsK_replicate k K m 0
    simp only [cK, pow_zero, Nat.div_one, zero_add] at this
    simp [andCount, FA, this]

/-- **Upper bound with a constant**: `ADDK k n K` has a circuit with `FA k n K` AND gates. -/
theorem upper_bound_const (k n K : ℕ) : FA k n K ∈ MCSet (ADDK k n K) :=
  ⟨addCircuitK k n K, addCircuitK_computes k n K, addCircuitK_andCount k n K⟩

end Upper

/-! ## Main theorems with a constant -/

/-- **Main theorem with a constant**, order-theoretic form: `FA k n K` is the least AND count of
a circuit computing `ADDK k n K`. -/
theorem isLeast_ADDK (k n K : ℕ) : IsLeast (MCSet (ADDK k n K)) (FA k n K) :=
  ⟨upper_bound_const k n K, fun _ ⟨C, hC, ht⟩ => ht ▸ lower_bound_const k n K C hC⟩

/-- **Main theorem with a constant.** `MC((x₁ + ⋯ + x_k + K) mod 2^n) = FA k n K`. -/
theorem MC_ADDK (k n K : ℕ) : MC (ADDK k n K) = FA k n K :=
  (isLeast_ADDK k n K).csInf_eq

/-- The top sum bit of `ADDK k (m+1) K`, as a function with one output. -/
def topBitK (k m K : ℕ) (x : Fin k × Fin (m + 1) → Bool) (_ : Unit) : Bool :=
  ADDK k (m + 1) K x (Fin.last m)

/-- Every circuit computing the top sum bit of `ADDK k (m+1) K` has at least `FA k (m+1) K`
AND gates. -/
theorem lower_bound_top_const (k m K : ℕ) (C : Circuit (Fin k × Fin (m + 1)) Unit)
    (hC : Computes C (topBitK k m K)) : FA k (m + 1) K ≤ C.andCount := by
  have hdot : ∀ y : Unit → Bool, dot (fun _ => true) y = y () := by
    intro y
    unfold dot
    cases h : y () <;> simp [Finset.univ_unique, h]
  have hW : walsh (fun x => dot (fun _ => true) (topBitK k m K x))
      (lformK k m K) = sgn (K.testBit m) * 2 ^ (k + cK k K m + aK k m K) := by
    simp_rw [hdot]
    exact walsh_top_const k m K
  have h := andCount_ge_of_walsh_sgn C _ hC _ _ _ _ hW
  have hid := count_identity_K k m K
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  rw [mul_add, mul_one] at h
  omega

/-- The top sum bit of `ADDK k (m+1) K` alone has multiplicative complexity `FA k (m+1) K`. -/
theorem MC_topBit_const (k m K : ℕ) : MC (topBitK k m K) = FA k (m + 1) K := by
  refine IsLeast.csInf_eq ⟨⟨⟨(addCircuitK k (m + 1) K).gates,
    fun _ => (addCircuitK k (m + 1) K).outs (Fin.last m)⟩, ?_,
    addCircuitK_andCount k (m + 1) K⟩, ?_⟩
  · intro x
    funext _
    exact congrFun (addCircuitK_computes k (m + 1) K x) (Fin.last m)
  · rintro _ ⟨C, hC, rfl⟩
    exact lower_bound_top_const k m K C hC

/-! ## The case `K = 0` agrees with `ADD k n` -/

lemma ADDK_zero (k n : ℕ) : ADDK k n 0 = ADD k n := by
  funext x j
  simp [ADDK, ADD]

lemma cK_zero (k j : ℕ) : cK k 0 j = cc k j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [cK, cc, ih]

lemma FA_zero (k n : ℕ) : FA k n 0 = U k n := by
  rw [U_eq_UU, FA, UU]
  apply Finset.sum_congr rfl
  intro j _
  rw [cK_zero]
  rfl

lemma lformK_zero (k m : ℕ) : lformK k m 0 = lform k m := by
  funext p
  simp [lformK, lform, cK_zero]

lemma aK_zero (k m : ℕ) : aK k m 0 = aa k m := by
  simp [aK, aa, cK_zero]

/-- For `K = 0`, `MC_ADDK` is `MC_ADD`. -/
theorem MC_ADDK_zero (k n : ℕ) : MC (ADDK k n 0) = U k n := by
  rw [MC_ADDK, FA_zero]

/-- For `K = 0`, `walsh_top_const` is `walsh_top`. -/
example (k m : ℕ) :
    walsh (fun x => ADD k (m + 1) x (Fin.last m)) (lform k m) = 2 ^ (k + cc k m + aa k m) := by
  have := walsh_top_const k m 0
  rw [ADDK_zero, lformK_zero, cK_zero, aK_zero] at this
  simpa [sgn] using this

end Mcadd
