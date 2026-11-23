import Mcadd.Basic

/-!
# Theorem S (Chistopolskaya–Podolskii, Lemma 5; credited there to Kulikov)

If a circuit has `t` AND gates and `N` inputs, then `2^(N-t)` divides every Walsh coefficient
of every XOR of its outputs.

Proof used here: by induction over the gate list, for every set `S` of inputs and every set `m`
of gates, `2^N ∣ 2^t · Σ_x (-1)^(⊕_{i∈S} x_i ⊕ ⊕_{j∈m} g_j(x))`. An XOR gate only changes the
sets; an AND gate uses `2·(-1)^(ab) = 1 + (-1)^a + (-1)^b - (-1)^(a⊕b)`.
-/


namespace Mcadd

open Finset

variable {ι κ : Type}

lemma sgn_xor (a b : Bool) : sgn (a ^^ b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

lemma sgn_and (a b : Bool) : 2 * sgn (a && b) = 1 + sgn a + sgn b - sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

lemma sgn_mul_self (a : Bool) : sgn a * sgn a = 1 := by
  cases a <;> simp [sgn]

/-- `(-1)^(⊕_{i∈S} x_i ⊕ ⊕_{j∈m} ws_j)`. -/
def chi (S : Finset ι) (m : Finset ℕ) (x : ι → Bool) (ws : List Bool) : ℤ :=
  (∏ i ∈ S, sgn (x i)) * ∏ j ∈ m, sgn (ws.getD j false)

lemma prod_tog {α : Type} [DecidableEq α] (s : Finset α) (a : α) (f : α → ℤ)
    (h : f a * f a = 1) :
    ∏ j ∈ (if a ∈ s then s.erase a else insert a s), f j = f a * ∏ j ∈ s, f j := by
  split_ifs with ha
  · rw [← Finset.mul_prod_erase s f ha, ← mul_assoc, h, one_mul]
  · rw [Finset.prod_insert ha]

/-- Multiplying by the sign of a literal changes the pair of sets and a constant factor. -/
lemma lit_chi (l : Lit ι) (S : Finset ι) (m : Finset ℕ) :
    ∃ (ε : ℤ) (S' : Finset ι) (m' : Finset ℕ), ∀ (x : ι → Bool) (ws : List Bool),
      sgn (l.eval x ws) * chi S m x ws = ε * chi S' m' x ws := by
  classical
  obtain ⟨src, neg⟩ := l
  cases src with
  | const =>
    exact ⟨sgn neg, S, m, fun x ws => by simp [Lit.eval, Src.eval]⟩
  | inp i =>
    refine ⟨sgn neg, if i ∈ S then S.erase i else insert i S, m, fun x ws => ?_⟩
    unfold chi
    rw [prod_tog S i (fun i => sgn (x i)) (sgn_mul_self _)]
    simp only [Lit.eval, Src.eval, sgn_xor]
    ring
  | gate j =>
    refine ⟨sgn neg, S, if j ∈ m then m.erase j else insert j m, fun x ws => ?_⟩
    unfold chi
    rw [prod_tog m j (fun j => sgn (ws.getD j false)) (sgn_mul_self _)]
    simp only [Lit.eval, Src.eval, sgn_xor]
    ring

lemma run_snoc (x : ι → Bool) (gs : List (Gate ι)) (g : Gate ι) :
    run x (gs ++ [g]) = run x gs ++ [g.eval x (run x gs)] := by
  simp [run, List.foldl_append]

@[simp] lemma length_run (x : ι → Bool) (gs : List (Gate ι)) : (run x gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [run_snoc, ih]

lemma getD_snoc_of_ne (ws : List Bool) (b : Bool) (j : ℕ) (h : j ≠ ws.length) :
    (ws ++ [b]).getD j false = ws.getD j false := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · have h1 : ws.length ≤ j := le_of_lt h
    have h2 : (ws ++ [b]).length ≤ j := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

lemma getD_snoc_length (ws : List Bool) (b : Bool) :
    (ws ++ [b]).getD ws.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma chi_snoc (S : Finset ι) (m : Finset ℕ) (x : ι → Bool) (ws : List Bool) (b : Bool) :
    chi S m x (ws ++ [b]) =
      chi S (m.erase ws.length) x ws * (if ws.length ∈ m then sgn b else 1) := by
  unfold chi
  have h1 : ∏ j ∈ m.erase ws.length, sgn ((ws ++ [b]).getD j false) =
      ∏ j ∈ m.erase ws.length, sgn (ws.getD j false) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [getD_snoc_of_ne ws b j (Finset.ne_of_mem_erase hj)]
  split_ifs with hm
  · rw [← Finset.mul_prod_erase m _ hm, h1, getD_snoc_length]
    ring
  · rw [Finset.erase_eq_of_notMem hm] at h1 ⊢
    rw [h1, mul_one]

section
variable [Fintype ι] [DecidableEq ι]

/-- The invariant of the induction over the gate list. -/
def Good (t : ℕ) (gs : List (Gate ι)) : Prop :=
  ∀ (S : Finset ι) (m : Finset ℕ),
    (2 : ℤ) ^ Fintype.card ι ∣ 2 ^ t * ∑ x : ι → Bool, chi S m x (run x gs)

lemma Good.lit {t : ℕ} {gs : List (Gate ι)} (h : Good t gs) (l : Lit ι)
    (S : Finset ι) (m : Finset ℕ) :
    (2 : ℤ) ^ Fintype.card ι ∣
      2 ^ t * ∑ x : ι → Bool, sgn (l.eval x (run x gs)) * chi S m x (run x gs) := by
  obtain ⟨ε, S', m', hl⟩ := lit_chi l S m
  simp_rw [hl, ← Finset.mul_sum]
  rw [mul_left_comm]
  exact Dvd.dvd.mul_left (h S' m') ε

lemma Good.lit2 {t : ℕ} {gs : List (Gate ι)} (h : Good t gs) (a b : Lit ι)
    (S : Finset ι) (m : Finset ℕ) :
    (2 : ℤ) ^ Fintype.card ι ∣
      2 ^ t * ∑ x : ι → Bool,
        sgn (a.eval x (run x gs)) * (sgn (b.eval x (run x gs)) * chi S m x (run x gs)) := by
  obtain ⟨ε, S', m', hl⟩ := lit_chi b S m
  have : ∀ x : ι → Bool,
      sgn (a.eval x (run x gs)) * (sgn (b.eval x (run x gs)) * chi S m x (run x gs)) =
      ε * (sgn (a.eval x (run x gs)) * chi S' m' x (run x gs)) := by
    intro x; rw [hl]; ring
  simp_rw [this, ← Finset.mul_sum]
  rw [mul_left_comm]
  exact Dvd.dvd.mul_left (h.lit a S' m') ε

lemma good_nil : Good 0 ([] : List (Gate ι)) := by
  intro S m
  have h1 : ∀ x : ι → Bool, chi S m x (run x ([] : List (Gate ι))) =
      ∏ i : ι, (if i ∈ S then sgn (x i) else 1) := by
    intro x
    simp [chi, sgn]
  have h2 : ∑ x : ι → Bool, ∏ i : ι, (if i ∈ S then sgn (x i) else 1) =
      ∏ i : ι, ∑ b : Bool, (if i ∈ S then sgn b else 1) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2, pow_zero, one_mul, ← Finset.card_univ, ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  by_cases hi : i ∈ S <;> simp [hi, sgn]

lemma Good.xor {t : ℕ} {gs : List (Gate ι)} (h : Good t gs) (a b : Lit ι) :
    Good t (gs ++ [Gate.xor a b]) := by
  intro S m
  simp_rw [run_snoc, chi_snoc, length_run]
  by_cases hm : gs.length ∈ m
  · simp only [hm, ↓reduceIte, Gate.eval, sgn_xor]
    have := h.lit2 a b S (m.erase gs.length)
    convert this using 3
    ring
  · simp only [hm, ↓reduceIte, mul_one]
    exact h S _

lemma Good.and {t : ℕ} {gs : List (Gate ι)} (h : Good t gs) (a b : Lit ι) :
    Good (t + 1) (gs ++ [Gate.and a b]) := by
  intro S m
  simp_rw [run_snoc, chi_snoc, length_run]
  by_cases hm : gs.length ∈ m
  · simp only [hm, ↓reduceIte, Gate.eval]
    set m₀ := m.erase gs.length
    have key : (2 : ℤ) ^ (t + 1) * ∑ x : ι → Bool,
          chi S m₀ x (run x gs) * sgn (a.eval x (run x gs) && b.eval x (run x gs)) =
        2 ^ t * ∑ x : ι → Bool, chi S m₀ x (run x gs)
        + 2 ^ t * ∑ x : ι → Bool, sgn (a.eval x (run x gs)) * chi S m₀ x (run x gs)
        + 2 ^ t * ∑ x : ι → Bool, sgn (b.eval x (run x gs)) * chi S m₀ x (run x gs)
        - 2 ^ t * ∑ x : ι → Bool,
            sgn (a.eval x (run x gs)) * (sgn (b.eval x (run x gs)) * chi S m₀ x (run x gs)) := by
      rw [← mul_add, ← mul_add, ← mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib, pow_succ, mul_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      have := sgn_and (a.eval x (run x gs)) (b.eval x (run x gs))
      linear_combination (chi S m₀ x (run x gs)) * this
    rw [key]
    exact dvd_sub (dvd_add (dvd_add (h S m₀) (h.lit a S m₀)) (h.lit b S m₀)) (h.lit2 a b S m₀)
  · simp only [hm, ↓reduceIte, mul_one]
    rw [pow_succ, mul_assoc, mul_left_comm]
    exact Dvd.dvd.mul_left (h S _) 2

theorem good_andCount (gs : List (Gate ι)) : Good (andCount gs) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact good_nil
  | append_singleton gs g ih =>
    cases g with
    | and a b =>
      have : andCount (gs ++ [Gate.and a b]) = andCount gs + 1 := by
        simp [andCount, List.countP_append, Gate.isAnd]
      rw [this]; exact ih.and a b
    | xor a b =>
      have : andCount (gs ++ [Gate.xor a b]) = andCount gs := by
        simp [andCount, List.countP_append, Gate.isAnd]
      rw [this]; exact ih.xor a b

omit [DecidableEq ι] in
/-- `(-1)^(l·x)` is the product of the signs of the selected inputs. -/
lemma sgn_dot (l x : ι → Bool) :
    sgn (dot l x) = ∏ i ∈ Finset.univ.filter (fun i => l i = true), sgn (x i) := by
  rw [Finset.prod_filter]
  have : ∀ i, (if l i = true then sgn (x i) else 1) =
      if (l i && x i) = true then (-1 : ℤ) else 1 := by
    intro i; cases l i <;> cases x i <;> simp [sgn]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  unfold dot sgn
  generalize (Finset.univ.filter (fun i => (l i && x i) = true)).card = n
  rcases Nat.even_or_odd n with h | h
  · simp [h.neg_one_pow, Nat.not_odd_iff_even.mpr h]
  · simp [h.neg_one_pow, h]

end

/-- The sign of an XOR of a set `T` of outputs, times `chi`, is a constant times a `chi`. -/
lemma outs_chi (outs : κ → Lit ι) (T : Finset κ) :
    ∀ (S : Finset ι) (m : Finset ℕ),
    ∃ (ε : ℤ) (S' : Finset ι) (m' : Finset ℕ), ∀ (x : ι → Bool) (ws : List Bool),
      (∏ o ∈ T, sgn ((outs o).eval x ws)) * chi S m x ws = ε * chi S' m' x ws := by
  classical
  induction T using Finset.induction_on with
  | empty => intro S m; exact ⟨1, S, m, fun x ws => by simp⟩
  | insert o T ho ih =>
    intro S m
    obtain ⟨ε, S', m', h⟩ := ih S m
    obtain ⟨ε', S'', m'', h'⟩ := lit_chi (outs o) S' m'
    refine ⟨ε * ε', S'', m'', fun x ws => ?_⟩
    rw [Finset.prod_insert ho, mul_assoc, h, mul_left_comm, h']
    ring

/-- **Theorem S.** If a circuit on `N = card ι` inputs has `t` AND gates, then `2^(N-t)` divides
the Walsh coefficient `W_{u·F}(l)` of every XOR `u·F` of its outputs, at every linear form `l`. -/
theorem theoremS [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C : Circuit ι κ) (u : κ → Bool) (l : ι → Bool) :
    (2 : ℤ) ^ (Fintype.card ι - C.andCount) ∣ walsh (fun x => dot u (C.eval x)) l := by
  obtain ⟨ε, S, m, h⟩ := outs_chi C.outs (Finset.univ.filter (fun o => u o = true))
    (Finset.univ.filter (fun i => l i = true)) ∅
  have hW : walsh (fun x => dot u (C.eval x)) l =
      ε * ∑ x : ι → Bool, chi S m x (run x C.gates) := by
    unfold walsh
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← h x (run x C.gates), sgn_xor, sgn_dot, sgn_dot]
    simp [chi, Circuit.eval]
  have hG := good_andCount C.gates S m
  have h2 : (2 : ℤ) ^ Fintype.card ι ∣
      2 ^ C.andCount * walsh (fun x => dot u (C.eval x)) l := by
    rw [hW, mul_left_comm]
    exact Dvd.dvd.mul_left hG ε
  by_cases ht : C.andCount ≤ Fintype.card ι
  · have : (2 : ℤ) ^ Fintype.card ι = 2 ^ C.andCount * 2 ^ (Fintype.card ι - C.andCount) := by
      rw [← pow_add]; congr 1; omega
    rw [this] at h2
    exact (mul_dvd_mul_iff_left (by positivity)).mp h2
  · have : Fintype.card ι - C.andCount = 0 := by omega
    rw [this, pow_zero]
    exact one_dvd _

/-- **Corollary.** If a circuit computes `F` and some Walsh coefficient of an XOR of outputs of `F`
equals `±2^e`, then the circuit has at least `N - e` AND gates. -/
theorem andCount_ge_of_walsh_sgn [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C : Circuit ι κ) (F : (ι → Bool) → κ → Bool) (hC : Computes C F)
    (u : κ → Bool) (l : ι → Bool) (e : ℕ) (b : Bool)
    (hW : walsh (fun x => dot u (F x)) l = sgn b * 2 ^ e) :
    Fintype.card ι - e ≤ C.andCount := by
  have h := theoremS C u l
  have : (fun x => dot u (C.eval x)) = (fun x => dot u (F x)) := by
    funext x; rw [hC x]
  rw [this, hW] at h
  have h' : (2 : ℕ) ^ (Fintype.card ι - C.andCount) ∣ 2 ^ e := by
    cases b <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, dvd_neg] at h <;>
      exact_mod_cast h
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h'
  omega

/-- **Corollary** (the case `W = +2^e`). If a circuit computes `F` and some Walsh coefficient of
an XOR of outputs of `F` equals `2^e`, then the circuit has at least `N - e` AND gates. -/
theorem andCount_ge_of_walsh [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C : Circuit ι κ) (F : (ι → Bool) → κ → Bool) (hC : Computes C F)
    (u : κ → Bool) (l : ι → Bool) (e : ℕ)
    (hW : walsh (fun x => dot u (F x)) l = 2 ^ e) :
    Fintype.card ι - e ≤ C.andCount :=
  andCount_ge_of_walsh_sgn C F hC u l e false (by rw [hW]; simp [sgn])

end Mcadd
