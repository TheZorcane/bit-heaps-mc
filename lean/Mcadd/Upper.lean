import Mcadd.Lower

/-!
# Upper bound: the full-adder network

We build, for all `k` and `n`, an explicit circuit `addCircuit k n` for `ADD k n`:
columns are processed upwards; in each column below the top one, three wires are replaced by a
sum wire and a carry wire (one AND, `maj(a,b,c) = (a⊕c)(b⊕c)⊕c`) until at most two wires remain,
and two wires are handled by a half adder (one AND). The top column only uses XOR gates.
We prove that the circuit computes `ADD k n` and has exactly `U k n` AND gates.
-/

namespace Mcadd

open Finset

variable {ι : Type}

/-! ## Literals that stay valid when gates are appended -/

/-- The (uncomplemented) output of gate `j`. -/
def gl (j : ℕ) : Lit ι := ⟨.gate j, false⟩

/-- The constant `false`. -/
def Lit.zero : Lit ι := ⟨.const, false⟩

/-- A literal is well-formed for a gate list of length `n` if it does not refer to a gate `≥ n`. -/
def Lit.WF (n : ℕ) (l : Lit ι) : Prop :=
  match l.src with
  | .gate j => j < n
  | _ => True

lemma Lit.WF.mono {n n' : ℕ} {l : Lit ι} (h : l.WF n) (hn : n ≤ n') : l.WF n' := by
  obtain ⟨src, neg⟩ := l
  cases src <;> simp_all [Lit.WF]
  omega

lemma gl_WF {j n : ℕ} (h : j < n) : (gl j : Lit ι).WF n := by
  simpa [gl, Lit.WF] using h

lemma zero_WF (n : ℕ) : (Lit.zero : Lit ι).WF n := by
  simp [Lit.zero, Lit.WF]

lemma eval_append (x : ι → Bool) (ws t : List Bool) (l : Lit ι) (h : l.WF ws.length) :
    l.eval x (ws ++ t) = l.eval x ws := by
  obtain ⟨src, neg⟩ := l
  cases src with
  | const => rfl
  | inp i => rfl
  | gate j =>
    have hj : j < ws.length := by simpa [Lit.WF] using h
    simp [Lit.eval, Src.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma run_append_eq (x : ι → Bool) (gs e : List (Gate ι)) :
    run x (gs ++ e) = e.foldl (fun ws g => ws ++ [g.eval x ws]) (run x gs) := by
  simp [run]

lemma run_append (x : ι → Bool) (gs e : List (Gate ι)) :
    ∃ t, run x (gs ++ e) = run x gs ++ t := by
  induction e using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton e g ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [g.eval x (run x (gs ++ e))], ?_⟩
    rw [← List.append_assoc, run_snoc, ht, List.append_assoc]

/-- Value of a literal after evaluating the gate list `gs` on input `x`. -/
def val (x : ι → Bool) (gs : List (Gate ι)) (l : Lit ι) : Bool := l.eval x (run x gs)

lemma val_mono {gs gs' : List (Gate ι)} (h : gs <+: gs') {l : Lit ι} (hl : l.WF gs.length)
    (x : ι → Bool) : val x gs' l = val x gs l := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨t, ht⟩ := run_append x gs e
  unfold val
  rw [ht, eval_append]
  simpa using hl

lemma eval_run_append {gs : List (Gate ι)} {l : Lit ι} (h : l.WF gs.length) (x : ι → Bool)
    (t : List Bool) : l.eval x (run x gs ++ t) = l.eval x (run x gs) :=
  eval_append x _ t l (by simpa using h)

lemma eval_gl_run_append (x : ι → Bool) (gs : List (Gate ι)) (i : ℕ) (t : List Bool) :
    (gl (gs.length + i) : Lit ι).eval x (run x gs ++ t) = t.getD i false := by
  simp [gl, Lit.eval, Src.eval, List.getD_eq_getElem?_getD, List.getElem?_append_right]

lemma eval_gl_run_append0 (x : ι → Bool) (gs : List (Gate ι)) (t : List Bool) :
    (gl gs.length : Lit ι).eval x (run x gs ++ t) = t.getD 0 false :=
  eval_gl_run_append x gs 0 t

/-- Number of `true` values among a list of literals. -/
def cnt (x : ι → Bool) (gs : List (Gate ι)) (ls : List (Lit ι)) : ℕ :=
  (ls.map fun l => (val x gs l).toNat).sum

lemma cnt_mono {gs gs' : List (Gate ι)} (h : gs <+: gs') {ls : List (Lit ι)}
    (hl : ∀ l ∈ ls, l.WF gs.length) (x : ι → Bool) : cnt x gs' ls = cnt x gs ls := by
  unfold cnt
  congr 1
  apply List.map_congr_left
  intro l hl'
  rw [val_mono h (hl l hl')]

@[simp] lemma cnt_nil (x : ι → Bool) (gs : List (Gate ι)) : cnt x gs [] = 0 := rfl

@[simp] lemma cnt_cons (x : ι → Bool) (gs : List (Gate ι)) (a : Lit ι) (ls : List (Lit ι)) :
    cnt x gs (a :: ls) = (val x gs a).toNat + cnt x gs ls := by
  simp [cnt]

lemma cnt_append (x : ι → Bool) (gs : List (Gate ι)) (as bs : List (Lit ι)) :
    cnt x gs (as ++ bs) = cnt x gs as + cnt x gs bs := by
  simp [cnt]

/-! ## Full adder and half adder -/

/-- Full adder on `a, b, c`: 5 gates, 1 AND. Returns (gates, sum, carry). -/
def fullAdder (gs : List (Gate ι)) (a b c : Lit ι) : List (Gate ι) × Lit ι × Lit ι :=
  (gs ++ [Gate.xor a c, Gate.xor b c, Gate.and (gl gs.length) (gl (gs.length + 1)),
      Gate.xor (gl (gs.length + 2)) c, Gate.xor (gl gs.length) b],
    gl (gs.length + 4), gl (gs.length + 3))

/-- Half adder on `a, b`: 2 gates, 1 AND. Returns (gates, sum, carry). -/
def halfAdder (gs : List (Gate ι)) (a b : Lit ι) : List (Gate ι) × Lit ι × Lit ι :=
  (gs ++ [Gate.xor a b, Gate.and a b], gl gs.length, gl (gs.length + 1))

lemma fullAdder_sem (gs : List (Gate ι)) (a b c : Lit ι) (_ha : a.WF gs.length)
    (hb : b.WF gs.length) (hc : c.WF gs.length) (x : ι → Bool) :
    (val x (fullAdder gs a b c).1 (fullAdder gs a b c).2.1).toNat +
        2 * (val x (fullAdder gs a b c).1 (fullAdder gs a b c).2.2).toNat =
      (val x gs a).toNat + (val x gs b).toNat + (val x gs c).toNat := by
  simp only [fullAdder, val, run_append_eq, List.foldl_cons, List.foldl_nil, Gate.eval,
    List.append_assoc, List.cons_append, List.nil_append,
    eval_run_append hb, eval_run_append hc, eval_gl_run_append, eval_gl_run_append0]
  cases a.eval x (run x gs) <;> cases b.eval x (run x gs) <;> cases c.eval x (run x gs) <;> rfl

lemma halfAdder_sem (gs : List (Gate ι)) (a b : Lit ι) (ha : a.WF gs.length)
    (hb : b.WF gs.length) (x : ι → Bool) :
    (val x (halfAdder gs a b).1 (halfAdder gs a b).2.1).toNat +
        2 * (val x (halfAdder gs a b).1 (halfAdder gs a b).2.2).toNat =
      (val x gs a).toNat + (val x gs b).toNat := by
  simp only [halfAdder, val, run_append_eq, List.foldl_cons, List.foldl_nil, Gate.eval,
    List.append_assoc, List.cons_append, List.nil_append, eval_run_append ha,
    eval_run_append hb, eval_gl_run_append, eval_gl_run_append0]
  cases a.eval x (run x gs) <;> cases b.eval x (run x gs) <;> rfl

/-! ## One column -/

/-- Reduce a column consisting of the wire `s` and the wires in the list, to one sum wire
and a list of carries. Returns (gates, sum, carries). -/
def reduceCol : List (Lit ι) → List (Gate ι) → Lit ι → List (Gate ι) × Lit ι × List (Lit ι)
  | [], gs, s => (gs, s, [])
  | [a], gs, s => ((halfAdder gs s a).1, (halfAdder gs s a).2.1, [(halfAdder gs s a).2.2])
  | a :: b :: rest, gs, s =>
    let fa := fullAdder gs s a b
    let r := reduceCol rest fa.1 fa.2.1
    (r.1, r.2.1, fa.2.2 :: r.2.2)

/-- Specification of a processed column that held `len` wires with `total x` ones. -/
structure ColSpec (gs : List (Gate ι)) (total : (ι → Bool) → ℕ) (len : ℕ)
    (r : List (Gate ι) × Lit ι × List (Lit ι)) : Prop where
  pre : gs <+: r.1
  ands : andCount r.1 = andCount gs + len / 2
  wfs : r.2.1.WF r.1.length
  wfc : ∀ c ∈ r.2.2, c.WF r.1.length
  clen : r.2.2.length = len / 2
  sem : ∀ x, (val x r.1 r.2.1).toNat + 2 * cnt x r.1 r.2.2 = total x

theorem reduceCol_spec : ∀ (rest : List (Lit ι)) (gs : List (Gate ι)) (s : Lit ι),
    s.WF gs.length → (∀ l ∈ rest, l.WF gs.length) →
    ColSpec gs (fun x => (val x gs s).toNat + cnt x gs rest) (rest.length + 1)
      (reduceCol rest gs s)
  | [], gs, s, hs, _ => by
    refine ⟨List.prefix_refl _, by simp [reduceCol], hs, by simp [reduceCol],
      by simp [reduceCol], fun x => by simp [reduceCol]⟩
  | [a], gs, s, hs, hr => by
    have ha : a.WF gs.length := hr a (by simp)
    refine ⟨⟨_, rfl⟩, ?_, ?_, ?_, by simp [reduceCol], fun x => ?_⟩
    · simp [reduceCol, halfAdder, andCount, Gate.isAnd, List.countP_append, List.countP_cons]
    · exact gl_WF (by simp [reduceCol, halfAdder])
    · intro c hc
      simp only [reduceCol, List.mem_singleton] at hc
      rw [hc]
      exact gl_WF (by simp [reduceCol, halfAdder])
    · have := halfAdder_sem gs s a hs ha x
      simpa [reduceCol] using this
  | a :: b :: rest, gs, s, hs, hr => by
    have ha : a.WF gs.length := hr a (by simp)
    have hb : b.WF gs.length := hr b (by simp)
    have hpre : gs <+: (fullAdder gs s a b).1 := ⟨_, rfl⟩
    have hlen : gs.length ≤ (fullAdder gs s a b).1.length := hpre.length_le
    have hsum : (fullAdder gs s a b).2.1.WF (fullAdder gs s a b).1.length :=
      gl_WF (by simp [fullAdder])
    have hcar : (fullAdder gs s a b).2.2.WF (fullAdder gs s a b).1.length :=
      gl_WF (by simp [fullAdder])
    have hrest : ∀ l ∈ rest, l.WF (fullAdder gs s a b).1.length :=
      fun l hl => (hr l (by simp [hl])).mono hlen
    have ih := reduceCol_spec rest (fullAdder gs s a b).1 (fullAdder gs s a b).2.1 hsum hrest
    have hands : andCount (fullAdder gs s a b).1 = andCount gs + 1 := by
      simp [fullAdder, andCount, Gate.isAnd, List.countP_append, List.countP_cons]
    refine ⟨hpre.trans ih.pre, ?_, ih.wfs, ?_, ?_, fun x => ?_⟩
    · have := ih.ands
      simp only [reduceCol, List.length_cons] at this ⊢
      omega
    · intro c hc
      simp only [reduceCol, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hcar.mono ih.pre.length_le
      · exact ih.wfc c hc
    · have := ih.clen
      simp only [reduceCol, List.length_cons] at this ⊢
      omega
    · have h1 := ih.sem x
      have h2 := fullAdder_sem gs s a b hs ha hb x
      have h3 := cnt_mono hpre (fun l hl => hr l (by simp [hl])) x (ls := rest)
      have h4 := val_mono ih.pre hcar x
      simp only [reduceCol, cnt_cons] at h1 h4 ⊢
      rw [h4]
      omega

/-- Process a whole column (possibly empty). -/
def procCol (ls : List (Lit ι)) (gs : List (Gate ι)) : List (Gate ι) × Lit ι × List (Lit ι) :=
  match ls with
  | [] => (gs, Lit.zero, [])
  | s :: rest => reduceCol rest gs s

lemma val_zero (x : ι → Bool) (gs : List (Gate ι)) : val x gs Lit.zero = false := by
  simp [val, Lit.zero, Lit.eval, Src.eval]

theorem procCol_spec (ls : List (Lit ι)) (gs : List (Gate ι)) (h : ∀ l ∈ ls, l.WF gs.length) :
    ColSpec gs (fun x => cnt x gs ls) ls.length (procCol ls gs) := by
  cases ls with
  | nil =>
    exact ⟨List.prefix_refl _, by simp [procCol], zero_WF _, by simp [procCol],
      by simp [procCol], fun x => by simp [procCol, val_zero]⟩
  | cons s rest =>
    have := reduceCol_spec rest gs s (h s (by simp)) (fun l hl => h l (by simp [hl]))
    simpa [procCol] using this

/-! ## The top column: XOR only -/

/-- XOR of the wire `s` and the wires in the list. Returns (gates, result). -/
def xorAll : List (Lit ι) → List (Gate ι) → Lit ι → List (Gate ι) × Lit ι
  | [], gs, s => (gs, s)
  | a :: rest, gs, s => xorAll rest (gs ++ [Gate.xor s a]) (gl gs.length)

lemma val_snoc_new (x : ι → Bool) (gs : List (Gate ι)) (g : Gate ι) :
    val x (gs ++ [g]) (gl gs.length) = g.eval x (run x gs) := by
  unfold val
  rw [run_snoc]
  have := eval_gl_run_append0 x gs [g.eval x (run x gs)]
  simpa using this

theorem xorAll_spec : ∀ (rest : List (Lit ι)) (gs : List (Gate ι)) (s : Lit ι),
    s.WF gs.length → (∀ l ∈ rest, l.WF gs.length) →
    gs <+: (xorAll rest gs s).1 ∧ andCount (xorAll rest gs s).1 = andCount gs ∧
      (xorAll rest gs s).2.WF (xorAll rest gs s).1.length ∧
      ∀ x, (val x (xorAll rest gs s).1 (xorAll rest gs s).2).toNat =
        ((val x gs s).toNat + cnt x gs rest) % 2
  | [], gs, s, hs, _ => by
    refine ⟨List.prefix_refl _, rfl, hs, fun x => ?_⟩
    simp only [xorAll, cnt_nil, add_zero]
    cases val x gs s <;> rfl
  | a :: rest, gs, s, hs, hr => by
    have hpre : gs <+: gs ++ [Gate.xor s a] := ⟨_, rfl⟩
    have hrest : ∀ l ∈ rest, l.WF (gs ++ [Gate.xor s a]).length :=
      fun l hl => (hr l (by simp [hl])).mono hpre.length_le
    obtain ⟨i1, i2, i3, i4⟩ := xorAll_spec rest (gs ++ [Gate.xor s a]) (gl gs.length)
      (gl_WF (by simp)) hrest
    refine ⟨hpre.trans i1, ?_, i3, fun x => ?_⟩
    · rw [xorAll, i2]
      simp [andCount, Gate.isAnd, List.countP_append]
    · have h1 := i4 x
      have h2 := val_snoc_new x gs (Gate.xor s a)
      have h3 := cnt_mono hpre (fun l hl => hr l (by simp [hl])) x (ls := rest)
      rw [xorAll, h1, h2, h3, cnt_cons]
      simp only [Gate.eval]
      change ((val x gs s ^^ val x gs a).toNat + cnt x gs rest) % 2 = _
      cases val x gs s <;> cases val x gs a <;> simp
      omega

/-- Process the top column. -/
def procTop (ls : List (Lit ι)) (gs : List (Gate ι)) : List (Gate ι) × Lit ι :=
  match ls with
  | [] => (gs, Lit.zero)
  | s :: rest => xorAll rest gs s

theorem procTop_spec (ls : List (Lit ι)) (gs : List (Gate ι)) (h : ∀ l ∈ ls, l.WF gs.length) :
    gs <+: (procTop ls gs).1 ∧ andCount (procTop ls gs).1 = andCount gs ∧
      ∀ x, (val x (procTop ls gs).1 (procTop ls gs).2).toNat = cnt x gs ls % 2 := by
  cases ls with
  | nil => exact ⟨List.prefix_refl _, rfl, fun x => by simp [procTop, val_zero]⟩
  | cons s rest =>
    obtain ⟨h1, h2, _, h4⟩ :=
      xorAll_spec rest gs s (h s (by simp)) (fun l hl => h l (by simp [hl]))
    exact ⟨h1, h2, fun x => by simpa [procTop] using h4 x⟩

/-! ## The whole heap -/

/-- Process the columns (least significant first), given the carries `cs` entering the first
column. The last column is the top column. Returns (gates, output literals). -/
def addHeap : List (List (Lit ι)) → List (Gate ι) → List (Lit ι) → List (Gate ι) × List (Lit ι)
  | [], gs, _ => (gs, [])
  | [top], gs, cs => ((procTop (cs ++ top) gs).1, [(procTop (cs ++ top) gs).2])
  | col :: c2 :: cols, gs, cs =>
    let rc := procCol (cs ++ col) gs
    let r := addHeap (c2 :: cols) rc.1 rc.2.2
    (r.1, rc.2.1 :: r.2)

/-- AND count of `addHeap`, from the number `c` of entering carries and the column sizes. -/
def heapAnds : ℕ → List ℕ → ℕ
  | _, [] => 0
  | _, [_] => 0
  | c, v :: w :: rest => (c + v) / 2 + heapAnds ((c + v) / 2) (w :: rest)

/-- The number represented by a heap: column `j` has weight `2^j`. -/
def heapVal (x : ι → Bool) (gs : List (Gate ι)) : List (List (Lit ι)) → ℕ
  | [] => 0
  | col :: cols => cnt x gs col + 2 * heapVal x gs cols

lemma heapVal_mono {gs gs' : List (Gate ι)} (h : gs <+: gs') (x : ι → Bool) :
    ∀ (cols : List (List (Lit ι))), (∀ col ∈ cols, ∀ l ∈ col, l.WF gs.length) →
      heapVal x gs' cols = heapVal x gs cols
  | [], _ => rfl
  | col :: cols, hc => by
    simp only [heapVal]
    rw [cnt_mono h (hc col (by simp)), heapVal_mono h x cols (fun c hc' => hc c (by simp [hc']))]

lemma testBit_bit_zero (b : Bool) (t : ℕ) : (b.toNat + 2 * t).testBit 0 = b := by
  rw [Nat.testBit_zero]
  cases b <;> simp

lemma testBit_bit_succ (b : Bool) (t j : ℕ) :
    (b.toNat + 2 * t).testBit (j + 1) = t.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  cases b <;> simp
  omega

/-- Specification of `addHeap`. -/
structure HeapSpec (gs : List (Gate ι)) (cs : List (Lit ι)) (cols : List (List (Lit ι)))
    (r : List (Gate ι) × List (Lit ι)) : Prop where
  pre : gs <+: r.1
  ands : andCount r.1 = andCount gs + heapAnds cs.length (cols.map List.length)
  sem : ∀ x j, j < cols.length →
    val x r.1 (r.2.getD j Lit.zero) = (cnt x gs cs + heapVal x gs cols).testBit j

theorem addHeap_spec : ∀ (cols : List (List (Lit ι))) (gs : List (Gate ι)) (cs : List (Lit ι)),
    (∀ c ∈ cs, c.WF gs.length) → (∀ col ∈ cols, ∀ l ∈ col, l.WF gs.length) →
    HeapSpec gs cs cols (addHeap cols gs cs)
  | [], gs, cs, _, _ =>
    ⟨List.prefix_refl _, by simp [addHeap, heapAnds], fun x j hj => by simp at hj⟩
  | [top], gs, cs, hcs, hcols => by
    have hall : ∀ l ∈ cs ++ top, l.WF gs.length := by
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact hcs l h
      · exact hcols top (by simp) l h
    obtain ⟨h1, h2, h3⟩ := procTop_spec (cs ++ top) gs hall
    refine ⟨h1, by simp [addHeap, heapAnds, h2], fun x j hj => ?_⟩
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    have := h3 x
    rw [cnt_append] at this
    simp only [addHeap, heapVal, List.getD_cons_zero, mul_zero, add_zero, Nat.testBit_zero]
    cases hv : val x (procTop (cs ++ top) gs).1 (procTop (cs ++ top) gs).2 <;>
      simp [hv] at this ⊢ <;> omega
  | col :: c2 :: cols, gs, cs, hcs, hcols => by
    have hall : ∀ l ∈ cs ++ col, l.WF gs.length := by
      intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact hcs l h
      · exact hcols col (by simp) l h
    have hc := procCol_spec (cs ++ col) gs hall
    have hcols' : ∀ c ∈ c2 :: cols, ∀ l ∈ c, l.WF gs.length :=
      fun c hc' => hcols c (List.mem_cons_of_mem _ hc')
    have ih := addHeap_spec (c2 :: cols) (procCol (cs ++ col) gs).1 (procCol (cs ++ col) gs).2.2
      hc.wfc (fun c hc' l hl => (hcols' c hc' l hl).mono hc.pre.length_le)
    refine ⟨hc.pre.trans ih.pre, ?_, fun x j hj => ?_⟩
    · have h1 := ih.ands
      have h2 := hc.ands
      have h3 := hc.clen
      simp only [addHeap, List.map_cons, heapAnds, List.length_append] at h1 h2 h3 ⊢
      rw [h1, h2, h3]
      omega
    · have hsem := hc.sem x
      have hT : cnt x gs cs + heapVal x gs (col :: c2 :: cols) =
          (val x (procCol (cs ++ col) gs).1 (procCol (cs ++ col) gs).2.1).toNat +
            2 * (cnt x (procCol (cs ++ col) gs).1 (procCol (cs ++ col) gs).2.2 +
              heapVal x (procCol (cs ++ col) gs).1 (c2 :: cols)) := by
        rw [heapVal_mono hc.pre x (c2 :: cols) hcols']
        simp only [cnt_append] at hsem
        simp only [heapVal] at hsem ⊢
        omega
      rw [hT]
      cases j with
      | zero =>
        rw [testBit_bit_zero]
        simp only [addHeap, List.getD_cons_zero]
        exact val_mono ih.pre hc.wfs x
      | succ j =>
        rw [testBit_bit_succ]
        simp only [addHeap, List.getD_cons_succ]
        exact ih.sem x j (by simpa using hj)

/-! ## The circuit for `ADD k n` -/

/-- The columns of `ADD k n`: column `j` holds bit `j` of each of the `k` words. -/
def addCols (k n : ℕ) : List (List (Lit (Fin k × Fin n))) :=
  List.ofFn fun j : Fin n => List.ofFn fun i : Fin k => (⟨.inp (i, j), false⟩ : Lit (Fin k × Fin n))

/-- The full-adder network for `ADD k n`. -/
def addCircuit (k n : ℕ) : Circuit (Fin k × Fin n) (Fin n) where
  gates := (addHeap (addCols k n) [] []).1
  outs := fun j => (addHeap (addCols k n) [] []).2.getD j Lit.zero

lemma heapVal_ofFn (x : ι → Bool) (gs : List (Gate ι)) :
    ∀ (n : ℕ) (f : Fin n → List (Lit ι)),
      heapVal x gs (List.ofFn f) = ∑ j : Fin n, 2 ^ (j : ℕ) * cnt x gs (f j)
  | 0, f => by simp [heapVal]
  | n + 1, f => by
    rw [List.ofFn_succ, heapVal, heapVal_ofFn x gs n, Fin.sum_univ_succ, Finset.mul_sum]
    simp [pow_succ, mul_comm, mul_left_comm]

lemma heapAnds_replicate (k : ℕ) : ∀ (m j : ℕ),
    heapAnds (cc k j) (List.replicate (m + 1) k) = ∑ i ∈ range m, cc k (j + i + 1)
  | 0, j => by simp [heapAnds]
  | m + 1, j => by
    have h1 : (cc k j + k) / 2 = cc k (j + 1) := by simp [cc, add_comm]
    rw [List.replicate_succ, List.replicate_succ, heapAnds, ← List.replicate_succ, h1,
      heapAnds_replicate k m (j + 1), Finset.sum_range_succ']
    simp only [add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    omega

theorem addCircuit_spec (k n : ℕ) :
    HeapSpec [] [] (addCols k n) (addHeap (addCols k n) [] []) :=
  addHeap_spec (addCols k n) [] [] (by simp) (by
    intro col hcol l hl
    simp only [addCols, List.mem_ofFn] at hcol
    obtain ⟨j, rfl⟩ := hcol
    simp only [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    simp [Lit.WF])

/-- The full-adder network computes `ADD k n`. -/
theorem addCircuit_computes (k n : ℕ) : Computes (addCircuit k n) (ADD k n) := by
  intro x
  funext j
  have h := (addCircuit_spec k n).sem x j (by simp [addCols])
  have hval : heapVal x [] (addCols k n) =
      ∑ i : Fin k, ∑ b : Fin n, 2 ^ (b : ℕ) * (x (i, b)).toNat := by
    rw [addCols, heapVal_ofFn, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    congr 1
    simp [cnt, List.sum_ofFn, val, Lit.eval, Src.eval, Function.comp_def]
  unfold Circuit.eval ADD
  change val x (addCircuit k n).gates ((addCircuit k n).outs j) = _
  rw [Nat.testBit_mod_two_pow, ← hval]
  simp only [addCircuit, Fin.is_lt, decide_true, Bool.true_and]
  rw [h]
  simp

/-- The full-adder network has exactly `U k n` AND gates. -/
theorem addCircuit_andCount (k n : ℕ) : (addCircuit k n).andCount = U k n := by
  have h := (addCircuit_spec k n).ands
  have hlen : (addCols k n).map List.length = List.replicate n k := by
    simp [addCols, List.map_ofFn, Function.comp_def, List.ofFn_const]
  rw [hlen] at h
  unfold Circuit.andCount
  simp only [addCircuit]
  rw [h, U_eq_UU]
  cases n with
  | zero => simp [heapAnds, UU, andCount]
  | succ m =>
    have := heapAnds_replicate k m 0
    simp only [cc, zero_add] at this
    simp [andCount, UU, this, cc]

/-- **Upper bound**: `ADD k n` has a circuit with `U k n` AND gates. -/
theorem upper_bound (k n : ℕ) : U k n ∈ MCSet (ADD k n) :=
  ⟨addCircuit k n, addCircuit_computes k n, addCircuit_andCount k n⟩

end Mcadd
