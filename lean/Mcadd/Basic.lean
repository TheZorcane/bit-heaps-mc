module

public import Mathlib

/-!
# Basic definitions

* XAG circuits (XOR-AND graphs) with free NOT and constants;
* multiplicative complexity `MC`;
* Walsh coefficients;
* the function `ADD k n` (sum of `k` words modulo `2^n`) and the bound `U k n`.
-/

@[expose] public section

namespace Mcadd

variable {ι κ : Type}

/-! ## XAG circuits -/

/-- What a literal refers to: the constant `false`, an input, or the output of the `j`-th gate
(gates are numbered from `0` in the order of the gate list). -/
inductive Src (ι : Type) where
  | const : Src ι
  | inp (i : ι) : Src ι
  | gate (j : ℕ) : Src ι

/-- A literal: a source, optionally complemented (`neg = true`). NOT is free. -/
structure Lit (ι : Type) where
  src : Src ι
  neg : Bool

/-- A gate: 2-input AND or 2-input XOR of literals. -/
inductive Gate (ι : Type) where
  | and (a b : Lit ι) : Gate ι
  | xor (a b : Lit ι) : Gate ι

/-- Value of a source, given the input `x` and the list `ws` of the values of the gates
computed so far. A reference to a gate that is not yet computed reads `false`. -/
def Src.eval (x : ι → Bool) (ws : List Bool) : Src ι → Bool
  | .const => false
  | .inp i => x i
  | .gate j => ws.getD j false

/-- Value of a literal. -/
def Lit.eval (x : ι → Bool) (ws : List Bool) (l : Lit ι) : Bool :=
  (l.src.eval x ws) ^^ l.neg

/-- Value of a gate. -/
def Gate.eval (x : ι → Bool) (ws : List Bool) : Gate ι → Bool
  | .and a b => a.eval x ws && b.eval x ws
  | .xor a b => a.eval x ws ^^ b.eval x ws

/-- Is the gate an AND gate? -/
def Gate.isAnd : Gate ι → Bool
  | .and _ _ => true
  | .xor _ _ => false

/-- Evaluate a list of gates in order; the result is the list of all gate values.
Gate number `j` can only see the values of gates `0, …, j-1`. -/
def run (x : ι → Bool) (gs : List (Gate ι)) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.eval x ws]) []

/-- Number of AND gates in a gate list. -/
def andCount (gs : List (Gate ι)) : ℕ := gs.countP Gate.isAnd

/-- A circuit with inputs indexed by `ι` and outputs indexed by `κ`:
a list of gates and one literal per output. -/
structure Circuit (ι κ : Type) where
  gates : List (Gate ι)
  outs : κ → Lit ι

/-- The function computed by a circuit. -/
def Circuit.eval (C : Circuit ι κ) (x : ι → Bool) : κ → Bool :=
  fun o => (C.outs o).eval x (run x C.gates)

/-- Number of AND gates of a circuit. -/
def Circuit.andCount (C : Circuit ι κ) : ℕ := Mcadd.andCount C.gates

/-- `C` computes the multi-output Boolean function `F`. -/
def Computes (C : Circuit ι κ) (F : (ι → Bool) → κ → Bool) : Prop :=
  ∀ x, C.eval x = F x

/-- The set of AND counts of circuits computing `F`. -/
def MCSet (F : (ι → Bool) → κ → Bool) : Set ℕ :=
  {t | ∃ C : Circuit ι κ, Computes C F ∧ C.andCount = t}

/-- Multiplicative complexity: the least number of AND gates of a circuit computing `F`. -/
noncomputable def MC (F : (ι → Bool) → κ → Bool) : ℕ := sInf (MCSet F)

/-! ## Walsh coefficients -/

/-- `(-1)^b` as an integer. -/
def sgn (b : Bool) : ℤ := if b then -1 else 1

/-- The `𝔽₂` inner product `l · x = ⊕ᵢ lᵢ xᵢ`. -/
def dot [Fintype ι] (l x : ι → Bool) : Bool :=
  decide (Odd (Finset.univ.filter (fun i => (l i && x i) = true)).card)

/-- Walsh coefficient `W_f(l) = Σ_x (-1)^(f(x) ⊕ l·x)`. -/
def walsh [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) (l : ι → Bool) : ℤ :=
  ∑ x : ι → Bool, sgn (f x ^^ dot l x)

/-! ## Multi-operand modular addition -/

/-- `ADD k n`: the inputs are `k` words of `n` bits, `x (i, b)` is bit `b` (weight `2^b`) of
word `i`; output `j` is bit `j` of `(x₁ + ⋯ + x_k) mod 2^n`. -/
def ADD (k n : ℕ) (x : Fin k × Fin n → Bool) (j : Fin n) : Bool :=
  ((∑ i : Fin k, ∑ b : Fin n, 2 ^ (b : ℕ) * (x (i, b)).toNat) % 2 ^ n).testBit j

/-- `U k n = Σ_{i=1}^{n-1} (k - ⌈k / 2^i⌉)`. -/
def U (k n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 (n - 1), (k - ⌈(k : ℚ) / 2 ^ i⌉₊)

/-! ## Addition with a constant (Theorems 2 and 3 of the paper with a constant `K`) -/

/-- `ADDK k n K`: the same inputs as `ADD k n`; output `j` is bit `j` of
`(x₁ + ⋯ + x_k + K) mod 2^n`. An integer constant can be replaced by its residue mod `2^n`,
so taking `K : ℕ` loses nothing. -/
def ADDK (k n K : ℕ) (x : Fin k × Fin n → Bool) (j : Fin n) : Bool :=
  ((∑ i : Fin k, ∑ b : Fin n, 2 ^ (b : ℕ) * (x (i, b)).toNat + K) % 2 ^ n).testBit j

/-- Carries entering column `j` of the full-adder network for `ADDK k n K`:
`c₀ = 0`, `c_{j+1} = ⌊(k + c_j + K_j)/2⌋`, where `K_j = ⌊K/2^j⌋ mod 2` is bit `j` of `K`. -/
def cK (k K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (k + cK k K j + K / 2 ^ j % 2) / 2

/-- `FA k n K = Σ_{j<n-1} ⌊(k + c_j)/2⌋` with `c_j = cK k K j`: the number of AND gates of the
full-adder network for `ADDK k n K`. -/
def FA (k n K : ℕ) : ℕ := ∑ j ∈ Finset.range (n - 1), (k + cK k K j) / 2

end Mcadd

end
