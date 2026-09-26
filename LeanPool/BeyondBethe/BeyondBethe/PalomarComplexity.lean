/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham

/-!
# A source-stable statement of polynomial time for Palomar

Palomar compares the declarations exported from `Challenge.lean` and
`Solution.lean`.  A recursive definition written with equation syntax acquires
module-private auxiliary declarations, so copying Complexitylib's definition
of recursion on notation into a standalone challenge does not produce the
same exported declaration.  This file gives an equivalent presentation using
the public recursor `List.rec`.  It is therefore declaration-stable when copied
to the Mathlib-only challenge.

The final theorem below embeds Complexitylib's Cobham class into this
presentation.  Together with Complexitylib's formalized Cobham theorem, this
shows that membership still has its usual meaning: deterministic polynomial
time on finite bitstrings.
-/

@[expose] public section

namespace BeyondBethe.PalomarComplexity

/-- Recursion on the bit notation of the first input, written directly with
`List.rec` so its declaration has no module-private equation compiler helper. -/
def recNotation {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool)
    (x : List Bool) (v : Fin n → List Bool) : List Bool :=
  List.rec g
    (fun b tail recurse parameters =>
      (bif b then h₁ else h₀)
        (Fin.cons tail (Fin.cons (recurse parameters) parameters)))
    x v

@[simp] theorem recNotation_nil {n : ℕ}
    (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool)
    (v : Fin n → List Bool) :
    recNotation g h₀ h₁ [] v = g v := by
  rfl

@[simp] theorem recNotation_cons {n : ℕ}
    (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool)
    (b : Bool) (tail : List Bool) (v : Fin n → List Bool) :
    recNotation g h₀ h₁ (b :: tail) v =
      (bif b then h₁ else h₀)
        (Fin.cons tail (Fin.cons (recNotation g h₀ h₁ tail v) v)) := by
  rfl

/-- Cobham's algebra of polynomial-time bitstring functions, in a
source-stable presentation suitable for Palomar's challenge/solution
comparison. -/
inductive Cobham : ∀ {n : ℕ}, ((Fin n → List Bool) → List Bool) → Prop
  | proj {n : ℕ} (i : Fin n) : Cobham fun v => v i
  | empty {n : ℕ} : Cobham fun _ : Fin n → List Bool => []
  | bit (b : Bool) : Cobham fun v : Fin 1 → List Bool =>
      b :: v ⟨0, Nat.zero_lt_succ 0⟩
  | smash : Cobham fun v : Fin 2 → List Bool =>
      Complexity.smash
        (v ⟨0, Nat.zero_lt_succ 1⟩)
        (v ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩)
  | comp {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
      {gs : Fin m → (Fin n → List Bool) → List Bool} :
      Cobham f → (∀ i, Cobham (gs i)) →
      Cobham fun v => f fun i => gs i v
  | boundedRec {n : ℕ} {g : (Fin n → List Bool) → List Bool}
      {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
      {j : (Fin (n + 1) → List Bool) → List Bool} :
      Cobham g → Cobham h₀ → Cobham h₁ → Cobham j →
      (∀ x v, (recNotation g h₀ h₁ x v).length ≤
        (j (Fin.cons x v)).length) →
      Cobham fun v : Fin (n + 1) → List Bool =>
        recNotation g h₀ h₁ (v ⟨0, Nat.zero_lt_succ n⟩) (Fin.tail v)

/-- The unary fragment of the source-stable Cobham algebra. -/
def CobhamFP : Set (List Bool → List Bool) :=
  {f | Cobham fun v : Fin 1 → List Bool =>
    f (v ⟨0, Nat.zero_lt_succ 0⟩)}

theorem recNotation_eq_complexity {n : ℕ}
    (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) :
    recNotation g h₀ h₁ = Complexity.recNotation g h₀ h₁ := by
  funext x v
  induction x with
  | nil => rfl
  | cons b tail ih =>
      simp only [recNotation_cons, Complexity.recNotation_cons, ih]

/-- Complexitylib's standard Cobham class embeds into the source-stable
presentation. -/
theorem of_complexity_cobham {n : ℕ}
    {f : (Fin n → List Bool) → List Bool}
    (hf : Complexity.Cobham f) : Cobham f := by
  induction hf with
  | proj i => exact .proj i
  | empty => exact .empty
  | bit b => exact .bit b
  | smash => exact .smash
  | comp hf hgs ihf ihgs => exact .comp ihf ihgs
  | @boundedRec n g h₀ h₁ j hg hh₀ hh₁ hj hbound ihg ihh₀ ihh₁ ihj =>
      have hstable : Cobham fun v : Fin (n + 1) → List Bool =>
          recNotation g h₀ h₁ (v ⟨0, Nat.zero_lt_succ n⟩) (Fin.tail v) := by
        refine .boundedRec ihg ihh₀ ihh₁ ihj ?_
        intro x v
        simpa only [recNotation_eq_complexity] using! hbound x v
      simpa only [recNotation_eq_complexity] using! hstable

/-- The source-stable presentation also embeds back into Complexitylib's
standard Cobham class. -/
theorem to_complexity_cobham {n : ℕ}
    {f : (Fin n → List Bool) → List Bool}
    (hf : Cobham f) : Complexity.Cobham f := by
  induction hf with
  | proj i => exact .proj i
  | empty => exact .empty
  | bit b => exact .bit b
  | smash => exact .smash
  | comp hf hgs ihf ihgs => exact .comp ihf ihgs
  | @boundedRec n g h₀ h₁ j hg hh₀ hh₁ hj hbound ihg ihh₀ ihh₁ ihj =>
      have hstandard : Complexity.Cobham fun v : Fin (n + 1) → List Bool =>
          Complexity.recNotation g h₀ h₁
            (v ⟨0, Nat.zero_lt_succ n⟩) (Fin.tail v) := by
        refine .boundedRec ihg ihh₀ ihh₁ ihj ?_
        intro x v
        simpa only [recNotation_eq_complexity] using! hbound x v
      simpa only [recNotation_eq_complexity] using! hstandard

/-- Every polynomial-time function in Complexitylib's Cobham presentation
belongs to the source-stable presentation used in the Palomar statement. -/
theorem cobhamFP_of_complexity {f : List Bool → List Bool}
    (hf : f ∈ Complexity.CobhamFP) : f ∈ CobhamFP :=
  of_complexity_cobham hf

/-- The Palomar-facing class is extensionally the usual Cobham class used by
Complexitylib. -/
theorem cobhamFP_iff_complexity {f : List Bool → List Bool} :
    f ∈ CobhamFP ↔ f ∈ Complexity.CobhamFP := by
  constructor
  · intro hf
    exact to_complexity_cobham hf
  · exact cobhamFP_of_complexity

end BeyondBethe.PalomarComplexity
