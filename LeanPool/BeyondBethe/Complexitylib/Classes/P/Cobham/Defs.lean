/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Cobham's characterization of FP — definitions

This file defines Cobham's machine-independent characterization of the polynomial-time
computable functions on bitstrings (Cobham, *The intrinsic computational difficulty of
functions*, 1965): the smallest class of functions `(Fin n → List Bool) → List Bool`
containing the projections, the empty string, the two bit successors, and the smash
function, and closed under composition and **limited recursion on notation**.

Bitstrings are LSB-first: in the recursion on notation, the head of the list is the
least-significant (innermost) bit, so the bit successors *prepend* a bit
(`x ↦ b :: x`, the string analogue of `n ↦ 2·n + bit`), and recursion on notation
peels bits off the head.

The functions are multi-arity (indexed by `Fin n` argument vectors) because limited
recursion on notation inherently produces functions of higher arity; the unary fragment
is collected in `CobhamFP`, which `Complexitylib.Classes.P.Cobham` proves equal to the
machine class `FP`.

## Main definitions

- `Complexity.smash` — binary-word smash: `1^(|x| · |y|)`
- `Complexity.recNotation` — the recursion-on-notation combinator
- `Complexity.Cobham` — the inductive predicate carving out Cobham's function algebra
- `Complexity.CobhamFP` — the unary fragment, as a set of string functions

## Design notes

The bound in `Cobham.boundedRec` follows Cobham's original formulation: the recursively
defined function must be *length-bounded by another function of the class* (rather than
by an external polynomial). Together with `smash` and the successors this realizes
exactly the polynomial length bounds, which is what makes the class no larger than `FP`;
dropping the bound would admit iterated doubling and hence exponential growth.

The string toolkit the proof is written in — bit dispatch, flags, fixed-width blocks
— is not part of this statement and lives in
`Complexitylib.Classes.P.Cobham.Internal.Blocks`.
-/


@[expose] public section

namespace Complexity

/-- **Cobham's smash function** in the binary-word presentation:
`smash x y = 1^(|x| · |y|)`. This is the length-arithmetic engine of the class:
composing `smash` with the bit successors and projections realizes every polynomial
length bound, which is what lets `Cobham.boundedRec` bound recursions by a function of
the class itself.

This all-one word is the customary string analogue of Cobham's original
number-theoretic smash `x # y = 2^(|x|·|y|)`. -/
def smash (x y : List Bool) : List Bool :=
  List.replicate (x.length * y.length) true

@[simp] theorem smash_length (x y : List Bool) :
    (smash x y).length = x.length * y.length := by
  simp [smash]


/-- **Recursion on notation**: the string analogue of primitive recursion, recursing on
the bit structure of the first argument.

`recNotation g h₀ h₁ x v` computes `g v` when `x` is empty, and on `b :: x` applies the
step function selected by the bit `b` to the argument vector consisting of the tail
`x`, the recursive value on the tail, and the parameters `v`. -/
def recNotation {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) :
    List Bool → (Fin n → List Bool) → List Bool
  | [], v => g v
  | b :: x, v =>
      (bif b then h₁ else h₀) (Fin.cons x (Fin.cons (recNotation g h₀ h₁ x v) v))

@[simp] theorem recNotation_nil {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (v : Fin n → List Bool) :
    recNotation g h₀ h₁ [] v = g v := rfl

@[simp] theorem recNotation_cons {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (b : Bool) (x : List Bool)
    (v : Fin n → List Bool) :
    recNotation g h₀ h₁ (b :: x) v =
      (bif b then h₁ else h₀) (Fin.cons x (Fin.cons (recNotation g h₀ h₁ x v) v)) := rfl

/-- **Cobham's function algebra**: the smallest class of bitstring functions containing
the projections, the empty string, the bit successors `x ↦ b :: x`, and `smash`, and
closed under composition and limited recursion on notation.

In `boundedRec`, the recursion is *limited*: the result must be length-bounded,
uniformly in the arguments, by a function `j` already in the class. This is the
polynomial-growth leash that pins the class to exactly `FP`
(see `Complexitylib.Classes.P.Cobham`). -/
inductive Cobham : ∀ {n : ℕ}, ((Fin n → List Bool) → List Bool) → Prop
  /-- Every projection is in the class. -/
  | proj {n : ℕ} (i : Fin n) : Cobham fun v => v i
  /-- The empty-string constant (at every arity) is in the class. -/
  | empty {n : ℕ} : Cobham fun _ : Fin n → List Bool => []
  /-- The bit successors `x ↦ b :: x` (the string analogue of `n ↦ 2·n + b`) are in
  the class. -/
  | bit (b : Bool) : Cobham fun v : Fin 1 → List Bool => b :: v 0
  /-- The smash function is in the class. -/
  | smash : Cobham fun v : Fin 2 → List Bool => smash (v 0) (v 1)
  /-- The class is closed under composition. -/
  | comp {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
      {gs : Fin m → (Fin n → List Bool) → List Bool} :
      Cobham f → (∀ i, Cobham (gs i)) → Cobham fun v => f fun i => gs i v
  /-- The class is closed under **limited recursion on notation**: recursion on the bit
  structure of the first argument, provided the result is length-bounded by a function
  `j` of the class. -/
  | boundedRec {n : ℕ} {g : (Fin n → List Bool) → List Bool}
      {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
      {j : (Fin (n + 1) → List Bool) → List Bool} :
      Cobham g → Cobham h₀ → Cobham h₁ → Cobham j →
      (∀ x v, (recNotation g h₀ h₁ x v).length ≤ (j (Fin.cons x v)).length) →
      Cobham fun v : Fin (n + 1) → List Bool => recNotation g h₀ h₁ (v 0) (Fin.tail v)

/-- The unary fragment of Cobham's function algebra, as a class of string functions.
`Complexitylib.Classes.P.Cobham` proves `CobhamFP = FP`: this machine-independent
algebra carves out exactly the polynomial-time computable functions. -/
def CobhamFP : Set (List Bool → List Bool) :=
  {f | Cobham fun v : Fin 1 → List Bool => f (v 0)}

end Complexity
