/-
Copyright (c) 2026 Tom Adamczewski and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.TypeStar
/-!
# Pencils, periodic masks and mortality

The shared vocabulary of the mortality argument: a *pencil* is a matrix of homogeneous linear
forms in three letters, affine in one central parameter whose coefficient is supported in the
distinguished root row; its evaluation at letter vectors, its lift along three elements of an
algebra, forward word products and windows of a letter sequence. A *periodic mask* fixes
nonzero letters at some residues and leaves the others free. `MaskMortality` is the
matrix-mortality property proved in `LeanPool.Koethe.Mortality.MaskMortality`, and
`UniversalMortalSequence` is the target of the construction in
`LeanPool.Koethe.MaskSequence.Universal`.
-/

noncomputable section

namespace KoetheCounterexample

/-- A letter: a vector of three coefficients, one for each generator. -/
abbrev Triple (k : Type*) := Fin 3 → k

/-- A homogeneous three-letter pencil, affine in one central parameter, whose
parameter coefficient is supported in the distinguished row. -/
structure Pencil (k : Type*) [Field k] (d : ℕ) where
  /-- The coefficient matrix of each letter in the parameter-free part. -/
  scalar : Fin 3 → Matrix (Fin (d + 1)) (Fin (d + 1)) k
  /-- The coefficient matrix of each letter multiplying the central parameter. -/
  linear : Fin 3 → Matrix (Fin (d + 1)) (Fin (d + 1)) k
  linear_off_root : ∀ i row col, row ≠ 0 → linear i row col = 0

namespace Pencil

variable {k : Type*} [Field k] {d : ℕ}

@[ext] theorem ext {P Q : Pencil k d}
    (hc : P.scalar = Q.scalar) (hl : P.linear = Q.linear) : P = Q := by
  cases P
  cases Q
  simp_all

instance [Countable k] : Countable (Pencil k d) := by
  have : Countable (Matrix (Fin (d + 1)) (Fin (d + 1)) k) := by
    change Countable (Fin (d + 1) → Fin (d + 1) → k)
    infer_instance
  exact Function.Injective.countable (f := fun P : Pencil k d => (P.scalar, P.linear))
    (fun _ _ h => Pencil.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Evaluation at a constant letter vector. -/
def eval (P : Pencil k d) (v : Triple k) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  fun row col => Polynomial.C (∑ i : Fin 3, v i * P.scalar i row col) +
    Polynomial.X * Polynomial.C (∑ i : Fin 3, v i * P.linear i row col)

/-- Evaluation at three elements of an arbitrary algebra. -/
def lift {R : Type*} [Ring R] [Algebra k R] (P : Pencil k d) (a : Fin 3 → R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial R) :=
  fun row col => Polynomial.C (∑ i : Fin 3, algebraMap k R (P.scalar i row col) * a i) +
    Polynomial.X * Polynomial.C
      (∑ i : Fin 3, algebraMap k R (P.linear i row col) * a i)

/-- Forward chronological multiplication. This is the transfer convention for
backward shifts `(a_i u)(n) = v_n(i) u(n+1)`. -/
def wordProd (P : Pencil k d) (w : List (Triple k)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  (w.map P.eval).prod

@[simp] theorem wordProd_nil (P : Pencil k d) : P.wordProd [] = 1 := rfl

@[simp] theorem wordProd_append (P : Pencil k d) (u w : List (Triple k)) :
    P.wordProd (u ++ w) = P.wordProd u * P.wordProd w := by
  simp [wordProd]

/-- The forward product of the pencil along `len` consecutive letters of `v` from `start`. -/
def window (P : Pencil k d) (v : ℕ → Triple k) (start len : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  P.wordProd (List.ofFn fun i : Fin len => v (start + i.val))

end Pencil

/-- A finite periodic collection of assigned nonzero letter vectors. Unassigned
occurrences of a residue remain independent choices. -/
structure PeriodicMask (k : Type*) [Field k] where
  /-- The period of the mask. -/
  period : ℕ
  /-- The period is positive. -/
  period_pos : 0 < period
  /-- The letter assigned at each residue, or `none` if the residue is free. -/
  value : Fin period → Option (Triple k)
  /-- Every assigned letter is nonzero. -/
  nonzero : ∀ i v, value i = some v → v ≠ 0

namespace PeriodicMask

variable {k : Type*} [Field k]

/-- The assignment of the mask at a site, read off its residue. -/
def lookup (M : PeriodicMask k) (n : ℕ) : Option (Triple k) :=
  M.value ⟨n % M.period, Nat.mod_lt n M.period_pos⟩

/-- The number of free residues in one period. -/
noncomputable def holes (M : PeriodicMask k) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => M.value i = none).card

/-- The number of assigned residues in one period. -/
noncomputable def assigned (M : PeriodicMask k) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => M.value i ≠ none).card

/-- A word agrees with the mask at every assigned position it covers. -/
def Compatible (M : PeriodicMask k) (w : List (Triple k)) : Prop :=
  ∀ (i : Fin w.length) (z : Triple k), M.lookup i.val = some z → w.get i = z

/-- A sequence agrees with the mask at every assigned site. -/
def SeqCompatible (M : PeriodicMask k) (v : ℕ → Triple k) : Prop :=
  ∀ (n : ℕ) (z : Triple k), M.lookup n = some z → v n = z

end PeriodicMask

/-- The algebraic matrix-mortality property needed by the mask construction. -/
def MaskMortality (k : Type*) [Field k] : Prop :=
  ∀ (d : ℕ) (P : Pencil k d) (M : PeriodicMask k),
    M.period < 2 * M.holes →
    ∃ w : List (Triple k), M.period ≤ w.length ∧ M.period ∣ w.length ∧
      (∀ z ∈ w, z ≠ 0) ∧ M.Compatible w ∧ P.wordProd w = 0

/-- A nonvanishing edge sequence killing every one-row pencil on uniformly
bounded windows. Nil bounds are permitted to depend on the pencil. -/
def UniversalMortalSequence (k : Type*) [Field k] (v : ℕ → Triple k) : Prop :=
  (∀ n, v n ≠ 0) ∧ ∀ (d : ℕ) (P : Pencil k d),
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, P.window v n N = 0

end KoetheCounterexample

end
