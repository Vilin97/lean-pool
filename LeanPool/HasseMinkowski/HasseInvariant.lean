/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Layer 2c of the Hasse–Minkowski development: the Hasse–Minkowski invariant

Over a field `k` whose Hilbert symbol is the one attached to a number field, every nondegenerate
quadratic form is isometric to a diagonal form `w₀ X₀² + ⋯ + w_{n-1} X_{n-1}²` with nonzero
structure constants.  The **Hasse–Minkowski invariant** of such a diagonal form is the product of
all the pairwise Hilbert symbols

`ε(w) = ∏_{i < j} (wᵢ, wⱼ)_k`.

This file defines `hasseMinkowskiInvAux` on the diagonal data and proves the elementary
evaluations of the invariant.  These are exactly the statements of Serre's *Cours
d'arithmétique*, Ch. IV, together with the small-rank computations used in the classification.

## Main definitions

* `hasseMinkowskiInvAux w`: the invariant of the diagonal form with weights `w : Fin n → kˣ`.

## Main results

* `hasseMinkowskiInvAux_zero`, `hasseMinkowskiInvAux_one`, `hasseMinkowskiInvAux_two`,
  `hasseMinkowskiInvAux_three`: the invariant in ranks `0` through `3`.
* `hasseMinkowskiInvAux_cons`: prepending a rank-one weight multiplies the invariant by the
  product of the Hilbert symbols of the new weight against the old ones.
* `hasseMinkowskiInvAux_prod_rank_one`: with a bilinear Hilbert symbol, the same product collapses
  to a single Hilbert symbol with the product (discriminant) of the old weights.
* `hasseMinkowskiInvAux_eq_one_or_neg_one`: the invariant is `1` or `-1`.

## Omitted

The well-definedness of the invariant, i.e. the statement that equivalent diagonal forms have the
same invariant (`hasseMinkowskiInvAux.eq_of_equivalent` in the reference development), is *not*
stated here: it depends on the theory of Hilbert symbols over local fields that is not yet
available in this project.  A form-level invariant `hasseMinkowskiInv` is therefore kept as a
`private` definition that no theorem or consumer exposes.  As a consequence the computational
lemmas at the level of `hasseMinkowskiInv` (which all pass through well-definedness) are also
omitted.  In particular the reference development's `hasseMinkowskiInv.weightedSumSquares`,
`…_two`, `…_three`, `hasseMinkowskiInv.prod_rank_one` and
`hasseMinkowskiInv.of_baseChange_weightedSumSquares` are not reproduced: without
`eq_of_equivalent` there is no way to identify the diagonalization chosen by `Classical.choose`
with any concrete list of weights.  The diagonal-level statements (`hasseMinkowskiInvAux_*`)
proved here are exactly the part of the development that does not need that machinery.
-/

public section

namespace HasseMinkowski

variable {k : Type*} [Field k]

/-! ### The invariant of a diagonal form -/

/-- The Hasse–Minkowski invariant of the diagonal form with nonzero weights `w : Fin n → kˣ`,
namely the product `∏_{i < j} (wᵢ, wⱼ)_k` of the Hilbert symbols of all pairs of weights. -/
noncomputable def hasseMinkowskiInvAux {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2 : k)

-- Theorem: definitional unfolding of `hasseMinkowskiInvAux`.
theorem hasseMinkowskiInvAux_def {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkowskiInvAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2 : k) := by rfl

-- Theorem: the invariant of the empty diagonal form (rank `0`) is `1`.
theorem hasseMinkowskiInvAux_zero (w : Fin 0 → kˣ) : hasseMinkowskiInvAux w = 1 := by
  rw [hasseMinkowskiInvAux_def]
  simp

-- Theorem: the invariant of a rank-`1` diagonal form is `1` (the empty product).
theorem hasseMinkowskiInvAux_one (w : Fin 1 → kˣ) : hasseMinkowskiInvAux w = 1 := by
  rw [hasseMinkowskiInvAux_def]
  have h : ({p : Fin 1 × Fin 1 | p.1 < p.2} : Finset (Fin 1 × Fin 1)) = ∅ := by
    ext p
    obtain ⟨i, j⟩ := p
    fin_cases i; fin_cases j; simp
  rw [h, Finset.prod_empty]

-- Theorem: the invariant of a rank-`2` diagonal form is the single Hilbert symbol of its weights.
theorem hasseMinkowskiInvAux_two (w : Fin 2 → kˣ) :
    hasseMinkowskiInvAux w = hilbertSym (w 0 : k) (w 1 : k) := by
  rw [hasseMinkowskiInvAux_def]
  have h : ({p : Fin 2 × Fin 2 | p.1 < p.2} : Finset (Fin 2 × Fin 2)) =
      {((0 : Fin 2), (1 : Fin 2))} := by
    ext p
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j <;> simp
  rw [h, Finset.prod_singleton]

-- Theorem: the invariant of a rank-`3` diagonal form is the product of the three pairwise
-- Hilbert symbols.
theorem hasseMinkowskiInvAux_three (w : Fin 3 → kˣ) :
    hasseMinkowskiInvAux w = hilbertSym (w 0 : k) (w 1 : k) * hilbertSym (w 0 : k) (w 2 : k) *
      hilbertSym (w 1 : k) (w 2 : k) := by
  rw [hasseMinkowskiInvAux_def]
  have h : ({p : Fin 3 × Fin 3 | p.1 < p.2} : Finset (Fin 3 × Fin 3)) =
      {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} := by
    ext p
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp [mul_assoc]

/-! ### The invariant only takes the values `1` and `-1` -/

-- Theorem: for nonzero arguments the Hilbert symbol is `1` or `-1`.
theorem hilbertSym_eq_one_or_neg_one_of_ne_zero {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ∨ hilbertSym a b = -1 := by
  rcases hilbertSym_eq_one_or a b with h | h | h
  · exact Or.inl h
  · exact absurd ((hilbertSym_eq_zero_iff a b).mp h) (by tauto)
  · exact Or.inr h

-- Theorem: the Hasse–Minkowski invariant of a diagonal form is `1` or `-1`.
theorem hasseMinkowskiInvAux_eq_one_or_neg_one {n : ℕ} (w : Fin n → kˣ) :
    hasseMinkowskiInvAux w = 1 ∨ hasseMinkowskiInvAux w = -1 := by
  rw [hasseMinkowskiInvAux_def, ← Int.isUnit_iff]
  rw [IsUnit.prod_iff]
  intro p _
  exact Int.isUnit_iff.mpr
    (hilbertSym_eq_one_or_neg_one_of_ne_zero (Units.ne_zero _) (Units.ne_zero _))

/-! ### Splitting off a rank-one factor -/

-- Theorem: prepending a rank-one weight multiplies the invariant by the product of the Hilbert
-- symbols of the new weight against all the old ones.
theorem hasseMinkowskiInvAux_cons {n : ℕ} (a : kˣ) (w : Fin n → kˣ) :
    hasseMinkowskiInvAux (Fin.cons a w) =
      (∏ i : Fin n, hilbertSym (a : k) (w i : k)) * hasseMinkowskiInvAux w := by
  simp only [hasseMinkowskiInvAux_def, Finset.prod_filter, Fintype.prod_prod_type,
    Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_lt_succ_iff]
  simp

-- Theorem: with a bilinear Hilbert symbol, prepending a rank-one weight multiplies the invariant
-- by the Hilbert symbol of the new weight against the product (discriminant) of the old weights.
theorem hasseMinkowskiInvAux_prod_rank_one [HasBilinHilbertSym k] {n : ℕ} (a : kˣ)
    (w : Fin n → kˣ) :
    hasseMinkowskiInvAux (Fin.cons a w) =
      hilbertSym (a : k) (∏ i : Fin n, (w i : k)) * hasseMinkowskiInvAux w := by
  rw [hasseMinkowskiInvAux_cons]
  congr 1
  have h1 : hilbertSym (a : k) (1 : k) = 1 := by
    have hmul : hilbertSym (a : k) (1 : k) =
        hilbertSym (a : k) (1 : k) * hilbertSym (a : k) (1 : k) := by
      simpa using (HasBilinHilbertSym.mul_right_eq (a := (a : k)) (b := (1 : k)) (b' := (1 : k)))
    have hne : hilbertSym (a : k) (1 : k) ≠ 0 := by
      simp [hilbertSym_eq_zero_iff]
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact hmul)).symm
  let φ : k →* ℤ :=
    { toFun := fun b => hilbertSym (a : k) b
      map_one' := h1
      map_mul' := fun b b' => HasBilinHilbertSym.mul_right_eq (a := (a : k)) }
  exact (map_prod φ (fun i : Fin n => (w i : k)) Finset.univ).symm

/-! ### The invariant of a nondegenerate form -/

/-- The Hasse–Minkowski invariant of a nondegenerate quadratic form `Q`: diagonalize `Q` as
`w₀ X₀² + ⋯ + w_{n-1} X_{n-1}²` and take `hasseMinkowskiInvAux w`.

The definition uses a chosen diagonalization (`Classical.choose`), so it is only meaningful once
well-definedness under equivalence is available; that fact is not yet proved in this project, so
the definition is `private` and no computational lemmas at this level are stated. -/
private noncomputable def hasseMinkowskiInv {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Invertible (2 : k)]
    (Q : QuadraticForm k V) (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  hasseMinkowskiInvAux
    (QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

end HasseMinkowski
