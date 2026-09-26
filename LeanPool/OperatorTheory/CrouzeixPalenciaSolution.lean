/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.OperatorTheory.Operator.Dilation.Schaeffer
public import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
public import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportDomain

/-!
# Operator theory (Solution)

Compatibility namespace for the upstream `CrouzeixPalenciaChallenge.lean` statements.
The definitions abbreviate the proof library's public representations, and the
theorems delegate to its proofs.
-/

@[expose] public section

open scoped InnerProductSpace Polynomial

namespace PalomarCrouzeixPalencia

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range of a bounded operator. -/
noncomputable abbrev numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  _root_.numericalRange A

/-- The supremum norm of a polynomial on a set. -/
noncomputable abbrev polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  _root_.polynomialSupNorm p X

/-- The predicate that `X` is a `K`-polynomial spectral set for `A`. -/
abbrev IsKPolynomialSpectralSet (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  _root_.IsKPolynomialSpectralSet A K X

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_unitary_power_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) :=
  _root_.exists_unitary_power_dilation T hT

theorem vonNeumann_inequality (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval T p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) :=
  _root_.vonNeumann_inequality T hT p

theorem crouzeix_palencia (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) :=
  _root_.crouzeix_palencia A

end PalomarCrouzeixPalencia

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
