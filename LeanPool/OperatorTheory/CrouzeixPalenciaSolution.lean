/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.OperatorTheory.Operator.Dilation.Schaeffer
import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothSupportDomain

/-!
# Operator theory (Solution)

Redeclare-bridge: every definition and theorem from
`CrouzeixPalenciaChallenge.lean` is restated in the `PalomarCrouzeixPalencia`
namespace and closed by delegating to the proof library.
-/

open scoped InnerProductSpace Polynomial

namespace PalomarCrouzeixPalencia

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range of a bounded operator. -/
noncomputable def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  { z | ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z }

/-- The supremum norm of a polynomial on a set. -/
noncomputable def polynomialSupNorm (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  ⨆ z ∈ X, ‖Polynomial.eval z p‖

/-- The predicate that `X` is a `K`-polynomial spectral set for `A`. -/
def IsKPolynomialSpectralSet (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  spectrum ℂ (A : E →L[ℂ] E) ⊆ X ∧
  ∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤ K * polynomialSupNorm p X

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
