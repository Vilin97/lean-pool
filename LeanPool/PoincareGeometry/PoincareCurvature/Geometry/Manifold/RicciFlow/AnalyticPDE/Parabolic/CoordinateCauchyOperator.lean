/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.HigherBanachSpace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LinearSecondOrder

/-!
# The coordinate parabolic Cauchy operator on the higher Banach space

This file bundles the genuine differential expression

`u ↦ ∂ₜ u - A(D²u) - B(Du) - C(u)`

as a bounded linear map from the closed derivative-graph Banach space to the
parabolic `C^{0,α}` Banach space.  The coefficient multiplications are the
actual pointwise contractions by `A`, `B`, and `C`; the four inputs are the
bounded projections of a compatible second jet.  Consequently the evaluation
theorem below recovers the displayed differential operator at every
space-time point.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Keep operator-valued coefficient instances deterministic.
@[reducible] local instance coordinateCauchyFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinateCauchyFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinateCauchyHessianNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinateCauchyHessianNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinateCauchyPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinateCauchyPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinateCauchyFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinateCauchyFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

namespace GlobalParabolicC2AlphaBanach

variable {α : ℝ}

/-- The type of principal coefficient fields `A`. -/
abbrev PrincipalCoefficientSpace :=
  ParabolicC0AlphaSpace X
    ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) α
    (Set.univ : Set (ℝ × X))

/-- The type of first-order coefficient fields `B`. -/
abbrev FirstCoefficientSpace :=
  ParabolicC0AlphaSpace X ((X →L[ℝ] E) →L[ℝ] E) α
    (Set.univ : Set (ℝ × X))

/-- The type of zeroth-order coefficient fields `C`. -/
abbrev ZeroCoefficientSpace :=
  ParabolicC0AlphaSpace X (E →L[ℝ] E) α
    (Set.univ : Set (ℝ × X))

/-- The spatial second-order part `A(D²u) + B(Du) + C(u)` as a bounded
operator from the genuine higher Banach space to `C^{0,α}`. -/
def coordinateSecondOrderL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (α := α)) :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (X →L[ℝ] X →L[ℝ] E) E) A).comp
      spaceSecondDerivComponentL +
    (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (X →L[ℝ] E) E) B).comp
      spaceDerivComponentL +
    (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation E E) C).comp valueComponentL

/-- The full coordinate parabolic operator `∂ₜ - A D² - B D - C` as a
bounded linear map between Banach spaces. -/
def coordinateCauchyL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (α := α)) :
    GlobalParabolicC2AlphaBanach X E α →L[ℝ]
      ParabolicC0AlphaBanach X E α (Set.univ : Set (ℝ × X)) :=
  timeDerivComponentL - coordinateSecondOrderL A B C

/-- Pointwise readout of the bundled spatial second-order operator. -/
theorem evalCLM_coordinateSecondOrderL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (α := α))
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z)
        (coordinateSecondOrderL A B C u) =
      ParabolicC0AlphaSpace.toFun A z (spaceSecondDeriv u z) +
        ParabolicC0AlphaSpace.toFun B z (spaceDeriv u z) +
          ParabolicC0AlphaSpace.toFun C z (value u z) := by
  change ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z)
      (((ParabolicC0AlphaBanach.mulCoeffL
          (operatorEvaluation (X →L[ℝ] X →L[ℝ] E) E) A)
          (spaceSecondDerivComponentL u) +
        (ParabolicC0AlphaBanach.mulCoeffL
          (operatorEvaluation (X →L[ℝ] E) E) B)
          (spaceDerivComponentL u)) +
        (ParabolicC0AlphaBanach.mulCoeffL (operatorEvaluation E E) C)
          (valueComponentL u)) = _
  rw [map_add, map_add,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    evalCLM_spaceSecondDerivComponentL,
    evalCLM_spaceDerivComponentL, evalCLM_valueComponentL]
  simp only [operatorEvaluation_apply]

/-- Pointwise readout of the bundled Cauchy operator: this is literally the
stored genuine time derivative minus the coefficient contraction of the
stored genuine spatial two-jet. -/
theorem evalCLM_coordinateCauchyL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (α := α))
    (u : GlobalParabolicC2AlphaBanach X E α) (z : ℝ × X) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z)
        (coordinateCauchyL A B C u) =
      timeDeriv u z -
        (ParabolicC0AlphaSpace.toFun A z (spaceSecondDeriv u z) +
          ParabolicC0AlphaSpace.toFun B z (spaceDeriv u z) +
            ParabolicC0AlphaSpace.toFun C z (value u z)) := by
  rw [coordinateCauchyL, ContinuousLinearMap.sub_apply, map_sub,
    evalCLM_coordinateSecondOrderL]
  rw [ParabolicC0AlphaBanach.evalCLM_eq_representative]
  rfl

end GlobalParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
