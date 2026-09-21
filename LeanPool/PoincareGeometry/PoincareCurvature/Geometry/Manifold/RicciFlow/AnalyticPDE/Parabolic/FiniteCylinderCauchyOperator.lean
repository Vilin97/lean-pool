/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderBanach
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LinearSecondOrder

/-!
# Coordinate Cauchy operators on finite parabolic cylinders

This is the finite-time counterpart of `CoordinateCauchyOperator`.  It acts
on the complete genuine higher space over `(t₀,T] × X`, and evaluates to
the classical differential expression at every point of that cylinder.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[reducible] local instance finiteCauchyFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteCauchyFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteCauchyHessianNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteCauchyHessianNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteCauchyPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteCauchyPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteCauchyFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] E) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteCauchyFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] E) →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

namespace FiniteParabolicC2AlphaBanach

variable {t₀ T α : ℝ}

abbrev PrincipalCoefficientSpace :=
  ParabolicC0AlphaSpace X ((X →L[ℝ] X →L[ℝ] E) →L[ℝ] E) α
    (parabolicFiniteCylinder X t₀ T)

abbrev FirstCoefficientSpace :=
  ParabolicC0AlphaSpace X ((X →L[ℝ] E) →L[ℝ] E) α
    (parabolicFiniteCylinder X t₀ T)

abbrev ZeroCoefficientSpace :=
  ParabolicC0AlphaSpace X (E →L[ℝ] E) α (parabolicFiniteCylinder X t₀ T)

/-- `A(D²u)+B(Du)+C(u)` on the finite-cylinder higher Banach space. -/
def coordinateSecondOrderL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (X →L[ℝ] X →L[ℝ] E) E) A).comp
      spaceSecondDerivComponentL +
    (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (X →L[ℝ] E) E) B).comp spaceDerivComponentL +
    (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation E E) C).comp valueComponentL

/-- `∂ₜ-A D²-BD-C` on the finite-cylinder higher Banach space. -/
def coordinateCauchyL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α)) :
    FiniteParabolicC2AlphaBanach X E t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X E α (parabolicFiniteCylinder X t₀ T) :=
  timeDerivComponentL - coordinateSecondOrderL A B C

theorem evalCLM_coordinateSecondOrderL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (coordinateSecondOrderL A B C u) =
      ParabolicC0AlphaSpace.toFun A z (spaceSecondDeriv u z) +
        ParabolicC0AlphaSpace.toFun B z (spaceDeriv u z) +
          ParabolicC0AlphaSpace.toFun C z (value u z) := by
  change ParabolicC0AlphaBanach.evalCLM z hz
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

theorem evalCLM_coordinateCauchyL
    (A : PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) (z : ℝ × X)
    (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (coordinateCauchyL A B C u) =
      timeDeriv u z -
        (ParabolicC0AlphaSpace.toFun A z (spaceSecondDeriv u z) +
          ParabolicC0AlphaSpace.toFun B z (spaceDeriv u z) +
            ParabolicC0AlphaSpace.toFun C z (value u z)) := by
  rw [coordinateCauchyL, ContinuousLinearMap.sub_apply, map_sub,
    evalCLM_coordinateSecondOrderL, evalCLM_timeDerivComponentL]

/-- The finite-cylinder Cauchy operator commutes exactly with terminal-time
restriction, provided its three coefficient fields are restricted to the same
shorter cylinder. -/
theorem coordinateCauchyL_restrictTerminal
    {S : ℝ} (hST : S ≤ T)
    (A : PrincipalCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (B : FirstCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (C : ZeroCoefficientSpace (X := X) (E := E) (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    coordinateCauchyL
        (ParabolicC0AlphaSpace.restrictL
          (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST) A)
        (ParabolicC0AlphaSpace.restrictL
          (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST) B)
        (ParabolicC0AlphaSpace.restrictL
          (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST) C)
        (restrictTerminal hST u) =
      ParabolicC0AlphaBanach.restrictL
        (parabolicFiniteCylinder_mono (X := X) (t₀ := t₀) hST)
        (coordinateCauchyL A B C u) := by
  apply ParabolicC0AlphaBanach.eq_of_eval_eq
  intro z hz
  rw [evalCLM_coordinateCauchyL,
    ParabolicC0AlphaBanach.evalCLM_restrictL_apply,
    evalCLM_coordinateCauchyL]
  rw [timeDeriv_restrictTerminal hST u hz,
    spaceSecondDeriv_restrictTerminal hST u hz,
    spaceDeriv_restrictTerminal hST u hz,
    value_restrictTerminal hST u hz]
  simp only [ParabolicC0AlphaSpace.toFun_restrictL]

end FiniteParabolicC2AlphaBanach

end AnalyticPDE
end RicciFlow
