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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderInterpolation
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LinearSecondOrder

/-!
# Lower-order operators on finite parabolic cylinders

This file packages the analytic form of the error produced by spatial
cutoffs and changes of bundle frame.  Such an error contains no second
spatial derivative of the unknown: it is a `C^{0,α}` coefficient acting on
the first spatial derivative, plus a `C^{0,α}` coefficient acting on the
value.

The resulting map is a genuine bounded linear operator from the finite
`C^{2+α,1+α/2}` jet space to the finite-cylinder source space.  Its
estimate is deliberately stated in terms of the norms of the value and
first-derivative projections.  Consequently the zero-initial short-time
interpolation estimates make the whole lower-order operator small.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

variable {t₀ T α : ℝ}

@[reducible] local instance finiteLowerFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup

@[reducible] local instance finiteLowerFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

@[reducible] local instance finiteLowerFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup

@[reducible] local instance finiteLowerFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

@[reducible] local instance finiteLowerZeroCoeffNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup

@[reducible] local instance finiteLowerZeroCoeffNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace

/-- A first-order coefficient field on a finite parabolic cylinder. -/
abbrev FiniteFirstCoefficientSpace :=
  ParabolicC0AlphaSpace X ((X →L[ℝ] W) →L[ℝ] W) α
    (parabolicFiniteCylinder X t₀ T)

/-- A zeroth-order coefficient field on a finite parabolic cylinder. -/
abbrev FiniteZeroCoefficientSpace :=
  ParabolicC0AlphaSpace X (W →L[ℝ] W) α
    (parabolicFiniteCylinder X t₀ T)

namespace FiniteParabolicC2AlphaBanach

/-- The finite-cylinder lower-order operator
`u ↦ G(∇u) + D(u)` associated with two fixed coefficient fields. -/
def lowerOrderL
    (G : FiniteFirstCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (D : FiniteZeroCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α)) :
    FiniteParabolicC2AlphaBanach X W t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (X →L[ℝ] W) W) G).comp spaceDerivComponentL +
    (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation W W) D).comp valueComponentL

/-- Pointwise readout of the finite-cylinder lower-order operator. -/
theorem evalCLM_lowerOrderL
    (G : FiniteFirstCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (D : FiniteZeroCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X W t₀ T α)
    (z : ℝ × X) (hz : z ∈ parabolicFiniteCylinder X t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz (lowerOrderL G D u) =
      ParabolicC0AlphaSpace.toFun G z (spaceDeriv u z) +
        ParabolicC0AlphaSpace.toFun D z (value u z) := by
  rw [lowerOrderL, ContinuousLinearMap.add_apply, map_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    evalCLM_spaceDerivComponentL, evalCLM_valueComponentL]
  rfl

/-- The lower-order source norm is controlled separately by the full
`C^{0,α}` norms of the gradient and value components. -/
theorem norm_lowerOrderL_apply_le
    (G : FiniteFirstCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (D : FiniteZeroCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X W t₀ T α) :
    ‖lowerOrderL G D u‖ ≤
      (‖operatorEvaluation (X →L[ℝ] W) W‖ * ‖G‖) *
          ‖spaceDerivComponentL u‖ +
        (‖operatorEvaluation W W‖ * ‖D‖) *
          ‖valueComponentL u‖ := by
  let LG := ParabolicC0AlphaBanach.mulCoeffL
    (X := X) (E := (X →L[ℝ] W) →L[ℝ] W)
    (F := X →L[ℝ] W) (G := W)
    (operatorEvaluation (X →L[ℝ] W) W) G
  let LD := ParabolicC0AlphaBanach.mulCoeffL
    (X := X) (E := W →L[ℝ] W) (F := W) (G := W)
    (operatorEvaluation W W) D
  have hG : ‖LG (spaceDerivComponentL u)‖ ≤
      (‖operatorEvaluation (X →L[ℝ] W) W‖ * ‖G‖) *
        ‖spaceDerivComponentL u‖ := by
    calc
      ‖LG (spaceDerivComponentL u)‖ ≤
          ‖LG‖ * ‖spaceDerivComponentL u‖ :=
        LG.le_opNorm (spaceDerivComponentL u)
      _ ≤ (‖operatorEvaluation (X →L[ℝ] W) W‖ * ‖G‖) *
          ‖spaceDerivComponentL u‖ :=
        mul_le_mul_of_nonneg_right
          (ParabolicC0AlphaBanach.norm_mulCoeffL_le
            (operatorEvaluation (X →L[ℝ] W) W) G)
          (norm_nonneg _)
  have hD : ‖LD (valueComponentL u)‖ ≤
      (‖operatorEvaluation W W‖ * ‖D‖) * ‖valueComponentL u‖ := by
    calc
      ‖LD (valueComponentL u)‖ ≤ ‖LD‖ * ‖valueComponentL u‖ :=
        LD.le_opNorm (valueComponentL u)
      _ ≤ (‖operatorEvaluation W W‖ * ‖D‖) *
          ‖valueComponentL u‖ :=
        mul_le_mul_of_nonneg_right
          (ParabolicC0AlphaBanach.norm_mulCoeffL_le
            (operatorEvaluation W W) D)
          (norm_nonneg _)
  rw [lowerOrderL, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change ‖LG (spaceDerivComponentL u) + LD (valueComponentL u)‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add hG hD)

/-- Explicit coefficient-weighted short-time factor for a lower-order
operator. -/
def lowerOrderShortTimeFactor
    (Gnorm Dnorm thickness α : ℝ) : ℝ :=
  ‖operatorEvaluation (X →L[ℝ] W) W‖ * Gnorm *
      gradientShortTimeFactor thickness α +
    ‖operatorEvaluation W W‖ * Dnorm *
      valueShortTimeFactor thickness α

lemma lowerOrderShortTimeFactor_nonneg
    {Gnorm Dnorm thickness α : ℝ}
    (hG : 0 ≤ Gnorm) (hD : 0 ≤ Dnorm) (hthickness : 0 ≤ thickness) :
    0 ≤ lowerOrderShortTimeFactor (X := X) (W := W)
      Gnorm Dnorm thickness α := by
  unfold lowerOrderShortTimeFactor
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (norm_nonneg _) hG)
      (gradientShortTimeFactor_nonneg hthickness))
    (mul_nonneg
      (mul_nonneg (norm_nonneg _) hD)
      (valueShortTimeFactor_nonneg hthickness))

/-- On a zero-initial jet the complete lower-order source norm has the
coefficient-weighted small short-time factor. -/
theorem norm_lowerOrderL_apply_le_shortTimeFactor
    (hT : t₀ < T) (hα : 0 < α) (hα' : α < 1) (hthin : T - t₀ ≤ 1)
    (G : FiniteFirstCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (D : FiniteZeroCoefficientSpace (X := X) (W := W)
      (t₀ := t₀) (T := T) (α := α))
    (u : FiniteParabolicC2AlphaBanach X W t₀ T α)
    (hu₀ : initialTraceL hT hα u = 0) :
    ‖lowerOrderL G D u‖ ≤
      lowerOrderShortTimeFactor (X := X) (W := W)
        ‖G‖ ‖D‖ (T - t₀) α * ‖u‖ := by
  have hgrad := norm_spaceDerivComponentL_le_gradientShortTimeFactor
    hT hα hα' u hu₀
  have hvalue := norm_valueComponentL_le_valueShortTimeFactor
    hT hα hα' hthin u hu₀
  calc
    ‖lowerOrderL G D u‖ ≤
        (‖operatorEvaluation (X →L[ℝ] W) W‖ * ‖G‖) *
            ‖spaceDerivComponentL u‖ +
          (‖operatorEvaluation W W‖ * ‖D‖) *
            ‖valueComponentL u‖ := norm_lowerOrderL_apply_le G D u
    _ ≤ (‖operatorEvaluation (X →L[ℝ] W) W‖ * ‖G‖) *
            (gradientShortTimeFactor (T - t₀) α * ‖u‖) +
          (‖operatorEvaluation W W‖ * ‖D‖) *
            (valueShortTimeFactor (T - t₀) α * ‖u‖) := by
      gcongr
    _ = lowerOrderShortTimeFactor (X := X) (W := W)
          ‖G‖ ‖D‖ (T - t₀) α * ‖u‖ := by
      unfold lowerOrderShortTimeFactor
      ring

end FiniteParabolicC2AlphaBanach
end AnalyticPDE
end RicciFlow
