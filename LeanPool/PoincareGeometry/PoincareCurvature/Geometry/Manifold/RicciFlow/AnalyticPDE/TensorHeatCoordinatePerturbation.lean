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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatInitialTrace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderCauchyOperator

/-!
# Quantitative coordinate perturbation of frozen tensor heat

This file identifies the finite-cylinder coordinate operator

`∂ₜ - A D² - B D - C`

with the genuine frozen tensor-heat operator plus three explicit errors.  The
errors are estimated *after* the frozen inverse.  This distinction retains
the small-time gains of the value and gradient components and the spatial
oscillation gain of the Hessian component, rather than bounding everything
by the full Schauder norm of the inverse.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

variable {d : ℕ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W" => (Fin d × Fin d → ℝ)

@[reducible] local instance coordinatePerturbationWNormedAddCommGroup :
    NormedAddCommGroup W := Pi.normedAddCommGroup
@[reducible] local instance coordinatePerturbationWNormedSpace :
    NormedSpace ℝ W := Pi.normedSpace
@[reducible] local instance coordinatePerturbationFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinatePerturbationFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinatePerturbationSecondNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinatePerturbationSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinatePerturbationPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinatePerturbationPrincipalNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance coordinatePerturbationFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance coordinatePerturbationFirstCoeffNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] W) →L[ℝ] W) := ContinuousLinearMap.toNormedSpace

/-! ## Constant frozen coefficient field -/

/-- The genuine frozen principal symbol, embedded as a constant parabolic
coefficient field on the finite cylinder. -/
def frozenTensorHeatPrincipalField
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (t₀ T α : ℝ) :
    FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α) :=
  ParabolicC0AlphaSpace.constL
    (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
    (frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x)

@[simp]
theorem frozenTensorHeatPrincipalField_apply
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (t₀ T α : ℝ) (z : ℝ × E) :
    ParabolicC0AlphaSpace.toFun
        (frozenTensorHeatPrincipalField
          (I := I) p e b x t₀ T α) z =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x := by
  rw [frozenTensorHeatPrincipalField, ParabolicC0AlphaSpace.toFun_constL]

/-- The coordinate Cauchy operator with the genuine frozen principal field
and zero lower-order fields is definitionally the same differential
expression as `frozenTensorHeatCauchyL`. -/
theorem coordinateCauchyL_frozen_eq
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (t₀ T α : ℝ) :
    FiniteParabolicC2AlphaBanach.coordinateCauchyL
        (frozenTensorHeatPrincipalField
          (I := I) p e b x t₀ T α)
        0 0 =
      frozenTensorHeatCauchyL (I := I) p e b x t₀ T α := by
  ext u
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rw [FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL,
    evalCLM_frozenTensorHeatCauchyL]
  have hB : ParabolicC0AlphaSpace.toFun
      (0 : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
        (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) z = 0 := rfl
  have hC : ParabolicC0AlphaSpace.toFun
      (0 : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
        (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) z = 0 := rfl
  rw [hB, hC]
  simp

/-! ## Error after an arbitrary right parametrix -/

/-- Principal-part error after applying a candidate right parametrix. -/
def tensorHeatPrincipalPostErrorL
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (E →L[ℝ] E →L[ℝ] W) W) (A - A₀)).comp
    (FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL.comp Q)

/-- First-order error after applying a candidate right parametrix. -/
def tensorHeatFirstPostErrorL
    {t₀ T α : ℝ}
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL
      (operatorEvaluation (E →L[ℝ] W) W) B).comp
    (FiniteParabolicC2AlphaBanach.spaceDerivComponentL.comp Q)

/-- Zeroth-order error after applying a candidate right parametrix. -/
def tensorHeatZeroPostErrorL
    {t₀ T α : ℝ}
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) :=
  (ParabolicC0AlphaBanach.mulCoeffL (operatorEvaluation W W) C).comp
    (FiniteParabolicC2AlphaBanach.valueComponentL.comp Q)

/-- Sum of the three coordinate coefficient errors after the right
parametrix. -/
def tensorHeatCoordinatePostErrorL
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :=
  tensorHeatPrincipalPostErrorL A A₀ Q +
    tensorHeatFirstPostErrorL B Q + tensorHeatZeroPostErrorL C Q

/-- Exact operator identity: subtracting the frozen coordinate Cauchy
operator and then applying `Q` gives the negative sum of the three post-error
operators. -/
theorem coordinateCauchyL_sub_frozen_comp
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C -
      FiniteParabolicC2AlphaBanach.coordinateCauchyL A₀ 0 0).comp Q =
      -tensorHeatCoordinatePostErrorL A A₀ B C Q := by
  ext q
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply]
  rw [map_sub, map_neg]
  rw [FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL,
    FiniteParabolicC2AlphaBanach.evalCLM_coordinateCauchyL]
  simp only [tensorHeatCoordinatePostErrorL,
    tensorHeatPrincipalPostErrorL, tensorHeatFirstPostErrorL,
    tensorHeatZeroPostErrorL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply]
  rw [map_add, map_add,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    ParabolicC0AlphaBanach.evalCLM_mulCoeffL_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_spaceSecondDerivComponentL,
    FiniteParabolicC2AlphaBanach.evalCLM_spaceDerivComponentL,
    FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
  simp only [operatorEvaluation_apply]
  have hA : ParabolicC0AlphaSpace.toFun (A - A₀) z =
      ParabolicC0AlphaSpace.toFun A z -
        ParabolicC0AlphaSpace.toFun A₀ z := rfl
  have hB0 : ParabolicC0AlphaSpace.toFun
      (0 : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
        (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) z = 0 := rfl
  have hC0 : ParabolicC0AlphaSpace.toFun
      (0 : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
        (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) z = 0 := rfl
  rw [hA, hB0, hC0, ContinuousLinearMap.sub_apply]
  simp only [ContinuousLinearMap.zero_apply, zero_add, add_zero]
  abel

/-! ## Componentwise quantitative bound -/

/-- The sharp componentwise error constant.  In particular, it does not
replace the three component compositions by the full norm of `Q`. -/
def tensorHeatCoordinatePostErrorBound
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) : ℝ :=
  ‖operatorEvaluation (E →L[ℝ] E →L[ℝ] W) W‖ * ‖A - A₀‖ *
      ‖FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL.comp Q‖ +
    ‖operatorEvaluation (E →L[ℝ] W) W‖ * ‖B‖ *
      ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL.comp Q‖ +
    ‖operatorEvaluation W W‖ * ‖C‖ *
      ‖FiniteParabolicC2AlphaBanach.valueComponentL.comp Q‖

theorem norm_tensorHeatPrincipalPostErrorL_le
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ‖tensorHeatPrincipalPostErrorL A A₀ Q‖ ≤
      ‖operatorEvaluation (E →L[ℝ] E →L[ℝ] W) W‖ * ‖A - A₀‖ *
        ‖FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL.comp Q‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (ParabolicC0AlphaBanach.norm_mulCoeffL_le
        (operatorEvaluation (E →L[ℝ] E →L[ℝ] W) W) (A - A₀))
      (norm_nonneg _))

theorem norm_tensorHeatFirstPostErrorL_le
    {t₀ T α : ℝ}
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ‖tensorHeatFirstPostErrorL B Q‖ ≤
      ‖operatorEvaluation (E →L[ℝ] W) W‖ * ‖B‖ *
        ‖FiniteParabolicC2AlphaBanach.spaceDerivComponentL.comp Q‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (ParabolicC0AlphaBanach.norm_mulCoeffL_le
        (operatorEvaluation (E →L[ℝ] W) W) B)
      (norm_nonneg _))

theorem norm_tensorHeatZeroPostErrorL_le
    {t₀ T α : ℝ}
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ‖tensorHeatZeroPostErrorL C Q‖ ≤
      ‖operatorEvaluation W W‖ * ‖C‖ *
        ‖FiniteParabolicC2AlphaBanach.valueComponentL.comp Q‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (ParabolicC0AlphaBanach.norm_mulCoeffL_le
        (operatorEvaluation W W) C)
      (norm_nonneg _))

theorem norm_tensorHeatCoordinatePostErrorL_le
    {t₀ T α : ℝ}
    (A A₀ : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (Q : ParabolicC0AlphaBanach E W α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W t₀ T α) :
    ‖tensorHeatCoordinatePostErrorL A A₀ B C Q‖ ≤
      tensorHeatCoordinatePostErrorBound A A₀ B C Q := by
  calc
    ‖tensorHeatCoordinatePostErrorL A A₀ B C Q‖
        ≤ ‖tensorHeatPrincipalPostErrorL A A₀ Q‖ +
            ‖tensorHeatFirstPostErrorL B Q‖ +
              ‖tensorHeatZeroPostErrorL C Q‖ := by
          unfold tensorHeatCoordinatePostErrorL
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ tensorHeatCoordinatePostErrorBound A A₀ B C Q := by
          unfold tensorHeatCoordinatePostErrorBound
          exact add_le_add
            (add_le_add
              (norm_tensorHeatPrincipalPostErrorL_le A A₀ Q)
              (norm_tensorHeatFirstPostErrorL_le B Q))
            (norm_tensorHeatZeroPostErrorL_le C Q)

/-! ## Specialization to the genuine frozen inverse -/

/-- For a coordinate coefficient triple, the concrete perturbation from
`TensorHeatLocalInverse` is exactly the negative componentwise post-error. -/
theorem frozenTensorHeatPerturbationL_coordinateCauchyL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (A : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) :
    frozenTensorHeatPerturbationL
        (I := I) p e b x hxChart hT hα hα1
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) =
      -tensorHeatCoordinatePostErrorL A
        (frozenTensorHeatPrincipalField
          (I := I) p e b x t₀ T α) B C
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1) := by
  rw [frozenTensorHeatPerturbationL, ← coordinateCauchyL_frozen_eq
    (I := I) p e b x t₀ T α]
  exact coordinateCauchyL_sub_frozen_comp A
    (frozenTensorHeatPrincipalField
      (I := I) p e b x t₀ T α) B C _

/-- The componentwise constant bounds the actual frozen-relative
perturbation norm. -/
theorem norm_frozenTensorHeatPerturbationL_coordinateCauchyL_le
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (A : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α)) :
    ‖frozenTensorHeatPerturbationL
        (I := I) p e b x hxChart hT hα hα1
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C)‖ ≤
      tensorHeatCoordinatePostErrorBound A
        (frozenTensorHeatPrincipalField
          (I := I) p e b x t₀ T α) B C
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1) := by
  rw [frozenTensorHeatPerturbationL_coordinateCauchyL
    (I := I) p e b hxChart hT hα hα1 A B C, norm_neg]
  exact norm_tensorHeatCoordinatePostErrorL_le _ _ _ _ _

/-- A componentwise bound below one therefore constructs an exact local
solution operator for the variable coordinate tensor-heat equation. -/
theorem exists_localTensorHeatSolutionL_of_coordinate_bound_lt_one
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (A : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (hsmall : tensorHeatCoordinatePostErrorBound A
      (frozenTensorHeatPrincipalField
        (I := I) p e b x t₀ T α) B C
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) < 1) :
    ∃ Q : ParabolicC0AlphaBanach E W α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        FiniteParabolicC2AlphaBanach E W t₀ T α,
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C).comp Q =
        ContinuousLinearMap.id ℝ
          (ParabolicC0AlphaBanach E W α
            (parabolicFiniteCylinder E t₀ T)) := by
  have hpert : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C)‖ < 1 :=
    lt_of_le_of_lt
      (norm_frozenTensorHeatPerturbationL_coordinateCauchyL_le
        (I := I) p e b hxChart hT hα hα1 A B C) hsmall
  refine ⟨localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) hpert, ?_⟩
  exact comp_localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) hpert

/-- The selected coordinate right inverse also has zero canonical initial
trace.  The two operator identities are returned together so the Cauchy
condition cannot be lost when this result is propagated through localization. -/
theorem exists_localTensorHeatSolutionL_of_coordinate_bound_lt_one_zeroTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (A : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := W) (t₀ := t₀) (T := T) (α := α))
    (hsmall : tensorHeatCoordinatePostErrorBound A
      (frozenTensorHeatPrincipalField
        (I := I) p e b x t₀ T α) B C
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) < 1) :
    ∃ Q : ParabolicC0AlphaBanach E W α
          (parabolicFiniteCylinder E t₀ T) →L[ℝ]
        FiniteParabolicC2AlphaBanach E W t₀ T α,
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C).comp Q =
          ContinuousLinearMap.id ℝ
            (ParabolicC0AlphaBanach E W α
              (parabolicFiniteCylinder E t₀ T)) ∧
      (FiniteParabolicC2AlphaBanach.initialTraceL
        (X := E) (E := W) hT hα).comp Q = 0 := by
  have hpert : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C)‖ < 1 :=
    lt_of_le_of_lt
      (norm_frozenTensorHeatPerturbationL_coordinateCauchyL_le
        (I := I) p e b hxChart hT hα hα1 A B C) hsmall
  let Q := localTensorHeatSolutionL
    (I := I) p e b hxFrame hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) hpert
  refine ⟨Q, ?_, ?_⟩
  · exact comp_localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) hpert
  · exact initialTraceL_comp_localTensorHeatSolutionL
      (I := I) p e b hxFrame hxChart hT hα hα1
        (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C) hpert

end AnalyticPDE
end RicciFlow
