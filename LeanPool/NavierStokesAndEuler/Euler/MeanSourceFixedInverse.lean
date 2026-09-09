/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceVariationalInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientTime
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceOperatorRegularity

/-!
# The actual source mean inverse on a fixed spatial Hilbert space

The lower boundary bound is discharged by the proved harmonic localization
estimate. Coefficients are actual bounded smooth matrix fields. The fixed
coordinate solver is identified with the original source mean solver, and its
spatial translation regularity follows from the constructed coefficient families.
-/

@[expose] public section


noncomputable section

namespace EulerMeanSourceFixedInverse

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceOperatorRegularity
  EulerMeanTimeTranslation EulerTimeLp EulerCoerciveProjection
open scoped NNReal ContDiff

-- Reuse the nested Hilbert-space instances in the source solver construction.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceFixedInverse1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceFixedInverse2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceFixedInverse3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanSourceFixedInverse4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanSourceFixedInverse5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace)
    := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanSourceFixedInverse6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

/-- The actual full source form on fixed solenoidal derivative coordinates. -/
def sourceFixedForm : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace :=
  fixedMeanOperator T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L

/-- The positive source coercivity constant uses the actual inverse-frame bound. -/
def sourceFixedCoercivity : ℝ :=
  fixedMeanCoercivity T (operatorPath T F.field) (operatorPath T F₁.field) FInv

include hT in
theorem sourceFixedCoercivity_pos : 0 < sourceFixedCoercivity T F F₁ FInv :=
  fixedMeanCoercivity_pos T hT (operatorPath T F.field) (operatorPath T F₁.field) FInv

include hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall in
/-- The source's spatial and time assumptions imply fixed-space coercivity. -/
theorem sourceFixedForm_coercive (v : TimeLp T solenoidalSpace) :
    sourceFixedCoercivity T F F₁ FInv*‖v‖^2 ≤ ⟪sourceFixedForm T hT ℓ hℓ F F₁ H M0 L v,v⟫_ℝ :=
  fixedMeanOperator_coercive T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    FInv hInv hF K (effectiveNegativeBound Be Bc r) hK
    (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0
    (operatorPath_quadratic_upper T H.field K hH)
    (scaled_mean_boundary_lower_bound ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) v

/-- The fixed coordinate source solver is constructed from the proved coercive form. -/
def sourceCoordinateSolver : TimeLp T L2 →L[ℝ] TimeLp T solenoidalSpace :=
  (coerciveInverse (sourceFixedForm T hT ℓ hℓ F F₁ H M0 L) (sourceFixedCoercivity T F F₁ FInv)
    (sourceFixedCoercivity_pos T hT F F₁ FInv)
    (sourceFixedForm_coercive T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall)).comp
    (-(fixedMeanPrimitive T hT (operatorPath T F.field) (operatorPath T F₁.field)).adjoint)

/-- The new fixed representation is exactly the original actual source solver in coordinates. -/
theorem sourceCoordinateSolver_eq_mean
    (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
    (f : TimeLp T L2) :
    sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall f =
    meanBackward T hT FInv (operatorPath T F.field) (operatorPath T F₁.field) hInv
      (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
        ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
        FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
            f) :=
  fixedMeanSolver_eq_mean T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    FInv hInv hF K (effectiveNegativeBound Be Bc r) hK
    (effectiveNegativeBound_nonneg Be Bc r hBe hBc hr) hF0
    (operatorPath_quadratic_upper T H.field K hH)
    (scaled_mean_boundary_lower_bound ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore)
    (source_smallness T K Be Bc r hsmall) hRight f

/-- Actual smooth coefficients and a smooth forcing orbit imply a smooth source-solution orbit;
no inverse regularity or coercivity premise remains to be supplied. -/
theorem sourceCoordinateSolver_translation_contDiff (f : TimeLp T L2)
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f)) :
    ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a
      (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
        hext hcore hInv hF K hK hF0 hH hsmall f)) :=
  sourceSolution_translation_contDiff T hT F F₁ H M0 (scaledCutoff ℓ hℓ) L
    (sourceFixedCoercivity T F F₁ FInv) (sourceFixedCoercivity_pos T hT F F₁ FInv)
    (sourceFixedForm_coercive T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall) f hf

end EulerMeanSourceFixedInverse
