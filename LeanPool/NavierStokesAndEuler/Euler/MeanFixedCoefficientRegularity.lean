/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEstimates
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap

@[expose] public section

/-!
# Genuine parameter regularity of the fixed mean form

Restricting a coefficient to the ordinary solenoidal space is itself a bounded
linear map. The actual time multipliers, H¹ transport, trace, and full mean
form therefore inherit parameter regularity from the coefficient paths.
-/

noncomputable section

namespace EulerMeanFixedCoefficientRegularity

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanVariationalOperator
  EulerTimeLpCoefficientMap EulerTransverseGramInverse EulerTransverseVariationalInverse
  EulerHilbertCoerciveTransport EulerVolterraConvolution
open scoped ContDiff

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) :=
  inferInstance
private local instance (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) :=
  inferInstance

/-- The actual continuous linear restriction of spatial operators to L²σ. -/
def frameRestriction : (L2 →L[ℝ] L2) →L[ℝ] (solenoidalSpace →L[ℝ] L2) :=
  (compL ℝ solenoidalSpace L2 L2).flip solenoidalSpace.subtypeL

/-- The actual continuous linear restriction of time-dependent spatial operators. -/
def framePathRestriction (T : ℝ) :
    C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) →L[ℝ] C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) :=
  frameRestriction.compLeftContinuous ℝ (Icc (0 : ℝ) T)

@[simp] theorem framePathRestriction_apply (T : ℝ) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    framePathRestriction T F = solenoidalFrame T F := rfl

/-- Solenoidal frame restriction is a norm contraction. -/
theorem framePathRestriction_norm (T : ℝ) : ‖framePathRestriction T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro F
  simpa only [framePathRestriction_apply, one_mul] using solenoidalFrame_norm_le T F

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : P → C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (M0 A : P → L2 →L[ℝ] L2) (L : ℝ) {n : ℕ∞ω}

/-- The actual restricted frame has the given parameter regularity. -/
theorem contDiff_solenoidalFrame (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun p => solenoidalFrame T (F p)) := by
  change ContDiff ℝ n ((framePathRestriction T) ∘ F)
  exact ContDiff.comp (g := framePathRestriction T) (f := F)
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
      (F := C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)) (framePathRestriction T)) hF

/-- The genuine physical derivative map inherits parameter regularity. -/
theorem contDiff_fixedMeanDerivative (hF : ContDiff ℝ n F) (hF₁ : ContDiff ℝ n F₁) :
    ContDiff ℝ n (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) :=
  contDiff_productDerivative T hT (fun p => solenoidalFrame T (F p))
    (fun p => solenoidalFrame T (F₁ p)) (contDiff_solenoidalFrame T F hF)
    (contDiff_solenoidalFrame T F₁ hF₁)

/-- The genuine displacement primitive map inherits parameter regularity. -/
theorem contDiff_fixedMeanPrimitive (hF : ContDiff ℝ n F) (hF₁ : ContDiff ℝ n F₁) :
    ContDiff ℝ n (fun p => fixedMeanPrimitive T hT (F p) (F₁ p)) :=
  contDiff_const.clm_comp (contDiff_fixedMeanDerivative T hT F F₁ hF hF₁)

/-- The actual initial-trace map inherits parameter regularity. -/
theorem contDiff_fixedMeanTrace (hF : ContDiff ℝ n F) (hF₁ : ContDiff ℝ n F₁) :
    ContDiff ℝ n (fun p => fixedMeanTrace T hT (F p) (F₁ p)) :=
  contDiff_const.clm_comp (contDiff_fixedMeanDerivative T hT F F₁ hF hF₁)

/-- The full mean form, including the nonlocal boundary term, is a genuinely
regular family whenever its actual coefficient paths are. -/
theorem contDiff_fixedMeanOperator
    (hF : ContDiff ℝ n F) (hF₁ : ContDiff ℝ n F₁) (hH : ContDiff ℝ n H)
    (hM0 : ContDiff ℝ n M0) (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (fun p => fixedMeanOperator T hT (F p) (F₁ p) (H p) (M0 p) (A p) L) := by
  have hD := contDiff_fixedMeanDerivative T hT F F₁ hF hF₁
  have hDadj : ContDiff ℝ n (fun p => (fixedMeanDerivative T hT (F p) (F₁ p)).adjoint) :=
    (realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hD
  have hHC := contDiff_timeMultiplier T hT H hH
  have hC : ContDiff ℝ n (fun p => M0 p+L • A p) := hM0.add (hA.const_smul L)
  have hbase : ContDiff ℝ n (fun p =>
      meanOperator (primitiveTimeLp T hT) (initialTrace T hT)
        (timeMultiplier T hT (H p)) (M0 p+L • A p)) := by
    exact (contDiff_const.sub (contDiff_const.clm_comp (hHC.clm_comp contDiff_const))).add
      (contDiff_const.clm_comp (hC.clm_comp contDiff_const))
  exact hDadj.clm_comp (hbase.clm_comp hD)

end EulerMeanFixedCoefficientRegularity
