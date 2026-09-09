/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFormGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quantitative genuine coefficient calculus for the fixed mean inverse

The actual fixed operator has a polynomial amplitude depending on the time
interval and coefficient bounds. The factorial radius and derivative shift
are preserved by the coefficient-to-time-operator constructions.
-/

@[expose] public section


noncomputable section

namespace EulerMeanFixedCoefficientGevrey

open Set ContinuousLinearMap EulerTimeLp EulerTerminalTimePrimitive EulerMeanSolenoidal
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanFixedCoefficientRegularity
  EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey EulerOperatorGevreyCalculus
  EulerMeanFormGevrey EulerGevrey EulerVolterraConvolution
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey2 : InnerProductSpace ℝ solenoidalSpace :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedCoefficientGevrey4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2
    →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanFixedCoefficientGevrey8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance

private theorem scalar_bound {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (r C : ℝ) (d : ℕ) (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => a • f p) x‖ ≤ (|a| *C)*majorant r d n := by
  calc
    _ = |a| *‖iteratedFDeriv ℝ n f x‖ := by
      rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by
          simp)), norm_smul, Real.norm_eq_abs]
    _ ≤ |a| *(C*majorant r d n) := mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg a)
    _ = _ := by ring

/-- The sharp terminal time bounds control the norm factors in the actual physical form. -/
theorem baseAmplitude_time_bound (T : ℝ) (hT : 0 ≤ T) (CH CC : ℝ)
    (hCH : 0 ≤ CH) (hCC : 0 ≤ CC) :
    baseAmplitude (primitiveTimeLp (E := L2) T hT) (initialTrace (E := L2) T hT) CH CC ≤
      1+(T^2/2)*CH+T*CC := by
  have hJ := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg (T^2/2))).2
    (primitiveTimeLp_norm_le (E := L2) T hT)
  have hR := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg T)).2
    (initialTrace_norm_le (E := L2) T hT)
  have hJ := hJ.trans_eq (Real.sq_sqrt (by positivity : 0 ≤ T^2/2))
  have hR := hR.trans_eq (Real.sq_sqrt hT)
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hJ hCH))
    (mul_le_mul_of_nonneg_right hR hCC)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : P → C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (M0 A : P → L2 →L[ℝ] L2) (L : ℝ)

/-- Restriction to the actual solenoidal space does not enlarge any factorial bound. -/
theorem solenoidalFrame_bound (hF : ContDiff ℝ ∞ F)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (d : ℕ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ C * majorant r d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => solenoidalFrame T (F p)) x‖ ≤ C*majorant r d n :=
  contraction_bound (P := P) (E := C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (F := C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2))
    (framePathRestriction T) (framePathRestriction_norm T) F hF r C hr hC d hb n x

/-- The genuine fixed derivative map has only polynomial time cost. -/
theorem fixedMeanDerivative_bound (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁)
    (r CF CF₁ : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (d : ℕ)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r d n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) x‖ ≤
      (T*CF₁+CF)*majorant r d n :=
  productDerivative_bound T hT (fun p => solenoidalFrame T (F p))
    (fun p => solenoidalFrame T (F₁ p)) (contDiff_solenoidalFrame T F hF)
    (contDiff_solenoidalFrame T F₁ hF₁) r CF CF₁ hr hCF hCF₁ d
    (solenoidalFrame_bound T F hF r CF hr hCF d hFb)
    (solenoidalFrame_bound T F₁ hF₁ r CF₁ hr hCF₁ d hF₁b) n x

/-- A fully explicit polynomial amplitude for actual derivatives of the entire fixed mean operator.
-/
theorem fixedMeanOperator_bound
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁) (hH : ContDiff ℝ ∞ H)
    (hM0 : ContDiff ℝ ∞ M0) (hA : ContDiff ℝ ∞ A)
    (r CF CF₁ CH CM CA : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁)
    (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCA : 0 ≤ CA)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r 0 n)
    (hHb : ∀ n x, ‖iteratedFDeriv ℝ n H x‖ ≤ CH * majorant r 0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n M0 x‖ ≤ CM * majorant r 0 n)
    (hAb : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ CA * majorant r 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => fixedMeanOperator T hT (F p) (F₁ p) (H p) (M0 p) (A p) L) x‖ ≤
      (9*(T*CF₁+CF)^2*(1+(T^2/2)*CH+T*(CM+|L| *CA))) * majorant r 0 n := by
  have hD := contDiff_fixedMeanDerivative T hT F F₁ hF hF₁
  have hDb := fixedMeanDerivative_bound T hT F F₁ hF hF₁ r CF CF₁ hr hCF hCF₁ 0 hFb hF₁b
  have hHC := contDiff_timeMultiplier T hT H hH
  have hHCb := timeMultiplier_bound T hT H hH r CH hr hCH 0 hHb
  have hC : ContDiff ℝ ∞ (fun p => M0 p+L • A p) := hM0.add (hA.const_smul L)
  have hCb := add_bound M0 (fun p => L • A p) hM0 (hA.const_smul L) r CM (|L| *CA) 0
    hMb (scalar_bound L A hA r CA 0 hAb)
  have hD0 : 0 ≤ T*CF₁+CF := add_nonneg (mul_nonneg hT hCF₁) hCF
  have hC0 : 0 ≤ CM+|L| *CA := add_nonneg hCM (mul_nonneg (abs_nonneg L) hCA)
  have hb := pullbackMeanOperator_bound
    (primitiveTimeLp (E := L2) T hT) (initialTrace (E := L2) T hT)
    (fun p => timeMultiplier T hT (H p)) (fun p => M0 p+L • A p)
    (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) hD hHC hC
    r (T*CF₁+CF) CH (CM+|L| *CA) hr hD0 hCH hC0 hDb hHCb hCb n x
  have hb' : ‖iteratedFDeriv ℝ n
      (fun p => fixedMeanOperator T hT (F p) (F₁ p) (H p) (M0 p) (A p) L) x‖ ≤
      (9*(T*CF₁+CF)^2*baseAmplitude (primitiveTimeLp (E := L2) T hT)
        (initialTrace (E := L2) T hT) CH (CM+|L| *CA))*majorant r 0 n := hb
  exact hb'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (baseAmplitude_time_bound T hT CH (CM+|L| *CA) hCH hC0) (by
        positivity))
    (majorant_nonneg r hr 0 n))

/-- The actual force pullback preserves the forcing shift and has explicit polynomial amplitude. -/
theorem fixedMeanForcing_bound (f : P → TimeLp T L2)
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁) (hf : ContDiff ℝ ∞ f)
    (r CF CF₁ Cf : ℝ) (hr : 0 ≤ r) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (d : ℕ)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant r 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant r 0 n)
    (hfb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ Cf * majorant r d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun p => -(fixedMeanPrimitive T hT (F p) (F₁ p)).adjoint (f p)) x‖ ≤
      (3*(T*(T*CF₁+CF))*Cf)*majorant r d n := by
  have hD0 : 0 ≤ T*CF₁+CF := add_nonneg (mul_nonneg hT hCF₁) hCF
  have hb := pullbackMeanForcing_bound (primitiveTimeLp (E := L2) T hT)
    (fun p => fixedMeanDerivative T hT (F p) (F₁ p)) f
    (contDiff_fixedMeanDerivative T hT F F₁ hF hF₁) hf r (T*CF₁+CF) Cf hr hD0 hCf d
    (fixedMeanDerivative_bound T hT F F₁ hF hF₁ r CF CF₁ hr hCF hCF₁ 0 hFb hF₁b) hfb n x
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := L2) T hT) hD0) (by norm_num)) hCf)
    (majorant_nonneg r hr d n))

end EulerMeanFixedCoefficientGevrey
