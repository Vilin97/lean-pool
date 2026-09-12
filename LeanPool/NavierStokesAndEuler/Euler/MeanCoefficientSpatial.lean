/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientMultipliers
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffTaylor
import Mathlib.Algebra.Order.Star.Real

/-! Spatial translations and their genuine uniform-norm derivatives for matrix coefficients. -/

@[expose] public section


noncomputable section

namespace EulerMeanCoefficients

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal Filter
open scoped ContDiff BoundedContinuousFunction Topology

section BoundedFields

variable {V : Type*} [NormedAddCommGroup V]

/-- Translated, given by `A.compContinuous ⟨fun x => x+a, continuous_id.add continuous_const⟩`. -/
def translated (A : Space →ᵇ V) (a : Space) : Space →ᵇ V :=
  A.compContinuous ⟨fun x => x+a, continuous_id.add continuous_const⟩

@[simp] theorem translated_apply (A : Space →ᵇ V) (a x : Space) :
    translated A a x = A (x+a) := rfl

@[simp] theorem translated_zero (A : Space →ᵇ V) : translated A 0 = A := by
  ext x
  exact congrArg A (add_zero x)

theorem translated_add (A : Space →ᵇ V) (a b : Space) :
    translated (translated A a) b = translated A (b+a) := by
  ext x
  exact congrArg A (add_assoc x b a)

theorem translated_norm_le (A : Space →ᵇ V) (a : Space) : ‖translated A a‖ ≤ ‖A‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _

variable [NormedSpace ℝ V]

/-- Bounded derivative, given by `BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ (A :
Space → V)) (hA.fderiv_right (m := ∞) (by simp)).continuous C hC`. -/
def boundedDerivative (A : Space →ᵇ V) (hA : ContDiff ℝ ∞ (A : Space → V))
    (C : ℝ) (hC : ∀ x, ‖fderiv ℝ (A : Space → V) x‖ ≤ C) :
    Space →ᵇ (Space →L[ℝ] V) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ (A : Space → V))
    (hA.fderiv_right (m := ∞) (by simp)).continuous C hC

/-- Field direction, constructed using `BoundedContinuousFunction.ofNormedAddCommGroup`. -/
def fieldDirection (DA : Space →ᵇ (Space →L[ℝ] V)) (a : Space) : Space →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => DA x a)
    (DA.continuous.clm_apply continuous_const) (‖DA‖ * ‖a‖)
    (fun x => (DA x).le_opNorm a |>.trans
      (mul_le_mul_of_nonneg_right (DA.norm_coe_le_norm x) (norm_nonneg a)))

@[simp] theorem fieldDirection_apply (DA : Space →ᵇ (Space →L[ℝ] V)) (a x : Space) :
    fieldDirection DA a x = DA x a := rfl

theorem fieldDirection_norm_le (DA : Space →ᵇ (Space →L[ℝ] V)) (a : Space) :
    ‖fieldDirection DA a‖ ≤ ‖DA‖ * ‖a‖ :=
  (BoundedContinuousFunction.norm_le (f := fieldDirection DA a)
    (mul_nonneg (norm_nonneg DA) (norm_nonneg a))).2
    (fun x => (DA x).le_opNorm a |>.trans
      (mul_le_mul_of_nonneg_right (DA.norm_coe_le_norm x) (norm_nonneg a)))

/-- Field derivative linear, bundling `toFun`, `map_add`, `map_smul`. -/
def fieldDerivativeLinear (DA : Space →ᵇ (Space →L[ℝ] V)) : Space →ₗ[ℝ] (Space →ᵇ V) where
  toFun := fieldDirection DA
  map_add' a b := by ext x; exact (DA x).map_add a b
  map_smul' c a := by ext x; exact (DA x).map_smul c a

/-- Field derivative map, bundling `toLinearMap`, `cont`. -/
def fieldDerivativeMap (DA : Space →ᵇ (Space →L[ℝ] V)) : Space →L[ℝ] (Space →ᵇ V) where
  toLinearMap := fieldDerivativeLinear DA
  cont := AddMonoidHomClass.continuous_of_bound (fieldDerivativeLinear DA) ‖DA‖
    (fieldDirection_norm_le DA)

@[simp] theorem fieldDerivativeMap_apply (DA : Space →ᵇ (Space →L[ℝ] V)) (a x : Space) :
    fieldDerivativeMap DA a x = DA x a := rfl

theorem translated_taylor_bound (A : Space →ᵇ V) (DA : Space →ᵇ (Space →L[ℝ] V))
    (hA : ContDiff ℝ ∞ (A : Space → V))
    (hDA : ∀ x, DA x = fderiv ℝ (A : Space → V) x)
    (M : ℝ) (hM : 0 ≤ M)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ (A : Space → V)) x‖ ≤ M) (a b : Space) :
    ‖translated A b - translated A a - fieldDerivativeMap (translated DA a) (b-a)‖ ≤
      M * ‖b-a‖^2 := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hM (sq_nonneg _))).2
  intro x
  change ‖A (x+b) - A (x+a) - DA (x+a) (b-a)‖ ≤ _
  rw [hDA]
  have h := EulerMeanBoundary.norm_linearization_remainder_le
    (A : Space → V) hA M hM h₂ (x+a) (b-a)
  have he : x+a+(b-a) = x+b := by abel
  rwa [he] at h

/-- Bounded actual second derivatives yield the true Fréchet derivative of translation in sup norm.
-/
theorem translated_hasFDerivAt (A : Space →ᵇ V) (DA : Space →ᵇ (Space →L[ℝ] V))
    (hA : ContDiff ℝ ∞ (A : Space → V))
    (hDA : ∀ x, DA x = fderiv ℝ (A : Space → V) x)
    (M : ℝ) (hM : 0 ≤ M)
    (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ (A : Space → V)) x‖ ≤ M) (a : Space) :
    HasFDerivAt (translated A) (fieldDerivativeMap (translated DA a)) a := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun b => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun b : Space => M * ‖b-a‖)
  · intro b
    calc
      _ ≤ ‖b-a‖⁻¹ * (M * ‖b-a‖^2) := mul_le_mul_of_nonneg_left
        (translated_taylor_bound A DA hA hDA M hM h₂ a b) (inv_nonneg.mpr (norm_nonneg _))
      _ = M * ‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => M * ‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a

end BoundedFields

/-- Multiplication by an actual translated coefficient intertwines the ordinary L² translations. -/
theorem multiplier_translation (A : Field) (a : Space) (u : L2) :
    translation a (multiplier A u) = multiplier (translated A a) (translation a u) := by
  apply Lp.ext
  filter_upwards [translation_ae a (multiplier A u),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
      (multiplier_ae A u), multiplier_ae (translated A a) (translation a u),
    translation_ae a u] with x hl hm hr hu
  rw [hl, hm, hr, hu, translated_apply]

end EulerMeanCoefficients
