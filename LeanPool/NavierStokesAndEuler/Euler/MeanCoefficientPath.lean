/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedCoefficientSmooth
import Mathlib.Algebra.Order.Star.Real

/-! Spatial translation calculus for coefficients uniformly on a compact time interval. -/

@[expose] public section


noncomputable section

namespace EulerMeanCoefficients

open MeasureTheory InnerProductSpace EulerSmoothLimit Set Filter
open scoped ContDiff BoundedContinuousFunction Topology

section Paths

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (Space →ᵇ V)` instance to shorten typeclass
synthesis. -/
local instance instMeanCoefficientPath1 : NormedAddCommGroup (Space →ᵇ V) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ V)` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientPath2 : NormedSpace ℝ (Space →ᵇ V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V))` instance to shorten
typeclass synthesis. -/
local instance instMeanCoefficientPath3 : NormedAddCommGroup (Space →ᵇ (Space →L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instMeanCoefficientPath4 : NormedSpace ℝ (Space →ᵇ (Space →L[ℝ] V)) := inferInstance

/-- Translate coefficient path as an element of `C(K, Space →ᵇ V)`. -/
def translateCoefficientPath (A : C(K, Space →ᵇ V)) (a : Space) : C(K, Space →ᵇ V) :=
  (BoundedContinuousFunction.compContinuousCLM V ℝ
    ⟨fun x : Space => x+a, continuous_id.add continuous_const⟩).compLeftContinuous ℝ K A

omit [CompactSpace K] in
@[simp] theorem translateCoefficientPath_apply (A : C(K, Space →ᵇ V)) (a : Space) (t : K) :
    translateCoefficientPath A a t = translated (A t) a := rfl

/-- Path direction, given by `⟨fun t => fieldDerivativeMap (DA t) a, ((derivativeBundling (V :=
V)).continuous.comp DA.continuous).clm_apply continuous_const⟩`. -/
def pathDirection (DA : C(K, Space →ᵇ (Space →L[ℝ] V))) (a : Space) : C(K, Space →ᵇ V) :=
  ⟨fun t => fieldDerivativeMap (DA t) a,
    ((derivativeBundling (V := V)).continuous.comp DA.continuous).clm_apply continuous_const⟩

omit [CompactSpace K] in
@[simp] theorem pathDirection_apply (DA : C(K, Space →ᵇ (Space →L[ℝ] V)))
    (a : Space) (t : K) (x : Space) : pathDirection DA a t x = DA t x a := rfl

theorem pathDirection_norm_le (DA : C(K, Space →ᵇ (Space →L[ℝ] V))) (a : Space) :
    ‖pathDirection DA a‖ ≤ ‖DA‖ * ‖a‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro t
  exact (fieldDirection_norm_le (DA t) a).trans
    (mul_le_mul_of_nonneg_right (DA.norm_coe_le_norm t) (norm_nonneg a))

/-- Path derivative linear, bundling `toFun`, `map_add`, `map_smul`. -/
def pathDerivativeLinear (DA : C(K, Space →ᵇ (Space →L[ℝ] V))) :
    Space →ₗ[ℝ] C(K, Space →ᵇ V) where
  toFun := pathDirection DA
  map_add' a b := by ext t x; exact (DA t x).map_add a b
  map_smul' c a := by ext t x; exact (DA t x).map_smul c a

/-- Path derivative map, bundling `toLinearMap`, `cont`. -/
def pathDerivativeMap (DA : C(K, Space →ᵇ (Space →L[ℝ] V))) :
    Space →L[ℝ] C(K, Space →ᵇ V) where
  toLinearMap := pathDerivativeLinear DA
  cont := AddMonoidHomClass.continuous_of_bound (pathDerivativeLinear DA) ‖DA‖
    (pathDirection_norm_le DA)

@[simp] theorem pathDerivativeMap_apply (DA : C(K, Space →ᵇ (Space →L[ℝ] V)))
    (a : Space) (t : K) (x : Space) : pathDerivativeMap DA a t x = DA t x a := rfl

theorem pathDerivativeMap_norm_le (DA : C(K, Space →ᵇ (Space →L[ℝ] V))) :
    ‖pathDerivativeMap DA‖ ≤ ‖DA‖ :=
  (pathDerivativeMap DA).opNorm_le_bound (norm_nonneg DA) (pathDirection_norm_le DA)

/-- Path derivative bundling linear, bundling `toFun`, `map_add`, `map_smul`. -/
def pathDerivativeBundlingLinear : C(K, Space →ᵇ (Space →L[ℝ] V)) →ₗ[ℝ]
    (Space →L[ℝ] C(K, Space →ᵇ V)) where
  toFun := pathDerivativeMap
  map_add' A B := by ext v t x; rfl
  map_smul' c A := by ext v t x; rfl

/-- Path derivative bundling, bundling `toLinearMap`, `cont`. -/
def pathDerivativeBundling : C(K, Space →ᵇ (Space →L[ℝ] V)) →L[ℝ]
    (Space →L[ℝ] C(K, Space →ᵇ V)) where
  toLinearMap := pathDerivativeBundlingLinear
  cont := AddMonoidHomClass.continuous_of_bound (pathDerivativeBundlingLinear (K := K) (V := V)) 1
    (fun (A : C(K, Space →ᵇ (Space →L[ℝ] V))) => by
    change ‖pathDerivativeMap A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using pathDerivativeMap_norm_le A)

theorem translateCoefficientPath_taylor (A : C(K, Space →ᵇ V))
    (DA : C(K, Space →ᵇ (Space →L[ℝ] V)))
    (hA : ∀ t, ContDiff ℝ ∞ (A t : Space → V))
    (hDA : ∀ t x, DA t x = fderiv ℝ (A t : Space → V) x)
    (M : ℝ) (hM : 0 ≤ M)
    (h₂ : ∀ t x, ‖fderiv ℝ (fderiv ℝ (A t : Space → V)) x‖ ≤ M) (a b : Space) :
    ‖translateCoefficientPath A b - translateCoefficientPath A a -
      pathDerivativeMap (translateCoefficientPath DA a) (b-a)‖ ≤ M * ‖b-a‖^2 := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hM (sq_nonneg _))).2
  intro t
  exact translated_taylor_bound (A t) (DA t) (hA t) (hDA t) M hM (h₂ t) a b

/-- Actual spatial differentiation holds in the uniform time-path norm. -/
theorem translateCoefficientPath_hasFDerivAt (A : C(K, Space →ᵇ V))
    (DA : C(K, Space →ᵇ (Space →L[ℝ] V)))
    (hA : ∀ t, ContDiff ℝ ∞ (A t : Space → V))
    (hDA : ∀ t x, DA t x = fderiv ℝ (A t : Space → V) x)
    (M : ℝ) (hM : 0 ≤ M)
    (h₂ : ∀ t x, ‖fderiv ℝ (fderiv ℝ (A t : Space → V)) x‖ ≤ M) (a : Space) :
    HasFDerivAt (translateCoefficientPath A)
      (pathDerivativeMap (translateCoefficientPath DA a)) a := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply squeeze_zero (fun b => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun b : Space => M * ‖b-a‖)
  · intro b
    calc
      _ ≤ ‖b-a‖⁻¹ * (M * ‖b-a‖^2) := mul_le_mul_of_nonneg_left
        (translateCoefficientPath_taylor A DA hA hDA M hM h₂ a b)
          (inv_nonneg.mpr (norm_nonneg _))
      _ = M * ‖b-a‖ := by
        by_cases h : ‖b-a‖ = 0
        · simp only [h, inv_zero, zero_mul, mul_zero]
        · field_simp
  · have hc : Continuous (fun b : Space => M * ‖b-a‖) := by fun_prop
    simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto a

end Paths

/-- Cache the standard `NormedAddCommGroup Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientPath5 : NormedAddCommGroup Field := inferInstance
/-- Cache the standard `NormedSpace ℝ Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientPath6 : NormedSpace ℝ Field := inferInstance

/-- Translated path: an abbreviation for `translateCoefficientPath A a`. -/
abbrev translatedPath (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) (a : Space) :
    C(Icc (0 : ℝ) T, Field) := translateCoefficientPath A a

@[simp] theorem translatedPath_apply (T : ℝ) (A : C(Icc (0 : ℝ) T, Field))
    (a : Space) (t : Icc (0 : ℝ) T) (x : Space) : translatedPath T A a t x = A t (x+a) := rfl

end EulerMeanCoefficients
