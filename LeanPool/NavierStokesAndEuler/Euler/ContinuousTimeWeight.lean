/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
import Mathlib.Tactic.Positivity.Finset

/-!
# Actual profile normalization of continuous time paths

A positive scalar time profile gives inverse bounded linear scaling maps.
The norm of a normalized path is bounded directly by its profile estimate;
no quotient of the maximum and minimum profile enters that estimate.
-/

@[expose] public section


noncomputable section


namespace EulerContinuousTimeWeight

open Set ContinuousLinearMap EulerContinuousTimeIntegral

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplication by the literal scalar profile. -/
def weight (g : C(K, ℝ)) : C(K,E) →L[ℝ] C(K,E) :=
  multiplier ⟨fun t => g t • ContinuousLinearMap.id ℝ E,
    g.continuous.smul continuous_const⟩

@[simp] theorem weight_apply (g : C(K, ℝ)) (f : C(K, E)) (t : K) :
    weight g f t = g t • f t := rfl

/-- The reciprocal of a positive continuous profile is an actual continuous path. -/
def reciprocal (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) : C(K,ℝ) :=
  ⟨fun t => (g t)⁻¹, g.continuous.inv₀ (fun t => (hg t).ne')⟩

/-- Profile division as a genuine bounded linear map. -/
def normalize (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) : C(K,E) →L[ℝ] C(K,E) :=
  weight (reciprocal g hg)

@[simp] theorem normalize_apply (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (f : C(K, E)) (t : K) :
    normalize g hg f t = (g t)⁻¹ • f t := rfl

/-- Weighting and normalization are actual inverse operators. -/
theorem normalize_weight (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (f : C(K, E)) :
    normalize g hg (weight g f) = f := by
  ext t
  simp only [normalize_apply, weight_apply, smul_smul, inv_mul_cancel₀ (hg t).ne', one_smul]

/-- Normalization and weighting are inverse in the other order too. -/
theorem weight_normalize (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) (f : C(K, E)) :
    weight g (normalize g hg f) = f := by
  ext t
  simp only [normalize_apply, weight_apply, smul_smul, mul_inv_cancel₀ (hg t).ne', one_smul]

/-- Literal pointwise control of a weighted path, with no profile extremum. -/
theorem weight_pointwise_bound (g : C(K, ℝ)) (hg : ∀ t, 0 ≤ g t) (f : C(K, E)) (t : K) :
    ‖weight g f t‖ ≤ g t * ‖f‖ := by
  rw [weight_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hg t)]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm t) (hg t)

/-- A pointwise profile bound gives the normalized uniform norm directly. -/
theorem normalize_norm_le (g : C(K, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(K, E)) (D : ℝ) (hD : 0 ≤ D) (hf : ∀ t, ‖f t‖ ≤ D * g t) :
    ‖normalize g hg f‖ ≤ D := by
  apply (ContinuousMap.norm_le _ hD).2
  intro t
  rw [normalize_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hg t))]
  calc
    _ ≤ (g t)⁻¹ * (D*g t) := mul_le_mul_of_nonneg_left (hf t) (inv_nonneg.mpr (hg t).le)
    _ = D := by field_simp [(hg t).ne']

/-- Scalar normalization commutes with every coefficient multiplier. -/
theorem normalize_multiplier (g : C(K, ℝ)) (hg : ∀ t, 0 < g t)
    (A : C(K, E →L[ℝ] E)) (f : C(K, E)) :
    normalize g hg (multiplier A f) = multiplier A (normalize g hg f) := by
  ext t
  simp only [normalize_apply, multiplier_apply, map_smul]

/-- Scalar weighting commutes with every coefficient multiplier. -/
theorem weight_multiplier (g : C(K, ℝ)) (A : C(K, E →L[ℝ] E)) (f : C(K, E)) :
    weight g (multiplier A f) = multiplier A (weight g f) := by
  ext t
  simp only [weight_apply, multiplier_apply, map_smul]

end EulerContinuousTimeWeight
