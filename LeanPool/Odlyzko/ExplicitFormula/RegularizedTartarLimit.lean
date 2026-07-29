/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarTransform

/-!
# Regularized Tartar Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace NumberField.Odlyzko

theorem regularizedScaledTartar_integrable
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 ≤ δ) :
    Integrable (regularizedScaledTartar y δ) := by
  apply (scaledTartarTestFunction_integrable hy).mono'
  · exact (continuous_regularizedScaledTartar y δ).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (regularizedScaledTartar_nonneg y δ x)]
    exact regularizedScaledTartar_le_scaledTartar hδ

theorem poitouTransformIntegrand_regularizedScaledTartar_eq
    (y δ : ℝ) (s : ℂ) (x : ℝ) :
    poitouTransformIntegrand (regularizedScaledTartar y δ) s x =
      Real.exp (-δ * x ^ 2) *
        poitouTransformIntegrand (scaledTartarTestFunction y) s x := by
  rw [poitouTransformIntegrand, poitouTransformIntegrand,
    poitouKernel, poitouKernel, regularizedScaledTartar]
  push_cast
  ring

theorem norm_poitouTransformIntegrand_regularized_le_scaled
    {y δ : ℝ} (hδ : 0 ≤ δ) (s : ℂ) (x : ℝ) :
    ‖poitouTransformIntegrand (regularizedScaledTartar y δ) s x‖ ≤
      ‖poitouTransformIntegrand (scaledTartarTestFunction y) s x‖ := by
  rw [poitouTransformIntegrand_regularizedScaledTartar_eq,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-δ * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hδ (sq_nonneg x))
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)

theorem tendsto_poitouTransform_regularizedScaledTartar_nhdsGT_zero
    {y : ℝ} (hy : y ≠ 0) {s : ℂ} (hs : s.re ∈ Icc 0 1) :
    Tendsto
      (fun δ : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) s)
      (𝓝[>] 0)
      (𝓝 (poitouTransform (scaledTartarTestFunction y) s)) := by
  unfold poitouTransform
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : ℝ ↦ 2 * scaledTartarTestFunction y x)
  · filter_upwards [] with δ
    exact
      (continuous_poitouTransformIntegrand_regularizedScaledTartar
        y δ s).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [] with x
    exact (norm_poitouTransformIntegrand_regularized_le_scaled
      hδ.le s x).trans
        (norm_poitouTransformIntegrand_scaledTartar_le hs x)
  · exact (scaledTartarTestFunction_integrable hy).const_mul 2
  · filter_upwards [] with x
    simp_rw [poitouTransformIntegrand_regularizedScaledTartar_eq]
    have hexp :
        Tendsto (fun δ : ℝ ↦ (Real.exp (-δ * x ^ 2) : ℂ))
          (𝓝[>] 0) (𝓝 1) := by
      have harg :
          Tendsto (fun δ : ℝ ↦ -δ * x ^ 2)
            (𝓝[>] 0) (𝓝 0) := by
        have hid :
            Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left inf_le_left
        have hneg :
            Tendsto (fun δ : ℝ ↦ -δ) (𝓝[>] 0) (𝓝 0) := by
          simpa only [id_eq, neg_zero] using hid.neg
        simpa using hneg.mul_const (x ^ 2)
      simpa using
        (Real.continuous_exp.continuousAt.tendsto.comp harg).ofReal
    simpa only [one_mul] using
      hexp.mul tendsto_const_nhds

end NumberField.Odlyzko
