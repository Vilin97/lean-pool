/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseDilation

/-!
# Common maximal terms under positive dilation

The ordinary Hilbert maximal truncation is exactly invariant under positive
dilation. We also record the positive change of variables for nonnegative
Lebesgue integrals. No maximal-function dilation estimate is assumed here.
-/

open MeasureTheory Set Metric
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace CommonMaximalDilation


noncomputable section

theorem quadraticHilbertTrunc_zero_dilate (a : ℝ) (ha : 0 < a)
    (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertTrunc 0 ε (fun u ↦ f (u / a)) (a * x) =
      quadraticHilbertTrunc 0 (ε / a) f x := by
  simpa only [zero_mul, mul_div_cancel₀ _ ha.ne'] using
    (quadraticHilbertTrunc_scale 0 ha (ε / a) f x).symm

theorem quadraticHilbertMaximalTruncation_zero_dilate_le (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 (fun u ↦ f (u / a)) (a * x) ≤
      quadraticHilbertMaximalTruncation 0 f x := by
  apply iSup_le
  intro ε
  rw [quadraticHilbertTrunc_zero_dilate a ha]
  exact le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
    ‖quadraticHilbertTrunc 0 δ f x‖ₑ) ⟨ε / a, div_pos ε.property ha⟩

theorem quadraticHilbertMaximalTruncation_zero_dilate (a : ℝ) (ha : 0 < a)
    (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 (fun u ↦ f (u / a)) (a * x) =
      quadraticHilbertMaximalTruncation 0 f x := by
  apply le_antisymm (quadraticHilbertMaximalTruncation_zero_dilate_le a ha f x)
  have h := quadraticHilbertMaximalTruncation_zero_dilate_le a⁻¹
    (inv_pos.mpr ha) (fun u ↦ f (u / a)) (a * x)
  simpa only [inv_mul_cancel_left₀ ha.ne', div_inv_eq_mul,
    mul_div_cancel_right₀ _ ha.ne'] using h

theorem lintegral_comp_div (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ≥0∞) :
    (∫⁻ u, F (u / a)) = ENNReal.ofReal a * ∫⁻ y, F y := by
  have h := lintegral_map_equiv (μ := (volume : Measure ℝ)) F
    (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha.ne')).toMeasurableEquiv
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀,
    Real.map_volume_mul_left (inv_ne_zero ha.ne'), inv_inv,
    abs_of_pos ha, lintegral_smul_measure] at h
  simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using h.symm


end
end CommonMaximalDilation
end QuadraticCarleson
