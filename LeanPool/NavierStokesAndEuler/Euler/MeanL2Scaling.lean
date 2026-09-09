/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanMollifierLimit
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicScaling
import LeanPool.NavierStokesAndEuler.Euler.MeanScalarSobolev

/-! Actual dilation identities for L² fields and weak harmonic scalar functions. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit
open scoped ContDiff

theorem memLp_dilation {V : Type*} [NormedAddCommGroup V]
    (f : Space → V) (hf : MemLp f 2 volume) (a : ℝ) (ha : a ≠ 0) :
    MemLp (fun x => f (a • x)) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => f (a • x)) volume :=
    hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume ha)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  exact ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).comp_smul ha

theorem lpNorm_dilation_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    (f : Space → V) (hf : MemLp f 2 volume) (a : ℝ) (ha : 0 < a) :
    lpNorm (fun x => f (a • x)) 2 volume ^ 2 = (a^3)⁻¹ * lpNorm f 2 volume ^ 2 := by
  rw [lpNorm_sq_eq_integral_norm_sq _ (memLp_dilation f hf a ha.ne'),
    lpNorm_sq_eq_integral_norm_sq f hf]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => ‖f x‖^2) a (hR := ha.le)]
  simp [Space, smul_eq_mul]

/-- The distributional harmonic test identity is preserved by spatial dilation. -/
theorem scalarWeakHarmonicOn_dilation (f : Space → ℝ) (R : ℝ) (hR : 0 < R)
    (hf : ScalarWeakHarmonicOn (Metric.ball (0 : Space) R) f) :
    ScalarWeakHarmonicOn (Metric.ball (0 : Space) 1) (fun x => f (R • x)) := by
  intro φ hc hs ht
  let ψ : Space → ℝ := fun y => φ (R⁻¹ • y)
  have hcψ : HasCompactSupport ψ := hc.comp_smul (inv_ne_zero hR.ne')
  have hsψ : ContDiff ℝ ∞ ψ := hs.comp (contDiff_id.const_smul R⁻¹)
  have htψ : tsupport ψ ⊆ Metric.ball (0 : Space) R := by
    intro x hx
    have hx' : R⁻¹ • x ∈ tsupport φ :=
      tsupport_comp_subset_preimage φ (continuous_const_smul R⁻¹) hx
    have hn : ‖R⁻¹ • x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using ht hx'
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hn
    simp only [Metric.mem_ball, dist_zero_right]
    calc
      ‖x‖ = R * (R⁻¹ * ‖x‖) := by field_simp
      _ < R * 1 := mul_lt_mul_of_pos_left hn hR
      _ = R := mul_one _
  have H := hf ψ hcψ hsψ htψ
  have hΔ (x : Space) : Δ ψ x = R⁻¹ ^ 2 * Δ φ (R⁻¹ • x) :=
    laplacian_comp_const_smul φ hs R⁻¹ x
  simp_rw [hΔ] at H
  have H' : (R⁻¹)^2 * (∫ x, f x * Δ φ (R⁻¹ • x)) = 0 := by
    rw [← integral_const_mul]
    convert H using 1
    congr 1
    funext x
    ring
  have hz : (∫ x, f x * Δ φ (R⁻¹ • x)) = 0 :=
    (mul_eq_zero.mp H').resolve_left (pow_ne_zero 2 (inv_ne_zero hR.ne'))
  have hi := Measure.integral_comp_smul volume
    (fun x => f x * Δ φ (R⁻¹ • x)) R
  have heval (x : Space) : R⁻¹ • (R • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  simp_rw [heval] at hi
  rw [hz, smul_zero] at hi
  exact hi

end EulerMeanHarmonic
