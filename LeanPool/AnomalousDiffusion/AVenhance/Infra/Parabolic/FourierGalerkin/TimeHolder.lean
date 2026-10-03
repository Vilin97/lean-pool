/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The time Cauchy estimate

An `L²`-in-time energy bound gives the square-root modulus needed by weak path compactness. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance two_ne_top_timeHolder : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- On a subinterval, the integral of a nonnegative function is bounded by the square root of
the interval length times its global `L²` energy. -/
theorem intervalIntegral_nonneg_le_sqrt_energy {g : ℝ → ℝ} {s t E : ℝ}
    (hst : s ≤ t) (hs : 0 ≤ s) (ht : t ≤ 1)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hgnonneg : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) 1)), 0 ≤ g r)
    (hE : (∫ r in (0 : ℝ)..1, g r ^ 2) ≤ E) :
    ∫ r in s..t, g r ≤ Real.sqrt (t - s) * Real.sqrt E := by
  let μ₀ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let μst : Measure ℝ := volume.restrict (Ioc s t)
  have hsubset : Ioc s t ⊆ Ioc (0 : ℝ) 1 := Ioc_subset_Ioc hs ht
  have hμle : μst ≤ μ₀ := Measure.restrict_mono_set volume hsubset
  have hgst : MemLp g 2 μst := hg.mono_measure hμle
  have hgnonnegst : ∀ᵐ r ∂μst, 0 ≤ g r := hgnonneg.filter_mono (ae_mono hμle)
  have hglobalSq : Integrable (fun r => g r ^ 2) μ₀ :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  have hglobalNonneg : ∀ᵐ r ∂μ₀, 0 ≤ g r ^ 2 :=
    Filter.Eventually.of_forall fun r => sq_nonneg (g r)
  have hIcc : (∫ r, g r ^ 2 ∂μ₀) = ∫ r in (0 : ℝ)..1, g r ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
  have hsegSq : ∫ r, g r ^ 2 ∂μst ≤ E := by
    calc
      ∫ r, g r ^ 2 ∂μst ≤ ∫ r, g r ^ 2 ∂μ₀ :=
        integral_mono_measure hμle hglobalNonneg hglobalSq
      _ = ∫ r in (0 : ℝ)..1, g r ^ 2 := hIcc
      _ ≤ E := hE
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μst := by
    exact memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hgst) (by simpa using hconst)
  have hholder' :
      (∫ r, g r ∂μst) ≤
        (∫ r, g r ^ 2 ∂μst) ^ ((1 : ℝ) / 2) *
          (∫ r, (1 : ℝ) ^ (2 : ℝ) ∂μst) ^ ((1 : ℝ) / 2) := by
    have hleft : (∫ r, ‖g r‖ * ‖(1 : ℝ)‖ ∂μst) = ∫ r, g r ∂μst := by
      apply integral_congr_ae
      filter_upwards [hgnonnegst] with r hr
      simp [abs_of_nonneg hr]
    have hright : (∫ r, ‖g r‖ ^ (2 : ℝ) ∂μst) ^ ((1 : ℝ) / 2) =
        (∫ r, g r ^ 2 ∂μst) ^ ((1 : ℝ) / 2) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with r
      simp [Real.norm_eq_abs, sq_abs]
    rw [hleft, hright] at hholder
    simpa only [Real.norm_eq_abs, abs_one] using hholder
  have hμlength : μst.real univ = t - s := by
    calc
      μst.real univ = volume.real (Ioc s t) := by
        simp [μst]
      _ = t - s := by
        simp [measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
  have hconstIntegral : (∫ r, (1 : ℝ) ^ (2 : ℝ) ∂μst) = t - s := by
    calc
      _ = ∫ r, (1 : ℝ) ∂μst := by
        apply integral_congr_ae
        filter_upwards with r
        norm_num
      _ = μst.real univ := by simp
      _ = t - s := hμlength
  have hsqrtEnergy : Real.sqrt (∫ r, g r ^ 2 ∂μst) ≤ Real.sqrt E :=
    Real.sqrt_le_sqrt hsegSq
  have hsqrtLen : 0 ≤ Real.sqrt (t - s) := Real.sqrt_nonneg _
  have hholderSqrt :
      (∫ r, g r ∂μst) ≤
        Real.sqrt (t - s) * Real.sqrt (∫ r, g r ^ 2 ∂μst) := by
    simpa only [← Real.sqrt_eq_rpow, hconstIntegral, mul_comm] using hholder'
  have hinterval : (∫ r in s..t, g r) = ∫ r, g r ∂μst := by
    rw [intervalIntegral.integral_of_le hst]
  rw [hinterval]
  calc
    ∫ r, g r ∂μst ≤ Real.sqrt (t - s) * Real.sqrt (∫ r, g r ^ 2 ∂μst) := hholderSqrt
    _ ≤ Real.sqrt (t - s) * Real.sqrt E :=
      mul_le_mul_of_nonneg_left hsqrtEnergy hsqrtLen

end AVenhance.Infra.Parabolic.FourierGalerkin

end
