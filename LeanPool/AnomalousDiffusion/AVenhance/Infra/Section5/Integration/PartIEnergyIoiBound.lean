/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIEnergyIoiCutoff

/-! # The integrated energy inequality on a positive-time interval `[s,t]`

For `0 < s ≤ t ≤ 1`:
`∫ w(t)² + κ ∫_s^t ∫ |∇w|² ≤ ∫ w(s)² + κ⁻¹ ‖f‖²_{L²(0,1;HDot⁻¹)}`, for `w = u - v` with `v` only
jointly `C²` on `(0,∞) × ℝ²`.  Reduces to the `Energy` development through the cutoff
`cutoffV s v`. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.Integration.EnergyIoi

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration.Energy

/-- Integrated differential inequality on a compact subinterval of `(0,∞)`; the inequality is only
needed almost everywhere on the open interval. -/
theorem sub_le_integral_of_deriv_le_Ioo {E D h : ℝ → ℝ} {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t)
    (hEd : ∀ x, 0 < x → HasDerivAt E (D x) x)
    (hDc : ContinuousOn D (Ioi 0))
    (hh : IntervalIntegrable h volume s t)
    (hineq : ∀ᵐ x ∂volume.restrict (Ioo s t), D x ≤ h x) :
    E t - E s ≤ ∫ x in s..t, h x := by
  have hsub : uIcc s t ⊆ Ioi 0 := by
    rw [uIcc_of_le hst]
    intro x hx
    exact lt_of_lt_of_le hs hx.1
  have hDint : IntervalIntegrable D volume s t :=
    (hDc.mono hsub).intervalIntegrable
  have hftc : ∫ x in s..t, D x = E t - E s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hEd x (hsub hx)) hDint
  have hae : ∀ᵐ x ∂volume.restrict (Icc s t), D x ≤ h x := by
    rwa [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  rw [← hftc]
  exact intervalIntegral.integral_mono_ae_restrict hst hDint hh hae

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}

/-- The integrated forced energy inequality on `[s,t] ⊆ (0,1]`. -/
theorem IoiSetup.interval_bound (S : IoiSetup φ κ θ₀ u v)
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∫ x in unitCell 2, (u t x - v t x) ^ 2) + κ * ∫ r in s..t, errGrad u v r ≤
      (∫ x in unitCell 2, (u s x - v s x) ^ 2) +
        (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal ^ 2 / κ := by
  have S' := S.cutoff hs
  set f : ℝ → Vec 2 → ℝ := fun s x => advDiffOp (streamVel φ) κ v s x with hf
  have hfc : ContinuousOn (fun p : ℝ × Vec 2 => f p.1 p.2) (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) :=
    S.forcing_continuousOn.mono (Set.prod_mono Set.Ioo_subset_Ioi_self le_rfl)
  have hm := aemeasurable_hMinusOneNorm_of_continuousOn hfc
  have hgint := integrable_toReal_sq hm hfin
  have hae := ae_hMinusOneNorm_ne_top hm hfin
  have hF2 := integral_toReal_sq_eq hm hfin
  set g : ℝ → ℝ := fun r => (hMinusOneNorm (f r)).toReal ^ 2 with hg
  have hG : ContinuousOn (errGrad u v) (Icc s t) := by
    refine (S'.errGrad_continuousOn.mono (Icc_subset_Icc hs.le ht)).congr ?_
    intro r hr
    exact (errGrad_cutoffV u hs v (by linarith [hr.1])).symm
  set h : ℝ → ℝ := fun r => g r / κ - κ * errGrad u v r with hh
  have hgI : IntervalIntegrable g volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hgint).mono_set
      (Set.Ioc_subset_Ioc hs.le ht)
  have hGI : IntervalIntegrable (errGrad u v) volume s t := hG.intervalIntegrable_of_Icc hst
  have hhint : IntervalIntegrable h volume s t := (hgI.div_const κ).sub (hGI.const_mul κ)
  have hae' : ∀ᵐ r ∂(volume.restrict (Set.Ioo s t)), hMinusOneNorm (f r) ≠ ⊤ :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hs.le ht) hae
  have hineq : ∀ᵐ r ∂(volume.restrict (Set.Ioo s t)),
      (∫ x in unitCell 2, 2 * (u r x - cutoffV s v r x) *
        deriv (fun q => u q x - cutoffV s v q x) r) ≤ h r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hae'] with r hr hrfin
    have hr0 : 0 < r := lt_trans hs hr.1
    have hrs : s / 2 < r := by linarith [hr.1]
    have hfin' : hMinusOneNorm (advDiffOp (streamVel φ) κ (cutoffV s v) r) ≠ ⊤ := by
      rw [advDiffOp_cutoffV_slice _ _ hs v hrs]
      exact hrfin
    have key := S'.energy_inequality hr0 hfin'
    rw [← S'.errGrad_eq hr0.le, errGrad_cutoffV u hs v hrs.le,
      advDiffOp_cutoffV_slice _ _ hs v hrs] at key
    simp only [hh, hg]
    have hκ := S.hκ
    rw [le_sub_iff_add_le]
    exact key
  have hEd : ∀ r, 0 < r → HasDerivAt (fun q => ∫ x in unitCell 2, (u q x - cutoffV s v q x) ^ 2)
      (∫ x in unitCell 2, 2 * (u r x - cutoffV s v r x) *
        deriv (fun q => u q x - cutoffV s v q x) r) r :=
    fun r hr => energy_hasDerivAt_one (g := fun q x => u q x - cutoffV s v q x) S'.hw1 hr
  have hmain := sub_le_integral_of_deriv_le_Ioo hs hst hEd S'.energyRate_continuousOn hhint hineq
  have hE : ∀ r, s / 2 ≤ r → (∫ x in unitCell 2, (u r x - cutoffV s v r x) ^ 2) =
      ∫ x in unitCell 2, (u r x - v r x) ^ 2 := fun r hr => by
    rw [cutoffV_slice_eq hs v hr]
  rw [hE t (by linarith), hE s (by linarith)] at hmain
  have hsplit : ∫ r in s..t, h r =
      (∫ r in s..t, g r) / κ - κ * ∫ r in s..t, errGrad u v r := by
    simp only [hh]
    rw [intervalIntegral.integral_sub (hgI.div_const κ) (hGI.const_mul κ),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  have hgmono : ∫ r in s..t, g r ≤ ∫ r in (0 : ℝ)..1, g r := by
    have h1I : IntervalIntegrable g volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).2 hgint
    exact intervalIntegral.integral_mono_interval hs.le hst ht
      (Filter.Eventually.of_forall fun r => sq_nonneg _) h1I
  have hg1 : ∫ r in (0 : ℝ)..1, g r = (timeHMinusOneNorm f).toReal ^ 2 := by
    rw [hF2, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hκ := S.hκ
  have hdiv : (∫ r in s..t, g r) / κ ≤ (timeHMinusOneNorm f).toReal ^ 2 / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le
    linarith
  rw [hsplit] at hmain
  linarith

end AVenhance.Infra.Section5.Integration.EnergyIoi

end
