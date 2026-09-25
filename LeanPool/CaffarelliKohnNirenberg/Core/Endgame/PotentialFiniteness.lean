/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.AdamsConstants

/-! # Almost-everywhere finiteness of subcritical potentials

Bounded support turns a finite Morrey norm into a finite global power
integral. The maximal estimate and the unoptimized Hedberg estimate then
give finiteness of the extended-real potential almost everywhere, before
any use of its real-valued conversion.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Endgame

/-- A bounded-support Morrey source has finite global power integral. -/
theorem source_power_integral_lt_top
    {P τ R : ℝ} (hP : 0 < P) (hR : 0 < R)
    {z₀ : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hN : morreyNorm P τ f < ∞)
    (hsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, f z = 0) :
    (∫⁻ z, ENNReal.ofReal |f z| ^ P) < ∞ := by
  have heq : (fun z => ENNReal.ofReal |f z| ^ P) =
      (parabolicCylinder z₀.1 z₀.2 R).indicator
        (fun z => ENNReal.ofReal |f z| ^ P) := by
    funext z
    by_cases hz : z ∈ parabolicCylinder z₀.1 z₀.2 R
    · simp [hz]
    · simp [hz, hsupp z hz, ENNReal.zero_rpow_of_pos hP]
  have hset : MeasurableSet (parabolicCylinder z₀.1 z₀.2 R) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  rw [heq, lintegral_indicator hset]
  have hbound := cylinderPowerIntegral_le_morreyNorm_pow (q := τ) hP hf hR
    (z := z₀)
  apply hbound.trans_lt
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top))
    (ENNReal.rpow_lt_top_of_nonneg hP.le hN.ne)

/-- In the strict subcritical range, a bounded-support Morrey source has a
finite extended-real Riesz potential almost everywhere. -/
theorem riesz_potential_ae_lt_top_of_morrey
    {β P τ R : ℝ} (hβ : 0 < β) (hP : 1 < P)
    (hPτ : P ≤ τ) (hβτ : β * τ < 5) (hR : 0 < R)
    {z₀ : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hN : morreyNorm P τ f < ∞)
    (hsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, f z = 0) :
    ∀ᵐ z, parabolicRieszPotential β f z < ∞ := by
  have hP0 : 0 < P := by linarith only [hP]
  have hτ : 1 ≤ τ := hP.le.trans hPτ
  have hτ0 : 0 < τ := hP0.trans_le hPτ
  have hβ5 : β < 5 := by
    have hmul : β ≤ β * τ := by nlinarith only [hβ, hτ]
    exact hmul.trans_lt hβτ
  have hglobal := source_power_integral_lt_top hP0 hR hf.aemeasurable hN hsupp
  have hglobal' : (∫⁻ z, ENNReal.ofReal ‖f z‖ ^ P) < ∞ := by
    simpa only [Real.norm_eq_abs] using hglobal
  have hmax := lintegral_rpow_parabolicMaximalFunction_ofReal_le f hf hP hglobal'
  have hmaxfinite : (∫⁻ z, parabolicMaximalMajorant f z ^ P) < ∞ := by
    simpa only [parabolicMaximalMajorant, Real.norm_eq_abs] using
      hmax.trans_lt (ENNReal.mul_lt_top (maximal_strong_constant_lt_top hP) hglobal')
  have hmaxae : ∀ᵐ z, parabolicMaximalMajorant f z < ∞ := by
    have hmeas := (measurable_parabolicMaximalFunction
      (fun z => ENNReal.ofReal |f z|)).pow_const P
    filter_upwards [ae_lt_top hmeas hmaxfinite.ne] with z hz
    exact (ENNReal.rpow_lt_top_iff_of_pos hP0).mp hz
  have hlow := morreyNorm_lower_p (p' := 1) (p := P) (q := τ)
    (by norm_num) hP.le hPτ hf.aemeasurable
  have hN1 : morreyNorm 1 τ f < ∞ := by
    apply hlow.trans_lt
    apply ENNReal.mul_lt_top _ hN
    apply ENNReal.rpow_lt_top_of_nonneg _ Integration.volume_parabolicCylinder_lt_top.ne
    have hi : 1 / P ≤ (1 : ℝ) := (div_le_one hP0).mpr hP.le
    simpa only [one_div_one] using sub_nonneg.mpr hi
  filter_upwards [hmaxae] with z hz
  have hbound := parabolicRieszPotential_scale_le hβ hβ5 hτ hβτ
    (R := 1) one_pos hf.aemeasurable
    (isParabolicMaximalMajorant_parabolicMaximalMajorant f) z
  simp only [Real.one_rpow, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one] at hbound
  exact hbound.trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (hedberg_near_constant_lt_top hβ) hz,
      ENNReal.mul_lt_top (tail_kernel_constant_lt_top hτ0 hβτ) hN1⟩)

/-- Almost-everywhere changes of a scalar source preserve its Morrey norm. -/
theorem morrey_norm_congr_ae {P τ : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) : morreyNorm P τ f = morreyNorm P τ g := by
  unfold morreyNorm
  congr 1
  funext z
  congr 1
  funext r
  unfold morreyCell
  congr 2
  unfold cylinderPowerIntegral
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  rw [hw]

/-- Almost-everywhere changes of a source preserve the extended-real
potential at every evaluation point. -/
theorem riesz_potential_congr_ae {β : ℝ} {f g : ParabolicPoint → ℝ}
    (hfg : f =ᵐ[volume] g) (z : ParabolicPoint) :
    parabolicRieszPotential β f z = parabolicRieszPotential β g z := by
  unfold parabolicRieszPotential
  apply lintegral_congr_ae
  filter_upwards [hfg] with w hw
  rw [hw]

/-- The subcritical finiteness theorem needs only almost-everywhere
measurability; a measurable representative is truncated to the same support. -/
theorem riesz_potential_ae_lt_top_of_aemeasurable_morrey
    {β P τ R : ℝ} (hβ : 0 < β) (hP : 1 < P)
    (hPτ : P ≤ τ) (hβτ : β * τ < 5) (hR : 0 < R)
    {z₀ : ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hN : morreyNorm P τ f < ∞)
    (hsupp : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, f z = 0) :
    ∀ᵐ z, parabolicRieszPotential β f z < ∞ := by
  let S := parabolicCylinder z₀.1 z₀.2 R
  have hS : MeasurableSet S := (vec3Ball_measurable _ _).prod measurableSet_Ioc
  let g := S.indicator (hf.mk f)
  have hg : Measurable g := hf.measurable_mk.indicator hS
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hf.ae_eq_mk] with z hz
    by_cases hzs : z ∈ S
    · simpa only [g, indicator_of_mem hzs] using hz
    · simpa only [g, indicator_of_notMem hzs] using hsupp z hzs
  have hgN : morreyNorm P τ g < ∞ := by
    rw [← morrey_norm_congr_ae hfg]
    exact hN
  have hgs : ∀ z ∉ parabolicCylinder z₀.1 z₀.2 R, g z = 0 := by
    intro z hz
    exact indicator_of_notMem hz _
  filter_upwards [riesz_potential_ae_lt_top_of_morrey hβ hP hPτ hβτ hR hg hgN hgs]
    with z hz
  rwa [riesz_potential_congr_ae hfg z]

end CKN.Core.Endgame
