/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.PotentialMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # Adams estimates for almost-everywhere measurable sources

A measurable representative preserves the source Morrey norm and the Riesz
potential at every evaluation point. Thus the scalar Adams estimate does not
require pointwise measurability of the original source.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- The quantitative Adams estimate is invariant under almost-everywhere
changes of the source. -/
theorem riesz_adams_of_aemeasurable
    {P τ β : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) (hβ : 0 < β)
    (hβτ : β * τ < 5) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) :
    morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
      (fun z => (parabolicRieszPotential β f z).toReal) ≤
        parabolicAdamsPotentialConstant β P τ * morreyNorm P τ f := by
  have h := parabolicRieszPotential_adams hP hPτ hβ hβτ hf.measurable_mk
  have heq : parabolicRieszPotential β f = parabolicRieszPotential β (hf.mk f) := by
    funext z
    exact riesz_potential_congr_ae hf.ae_eq_mk z
  rw [← heq, ← morrey_norm_congr_ae hf.ae_eq_mk] at h
  exact h

private theorem lower_three_finite {s : ℝ} {f : ParabolicPoint → ℝ}
    (hs : 3 ≤ s) (hs25 : s ≤ 25) (hf : AEMeasurable f volume)
    (hN : morreyNorm s 25 f < ∞) : morreyNorm 3 25 f < ∞ := by
  have hlow := morreyNorm_lower_integrability (p' := 3) (p := s) (q := 25)
    (by norm_num) hs hs25 hf
  have hpow : 0 ≤ 1 / (3 : ℝ) - 1 / s := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hs
    exact sub_nonneg.mpr h
  exact hlow.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hpow Integration.volume_parabolicCylinder_lt_top.ne) hN)

/-- The order-two estimate at the first bootstrap exponents, lowered to
integrability exponent three. All numerical constants are discharged. -/
theorem order_two_adams_lower_three_of_aemeasurable
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hN : morreyNorm (6 / 5) (25 / 11) f < ∞) :
    morreyNorm 3 25 (fun z => (parabolicRieszPotential 2 f z).toReal) < ∞ := by
  have hbound := riesz_adams_of_aemeasurable
    (P := 6 / 5) (τ := 25 / 11) (β := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf
  have hC := adams_potential_constant_lt_top
    (P := 6 / 5) (τ := 25 / 11) (β := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfinite : morreyNorm (66 / 5) 25
      (fun z => (parabolicRieszPotential 2 f z).toReal) < ∞ := by
    convert hbound.trans_lt (ENNReal.mul_lt_top hC hN) using 1
    norm_num
  exact lower_three_finite (by norm_num) (by norm_num)
    (measurable_riesz_potential_of_aemeasurable 2 hf).ennreal_toReal.aemeasurable hfinite

/-- The order-one estimate at the first bootstrap exponents, lowered to
integrability exponent three. -/
theorem order_one_adams_lower_three_of_aemeasurable
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hN : morreyNorm 3 (25 / 6) f < ∞) :
    morreyNorm 3 25 (fun z => (parabolicRieszPotential 1 f z).toReal) < ∞ := by
  have hbound := riesz_adams_of_aemeasurable
    (P := 3) (τ := 25 / 6) (β := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf
  have hC := adams_potential_constant_lt_top
    (P := 3) (τ := 25 / 6) (β := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfinite : morreyNorm 18 25
      (fun z => (parabolicRieszPotential 1 f z).toReal) < ∞ := by
    convert hbound.trans_lt (ENNReal.mul_lt_top hC hN) using 1
    norm_num
  exact lower_three_finite (by norm_num) (by norm_num)
    (measurable_riesz_potential_of_aemeasurable 1 hf).ennreal_toReal.aemeasurable hfinite

end CKN.Core.Endgame
