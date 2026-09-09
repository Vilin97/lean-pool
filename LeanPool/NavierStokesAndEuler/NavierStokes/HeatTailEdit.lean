/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialHeatProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The actual terminal heat edit and its integral debts

The switch uses logarithmic time: it starts at tail time `1/5` and is
complete at tail time `1/2`.  Quantitative estimates below are proved for
the actual improper integrals, then applied to the constructed outgoing
tail.  No debt bound is an input to the final outgoing-tail theorems.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.HeatTailEdit

noncomputable def exponent (h : ℝ) : ℝ := 1 / 2 + h

noncomputable def heatConstant (h ν : ℝ) : ℝ := 2 * ν * h * (1 + h)

noncomputable def switch (K X : ℝ) : ℝ :=
  OutgoingSchedule.sigma (Real.log (X / K) / (3 / 10))

noncomputable def multiplier (h ν K X : ℝ) : ℝ :=
  1 + switch K X * (RadialHeatProfile.profile (1 + h) (2 * ν / X) - 1)

noncomputable def edit (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ :=
  E X * multiplier h ν K X

noncomputable def change (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ :=
  edit E h ν K X - E X

noncomputable def squareChange (E : ℝ → ℝ) (h ν K X : ℝ) : ℝ :=
  edit E h ν K X ^ 2 - E X ^ 2

theorem switch_bounds (K X : ℝ) : 0 ≤ switch K X ∧ switch K X ≤ 1 :=
  ⟨OutgoingSchedule.sigma_nonneg _, OutgoingSchedule.sigma_le_one _⟩

theorem switch_zero {K X : ℝ} (hK : 0 < K) (hX : 0 < X) (hXK : X ≤ K) :
    switch K X = 0 := by
  apply OutgoingSchedule.sigma_zero
  exact div_nonpos_of_nonpos_of_nonneg
    (Real.log_nonpos (div_pos hX hK).le ((div_le_one hK).mpr hXK)) (by norm_num)

theorem switch_one {K X : ℝ} (h : 3 / 10 ≤ Real.log (X / K)) : switch K X = 1 := by
  apply OutgoingSchedule.sigma_one
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 3 / 10)).mpr (by simpa using h)

theorem edit_before (E : ℝ → ℝ) (h ν : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (hXK : X ≤ K) : edit E h ν K X = E X := by
  simp only [edit, multiplier, switch_zero hK hX hXK, zero_mul, add_zero, mul_one]

theorem edit_after (E : ℝ → ℝ) (h ν : ℝ) {K X : ℝ}
    (hfull : 3 / 10 ≤ Real.log (X / K)) :
    edit E h ν K X = E X * RadialHeatProfile.profile (1 + h) (2 * ν / X) := by
  simp only [edit, multiplier, switch_one hfull, one_mul, add_sub_cancel]

theorem multiplier_bounds {h ν K X : ℝ} (hh : 0 < h) (hν : 0 ≤ ν) (hX : 0 < X) :
    0 < multiplier h ν K X ∧ multiplier h ν K X ≤ 1 := by
  have hz : 0 ≤ 2 * ν / X := div_nonneg (mul_nonneg (by norm_num) hν) hX.le
  have hH := RadialHeatProfile.profile_pos (a := 1 + h) (by linarith) hz
  have hH1 := RadialHeatProfile.profile_le_one (a := 1 + h) (by linarith) hz
  have hs := switch_bounds K X
  have hp := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hH1)
  have hn := mul_nonpos_of_nonneg_of_nonpos hs.1 (sub_nonpos.mpr hH1)
  dsimp [multiplier]
  constructor <;> nlinarith

theorem edit_pos {E : ℝ → ℝ} {h ν K X : ℝ} (hh : 0 < h) (hν : 0 ≤ ν)
    (hX : 0 < X) (hE : 0 < E X) : 0 < edit E h ν K X :=
  mul_pos hE (multiplier_bounds hh hν hX).1

theorem switch_contDiffOn {K : ℝ} (hK : 0 < K) :
    ContDiffOn ℝ ∞ (switch K) (Ioi 0) := by
  intro X hX
  have hl : ContDiffAt ℝ ∞ (fun X : ℝ => Real.log (X / K)) X :=
    (Real.contDiffAt_log.mpr (div_pos hX hK).ne').comp X (contDiffAt_id.div_const K)
  exact (OutgoingSchedule.sigma_contDiff.contDiffAt.comp X
    (hl.div_const (3 / 10))).contDiffWithinAt

theorem multiplier_contDiffOn {h ν K : ℝ} (hh : 0 < h) (hν : 0 < ν) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (multiplier h ν K) (Ioi 0) := by
  apply contDiffOn_const.add
  apply (switch_contDiffOn hK).mul
  apply ContDiffOn.sub _ contDiffOn_const
  apply (RadialHeatProfile.profile_contDiffOn (a := 1 + h) (by linarith)).comp
    (contDiffOn_const.div contDiffOn_id (fun X hX => (show 0 < X from hX).ne'))
  intro X hX
  exact (div_pos (mul_pos (by norm_num) hν) hX).le

theorem edit_contDiffOn {E : ℝ → ℝ} {h ν K : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (hE : ContDiffOn ℝ ∞ E (Ioi 0)) :
    ContDiffOn ℝ ∞ (edit E h ν K) (Ioi 0) :=
  hE.mul (multiplier_contDiffOn hh hν hK)

theorem heatConstant_pos {h ν : ℝ} (hh : 0 < h) (hν : 0 < ν) :
    0 < heatConstant h ν := by unfold heatConstant; positivity

theorem multiplier_sub_one_bound {h ν K X : ℝ} (hh : 0 < h) (hν : 0 ≤ ν)
    (hX : 0 < X) : |multiplier h ν K X - 1| ≤ heatConstant h ν / X := by
  have hz : 0 ≤ 2 * ν / X := div_nonneg (mul_nonneg (by norm_num) hν) hX.le
  have hb := RadialHeatProfile.profile_h_sub_one_bound hh hz
  have hs := switch_bounds K X
  have he : multiplier h ν K X - 1 =
      switch K X * (RadialHeatProfile.profile (1 + h) (2 * ν / X) - 1) := by
    unfold multiplier
    ring
  rw [he, abs_mul, abs_of_nonneg hs.1]
  calc
    _ ≤ 1 * |RadialHeatProfile.profile (1 + h) (2 * ν / X) - 1| :=
      mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
    _ ≤ h * (1 + h) * (2 * ν / X) := by simpa only [one_mul] using hb
    _ = heatConstant h ν / X := by unfold heatConstant; ring

theorem change_bound {E : ℝ → ℝ} {h ν K X : ℝ} (hh : 0 < h) (hν : 0 ≤ ν)
    (hX : 0 < X) : |change E h ν K X| ≤ heatConstant h ν * |E X| / X := by
  have he : change E h ν K X = E X * (multiplier h ν K X - 1) := by
    unfold change edit
    ring
  rw [he, abs_mul]
  calc
    _ ≤ |E X| * (heatConstant h ν / X) :=
      mul_le_mul_of_nonneg_left (multiplier_sub_one_bound hh hν hX) (abs_nonneg _)
    _ = _ := by ring

theorem squareChange_bound {E : ℝ → ℝ} {h ν K X : ℝ} (hh : 0 < h) (hν : 0 ≤ ν)
    (hX : 0 < X) : |squareChange E h ν K X| ≤
      2 * heatConstant h ν * E X ^ 2 / X := by
  have hm := multiplier_bounds (K := K) hh hν hX
  have hs : multiplier h ν K X ^ 2 ≤ 1 := by nlinarith
  have he : squareChange E h ν K X = E X ^ 2 * (multiplier h ν K X ^ 2 - 1) := by
    unfold squareChange edit
    ring
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonpos (sub_nonpos.mpr hs)]
  have hb := multiplier_sub_one_bound (K := K) hh hν hX
  rw [abs_of_nonpos (sub_nonpos.mpr hm.2)] at hb
  have hsq : -(multiplier h ν K X ^ 2 - 1) ≤ 2 * (heatConstant h ν / X) := by
    nlinarith [sq_nonneg (multiplier h ν K X - 1)]
  calc
    _ ≤ E X ^ 2 * (2 * (heatConstant h ν / X)) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

/-! ## One exact weighted power integral -/

noncomputable def weightedKernel (K p q X : ℝ) : ℝ :=
  X ^ q * (X / K) ^ p / X

theorem weightedKernel_eq {K X : ℝ} (hK : 0 < K) (hX : 0 < X) (p q : ℝ) :
    weightedKernel K p q X = X ^ (p + q - 1) / K ^ p := by
  unfold weightedKernel
  rw [Real.div_rpow hX.le hK.le, Real.rpow_sub hX, Real.rpow_one,
    Real.rpow_add hX]
  ring

theorem weightedKernel_integrable {K p q : ℝ} (hK : 0 < K) (hpq : p + q < 0) :
    IntegrableOn (weightedKernel K p q) (Ioi K) := by
  apply ((integrableOn_Ioi_rpow_of_lt (a := p + q - 1) (by linarith) hK).div_const
    (K ^ p)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  exact (weightedKernel_eq hK (hK.trans hX) p q).symm

theorem integral_weightedKernel {K p q : ℝ} (hK : 0 < K) (hpq : p + q < 0) :
    (∫ X in Ioi K, weightedKernel K p q X) = K ^ q / (-p - q) := by
  calc
    _ = ∫ X in Ioi K, X ^ (p + q - 1) / K ^ p := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro X hX
      exact weightedKernel_eq hK (hK.trans hX) p q
    _ = (-K ^ (p + q) / (p + q)) / K ^ p := by
      rw [integral_div, integral_Ioi_rpow_of_lt (by linarith) hK]
      rw [show p + q - 1 + 1 = p + q by ring]
    _ = K ^ q / (-p - q) := by
      rw [Real.rpow_add hK]
      have hk : K ^ p ≠ 0 := (Real.rpow_pos_of_pos hK p).ne'
      have hd : p + q ≠ 0 := hpq.ne
      have hd' : -p - q ≠ 0 := by linarith
      field_simp [hk, hd, hd'] ; ring

theorem weighted_integral_bound {K p q B : ℝ} {g : ℝ → ℝ} (hK : 0 < K)
    (hpq : p + q < 0) (hg : ContinuousOn g (Ioi K))
    (hb : ∀ X ∈ Ioi K, |g X| ≤ B * (X / K) ^ p / X) :
    IntegrableOn (fun X => X ^ q * g X) (Ioi K) ∧
      |∫ X in Ioi K, X ^ q * g X| ≤ B * K ^ q / (-p - q) := by
  have hw := (weightedKernel_integrable hK hpq).const_mul B
  have hc : ContinuousOn (fun X => X ^ q * g X) (Ioi K) :=
    ((continuousOn_id.rpow_const (fun X hX => Or.inl (hK.trans hX).ne')).mul hg)
  have hbound : ∀ X ∈ Ioi K, ‖X ^ q * g X‖ ≤ B * weightedKernel K p q X := by
    intro X hX
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hK.trans hX) q)]
    have h := mul_le_mul_of_nonneg_left (hb X hX) (Real.rpow_nonneg (hK.trans hX).le q)
    convert! h using 1 ; unfold weightedKernel ; ring
  have hi : IntegrableOn (fun X => X ^ q * g X) (Ioi K) :=
    hw.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; exact hbound X hX)
  refine ⟨hi, ?_⟩
  have h := norm_integral_le_of_norm_le hw
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; exact hbound X hX)
  simpa only [Real.norm_eq_abs, integral_const_mul, integral_weightedKernel hK hpq,
    mul_div_assoc] using h

/-! ## Quantitative debts for a prescribed bounded terminal shape -/

noncomputable def powerTail (h e K : ℝ) (f : ℝ → ℝ) (X : ℝ) : ℝ :=
  e * (X / K) ^ (-exponent h) * f (Real.log (X / K))

theorem powerTail_contDiffOn {K : ℝ} (hK : 0 < K) (h e : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiffOn ℝ ∞ (powerTail h e K f) (Ioi 0) := by
  intro X hX
  have hp : ContDiffAt ℝ ∞ (fun X : ℝ => (X / K) ^ (-exponent h)) X :=
    (contDiffAt_id.div_const K).rpow_const_of_ne (div_pos hX hK).ne'
  have hl : ContDiffAt ℝ ∞ (fun X : ℝ => Real.log (X / K)) X :=
    (Real.contDiffAt_log.mpr (div_pos hX hK).ne').comp X (contDiffAt_id.div_const K)
  exact ((contDiffAt_const.mul hp).mul (hf.contDiffAt.comp X hl)).contDiffWithinAt

theorem powerTail_bound {K e M X : ℝ} (hK : 0 < K) (he : 0 ≤ e) (hX : K ≤ X)
    (h : ℝ) {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ t → |f t| ≤ M) :
    |powerTail h e K f X| ≤ e * M * (X / K) ^ (-exponent h) := by
  have hp := div_pos (hK.trans_le hX) hK
  have hlog : 0 ≤ Real.log (X / K) :=
    Real.log_nonneg ((one_le_div hK).mpr hX)
  unfold powerTail
  rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  calc
    _ ≤ (e * (X / K) ^ (-exponent h)) * M :=
      mul_le_mul_of_nonneg_left (hf _ hlog)
        (mul_nonneg he (Real.rpow_pos_of_pos hp _).le)
    _ = _ := by ring

theorem powerTail_square_bound {K e M X : ℝ} (hK : 0 < K) (he : 0 ≤ e)
    (hM : 0 ≤ M) (hX : K ≤ X) (h : ℝ) {f : ℝ → ℝ}
    (hf : ∀ t, 0 ≤ t → |f t| ≤ M) :
    powerTail h e K f X ^ 2 ≤ e ^ 2 * M ^ 2 * (X / K) ^ (-2 * exponent h) := by
  have hb := powerTail_bound hK he hX h hf
  have hp := div_pos (hK.trans_le hX) hK
  have hnon : 0 ≤ e * M * (X / K) ^ (-exponent h) := by positivity
  have hs := (sq_le_sq₀ (abs_nonneg _) hnon).mpr hb
  rw [sq_abs, mul_pow, mul_pow, ← Real.rpow_mul_natCast hp.le] at hs
  convert! hs using 1
  congr 2
  ring

theorem powerTail_weighted_change {h ν K e M q : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (he : 0 ≤ e) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ t, 0 ≤ t → |f t| ≤ M) (hq : q < exponent h) :
    IntegrableOn (fun X => X ^ q * change (powerTail h e K f) h ν K X) (Ioi K) ∧
      |∫ X in Ioi K, X ^ q * change (powerTail h e K f) h ν K X| ≤
        heatConstant h ν * e * M * K ^ q / (exponent h - q) := by
  have hE := powerTail_contDiffOn hK h e hf
  have hg := ((edit_contDiffOn hh hν hK hE).continuousOn.fun_sub hE.continuousOn).mono
    (Ioi_subset_Ioi hK.le)
  have hC := (heatConstant_pos hh hν).le
  have hres := weighted_integral_bound (p := -exponent h) (q := q)
    (B := heatConstant h ν * e * M) hK (by linarith) hg ?_
  · unfold change
    simpa only [neg_neg] using hres
  · intro X hX
    calc
      _ ≤ heatConstant h ν * |powerTail h e K f X| / X :=
        change_bound hh hν.le (hK.trans hX)
      _ ≤ heatConstant h ν * (e * M * (X / K) ^ (-exponent h)) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (powerTail_bound hK he hX.le h hbound) hC)
          (hK.trans hX).le
      _ = _ := by ring

theorem powerTail_weighted_squareChange {h ν K e M q : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (he : 0 ≤ e) (hM : 0 ≤ M) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ t, 0 ≤ t → |f t| ≤ M) (hq : q < 2 * exponent h) :
    IntegrableOn (fun X => X ^ q * squareChange (powerTail h e K f) h ν K X) (Ioi K) ∧
      |∫ X in Ioi K, X ^ q * squareChange (powerTail h e K f) h ν K X| ≤
        2 * heatConstant h ν * e ^ 2 * M ^ 2 * K ^ q / (2 * exponent h - q) := by
  have hE := powerTail_contDiffOn hK h e hf
  have hg := (((edit_contDiffOn hh hν hK hE).continuousOn.fun_pow 2).fun_sub
    (hE.continuousOn.fun_pow 2)).mono (Ioi_subset_Ioi hK.le)
  have hC : 0 ≤ 2 * heatConstant h ν :=
    mul_nonneg (by norm_num) (heatConstant_pos hh hν).le
  have hres := weighted_integral_bound (p := -2 * exponent h) (q := q)
    (B := 2 * heatConstant h ν * e ^ 2 * M ^ 2) hK (by linarith) hg ?_
  · unfold squareChange
    simpa only [neg_mul, neg_neg] using hres
  · intro X hX
    calc
      _ ≤ 2 * heatConstant h ν * powerTail h e K f X ^ 2 / X :=
        squareChange_bound hh hν.le (hK.trans hX)
      _ ≤ (2 * heatConstant h ν) * (e ^ 2 * M ^ 2 * (X / K) ^ (-2 * exponent h)) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (powerTail_square_bound hK he hM hX.le h hbound) hC)
          (hK.trans hX).le
      _ = _ := by ring

noncomputable def pressureDebt (E : ℝ → ℝ) (h ν K : ℝ) : ℝ :=
  ∫ X in Ioi K, squareChange E h ν K X / X

noncomputable def energyDebt (E : ℝ → ℝ) (h ν K : ℝ) : ℝ :=
  ∫ X in Ioi K, squareChange E h ν K X

noncomputable def angularDebt (E : ℝ → ℝ) (h ν K : ℝ) : ℝ :=
  ∫ X in Ioi K, Real.sqrt (2 * X) * change E h ν K X

theorem pressureDebt_eq (E : ℝ → ℝ) (h ν K : ℝ) :
    pressureDebt E h ν K = ∫ X in Ioi K, X ^ (-1 : ℝ) * squareChange E h ν K X := by
  simp only [pressureDebt, Real.rpow_neg_one, div_eq_mul_inv, mul_comm]

theorem angularDebt_eq (E : ℝ → ℝ) (h ν K : ℝ) :
    angularDebt E h ν K = Real.sqrt 2 *
      ∫ X in Ioi K, X ^ (1 / 2 : ℝ) * change E h ν K X := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X _
  simp only [ Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_eq_rpow, mul_assoc]

theorem powerTail_pressure {h ν K e M : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (he : 0 ≤ e) (hM : 0 ≤ M) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ t, 0 ≤ t → |f t| ≤ M) :
    IntegrableOn (fun X => squareChange (powerTail h e K f) h ν K X / X) (Ioi K) ∧
      |pressureDebt (powerTail h e K f) h ν K| ≤
        2 * heatConstant h ν * e ^ 2 * M ^ 2 / (K * (2 * exponent h + 1)) := by
  rcases powerTail_weighted_squareChange (q := -1) hh hν hK he hM hf hbound
    (by unfold exponent; linarith) with ⟨hi, hb⟩
  constructor
  · simpa only [Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using hi
  · rw [pressureDebt_eq]
    convert! hb using 1 ;
      simp only [Real.rpow_neg_one, sub_neg_eq_add, div_eq_mul_inv, mul_inv_rev] ; ring

theorem powerTail_energy {h ν K e M : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (he : 0 ≤ e) (hM : 0 ≤ M) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ t, 0 ≤ t → |f t| ≤ M) :
    IntegrableOn (squareChange (powerTail h e K f) h ν K) (Ioi K) ∧
      |energyDebt (powerTail h e K f) h ν K| ≤
        2 * heatConstant h ν * e ^ 2 * M ^ 2 / (2 * exponent h) := by
  simpa only [energyDebt, Real.rpow_zero, one_mul, mul_one, sub_zero] using
    (powerTail_weighted_squareChange (q := 0) hh hν hK he hM hf hbound
      (by unfold exponent; linarith))

theorem powerTail_angular {h ν K e M : ℝ} (hh : 0 < h) (hν : 0 < ν)
    (hK : 0 < K) (he : 0 ≤ e) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ t, 0 ≤ t → |f t| ≤ M) :
    IntegrableOn (fun X => Real.sqrt (2 * X) * change (powerTail h e K f) h ν K X) (Ioi K) ∧
      |angularDebt (powerTail h e K f) h ν K| ≤
        Real.sqrt 2 * heatConstant h ν * e * M * Real.sqrt K / h := by
  rcases powerTail_weighted_change (q := 1 / 2) hh hν hK he hf hbound
    (by unfold exponent; linarith) with ⟨hi, hb⟩
  constructor
  · have hi' := hi.const_mul (Real.sqrt 2)
    have heq : (fun X => Real.sqrt (2 * X) * change (powerTail h e K f) h ν K X) =
        (fun X => Real.sqrt 2 * (X ^ (1 / 2 : ℝ) * change (powerTail h e K f) h ν K X)) := by
      funext X
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow X]
      ring
    rw [heq]
    exact hi'
  · rw [angularDebt_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    calc
      _ ≤ Real.sqrt 2 *
          (heatConstant h ν * e * M * K ^ (1 / 2 : ℝ) / (exponent h - 1 / 2)) :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg 2)
      _ = _ := by
        rw [← Real.sqrt_eq_rpow K, show exponent h - 1 / 2 = h by unfold exponent; ring]
        ring

/-! ## The actual outgoing schedule -/

open OutgoingTail

noncomputable def switchStart (d : TailData) : ℝ := tailStart d + 1 / 5

/-- This carrier amplitude is fixed by the schedule, independently of `K`. -/
noncomputable def outgoingAmplitude (d : TailData) : ℝ :=
  powerConstant d * Real.exp (-exponent d.h * switchStart d)

noncomputable def outgoingShape (d : TailData) (t : ℝ) : ℝ := tailShape d (t + 1 / 5)

noncomputable def outgoingProfile (d : TailData) (K eta X : ℝ) : ℝ :=
  finalAngular d (switchStart d + Real.log (X / K), eta)

noncomputable def outgoingEdit (d : TailData) (ν K eta X : ℝ) : ℝ :=
  edit (outgoingProfile d K eta) d.h ν K X

theorem outgoingAmplitude_pos (d : TailData) : 0 < outgoingAmplitude d :=
  mul_pos (powerConstant_pos d) (Real.exp_pos _)

theorem outgoingShape_contDiff (d : TailData) : ContDiff ℝ ∞ (outgoingShape d) :=
  (tailShape_contDiff d).comp (contDiff_id.add contDiff_const)

theorem outgoingShape_bound (d : TailData) (t : ℝ) : |outgoingShape d t| ≤ 1 := by
  rw [outgoingShape, abs_of_pos (tailShape_pos d _)]
  exact (tailShape_bounds d _).2

theorem outgoingProfile_pos (d : TailData) (K eta X : ℝ) : 0 < outgoingProfile d K eta X :=
  finalAngular_pos d _

theorem outgoingProfile_eq_powerTail_of_log (d : TailData) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (hlog : 0 ≤ Real.log (X / K)) (eta : ℝ) :
    outgoingProfile d K eta X =
      powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X := by
  have hy : tailStart d ≤ switchStart d + Real.log (X / K) := by
    unfold switchStart
    linarith
  have hshape : switchStart d + Real.log (X / K) - tailStart d = Real.log (X / K) + 1 / 5 := by
    unfold switchStart
    ring
  have hex : Real.exp (-exponent d.h * (switchStart d + Real.log (X / K))) =
      Real.exp (-exponent d.h * switchStart d) * (X / K) ^ (-exponent d.h) := by
    rw [Real.rpow_def_of_pos (div_pos hX hK), ← Real.exp_add]
    congr 1
    ring
  unfold outgoingProfile
  rw [finalAngular_tail d eta hy, hshape]
  change powerConstant d * Real.exp (-exponent d.h * (switchStart d + Real.log (X / K))) *
      tailShape d (Real.log (X / K) + 1 / 5) = _
  rw [hex]
  unfold powerTail outgoingAmplitude outgoingShape
  ring

theorem outgoingProfile_eq_powerTail (d : TailData) {K X : ℝ}
    (hK : 0 < K) (hX : K ≤ X) (eta : ℝ) :
    outgoingProfile d K eta X =
      powerTail d.h (outgoingAmplitude d) K (outgoingShape d) X :=
  outgoingProfile_eq_powerTail_of_log d hK (hK.trans_le hX)
    (Real.log_nonneg ((one_le_div hK).mpr hX)) eta

theorem outgoingProfile_joint_contDiffOn (d : TailData) {K : ℝ} (hK : 0 < K) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => outgoingProfile d K p.2 p.1)
      (Ioi 0 ×ˢ univ) := by
  intro p hp
  have hl : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Real.log (p.1 / K)) p :=
    (Real.contDiffAt_log.mpr (div_pos hp.1 hK).ne').comp p (contDiffAt_fst.div_const K)
  exact ((finalAngular_contDiff d).contDiffAt.comp p
    ((contDiffAt_const.add hl).prodMk contDiffAt_snd)).contDiffWithinAt

theorem outgoingEdit_joint_contDiffOn (d : TailData) {ν K : ℝ}
    (hν : 0 < ν) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => outgoingEdit d ν K p.2 p.1)
      (Ioi 0 ×ˢ univ) := by
  apply (outgoingProfile_joint_contDiffOn d hK).mul
  exact (multiplier_contDiffOn d.h_pos hν hK).comp contDiffOn_fst (fun _ hp => hp.1)

theorem outgoingEdit_pos (d : TailData) {ν K X : ℝ} (hν : 0 ≤ ν) (hX : 0 < X)
    (eta : ℝ) : 0 < outgoingEdit d ν K eta X :=
  edit_pos d.h_pos hν hX (outgoingProfile_pos d K eta X)

/-- Exact matching before tail logarithmic time `0.2`. -/
theorem outgoingEdit_before (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (hXK : X ≤ K) :
    outgoingEdit d ν K eta X = outgoingProfile d K eta X :=
  edit_before _ _ _ hK hX hXK

/-- At tail logarithmic time `0.5`, the full heat factor is present. -/
theorem outgoingEdit_full (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (hfull : 1 / 2 ≤ Real.log (X / K) + 1 / 5) :
    outgoingEdit d ν K eta X =
      outgoingAmplitude d * (X / K) ^ (-exponent d.h) *
        tailShape d (Real.log (X / K) + 1 / 5) *
          RadialHeatProfile.profile (1 + d.h) (2 * ν / X) := by
  unfold outgoingEdit
  rw [edit_after _ _ _ (by linarith),
    outgoingProfile_eq_powerTail_of_log d hK hX (by linarith) eta]
  rfl

theorem outgoing_change_eq (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : K ≤ X) :
    change (outgoingProfile d K eta) d.h ν K X =
      change (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K X := by
  simp only [change, edit, outgoingProfile_eq_powerTail d hK hX eta]

theorem outgoing_squareChange_eq (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : K ≤ X) :
    squareChange (outgoingProfile d K eta) d.h ν K X =
      squareChange (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K X := by
  simp only [squareChange, edit, outgoingProfile_eq_powerTail d hK hX eta]

theorem outgoing_pressureDebt_eq (d : TailData) (ν eta : ℝ) {K : ℝ} (hK : 0 < K) :
    pressureDebt (outgoingProfile d K eta) d.h ν K =
      pressureDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [outgoing_squareChange_eq d ν eta hK hX.le]

theorem outgoing_energyDebt_eq (d : TailData) (ν eta : ℝ) {K : ℝ} (hK : 0 < K) :
    energyDebt (outgoingProfile d K eta) d.h ν K =
      energyDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  rw [outgoing_squareChange_eq d ν eta hK hX.le]

theorem outgoing_angularDebt_eq (d : TailData) (ν eta : ℝ) {K : ℝ} (hK : 0 < K) :
    angularDebt (outgoingProfile d K eta) d.h ν K =
      angularDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [outgoing_change_eq d ν eta hK hX.le]

theorem outgoing_pressure (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K) (eta : ℝ) :
    IntegrableOn (fun X => squareChange (outgoingProfile d K eta) d.h ν K X / X) (Ioi K) ∧
      |pressureDebt (outgoingProfile d K eta) d.h ν K| ≤
        2 * heatConstant d.h ν * outgoingAmplitude d ^ 2 / (K * (2 * exponent d.h + 1)) := by
  have h := powerTail_pressure d.h_pos hν hK (outgoingAmplitude_pos d).le
    (show (0 : ℝ) ≤ 1 by norm_num) (outgoingShape_contDiff d) (fun t _ => outgoingShape_bound d t)
  constructor
  · apply h.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [outgoing_squareChange_eq d ν eta hK hX.le]
  · rw [outgoing_pressureDebt_eq d ν eta hK]
    simpa only [one_pow, mul_one] using h.2

theorem outgoing_energy (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K) (eta : ℝ) :
    IntegrableOn (squareChange (outgoingProfile d K eta) d.h ν K) (Ioi K) ∧
      |energyDebt (outgoingProfile d K eta) d.h ν K| ≤
        2 * heatConstant d.h ν * outgoingAmplitude d ^ 2 / (2 * exponent d.h) := by
  have h := powerTail_energy d.h_pos hν hK (outgoingAmplitude_pos d).le
    (show (0 : ℝ) ≤ 1 by norm_num) (outgoingShape_contDiff d) (fun t _ => outgoingShape_bound d t)
  constructor
  · apply h.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [outgoing_squareChange_eq d ν eta hK hX.le]
  · rw [outgoing_energyDebt_eq d ν eta hK]
    simpa only [one_pow, mul_one] using h.2

theorem outgoing_angular (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K) (eta : ℝ) :
    IntegrableOn (fun X => Real.sqrt (2 * X) * change (outgoingProfile d K eta) d.h ν K X)
      (Ioi K) ∧
      |angularDebt (outgoingProfile d K eta) d.h ν K| ≤
        Real.sqrt 2 * heatConstant d.h ν * outgoingAmplitude d * Real.sqrt K / d.h := by
  have h := powerTail_angular d.h_pos hν hK (outgoingAmplitude_pos d).le
    (outgoingShape_contDiff d) (M := 1) (fun t _ => outgoingShape_bound d t)
  constructor
  · apply h.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    rw [outgoing_change_eq d ν eta hK hX.le]
  · rw [outgoing_angularDebt_eq d ν eta hK]
    simpa only [mul_one] using h.2

/-- The fully switched profile is exactly the radial heat profile times the
prescribed flat terminal shape, with its normalization made explicit. -/
theorem outgoingEdit_heat_factorization (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (hfull : 1 / 2 ≤ Real.log (X / K) + 1 / 5) :
    outgoingEdit d ν K eta X =
      (outgoingAmplitude d * K ^ exponent d.h) *
        RadialHeatProfile.spatialProfile (1 + d.h) ν X *
          tailShape d (Real.log (X / K) + 1 / 5) := by
  rw [outgoingEdit_full d ν eta hK hX hfull]
  have hexp : RadialHeatProfile.spatialExponent (1 + d.h) = -exponent d.h := by
    unfold RadialHeatProfile.spatialExponent exponent
    ring
  rw [RadialHeatProfile.spatialProfile, hexp, Real.div_rpow hX.le hK.le,
    Real.rpow_neg hK.le]
  simp only [div_inv_eq_mul]
  ring

/-- Beyond the terminal taper, the profile is the unmodified exact radial
heat solution with a positive constant normalization. -/
theorem outgoingEdit_eventual_heat (d : TailData) (ν eta : ℝ) {K X : ℝ}
    (hK : 0 < K) (hX : 0 < X) (htail : 3 ≤ Real.log (X / K) + 1 / 5) :
    outgoingEdit d ν K eta X =
      (outgoingAmplitude d * K ^ exponent d.h) *
        RadialHeatProfile.spatialProfile (1 + d.h) ν X := by
  rw [outgoingEdit_heat_factorization d ν eta hK hX (by linarith),
    tailShape_late d htail, mul_one]

/-- The actual switch amplitude is fixed by the schedule and comparable to
the carrier amplitude used in the estimates. -/
theorem outgoingProfile_at_switch (d : TailData) {K : ℝ} (hK : 0 < K) (eta : ℝ) :
    outgoingProfile d K eta K = outgoingAmplitude d * (1 - d.rho) := by
  rw [outgoingProfile_eq_powerTail d hK le_rfl eta]
  simp only [powerTail, div_self hK.ne', Real.one_rpow, mul_one, Real.log_one,
    outgoingShape, zero_add, tailShape_early d (by norm_num : (1 / 5 : ℝ) ≤ 1)]

theorem outgoing_pressure_eta_contDiff (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K) :
    ContDiff ℝ ∞ (fun eta => pressureDebt (outgoingProfile d K eta) d.h ν K) := by
  have heq : (fun eta => pressureDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => pressureDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_pressureDebt_eq d ν eta hK
  rw [heq]
  exact contDiff_const

theorem outgoing_energy_eta_contDiff (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K) :
    ContDiff ℝ ∞ (fun eta => energyDebt (outgoingProfile d K eta) d.h ν K) := by
  have heq : (fun eta => energyDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => energyDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_energyDebt_eq d ν eta hK
  rw [heq]
  exact contDiff_const

theorem outgoing_angular_eta_contDiff (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K) :
    ContDiff ℝ ∞ (fun eta => angularDebt (outgoingProfile d K eta) d.h ν K) := by
  have heq : (fun eta => angularDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => angularDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_angularDebt_eq d ν eta hK
  rw [heq]
  exact contDiff_const

theorem outgoing_pressure_eta_jet_zero (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    iteratedDeriv (n + 1) (fun eta => pressureDebt (outgoingProfile d K eta) d.h ν K) eta = 0 := by
  have heq : (fun eta => pressureDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => pressureDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_pressureDebt_eq d ν eta hK
  rw [heq, SmoothCutoffs.iteratedDeriv_const_succ]

theorem outgoing_energy_eta_jet_zero (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    iteratedDeriv (n + 1) (fun eta => energyDebt (outgoingProfile d K eta) d.h ν K) eta = 0 := by
  have heq : (fun eta => energyDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => energyDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_energyDebt_eq d ν eta hK
  rw [heq, SmoothCutoffs.iteratedDeriv_const_succ]

theorem outgoing_angular_eta_jet_zero (d : TailData) (ν : ℝ) {K : ℝ} (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    iteratedDeriv (n + 1) (fun eta => angularDebt (outgoingProfile d K eta) d.h ν K) eta = 0 := by
  have heq : (fun eta => angularDebt (outgoingProfile d K eta) d.h ν K) =
      (fun _ => angularDebt (powerTail d.h (outgoingAmplitude d) K (outgoingShape d)) d.h ν K) :=
    funext fun eta => outgoing_angularDebt_eq d ν eta hK
  rw [heq, SmoothCutoffs.iteratedDeriv_const_succ]

/-- The pressure estimate holds with every fixed slow-variable jet. -/
theorem outgoing_pressure_jet_bound (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    |iteratedDeriv n (fun eta => pressureDebt (outgoingProfile d K eta) d.h ν K) eta| ≤
      2 * heatConstant d.h ν * outgoingAmplitude d ^ 2 / (K * (2 * exponent d.h + 1)) := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using (outgoing_pressure d hν hK eta).2
  | succ n =>
    rw [outgoing_pressure_eta_jet_zero d ν hK n eta, abs_zero]
    have hc := heatConstant_pos d.h_pos hν
    have he : 0 < exponent d.h := by unfold exponent; linarith [d.h_pos]
    positivity

/-- The energy estimate holds with every fixed slow-variable jet. -/
theorem outgoing_energy_jet_bound (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    |iteratedDeriv n (fun eta => energyDebt (outgoingProfile d K eta) d.h ν K) eta| ≤
      2 * heatConstant d.h ν * outgoingAmplitude d ^ 2 / (2 * exponent d.h) := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using (outgoing_energy d hν hK eta).2
  | succ n =>
    rw [outgoing_energy_eta_jet_zero d ν hK n eta, abs_zero]
    have hc := heatConstant_pos d.h_pos hν
    have he : 0 < exponent d.h := by unfold exponent; linarith [d.h_pos]
    positivity

/-- The renormalized angular estimate holds with every fixed slow-variable jet. -/
theorem outgoing_angular_jet_bound (d : TailData) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K)
    (n : ℕ) (eta : ℝ) :
    |iteratedDeriv n (fun eta => angularDebt (outgoingProfile d K eta) d.h ν K) eta| ≤
      Real.sqrt 2 * heatConstant d.h ν * outgoingAmplitude d * Real.sqrt K / d.h := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using (outgoing_angular d hν hK eta).2
  | succ n =>
    rw [outgoing_angular_eta_jet_zero d ν hK n eta, abs_zero]
    have hc := heatConstant_pos d.h_pos hν
    have he := outgoingAmplitude_pos d
    have hh := d.h_pos
    positivity

end NavierStokes.HeatTailEdit
