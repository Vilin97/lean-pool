/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Constants

/-! # Note Constants -/

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSNoteStepCoeff_nonneg (s : ℝ) :
    0 ≤ coarsePoincareRHSNoteStepCoeff s := by
  unfold coarsePoincareRHSNoteStepCoeff
  exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem coarsePoincareRHSFiniteSumRatio_noteStepCoeff_eq (s : ℝ) :
    coarsePoincareRHSFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) =
      Real.rpow (3 : ℝ) (-s / 2) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  unfold coarsePoincareRHSFiniteSumRatio coarsePoincareRHSScaledStepCoeff
    coarsePoincareRHSNoteStepCoeff
  calc
    Real.rpow (3 : ℝ) (-(3 * s / 2)) * Real.rpow (3 : ℝ) s =
        Real.rpow (3 : ℝ) (-(3 * s / 2) + s) := by
          exact (Real.rpow_add h3 (-(3 * s / 2)) s).symm
    _ = Real.rpow (3 : ℝ) (-s / 2) := by
          congr 1
          ring

theorem coarsePoincareRHSForceFiniteSumRatio_noteStepCoeff_eq (s : ℝ) :
    coarsePoincareRHSForceFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) =
      Real.rpow (3 : ℝ) (-(3 * s / 2)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hscaled :
      coarsePoincareRHSScaledStepCoeff s (coarsePoincareRHSNoteStepCoeff s) =
        Real.rpow (3 : ℝ) (-s / 2) := by
    simpa [coarsePoincareRHSFiniteSumRatio] using
      coarsePoincareRHSFiniteSumRatio_noteStepCoeff_eq s
  unfold coarsePoincareRHSForceFiniteSumRatio
  rw [hscaled]
  calc
    Real.rpow (3 : ℝ) (-s / 2) * Real.rpow (3 : ℝ) (-s) =
        Real.rpow (3 : ℝ) (-s / 2 + -s) := by
          exact (Real.rpow_add h3 (-s / 2) (-s)).symm
    _ = Real.rpow (3 : ℝ) (-(3 * s / 2)) := by
          congr 1
          ring

theorem coarsePoincareRHSFiniteSumRatio_noteStepCoeff_nonneg (s : ℝ) :
    0 ≤ coarsePoincareRHSFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) := by
  rw [coarsePoincareRHSFiniteSumRatio_noteStepCoeff_eq]
  exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem coarsePoincareRHSFiniteSumRatio_noteStepCoeff_lt_one
    {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSFiniteSumRatio s (coarsePoincareRHSNoteStepCoeff s) < 1 := by
  rw [coarsePoincareRHSFiniteSumRatio_noteStepCoeff_eq]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith)

theorem coarsePoincareRHSForceFiniteSumRatio_nonneg_of_finiteSumRatio_nonneg
    {s θ : ℝ} (hr_nonneg : 0 ≤ coarsePoincareRHSFiniteSumRatio s θ) :
    0 ≤ coarsePoincareRHSForceFiniteSumRatio s θ := by
  unfold coarsePoincareRHSForceFiniteSumRatio
  exact mul_nonneg (by simpa [coarsePoincareRHSFiniteSumRatio] using hr_nonneg)
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)

theorem coarsePoincareRHSForceFiniteSumRatio_lt_one_of_finiteSumRatio_lt_one
    {s θ : ℝ} (hs : 0 < s)
    (hr_nonneg : 0 ≤ coarsePoincareRHSFiniteSumRatio s θ)
    (hr_lt_one : coarsePoincareRHSFiniteSumRatio s θ < 1) :
    coarsePoincareRHSForceFiniteSumRatio s θ < 1 := by
  have hdecay_le_one : Real.rpow (3 : ℝ) (-s) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hle :
      coarsePoincareRHSForceFiniteSumRatio s θ ≤ coarsePoincareRHSFiniteSumRatio s θ := by
    unfold coarsePoincareRHSForceFiniteSumRatio
    simpa [coarsePoincareRHSFiniteSumRatio] using
      mul_le_of_le_one_right hr_nonneg hdecay_le_one
  exact lt_of_le_of_lt hle hr_lt_one

theorem coarsePoincareRHSNoteEta_pos {s : ℝ} (hs : 0 < s) :
    0 < coarsePoincareRHSNoteEta s := by
  unfold coarsePoincareRHSNoteEta
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  exact div_pos (by linarith) (by linarith)

theorem coarsePoincareRHSNoteEta_lt_half {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSNoteEta s < (1 : ℝ) / 2 := by
  unfold coarsePoincareRHSNoteEta
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hden : 0 < 2 - r := by linarith
  rw [div_lt_iff₀ hden]
  nlinarith

theorem one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_eq {s : ℝ}
    (hs : 0 < s) :
    1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s) =
      Real.rpow (3 : ℝ) (-s / 2) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hden : 2 - r ≠ 0 := by linarith
  unfold coarsePoincareRHSNoteEta
  change 1 - coarsePoincareRHSAbsorbedRnCoeff ((1 - r) / (2 - r)) = r
  unfold coarsePoincareRHSAbsorbedRnCoeff
  have hone_sub :
      1 - (1 - r) / (2 - r) = (2 - r)⁻¹ := by
    field_simp [hden]
    ring
  rw [hone_sub]
  field_simp [hden]
  ring

theorem one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_pos {s : ℝ}
    (hs : 0 < s) :
    0 < 1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s) := by
  rw [one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_eq hs]
  exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _

theorem coarsePoincareRHSAbsorbedEnergyCoeff_noteEta_eq {s : ℝ}
    (hs : 0 < s) :
    coarsePoincareRHSAbsorbedEnergyCoeff (coarsePoincareRHSNoteEta s) =
      2 - Real.rpow (3 : ℝ) (-s / 2) := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hden : 2 - r ≠ 0 := by linarith
  unfold coarsePoincareRHSNoteEta
  change coarsePoincareRHSAbsorbedEnergyCoeff ((1 - r) / (2 - r)) = 2 - r
  unfold coarsePoincareRHSAbsorbedEnergyCoeff
  have hone_sub :
      1 - (1 - r) / (2 - r) = (2 - r)⁻¹ := by
    field_simp [hden]
    ring
  rw [hone_sub]
  field_simp [hden]
  ring

theorem coarsePoincareRHSNoteEnergyEnvelope_eq {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSNoteEnergyEnvelope s =
      (Real.rpow (3 : ℝ) (-s / 2))⁻¹ *
        (2 - Real.rpow (3 : ℝ) (-s / 2)) := by
  unfold coarsePoincareRHSNoteEnergyEnvelope
  rw [one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_eq hs,
    coarsePoincareRHSAbsorbedEnergyCoeff_noteEta_eq hs]

theorem coarsePoincareRHSAbsorbedForceCoeff_noteEta_eq {s : ℝ}
    (hs : 0 < s) :
    coarsePoincareRHSAbsorbedForceCoeff (coarsePoincareRHSNoteEta s) =
      2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) +
        2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) *
          (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hden : 2 - r ≠ 0 := by linarith
  have hnum : 1 - r ≠ 0 := by linarith
  unfold coarsePoincareRHSNoteEta
  change
    coarsePoincareRHSAbsorbedForceCoeff ((1 - r) / (2 - r)) =
      2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹
  unfold coarsePoincareRHSAbsorbedForceCoeff
  have hone_sub :
      1 - (1 - r) / (2 - r) = (2 - r)⁻¹ := by
    field_simp [hden]
    ring
  rw [hone_sub]
  field_simp [hden, hnum]

theorem coarsePoincareRHSNoteForceEnvelope_eq {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSNoteForceEnvelope s =
      (Real.rpow (3 : ℝ) (-s / 2))⁻¹ *
        (2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) +
          2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) *
            (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹) := by
  unfold coarsePoincareRHSNoteForceEnvelope
  rw [one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_eq hs,
    coarsePoincareRHSAbsorbedForceCoeff_noteEta_eq hs]

theorem inv_rpow_three_neg_half_eq_rpow_half (s : ℝ) :
    (Real.rpow (3 : ℝ) (-s / 2))⁻¹ = Real.rpow (3 : ℝ) (s / 2) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hneg :
      Real.rpow (3 : ℝ) (-s / 2) = (Real.rpow (3 : ℝ) (s / 2))⁻¹ := by
    rw [show -s / 2 = -(s / 2) by ring]
    exact Real.rpow_neg h3.le (s / 2)
  rw [hneg, inv_inv]

theorem rpow_three_half_mul_rpow_three_neg_half_eq_one (s : ℝ) :
    Real.rpow (3 : ℝ) (s / 2) * Real.rpow (3 : ℝ) (-s / 2) = 1 := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  calc
    Real.rpow (3 : ℝ) (s / 2) * Real.rpow (3 : ℝ) (-s / 2)
        = Real.rpow (3 : ℝ) (s / 2 + -s / 2) := by
            exact (Real.rpow_add h3 (s / 2) (-s / 2)).symm
    _ = 1 := by
          rw [show s / 2 + -s / 2 = 0 by ring]
          simp

theorem coarsePoincareRHSNoteEnergyEnvelope_eq_two_mul_rpow_half_sub_one
    {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSNoteEnergyEnvelope s =
      2 * Real.rpow (3 : ℝ) (s / 2) - 1 := by
  rw [coarsePoincareRHSNoteEnergyEnvelope_eq hs,
    inv_rpow_three_neg_half_eq_rpow_half]
  rw [mul_sub, rpow_three_half_mul_rpow_three_neg_half_eq_one]
  ring

theorem coarsePoincareRHSNoteForceEnvelope_eq_rpow_half_mul {s : ℝ}
    (hs : 0 < s) :
    coarsePoincareRHSNoteForceEnvelope s =
      Real.rpow (3 : ℝ) (s / 2) *
        (2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) +
          2 * (2 - Real.rpow (3 : ℝ) (-s / 2)) *
            (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹) := by
  rw [coarsePoincareRHSNoteForceEnvelope_eq hs,
    inv_rpow_three_neg_half_eq_rpow_half]

theorem rpow_three_half_le_three_of_le_two {s : ℝ} (hs_le : s ≤ 2) :
    Real.rpow (3 : ℝ) (s / 2) ≤ 3 := by
  have hexp : s / 2 ≤ (1 : ℝ) := by linarith
  simpa using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp

theorem coarsePoincareRHSNoteEnergyEnvelope_le_five {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 2) :
    coarsePoincareRHSNoteEnergyEnvelope s ≤ 5 := by
  rw [coarsePoincareRHSNoteEnergyEnvelope_eq_two_mul_rpow_half_sub_one hs]
  have hpow : Real.rpow (3 : ℝ) (s / 2) ≤ 3 :=
    rpow_three_half_le_three_of_le_two hs_le
  linarith

theorem coarsePoincareRHSNoteForceEnvelope_le_twentyfour_mul_inv_one_sub
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 2) :
    coarsePoincareRHSNoteForceEnvelope s ≤
      24 * (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hB_nonneg : 0 ≤ (1 - r)⁻¹ := by
    exact inv_nonneg.mpr (by linarith)
  have hB_ge_one : 1 ≤ (1 - r)⁻¹ := by
    exact (one_le_inv₀ (by linarith : 0 < 1 - r)).2 (by linarith)
  have hpow : Real.rpow (3 : ℝ) (s / 2) ≤ 3 :=
    rpow_three_half_le_three_of_le_two hs_le
  have hterm1 :
      2 * (2 - r) ≤ 4 * (1 - r)⁻¹ := by
    have hleft : 2 * (2 - r) ≤ 4 := by nlinarith [hr_nonneg]
    have hright : 4 ≤ 4 * (1 - r)⁻¹ := by nlinarith [hB_ge_one]
    linarith
  have hterm2 :
      2 * (2 - r) * (1 - r)⁻¹ ≤ 4 * (1 - r)⁻¹ := by
    have hleft : 2 * (2 - r) ≤ 4 := by nlinarith [hr_nonneg]
    exact mul_le_mul_of_nonneg_right hleft hB_nonneg
  have hinner :
      2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹ ≤ 8 * (1 - r)⁻¹ := by
    linarith
  have hinner_nonneg :
      0 ≤ 2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹ := by
    nlinarith [hr_lt_one, hB_nonneg]
  rw [coarsePoincareRHSNoteForceEnvelope_eq_rpow_half_mul hs]
  change
    Real.rpow (3 : ℝ) (s / 2) *
        (2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹) ≤
      24 * (1 - r)⁻¹
  calc
    Real.rpow (3 : ℝ) (s / 2) *
        (2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹)
        ≤ 3 * (2 * (2 - r) + 2 * (2 - r) * (1 - r)⁻¹) := by
          exact mul_le_mul_of_nonneg_right hpow hinner_nonneg
    _ ≤ 3 * (8 * (1 - r)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = 24 * (1 - r)⁻¹ := by ring

theorem one_half_le_log_three : (1 / 2 : ℝ) ≤ Real.log 3 := by
  have hexp_half_le_exp_one : Real.exp ((1 : ℝ) / 2) ≤ Real.exp 1 := by
    exact (Real.exp_le_exp).2 (by norm_num)
  have hexp_half_lt_three : Real.exp ((1 : ℝ) / 2) < 3 := by
    exact lt_of_le_of_lt hexp_half_le_exp_one
      (lt_trans Real.exp_one_lt_d9 (by norm_num))
  exact le_of_lt <|
    (Real.lt_log_iff_exp_lt (by norm_num : 0 < (3 : ℝ))).2 hexp_half_lt_three

theorem inv_one_sub_rpow_three_neg_half_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ ≤ 5 * s⁻¹ := by
  let x : ℝ := s * Real.log 3 / 2
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hlog_pos : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have h1x_pos : 0 < 1 + x := by linarith
  have hr_eq : r = (Real.exp x)⁻¹ := by
    dsimp [r, x]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ))]
    have harg : Real.log 3 * (-s / 2) = -(s * Real.log 3 / 2) := by ring
    rw [harg, Real.exp_neg]
  have hexp_ge : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hr_le : r ≤ (1 + x)⁻¹ := by
    rw [hr_eq]
    exact (inv_le_inv₀ (Real.exp_pos x) h1x_pos).2 hexp_ge
  have hx_div_pos : 0 < x / (1 + x) := div_pos hx_pos h1x_pos
  have hden_lower : x / (1 + x) ≤ 1 - r := by
    have hcalc : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      field_simp [h1x_pos.ne']
      ring
    calc
      x / (1 + x) = 1 - (1 + x)⁻¹ := hcalc.symm
      _ ≤ 1 - r := by linarith
  have hden_pos : 0 < 1 - r :=
    lt_of_lt_of_le hx_div_pos hden_lower
  have hinv_le : (1 - r)⁻¹ ≤ (x / (1 + x))⁻¹ := by
    exact (inv_le_inv₀ hden_pos hx_div_pos).2 hden_lower
  have hquot_inv : (x / (1 + x))⁻¹ = (1 + x) / x := by
    field_simp [hx_pos.ne', h1x_pos.ne']
  have hx_lower : s / 4 ≤ x := by
    dsimp [x]
    nlinarith [mul_le_mul_of_nonneg_left one_half_le_log_three hs.le]
  have hs4_pos : 0 < s / 4 := by positivity
  have hx_inv_le : x⁻¹ ≤ 4 * s⁻¹ := by
    have hbase : x⁻¹ ≤ (s / 4)⁻¹ :=
      (inv_le_inv₀ hx_pos hs4_pos).2 hx_lower
    have hrewrite : (s / 4)⁻¹ = 4 * s⁻¹ := by
      field_simp [hs.ne']
    simpa [hrewrite] using hbase
  have hs_inv_ge_one : 1 ≤ s⁻¹ := (one_le_inv₀ hs).2 hs_le
  have hquot_le : (1 + x) / x ≤ 5 * s⁻¹ := by
    have hquot : (1 + x) / x = 1 + x⁻¹ := by
      field_simp [hx_pos.ne']
      ring
    rw [hquot]
    nlinarith [hx_inv_le, hs_inv_ge_one]
  calc
    (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ = (1 - r)⁻¹ := rfl
    _ ≤ (x / (1 + x))⁻¹ := hinv_le
    _ = (1 + x) / x := hquot_inv
    _ ≤ 5 * s⁻¹ := hquot_le

theorem inv_one_sub_rpow_three_neg_three_half_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-(3 * s / 2)))⁻¹ ≤ 5 * s⁻¹ := by
  let r₁ : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  let r₃ : ℝ := Real.rpow (3 : ℝ) (-(3 * s / 2))
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr₃_lt_one : r₃ < 1 := by
    dsimp [r₃]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr_le : r₃ ≤ r₁ := by
    dsimp [r₁, r₃]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hden₁_pos : 0 < 1 - r₁ := by linarith
  have hden₃_pos : 0 < 1 - r₃ := by linarith
  have hden_order : 1 - r₁ ≤ 1 - r₃ := by linarith
  have hinv_order : (1 - r₃)⁻¹ ≤ (1 - r₁)⁻¹ :=
    (inv_le_inv₀ hden₃_pos hden₁_pos).2 hden_order
  calc
    (1 - Real.rpow (3 : ℝ) (-(3 * s / 2)))⁻¹ = (1 - r₃)⁻¹ := rfl
    _ ≤ (1 - r₁)⁻¹ := hinv_order
    _ = (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := rfl
    _ ≤ 5 * s⁻¹ := inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le

theorem inv_one_sub_rpow_three_neg_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ 5 * s⁻¹ := by
  let r₁ : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  let r₂ : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr₂_lt_one : r₂ < 1 := by
    dsimp [r₂]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr_le : r₂ ≤ r₁ := by
    dsimp [r₁, r₂]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hden₁_pos : 0 < 1 - r₁ := by linarith
  have hden₂_pos : 0 < 1 - r₂ := by linarith
  have hden_order : 1 - r₁ ≤ 1 - r₂ := by linarith
  have hinv_order : (1 - r₂)⁻¹ ≤ (1 - r₁)⁻¹ :=
    (inv_le_inv₀ hden₂_pos hden₁_pos).2 hden_order
  calc
    (1 - Real.rpow (3 : ℝ) (-s))⁻¹ = (1 - r₂)⁻¹ := rfl
    _ ≤ (1 - r₁)⁻¹ := hinv_order
    _ = (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := rfl
    _ ≤ 5 * s⁻¹ := inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le

theorem inv_geometricDiscount_two_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (geometricDiscount s 2)⁻¹ ≤ 5 * s⁻¹ := by
  let r₁ : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  let r₂ : ℝ := Real.rpow (3 : ℝ) (-s * 2)
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr₂_lt_one : r₂ < 1 := by
    dsimp [r₂]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hr_le : r₂ ≤ r₁ := by
    dsimp [r₁, r₂]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hden₁_pos : 0 < 1 - r₁ := by linarith
  have hden₂_pos : 0 < 1 - r₂ := by linarith
  have hden_order : 1 - r₁ ≤ 1 - r₂ := by linarith
  have hinv_order : (1 - r₂)⁻¹ ≤ (1 - r₁)⁻¹ :=
    (inv_le_inv₀ hden₂_pos hden₁_pos).2 hden_order
  calc
    (geometricDiscount s 2)⁻¹ = (1 - r₂)⁻¹ := by
      simp [geometricDiscount, r₂]
    _ ≤ (1 - r₁)⁻¹ := hinv_order
    _ = (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := rfl
    _ ≤ 5 * s⁻¹ := inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le

theorem coarsePoincareRHSNoteForceEnvelope_le_oneTwenty_mul_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    coarsePoincareRHSNoteForceEnvelope s ≤ 120 * s⁻¹ := by
  have henv :=
    coarsePoincareRHSNoteForceEnvelope_le_twentyfour_mul_inv_one_sub
      hs (by linarith : s ≤ 2)
  have hinv := inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le
  calc
    coarsePoincareRHSNoteForceEnvelope s
        ≤ 24 * (1 - Real.rpow (3 : ℝ) (-s / 2))⁻¹ := henv
    _ ≤ 24 * (5 * s⁻¹) := by
          exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 120 * s⁻¹ := by ring

theorem coarsePoincareRHS_noteEta_discount_le_noteStepCoeff {s : ℝ} (hs : 0 < s) :
    (1 - coarsePoincareRHSAbsorbedRnCoeff (coarsePoincareRHSNoteEta s))⁻¹ *
        coarsePoincareRHSDiscount s ≤ coarsePoincareRHSNoteStepCoeff s := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  rw [one_sub_coarsePoincareRHSAbsorbedRnCoeff_noteEta_eq hs]
  unfold coarsePoincareRHSDiscount coarsePoincareRHSNoteStepCoeff
  have h_inv :
      (Real.rpow (3 : ℝ) (-s / 2))⁻¹ = Real.rpow (3 : ℝ) (s / 2) := by
    have hneg :
        Real.rpow (3 : ℝ) (-s / 2) = (Real.rpow (3 : ℝ) (s / 2))⁻¹ := by
      rw [show -s / 2 = -(s / 2) by ring]
      exact Real.rpow_neg h3.le (s / 2)
    rw [hneg, inv_inv]
  rw [h_inv]
  calc
    Real.rpow (3 : ℝ) (s / 2) * Real.rpow (3 : ℝ) (-2 * s)
        = Real.rpow (3 : ℝ) ((s / 2) + (-2 * s)) := by
          exact (Real.rpow_add h3 (s / 2) (-2 * s)).symm
    _ = Real.rpow (3 : ℝ) (-(3 * s / 2)) := by
          congr 1
          ring
    _ ≤ Real.rpow (3 : ℝ) (-(3 * s / 2)) := le_rfl

end

end Homogenization
