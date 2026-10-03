/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.ChangeExponentDiscount

/-! # Discount Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Finite-exponent multiscale ellipticity: discount scalar bounds
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem book_geometricDiscount_nonneg {s q : ℝ} (hsq : 0 ≤ s * q) :
    0 ≤ geometricDiscount s q := by
  simpa [geometricDiscount_eq_old] using
    Homogenization.geometricDiscount_nonneg hsq

theorem book_geometricDiscount_pos {s q : ℝ} (hsq : 0 < s * q) :
    0 < geometricDiscount s q := by
  simpa [geometricDiscount_eq_old] using
    Homogenization.geometricDiscount_pos hsq

theorem geometricDiscount_le_two_mul {s q : ℝ} (hsq : 0 ≤ s * q) :
    geometricDiscount s q ≤ 2 * (s * q) := by
  let x : ℝ := s * q
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have h3nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have hpow_pos : 0 < Real.rpow (3 : ℝ) x :=
    Real.rpow_pos_of_pos h3pos x
  have hlog_le :
      Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos h3pos
    norm_num at h ⊢
    exact h
  have hxlog_le : x * Real.log (3 : ℝ) ≤ x * 2 :=
    mul_le_mul_of_nonneg_left hlog_le (by simpa [x] using hsq)
  calc
    geometricDiscount s q = 1 - Real.rpow (3 : ℝ) (-x) := by
      simp [geometricDiscount, x]
    _ = 1 - (Real.rpow (3 : ℝ) x)⁻¹ := by
      have h := Real.rpow_neg h3nonneg x
      simpa [Real.rpow_eq_pow] using congrArg (fun y : ℝ => 1 - y) h
    _ ≤ Real.log (Real.rpow (3 : ℝ) x) :=
      Real.one_sub_inv_le_log_of_pos hpow_pos
    _ = x * Real.log (3 : ℝ) := by
      simpa [Real.rpow_eq_pow] using Real.log_rpow h3pos x
    _ ≤ x * 2 := hxlog_le
    _ = 2 * (s * q) := by
      simp [x]
      ring

theorem two_mul_self_rpow_two_div_le_exp_four {q : ℝ} (hq : 1 ≤ q) :
    Real.rpow (2 * q) (2 / q) ≤ Real.exp 4 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hxpos : 0 < 2 * q := by positivity
  have hlog_le :
      Real.log (2 * q) ≤ 2 * q := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hfactor_nonneg : 0 ≤ 2 / q := by positivity
  have hrpow_eq :
      Real.rpow (2 * q) (2 / q) =
        Real.exp (Real.log (2 * q) * (2 / q)) := by
    simpa [Real.rpow_eq_pow] using
      Real.rpow_def_of_pos hxpos (2 / q)
  rw [hrpow_eq]
  exact Real.exp_le_exp.mpr <| by
    calc
      Real.log (2 * q) * (2 / q) ≤ (2 * q) * (2 / q) :=
        mul_le_mul_of_nonneg_right hlog_le hfactor_nonneg
      _ = 4 := by
        field_simp [hqpos.ne']
        ring

theorem geometricDiscount_rpow_two_div_le_exp_four_mul {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    Real.rpow (geometricDiscount s q) (2 / q) ≤
      Real.exp 4 * Real.rpow s (2 / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsq_nonneg : 0 ≤ s * q := mul_nonneg hs.le hqpos.le
  have hdisc_nonneg : 0 ≤ geometricDiscount s q :=
    book_geometricDiscount_nonneg hsq_nonneg
  have hupper : geometricDiscount s q ≤ 2 * (s * q) :=
    geometricDiscount_le_two_mul hsq_nonneg
  have hpow_le :
      Real.rpow (geometricDiscount s q) (2 / q) ≤
        Real.rpow (2 * (s * q)) (2 / q) :=
    Real.rpow_le_rpow hdisc_nonneg hupper (by positivity)
  have hsplit :
      Real.rpow (2 * (s * q)) (2 / q) =
        Real.rpow s (2 / q) * Real.rpow (2 * q) (2 / q) := by
    calc
      Real.rpow (2 * (s * q)) (2 / q) =
          Real.rpow (s * (2 * q)) (2 / q) := by
            ring_nf
      _ =
          Real.rpow s (2 / q) * Real.rpow (2 * q) (2 / q) := by
            simpa [Real.rpow_eq_pow] using
              Real.mul_rpow hs.le (by positivity : 0 ≤ 2 * q) (z := 2 / q)
  calc
    Real.rpow (geometricDiscount s q) (2 / q)
        ≤ Real.rpow (2 * (s * q)) (2 / q) := hpow_le
    _ = Real.rpow s (2 / q) * Real.rpow (2 * q) (2 / q) := hsplit
    _ ≤ Real.rpow s (2 / q) * Real.exp 4 := by
          exact mul_le_mul_of_nonneg_left
            (two_mul_self_rpow_two_div_le_exp_four hq)
            (Real.rpow_nonneg hs.le _)
    _ = Real.exp 4 * Real.rpow s (2 / q) := by ring

theorem one_half_le_log_three : (1 / 2 : ℝ) ≤ Real.log 3 := by
  have hexp_half_le_exp_one : Real.exp ((1 : ℝ) / 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by norm_num)
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
  have hlog_pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have h1x_pos : 0 < 1 + x := by linarith
  have hr_eq : r = (Real.exp x)⁻¹ := by
    dsimp [r, x]
    have hpow :
        Real.rpow (3 : ℝ) (-s / 2) =
          Real.exp (Real.log 3 * (-s / 2)) := by
      simpa [Real.rpow_eq_pow] using
        Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ)) (-s / 2)
    change
      Real.rpow (3 : ℝ) (-s / 2) =
        (Real.exp (s * Real.log 3 / 2))⁻¹
    rw [hpow]
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
  have hinv_le : (1 - r)⁻¹ ≤ (x / (1 + x))⁻¹ :=
    (inv_le_inv₀ hden_pos hx_div_pos).2 hden_lower
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

theorem inv_one_sub_rpow_three_neg_le_five_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ 5 * s⁻¹ := by
  let r₁ : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  let r₂ : ℝ := Real.rpow (3 : ℝ) (-s)
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : 1 < (3 : ℝ)) (by linarith : -s / 2 < 0)
  have hr₂_lt_one : r₂ < 1 := by
    dsimp [r₂]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : 1 < (3 : ℝ)) (by linarith : -s < 0)
  have hr_le : r₂ ≤ r₁ := by
    dsimp [r₁, r₂]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) (by linarith : -s ≤ -s / 2)
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

theorem inv_geometricDiscount_le_five_inv {s p : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) :
    (geometricDiscount s p)⁻¹ ≤ 5 * s⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdisc_one_pos : 0 < geometricDiscount s 1 := by
    exact book_geometricDiscount_pos (by simpa using hs)
  have hdisc_p_pos : 0 < geometricDiscount s p :=
    book_geometricDiscount_pos (mul_pos hs hp_pos)
  have hmono : geometricDiscount s 1 ≤ geometricDiscount s p := by
    unfold geometricDiscount
    have hpow :
        Real.rpow (3 : ℝ) (-s * p) ≤
          Real.rpow (3 : ℝ) (-s * 1) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
      nlinarith
    linarith
  calc
    (geometricDiscount s p)⁻¹ ≤ (geometricDiscount s 1)⁻¹ :=
      (inv_le_inv₀ hdisc_p_pos hdisc_one_pos).2 hmono
    _ ≤ 5 * s⁻¹ := by
      simpa [geometricDiscount] using
        inv_one_sub_rpow_three_neg_le_five_inv hs hs_le

theorem geometricDiscount_rpow_neg_two_div_le_twentyFive_mul {s p : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) :
    Real.rpow (geometricDiscount s p) (-2 / p) ≤
      25 * Real.rpow s (-2 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hdisc_p_pos : 0 < geometricDiscount s p :=
    book_geometricDiscount_pos (mul_pos hs hp_pos)
  have hinv_le : (geometricDiscount s p)⁻¹ ≤ 5 * s⁻¹ :=
    inv_geometricDiscount_le_five_inv hs hs_le hp
  have hinv_nonneg : 0 ≤ (geometricDiscount s p)⁻¹ :=
    inv_nonneg.mpr hdisc_p_pos.le
  have hfive_inv_nonneg : 0 ≤ 5 * s⁻¹ := by positivity
  have hpow_le :
      Real.rpow ((geometricDiscount s p)⁻¹) (2 / p) ≤
        Real.rpow (5 * s⁻¹) (2 / p) :=
    Real.rpow_le_rpow hinv_nonneg hinv_le (by positivity)
  have hleft :
      Real.rpow (geometricDiscount s p) (-2 / p) =
        Real.rpow ((geometricDiscount s p)⁻¹) (2 / p) := by
    have hneg : (-2 / p : ℝ) = -(2 / p) := by ring
    have h :=
      Real.rpow_neg_eq_inv_rpow (geometricDiscount s p) (2 / p)
    simpa [hneg, Real.rpow_eq_pow] using h
  have hsplit :
      Real.rpow (5 * s⁻¹) (2 / p) =
        Real.rpow (5 : ℝ) (2 / p) * Real.rpow s⁻¹ (2 / p) := by
    simpa [Real.rpow_eq_pow] using
      Real.mul_rpow (by norm_num : 0 ≤ (5 : ℝ)) (inv_nonneg.mpr hs.le)
        (z := 2 / p)
  have hexp_le : (2 / p : ℝ) ≤ 2 := by
    field_simp [hp_pos.ne']
    nlinarith
  have hfive_pow : Real.rpow (5 : ℝ) (2 / p) ≤ 25 := by
    calc
      Real.rpow (5 : ℝ) (2 / p) ≤ Real.rpow (5 : ℝ) 2 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hexp_le
      _ = 25 := by norm_num
  have hs_inv_rpow :
      Real.rpow s⁻¹ (2 / p) = Real.rpow s (-2 / p) := by
    have hneg : (-2 / p : ℝ) = -(2 / p) := by ring
    have h :=
      (Real.rpow_neg_eq_inv_rpow s (2 / p)).symm
    simpa [hneg, Real.rpow_eq_pow] using h
  calc
    Real.rpow (geometricDiscount s p) (-2 / p)
        = Real.rpow ((geometricDiscount s p)⁻¹) (2 / p) := hleft
    _ ≤ Real.rpow (5 * s⁻¹) (2 / p) := hpow_le
    _ = Real.rpow (5 : ℝ) (2 / p) * Real.rpow s⁻¹ (2 / p) := hsplit
    _ ≤ 25 * Real.rpow s⁻¹ (2 / p) := by
          exact mul_le_mul_of_nonneg_right hfive_pow
            (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _)
    _ = 25 * Real.rpow s (-2 / p) := by
          rw [hs_inv_rpow]

theorem geometricDiscount_change_exponent_factor_le {s p q : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) (hpq : p ≤ q) :
    Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p) ≤
      (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : 1 ≤ q := le_trans hp hpq
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnum :=
    geometricDiscount_rpow_two_div_le_exp_four_mul (s := s) (q := q) hs hq
  have hden :=
    geometricDiscount_rpow_neg_two_div_le_twentyFive_mul
      (s := s) (p := p) hs hs_le hp
  have hden_nonneg :
      0 ≤ Real.rpow (geometricDiscount s p) (-2 / p) :=
    Real.rpow_nonneg
      (book_geometricDiscount_nonneg (mul_nonneg hs.le hp_pos.le)) _
  have hnum_bound_nonneg :
      0 ≤ Real.exp 4 * Real.rpow s (2 / q) :=
    mul_nonneg (Real.exp_pos 4).le (Real.rpow_nonneg hs.le _)
  have hcombine :
      Real.rpow s (2 / q) * Real.rpow s (-2 / p) =
        Real.rpow s (2 / q - 2 / p) := by
    have h :
        Real.rpow s (2 / q + (-2 / p)) =
          Real.rpow s (2 / q) * Real.rpow s (-2 / p) := by
      simpa [Real.rpow_eq_pow] using Real.rpow_add hs (2 / q) (-2 / p)
    rw [← h]
    congr 1
    ring
  calc
    Real.rpow (geometricDiscount s q) (2 / q) *
        Real.rpow (geometricDiscount s p) (-2 / p)
        ≤ (Real.exp 4 * Real.rpow s (2 / q)) *
            (25 * Real.rpow s (-2 / p)) := by
          exact mul_le_mul hnum hden hden_nonneg hnum_bound_nonneg
    _ = (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) := by
          rw [show Real.exp 4 * Real.rpow s (2 / q) *
                (25 * Real.rpow s (-2 / p)) =
              25 * Real.exp 4 *
                (Real.rpow s (2 / q) * Real.rpow s (-2 / p)) by ring,
            hcombine]

end

end Ch02
end Book
end Homogenization
