/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Penultimate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Metric/sign dichotomy

The normalized algebraic kernel for draft Section 5 and Lean-plan step 10.
The proof uses only the four cross-color metric parameters, so its conclusion
applies uniformly to all four cross-color pairs.  The two boundary radicals
are retained as exact kernel inequalities.
-/

namespace LeanPool.Erdos132ConvexK3

private lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private lemma sqrt_thirty_nine_sq : (Real.sqrt 39) ^ 2 = 39 := by
  exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39)

private lemma five_thirds_lt_sqrt_three : (5 : ℝ) / 3 < Real.sqrt 3 := by
  have hs := sqrt_three_sq
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

private lemma three_halves_lt_sqrt_three : (3 : ℝ) / 2 < Real.sqrt 3 := by
  have hs := sqrt_three_sq
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

private lemma sqrt_three_lt_two : Real.sqrt 3 < (2 : ℝ) := by
  have hs := sqrt_three_sq
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

private lemma six_lt_sqrt_thirty_nine : (6 : ℝ) < Real.sqrt 39 := by
  have hs := sqrt_thirty_nine_sq
  have hs0 := Real.sqrt_nonneg (39 : ℝ)
  nlinarith

/-- First exact boundary constant in the short-sign regime. -/
theorem first_hard_constant_pos :
    0 < (3 * Real.sqrt 3 - 5) / 4 := by
  have hs := five_thirds_lt_sqrt_three
  linarith

/-- Second exact boundary constant in the long-sign regime. -/
theorem second_hard_constant_gt_nine_eighths :
    (9 : ℝ) / 8 < (4 * Real.sqrt 3 + Real.sqrt 39) / 8 := by
  have h3 := three_halves_lt_sqrt_three
  have h39 := six_lt_sqrt_thirty_nine
  linarith

/-- Failure of the desired metric inequality gives the strict numerator
comparison used by all three beta ranges. -/
theorem metric_failure_numerator_lt_majorant
    {β γ : ℝ} (hγ : 0 < γ) (hfailure : 1 + γ < 2 * β) :
    1 + 2 * γ ^ 2 - 3 * β ^ 2 < (1 - β) * (3 - 5 * β) := by
  have hgap : 0 < 2 * β - 1 := by linarith
  have hγgap : γ < 2 * β - 1 := by linarith
  have hsq : γ ^ 2 < (2 * β - 1) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hγgap) (add_pos_of_pos_of_nonneg hγ (le_of_lt hgap))]
  nlinarith

/-- AM-GM in polynomial form.  In the first beta range the single identity
`β²=1-4rp` already forces `2r+p>1`. -/
theorem amgm_two_r_add_p_gt_one
    {r p β : ℝ} (hr : 0 < r)
    (hβlo : (1 : ℝ) / 2 < β) (hβhi : β < (3 : ℝ) / 5)
    (hβsq : β ^ 2 = 1 - 4 * r * p) :
    1 < 2 * r + p := by
  have hβsq_lt : β ^ 2 < (1 : ℝ) / 2 := by
    nlinarith [mul_pos (sub_pos.mpr hβhi) (by linarith : 0 < (3 : ℝ) / 5 + β)]
  nlinarith [sq_nonneg (r - (1 : ℝ) / 4)]

/-- Exact rationalized inequality behind beta range `1/2<β<3/5`. -/
theorem range_one_exact_radical_bound
    {β : ℝ} (hβlo : (1 : ℝ) / 2 < β) (hβhi : β < (3 : ℝ) / 5) :
    (3 - 5 * β) / (1 + β) < Real.sqrt 3 / 2 - β := by
  have hconst := first_hard_constant_pos
  have hfactor : 0 < (β - (1 : ℝ) / 2) *
      ((7 : ℝ) / 2 + Real.sqrt 3 / 2 - β) := by
    apply mul_pos
    · linarith
    · have hs0 := Real.sqrt_nonneg (3 : ℝ)
      linarith
  have hpoly : 0 < Real.sqrt 3 / 2 - 3 +
      (Real.sqrt 3 / 2 + 4) * β - β ^ 2 := by
    nlinarith
  apply (div_lt_iff₀ (by linarith : 0 < 1 + β)).2
  nlinarith

private lemma normalized_height_lower
    {r h : ℝ} (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2) :
    Real.sqrt 3 / 2 ≤ h := by
  have hs := sqrt_three_sq
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  by_contra hnot
  have hhlt : h < Real.sqrt 3 / 2 := lt_of_not_ge hnot
  nlinarith [mul_nonneg (sub_nonneg.mpr hrhi) (by linarith : 0 ≤ r + (1 : ℝ) / 2),
    mul_pos (sub_pos.mpr hhlt) (by positivity : 0 < Real.sqrt 3 / 2 + h)]

/-- Beta range 1 (`1/2<β<3/5`).  The AM-GM consequence makes
`δ>p/2`; the exact first radical constant then closes the sign inequality. -/
theorem metric_dichotomy_range_one
    {r p β γ h k δ : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2) (hp : 0 < p)
    (hβlo : (1 : ℝ) / 2 < β) (hβhi : β < (3 : ℝ) / 5)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hγ : 0 < γ) (hfailure : 1 + γ < 2 * β)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hksq : k ^ 2 = 1 - (r + p) ^ 2)
    (hδ : 0 < δ) (hδdef : δ = h - k) :
    (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) < h - β := by
  have hNltM := metric_failure_numerator_lt_majorant hγ hfailure
  have hT : 1 < 2 * r + p :=
    amgm_two_r_add_p_gt_one hr hβlo hβhi hβsq
  have hh_lt_one : h < 1 := by
    nlinarith [sq_pos_of_pos hr]
  have hrp : 0 < r + p := by linarith
  have hk_lt_one : k < 1 := by
    nlinarith [sq_pos_of_pos hrp]
  have hsum_lt : h + k < 2 := by linarith
  have hδproduct : δ * (h + k) = p * (2 * r + p) := by
    rw [hδdef]
    nlinarith
  have hp_lt_twoδ : p < 2 * δ := by
    have hleft : 0 < δ * (2 - (h + k)) :=
      mul_pos hδ (by linarith)
    have hright : 0 < p * ((2 * r + p) - 1) :=
      mul_pos hp (by linarith)
    nlinarith
  have hMpos : 0 < (1 - β) * (3 - 5 * β) := by
    exact mul_pos (by linarith) (by linarith)
  have hdenδ : 0 < 4 * δ := by positivity
  have hdenp : 0 < 2 * p := by positivity
  have hfirst :
      (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) <
        ((1 - β) * (3 - 5 * β)) / (4 * δ) :=
    (div_lt_div_iff_of_pos_right hdenδ).2 hNltM
  have hsecond :
      ((1 - β) * (3 - 5 * β)) / (4 * δ) <
        ((1 - β) * (3 - 5 * β)) / (2 * p) := by
    apply div_lt_div_of_pos_left hMpos hdenp
    linarith
  have hfactor : (1 - β) * (1 + β) = 4 * r * p := by
    nlinarith
  have hfactor_div : (1 - β) / (2 * p) = (2 * r) / (1 + β) := by
    apply (div_eq_div_iff (by positivity) (by linarith)).2
    nlinarith [hfactor]
  have hidentity :
      ((1 - β) * (3 - 5 * β)) / (2 * p) =
        (2 * r) * ((3 - 5 * β) / (1 + β)) := by
    calc
      ((1 - β) * (3 - 5 * β)) / (2 * p) =
          ((1 - β) / (2 * p)) * (3 - 5 * β) := by ring
      _ = ((2 * r) / (1 + β)) * (3 - 5 * β) := by rw [hfactor_div]
      _ = (2 * r) * ((3 - 5 * β) / (1 + β)) := by ring
  have hratio_pos : 0 < (3 - 5 * β) / (1 + β) :=
    div_pos (by linarith) (by linarith)
  have hscale :
      (2 * r) * ((3 - 5 * β) / (1 + β)) ≤
        (3 - 5 * β) / (1 + β) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 2 * r) (le_of_lt hratio_pos)]
  have hradical := range_one_exact_radical_bound hβlo hβhi
  have hheight := normalized_height_lower hr hrhi hh hhsq
  calc
    (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ)
        < ((1 - β) * (3 - 5 * β)) / (4 * δ) := hfirst
    _ < ((1 - β) * (3 - 5 * β)) / (2 * p) := hsecond
    _ = (2 * r) * ((3 - 5 * β) / (1 + β)) := hidentity
    _ ≤ (3 - 5 * β) / (1 + β) := hscale
    _ < Real.sqrt 3 / 2 - β := hradical
    _ ≤ h - β := by linarith

private lemma normalized_beta_lt_one
    {r p β γ : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hγ : 0 < γ) (hfailure : 1 + γ < 2 * β) :
    β < 1 := by
  have hβpos : 0 < β := by linarith
  have hprod : 0 < 4 * r * p := by positivity
  nlinarith

/-- Beta range 2 (`3/5≤β≤h`).  Here the majorant is nonpositive, so its
strict numerator bound immediately has the required sign. -/
theorem metric_dichotomy_range_two
    {r p β γ h δ : ℝ}
    (hr : 0 < r) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hγ : 0 < γ) (hfailure : 1 + γ < 2 * β)
    (hβlo : (3 : ℝ) / 5 ≤ β) (hβh : β ≤ h)
    (hδ : 0 < δ) :
    (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) < h - β := by
  have hβlt1 := normalized_beta_lt_one hr hp hβsq hγ hfailure
  have hNltM := metric_failure_numerator_lt_majorant hγ hfailure
  have hMle : (1 - β) * (3 - 5 * β) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hNneg : 1 + 2 * γ ^ 2 - 3 * β ^ 2 < 0 :=
    lt_of_lt_of_le hNltM hMle
  have hquotneg :
      (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) < 0 :=
    div_neg_of_neg_of_pos hNneg (by positivity)
  linarith

private lemma normalized_k_lower
    {r p k : ℝ} (hrhi : r ≤ (1 : ℝ) / 2)
    (hp : 0 < p) (hpquarter : p < r / 4)
    (hk : 0 < k) (hksq : k ^ 2 = 1 - (r + p) ^ 2) :
    Real.sqrt 39 / 8 < k := by
  have hrp : 0 < r + p := by linarith
  have hrp_hi : r + p < (5 : ℝ) / 8 := by linarith
  have hs := sqrt_thirty_nine_sq
  have hs0 := Real.sqrt_nonneg (39 : ℝ)
  by_contra hnot
  have hk_le : k ≤ Real.sqrt 39 / 8 := le_of_not_gt hnot
  have hsq_rp : (r + p) ^ 2 < ((5 : ℝ) / 8) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hrp_hi) (by linarith : 0 < (5 : ℝ) / 8 + (r + p))]
  have hsq_k : k ^ 2 ≤ (Real.sqrt 39 / 8) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk_le)
      (by positivity : 0 ≤ Real.sqrt 39 / 8 + k)]
  nlinarith

private lemma inverse_sqrt_three_bound :
    1 / Real.sqrt 3 < 5 * Real.sqrt 3 / 2 - 3 := by
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply (div_lt_iff₀ hspos).2
  have hs := sqrt_three_sq
  have hslt := sqrt_three_lt_two
  nlinarith

private lemma normalized_height_plus_k_gt
    {r p β h k : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hk : 0 < k) (hksq : k ^ 2 = 1 - (r + p) ^ 2)
    (hβh : h < β) :
    2 * r + p < h + k := by
  have hheight := normalized_height_lower hr hrhi hh hhsq
  have hβhprod : 0 < (β - h) * (β + h) :=
    mul_pos (sub_pos.mpr hβh) (by linarith)
  have hpquarter : p < r / 4 := by
    nlinarith
  have hkbound := normalized_k_lower hrhi hp hpquarter hk hksq
  have hTlt : 2 * r + p < (9 : ℝ) / 8 := by
    linarith
  have hsumRadical :
      (4 * Real.sqrt 3 + Real.sqrt 39) / 8 < h + k := by
    linarith
  have hhard := second_hard_constant_gt_nine_eighths
  linarith

private lemma normalized_delta_lt_p
    {r p β h k δ : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hk : 0 < k) (hksq : k ^ 2 = 1 - (r + p) ^ 2)
    (hδdef : δ = h - k) (hβh : h < β) :
    δ < p := by
  have hTsum :=
    normalized_height_plus_k_gt hr hrhi hp hβsq hh hhsq hk hksq hβh
  have hδproduct : δ * (h + k) = p * (2 * r + p) := by
    rw [hδdef]
    nlinarith
  have hsumpos : 0 < h + k := by linarith
  by_contra hnot
  have hpδ : p ≤ δ := le_of_not_gt hnot
  have hgap1 : 0 < p * ((h + k) - (2 * r + p)) :=
    mul_pos hp (by linarith)
  have hgap2 : 0 ≤ (δ - p) * (h + k) :=
    mul_nonneg (sub_nonneg.mpr hpδ) (le_of_lt hsumpos)
  nlinarith

private lemma normalized_ratio_lt_five_beta_sub_three
    {r β h : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2)
    (hβlt1 : β < 1) (hh : 0 < h) (hβh : h < β)
    (hheight : Real.sqrt 3 / 2 ≤ h) :
    ((1 + β) * r) / (β + h) < 5 * β - 3 := by
  have hnumLtOne : (1 + β) * r < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hβlt1) hr]
  have hdenSqrt : Real.sqrt 3 < β + h := by
    linarith
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hratioInv :
      ((1 + β) * r) / (β + h) < 1 / Real.sqrt 3 := by
    calc
      ((1 + β) * r) / (β + h) < 1 / (β + h) :=
        (div_lt_div_iff_of_pos_right (by linarith)).2 hnumLtOne
      _ < 1 / Real.sqrt 3 := one_div_lt_one_div_of_lt hspos hdenSqrt
  have hinv := inverse_sqrt_three_bound
  have hconstantBeta : 5 * Real.sqrt 3 / 2 - 3 < 5 * β - 3 := by
    linarith
  exact hratioInv.trans (hinv.trans hconstantBeta)

private lemma normalized_beta_height_difference
    {r p β h : ℝ}
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2) (hβh : h < β) :
    β - h = r * (r - 4 * p) / (β + h) := by
  have hdiffIdentity :
      (β - h) * (β + h) = r * (r - 4 * p) := by
    nlinarith
  have hden : 0 < β + h := by linarith
  apply (eq_div_iff (ne_of_gt hden)).2
  exact hdiffIdentity

private lemma normalized_range_three_core
    {r p β h δ : ℝ}
    (hr : 0 < r) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hβh : h < β) (hβlt1 : β < 1) (hδltp : δ < p)
    (hratio : ((1 + β) * r) / (β + h) < 5 * β - 3) :
    4 * δ * (β - h) < -((1 - β) * (3 - 5 * β)) := by
  have hdiffDiv := normalized_beta_height_difference hβsq hh hhsq hβh
  have hden : 0 < β + h := by linarith
  have hfirstCore : 4 * δ * (β - h) < 4 * p * (β - h) := by
    nlinarith [mul_pos (sub_pos.mpr hδltp) (sub_pos.mpr hβh)]
  have hinner :
      r * (r - 4 * p) / (β + h) < r * r / (β + h) := by
    apply (div_lt_div_iff_of_pos_right hden).2
    have h4rp : 0 < 4 * r * p := by positivity
    calc
      r * (r - 4 * p) = r * r - 4 * r * p := by ring
      _ < r * r := by linarith
  have hsecondCore :
      4 * p * (r * (r - 4 * p) / (β + h)) <
        4 * p * (r * r / (β + h)) :=
    (mul_lt_mul_iff_of_pos_left (by positivity : 0 < 4 * p)).2 hinner
  have hfactor : (1 - β) * (1 + β) = 4 * r * p := by
    calc
      (1 - β) * (1 + β) = 1 - β ^ 2 := by ring
      _ = 4 * r * p := by linarith
  have hnumIdentity :
      4 * p * r * r = (1 - β) * (1 + β) * r := by
    calc
      4 * p * r * r = (4 * r * p) * r := by ring
      _ = ((1 - β) * (1 + β)) * r := by rw [← hfactor]
      _ = (1 - β) * (1 + β) * r := by ring
  have hthirdCore :
      4 * p * (r * r / (β + h)) =
        (1 - β) * (((1 + β) * r) / (β + h)) := by
    calc
      4 * p * (r * r / (β + h)) = (4 * p * r * r) / (β + h) := by ring
      _ = ((1 - β) * (1 + β) * r) / (β + h) := by rw [hnumIdentity]
      _ = (1 - β) * (((1 + β) * r) / (β + h)) := by ring
  have hfourthCore :
      (1 - β) * (((1 + β) * r) / (β + h)) <
        (1 - β) * (5 * β - 3) :=
    (mul_lt_mul_iff_of_pos_left (sub_pos.mpr hβlt1)).2 hratio
  calc
    4 * δ * (β - h) < 4 * p * (β - h) := hfirstCore
    _ = 4 * p * (r * (r - 4 * p) / (β + h)) := by rw [hdiffDiv]
    _ < 4 * p * (r * r / (β + h)) := hsecondCore
    _ = (1 - β) * (((1 + β) * r) / (β + h)) := hthirdCore
    _ < (1 - β) * (5 * β - 3) := hfourthCore
    _ = -((1 - β) * (3 - 5 * β)) := by ring

/-- Beta range 3 (`h<β`).  The identity `β²-h²=r(r-4p)` gives `p<r/4`.
The exact second radical constant proves `δ<p`; the remaining ratio estimate
then reverses the negative majorant with room to spare. -/
theorem metric_dichotomy_range_three
    {r p β γ h k δ : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p)
    (hγ : 0 < γ) (hfailure : 1 + γ < 2 * β)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hk : 0 < k) (hksq : k ^ 2 = 1 - (r + p) ^ 2)
    (hδ : 0 < δ) (hδdef : δ = h - k)
    (hβh : h < β) :
    (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) < h - β := by
  have hβpos : 0 < β := by linarith
  have hβlt1 := normalized_beta_lt_one hr hp hβsq hγ hfailure
  have hNltM := metric_failure_numerator_lt_majorant hγ hfailure
  have hheight := normalized_height_lower hr hrhi hh hhsq
  have hδltp :=
    normalized_delta_lt_p hr hrhi hp hβsq hh hhsq hk hksq hδdef hβh
  have hratio :=
    normalized_ratio_lt_five_beta_sub_three hr hrhi hβlt1 hh hβh hheight
  have hcore :=
    normalized_range_three_core hr hp hβsq hh hhsq hβh hβlt1 hδltp hratio
  apply (div_lt_iff₀ (by positivity : 0 < 4 * δ)).2
  nlinarith

/-- Metric/sign dichotomy for one arbitrary full two-rung normalization.
Equality belongs to the length branch; only strict failure enters the three
beta regimes.  Since no earlier cross-color hypothesis occurs, this one
theorem applies unchanged to all four `AA`, `AB`, `BA`, and `BB` branches
from draft (4.2). -/
theorem metric_sign_dichotomy
    {r p β γ h k δ : ℝ}
    (hr : 0 < r) (hrhi : r ≤ (1 : ℝ) / 2) (hp : 0 < p)
    (hβsq : β ^ 2 = 1 - 4 * r * p) (hγ : 0 < γ)
    (hh : 0 < h) (hhsq : h ^ 2 = 1 - r ^ 2)
    (hk : 0 < k) (hksq : k ^ 2 = 1 - (r + p) ^ 2)
    (hδ : 0 < δ) (hδdef : δ = h - k) :
    2 * β ≤ 1 + γ ∨
      (1 + 2 * γ ^ 2 - 3 * β ^ 2) / (4 * δ) < h - β := by
  by_cases hlength : 2 * β ≤ 1 + γ
  · exact Or.inl hlength
  · right
    have hfailure : 1 + γ < 2 * β := lt_of_not_ge hlength
    have hβlo : (1 : ℝ) / 2 < β := by linarith
    by_cases hβfirst : β < (3 : ℝ) / 5
    · exact metric_dichotomy_range_one hr hrhi hp hβlo hβfirst hβsq
        hγ hfailure hh hhsq hksq hδ hδdef
    · have hβthree_fifths : (3 : ℝ) / 5 ≤ β := le_of_not_gt hβfirst
      by_cases hβh : β ≤ h
      · exact metric_dichotomy_range_two hr hp hβsq hγ hfailure
          hβthree_fifths hβh hδ
      · exact metric_dichotomy_range_three hr hrhi hp hβsq hγ hfailure
          hh hhsq hk hksq hδ hδdef (lt_of_not_ge hβh)

/-- The equality boundary belongs to the non-strict long regime. -/
theorem metric_equality_routes_long
    {d₁ d₂ d₃ : ℝ} (heq : d₁ + d₃ = 2 * d₂) :
    2 * d₂ ≤ d₁ + d₃ := by
  linarith

/-- The exact equality boundary is assigned to the long/counting regime:
strict edge-diagonal separation then forces the second center beyond `d₂`. -/
theorem metric_equality_forces_long_second_center
    {d₁ d₂ d₃ q : ℝ}
    (heq : d₁ + d₃ = 2 * d₂)
    (hED : d₁ + d₃ < q + d₂) :
    d₂ < q := by
  have hlong := metric_equality_routes_long heq
  linarith

end LeanPool.Erdos132ConvexK3
