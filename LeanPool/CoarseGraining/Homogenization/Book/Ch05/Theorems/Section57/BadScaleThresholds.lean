/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.DeterministicThresholds

/-! # Bad Scale Thresholds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Deterministic large-scale thresholds

These elementary real-variable lemmas discharge the side conditions in the
concrete bad-scale kernel once the bad scale is chosen above an explicit
deterministic threshold.
-/

noncomputable section

/-- If `q` is above the logarithmic threshold associated with a denominator
`D`, then the base-three tail parameter is at least one. -/
theorem one_le_rpow_three_linear_sub_div_of_log_bound
    {β O D q : ℝ}
    (hβ : 0 < β) (hD : 0 < D)
    (hq :
      (Real.log D + O * Real.log (3 : ℝ)) /
          (β * Real.log (3 : ℝ)) ≤ q) :
    1 ≤ ((3 : ℝ) ^ (β * q - O)) / D := by
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hden_pos : 0 < β * Real.log (3 : ℝ) := mul_pos hβ hlog3_pos
  have hmul :=
    mul_le_mul_of_nonneg_left hq hden_pos.le
  have hcancel :
      β * Real.log (3 : ℝ) *
          ((Real.log D + O * Real.log (3 : ℝ)) /
            (β * Real.log (3 : ℝ))) =
        Real.log D + O * Real.log (3 : ℝ) := by
    field_simp [hden_pos.ne']
  have hlog_le :
      Real.log D ≤ (β * q - O) * Real.log (3 : ℝ) := by
    rw [hcancel] at hmul
    nlinarith
  have hD_le_exp :
      D ≤ Real.exp ((β * q - O) * Real.log (3 : ℝ)) :=
    (Real.log_le_iff_le_exp hD).mp hlog_le
  have hrpow_eq :
      ((3 : ℝ) ^ (β * q - O)) =
        Real.exp ((β * q - O) * Real.log (3 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hD_le_pow : D ≤ ((3 : ℝ) ^ (β * q - O)) := by
    simpa [hrpow_eq] using hD_le_exp
  calc
    (1 : ℝ) = D / D := by field_simp [hD.ne']
    _ ≤ ((3 : ℝ) ^ (β * q - O)) / D :=
        div_le_div_of_nonneg_right hD_le_pow hD.le

/-- Natural-scale version of
`one_le_rpow_three_linear_sub_div_of_log_bound`. -/
theorem one_le_rpow_three_linear_sub_nat_div_of_log_bound
    {β O D : ℝ} {q : ℕ}
    (hβ : 0 < β) (hD : 0 < D)
    (hq :
      (Real.log D + O * Real.log (3 : ℝ)) /
          (β * Real.log (3 : ℝ)) ≤ (q : ℝ)) :
    1 ≤ ((3 : ℝ) ^ (β * (q : ℝ) - O)) / D :=
  one_le_rpow_three_linear_sub_div_of_log_bound
    (β := β) (O := O) (D := D) (q := (q : ℝ)) hβ hD hq

/-- A ceiling threshold is enough to make the base-three tail parameter at
least one. -/
theorem one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
    {β O D : ℝ} {q : ℕ}
    (hβ : 0 < β) (hD : 0 < D)
    (hq :
      Nat.ceil
          ((Real.log D + O * Real.log (3 : ℝ)) /
            (β * Real.log (3 : ℝ))) ≤ q) :
    1 ≤ ((3 : ℝ) ^ (β * (q : ℝ) - O)) / D := by
  have hceil :
      (Real.log D + O * Real.log (3 : ℝ)) /
          (β * Real.log (3 : ℝ)) ≤
        (Nat.ceil
          ((Real.log D + O * Real.log (3 : ℝ)) /
            (β * Real.log (3 : ℝ))) : ℝ) :=
    Nat.le_ceil _
  have hq_real :
      (Nat.ceil
          ((Real.log D + O * Real.log (3 : ℝ)) /
            (β * Real.log (3 : ℝ))) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq
  exact
    one_le_rpow_three_linear_sub_nat_div_of_log_bound
      (β := β) (O := O) (D := D) (q := q)
      hβ hD (hceil.trans hq_real)

/-- Once the scale is above the cutoff threshold, the crude-top branch is
deterministically empty. -/
theorem large_scale_cutoff_of_div_lt
    {L δ : ℝ} {q : ℕ}
    (hδ : 0 < δ) (hq : (L + 1) / δ < (q : ℝ)) :
    L + 1 < δ * (q : ℝ) := by
  have hmul := mul_lt_mul_of_pos_left hq hδ
  have hcancel : δ * ((L + 1) / δ) = L + 1 := by
    field_simp [hδ.ne']
  nlinarith

/-- Ceiling form of the large-scale cutoff. -/
theorem large_scale_cutoff_of_natCeil_add_one_le
    {L δ : ℝ} {q : ℕ}
    (hδ : 0 < δ)
    (hq : Nat.ceil ((L + 1) / δ + 1) ≤ q) :
    L + 1 < δ * (q : ℝ) := by
  have hceil :
      (L + 1) / δ + 1 ≤
        (Nat.ceil ((L + 1) / δ + 1) : ℝ) :=
    Nat.le_ceil _
  have hq_real :
      (Nat.ceil ((L + 1) / δ + 1) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hlt : (L + 1) / δ < (q : ℝ) := by
    linarith
  exact large_scale_cutoff_of_div_lt (L := L) (δ := δ) (q := q) hδ hlt

end

end Section57
end Ch05
end Book
end Homogenization
