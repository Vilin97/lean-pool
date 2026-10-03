/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.IterationCore

/-! # Iteration Constants -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators

noncomputable section

namespace SmallContrastAlgebraicDecay

open Section53.JUpperBoundCoarseFluctuations

/-!
# Constant selection for the small-contrast algebraic iteration
-/

/-- The lower scale used in the nonlinear iteration. -/
def threeQuarterScale (m : ℕ) : ℕ :=
  m - m / 4

theorem threeQuarterScale_lt_self {m : ℕ} (hm : 4 ≤ m) :
    threeQuarterScale m < m := by
  dsimp [threeQuarterScale]
  omega

theorem half_le_two_threeQuarterScale_sub (m : ℕ) :
    m / 2 ≤ 2 * threeQuarterScale m - m := by
  dsimp [threeQuarterScale]
  omega

theorem threeQuarterScale_decay_sq_le
    {α : ℝ} (hα_nonneg : 0 ≤ α) (m : ℕ) :
    (Real.rpow (3 : ℝ) (-α * (threeQuarterScale m : ℝ))) ^ (2 : ℕ) ≤
      Real.rpow (3 : ℝ) (-α * (m : ℝ)) *
        Real.rpow (3 : ℝ) (-α * ((m / 2 : ℕ) : ℝ)) := by
  let q := threeQuarterScale m
  have hgain_nat : m + m / 2 ≤ 2 * q := by
    dsimp [q, threeQuarterScale]
    omega
  have hgain_real : (m : ℝ) + ((m / 2 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast hgain_nat
  have hexp_le :
      -2 * α * (q : ℝ) ≤ -α * (m : ℝ) + -α * ((m / 2 : ℕ) : ℝ) := by
    nlinarith
  calc
    (Real.rpow (3 : ℝ) (-α * (threeQuarterScale m : ℝ))) ^ (2 : ℕ)
        = Real.rpow (3 : ℝ) (-2 * α * (q : ℝ)) := by
          dsimp [q]
          calc
            (Real.rpow (3 : ℝ) (-α * (threeQuarterScale m : ℝ))) ^ (2 : ℕ)
                = Real.rpow (3 : ℝ) (-α * (threeQuarterScale m : ℝ)) *
                    Real.rpow (3 : ℝ) (-α * (threeQuarterScale m : ℝ)) := by ring
            _ = Real.rpow (3 : ℝ)
                  (-α * (threeQuarterScale m : ℝ) +
                    -α * (threeQuarterScale m : ℝ)) := by
                exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                  (-α * (threeQuarterScale m : ℝ))
                  (-α * (threeQuarterScale m : ℝ))).symm
            _ = Real.rpow (3 : ℝ) (-2 * α * (threeQuarterScale m : ℝ)) := by
                ring_nf
    _ ≤ Real.rpow (3 : ℝ)
          (-α * (m : ℝ) + -α * ((m / 2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp_le
    _ = Real.rpow (3 : ℝ) (-α * (m : ℝ)) *
        Real.rpow (3 : ℝ) (-α * ((m / 2 : ℕ) : ℝ)) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 3)
          (-α * (m : ℝ)) (-α * ((m / 2 : ℕ) : ℝ))

theorem lagged_scale_window
    {L m : ℕ} (hL_pos : 0 < L) (hlarge : 8 * L + 4 ≤ m) :
    threeQuarterScale m < m - L ∧ m - L < m ∧
      L ≤ m - (m - L) ∧ m / 8 ≤ (m - L) - threeQuarterScale m := by
  dsimp [threeQuarterScale]
  omega

theorem scale_div_sixteen_le_nat_div_eight_cast {m : ℕ} (hm : 16 ≤ m) :
    (m : ℝ) / 16 ≤ ((m / 8 : ℕ) : ℝ) := by
  have hnat : m ≤ 16 * (m / 8) := by omega
  have hreal : (m : ℝ) ≤ 16 * ((m / 8 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  nlinarith

/-- There is a positive exponential rate compatible with a fixed contraction
and lag. -/
theorem exists_decay_rate_for_lag_contraction
    {L : ℕ} {θ α0 : ℝ}
    (hL_pos : 0 < L) (hθ_pos : 0 < θ) (hθ_lt_one : θ < 1)
    (hα0_pos : 0 < α0) :
    ∃ α : ℝ, 0 < α ∧ α ≤ α0 ∧
      θ * Real.rpow (3 : ℝ) (α * (L : ℝ)) < 1 := by
  let target : ℝ := (1 + θ) / (2 * θ)
  have htarget_pos : 0 < target := by
    dsimp [target]
    positivity
  have htarget_gt_one : 1 < target := by
    dsimp [target]
    rw [lt_div_iff₀ (by positivity : 0 < 2 * θ)]
    nlinarith
  let αlag : ℝ := Real.logb 3 target / (2 * (L : ℝ))
  have hαlag_pos : 0 < αlag := by
    dsimp [αlag]
    have hlogb_pos : 0 < Real.logb 3 target :=
      Real.logb_pos (by norm_num : (1 : ℝ) < 3) htarget_gt_one
    positivity
  let α : ℝ := min (α0 / 2) αlag
  have hα_pos : 0 < α := lt_min (by positivity) hαlag_pos
  have hα_le_α0 : α ≤ α0 := by
    have hhalf_le : α0 / 2 ≤ α0 := by nlinarith
    exact (min_le_left _ _).trans hhalf_le
  have hα_le_αlag : α ≤ αlag := min_le_right _ _
  have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
  have hαL_le : α * (L : ℝ) ≤ Real.logb 3 target / 2 := by
    have hL_pos_real : 0 < (L : ℝ) := by exact_mod_cast hL_pos
    calc
      α * (L : ℝ) ≤ αlag * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hα_le_αlag hL_nonneg
      _ = Real.logb 3 target / 2 := by
        dsimp [αlag]
        field_simp [hL_pos_real.ne']
  have hpow_le_target :
      Real.rpow (3 : ℝ) (α * (L : ℝ)) ≤ target := by
    have hpow_le_sqrt :
        Real.rpow (3 : ℝ) (α * (L : ℝ)) ≤
          Real.rpow (3 : ℝ) (Real.logb 3 target / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hαL_le
    have hsqrt_le_target :
        Real.rpow (3 : ℝ) (Real.logb 3 target / 2) ≤ target := by
      have hpow_nonneg :
          0 ≤ Real.rpow (3 : ℝ) (Real.logb 3 target / 2) :=
        Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
      have hsq_eq :
          (Real.rpow (3 : ℝ) (Real.logb 3 target / 2)) ^ (2 : ℕ) =
            target := by
        calc
          (Real.rpow (3 : ℝ) (Real.logb 3 target / 2)) ^ (2 : ℕ)
              = Real.rpow (3 : ℝ) (Real.logb 3 target / 2) *
                  Real.rpow (3 : ℝ) (Real.logb 3 target / 2) := by ring
          _ = Real.rpow (3 : ℝ)
                (Real.logb 3 target / 2 + Real.logb 3 target / 2) := by
              exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                (Real.logb 3 target / 2) (Real.logb 3 target / 2)).symm
          _ = Real.rpow (3 : ℝ) (Real.logb 3 target) := by ring_nf
          _ = target := by
              exact Real.rpow_logb (by norm_num : (0 : ℝ) < 3)
                (by norm_num : (3 : ℝ) ≠ 1) htarget_pos
      have htarget_one : 1 ≤ target := le_of_lt htarget_gt_one
      nlinarith
    exact hpow_le_sqrt.trans hsqrt_le_target
  refine ⟨α, hα_pos, hα_le_α0, ?_⟩
  calc
    θ * Real.rpow (3 : ℝ) (α * (L : ℝ)) ≤ θ * target :=
      mul_le_mul_of_nonneg_left hpow_le_target hθ_pos.le
    _ = (1 + θ) / 2 := by
      dsimp [target]
      field_simp [hθ_pos.ne']
    _ < 1 := by nlinarith

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
