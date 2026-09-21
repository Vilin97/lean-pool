/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries

/-! # Constants -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: Coefficients

Coefficient absorption and large-scale root coefficients.
-/

noncomputable def section52LargeScalarAbsorptionConst (d : ℕ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
    (20 * (2 * (d : ℝ)) * ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ)) +
      40 * (2 * (d : ℝ)) * Ch04.rosenthalBennettIntegralConst *
        Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ)))

theorem section52LargeScalarAbsorptionConst_nonneg (d : ℕ) :
    0 ≤ section52LargeScalarAbsorptionConst d := by
  unfold section52LargeScalarAbsorptionConst
  have hRB_nonneg : 0 ≤ Ch04.rosenthalBennettIntegralConst := by
    unfold Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  positivity

theorem section52_rosenthalDescendantsAtScaleLpConst_zero_le_color_mul_xi
    {d ξ : ℕ} (hξ : 1 ≤ (ξ : ℝ)) :
    Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ ≤
      2 * (ξ : ℝ) * ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ)) := by
  let A : ℝ := ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))
  have hξ_pos : 0 < (ξ : ℝ) := lt_of_lt_of_le zero_lt_one hξ
  have hA_pos_nat : 0 < (scaleColorPeriod 0) ^ d :=
    pow_pos (scaleColorPeriod_pos 0) d
  have hA_ge_one_nat : 1 ≤ (scaleColorPeriod 0) ^ d :=
    Nat.succ_le_of_lt hA_pos_nat
  have hA_ge_one : (1 : ℝ) ≤ A := by
    dsimp [A]
    exact_mod_cast hA_ge_one_nat
  have hexp_le_one : 1 - 1 / (ξ : ℝ) ≤ 1 := by
    have hnonneg : 0 ≤ 1 / (ξ : ℝ) := by positivity
    linarith
  have hpow_le :
      A ^ (1 - 1 / (ξ : ℝ)) ≤ A := by
    calc
      A ^ (1 - 1 / (ξ : ℝ)) ≤ A ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA_ge_one hexp_le_one
      _ = A := by simp
  unfold Ch04.rosenthalDescendantsAtScaleLpConst
  dsimp [A] at hpow_le ⊢
  exact mul_le_mul_of_nonneg_left hpow_le (by positivity)

theorem section52_rosenthalDescendantsAtScaleSqrtConst_zero_le_color_mul_xi
    {d ξ : ℕ} (hξ : 1 ≤ (ξ : ℝ)) :
    Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ ≤
      4 * Ch04.rosenthalBennettIntegralConst *
        Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ)) * (ξ : ℝ) := by
  let A : ℝ := ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))
  have hξ_nonneg : 0 ≤ (ξ : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ 1) hξ
  have hsqrt_ξ_le : Real.sqrt (ξ : ℝ) ≤ (ξ : ℝ) := by
    rw [Real.sqrt_le_left hξ_nonneg]
    nlinarith [hξ]
  have hRB_nonneg : 0 ≤ Ch04.rosenthalBennettIntegralConst := by
    unfold Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hleft_nonneg :
      0 ≤ 4 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A := by
    positivity
  unfold Ch04.rosenthalDescendantsAtScaleSqrtConst
  dsimp [A] at hsqrt_ξ_le hleft_nonneg ⊢
  calc
    4 * Ch04.rosenthalBennettIntegralConst *
        (Real.sqrt (ξ : ℝ) *
          Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))) =
        (4 * Ch04.rosenthalBennettIntegralConst *
          Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))) *
          Real.sqrt (ξ : ℝ) := by
        ring
    _ ≤
        (4 * Ch04.rosenthalBennettIntegralConst *
          Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))) *
          (ξ : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt_ξ_le hleft_nonneg
    _ =
      4 * Ch04.rosenthalBennettIntegralConst *
        Real.sqrt ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ)) * (ξ : ℝ) := by
        ring

theorem section52LargeScalarAbsorptionConst_absorbs
    {d ξ : ℕ} [NeZero d] {s : ℝ}
    (hξ_one : 1 ≤ (ξ : ℝ)) (hξ_two : (2 : ℝ) ≤ (ξ : ℝ))
    (hs : 0 ≤ s) (hs_lt_one : s < 1)
    (hlargeGap : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) :
    (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
          (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹) ≤
      section52LargeScalarAbsorptionConst d *
        ((ξ : ℝ) *
          ((((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s)⁻¹)) := by
  let A : ℝ := ((((scaleColorPeriod 0) ^ d : ℕ) : ℝ))
  let B : ℝ := 2 * (d : ℝ)
  let δ : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hd_nonneg : 0 ≤ (d : ℝ) := hd_pos.le
  have hd_ge_one : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne d)))
  have hB_ge_one : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB_nonneg : 0 ≤ B := le_trans (by norm_num : (0 : ℝ) ≤ 1) hB_ge_one
  have hξ_nonneg : 0 ≤ (ξ : ℝ) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) hξ_one
  have hδ_pos : 0 < δ := by
    simpa [δ] using hlargeGap
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ_pos.le
  have hLpGap_pos : 0 < (d : ℝ) - s := by
    linarith
  have hLpGap_le_B : (d : ℝ) - s ≤ B := by
    dsimp [B]
    nlinarith
  have hdiv_le_d : (d : ℝ) / (ξ : ℝ) ≤ (d : ℝ) := by
    have h := div_le_div_of_nonneg_left hd_nonneg (by norm_num : (0 : ℝ) < 1) hξ_one
    simpa using h
  have hδ_le_B : δ ≤ B := by
    dsimp [δ, B]
    nlinarith
  have hdiv_le_half : (d : ℝ) / (ξ : ℝ) ≤ (d : ℝ) / 2 := by
    exact div_le_div_of_nonneg_left hd_nonneg (by norm_num : (0 : ℝ) < 2) hξ_two
  have hδ_le_LpGap : δ ≤ (d : ℝ) - s := by
    dsimp [δ]
    linarith
  have hdisc_s_nonneg : 0 ≤ geometricDiscount s 1 :=
    geometricDiscount_nonneg (by simpa using hs)
  have hdisc_s_le_one : geometricDiscount s 1 ≤ 1 :=
    geometricDiscount_one_le_one s
  have hdisc_lp_pos : 0 < geometricDiscount ((d : ℝ) - s) 1 :=
    geometricDiscount_pos (by simpa using hLpGap_pos)
  have hinv_lp_nonneg : 0 ≤ (geometricDiscount ((d : ℝ) - s) 1)⁻¹ :=
    inv_nonneg.mpr hdisc_lp_pos.le
  have hinv_lp_raw :
      (geometricDiscount ((d : ℝ) - s) 1)⁻¹ ≤
        5 * B * (((d : ℝ) - s)⁻¹) :=
    inv_geometricDiscount_one_le_five_mul_upper_mul_inv
      hLpGap_pos hLpGap_le_B hB_ge_one
  have hLpGap_inv_le_delta_inv : ((d : ℝ) - s)⁻¹ ≤ δ⁻¹ :=
    (inv_le_inv₀ hLpGap_pos hδ_pos).2 hδ_le_LpGap
  have hinv_lp :
      (geometricDiscount ((d : ℝ) - s) 1)⁻¹ ≤ 5 * B * δ⁻¹ := by
    calc
      (geometricDiscount ((d : ℝ) - s) 1)⁻¹ ≤
          5 * B * (((d : ℝ) - s)⁻¹) := hinv_lp_raw
      _ ≤ 5 * B * δ⁻¹ := by
          exact mul_le_mul_of_nonneg_left hLpGap_inv_le_delta_inv
            (by positivity)
  have hdisc_delta_pos : 0 < geometricDiscount δ 1 :=
    geometricDiscount_pos (by simpa using hδ_pos)
  have hinv_delta_nonneg : 0 ≤ (geometricDiscount δ 1)⁻¹ :=
    inv_nonneg.mpr hdisc_delta_pos.le
  have hinv_delta :
      (geometricDiscount δ 1)⁻¹ ≤ 5 * B * δ⁻¹ :=
    inv_geometricDiscount_one_le_five_mul_upper_mul_inv hδ_pos hδ_le_B hB_ge_one
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.zero_le ((scaleColorPeriod 0) ^ d)
  have hsqrtA_nonneg : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hRB_nonneg : 0 ≤ Ch04.rosenthalBennettIntegralConst := by
    unfold Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  have hLp_const :=
    section52_rosenthalDescendantsAtScaleLpConst_zero_le_color_mul_xi
      (d := d) (ξ := ξ) hξ_one
  have hTwoLp_const :
      2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ ≤
        4 * A * (ξ : ℝ) := by
    calc
      2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ ≤
          2 * (2 * (ξ : ℝ) * A) :=
          mul_le_mul_of_nonneg_left (by simpa [A] using hLp_const)
            (by norm_num)
      _ = 4 * A * (ξ : ℝ) := by ring
  have hSqrt_const :=
    section52_rosenthalDescendantsAtScaleSqrtConst_zero_le_color_mul_xi
      (d := d) (ξ := ξ) hξ_one
  have hTwoSqrt_const :
      2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ ≤
        8 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A * (ξ : ℝ) := by
    calc
      2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ ≤
          2 * (4 * Ch04.rosenthalBennettIntegralConst *
            Real.sqrt A * (ξ : ℝ)) :=
          mul_le_mul_of_nonneg_left (by simpa [A] using hSqrt_const)
            (by norm_num)
      _ = 8 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A * (ξ : ℝ) := by
          ring
  have hLp_factor :
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ) *
          geometricDiscount s 1 ≤
        (4 * A * (ξ : ℝ)) * 1 :=
    mul_le_mul hTwoLp_const hdisc_s_le_one hdisc_s_nonneg
      (by positivity)
  have hLp_factor_nonneg : 0 ≤ (4 * A * (ξ : ℝ)) * 1 := by
    positivity
  have hLp_term :
      ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ) *
          geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ ≤
        20 * B * A * ((ξ : ℝ) * δ⁻¹) := by
    calc
      ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ) *
          geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ ≤
        ((4 * A * (ξ : ℝ)) * 1) * (5 * B * δ⁻¹) :=
          mul_le_mul hLp_factor hinv_lp hinv_lp_nonneg hLp_factor_nonneg
      _ = 20 * B * A * ((ξ : ℝ) * δ⁻¹) := by ring
  have hSqrt_factor :
      (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ) *
          geometricDiscount s 1 ≤
        (8 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A * (ξ : ℝ)) * 1 :=
    mul_le_mul hTwoSqrt_const hdisc_s_le_one hdisc_s_nonneg
      (by positivity)
  have hSqrt_factor_nonneg :
      0 ≤ (8 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A * (ξ : ℝ)) * 1 := by
    positivity
  have hSqrt_term :
      ((2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ) *
          geometricDiscount s 1) *
          (geometricDiscount δ 1)⁻¹ ≤
        40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A *
          ((ξ : ℝ) * δ⁻¹) := by
    calc
      ((2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ) *
          geometricDiscount s 1) *
          (geometricDiscount δ 1)⁻¹ ≤
        ((8 * Ch04.rosenthalBennettIntegralConst * Real.sqrt A * (ξ : ℝ)) * 1) *
          (5 * B * δ⁻¹) :=
          mul_le_mul hSqrt_factor hinv_delta hinv_delta_nonneg hSqrt_factor_nonneg
      _ = 40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A *
          ((ξ : ℝ) * δ⁻¹) := by ring
  have hcomponent :
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
            geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
            geometricDiscount s 1) *
          (geometricDiscount δ 1)⁻¹ ≤
        (20 * B * A +
          40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A) *
          ((ξ : ℝ) * δ⁻¹) := by
    calc
      (2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
            geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
            geometricDiscount s 1) *
          (geometricDiscount δ 1)⁻¹ =
        ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ) *
            geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        ((2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ) *
            geometricDiscount s 1) *
          (geometricDiscount δ 1)⁻¹ := by ring
      _ ≤
        20 * B * A * ((ξ : ℝ) * δ⁻¹) +
          40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A *
            ((ξ : ℝ) * δ⁻¹) :=
          add_le_add hLp_term hSqrt_term
      _ =
        (20 * B * A +
          40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A) *
          ((ξ : ℝ) * δ⁻¹) := by ring
  have hentry_nonneg :
      0 ≤ (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) := by
    positivity
  calc
    (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
          (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) 1)⁻¹) =
      (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
          (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
              geometricDiscount s 1) *
            (geometricDiscount δ 1)⁻¹) := by
        simp [δ]
    _ ≤
      (Fintype.card (Fin d) : ℝ) * (Fintype.card (Fin d) : ℝ) *
        ((20 * B * A +
          40 * B * Ch04.rosenthalBennettIntegralConst * Real.sqrt A) *
          ((ξ : ℝ) * δ⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hcomponent hentry_nonneg
    _ =
      section52LargeScalarAbsorptionConst d *
        ((ξ : ℝ) *
          ((((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s)⁻¹)) := by
        simp [section52LargeScalarAbsorptionConst, A, B, δ]
        ring

/-- The displayed Section 5.2 positive-excess coefficient is nonnegative. -/
theorem section52MomentBoundCoeff_nonneg
    {d ξ m : ℕ} {C s : ℝ}
    (hC : 0 ≤ C)
    (hDenom : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) :
    0 ≤ section52MomentBoundCoeff d ξ C s m := by
  unfold section52MomentBoundCoeff
  have hxi_nonneg : 0 ≤ (ξ : ℝ) := by exact_mod_cast Nat.zero_le ξ
  exact mul_nonneg
    (div_nonneg (mul_nonneg hC hxi_nonneg) hDenom.le)
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)

/-- The displayed Section 5.2 `widetildeTheta` error coefficient is
nonnegative. -/
theorem section52WidetildeThetaErrorCoeff_nonneg
    {d ξ m : ℕ} {C sMin : ℝ}
    (hC : 0 ≤ C) :
    0 ≤ section52WidetildeThetaErrorCoeff d ξ C sMin m := by
  unfold section52WidetildeThetaErrorCoeff
  exact mul_nonneg
    (mul_nonneg hC (sq_nonneg (ξ : ℝ)))
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)

/-- A displayed Section 5.2 positive-excess coefficient is bounded by the
common `widetildeTheta` scale whenever its exponent is at least the common
minimum exponent. -/
theorem section52MomentBoundCoeff_le_common_scale
    {d ξ m : ℕ} {C s sMin : ℝ}
    (hξ : 1 ≤ ξ)
    (hC : 0 ≤ C)
    (hDenom : 0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s)
    (hsMin_le : sMin ≤ s) :
    section52MomentBoundCoeff d ξ C s m ≤
      (C / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s)) * (ξ : ℝ) ^ 2 *
        Real.rpow (3 : ℝ) (-(sMin - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
  unfold section52MomentBoundCoeff
  let D : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s
  let X : ℝ := (ξ : ℝ)
  let scale : ℝ := Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  let commonScale : ℝ :=
    Real.rpow (3 : ℝ) (-(sMin - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  have hDpos : 0 < D := by simpa [D] using hDenom
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact_mod_cast Nat.zero_le ξ
  have hX_one : 1 ≤ X := by
    dsimp [X]
    exact_mod_cast hξ
  have hX_le_sq : X ≤ X ^ 2 := by
    calc
      X = X * 1 := by ring
      _ ≤ X * X := mul_le_mul_of_nonneg_left hX_one hX_nonneg
      _ = X ^ 2 := by ring
  have hratio_nonneg : 0 ≤ C / D := div_nonneg hC hDpos.le
  have hscale_nonneg : 0 ≤ scale :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hscale_le : scale ≤ commonScale := by
    have hExp :
        -(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ) ≤
          -(sMin - (d : ℝ) / (ξ : ℝ)) * (m : ℝ) := by
      have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      have hneg :
          -(s - (d : ℝ) / (ξ : ℝ)) ≤
            -(sMin - (d : ℝ) / (ξ : ℝ)) := by
        linarith
      exact mul_le_mul_of_nonneg_right hneg hm_nonneg
    simpa [scale, commonScale] using
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hExp
  calc
    C * X / D * scale =
        (C / D) * X * scale := by ring
    _ ≤ (C / D) * X ^ 2 * scale := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hX_le_sq hratio_nonneg)
        hscale_nonneg
    _ ≤ (C / D) * X ^ 2 * commonScale := by
      exact mul_le_mul_of_nonneg_left hscale_le
        (mul_nonneg hratio_nonneg (sq_nonneg X))
    _ =
        (C / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s)) * (ξ : ℝ) ^ 2 *
          Real.rpow (3 : ℝ) (-(sMin - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
      simp [D, X, commonScale]

/-- The product of the two displayed Section 5.2 positive-excess coefficients
is also bounded by the common `widetildeTheta` scale. -/
theorem section52MomentBoundCoeff_mul_le_common_scale
    {d ξ m : ℕ} {CUpper CLower sUpper sLower : ℝ}
    (hCUpper : 0 ≤ CUpper)
    (hCLower : 0 ≤ CLower)
    (hsUpper_gt : (d : ℝ) / (ξ : ℝ) < sUpper)
    (hsLower_gt : (d : ℝ) / (ξ : ℝ) < sLower)
    (hUpperDenom :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper)
    (hLowerDenom :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower) :
    section52MomentBoundCoeff d ξ CUpper sUpper m *
        section52MomentBoundCoeff d ξ CLower sLower m ≤
      (CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper) *
          (CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower))) *
        (ξ : ℝ) ^ 2 *
          Real.rpow (3 : ℝ)
            (-(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
  unfold section52MomentBoundCoeff
  let DU : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper
  let DL : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower
  let X : ℝ := (ξ : ℝ)
  let eU : ℝ := -(sUpper - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)
  let eL : ℝ := -(sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)
  let eMin : ℝ := -(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)
  have hDUpos : 0 < DU := by simpa [DU] using hUpperDenom
  have hDLpos : 0 < DL := by simpa [DL] using hLowerDenom
  have hratio_nonneg :
      0 ≤ CUpper / DU * (CLower / DL) :=
    mul_nonneg (div_nonneg hCUpper hDUpos.le) (div_nonneg hCLower hDLpos.le)
  have hscale_prod_eq :
      Real.rpow (3 : ℝ) eU * Real.rpow (3 : ℝ) eL =
        Real.rpow (3 : ℝ) (eU + eL) :=
    (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) eU eL).symm
  have hExp : eU + eL ≤ eMin := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hbeta_le_sum :
        min sUpper sLower - (d : ℝ) / (ξ : ℝ) ≤
          (sUpper - (d : ℝ) / (ξ : ℝ)) +
            (sLower - (d : ℝ) / (ξ : ℝ)) := by
      have hbeta_le_upper :
          min sUpper sLower - (d : ℝ) / (ξ : ℝ) ≤
            sUpper - (d : ℝ) / (ξ : ℝ) := by
        linarith [min_le_left sUpper sLower]
      have hlower_nonneg : 0 ≤ sLower - (d : ℝ) / (ξ : ℝ) := by
        linarith
      have hupper_nonneg : 0 ≤ sUpper - (d : ℝ) / (ξ : ℝ) := by
        linarith
      linarith
    have hneg :
        -((sUpper - (d : ℝ) / (ξ : ℝ)) +
            (sLower - (d : ℝ) / (ξ : ℝ))) ≤
          -(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hneg hm_nonneg
    calc
      eU + eL =
          -((sUpper - (d : ℝ) / (ξ : ℝ)) +
              (sLower - (d : ℝ) / (ξ : ℝ))) * (m : ℝ) := by
        dsimp [eU, eL]
        ring
      _ ≤ -(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ) := hmul
      _ = eMin := by
        dsimp [eMin]
  have hscale_le :
      Real.rpow (3 : ℝ) (eU + eL) ≤ Real.rpow (3 : ℝ) eMin :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hExp
  calc
    (CUpper * X / DU * Real.rpow (3 : ℝ) eU) *
        (CLower * X / DL * Real.rpow (3 : ℝ) eL) =
        (CUpper / DU * (CLower / DL)) * X ^ 2 *
          (Real.rpow (3 : ℝ) eU * Real.rpow (3 : ℝ) eL) := by
      ring
    _ = (CUpper / DU * (CLower / DL)) * X ^ 2 *
          Real.rpow (3 : ℝ) (eU + eL) := by
      rw [hscale_prod_eq]
    _ ≤ (CUpper / DU * (CLower / DL)) * X ^ 2 *
          Real.rpow (3 : ℝ) eMin := by
      exact mul_le_mul_of_nonneg_left hscale_le
        (mul_nonneg hratio_nonneg (sq_nonneg X))
    _ =
        (CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper) *
            (CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower))) *
          (ξ : ℝ) ^ 2 *
            Real.rpow (3 : ℝ)
              (-(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ)) := by
      dsimp [DU, DL, X, eMin]

/-- Coefficient absorption for the final displayed Section 5.2
`widetildeTheta` estimate. -/
theorem section52_coefficients_mixed_le_widetildeThetaErrorCoeff
    {d ξ m : ℕ} {CUpper CLower CTheta sUpper sLower : ℝ}
    (hξ : 1 ≤ ξ)
    (hCUpper : 0 ≤ CUpper)
    (hCLower : 0 ≤ CLower)
    (hsUpper_gt : (d : ℝ) / (ξ : ℝ) < sUpper)
    (hsLower_gt : (d : ℝ) / (ξ : ℝ) < sLower)
    (hUpperDenom :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper)
    (hLowerDenom :
      0 < ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower)
    (hCTheta :
      CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper) +
          CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower) +
          (CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper)) *
            (CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower)) ≤
        CTheta) :
    section52MomentBoundCoeff d ξ CUpper sUpper m +
          section52MomentBoundCoeff d ξ CLower sLower m +
          section52MomentBoundCoeff d ξ CUpper sUpper m *
            section52MomentBoundCoeff d ξ CLower sLower m ≤
        section52WidetildeThetaErrorCoeff d ξ CTheta (min sUpper sLower) m := by
  let DU : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper
  let DL : ℝ := ((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower
  let scale : ℝ :=
    Real.rpow (3 : ℝ) (-(min sUpper sLower - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))
  have hscale_nonneg : 0 ≤ scale :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hxi_sq_scale_nonneg : 0 ≤ (ξ : ℝ) ^ 2 * scale :=
    mul_nonneg (sq_nonneg (ξ : ℝ)) hscale_nonneg
  have hUpper :
      section52MomentBoundCoeff d ξ CUpper sUpper m ≤
        (CUpper / DU) * (ξ : ℝ) ^ 2 * scale := by
    simpa [DU, scale] using
      section52MomentBoundCoeff_le_common_scale
        (d := d) (ξ := ξ) (m := m) (C := CUpper)
        (s := sUpper) (sMin := min sUpper sLower)
        hξ hCUpper hUpperDenom (min_le_left sUpper sLower)
  have hLower :
      section52MomentBoundCoeff d ξ CLower sLower m ≤
        (CLower / DL) * (ξ : ℝ) ^ 2 * scale := by
    simpa [DL, scale] using
      section52MomentBoundCoeff_le_common_scale
        (d := d) (ξ := ξ) (m := m) (C := CLower)
        (s := sLower) (sMin := min sUpper sLower)
        hξ hCLower hLowerDenom (min_le_right sUpper sLower)
  have hProd :
      section52MomentBoundCoeff d ξ CUpper sUpper m *
          section52MomentBoundCoeff d ξ CLower sLower m ≤
        ((CUpper / DU) * (CLower / DL)) * (ξ : ℝ) ^ 2 * scale := by
    simpa [DU, DL, scale] using
      section52MomentBoundCoeff_mul_le_common_scale
        (d := d) (ξ := ξ) (m := m)
        (CUpper := CUpper) (CLower := CLower)
        (sUpper := sUpper) (sLower := sLower)
        hCUpper hCLower hsUpper_gt hsLower_gt hUpperDenom hLowerDenom
  calc
    section52MomentBoundCoeff d ξ CUpper sUpper m +
          section52MomentBoundCoeff d ξ CLower sLower m +
          section52MomentBoundCoeff d ξ CUpper sUpper m *
            section52MomentBoundCoeff d ξ CLower sLower m
        ≤ (CUpper / DU) * (ξ : ℝ) ^ 2 * scale +
            (CLower / DL) * (ξ : ℝ) ^ 2 * scale +
            ((CUpper / DU) * (CLower / DL)) * (ξ : ℝ) ^ 2 * scale := by
      linarith
    _ =
        (CUpper / DU + CLower / DL + (CUpper / DU) * (CLower / DL)) *
          ((ξ : ℝ) ^ 2 * scale) := by
      ring
    _ ≤ CTheta * ((ξ : ℝ) ^ 2 * scale) := by
      exact mul_le_mul_of_nonneg_right (by simpa [DU, DL] using hCTheta)
        hxi_sq_scale_nonneg
    _ = section52WidetildeThetaErrorCoeff d ξ CTheta (min sUpper sLower) m := by
      simp [section52WidetildeThetaErrorCoeff, scale, mul_assoc]

/-- The one-parent Rosenthal budget for unit-descendant averages over `Q`.
This is a private coefficient used to feed the Ch4 law-facing finite-parent
fluctuation theorem. -/
noncomputable def section52UnitDescendantRosenthalBudget {d : ℕ}
    (Q : TriadicCube d) (ξ : ℕ) (K : ℝ) : ℝ :=
  ((descendantsAtScale Q (0 : ℤ)).card : ℝ)⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
        ((descendantsAtScale Q (0 : ℤ)).card : ℝ) ^ (1 / (ξ : ℝ)) * K +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
        Real.sqrt ((descendantsAtScale Q (0 : ℤ)).card : ℝ) * K)

theorem section52UnitDescendantRosenthalBudget_nonneg {d : ℕ}
    (Q : TriadicCube d) (ξ : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 ≤ section52UnitDescendantRosenthalBudget Q ξ K := by
  unfold section52UnitDescendantRosenthalBudget
  have hcard_nonneg :
      0 ≤ ((descendantsAtScale Q (0 : ℤ)).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ := by
    have hξ_nonneg : 0 ≤ (ξ : ℝ) := by exact_mod_cast Nat.zero_le ξ
    have hbase_nonneg :
        0 ≤ (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le ((scaleColorPeriod 0) ^ d)
    have hpow_nonneg :
        0 ≤ (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) ^ (1 - (ξ : ℝ)⁻¹) :=
      Real.rpow_nonneg hbase_nonneg _
    have hprod :
        0 ≤ 2 * (ξ : ℝ) *
          (((scaleColorPeriod 0) ^ d : ℕ) : ℝ) ^ (1 - (ξ : ℝ)⁻¹) :=
      mul_nonneg (mul_nonneg (by norm_num) hξ_nonneg) hpow_nonneg
    simpa [Ch04.rosenthalDescendantsAtScaleLpConst, one_div, mul_assoc] using hprod
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst
      Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  positivity

noncomputable def section52LargeScaleLpRootCoeff
    (d ξ : ℕ) (s : ℝ) (m : ℕ) (n : ℤ) : ℝ :=
  section52LargeScaleWeight s m n *
    ((((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ) ^
        (1 / (ξ : ℝ))) *
      (((descendantsAtScale (originCube d n) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ *
          (((descendantsAtScale (originCube d n) 0).card : ℝ) ^
            (1 / (ξ : ℝ))) * 2)))

noncomputable def section52LargeScaleSqrtRootCoeff
    (d ξ : ℕ) (s : ℝ) (m : ℕ) (n : ℤ) : ℝ :=
  section52LargeScaleWeight s m n *
    ((((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ) ^
        (1 / (ξ : ℝ))) *
      (((descendantsAtScale (originCube d n) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ *
          Real.sqrt ((descendantsAtScale (originCube d n) 0).card : ℝ) * 2)))

noncomputable def section52LargeScaleRootCoeff
    (d ξ : ℕ) (s : ℝ) (m : ℕ) (n : ℤ) : ℝ :=
  section52LargeScaleLpRootCoeff d ξ s m n +
    section52LargeScaleSqrtRootCoeff d ξ s m n

theorem section52LargeScaleLpRootCoeff_nonneg
    {d ξ : ℕ} {s : ℝ} (m : ℕ) (n : ℤ) (hs : 0 ≤ s) :
    0 ≤ section52LargeScaleLpRootCoeff d ξ s m n := by
  unfold section52LargeScaleLpRootCoeff
  have hweight : 0 ≤ section52LargeScaleWeight s m n :=
    section52LargeScaleWeight_nonneg m hs n
  have hcard_m_nonneg :
      0 ≤ (((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ)) := by
    exact_mod_cast Nat.zero_le _
  have hcard_n_nonneg :
      0 ≤ (((descendantsAtScale (originCube d n) 0).card : ℝ)) := by
    exact_mod_cast Nat.zero_le _
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 ξ := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  positivity

theorem section52LargeScaleSqrtRootCoeff_nonneg
    {d ξ : ℕ} {s : ℝ} (m : ℕ) (n : ℤ) (hs : 0 ≤ s) :
    0 ≤ section52LargeScaleSqrtRootCoeff d ξ s m n := by
  unfold section52LargeScaleSqrtRootCoeff
  have hweight : 0 ≤ section52LargeScaleWeight s m n :=
    section52LargeScaleWeight_nonneg m hs n
  have hcard_m_nonneg :
      0 ≤ (((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ)) := by
    exact_mod_cast Nat.zero_le _
  have hcard_n_nonneg :
      0 ≤ (((descendantsAtScale (originCube d n) 0).card : ℝ)) := by
    exact_mod_cast Nat.zero_le _
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 ξ := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  positivity

theorem section52LargeScaleRootCoeff_nonneg
    {d ξ : ℕ} {s : ℝ} (m : ℕ) (n : ℤ) (hs : 0 ≤ s) :
    0 ≤ section52LargeScaleRootCoeff d ξ s m n := by
  unfold section52LargeScaleRootCoeff
  exact add_nonneg
    (section52LargeScaleLpRootCoeff_nonneg (d := d) (ξ := ξ) (s := s) m n hs)
    (section52LargeScaleSqrtRootCoeff_nonneg (d := d) (ξ := ξ) (s := s) m n hs)

end

end Section52
end Ch05
end Book
end Homogenization
