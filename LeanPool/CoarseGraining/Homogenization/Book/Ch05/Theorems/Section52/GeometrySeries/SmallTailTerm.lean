/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PointwiseSplits
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.TwoExponentBounds

/-! # Small Tail Term -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem upperSmallTailTerm_le_raw_unitDescendantSup
    {d : ℕ} [NeZero d] (m : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r < 1) (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    upperSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
        section52SmallTailWeight r m ≤
      ((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) := by
  intro D hD
  let S : ℝ := D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)
  let B : ℝ := 25 * s⁻¹ * (r - s)⁻¹ *
    Real.rpow (3 : ℝ) (-r * (m : ℝ))
  have hr_pos : 0 < r := hs.trans hsr
  have hVpos : 0 < section52SmallTailWeight r m :=
    section52SmallTailWeight_pos hr_pos m
  have hS_nonneg : 0 ≤ S := by
    dsimp [S, D]
    rcases hD with ⟨U0, hU0⟩
    exact
      (Ch04.LambdaSqCoeffField_finite_nonneg U0 a hs
        (by norm_num : (1 : ℝ) ≤ 1)).trans
        (Finset.le_sup'
          (f := fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) hU0)
  have hsqrtS_nonneg : 0 ≤ Real.rpow S (1 / 2 : ℝ) :=
    Real.rpow_nonneg hS_nonneg _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hgap_pos : 0 < r - s := sub_pos.mpr hsr
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (25 : ℝ)) (inv_nonneg.mpr hs.le))
        (inv_nonneg.mpr hgap_pos.le))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hT_nonneg : 0 ≤ upperSmallSqrtTailCoeffField (d := d) m r a :=
    upperSmallSqrtTailCoeffField_nonneg m hr_pos.le a
  have hT_le :
      upperSmallSqrtTailCoeffField (d := d) m r a ≤
        B * Real.rpow S (1 / 2 : ℝ) := by
    simpa [B, S, D] using
      upperSmallSqrtTailCoeffField_le_two_exponent_unitCube_source
        (d := d) m hs hsr hr a
  have hsq :
      upperSmallSqrtTailCoeffField (d := d) m r a ^ 2 ≤
        (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hT_nonneg hT_le 2
  have hsq_rhs :
      (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 = B ^ 2 * S := by
    rw [mul_pow]
    have hsS : (Real.rpow S (1 / 2 : ℝ)) ^ 2 = S :=
      Homogenization.sq_rpow_half_eq_self_of_nonneg hS_nonneg
    rw [hsS]
  calc
    upperSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
        section52SmallTailWeight r m ≤
      (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 /
        section52SmallTailWeight r m :=
        div_le_div_of_nonneg_right hsq hVpos.le
    _ = (B ^ 2 / section52SmallTailWeight r m) * S := by
        rw [hsq_rhs]
        ring
    _ =
      ((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) := by
        simp [B, S]

theorem lowerSmallTailTerm_le_raw_unitDescendantSup
    {d : ℕ} [NeZero d] (m : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r < 1) (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    lowerSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
        section52SmallTailWeight r m ≤
      ((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) := by
  intro D hD
  let S : ℝ := D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)
  let B : ℝ := 25 * s⁻¹ * (r - s)⁻¹ *
    Real.rpow (3 : ℝ) (-r * (m : ℝ))
  have hr_pos : 0 < r := hs.trans hsr
  have hVpos : 0 < section52SmallTailWeight r m :=
    section52SmallTailWeight_pos hr_pos m
  have hS_nonneg : 0 ≤ S := by
    dsimp [S, D]
    rcases hD with ⟨U0, hU0⟩
    exact
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg U0 a hs
          (by norm_num : (1 : ℝ) ≤ 1))).trans
        (Finset.le_sup'
          (f := fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) hU0)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    have hgap_pos : 0 < r - s := sub_pos.mpr hsr
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (25 : ℝ)) (inv_nonneg.mpr hs.le))
        (inv_nonneg.mpr hgap_pos.le))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hT_nonneg : 0 ≤ lowerSmallSqrtTailCoeffField (d := d) m r a :=
    lowerSmallSqrtTailCoeffField_nonneg m hr_pos.le a
  have hT_le :
      lowerSmallSqrtTailCoeffField (d := d) m r a ≤
        B * Real.rpow S (1 / 2 : ℝ) := by
    simpa [B, S, D] using
      lowerSmallSqrtTailCoeffField_le_two_exponent_unitCube_source
        (d := d) m hs hsr hr a
  have hsq :
      lowerSmallSqrtTailCoeffField (d := d) m r a ^ 2 ≤
        (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hT_nonneg hT_le 2
  have hsq_rhs :
      (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 = B ^ 2 * S := by
    rw [mul_pow]
    have hsS : (Real.rpow S (1 / 2 : ℝ)) ^ 2 = S :=
      Homogenization.sq_rpow_half_eq_self_of_nonneg hS_nonneg
    rw [hsS]
  calc
    lowerSmallSqrtTailCoeffField (d := d) m r a ^ 2 /
        section52SmallTailWeight r m ≤
      (B * Real.rpow S (1 / 2 : ℝ)) ^ 2 /
        section52SmallTailWeight r m :=
        div_le_div_of_nonneg_right hsq hVpos.le
    _ = (B ^ 2 / section52SmallTailWeight r m) * S := by
        rw [hsq_rhs]
        ring
    _ =
      ((25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ))) ^ 2 /
        section52SmallTailWeight r m) *
        D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) := by
        simp [B, S]

theorem upperSmallTailTerm_le_sameExponent_unitDescendantSum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let V := section52SmallTailWeight s m
    upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 / V ≤
      (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V) *
        ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a := by
  classical
  intro D V
  have hVpos : 0 < V := by
    simpa [V] using section52SmallTailWeight_pos hs m
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    have htail :
        upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 ≤
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ)) *
            ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a := by
      simpa [upperSmallSqrtTailCoeffField, Ch02.upperSmallSqrtTail,
        Ch02.geometricWeight_eq_old, D, F,
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale,
        Ch04.LambdaSqCoeffField, ha] using
        Ch02.upperSmallSqrtTail_sq_le_scale_factor_sq_mul_card_sum_scale_zero_LambdaSq
          (d := d) m hs F
    calc
      upperSmallSqrtTailCoeffField (d := d) m s a ^ 2 / V
          ≤ ((Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ)) *
              ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a) / V :=
            div_le_div_of_nonneg_right htail hVpos.le
      _ =
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V) *
            ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a := by
            ring
  · have htail_zero : upperSmallSqrtTailCoeffField (d := d) m s a = 0 := by
      simp [upperSmallSqrtTailCoeffField,
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha]
    have hsum_nonneg :
        0 ≤ ∑ U ∈ D, Ch04.LambdaSqCoeffField U s (.finite 1) a := by
      exact Finset.sum_nonneg fun U _hU =>
        Ch04.LambdaSqCoeffField_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1)
    have hcoeff_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V := by
      exact div_nonneg
        (mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le D.card))
        hVpos.le
    simpa [htail_zero] using mul_nonneg hcoeff_nonneg hsum_nonneg

theorem lowerSmallTailTerm_le_sameExponent_unitDescendantSum
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a : RegCoeffField d) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let V := section52SmallTailWeight s m
    lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 / V ≤
      (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V) *
        ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹ := by
  classical
  intro D V
  have hVpos : 0 < V := by
    simpa [V] using section52SmallTailWeight_pos hs m
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    have htail :
        lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 ≤
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ)) *
            ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹ := by
      simpa [lowerSmallSqrtTailCoeffField, Ch02.lowerSmallSqrtTail,
        Ch02.geometricWeight_eq_old, D, F,
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
        Ch04.lambdaSqCoeffField, ha] using
        Ch02.lowerSmallSqrtTail_sq_le_scale_factor_sq_mul_card_sum_scale_zero_lambdaSq_inv
          (d := d) m hs F
    calc
      lowerSmallSqrtTailCoeffField (d := d) m s a ^ 2 / V
          ≤ ((Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ)) *
              ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) / V :=
            div_le_div_of_nonneg_right htail hVpos.le
      _ =
          (Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V) *
            ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹ := by
            ring
  · have htail_zero : lowerSmallSqrtTailCoeffField (d := d) m s a = 0 := by
      simp [lowerSmallSqrtTailCoeffField,
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]
    have hsum_nonneg :
        0 ≤ ∑ U ∈ D, (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹ := by
      exact Finset.sum_nonneg fun U _hU =>
        inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg U a hs (by norm_num : (1 : ℝ) ≤ 1))
    have hcoeff_nonneg :
        0 ≤ Real.rpow (3 : ℝ) (-s * (m : ℝ)) ^ 2 * (D.card : ℝ) / V := by
      exact div_nonneg
        (mul_nonneg (sq_nonneg _) (by exact_mod_cast Nat.zero_le D.card))
        hVpos.le
    simpa [htail_zero] using mul_nonneg hcoeff_nonneg hsum_nonneg

theorem inv_geometricDiscount_one_le_five_mul_upper_mul_inv
    {gap B : ℝ} (hgap : 0 < gap) (hgap_le_B : gap ≤ B) (hB : 1 ≤ B) :
    (geometricDiscount gap 1)⁻¹ ≤ 5 * B * gap⁻¹ := by
  by_cases hgap_le_one : gap ≤ 1
  · have hinv :
        (geometricDiscount gap 1)⁻¹ ≤ 5 * gap⁻¹ :=
      Book.Ch02.inv_geometricDiscount_le_five_inv
        (s := gap) (p := 1) hgap hgap_le_one (by norm_num)
    have hgap_inv_nonneg : 0 ≤ gap⁻¹ := inv_nonneg.mpr hgap.le
    have hBmul : 5 * gap⁻¹ ≤ 5 * B * gap⁻¹ := by
      calc
        5 * gap⁻¹ ≤ (5 * B) * gap⁻¹ :=
            mul_le_mul_of_nonneg_right (by nlinarith) hgap_inv_nonneg
        _ = 5 * B * gap⁻¹ := by ring
    exact hinv.trans hBmul
  · have hone_le_gap : (1 : ℝ) ≤ gap := by linarith
    have hdisc_gap_pos : 0 < geometricDiscount gap 1 :=
      geometricDiscount_pos (by simpa using hgap)
    have hdisc_one_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
      geometricDiscount_pos (by norm_num)
    have hmono : geometricDiscount (1 : ℝ) 1 ≤ geometricDiscount gap 1 := by
      unfold geometricDiscount
      have hpow :
          Real.rpow (3 : ℝ) (-gap * 1) ≤
            Real.rpow (3 : ℝ) (-(1 : ℝ) * 1) := by
        refine Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 3) ?_
        nlinarith
      linarith
    have hinv_order :
        (geometricDiscount gap 1)⁻¹ ≤ (geometricDiscount (1 : ℝ) 1)⁻¹ :=
      (inv_le_inv₀ hdisc_gap_pos hdisc_one_pos).2 hmono
    have hinv_one :
        (geometricDiscount (1 : ℝ) 1)⁻¹ ≤ 5 := by
      have hinv_one_ch02 :
          (Book.Ch02.geometricDiscount (1 : ℝ) 1)⁻¹ ≤ 5 * (1 : ℝ)⁻¹ :=
        Book.Ch02.inv_geometricDiscount_le_five_inv
          (s := (1 : ℝ)) (p := 1) (by norm_num) (by norm_num) (by norm_num)
      simpa [Book.Ch02.geometricDiscount_eq_old] using hinv_one_ch02
    have hone_le_B_mul_inv : (1 : ℝ) ≤ B * gap⁻¹ := by
      have hmul :
          gap * gap⁻¹ ≤ B * gap⁻¹ :=
        mul_le_mul_of_nonneg_right hgap_le_B (inv_nonneg.mpr hgap.le)
      have hgap_mul_inv : gap * gap⁻¹ = 1 := by
        field_simp [hgap.ne']
      simpa [hgap_mul_inv] using hmul
    have hfive_le : (5 : ℝ) ≤ 5 * B * gap⁻¹ := by
      calc
        (5 : ℝ) = 5 * 1 := by ring
        _ ≤ 5 * (B * gap⁻¹) :=
            mul_le_mul_of_nonneg_left hone_le_B_mul_inv (by norm_num)
        _ = 5 * B * gap⁻¹ := by ring
    exact hinv_order.trans (hinv_one.trans hfive_le)

end

end Section52
end Ch05
end Book
end Homogenization
