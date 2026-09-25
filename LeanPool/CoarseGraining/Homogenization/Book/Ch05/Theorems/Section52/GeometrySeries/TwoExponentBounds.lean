/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PointwiseSplits
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

/-! # Two Exponent Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

theorem section52_gap_decay_mul_scale_decay_eq
    {s r : ℝ} (m j : ℕ) :
    Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) =
      Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  calc
    Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
        Real.rpow (3 : ℝ) (-s * (m : ℝ)) =
      Real.rpow (3 : ℝ)
        (-(r - s) * ((j + m : ℕ) : ℝ) + -s * (m : ℝ)) := by
        exact (Real.rpow_add h3 _ _).symm
    _ = Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ) + -r * (m : ℝ)) := by
        congr 1
        norm_num
        ring
    _ =
      Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) := by
        exact Real.rpow_add h3 _ _

theorem upperSmallSqrtTailCoeffField_term_le_two_exponent
    {d : ℕ} [NeZero d] (m j : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (a : RegCoeffField d) :
    geometricWeight r 1 (j + m) *
        Real.rpow
          (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
            (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
            Real.rpow
              ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                (descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (by simp [originCube]))
                (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
              (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let source : ℝ :=
    Real.rpow
      ((descendantsAtScale Q 0).sup'
        (descendantsAtScale_nonempty Q (by simp [Q, originCube]))
        (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
      (1 / 2 : ℝ)
  have hsource_nonneg : 0 ≤ source := by
    simpa [source, Q] using upper_unitCube_source_rpow_half_nonneg m hs a
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le
  have hgap_decay_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hscale_decay_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let root : ℝ :=
      Real.rpow
        (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
    have hroot_nonneg : 0 ≤ root := by
      exact Real.rpow_nonneg
        (maxDescendantBMatrixNormCoeffFieldAtScale_nonneg_of_le Q a
          (by dsimp [Q, originCube]; omega)) _
    have hweight :
        geometricWeight r 1 (j + m) ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
              geometricWeight s 1 (j + m) :=
      geometricWeight_one_le_inv_discount_mul_gap_decay_mul_geometricWeight
        hs hsr (j + m)
    have hterm_s :
        geometricWeight s 1 (j + m) * root ≤
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source := by
      simpa [Q, source, root, F, Ch02.geometricWeight_eq_old,
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale,
        Ch04.LambdaSqCoeffField, ha] using
        Ch02.upperSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_LambdaSq_sup'_rpow_half
          (d := d) m j hs F
    have hcoef_nonneg :
        0 ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) := by
      exact mul_nonneg hdisc_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    calc
      geometricWeight r 1 (j + m) *
          Real.rpow
            (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) (-(j : ℤ)) a)
            (1 / 2 : ℝ)
          = geometricWeight r 1 (j + m) * root := by simp [Q, root]
      _ ≤
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
                geometricWeight s 1 (j + m)) * root :=
            mul_le_mul_of_nonneg_right hweight hroot_nonneg
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
            (geometricWeight s 1 (j + m) * root) := by ring
      _ ≤
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
            (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source) :=
            mul_le_mul_of_nonneg_left hterm_s hcoef_nonneg
      _ =
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by
            calc
              ((geometricDiscount s 1)⁻¹ *
                  Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
                (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source) =
                  (geometricDiscount s 1)⁻¹ *
                    (Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
                      Real.rpow (3 : ℝ) (-s * (m : ℝ))) * source := by ring
              _ =
                  (geometricDiscount s 1)⁻¹ *
                    (Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
                      Real.rpow (3 : ℝ) (-r * (m : ℝ))) * source := by
                    rw [section52_gap_decay_mul_scale_decay_eq (s := s) (r := r) m j]
              _ =
                  (geometricDiscount s 1)⁻¹ *
                    Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
                      Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by ring
      _ =
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
                Real.rpow
                  ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                    (descendantsAtScale_nonempty (originCube d (m : ℤ))
                      (by simp [originCube]))
                    (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
                  (1 / 2 : ℝ) := by
            simp [source, Q]
  · have hleft :
        geometricWeight r 1 (j + m) *
            Real.rpow
              (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) (-(j : ℤ)) a)
              (1 / 2 : ℝ) = 0 := by
      simp [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, ha]
    rw [hleft]
    positivity

theorem lowerSmallSqrtTailCoeffField_term_le_two_exponent
    {d : ℕ} [NeZero d] (m j : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (a : RegCoeffField d) :
    geometricWeight r 1 (j + m) *
        Real.rpow
          (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            (originCube d (m : ℤ)) (-(j : ℤ)) a)
          (1 / 2 : ℝ) ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
            Real.rpow
              ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                (descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (by simp [originCube]))
                (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
              (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let source : ℝ :=
    Real.rpow
      ((descendantsAtScale Q 0).sup'
        (descendantsAtScale_nonempty Q (by simp [Q, originCube]))
        (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
      (1 / 2 : ℝ)
  have hsource_nonneg : 0 ≤ source := by
    simpa [source, Q] using lower_unitCube_source_rpow_half_nonneg m hs a
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le
  have hgap_decay_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hscale_decay_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  by_cases ha : Ch04.AELocallyUniformlyEllipticField a
  · let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let root : ℝ :=
      Real.rpow
        (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
    have hroot_nonneg : 0 ≤ root := by
      exact Real.rpow_nonneg
        (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_nonneg_of_le Q a
          (by dsimp [Q, originCube]; omega)) _
    have hweight :
        geometricWeight r 1 (j + m) ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
              geometricWeight s 1 (j + m) :=
      geometricWeight_one_le_inv_discount_mul_gap_decay_mul_geometricWeight
        hs hsr (j + m)
    have hterm_s :
        geometricWeight s 1 (j + m) * root ≤
          Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source := by
      simpa [Q, source, root, F, Ch02.geometricWeight_eq_old,
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
        Ch04.lambdaSqCoeffField, ha] using
        Ch02.lowerSmallSqrtTailTerm_le_scale_factor_mul_scale_zero_lambdaSq_inv_sup'_rpow_half
          (d := d) m j hs F
    have hcoef_nonneg :
        0 ≤
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) := by
      exact mul_nonneg hdisc_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    calc
      geometricWeight r 1 (j + m) *
          Real.rpow
            (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              (originCube d (m : ℤ)) (-(j : ℤ)) a)
            (1 / 2 : ℝ)
          = geometricWeight r 1 (j + m) * root := by simp [Q, root]
      _ ≤
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
                geometricWeight s 1 (j + m)) * root :=
            mul_le_mul_of_nonneg_right hweight hroot_nonneg
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
            (geometricWeight s 1 (j + m) * root) := by ring
      _ ≤
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
            (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source) :=
            mul_le_mul_of_nonneg_left hterm_s hcoef_nonneg
      _ =
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by
            calc
              ((geometricDiscount s 1)⁻¹ *
                  Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ))) *
                (Real.rpow (3 : ℝ) (-s * (m : ℝ)) * source) =
                  (geometricDiscount s 1)⁻¹ *
                    (Real.rpow (3 : ℝ) (-(r - s) * ((j + m : ℕ) : ℝ)) *
                      Real.rpow (3 : ℝ) (-s * (m : ℝ))) * source := by ring
              _ =
                  (geometricDiscount s 1)⁻¹ *
                    (Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
                      Real.rpow (3 : ℝ) (-r * (m : ℝ))) * source := by
                    rw [section52_gap_decay_mul_scale_decay_eq (s := s) (r := r) m j]
              _ =
                  (geometricDiscount s 1)⁻¹ *
                    Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
                      Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by ring
      _ =
          (geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
                Real.rpow
                  ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                    (descendantsAtScale_nonempty (originCube d (m : ℤ))
                      (by simp [originCube]))
                    (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
                  (1 / 2 : ℝ) := by
            simp [source, Q]
  · have hleft :
        geometricWeight r 1 (j + m) *
            Real.rpow
              (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                (originCube d (m : ℤ)) (-(j : ℤ)) a)
              (1 / 2 : ℝ) = 0 := by
      simp [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]
    rw [hleft]
    positivity

theorem upperSmallSqrtTailCoeffField_le_two_exponent_unitCube_source
    {d : ℕ} [NeZero d] (m : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r < 1) (a : RegCoeffField d) :
    upperSmallSqrtTailCoeffField (d := d) m r a ≤
      25 * s⁻¹ * (r - s)⁻¹ *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
          Real.rpow
            ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
              (descendantsAtScale_nonempty (originCube d (m : ℤ))
                (by simp [originCube]))
              (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
            (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let source : ℝ :=
    Real.rpow
      ((descendantsAtScale Q 0).sup'
        (descendantsAtScale_nonempty Q (by simp [Q, originCube]))
        (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
      (1 / 2 : ℝ)
  let f : ℕ → ℝ := fun j =>
    geometricWeight r 1 (j + m) *
      Real.rpow
        (Ch04.maxDescendantBMatrixNormCoeffFieldAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  let g : ℕ → ℝ := fun j =>
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source
  have hr_pos : 0 < r := hs.trans hsr
  have hgap_pos : 0 < r - s := sub_pos.mpr hsr
  have hgap_lt_one : r - s < 1 := by linarith
  have hsource_nonneg : 0 ≤ source := by
    simpa [source, Q] using upper_unitCube_source_rpow_half_nonneg m hs a
  have hfSummable : Summable f := by
    have hbase :=
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
        (Q := Q) a hr_pos
    have htail := (summable_nat_add_iff m).2 hbase
    refine htail.congr ?_
    intro j
    simp [f, Q, originCube, Ch02.geometricWeight_eq_old]
  have hgSummable : Summable g := by
    have hraw := summable_rpow_three_neg_mul_nat hgap_pos
    refine
      (hraw.mul_left
        ((geometricDiscount s 1)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source)).congr ?_
    intro j
    simp [g]
    ring
  have hterm : ∀ j : ℕ, f j ≤ g j := by
    intro j
    simpa [f, g, Q, source] using
      upperSmallSqrtTailCoeffField_term_le_two_exponent
        (d := d) m j hs hsr a
  have hsum :
      upperSmallSqrtTailCoeffField (d := d) m r a ≤ ∑' j : ℕ, g j := by
    calc
      upperSmallSqrtTailCoeffField (d := d) m r a = ∑' j : ℕ, f j := by
        simp [upperSmallSqrtTailCoeffField, f, Q]
      _ ≤ ∑' j : ℕ, g j :=
        Summable.tsum_le_tsum hterm hfSummable hgSummable
  have htsum_g :
      (∑' j : ℕ, g j) =
        ((geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := by
    calc
      (∑' j : ℕ, g j) =
          ∑' j : ℕ,
            ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
              Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) := by
            refine tsum_congr ?_
            intro j
            simp [g]
            ring
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
            ∑' j : ℕ, Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) := by
            rw [tsum_mul_left]
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
            (geometricDiscount (r - s) 1)⁻¹ := by
            rw [tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hgap_pos]
  have hdisc_s :
      (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
    inv_geometricDiscount_one_le_five_inv_of_pos_lt_one hs (by linarith)
  have hdisc_gap :
      (geometricDiscount (r - s) 1)⁻¹ ≤ 5 * (r - s)⁻¹ :=
    inv_geometricDiscount_one_le_five_inv_of_pos_lt_one hgap_pos hgap_lt_one
  have hdisc_s_nonneg : 0 ≤ (geometricDiscount s 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le
  have hdisc_gap_nonneg : 0 ≤ (geometricDiscount (r - s) 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hgap_pos)).le
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmid_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source *
        (geometricDiscount (r - s) 1)⁻¹ := by
    exact mul_nonneg (mul_nonneg hscale_nonneg hsource_nonneg) hdisc_gap_nonneg
  have hlast_nonneg : 0 ≤ 5 * (r - s)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hgap_pos.le)
  calc
    upperSmallSqrtTailCoeffField (d := d) m r a ≤ ∑' j : ℕ, g j := hsum
    _ =
        ((geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := htsum_g
    _ ≤
        (5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := by
          nlinarith [mul_le_mul_of_nonneg_right hdisc_s hmid_nonneg]
    _ ≤
        (5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (5 * (r - s)⁻¹) := by
          have hleft_nonneg :
              0 ≤ 5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by
            positivity
          exact mul_le_mul_of_nonneg_left hdisc_gap hleft_nonneg
    _ =
        25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by ring
    _ =
        25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
            Real.rpow
              ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                (descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (by simp [originCube]))
                (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
              (1 / 2 : ℝ) := by
          simp [source, Q]

theorem lowerSmallSqrtTailCoeffField_le_two_exponent_unitCube_source
    {d : ℕ} [NeZero d] (m : ℕ) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hr : r < 1) (a : RegCoeffField d) :
    lowerSmallSqrtTailCoeffField (d := d) m r a ≤
      25 * s⁻¹ * (r - s)⁻¹ *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
          Real.rpow
            ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
              (descendantsAtScale_nonempty (originCube d (m : ℤ))
                (by simp [originCube]))
              (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
            (1 / 2 : ℝ) := by
  classical
  let Q : TriadicCube d := originCube d (m : ℤ)
  let source : ℝ :=
    Real.rpow
      ((descendantsAtScale Q 0).sup'
        (descendantsAtScale_nonempty Q (by simp [Q, originCube]))
        (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
      (1 / 2 : ℝ)
  let f : ℕ → ℝ := fun j =>
    geometricWeight r 1 (j + m) *
      Real.rpow
        (Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (-(j : ℤ)) a)
        (1 / 2 : ℝ)
  let g : ℕ → ℝ := fun j =>
    (geometricDiscount s 1)⁻¹ *
      Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source
  have hr_pos : 0 < r := hs.trans hsr
  have hgap_pos : 0 < r - s := sub_pos.mpr hsr
  have hgap_lt_one : r - s < 1 := by linarith
  have hsource_nonneg : 0 ≤ source := by
    simpa [source, Q] using lower_unitCube_source_rpow_half_nonneg m hs a
  have hfSummable : Summable f := by
    have hbase :=
      Ch04.RestrictionLawCarrier.summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        (Q := Q) a hr_pos
    have htail := (summable_nat_add_iff m).2 hbase
    refine htail.congr ?_
    intro j
    simp [f, Q, originCube, Ch02.geometricWeight_eq_old]
  have hgSummable : Summable g := by
    have hraw := summable_rpow_three_neg_mul_nat hgap_pos
    refine
      (hraw.mul_left
        ((geometricDiscount s 1)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source)).congr ?_
    intro j
    simp [g]
    ring
  have hterm : ∀ j : ℕ, f j ≤ g j := by
    intro j
    simpa [f, g, Q, source] using
      lowerSmallSqrtTailCoeffField_term_le_two_exponent
        (d := d) m j hs hsr a
  have hsum :
      lowerSmallSqrtTailCoeffField (d := d) m r a ≤ ∑' j : ℕ, g j := by
    calc
      lowerSmallSqrtTailCoeffField (d := d) m r a = ∑' j : ℕ, f j := by
        simp [lowerSmallSqrtTailCoeffField, f, Q]
      _ ≤ ∑' j : ℕ, g j :=
        Summable.tsum_le_tsum hterm hfSummable hgSummable
  have htsum_g :
      (∑' j : ℕ, g j) =
        ((geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := by
    calc
      (∑' j : ℕ, g j) =
          ∑' j : ℕ,
            ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
              Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) := by
            refine tsum_congr ?_
            intro j
            simp [g]
            ring
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
            ∑' j : ℕ, Real.rpow (3 : ℝ) (-(r - s) * (j : ℝ)) := by
            rw [tsum_mul_left]
      _ =
          ((geometricDiscount s 1)⁻¹ *
              Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
            (geometricDiscount (r - s) 1)⁻¹ := by
            rw [tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hgap_pos]
  have hdisc_s :
      (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
    inv_geometricDiscount_one_le_five_inv_of_pos_lt_one hs (by linarith)
  have hdisc_gap :
      (geometricDiscount (r - s) 1)⁻¹ ≤ 5 * (r - s)⁻¹ :=
    inv_geometricDiscount_one_le_five_inv_of_pos_lt_one hgap_pos hgap_lt_one
  have hdisc_s_nonneg : 0 ≤ (geometricDiscount s 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hs)).le
  have hdisc_gap_nonneg : 0 ≤ (geometricDiscount (r - s) 1)⁻¹ :=
    inv_nonneg.mpr (geometricDiscount_pos (by simpa using hgap_pos)).le
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hmid_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source *
        (geometricDiscount (r - s) 1)⁻¹ := by
    exact mul_nonneg (mul_nonneg hscale_nonneg hsource_nonneg) hdisc_gap_nonneg
  have hlast_nonneg : 0 ≤ 5 * (r - s)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hgap_pos.le)
  calc
    lowerSmallSqrtTailCoeffField (d := d) m r a ≤ ∑' j : ℕ, g j := hsum
    _ =
        ((geometricDiscount s 1)⁻¹ *
            Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := htsum_g
    _ ≤
        (5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (geometricDiscount (r - s) 1)⁻¹ := by
          nlinarith [mul_le_mul_of_nonneg_right hdisc_s hmid_nonneg]
    _ ≤
        (5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source) *
          (5 * (r - s)⁻¹) := by
          have hleft_nonneg :
              0 ≤ 5 * s⁻¹ * Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by
            positivity
          exact mul_le_mul_of_nonneg_left hdisc_gap hleft_nonneg
    _ =
        25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) * source := by ring
    _ =
        25 * s⁻¹ * (r - s)⁻¹ *
          Real.rpow (3 : ℝ) (-r * (m : ℝ)) *
            Real.rpow
              ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
                (descendantsAtScale_nonempty (originCube d (m : ℤ))
                  (by simp [originCube]))
                (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
              (1 / 2 : ℝ) := by
          simp [source, Q]

end

end Section52
end Ch05
end Book
end Homogenization
