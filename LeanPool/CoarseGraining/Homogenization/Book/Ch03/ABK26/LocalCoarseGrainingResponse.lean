/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.ParentTruncatedHomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.AEEq
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.Finite

/-! # Local Coarse Graining Response -/

open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

noncomputable section

/-- The globally measurable pointwise-good representative of a root coefficient,
viewed as a compatible coefficient family on every triadic cube. -/
noncomputable def rootPointwiseCoeffFamily {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) :
    Ch02.TriadicCoeffFamily d where
  coeffOn := fun R =>
    { toCoeffField := Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) a
      lam := a.lam
      Lam := a.Lam
      lam_pos := a.lam_pos
      lam_le_Lam := a.lam_le_Lam
      aeStronglyMeasurable := by
        classical
        intro i j
        have hcoeff :
            Measurable fun x : Vec d =>
              Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) a x i j := by
          exact (measurable_pi_iff.1 (measurable_pi_iff.1
            (Internal.Ch02.BookCh02.pointwiseCoeffField_measurable
              (Ch02.cubeDomain Q) a) i) j)
        have hentry : Measurable fun x : Vec d =>
            restrictCoeffField (openCubeSet R)
              (Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) a) x i j := by
          have hite : Measurable fun x : Vec d =>
              if x ∈ openCubeSet R then
                Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) a x i j
              else 0 :=
            Measurable.ite (measurableSet_openCubeSet R) hcoeff measurable_const
          convert hite using 1
          funext x
          by_cases hx : x ∈ openCubeSet R <;> simp [restrictCoeffField, hx]
        exact hentry.aestronglyMeasurable
      aeElliptic := by
        filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)]
          with x _hx
        by_cases hxGood : x ∈
            (Internal.Ch02.BookCh02.goodSetData (Ch02.cubeDomain Q) a).set
        · simpa [Internal.Ch02.BookCh02.pointwiseCoeffField, hxGood] using
            (Internal.Ch02.BookCh02.goodSetData (Ch02.cubeDomain Q) a).elliptic x hxGood
        · simpa [Internal.Ch02.BookCh02.pointwiseCoeffField, hxGood] using
            Internal.Ch02.BookCh02.isEllipticMatrix_smul_one
              (d := d) a.lam_pos a.lam_le_Lam }
  restrictsTo_of_subset := by
    intro R S _hSR
    exact Filter.EventuallyEq.rfl

/-- At its root, the canonical pointwise family agrees a.e. with the supplied
public coefficient. -/
theorem rootPointwiseCoeffFamily_root_aeeq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) :
    Ch02.CoeffOn.AEEq ((rootPointwiseCoeffFamily Q a).coeffOn Q) a := by
  exact Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq (Ch02.cubeDomain Q) a

/-- On every descendant, the canonical pointwise family agrees a.e. with the
literal restriction of the supplied root coefficient. -/
theorem rootPointwiseCoeffFamily_descendant_aeeq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    Ch02.CoeffOn.AEEq ((rootPointwiseCoeffFamily Q a).coeffOn R)
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR)) := by
  have hroot := Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
    (Ch02.cubeDomain Q) a
  exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtScale hk hR) hroot

/-- On a descendant, the canonical extended-real scalar response maximum is no
larger than the nonnegative encoding of the legacy real response maximum. -/
theorem normalizedBlockResponseScalarEMaxOnCube_le_ofReal_rootPointwise
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    Ch02.normalizedBlockResponseScalarEMaxOnCube R
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
      sigma0 hsigma0 ≤
      ENNReal.ofReal (Ch02.normalizedBlockResponseMax R
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  apply csSup_le
    (Ch02.normalizedBlockResponseScalarEValueSetOnCube_nonempty R
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR)) sigma0 hsigma0)
  rintro y hy
  rcases (Ch02.mem_normalizedBlockResponseScalarEValueSetOnCube_iff.mp hy)
    with ⟨e, he, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  have hA := rootPointwiseCoeffFamily_descendant_aeeq Q a hk hR
  rw [Ch02.doubledResponseJ_eq_ofAEEq hA.symm]
  exact le_csSup
    (Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) hR)
    ⟨e, he, rfl⟩

/-- Conversely, the nonnegative encoding of the legacy real response maximum
is bounded by the canonical extended-real scalar response maximum. -/
theorem ofReal_normalizedBlockResponseMax_le_rootPointwise
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    ENNReal.ofReal (Ch02.normalizedBlockResponseMax R
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
      Ch02.normalizedBlockResponseScalarEMaxOnCube R
        (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
        sigma0 hsigma0 := by
  let E := Ch02.normalizedBlockResponseScalarEMaxOnCube R
    (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
    sigma0 hsigma0
  have hEtop : E ≠ ∞ :=
    (Ch02.normalizedBlockResponseScalarEMaxOnCube_lt_top R
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
      sigma0 hsigma0).ne
  change ENNReal.ofReal (Ch02.normalizedBlockResponseMax R
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤ E
  rw [← ENNReal.ofReal_toReal hEtop]
  apply ENNReal.ofReal_le_ofReal
  apply csSup_le
    (Ch02.normalizedBlockResponseValueSet_nonempty R (rootPointwiseCoeffFamily Q a)
      (scalarMatrix (d := d) sigma0))
  rintro x ⟨e, he, rfl⟩
  have hnonneg : 0 ≤ Ch02.doubledResponseJ (Ch02.cubeDomain R)
      ((rootPointwiseCoeffFamily Q a).coeffOn R)
      (ofFullBlockVec (Matrix.mulVec
        (Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) sigma0)) e))
      (ofFullBlockVec (Matrix.mulVec
        (Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) sigma0)) e)) :=
    Ch02.doubledResponseJ_nonneg _ _ _ _
  rw [← ENNReal.toReal_ofReal hnonneg]
  apply ENNReal.toReal_mono hEtop
  apply Ch02.normalizedBlockResponseScalarEValueSetOnCube_le_eMax
  apply Ch02.mem_normalizedBlockResponseScalarEValueSetOnCube_iff.mpr
  refine ⟨e, he, ?_⟩
  have hA := rootPointwiseCoeffFamily_descendant_aeeq Q a hk hR
  rw [← Ch02.doubledResponseJ_eq_ofAEEq hA.symm]

/-- The real and extended-real one-cube response maxima agree exactly for the
canonical root family and every descendant of its root. -/
theorem normalizedBlockResponseScalarEMaxOnCube_eq_ofReal_rootPointwise
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ Q.scale)
    (hR : R ∈ descendantsAtScale Q k) :
    Ch02.normalizedBlockResponseScalarEMaxOnCube R
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hk hR))
      sigma0 hsigma0 =
      ENNReal.ofReal (Ch02.normalizedBlockResponseMax R
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  apply le_antisymm
  · exact normalizedBlockResponseScalarEMaxOnCube_le_ofReal_rootPointwise
      Q a sigma0 hsigma0 hk hR
  · exact ofReal_normalizedBlockResponseMax_le_rootPointwise Q a sigma0 hsigma0 hk hR

/-- At every physical scale, the canonical parent extended-real maximum is the
nonnegative encoding of the legacy finite descendant maximum for the root
pointwise family. -/
theorem parentTruncatedNormalizedBlockResponseScalarEMaxAtScale_eq_ofReal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0) :
    Ch02.parentTruncatedNormalizedBlockResponseScalarEMaxAtScale Q k hk a sigma0 hsigma0 =
      ENNReal.ofReal (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  classical
  let S := descendantsAtScale Q k
  let F : {R // R ∈ S} → ℝ≥0∞ := fun R =>
    Ch02.normalizedBlockResponseScalarEMaxOnCube R.1
      (a.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2)) sigma0 hsigma0
  let G : TriadicCube d → ℝ := fun R => Ch02.normalizedBlockResponseMax R
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  have hS_nonempty : S.Nonempty := by
    simpa [S] using descendantsAtScale_nonempty Q hk
  have hG_bdd : BddAbove (G '' (↑S : Set (TriadicCube d))) :=
    (S.finite_toSet.image G).bddAbove
  have hF_top : ∀ R : {R // R ∈ S}, F R < ∞ := by
    intro R
    exact Ch02.normalizedBlockResponseScalarEMaxOnCube_lt_top R.1
      (a.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2)) sigma0 hsigma0
  have hsup_top : S.attach.sup F < ∞ := by
    exact (Finset.sup_lt_iff bot_lt_top).mpr fun R _ => hF_top R
  have hleft : S.attach.sup F ≤ ENNReal.ofReal (Ch02.finsetSupReal S G) := by
    apply Finset.sup_le
    intro R _
    change Ch02.normalizedBlockResponseScalarEMaxOnCube R.1
      (a.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtScale hk R.2)) sigma0 hsigma0 ≤
        ENNReal.ofReal (Ch02.finsetSupReal S G)
    rw [normalizedBlockResponseScalarEMaxOnCube_eq_ofReal_rootPointwise
      Q a sigma0 hsigma0 hk R.2]
    apply ENNReal.ofReal_le_ofReal
    exact le_csSup hG_bdd ⟨R.1, R.2, rfl⟩
  have hright : ENNReal.ofReal (Ch02.finsetSupReal S G) ≤ S.attach.sup F := by
    rw [← ENNReal.ofReal_toReal hsup_top.ne]
    apply ENNReal.ofReal_le_ofReal
    unfold Ch02.finsetSupReal
    apply csSup_le
    · rcases hS_nonempty with ⟨R, hR⟩
      exact ⟨G R, ⟨R, hR, rfl⟩⟩
    rintro x ⟨R, hR, rfl⟩
    dsimp [G]
    rw [← ENNReal.toReal_ofReal
      (Ch02.normalizedBlockResponseMax_nonneg R (rootPointwiseCoeffFamily Q a)
        (scalarMatrix (d := d) sigma0))]
    apply ENNReal.toReal_mono hsup_top.ne
    calc
      ENNReal.ofReal (G R) = F ⟨R, hR⟩ := by
        symm
        exact normalizedBlockResponseScalarEMaxOnCube_eq_ofReal_rootPointwise
          Q a sigma0 hsigma0 hk hR
      _ ≤ S.attach.sup F := Finset.le_sup (s := S.attach) (f := F) (by simp)
  change S.attach.sup F = ENNReal.ofReal (Ch02.finsetSupReal S G)
  exact le_antisymm hleft hright

private theorem summable_rootPointwise_infinity_one_terms {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (s : FractionalOrder) :
    Summable (fun j : ℕ => Ch02.geometricWeight s.1 1 j *
      Ch02.scaleResponseAtScale Q (n - (j : ℤ)) .infinity
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  have hOld : Summable (fun j : ℕ => Homogenization.geometricWeight s.1 1 j *
      Ch02.scaleResponseAtScale Q (n - (j : ℤ)) .infinity
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s.1) (q := 1)
      (C := Real.rpow
        (Ch02.normalizedBlockResponseUniformBound Q (rootPointwiseCoeffFamily Q a)
          (scalarMatrix (d := d) sigma0)) (1 / 2 : ℝ))
      (by simpa using s.2.1) ?_ ?_
    · intro j
      exact Ch02.scaleResponseAtScale_infinity_nonneg Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
    · intro j
      exact Ch02.scaleResponseAtScale_infinity_le_uniform Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  simpa [Ch02.geometricWeight_eq_old] using hOld

/-- The canonical frozen `q = 1` parent error is exactly the extended-real
encoding of the legacy finite homogenization error for the root family. -/
theorem parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 s =
      ENNReal.ofReal (Ch02.HomogenizationErrorFinite Q n s.1 .infinity 1
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar_eq_tsum,
    Ch02.homogenizationErrorFinite_infinity_one_eq_tsum,
    ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro j
    have hjk : n - (j : ℤ) ≤ Q.scale :=
      (sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn
    have hmax_nonneg := Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hjk
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
    rw [Ch02.scaleResponseAtScale_infinity_eq,
      parentTruncatedNormalizedBlockResponseScalarEMaxAtScale_eq_ofReal
        Q (n - (j : ℤ)) hjk a sigma0 hsigma0,
      ENNReal.ofReal_rpow_of_nonneg hmax_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hdisc : 0 ≤ 1 - Real.rpow 3 (-s.1) := by
      simpa [Homogenization.geometricDiscount] using
        (Homogenization.geometricDiscount_nonneg
          (show 0 ≤ s.1 * (1 : ℝ) by nlinarith [s.2.1]))
    have hweight : 0 ≤ (1 - Real.rpow 3 (-s.1)) *
        Real.rpow 3 (-s.1 * (j : ℝ)) :=
      mul_nonneg hdisc (Real.rpow_nonneg (by norm_num) _)
    rw [← ENNReal.ofReal_mul hdisc, ← ENNReal.ofReal_mul hweight]
    simp only [Ch02.geometricWeight, Ch02.geometricDiscount]
    congr 1
    change (1 - Real.rpow 3 (-s.1)) * Real.rpow 3 (-s.1 * (j : ℝ)) *
        (Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) ^ (1 / 2 : ℝ)) =
      Ch02.geometricWeight s.1 1 j *
        Real.rpow
          (Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
          (1 / 2 : ℝ)
    change (1 - Real.rpow 3 (-s.1)) * Real.rpow 3 (-s.1 * (j : ℝ)) *
        Real.rpow
          (Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
          (1 / 2 : ℝ) = _
    unfold Ch02.geometricWeight Ch02.geometricDiscount
    ring_nf
  · intro j
    refine mul_nonneg ?_ ?_
    · simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s.1) (q := 1) j
          (show 0 ≤ s.1 * (1 : ℝ) by nlinarith [s.2.1]))
    · exact Ch02.scaleResponseAtScale_infinity_nonneg Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  · exact summable_rootPointwise_infinity_one_terms Q n hn a sigma0 s

private theorem summable_rootPointwise_infinity_two_terms {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (s : FractionalOrder) :
    Summable (fun j : ℕ => Ch02.geometricWeight s.1 2 j *
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  have hOld : Summable (fun j : ℕ => Homogenization.geometricWeight s.1 2 j *
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s.1) (q := 2)
      (C := Ch02.normalizedBlockResponseUniformBound Q (rootPointwiseCoeffFamily Q a)
        (scalarMatrix (d := d) sigma0))
      (by nlinarith [s.2.1]) ?_ ?_
    · intro j
      exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
    · intro j
      exact Ch02.maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
        ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  simpa [Ch02.geometricWeight_eq_old] using hOld

/-- The canonical frozen `q = 2` parent error is exactly the extended-real
encoding of the legacy finite homogenization error for the root family. -/
theorem parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (s : FractionalOrder) :
    Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 s =
      ENNReal.ofReal (Ch02.HomogenizationErrorFinite Q n s.1 .infinity 2
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  rw [Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_tsum]
  unfold Ch02.HomogenizationErrorFinite
  have hterm : (fun j : ℕ =>
      Ch02.geometricWeight s.1 2 j *
        Real.rpow (Ch02.scaleResponseAtScale Q (n - (j : ℤ)) .infinity
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) 2) =
      fun j : ℕ => Ch02.geometricWeight s.1 2 j *
        Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) := by
    funext j
    congr 1
    exact Ch02.scaleResponseAtScale_infinity_rpow_two_eq Q
      (by omega)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  rw [hterm]
  have hsum_nonneg : 0 ≤ ∑' j : ℕ,
      Ch02.geometricWeight s.1 2 j *
        Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) := by
    refine tsum_nonneg fun j => mul_nonneg ?_ ?_
    · simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s.1) (q := 2) j
          (show 0 ≤ s.1 * (2 : ℝ) by nlinarith [s.2.1]))
    · exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
          ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  have hencode : ENNReal.ofReal
      (Real.rpow (∑' j : ℕ,
        Ch02.geometricWeight s.1 2 j *
          Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) (1 / 2 : ℝ)) =
      ENNReal.ofReal (∑' j : ℕ,
        Ch02.geometricWeight s.1 2 j *
          Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n - (j : ℤ))
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ^
        (1 / 2 : ℝ) :=
    (ENNReal.ofReal_rpow_of_nonneg hsum_nonneg (by norm_num)).symm
  rw [hencode]
  congr 1
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro j
    have hjk : n - (j : ℤ) ≤ Q.scale :=
      (sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn
    rw [parentTruncatedNormalizedBlockResponseScalarEMaxAtScale_eq_ofReal
        Q (n - (j : ℤ)) hjk a sigma0 hsigma0]
    have hdisc : 0 ≤ 1 - Real.rpow 3 (-s.1 * 2) := by
      simpa [Homogenization.geometricDiscount] using
        (Homogenization.geometricDiscount_nonneg
          (show 0 ≤ s.1 * (2 : ℝ) by nlinarith [s.2.1]))
    have hweight : 0 ≤ (1 - Real.rpow 3 (-s.1 * 2)) *
        Real.rpow 3 (-s.1 * 2 * (j : ℝ)) :=
      mul_nonneg hdisc (Real.rpow_nonneg (by norm_num) _)
    rw [← ENNReal.ofReal_mul hdisc, ← ENNReal.ofReal_mul hweight]
    simp only [Ch02.geometricWeight, Ch02.geometricDiscount]
  · intro j
    refine mul_nonneg ?_ ?_
    · simpa [Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s.1) (q := 2) j
          (show 0 ≤ s.1 * (2 : ℝ) by nlinarith [s.2.1]))
    · exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
          ((sub_le_self n (by exact_mod_cast Nat.zero_le j)).trans hn)
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  · exact summable_rootPointwise_infinity_two_terms Q n hn a sigma0 s

/-- The one-scale response comparison used in the exact shifted parent-error
series.  A descendant's on-cube term at depth `j` is controlled by the root
family at the matching physical scale `n - (h + j)`. -/
theorem rootPointwise_scaleResponse_shift_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n)
    (hR : R ∈ descendantsAtScale Q k) (j : ℕ) :
    Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) ≤
      Ch02.scaleResponseAtScale Q
        (n - ((j + Int.toNat (n - k) : ℕ) : ℤ)) .infinity
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) := by
  have hkQ : k ≤ Q.scale := hkn.trans hn
  have hh : (Int.toNat (n - k) : ℤ) = n - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hkn)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hl : R.scale - (j : ℤ) ≤ R.scale := by omega
  have hscale : R.scale - (j : ℤ) = n - ((j + Int.toNat (n - k) : ℕ) : ℤ) := by
    rw [hRscale, Nat.cast_add, hh]
    ring
  rw [← hscale]
  exact Ch02.scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) hR hl

/-- The source-family-facing on-cube `q = 1` response series is summable on
every descendant. -/
theorem summable_rootPointwise_descendant_infinity_one_terms
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) {R : TriadicCube d} {k : ℤ}
    (_hR : R ∈ descendantsAtScale Q k) (sigma0 : ℝ) (s : FractionalOrder) :
    Summable (fun j : ℕ => Ch02.geometricWeight s.1 1 j *
      Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
  exact Ch02.summable_homogenizationErrorOnCube_infinity_one_terms R
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) s.2.1

private theorem rootPointwise_weight_one_nonneg (s : FractionalOrder) (j : ℕ) :
    0 ≤ Ch02.geometricWeight s.1 1 j := by
  have h := Homogenization.geometricWeight_nonneg (s := s.1) (q := (1 : ℝ)) j
    (show 0 ≤ s.1 * (1 : ℝ) by nlinarith [s.2.1])
  simpa [Ch02.geometricWeight_eq_old] using h

private theorem rootPointwise_descendant_infinity_one_le_parent_real
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n) (hR : R ∈ descendantsAtScale Q k)
    (s : FractionalOrder) :
    Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 1)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) ≤
      Real.rpow 3 (s.1 * (Int.toNat (n - k) : ℝ)) *
        Ch02.HomogenizationErrorFinite Q n s.1 .infinity 1
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) := by
  let h : ℕ := Int.toNat (n - k)
  let fQ : ℕ → ℝ := fun j => Ch02.geometricWeight s.1 1 j *
    Ch02.scaleResponseAtScale Q (n - (j : ℤ)) .infinity
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let fR : ℕ → ℝ := fun j => Ch02.geometricWeight s.1 1 j *
    Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let c : ℝ := Real.rpow 3 (s.1 * (h : ℝ))
  have hsum : Summable fQ := by
    simpa [fQ] using summable_rootPointwise_infinity_one_terms Q n hn a sigma0 s
  have hq : ∀ j : ℕ, 0 ≤ fQ j := by
    intro j
    exact mul_nonneg (rootPointwise_weight_one_nonneg s j)
      (Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ j : ℕ, fR j ≤ c * fQ (j + h) := by
    intro j
    have hw : Ch02.geometricWeight s.1 1 j =
        c * Ch02.geometricWeight s.1 1 (j + h) := by
      simpa [c, h, Ch02.geometricWeight_eq_old] using
        Homogenization.geometricWeight_one_shift (s := s.1) h j
    have hresp := rootPointwise_scaleResponse_shift_le Q n hn a sigma0 hkn hR j
    calc
      fR j = c * (Ch02.geometricWeight s.1 1 (j + h) *
          Ch02.scaleResponseAtScale R (R.scale - (j : ℤ)) .infinity
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
          dsimp [fR]; rw [hw]; ring
      _ ≤ c * (Ch02.geometricWeight s.1 1 (j + h) *
          Ch02.scaleResponseAtScale Q (n - ((j + h : ℕ) : ℤ)) .infinity
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul_of_nonneg_left hresp (rootPointwise_weight_one_nonneg s (j + h))
      _ = c * fQ (j + h) := by rfl
  have hr : ∀ j : ℕ, 0 ≤ fR j := by
    intro j
    exact mul_nonneg (rootPointwise_weight_one_nonneg s j)
      (Ch02.scaleResponseAtScale_infinity_nonneg R (by omega)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
  have htail : Summable (fun j : ℕ => fQ (j + h)) := (summable_nat_add_iff h).2 hsum
  have hscaled : Summable (fun j : ℕ => c * fQ (j + h)) := htail.mul_left c
  have hrsum : Summable fR := Summable.of_nonneg_of_le hr hterm hscaled
  have hmain := Summable.tsum_le_tsum hterm hrsum hscaled
  have htail_le : ∑' j : ℕ, fQ (j + h) ≤ ∑' j : ℕ, fQ j := by
    have hsplit := hsum.sum_add_tsum_nat_add h
    have hpref : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg fun i _ => hq i
    linarith
  calc
    Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 1)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) = ∑' j, fR j := by
      rw [Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    _ ≤ ∑' j, c * fQ (j + h) := hmain
    _ = c * ∑' j, fQ (j + h) := by simpa using Summable.tsum_mul_left c htail
    _ ≤ c * ∑' j, fQ j := mul_le_mul_of_nonneg_left htail_le hc
    _ = c * Ch02.HomogenizationErrorFinite Q n s.1 .infinity 1
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) := by
      rw [Ch02.homogenizationErrorFinite_infinity_one_eq_tsum]

/-- Exact shifted localization of a descendant on-cube `q = 1` error by the
canonical parent-truncated error. -/
theorem rootPointwise_descendant_infinity_one_le_parent
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n) (hR : R ∈ descendantsAtScale Q k)
    (s : FractionalOrder) :
    ENNReal.ofReal (Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 1)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3 (s.1 * (Int.toNat (n-k) : ℝ))) *
        Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar Q n hn a sigma0 hsigma0 s := by
  rw [parentTruncatedHomogenizationErrorInfinityOneScalar_eq_ofReal]
  have hc : 0 ≤ Real.rpow 3 (s.1 * (Int.toNat (n-k) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal
    (rootPointwise_descendant_infinity_one_le_parent_real Q n hn a sigma0 hkn hR s)

private theorem rootPointwise_weight_two_nonneg (s : FractionalOrder) (j : ℕ) :
    0 ≤ Ch02.geometricWeight s.1 2 j := by
  have h := Homogenization.geometricWeight_nonneg (s := s.1) (q := (2 : ℝ)) j
    (show 0 ≤ s.1 * (2 : ℝ) by nlinarith [s.2.1])
  simpa [Ch02.geometricWeight_eq_old] using h

private theorem rootPointwise_descendant_infinity_two_sq_le_parent_sq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n) (hR : R ∈ descendantsAtScale Q k)
    (s : FractionalOrder) :
    (Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 2)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ^ 2 ≤
      Real.rpow 3 (2 * s.1 * (Int.toNat (n-k) : ℝ)) *
        (Ch02.HomogenizationErrorFinite Q n s.1 .infinity 2
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ^ 2 := by
  let h := Int.toNat (n-k)
  let fQ : ℕ → ℝ := fun j => Ch02.geometricWeight s.1 2 j *
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n-(j:ℤ))
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let fR : ℕ → ℝ := fun j => Ch02.geometricWeight s.1 2 j *
    Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale-(j:ℤ))
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let c : ℝ := Real.rpow 3 (s.1 * 2 * (h:ℝ))
  have hsum : Summable fQ := by simpa [fQ] using
    summable_rootPointwise_infinity_two_terms Q n hn a sigma0 s
  have hq : ∀ j : ℕ, 0 ≤ fQ j := by
    intro j; exact mul_nonneg (rootPointwise_weight_two_nonneg s j)
      (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q (by omega)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ j : ℕ, fR j ≤ c * fQ (j+h) := by
    intro j
    have hw : Ch02.geometricWeight s.1 2 j = c * Ch02.geometricWeight s.1 2 (j+h) := by
      simpa [c, h, Ch02.geometricWeight_eq_old] using
        Homogenization.geometricWeight_shift (s := s.1) (q := (2:ℝ)) h j
    have hl : R.scale-(j:ℤ) ≤ R.scale := by omega
    have hresp := Ch02.maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0) hR hl
    have hscale : R.scale-(j:ℤ) = n-((j+h:ℕ):ℤ) := by
      have hh : (h:ℤ) = n-k := Int.toNat_of_nonneg (sub_nonneg.mpr hkn)
      have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
      rw [hRscale, Nat.cast_add, hh]; ring
    calc
      fR j = c * (Ch02.geometricWeight s.1 2 (j+h) *
          Ch02.maxDescendantNormalizedBlockResponseAtScale R (R.scale-(j:ℤ))
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
          dsimp [fR]; rw [hw]; ring
      _ ≤ c * (Ch02.geometricWeight s.1 2 (j+h) *
          Ch02.maxDescendantNormalizedBlockResponseAtScale Q (n-((j+h:ℕ):ℤ))
            (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul_of_nonneg_left (by simpa [hscale] using hresp)
            (rootPointwise_weight_two_nonneg s (j+h))
      _ = c * fQ (j+h) := by rfl
  have hr : ∀ j : ℕ, 0 ≤ fR j := by
    intro j; exact mul_nonneg (rootPointwise_weight_two_nonneg s j)
      (Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg R (by omega)
        (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0))
  have htail : Summable (fun j : ℕ => fQ (j+h)) := (summable_nat_add_iff h).2 hsum
  have hscaled : Summable (fun j : ℕ => c*fQ (j+h)) := htail.mul_left c
  have hrsum : Summable fR := Summable.of_nonneg_of_le hr hterm hscaled
  have hmain := Summable.tsum_le_tsum hterm hrsum hscaled
  have htail_le : ∑' j : ℕ, fQ (j+h) ≤ ∑' j : ℕ, fQ j := by
    have hs := hsum.sum_add_tsum_nat_add h
    have hp : 0 ≤ ∑ i ∈ Finset.range h, fQ i := Finset.sum_nonneg fun i _ => hq i
    linarith
  rw [Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum R s.2.1,
    Ch02.homogenizationErrorFinite_infinity_two_sq_eq_tsum Q hn s.2.1]
  have hceq : c = Real.rpow 3 (2 * s.1 * (Int.toNat (n-k) : ℝ)) := by
    dsimp [c, h]
    congr 1
    ring
  rw [← hceq]
  change (∑' j, fR j) ≤ c * (∑' j, fQ j)
  calc
    ∑' j, fR j ≤ ∑' j, c*fQ (j+h) := hmain
    _ = c * ∑' j, fQ (j+h) := by simpa using Summable.tsum_mul_left c htail
    _ ≤ c * ∑' j, fQ j := mul_le_mul_of_nonneg_left htail_le hc

/-- Exact shifted localization of a descendant on-cube `q = 2` error by the
canonical parent-truncated error. -/
theorem rootPointwise_descendant_infinity_two_le_parent
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q)) (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    {R : TriadicCube d} {k : ℤ} (hkn : k ≤ n) (hR : R ∈ descendantsAtScale Q k)
    (s : FractionalOrder) :
    ENNReal.ofReal (Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 2)
      (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) ≤
      ENNReal.ofReal (Real.rpow 3 (s.1 * (Int.toNat (n-k) : ℝ))) *
        Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar Q n hn a sigma0 hsigma0 s := by
  rw [parentTruncatedHomogenizationErrorInfinityTwoScalar_eq_ofReal]
  have hreal := rootPointwise_descendant_infinity_two_sq_le_parent_sq
    Q n hn a sigma0 hkn hR s
  let x := Ch02.HomogenizationErrorOnCube R s.1 .infinity (.finite 2)
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let y := Ch02.HomogenizationErrorFinite Q n s.1 .infinity 2
    (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)
  let c := Real.rpow 3 (s.1 * (Int.toNat (n-k) : ℝ))
  have hx : 0 ≤ x := by
    unfold x Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
      Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    refine tsum_nonneg fun j => mul_nonneg ?_ ?_
    · exact rootPointwise_weight_two_nonneg s j
    · exact Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg R (by omega)
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) _
  have hy : 0 ≤ y := by
    unfold y Ch02.HomogenizationErrorFinite
    apply Real.rpow_nonneg
    refine tsum_nonneg fun j => mul_nonneg ?_ ?_
    · exact rootPointwise_weight_two_nonneg s j
    · exact Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q (by omega)
          (rootPointwiseCoeffFamily Q a) (scalarMatrix (d := d) sigma0)) _
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hcSq : c ^ 2 = Real.rpow 3 (2 * s.1 * (Int.toNat (n-k) : ℝ)) := by
    rw [show c ^ 2 = Real.rpow c (2 : ℝ) by simp]
    dsimp [c]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (3:ℝ))]
    congr 1
    ring
  change ENNReal.ofReal x ≤ ENNReal.ofReal c * ENNReal.ofReal y
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hsq : x ^ 2 ≤ (c * y) ^ 2 := by
    rw [mul_pow, hcSq]
    simpa [x, y, c, mul_assoc] using hreal
  by_contra h
  have hlt : c * y < x := lt_of_not_ge h
  have hcy : 0 ≤ c * y := mul_nonneg hc hy
  have hpos : 0 < (x - c * y) * (x + c * y) := by
    apply mul_pos (sub_pos.mpr hlt)
    nlinarith
  nlinarith


end

end ABK26
end Ch03
end Book
end Homogenization
