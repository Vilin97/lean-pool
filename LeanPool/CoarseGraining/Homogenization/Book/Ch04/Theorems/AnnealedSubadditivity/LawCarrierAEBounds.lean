/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAveragesDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.StationaryExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions

public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner

/-! # Law Carrier AEBounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace RestrictionLawCarrier

/-- The deterministic descendant-average comparison for scalar response
observables holds almost surely under a law carrier. -/
theorem restrictionResponseJObservableCubeSet_le_descendantsAverage_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {n m : ℤ} (hnm : n ≤ m) (p q : Vec d) :
    restrictionResponseJObservableCubeSet (originCube d m) p q ≤ᵐ[P]
      fun a : RegCoeffField d =>
        descendantsAverage (originCube d m) (Int.toNat (m - n))
          (fun R => restrictionResponseJObservableCubeSet R p q a) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact
    restrictionResponseJObservableCubeSet_le_descendantsAverage_of_aelocallyUniformlyEllipticField
      ha hnm p q

/-- The deterministic descendant-average comparison for coarse block matrices on
an arbitrary triadic cube holds almost surely under a law carrier. -/
theorem coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) :
    ∀ᵐ a ∂P,
      BlockMatLoewnerLE
        (coarseBlockMatrix (cubeSet Q) a.toFun)
        (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  exact
    coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
      ha Q hk

/-- The deterministic descendant-average comparison for coarse block matrices
holds almost surely under a law carrier. -/
theorem coarseBlockMatrix_le_descendantsAverageBlockMat_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {n m : ℤ} (hnm : n ≤ m) :
    ∀ᵐ a ∂P,
      BlockMatLoewnerLE
        (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun)
        (descendantsAverageBlockMat (originCube d m) (Int.toNat (m - n))
          (fun R => coarseBlockMatrix (cubeSet R) a.toFun)) := by
  simpa using!
    hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae
      (originCube d m) hnm

/-- Diagonal upper-left block positive excess is controlled by the centered
descendant average of the corresponding entry observable. -/
theorem coarseBlockMatrix_upperLeft_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (i : Fin d) :
    (fun a : RegCoeffField d =>
      max
        ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i -
          ∫ b, (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).upperLeft i i ∂P)
        0) ≤ᵐ[P]
      fun a =>
        |restrictionCenteredDescendantAverageOnCube P Q k
          (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i i) a| := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => (coarseBlockMatrix U a.toFun).upperLeft i i
  let μ0 : ℝ := ∫ b, X (cubeSet (originCube d k)) b ∂P
  filter_upwards [hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae Q hk]
    with a hSub
  have hEntryBlock := blockMatLoewnerLE_upperLeft_apply hSub i
  have hEntry :
      (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i ≤
        restrictionDescendantAverageOnCube Q k X a := by
    have hAvg :
        (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).upperLeft i i =
          restrictionDescendantAverageOnCube Q k X a := by
      simp [X, restrictionDescendantAverageOnCube, descendantsAverageBlockMat,
        descendantsAverageMat, descendantsAverage,
        descendantsAtScale_eq_descendantsAtDepth Q hk]
    simpa [hAvg] using hEntryBlock
  have hCenter :
      restrictionCenteredDescendantAverageOnCube P Q k X a =
        restrictionDescendantAverageOnCube Q k X a - μ0 := by
    exact congrFun
      (restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
        (P := P) (Q := Q) (n := k) hk X) a
  have hPoint :
      max ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i - μ0) 0 ≤
        |restrictionCenteredDescendantAverageOnCube P Q k X a| := by
    have hle :
        (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i - μ0 ≤
          restrictionDescendantAverageOnCube Q k X a - μ0 := by
      linarith
    have hmax :
        max ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i - μ0) 0 ≤
          max (restrictionDescendantAverageOnCube Q k X a - μ0) 0 :=
      max_le_max hle le_rfl
    have hmax_abs :
        max (restrictionDescendantAverageOnCube Q k X a - μ0) 0 ≤
          |restrictionDescendantAverageOnCube Q k X a - μ0| :=
      max_le (le_abs_self _) (abs_nonneg _)
    simpa [hCenter] using hmax.trans hmax_abs
  simpa [X, μ0] using hPoint

/-- Operator-norm upper-left positive excess is controlled by the entrywise
centered descendant-average fluctuations.  The norm here is
`Ch02.matrixNorm`, i.e. the matrix operator norm. -/
theorem coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).upperLeft i j ∂P) :
    (fun a : RegCoeffField d =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
          Ch02.matrixNorm center)
        0) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField,
      hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae Q hk]
    with a ha hSub
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let A : Mat d := (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft
  let B : Mat d :=
    (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
      (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).upperLeft
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hApsd : A.PosSemidef := by
    change ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft).PosSemidef
    rw [hEq]
    exact Ch02.bCoarse_posSemidef (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hAB : MatLoewnerLE A B := by
    simpa [A, B] using matLoewnerLE_upperLeft_of_blockMatLoewnerLE hSub
  have hBpsd : B.PosSemidef := by
    change
      ((descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
        (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).upperLeft).PosSemidef
    change
      (descendantsAverageMat Q (Int.toNat (Q.scale - k))
        (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)).PosSemidef
    refine descendantsAverageMat_posSemidef ?_
    intro R hR
    have hEqR :
        coarseBlockMatrix (cubeSet R) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
      simpa [F] using
        RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha R
    rw [hEqR]
    exact Ch02.bCoarse_posSemidef (Ch02.cubeDomain R) (F.coeffOn R)
  have hNorm :
      Ch02.matrixNorm A ≤
        Ch02.matrixNorm center +
          ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| := by
    calc
      Ch02.matrixNorm A ≤
          Ch02.matrixNorm center + ∑ i : Fin d, ∑ j : Fin d, |B i j - center i j| :=
        Ch02.matrixNorm_le_center_add_sum_abs_sub_entries_of_matLoewnerLE
          hApsd hBpsd hAB
      _ =
          Ch02.matrixNorm center +
            ∑ i : Fin d, ∑ j : Fin d,
              |restrictionCenteredDescendantAverageOnCube P Q k
                (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _hi
        refine Finset.sum_congr rfl ?_
        intro j _hj
        let X : Set (Vec d) → RegCoeffField d → ℝ :=
          fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j
        have hAvg :
            B i j = restrictionDescendantAverageOnCube Q k X a := by
          simp [B, X, restrictionDescendantAverageOnCube, descendantsAverageBlockMat,
            descendantsAverageMat, descendantsAverage,
            descendantsAtScale_eq_descendantsAtDepth Q hk]
        have hCentered :
            restrictionCenteredDescendantAverageOnCube P Q k X a =
              restrictionDescendantAverageOnCube Q k X a - center i j := by
          calc
            restrictionCenteredDescendantAverageOnCube P Q k X a =
                restrictionDescendantAverageOnCube Q k X a -
                  ∫ b, X (cubeSet (originCube d k)) b ∂P := by
                  exact congrFun
                    (restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
                      (P := P) (Q := Q) (n := k) hk X) a
            _ = restrictionDescendantAverageOnCube Q k X a - center i j := by
                  exact congrArg
                    (fun c => restrictionDescendantAverageOnCube Q k X a - c)
                    (hcenter i j).symm
        rw [hAvg, ← hCentered]
  have hsum_nonneg :
      0 ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsub :
      Ch02.matrixNorm A - Ch02.matrixNorm center ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| := by
    linarith
  exact max_le hsub hsum_nonneg

/-- Finite-parent version of the upper-left operator-norm positive-excess
domination.  This is the clean raw deterministic input for the Ch4
large-scale fluctuation theorem: no representative observable is exposed. -/
theorem coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {k : ℤ}
    (hparent_scale : ∀ Q ∈ parents, k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).upperLeft i j ∂P) :
    (fun a : RegCoeffField d =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
              Ch02.matrixNorm center)
            0)) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          parents.sup' hparents
            (fun Q =>
              |restrictionCenteredDescendantAverageOnCube P Q k
                (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a|) := by
  have hPoint :
      ∀ᵐ a ∂P, ∀ Q, Q ∈ parents →
        max
          (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
            Ch02.matrixNorm center)
          0 ≤
          ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| :=
    ae_forall_mem_finset (P := P) parents fun Q hQ =>
      hP.coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
        Q (hparent_scale Q hQ) center hcenter
  filter_upwards [hPoint] with a hPoint_a
  refine Finset.sup'_le hparents _ ?_
  intro Q hQ
  calc
    max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
          Ch02.matrixNorm center)
        0
        ≤ ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a| :=
          hPoint_a Q hQ
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          parents.sup' hparents
            (fun Q' =>
              |restrictionCenteredDescendantAverageOnCube P Q' k
                (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a|) := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ =>
              Finset.le_sup'
                (f := fun Q' =>
                  |restrictionCenteredDescendantAverageOnCube P Q' k
                    (fun U a => (coarseBlockMatrix U a.toFun).upperLeft i j) a|) hQ

/-- Representative version of
`coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae`.
Each entry may be replaced by an a.e.-equal local/measurable representative
before applying the probabilistic partition-average theorem. -/
theorem coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_rep_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).upperLeft i j ∂P)
    (Y : Fin d → Fin d → Set (Vec d) → RegCoeffField d → ℝ)
    (hOrigin :
      ∀ i j : Fin d,
        (fun a : RegCoeffField d =>
          (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun).upperLeft i j) =ᵐ[P]
            Y i j (cubeSet (originCube d k)))
    (hDesc :
      ∀ i j : Fin d, ∀ R, R ∈ descendantsAtScale Q k →
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft i j) =ᵐ[P]
          Y i j (cubeSet R)) :
    (fun a : RegCoeffField d =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft -
          Ch02.matrixNorm center)
        0) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k (Y i j) a| := by
  let X : Fin d → Fin d → Set (Vec d) → RegCoeffField d → ℝ :=
    fun i j U a => (coarseBlockMatrix U a.toFun).upperLeft i j
  have hRaw :=
    hP.coarseBlockMatrix_upperLeft_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
      Q hk center hcenter
  have hCentered :
      ∀ i j : Fin d,
        restrictionCenteredDescendantAverageOnCube P Q k (X i j) =ᵐ[P]
          restrictionCenteredDescendantAverageOnCube P Q k (Y i j) := by
    intro i j
    exact restrictionCenteredDescendantAverageOnCube_ae_eq_of_ae_eq
      (P := P) (Q := Q) (n := k) (X := X i j) (Y := Y i j)
      (by simpa [X] using hOrigin i j)
      (by intro R hR; simpa [X] using hDesc i j R hR)
  have hAll :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        restrictionCenteredDescendantAverageOnCube P Q k (X i j) a =
          restrictionCenteredDescendantAverageOnCube P Q k (Y i j) a :=
    by
      filter_upwards
        [ae_forall_mem_finset_nested (P := P) Finset.univ
          (fun _ : Fin d => Finset.univ)
          (fun i _hi j _hj => hCentered i j)] with a h i j
      exact h i (by simp) j (by simp)
  filter_upwards [hRaw, hAll] with a hle hEq
  refine hle.trans_eq ?_
  congr 1
  ext i
  congr 1
  ext j
  rw [hEq i j]

/-- Same upper-left diagonal positive-excess control, after replacing the raw
coarse-block entry by an a.e.-equal representative.  This is the form consumed
by local/measurable representative arguments. -/
theorem coarseBlockMatrix_upperLeft_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_rep_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (i : Fin d)
    (Y : Set (Vec d) → RegCoeffField d → ℝ)
    (hOrigin :
      (fun a : RegCoeffField d =>
        (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun).upperLeft i i) =ᵐ[P]
          Y (cubeSet (originCube d k)))
    (hDesc :
      ∀ R, R ∈ descendantsAtScale Q k →
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft i i) =ᵐ[P]
          Y (cubeSet R)) :
    (fun a : RegCoeffField d =>
      max
        ((coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i i -
          ∫ b, (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).upperLeft i i ∂P)
        0) ≤ᵐ[P]
      fun a => |restrictionCenteredDescendantAverageOnCube P Q k Y a| := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => (coarseBlockMatrix U a.toFun).upperLeft i i
  have hRaw :=
    hP.coarseBlockMatrix_upperLeft_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_ae
      Q hk i
  have hCentered :
      restrictionCenteredDescendantAverageOnCube P Q k X =ᵐ[P]
        restrictionCenteredDescendantAverageOnCube P Q k Y :=
    restrictionCenteredDescendantAverageOnCube_ae_eq_of_ae_eq
      (P := P) (Q := Q) (n := k) (X := X) (Y := Y)
      (by simpa [X] using hOrigin)
      (by intro R hR; simpa [X] using hDesc R hR)
  filter_upwards [hRaw, hCentered] with a hle hEq
  simpa [X, hEq] using hle

/-- Diagonal lower-right block positive excess is controlled by the centered
descendant average of the corresponding entry observable. -/
theorem coarseBlockMatrix_lowerRight_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (i : Fin d) :
    (fun a : RegCoeffField d =>
      max
        ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i -
          ∫ b, (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).lowerRight i i ∂P)
        0) ≤ᵐ[P]
      fun a =>
        |restrictionCenteredDescendantAverageOnCube P Q k
          (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i i) a| := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => (coarseBlockMatrix U a.toFun).lowerRight i i
  let μ0 : ℝ := ∫ b, X (cubeSet (originCube d k)) b ∂P
  filter_upwards [hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae Q hk]
    with a hSub
  have hEntryBlock := blockMatLoewnerLE_lowerRight_apply hSub i
  have hEntry :
      (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i ≤
        restrictionDescendantAverageOnCube Q k X a := by
    have hAvg :
        (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
            (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).lowerRight i i =
          restrictionDescendantAverageOnCube Q k X a := by
      simp [X, restrictionDescendantAverageOnCube, descendantsAverageBlockMat,
        descendantsAverageMat, descendantsAverage,
        descendantsAtScale_eq_descendantsAtDepth Q hk]
    simpa [hAvg] using hEntryBlock
  have hCenter :
      restrictionCenteredDescendantAverageOnCube P Q k X a =
        restrictionDescendantAverageOnCube Q k X a - μ0 := by
    exact congrFun
      (restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
        (P := P) (Q := Q) (n := k) hk X) a
  have hPoint :
      max ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i - μ0) 0 ≤
        |restrictionCenteredDescendantAverageOnCube P Q k X a| := by
    have hle :
        (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i - μ0 ≤
          restrictionDescendantAverageOnCube Q k X a - μ0 := by
      linarith
    have hmax :
        max ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i - μ0) 0 ≤
          max (restrictionDescendantAverageOnCube Q k X a - μ0) 0 :=
      max_le_max hle le_rfl
    have hmax_abs :
        max (restrictionDescendantAverageOnCube Q k X a - μ0) 0 ≤
          |restrictionDescendantAverageOnCube Q k X a - μ0| :=
      max_le (le_abs_self _) (abs_nonneg _)
    simpa [hCenter] using hmax.trans hmax_abs
  simpa [X, μ0] using hPoint

/-- Operator-norm lower-right positive excess is controlled by the entrywise
centered descendant-average fluctuations.  The norm here is
`Ch02.matrixNorm`, i.e. the matrix operator norm. -/
theorem coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).lowerRight i j ∂P) :
    (fun a : RegCoeffField d =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
          Ch02.matrixNorm center)
        0) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField,
      hP.coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_ae Q hk]
    with a ha hSub
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let A : Mat d := (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight
  let B : Mat d :=
    (descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
      (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).lowerRight
  have hEq :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha Q
  have hApsd : A.PosSemidef := by
    change ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight).PosSemidef
    rw [hEq]
    exact (Ch02.sigmaStarInvCoarse_posDef (Ch02.cubeDomain Q) (F.coeffOn Q)).posSemidef
  have hAB : MatLoewnerLE A B := by
    simpa [A, B] using matLoewnerLE_lowerRight_of_blockMatLoewnerLE hSub
  have hBpsd : B.PosSemidef := by
    change
      ((descendantsAverageBlockMat Q (Int.toNat (Q.scale - k))
        (fun R => coarseBlockMatrix (cubeSet R) a.toFun)).lowerRight).PosSemidef
    change
      (descendantsAverageMat Q (Int.toNat (Q.scale - k))
        (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)).PosSemidef
    refine descendantsAverageMat_posSemidef ?_
    intro R hR
    have hEqR :
        coarseBlockMatrix (cubeSet R) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
      simpa [F] using
        RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          ha R
    rw [hEqR]
    exact (Ch02.sigmaStarInvCoarse_posDef (Ch02.cubeDomain R) (F.coeffOn R)).posSemidef
  have hNorm :
      Ch02.matrixNorm A ≤
        Ch02.matrixNorm center +
          ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| := by
    calc
      Ch02.matrixNorm A ≤
          Ch02.matrixNorm center + ∑ i : Fin d, ∑ j : Fin d, |B i j - center i j| :=
        Ch02.matrixNorm_le_center_add_sum_abs_sub_entries_of_matLoewnerLE
          hApsd hBpsd hAB
      _ =
          Ch02.matrixNorm center +
            ∑ i : Fin d, ∑ j : Fin d,
              |restrictionCenteredDescendantAverageOnCube P Q k
                (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _hi
        refine Finset.sum_congr rfl ?_
        intro j _hj
        let X : Set (Vec d) → RegCoeffField d → ℝ :=
          fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j
        have hAvg :
            B i j = restrictionDescendantAverageOnCube Q k X a := by
          simp [B, X, restrictionDescendantAverageOnCube, descendantsAverageBlockMat,
            descendantsAverageMat, descendantsAverage,
            descendantsAtScale_eq_descendantsAtDepth Q hk]
        have hCentered :
            restrictionCenteredDescendantAverageOnCube P Q k X a =
              restrictionDescendantAverageOnCube Q k X a - center i j := by
          calc
            restrictionCenteredDescendantAverageOnCube P Q k X a =
                restrictionDescendantAverageOnCube Q k X a -
                  ∫ b, X (cubeSet (originCube d k)) b ∂P := by
                  exact congrFun
                    (restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
                      (P := P) (Q := Q) (n := k) hk X) a
            _ = restrictionDescendantAverageOnCube Q k X a - center i j := by
                  exact congrArg
                    (fun c => restrictionDescendantAverageOnCube Q k X a - c)
                    (hcenter i j).symm
        rw [hAvg, ← hCentered]
  have hsum_nonneg :
      0 ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsub :
      Ch02.matrixNorm A - Ch02.matrixNorm center ≤
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k
            (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| := by
    linarith
  exact max_le hsub hsum_nonneg

/-- Finite-parent version of the lower-right operator-norm positive-excess
domination.  This is the clean raw deterministic input for the Ch4
large-scale fluctuation theorem: no representative observable is exposed. -/
theorem coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_finsetSup_le_sum_finsetSup_abs_restrictionCenteredDescendantAverageOnCube_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    {parents : Finset (TriadicCube d)} (hparents : parents.Nonempty)
    {k : ℤ}
    (hparent_scale : ∀ Q ∈ parents, k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).lowerRight i j ∂P) :
    (fun a : RegCoeffField d =>
      parents.sup' hparents
        (fun Q =>
          max
            (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
              Ch02.matrixNorm center)
            0)) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          parents.sup' hparents
            (fun Q =>
              |restrictionCenteredDescendantAverageOnCube P Q k
                (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a|) := by
  have hPoint :
      ∀ᵐ a ∂P, ∀ Q, Q ∈ parents →
        max
          (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
            Ch02.matrixNorm center)
          0 ≤
          ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| :=
    ae_forall_mem_finset (P := P) parents fun Q hQ =>
      hP.coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
        Q (hparent_scale Q hQ) center hcenter
  filter_upwards [hPoint] with a hPoint_a
  refine Finset.sup'_le hparents _ ?_
  intro Q hQ
  calc
    max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
          Ch02.matrixNorm center)
        0
        ≤ ∑ i : Fin d, ∑ j : Fin d,
            |restrictionCenteredDescendantAverageOnCube P Q k
              (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a| :=
          hPoint_a Q hQ
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          parents.sup' hparents
            (fun Q' =>
              |restrictionCenteredDescendantAverageOnCube P Q' k
                (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a|) := by
          exact Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ =>
              Finset.le_sup'
                (f := fun Q' =>
                  |restrictionCenteredDescendantAverageOnCube P Q' k
                    (fun U a => (coarseBlockMatrix U a.toFun).lowerRight i j) a|) hQ

/-- Representative version of
`coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae`.
Each entry may be replaced by an a.e.-equal local/measurable representative
before applying the probabilistic partition-average theorem. -/
theorem coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_rep_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (center : Mat d)
    (hcenter :
      ∀ i j : Fin d,
        center i j =
          ∫ b,
            (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).lowerRight i j ∂P)
    (Y : Fin d → Fin d → Set (Vec d) → RegCoeffField d → ℝ)
    (hOrigin :
      ∀ i j : Fin d,
        (fun a : RegCoeffField d =>
          (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun).lowerRight i j) =ᵐ[P]
            Y i j (cubeSet (originCube d k)))
    (hDesc :
      ∀ i j : Fin d, ∀ R, R ∈ descendantsAtScale Q k →
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight i j) =ᵐ[P]
          Y i j (cubeSet R)) :
    (fun a : RegCoeffField d =>
      max
        (Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
          Ch02.matrixNorm center)
        0) ≤ᵐ[P]
      fun a =>
        ∑ i : Fin d, ∑ j : Fin d,
          |restrictionCenteredDescendantAverageOnCube P Q k (Y i j) a| := by
  let X : Fin d → Fin d → Set (Vec d) → RegCoeffField d → ℝ :=
    fun i j U a => (coarseBlockMatrix U a.toFun).lowerRight i j
  have hRaw :=
    hP.coarseBlockMatrix_lowerRight_matrixNorm_positiveExcess_le_sum_abs_restrictionCenteredDescendantAverageOnCube_ae
      Q hk center hcenter
  have hCentered :
      ∀ i j : Fin d,
        restrictionCenteredDescendantAverageOnCube P Q k (X i j) =ᵐ[P]
          restrictionCenteredDescendantAverageOnCube P Q k (Y i j) := by
    intro i j
    exact restrictionCenteredDescendantAverageOnCube_ae_eq_of_ae_eq
      (P := P) (Q := Q) (n := k) (X := X i j) (Y := Y i j)
      (by simpa [X] using hOrigin i j)
      (by intro R hR; simpa [X] using hDesc i j R hR)
  have hAll :
      ∀ᵐ a ∂P, ∀ i j : Fin d,
        restrictionCenteredDescendantAverageOnCube P Q k (X i j) a =
          restrictionCenteredDescendantAverageOnCube P Q k (Y i j) a :=
    by
      filter_upwards
        [ae_forall_mem_finset_nested (P := P) Finset.univ
          (fun _ : Fin d => Finset.univ)
          (fun i _hi j _hj => hCentered i j)] with a h i j
      exact h i (by simp) j (by simp)
  filter_upwards [hRaw, hAll] with a hle hEq
  refine hle.trans_eq ?_
  congr 1
  ext i
  congr 1
  ext j
  rw [hEq i j]

/-- Same lower-right diagonal positive-excess control, after replacing the raw
coarse-block entry by an a.e.-equal representative. -/
theorem coarseBlockMatrix_lowerRight_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_rep_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale) (i : Fin d)
    (Y : Set (Vec d) → RegCoeffField d → ℝ)
    (hOrigin :
      (fun a : RegCoeffField d =>
        (coarseBlockMatrix (cubeSet (originCube d k)) a.toFun).lowerRight i i) =ᵐ[P]
          Y (cubeSet (originCube d k)))
    (hDesc :
      ∀ R, R ∈ descendantsAtScale Q k →
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight i i) =ᵐ[P]
          Y (cubeSet R)) :
    (fun a : RegCoeffField d =>
      max
        ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i i -
          ∫ b, (coarseBlockMatrix (cubeSet (originCube d k)) b.toFun).lowerRight i i ∂P)
        0) ≤ᵐ[P]
      fun a => |restrictionCenteredDescendantAverageOnCube P Q k Y a| := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => (coarseBlockMatrix U a.toFun).lowerRight i i
  have hRaw :=
    hP.coarseBlockMatrix_lowerRight_apply_positiveExcess_le_abs_restrictionCenteredDescendantAverageOnCube_ae
      Q hk i
  have hCentered :
      restrictionCenteredDescendantAverageOnCube P Q k X =ᵐ[P]
        restrictionCenteredDescendantAverageOnCube P Q k Y :=
    restrictionCenteredDescendantAverageOnCube_ae_eq_of_ae_eq
      (P := P) (Q := Q) (n := k) (X := X) (Y := Y)
      (by simpa [X] using hOrigin)
      (by intro R hR; simpa [X] using hDesc R hR)
  filter_upwards [hRaw, hCentered] with a hle hEq
  simpa [X, hEq] using hle


end RestrictionLawCarrier

end

end Ch04
end Book
end Homogenization
