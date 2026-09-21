/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuationsAEMeasurable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockExpectations
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.WrapAround
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Block Response Concentration -/

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem IsAEEllipticFieldOn.adjointCoeffField {d : ℕ} {lam Lam : ℝ}
    {U : Set (Vec d)} {a : CoeffField d}
    (h : IsAEEllipticFieldOn lam Lam U a) :
    IsAEEllipticFieldOn lam Lam U (adjointCoeffField a) := by
  refine ⟨h.measurableSet, ?_, ?_⟩
  · intro i j
    refine (h.aestronglyMeasurable_restrictCoeffField_apply j i).congr ?_
    exact Filter.Eventually.of_forall (by
      intro x
      by_cases hx : x ∈ U
      · simp [restrictCoeffField, Homogenization.adjointCoeffField,
          Homogenization.matTranspose, hx]
      · simp [restrictCoeffField, hx])
  · exact h.ae_isEllipticMatrix.mono fun x hx => by
      simpa [adjointCoeffField] using! isEllipticMatrix_transpose hx

/-- The underlying field of the carrier adjoint is the raw field adjoint. -/
theorem adjointReg_toFun {d : ℕ} (a : RegCoeffField d) :
    (adjointReg a).toFun = adjointCoeffField a.toFun := rfl

/-- Carrier a.e.-ellipticity transports under the carrier adjoint endomorphism:
the transpose preserves the local uniform elliptic bounds. -/
theorem AELocallyUniformlyEllipticField.adjointReg {d : ℕ}
    {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a) :
    AELocallyUniformlyEllipticField (Homogenization.adjointReg a) := by
  intro Q
  rcases ha Q with ⟨lam, Lam, hlam, hle, hEll⟩
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  have hEll' : IsAEEllipticFieldOn lam Lam (openCubeSet Q) a.toFun := hEll
  show IsAEEllipticFieldOn lam Lam (openCubeSet Q) (Homogenization.adjointReg a).toFun
  rw [adjointReg_toFun]
  exact IsAEEllipticFieldOn.adjointCoeffField hEll'

private theorem isRestrictionLocalRandomVariable_fullBlockMat_of_entries
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {X : RegCoeffField d → FullBlockMat d}
    (hX :
      ∀ α β : BlockCoord d,
        IsRestrictionLocalRandomVariable U hU (fun a => X a α β)) :
    IsRestrictionLocalRandomVariable U hU X := by
  change @Measurable (RegCoeffField d) (FullBlockMat d) (RestrictionSigmaR U hU) _ X
  refine (@measurable_pi_iff (RegCoeffField d) (BlockCoord d)
    (fun _ => BlockCoord d → ℝ) (RestrictionSigmaR U hU) (fun _ => inferInstance) X).2
    fun α => ?_
  refine (@measurable_pi_iff (RegCoeffField d) (BlockCoord d)
    (fun _ => ℝ) (RestrictionSigmaR U hU) (fun _ => inferInstance) (fun a => X a α)).2
    fun β => ?_
  exact hX α β

theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperRight_apply_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : RegCoeffField d → ℝ,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j)
          =ᵐ[P] Y := by
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q ((Pi.single i 1, 0) + (0, Pi.single j 1)) with
    ⟨Ysum, hYsum_local, hYsum_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (Pi.single i 1, 0) with ⟨Yi, hYi_local, hYi_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (0, Pi.single j 1) with ⟨Yj, hYj_local, hYj_eq⟩
  refine ⟨fun a => Ysum a - Yi a - Yj a,
    (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
  filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
  calc
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperRight i j =
        Mu (cubeSet Q) ((Pi.single i 1, 0) + (0, Pi.single j 1)) a.toFun -
          Mu (cubeSet Q) (Pi.single i 1, 0) a.toFun -
          Mu (cubeSet Q) (0, Pi.single j 1) a.toFun := by
          simp [coarseBlockMatrix_upperRight_apply]
    _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerLeft_apply_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (i j : Fin d) :
    ∃ Y : RegCoeffField d → ℝ,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j)
          =ᵐ[P] Y := by
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q ((0, Pi.single i 1) + (Pi.single j 1, 0)) with
    ⟨Ysum, hYsum_local, hYsum_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (0, Pi.single i 1) with ⟨Yi, hYi_local, hYi_eq⟩
  rcases hP.exists_isRestrictionLocalRandomVariable_ae_eq_Mu_cubeSet
      Q (Pi.single j 1, 0) with ⟨Yj, hYj_local, hYj_eq⟩
  refine ⟨fun a => Ysum a - Yi a - Yj a,
    (hYsum_local.sub hYi_local).sub hYj_local, ?_⟩
  filter_upwards [hYsum_eq, hYi_eq, hYj_eq] with a hsum hi hj
  calc
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j =
        Mu (cubeSet Q) ((0, Pi.single i 1) + (Pi.single j 1, 0)) a.toFun -
          Mu (cubeSet Q) (0, Pi.single i 1) a.toFun -
          Mu (cubeSet Q) (Pi.single j 1, 0) a.toFun := by
          simp [coarseBlockMatrix_lowerLeft_apply]
    _ = Ysum a - Yi a - Yj a := by rw [hsum, hi, hj]

theorem exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) :
    ∃ Y : RegCoeffField d → FullBlockMat d,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
          =ᵐ[P] Y := by
  classical
  let entry_exists : ∀ α β : BlockCoord d,
      ∃ Y : RegCoeffField d → ℝ,
        IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
          (fun a : RegCoeffField d =>
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β) =ᵐ[P] Y := by
    intro α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat] using
              hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperLeft_apply_cubeSet Q i j
        | inr j =>
            simpa [toFullBlockMat] using
              exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_upperRight_apply_cubeSet
                hP Q i j
    | inr i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat] using
              exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerLeft_apply_cubeSet
                hP Q i j
        | inr j =>
            simpa [toFullBlockMat] using
              hP.exists_isRestrictionLocalRandomVariable_ae_eq_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
  let Yentry : BlockCoord d → BlockCoord d → RegCoeffField d → ℝ :=
    fun α β => Classical.choose (entry_exists α β)
  let Y : RegCoeffField d → FullBlockMat d := fun a α β => Yentry α β a
  refine ⟨Y, ?_, ?_⟩
  · refine isRestrictionLocalRandomVariable_fullBlockMat_of_entries (measurableSet_cubeSet Q) ?_
    intro α β
    exact (Classical.choose_spec (entry_exists α β)).1
  · have hentry :
        ∀ α β : BlockCoord d,
          (fun a : RegCoeffField d =>
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β) =ᵐ[P]
              fun a => Y a α β := by
      intro α β
      exact (Classical.choose_spec (entry_exists α β)).2
    have hall :
        ∀ᵐ a ∂P,
          ∀ α β : BlockCoord d,
            toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) α β = Y a α β := by
      rw [Filter.eventually_all]
      intro α
      rw [Filter.eventually_all]
      intro β
      exact hentry α β
    filter_upwards [hall] with a ha
    ext α β
    exact ha α β

noncomputable def blockJObservableCubeSetBlockVec {d : ℕ}
    (Q : TriadicCube d) (P Qv : BlockVec d) : RegCoeffField d → ℝ :=
  blockJObservableCubeSet Q P.1 Qv.2 P.2 Qv.1

theorem blockJObservableCubeSetBlockVec_nonneg {d : ℕ}
    (Q : TriadicCube d) (P Qv : BlockVec d) (a : RegCoeffField d) :
    0 ≤ blockJObservableCubeSetBlockVec Q P Qv a := by
  rcases P with ⟨p, q⟩
  rcases Qv with ⟨qStar, pStar⟩
  dsimp [blockJObservableCubeSetBlockVec]
  have h1 := restrictionResponseJObservableCubeSet_nonneg Q (p - pStar) (qStar - q) a
  have h2 := restrictionResponseJObservableCubeSet_nonneg Q (pStar + p) (qStar + q) (adjointReg a)
  change 0 ≤
    (1 / 2 : ℝ) * restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a +
      (1 / 2 : ℝ) *
        restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointReg a)
  nlinarith

theorem blockJObservableCubeSetBlockVec_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (P Qv : BlockVec d) :
    blockJObservableCubeSetBlockVec Q P Qv a ≤
      descendantsAverage Q (Int.toNat (Q.scale - k))
        (fun R => blockJObservableCubeSetBlockVec R P Qv a) := by
  rcases P with ⟨p, q⟩
  rcases Qv with ⟨qStar, pStar⟩
  let j : ℕ := Int.toNat (Q.scale - k)
  let R₁ : TriadicCube d → ℝ :=
    fun R => restrictionResponseJObservableCubeSet R (p - pStar) (qStar - q) a
  let R₂ : TriadicCube d → ℝ :=
    fun R => restrictionResponseJObservableCubeSet R (pStar + p) (qStar + q) (adjointReg a)
  have h1 :=
    restrictionResponseJObservableCubeSet_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
      (a := a) ha Q hk (p - pStar) (qStar - q)
  have h2 :=
    restrictionResponseJObservableCubeSet_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
      (a := adjointReg a) ha.adjointReg Q hk
      (pStar + p) (qStar + q)
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hsum :
      (1 / 2 : ℝ) * restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointReg a) ≤
      (1 / 2 : ℝ) * descendantsAverage Q j R₁ +
        (1 / 2 : ℝ) * descendantsAverage Q j R₂ := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left (by simpa [j, R₁] using h1) hhalf_nonneg)
      (mul_le_mul_of_nonneg_left (by simpa [j, R₂] using h2) hhalf_nonneg)
  have havg :
      descendantsAverage Q j
          (fun R => blockJObservableCubeSetBlockVec R (p, q) (qStar, pStar) a) =
        (1 / 2 : ℝ) * descendantsAverage Q j R₁ +
          (1 / 2 : ℝ) * descendantsAverage Q j R₂ := by
    let D : Finset (TriadicCube d) := descendantsAtDepth Q j
    change
      (D.card : ℝ)⁻¹ *
          ∑ R ∈ D, ((1 / 2 : ℝ) * R₁ R + (1 / 2 : ℝ) * R₂ R) =
        (1 / 2 : ℝ) * ((D.card : ℝ)⁻¹ * ∑ R ∈ D, R₁ R) +
          (1 / 2 : ℝ) * ((D.card : ℝ)⁻¹ * ∑ R ∈ D, R₂ R)
    calc
      (D.card : ℝ)⁻¹ *
          ∑ R ∈ D, ((1 / 2 : ℝ) * R₁ R + (1 / 2 : ℝ) * R₂ R)
          =
        (D.card : ℝ)⁻¹ *
          ((∑ R ∈ D, (1 / 2 : ℝ) * R₁ R) +
            (∑ R ∈ D, (1 / 2 : ℝ) * R₂ R)) := by
            rw [Finset.sum_add_distrib]
      _ =
        (D.card : ℝ)⁻¹ *
          ((1 / 2 : ℝ) * (∑ R ∈ D, R₁ R) +
            (1 / 2 : ℝ) * (∑ R ∈ D, R₂ R)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
      _ =
        (1 / 2 : ℝ) * ((D.card : ℝ)⁻¹ * ∑ R ∈ D, R₁ R) +
          (1 / 2 : ℝ) * ((D.card : ℝ)⁻¹ * ∑ R ∈ D, R₂ R) := by
            ring
  calc
    blockJObservableCubeSetBlockVec Q (p, q) (qStar, pStar) a
        =
      (1 / 2 : ℝ) * restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q) (adjointReg a) := by
          rfl
    _ ≤ (1 / 2 : ℝ) * descendantsAverage Q j R₁ +
          (1 / 2 : ℝ) * descendantsAverage Q j R₂ := hsum
    _ = descendantsAverage Q j
          (fun R => blockJObservableCubeSetBlockVec R (p, q) (qStar, pStar) a) := havg.symm

theorem doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (P Qv : BlockVec d) :
    Ch02.doubledResponseJ (Ch02.cubeDomain Q)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        P Qv =
      blockJObservableCubeSetBlockVec Q P Qv a := by
  rcases P with ⟨p, q⟩
  rcases Qv with ⟨qStar, pStar⟩
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hresp₁ :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (p - pStar) (qStar - q) =
        restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (p - pStar) (qStar - q)
          = ResponseJ (openCubeSet Q) (p - pStar) (qStar - q) a.toFun := by
              simpa [F, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q) (p - pStar) (qStar - q)
      _ = restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
              (p - pStar) (qStar - q) a.toFun]
            rfl
  have hresp₂ :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
          (pStar + p) (qStar + q) =
        restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q)
          (adjointReg a) := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
          (pStar + p) (qStar + q)
          = ResponseJ (openCubeSet Q) (pStar + p) (qStar + q)
              (adjointCoeffField a.toFun) := by
              have hAdj :
                  ((F.coeffOn Q).transpose).toCoeffField = adjointCoeffField a.toFun := by
                funext x
                simp [F, triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                  coeffOnOfAEEllipticOn_toCoeffField, adjointCoeffField]
              simpa [F, hAdj, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
                  (pStar + p) (qStar + q)
      _ = restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q)
            (adjointReg a) := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
              (pStar + p) (qStar + q) (adjointCoeffField a.toFun)]
            rfl
  rw [Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  simp [blockJObservableCubeSetBlockVec, F, hresp₁, hresp₂]

def fullBlockReflect {d : ℕ} (M : FullBlockMat d) : FullBlockMat d :=
  toFullBlockMat (blockReflect (ofFullBlockMat M))

def fullBlockQuadraticCh04 {d : ℕ} (M : FullBlockMat d) (x : FullBlockVec d) : ℝ :=
  dotProduct x (Matrix.mulVec M x)

noncomputable def blockJQuadraticFullBlockMat {d : ℕ}
    (M : FullBlockMat d) (P Qv : BlockVec d) : ℝ :=
  (1 / 2 : ℝ) * fullBlockQuadraticCh04 M (toFullBlockVec P) +
    (1 / 2 : ℝ) * fullBlockQuadraticCh04 (fullBlockReflect M) (toFullBlockVec Qv) -
    blockVecDot P Qv

@[simp]
theorem fullBlockReflect_toFullBlockMat {d : ℕ} (A : BlockMat d) :
    fullBlockReflect (toFullBlockMat A) = toFullBlockMat (blockReflect A) := by
  ext α β
  cases α <;> cases β <;> simp [fullBlockReflect, toFullBlockMat,
    ofFullBlockMat, blockReflect]

theorem fullBlockQuadraticCh04_toFullBlockMat {d : ℕ} (A : BlockMat d)
    (P : BlockVec d) :
    fullBlockQuadraticCh04 (toFullBlockMat A) (toFullBlockVec P) =
      blockVecDot P (blockMatVecMul A P) := by
  unfold fullBlockQuadraticCh04
  rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]

private theorem measurable_fullBlockReflect {d : ℕ} :
    Measurable (fullBlockReflect (d := d)) := by
  refine measurable_pi_iff.2 fun α => ?_
  refine measurable_pi_iff.2 fun β => ?_
  cases α <;> cases β
  all_goals
    simp [fullBlockReflect, toFullBlockMat, ofFullBlockMat, blockReflect]
    measurability

private theorem measurable_fullBlockQuadraticCh04 {d : ℕ}
    (x : FullBlockVec d) :
    Measurable (fun M : FullBlockMat d => fullBlockQuadraticCh04 M x) := by
  unfold fullBlockQuadraticCh04 dotProduct Matrix.mulVec
  measurability

private theorem measurable_blockJQuadraticFullBlockMat {d : ℕ}
    (P Qv : BlockVec d) :
    Measurable (fun M : FullBlockMat d => blockJQuadraticFullBlockMat M P Qv) := by
  unfold blockJQuadraticFullBlockMat
  exact
    (((measurable_fullBlockQuadraticCh04 (toFullBlockVec P)).const_mul (1 / 2 : ℝ)).add
      (((measurable_fullBlockQuadraticCh04 (toFullBlockVec Qv)).comp measurable_fullBlockReflect).const_mul
        (1 / 2 : ℝ))).sub measurable_const

theorem blockJObservableCubeSetBlockVec_eq_blockJQuadraticFullBlockMat_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (P Qv : BlockVec d) :
    blockJObservableCubeSetBlockVec Q P Qv a =
      blockJQuadraticFullBlockMat
        (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P Qv := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hblock :=
    doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
      (a := a) ha Q P Qv
  have hsplit :=
    (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q) (F.coeffOn Q)).doubled_response_splitting P Qv
  have hcoarse :
      coarseBlockMatrix (cubeSet Q) a.toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    simpa [F] using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        (a := a) ha Q
  have hstar :
      Ch02.coarseStarredBlockMatrixInv (Ch02.cubeDomain Q) (F.coeffOn Q) =
        blockReflect (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)) :=
    (Ch02.blockCoarseMatrixTheory (Ch02.cubeDomain Q) (F.coeffOn Q)).starred_inverse_formula
  calc
    blockJObservableCubeSetBlockVec Q P Qv a =
        Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q) P Qv := hblock.symm
    _ =
        (1 / 2 : ℝ) *
            blockVecDot P
              (blockMatVecMul (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q)) P) +
          (1 / 2 : ℝ) *
            blockVecDot Qv
              (blockMatVecMul
                (Ch02.coarseStarredBlockMatrixInv (Ch02.cubeDomain Q) (F.coeffOn Q)) Qv) -
          blockVecDot P Qv := hsplit
    _ =
        blockJQuadraticFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P Qv := by
          rw [hcoarse, hstar]
          simp [blockJQuadraticFullBlockMat, fullBlockQuadraticCh04_toFullBlockMat]

theorem blockJObservableCubeSetBlockVec_ae_eq_blockJQuadraticFullBlockMat
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} (hPμ : RestrictionLawCarrier Pμ)
    (Q : TriadicCube d) (P Qv : BlockVec d) :
    blockJObservableCubeSetBlockVec Q P Qv =ᵐ[Pμ]
      fun a : RegCoeffField d =>
        blockJQuadraticFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P Qv := by
  filter_upwards [hPμ.ae_locallyUniformlyEllipticField] with a ha
  exact
    blockJObservableCubeSetBlockVec_eq_blockJQuadraticFullBlockMat_of_aelocallyUniformlyEllipticField
      ha Q P Qv

theorem exists_isRestrictionLocalRandomVariable_ae_eq_blockJObservableCubeSetBlockVec
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} (hPμ : RestrictionLawCarrier Pμ)
    (Q : TriadicCube d) (P Qv : BlockVec d) :
    ∃ Y : RegCoeffField d → ℝ,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        blockJObservableCubeSetBlockVec Q P Qv =ᵐ[Pμ] Y := by
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_coarseFullBlockMatrix_cubeSet hPμ Q with
    ⟨Ymat, hYmat_local, hYmat_eq⟩
  let g : FullBlockMat d → ℝ := fun M => blockJQuadraticFullBlockMat M P Qv
  refine ⟨fun a => g (Ymat a),
    hYmat_local.comp_measurable (measurable_blockJQuadraticFullBlockMat P Qv), ?_⟩
  have hraw :=
    blockJObservableCubeSetBlockVec_ae_eq_blockJQuadraticFullBlockMat hPμ Q P Qv
  filter_upwards [hraw, hYmat_eq] with a hJ hM
  simp [g, hJ, hM]

noncomputable def blockJSetObservableBlockVec {d : ℕ}
    (P Qv : BlockVec d) : Set (Vec d) → CoeffField d → ℝ :=
  fun U => blockJHalfResponseAdjointSumSet U P.1 Qv.2 P.2 Qv.1

/-- The raw set-observable, precomposed with the honest sample on a triadic
cube, is the carrier block-response observable. -/
@[simp]
theorem blockJSetObservableBlockVec_cubeSet {d : ℕ}
    (Q : TriadicCube d) (P Qv : BlockVec d) (a : RegCoeffField d) :
    blockJSetObservableBlockVec P Qv (cubeSet Q) a.toFun =
      blockJObservableCubeSetBlockVec Q P Qv a :=
  rfl

theorem blockJSetObservableBlockVec_translation_covariant {d : ℕ}
    (P Qv : BlockVec d) :
    IsTranslationCovariant (blockJSetObservableBlockVec P Qv) := by
  simpa [blockJSetObservableBlockVec] using!
    blockJHalfResponseAdjointSumSet_translation_covariant
      (d := d) P.1 Qv.2 P.2 Qv.1

/-- Restriction translation covariance of the raw set-observable precomposed
with the honest sample. -/
theorem blockJSetObservableBlockVec_restrictionTranslationCovariant {d : ℕ}
    (P Qv : BlockVec d) :
    IsRestrictionTranslationCovariant
      (fun U a => blockJSetObservableBlockVec P Qv U a.toFun) :=
  isRestrictionTranslationCovariant_comp_toFun
    (blockJSetObservableBlockVec_translation_covariant P Qv)

theorem exists_isRestrictionLocalRandomVariable_ae_eq_blockJSetObservableBlockVec_cubeSet
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} (hPμ : RestrictionLawCarrier Pμ)
    (Q : TriadicCube d) (P Qv : BlockVec d) :
    ∃ Y : RegCoeffField d → ℝ,
      IsRestrictionLocalRandomVariable (cubeSet Q) (measurableSet_cubeSet Q) Y ∧
        (fun a : RegCoeffField d => blockJSetObservableBlockVec P Qv (cubeSet Q) a.toFun)
          =ᵐ[Pμ] Y := by
  simpa using
    exists_isRestrictionLocalRandomVariable_ae_eq_blockJObservableCubeSetBlockVec hPμ Q P Qv

theorem aemeasurable_blockJSetObservableBlockVec_cubeSet
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} (hPμ : RestrictionLawCarrier Pμ)
    (Q : TriadicCube d) (P Qv : BlockVec d) :
    AEMeasurable
      (fun a : RegCoeffField d => blockJSetObservableBlockVec P Qv (cubeSet Q) a.toFun)
      Pμ := by
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_blockJSetObservableBlockVec_cubeSet
      hPμ Q P Qv with ⟨Y, hYloc, hYeq⟩
  exact (hPμ.aemeasurable_of_isLocalRandomVariable hYloc).congr hYeq.symm

private theorem gammaTriangleConst_pos' {σ : ℝ} :
    0 < gammaTriangleConst σ := by
  simpa [gammaTriangleConst] using
    (IndependentSums.gammaTriangleConst_pos (σ := σ))

theorem isBigO_gammaSigma_blockJObservableCubeSetBlockVec_originCube_of_scaleZero
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} [IsProbabilityMeasure Pμ]
    {σ θ : ℝ} (hPμ : RestrictionLawCarrier Pμ) (hstat : RestrictionStationaryLaw Pμ)
    (hσ : 0 < σ) (hθ : 0 < θ) (P Qv : BlockVec d)
    (h0 :
      IsBigO Pμ (gammaSigma σ)
        (blockJObservableCubeSetBlockVec (originCube d 0) P Qv) θ)
    {n : ℤ} (hn : 0 ≤ n) :
    IsBigO Pμ (gammaSigma σ)
      (blockJObservableCubeSetBlockVec (originCube d n) P Qv)
      (gammaTriangleConst σ * θ) := by
  classical
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => blockJSetObservableBlockVec P Qv U a.toFun
  let D : Finset (TriadicCube d) := descendantsAtScale (originCube d n) 0
  let Avg : RegCoeffField d → ℝ :=
    fun a => ((D.card : ℝ)⁻¹) *
      ∑ R ∈ D, blockJObservableCubeSetBlockVec R P Qv a
  have hn0 : (0 : ℤ) ≤ (originCube d n).scale := by
    simpa [originCube] using hn
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtScale_nonempty (originCube d n) hn0
  have hX_cov : IsRestrictionTranslationCovariant X := by
    simpa [X] using blockJSetObservableBlockVec_restrictionTranslationCovariant P Qv
  have hX0_aemeas :
      AEMeasurable (X (cubeSet (originCube d 0))) Pμ := by
    simpa [X] using
      aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ (originCube d 0) P Qv
  have hDesc_aemeas :
      ∀ R, AEMeasurable (blockJObservableCubeSetBlockVec R P Qv) Pμ := by
    intro R
    simpa using
      aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ R P Qv
  have hDesc_tail :
      ∀ R ∈ D,
        IsBigO Pμ (gammaSigma σ)
          (blockJObservableCubeSetBlockVec R P Qv) θ := by
    intro R hR
    have hshift :
        cubeSet R =
          translateSet (intVecToRealVec (scaleTranslationShift 0 R))
            (cubeSet (originCube d 0)) := by
      exact cubeSet_eq_translateSet_originCube_of_mem_descendantsAtScale_originCube
        (d := d) (n := 0) (m := n) (R := R) (by norm_num)
        hn (by simpa [D] using hR)
    have hXR_aemeas : AEMeasurable (X (cubeSet R)) Pμ := by
      simpa [X] using hDesc_aemeas R
    have hmap :
        Measure.map (X (cubeSet R)) Pμ =
          Measure.map (X (cubeSet (originCube d 0))) Pμ := by
      calc
        Measure.map (X (cubeSet R)) Pμ =
            Measure.map
              (X
                (translateSet (intVecToRealVec (scaleTranslationShift 0 R))
                  (cubeSet (originCube d 0)))) Pμ := by
              rw [hshift]
        _ = Measure.map (X (cubeSet (originCube d 0))) Pμ := by
              exact map_eq_map_translateReg_of_isRestrictionTranslationCovariant_aemeasurable
                (P := Pμ) hstat (U := cubeSet (originCube d 0))
                hX0_aemeas hX_cov (scaleTranslationShift 0 R)
    have htailX :
        IsBigO Pμ (gammaSigma σ) (X (cubeSet R)) θ := by
      have h0X :
          IsBigO Pμ (gammaSigma σ) (X (cubeSet (originCube d 0))) θ := by
        simpa [X] using h0
      exact
        (isBigO_gammaSigma_iff_of_map_eq_map_aemeasurable
          (μ := Pμ) (σ := σ) (A := θ)
          hXR_aemeas hX0_aemeas hmap).2 h0X
    simpa [X] using htailX
  have hAvg_tail_raw :
      IsBigO Pμ (gammaSigma σ) Avg
        (gammaTriangleConst σ * (((D.card : ℝ)⁻¹) * ∑ R ∈ D, θ)) := by
    simpa [Avg, D] using
      isBigO_finsetAverage_of_isBigO_gammaSigma_aemeasurable
        (μ := Pμ) (s := D)
        (X := fun R => blockJObservableCubeSetBlockVec R P Qv)
        (a := fun _R => θ) (σ := σ) hσ hD_nonempty
        (by intro R hR; exact hθ) hDesc_tail hDesc_aemeas
  have hAvg_tail :
      IsBigO Pμ (gammaSigma σ) Avg (gammaTriangleConst σ * θ) := by
    have hD_card_ne : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast hD_nonempty.card_ne_zero
    have hscale_card : (D.card : ℝ)⁻¹ * ((D.card : ℝ) * θ) = θ := by
      field_simp [hD_card_ne]
    simpa [Finset.sum_const, nsmul_eq_mul, hscale_card] using hAvg_tail_raw
  have hsub_ae :
      ∀ᵐ a ∂Pμ,
        blockJObservableCubeSetBlockVec (originCube d n) P Qv a ≤ Avg a := by
    filter_upwards [hPμ.ae_locallyUniformlyEllipticField] with a ha
    have hsub :=
      blockJObservableCubeSetBlockVec_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
        (a := a) ha (originCube d n) (k := 0) hn0 P Qv
    simpa [Avg, D, descendantsAverage,
      descendantsAtScale_eq_descendantsAtDepth (originCube d n) hn0] using hsub
  rw [IsBigO]
  refine isBigOWith_of_ae_le (μ := Pμ) (Ψ := gammaSigma σ)
    (X := fun a => |Avg a|)
    (Y := fun a => |blockJObservableCubeSetBlockVec (originCube d n) P Qv a|)
    (A := gammaTriangleConst σ * θ) hAvg_tail ?_
  filter_upwards [hsub_ae] with a hsub
  have hraw_nonneg :
      0 ≤ blockJObservableCubeSetBlockVec (originCube d n) P Qv a :=
    blockJObservableCubeSetBlockVec_nonneg (originCube d n) P Qv a
  have hAvg_nonneg : 0 ≤ Avg a := by
    dsimp [Avg, D]
    refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
    exact Finset.sum_nonneg fun R _hR =>
      blockJObservableCubeSetBlockVec_nonneg R P Qv a
  rw [abs_of_nonneg hraw_nonneg, abs_of_nonneg hAvg_nonneg]
  exact hsub

theorem isBigO_gammaSigma_centeredOrigin_blockJSetObservableBlockVec_of_scaleZero
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} [IsProbabilityMeasure Pμ]
    {σ θ : ℝ} (hPμ : RestrictionLawCarrier Pμ) (hstat : RestrictionStationaryLaw Pμ)
    (hσ : 0 < σ) (hθ : 0 < θ) (P Qv : BlockVec d)
    (h0 :
      IsBigO Pμ (gammaSigma σ)
        (blockJObservableCubeSetBlockVec (originCube d 0) P Qv) θ)
    {n : ℤ} (hn : 0 ≤ n) :
    IsBigO Pμ (gammaSigma σ)
      (restrictionCenteredOriginObservable Pμ n
        (fun U a => blockJSetObservableBlockVec P Qv U a.toFun))
      (gammaTriangleConst σ *
        (gammaTriangleConst σ * θ +
          gammaMomentConst σ * (gammaTriangleConst σ * θ))) := by
  let rawK : ℝ := gammaTriangleConst σ * θ
  let Xn : RegCoeffField d → ℝ :=
    blockJObservableCubeSetBlockVec (originCube d n) P Qv
  have hrawK_pos : 0 < rawK := by
    exact mul_pos gammaTriangleConst_pos' hθ
  have hraw :
      IsBigO Pμ (gammaSigma σ) Xn rawK := by
    simpa [Xn, rawK] using
      isBigO_gammaSigma_blockJObservableCubeSetBlockVec_originCube_of_scaleZero
        hPμ hstat hσ hθ P Qv h0 hn
  have hXn_aemeas : AEMeasurable Xn Pμ := by
    simpa [Xn] using
      aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ (originCube d n) P Qv
  have hMomentConst_pos : 0 < gammaMomentConst σ := by
    simpa [gammaMomentConst] using
      (IndependentSums.gammaMomentConst_pos hσ)
  have hM_pos : 0 < gammaMomentConst σ * rawK :=
    mul_pos hMomentConst_pos hrawK_pos
  have hmean_bound :
      |∫ a, Xn a ∂Pμ| ≤ gammaMomentConst σ * rawK := by
    have hmoment :=
      integral_abs_rpow_le_of_isBigO_gammaSigma
        (μ := Pμ) (X := Xn) (K := rawK) (σ := σ) (p := (1 : ℝ))
        hσ hrawK_pos (by norm_num) hXn_aemeas hraw
    calc
      |∫ a, Xn a ∂Pμ| ≤ ∫ a, |Xn a| ∂Pμ :=
        abs_integral_le_integral_abs
      _ = ∫ a, |Xn a| ^ (1 : ℝ) ∂Pμ := by
        simp
      _ ≤ (gammaMomentConst σ * (1 : ℝ) ^ σ⁻¹ * rawK) ^ (1 : ℝ) :=
        hmoment
      _ = gammaMomentConst σ * rawK := by
        simp
  have hcenter :=
    isBigO_gammaSigma_sub_const_of_abs_const_le_aemeasurable
      (μ := Pμ) (σ := σ) (K := rawK)
      (M := gammaMomentConst σ * rawK)
      (c := ∫ a, Xn a ∂Pμ) (X := Xn)
      hσ hrawK_pos hM_pos hraw hXn_aemeas hmean_bound
  simpa [restrictionCenteredOriginObservable, Xn, rawK,
    mul_assoc, mul_left_comm, mul_comm] using! hcenter

theorem isBigOWith_gammaSigma_blockJObservableCubeSetBlockVec_originCube_sub_integral
    {d : ℕ} [NeZero d] {Pμ : RestrictionCoeffLaw d} [IsProbabilityMeasure Pμ]
    {σ θ : ℝ} (hPμ : RestrictionLawCarrier Pμ) (hstat : RestrictionStationaryLaw Pμ)
    (hdep : RestrictionUnitRangeDependentLaw Pμ)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) (hθ : 0 < θ) (P Qv : BlockVec d)
    (h0 :
      IsBigO Pμ (gammaSigma σ)
        (blockJObservableCubeSetBlockVec (originCube d 0) P Qv) θ)
    {n m : ℤ} (hn : 0 ≤ n) (hnm : n < m) :
    IsBigOWith Pμ (gammaSigma σ)
      (fun a =>
        blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
          ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
      (gammaSigmaDescendantsAtScaleConst d n σ *
        (Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) /
          ((descendantsAtScale (originCube d m) n).card : ℝ)) *
        (gammaTriangleConst σ *
          (gammaTriangleConst σ * θ +
            gammaMomentConst σ * (gammaTriangleConst σ * θ)))) := by
  classical
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fun U a => blockJSetObservableBlockVec P Qv U a.toFun
  let Q : TriadicCube d := originCube d m
  let centerK : ℝ :=
    gammaTriangleConst σ *
      (gammaTriangleConst σ * θ +
        gammaMomentConst σ * (gammaTriangleConst σ * θ))
  have hnm_le : n ≤ m := le_of_lt hnm
  have hnQ : n ≤ Q.scale := by
    simpa [Q] using! hnm_le
  have hrawK_pos : 0 < gammaTriangleConst σ * θ :=
    mul_pos gammaTriangleConst_pos' hθ
  have hMomentConst_pos : 0 < gammaMomentConst σ := by
    simpa [gammaMomentConst] using
      (IndependentSums.gammaMomentConst_pos hσ₀)
  have hcenterK_pos : 0 < centerK := by
    dsimp [centerK]
    exact mul_pos gammaTriangleConst_pos'
      (add_pos hrawK_pos (mul_pos hMomentConst_pos hrawK_pos))
  have hcenter :
      IsBigO Pμ (gammaSigma σ)
        (restrictionCenteredOriginObservable Pμ n X) centerK := by
    simpa [X, centerK] using
      isBigO_gammaSigma_centeredOrigin_blockJSetObservableBlockVec_of_scaleZero
        hPμ hstat hσ₀ hθ P Qv h0 hn
  have hX_cov : IsRestrictionTranslationCovariant X := by
    simpa [X] using blockJSetObservableBlockVec_restrictionTranslationCovariant P Qv
  have hX_local :
      ∀ R ∈ descendantsAtScale Q n,
        ∃ Y : RegCoeffField d → ℝ,
          IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) Y ∧
            X (cubeSet R) =ᵐ[Pμ] Y := by
    intro R _hR
    simpa [X] using
      exists_isRestrictionLocalRandomVariable_ae_eq_blockJSetObservableBlockVec_cubeSet
        hPμ R P Qv
  have hX0_aemeas :
      AEMeasurable (X (cubeSet (originCube d n))) Pμ := by
    simpa [X] using
      aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ (originCube d n) P Qv
  have hX_desc_aemeas :
      ∀ R ∈ descendantsAtScale Q n, AEMeasurable (X (cubeSet R)) Pμ := by
    intro R _hR
    simpa [X] using
      aemeasurable_blockJSetObservableBlockVec_cubeSet hPμ R P Qv
  have hpart :
      IsBigO Pμ (gammaSigma σ) (restrictionCenteredDescendantAverageOnCube Pμ Q n X)
        (gammaSigmaDescendantsAtScaleConst d n σ *
          (Real.sqrt ((descendantsAtScale Q n).card : ℝ) /
            ((descendantsAtScale Q n).card : ℝ)) * centerK) :=
    isBigO_gammaSigma_restrictionCenteredDescendantAverageOnCube_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
      (Q := Q) (n := n) (P := Pμ) hPμ hn hnQ hstat hdep X
      hX_local hX_cov hX0_aemeas hX_desc_aemeas hσ₀ hσ₂
      hcenterK_pos hcenter
  have hsub_ae :
      ∀ᵐ a ∂Pμ,
        blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
            ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ ≤
          restrictionCenteredDescendantAverageOnCube Pμ Q n X a := by
    filter_upwards [hPμ.ae_locallyUniformlyEllipticField] with a ha
    have hsub :=
      blockJObservableCubeSetBlockVec_le_descendantsAverage_cubeSet_of_aelocallyUniformlyEllipticField
        (a := a) ha Q (k := n) hnQ P Qv
    have hcenter_eq :=
      congrFun
        (restrictionCenteredDescendantAverageOnCube_eq_restrictionDescendantAverageOnCube_sub
          (P := Pμ) (Q := Q) (n := n) hnQ X) a
    calc
      blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
          ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ
          ≤
        descendantsAverage Q (Int.toNat (Q.scale - n))
            (fun R => blockJObservableCubeSetBlockVec R P Qv a) -
          ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ := by
            simpa [Q] using sub_le_sub_right hsub
              (∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
      _ =
        restrictionDescendantAverageOnCube Q n X a -
          ∫ b, X (cubeSet (originCube d n)) b ∂Pμ := by
            simp [restrictionDescendantAverageOnCube, descendantsAverage, X, Q,
              descendantsAtScale_eq_descendantsAtDepth Q hnQ]
      _ = restrictionCenteredDescendantAverageOnCube Pμ Q n X a := by
            rw [hcenter_eq]
  have hfinal :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a =>
          blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
            ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
        (gammaSigmaDescendantsAtScaleConst d n σ *
          (Real.sqrt ((descendantsAtScale Q n).card : ℝ) /
            ((descendantsAtScale Q n).card : ℝ)) * centerK) := by
    refine isBigOWith_of_ae_le (μ := Pμ) (Ψ := gammaSigma σ)
      (X := fun a => |restrictionCenteredDescendantAverageOnCube Pμ Q n X a|)
      (Y := fun a =>
        blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
          ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
      (A := gammaSigmaDescendantsAtScaleConst d n σ *
        (Real.sqrt ((descendantsAtScale Q n).card : ℝ) /
          ((descendantsAtScale Q n).card : ℝ)) * centerK) hpart ?_
    filter_upwards [hsub_ae] with a ha
    exact ha.trans (le_abs_self _)
  simpa [Q, centerK, X, mul_assoc, mul_left_comm, mul_comm] using hfinal

private theorem scaleColorPeriod_natCast_eq_zero_ch04 (n : ℕ) :
    scaleColorPeriod (n : ℤ) = scaleColorPeriod 0 := by
  have hpos : 0 < (3 : ℝ) ^ (-(n : ℤ)) :=
    zpow_pos (by norm_num : (0 : ℝ) < 3) (-(n : ℤ))
  have hle_one : (3 : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
    exact zpow_le_one_of_nonpos₀
      (show (1 : ℝ) ≤ 3 by norm_num)
      (by exact neg_nonpos.mpr (Int.natCast_nonneg n))
  have hceil :
      Nat.ceil ((3 : ℝ) ^ (-(n : ℤ))) = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
    constructor
    · have h1 : ((1 : ℕ) - 1 : ℕ) = 0 := by norm_num
      simp only [h1, Nat.cast_zero]
      exact hpos
    · simpa using hle_one
  unfold scaleColorPeriod
  rw [hceil]
  norm_num

private theorem gammaSigmaDescendantsAtScaleConst_eq_zero_of_nonneg
    {d : ℕ} {n : ℤ} {σ : ℝ} (hn : 0 ≤ n) :
    gammaSigmaDescendantsAtScaleConst d n σ =
      gammaSigmaDescendantsAtScaleConst d 0 σ := by
  have hn_toNat : ((Int.toNat n : ℤ) = n) := Int.toNat_of_nonneg hn
  have hperiod : scaleColorPeriod n = scaleColorPeriod 0 := by
    calc
      scaleColorPeriod n = scaleColorPeriod (Int.toNat n : ℤ) := by
        rw [hn_toNat]
      _ = scaleColorPeriod 0 := scaleColorPeriod_natCast_eq_zero_ch04 (Int.toNat n)
  simp [gammaSigmaDescendantsAtScaleConst, hperiod]

private theorem descendantsAtScale_originCube_card
    {d : ℕ} {n m : ℤ} (hnm : n ≤ m) :
    (descendantsAtScale (originCube d m) n).card =
      (3 ^ d) ^ Int.toNat (m - n) := by
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d m) hnm]
  exact descendantsAtDepth_card (originCube d m) (Int.toNat (m - n))

private theorem descendantsAtScale_originCube_sqrt_card_div_card
    {d : ℕ} {n m : ℤ} (hnm : n ≤ m) :
    Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) /
        ((descendantsAtScale (originCube d m) n).card : ℝ) =
      (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) := by
  let j : ℕ := Int.toNat (m - n)
  have hcard := descendantsAtScale_originCube_card (d := d) (n := n) (m := m) hnm
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have h3_pos : 0 < (3 : ℝ) := by norm_num
  have hcast :
      (((3 ^ d) ^ j : ℕ) : ℝ) = (3 : ℝ) ^ (d * j) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  have hsqrt :
      Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) =
        (3 : ℝ) ^ (((d : ℝ) / 2) * (j : ℝ)) := by
    rw [hcard, Real.sqrt_eq_rpow]
    rw [hcast]
    rw [← Real.rpow_natCast (3 : ℝ) (d * j)]
    rw [← Real.rpow_mul h3_nonneg]
    congr 1
    rw [Nat.cast_mul]
    ring
  have hinv :
      (((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹) =
        (3 : ℝ) ^ (-(d : ℝ) * (j : ℝ)) := by
    rw [hcard]
    rw [hcast]
    rw [← Real.rpow_natCast (3 : ℝ) (d * j)]
    rw [show ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) by rw [Nat.cast_mul]]
    simpa [neg_mul] using
      (Real.rpow_neg h3_nonneg ((d : ℝ) * (j : ℝ))).symm
  calc
    Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) /
        ((descendantsAtScale (originCube d m) n).card : ℝ)
        =
      Real.sqrt ((descendantsAtScale (originCube d m) n).card : ℝ) *
        (((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹) := by
          rw [div_eq_mul_inv]
    _ = (3 : ℝ) ^ (((d : ℝ) / 2) * (j : ℝ)) *
        (3 : ℝ) ^ (-(d : ℝ) * (j : ℝ)) := by
          rw [hsqrt, hinv]
    _ = (3 : ℝ) ^ ((((d : ℝ) / 2) * (j : ℝ)) +
        (-(d : ℝ) * (j : ℝ))) := by
          rw [← Real.rpow_add h3_pos]
    _ = (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) := by
          simp [j]
          ring_nf

noncomputable def blockJConcentrationConst (d : ℕ) (σ : ℝ) : ℝ :=
  gammaSigmaDescendantsAtScaleConst d 0 σ *
    (gammaTriangleConst σ *
      (gammaTriangleConst σ + gammaMomentConst σ * gammaTriangleConst σ))

theorem blockJConcentrationConst_pos {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    0 < blockJConcentrationConst d σ := by
  have hG : 0 < gammaSigmaDescendantsAtScaleConst d 0 σ :=
    gammaSigmaDescendantsAtScaleConst_pos hσ
  have hMoment : 0 < gammaMomentConst σ := by
    simpa [gammaMomentConst] using
      (IndependentSums.gammaMomentConst_pos hσ)
  have hcenter :
      0 < gammaTriangleConst σ *
        (gammaTriangleConst σ + gammaMomentConst σ * gammaTriangleConst σ) := by
    exact mul_pos gammaTriangleConst_pos'
      (add_pos gammaTriangleConst_pos'
        (mul_pos hMoment gammaTriangleConst_pos'))
  exact mul_pos hG hcenter

/-- Lemma `l.concentration.of.J`, in the block-vector form used by the Lean
development.  The manuscript's normalized pair
`(B^{-1/2}e, B^{1/2}e)` is obtained by specializing `P` and `Qv`.

The constant is chosen before `θ`, the law, the vectors, and the scales. -/
theorem concentration_of_blockJObservableCubeSetBlockVec
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {θ : ℝ}, 0 < θ →
      ∀ {Pμ : RestrictionCoeffLaw d} [IsProbabilityMeasure Pμ],
        RestrictionLawCarrier Pμ → RestrictionStationaryLaw Pμ → RestrictionUnitRangeDependentLaw Pμ →
      ∀ (P Qv : BlockVec d),
        IsBigO Pμ (gammaSigma σ)
          (blockJObservableCubeSetBlockVec (originCube d 0) P Qv) θ →
      ∀ {n m : ℤ}, 0 ≤ n → n < m →
        IsBigOWith Pμ (gammaSigma σ)
          (fun a =>
            blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
              ∫ b, blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
          (C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) * θ) := by
  refine ⟨blockJConcentrationConst d σ, blockJConcentrationConst_pos hσ₀, ?_⟩
  intro θ hθ Pμ _hprob hPμ hstat hdep P Qv h0 n m hn hnm
  have hnm_le : n ≤ m := le_of_lt hnm
  have hexact :=
    isBigOWith_gammaSigma_blockJObservableCubeSetBlockVec_originCube_sub_integral
      (Pμ := Pμ) hPμ hstat hdep hσ₀ hσ₂ hθ P Qv h0 hn hnm
  have hG :=
    gammaSigmaDescendantsAtScaleConst_eq_zero_of_nonneg
      (d := d) (n := n) (σ := σ) hn
  have hcard :=
    descendantsAtScale_originCube_sqrt_card_div_card
      (d := d) (n := n) (m := m) hnm_le
  convert hexact using 1
  rw [hG, hcard]
  simp [blockJConcentrationConst]
  ring_nf

end

end Ch04
end Book
end Homogenization
