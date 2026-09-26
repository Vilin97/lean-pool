/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.Finite

/-! # Homogenization Error Control -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open Section54.VarianceBoundGoodScale
open scoped ENNReal MatrixOrder

/-!
# Finite-q homogenization-error control above the minimal scale

This file begins the Section 5.7 corollary converting the localized
minimal-scale `J` estimate into finite-`q` control of
`\mathcal E_{r,\infty,q}`.  The first lemma is the deterministic geometric
summation step: after each weighted scale response term is bounded by a
summable geometric row, the finite-`q` homogenization error is bounded by the
corresponding `q`-root.
-/

noncomputable section

/-- For a scalar reference coefficient, the Chapter 2 full block matrix is the
diagonal matrix with entries `σ` and `σ⁻¹`. -/
theorem constantFullBlockMatrix_scalarMatrix_eq_diagonal
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ : 0 < σ) :
    Ch02.constantFullBlockMatrix (scalarMatrix (d := d) σ) =
      Matrix.diagonal (fun α : BlockCoord d =>
        match α with
        | Sum.inl _ => σ
        | Sum.inr _ => σ⁻¹) := by
  change toFullBlockMat (Ch02.constantBlockMatrix (scalarMatrix (d := d) σ)) = _
  rw [Ch02.constantBlockMatrix_scalarMatrix hσ]
  ext α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          by_cases hij : i = j
          · subst j
            simp [toFullBlockMat, scalarMatrix, Matrix.diagonal]
          · simp [toFullBlockMat, scalarMatrix, Matrix.diagonal, hij]
      | inr j =>
          simp [toFullBlockMat, Matrix.diagonal]
  | inr i =>
      cases β with
      | inl j =>
          simp [toFullBlockMat, Matrix.diagonal]
      | inr j =>
          by_cases hij : i = j
          · subst j
            simp [toFullBlockMat, scalarMatrix, Matrix.diagonal]
          · simp [toFullBlockMat, scalarMatrix, Matrix.diagonal, hij]

/-- The Chapter 2 square-root normalizer agrees with the Section 5.7 scalar
normalizer for a scalar reference coefficient. -/
theorem constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ : 0 < σ) :
    Ch02.constantFullBlockMatrixSqrt (scalarMatrix (d := d) σ) =
      Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) σ σ) := by
  let D : FullBlockMat d :=
    Matrix.diagonal (Section56.scalarFullBlockSqrtDiag (d := d) σ σ)
  have hD_nonneg : 0 ≤ D := by
    have hentries : 0 ≤ Section56.scalarFullBlockSqrtDiag (d := d) σ σ := by
      intro α
      cases α <;> simp [Section56.scalarFullBlockSqrtDiag]
    exact (Matrix.PosSemidef.diagonal hentries).nonneg
  have hsq : D * D = Ch02.constantFullBlockMatrix (scalarMatrix (d := d) σ) := by
    rw [constantFullBlockMatrix_scalarMatrix_eq_diagonal hσ]
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            by_cases hij : i = j
            · subst j
              simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal]
              rw [Real.mul_self_sqrt hσ.le]
            · simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal, hij]
        | inr j =>
            simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal]
    | inr i =>
        cases β with
        | inl j =>
            simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal]
        | inr j =>
            by_cases hij : i = j
            · subst j
              simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal]
              rw [← mul_inv]
              rw [Real.mul_self_sqrt hσ.le]
            · simp [Section56.scalarFullBlockSqrtDiag, Matrix.diagonal, hij]
  dsimp [Ch02.constantFullBlockMatrixSqrt]
  exact CFC.sqrt_unique hsq hD_nonneg

/-- Coordinatewise inverse of the scalar square-root diagonal used in Section
5.7. -/
theorem ringInverse_scalarFullBlockSqrtDiag_eq_scalarFullBlockInvSqrtDiag
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ : 0 < σ) :
    Ring.inverse (Section56.scalarFullBlockSqrtDiag (d := d) σ σ) =
      Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ := by
  let v : BlockCoord d → ℝ := Section56.scalarFullBlockSqrtDiag (d := d) σ σ
  let w : BlockCoord d → ℝ := Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ
  have hvw : v * w = 1 := by
    funext α
    cases α
    · simp [v, w, Section56.scalarFullBlockSqrtDiag,
        Ch04.scalarFullBlockInvSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
    · simp [v, w, Section56.scalarFullBlockSqrtDiag,
        Ch04.scalarFullBlockInvSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
  have hwv : w * v = 1 := by
    funext α
    cases α
    · simp [v, w, Section56.scalarFullBlockSqrtDiag,
        Ch04.scalarFullBlockInvSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
    · simp [v, w, Section56.scalarFullBlockSqrtDiag,
        Ch04.scalarFullBlockInvSqrtDiag]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hσ)]
  let u : (BlockCoord d → ℝ)ˣ := ⟨v, w, hvw, hwv⟩
  simpa [u, v, w] using Ring.inverse_unit u

/-- The Chapter 2 inverse square-root normalizer agrees with the Section 5.7
scalar inverse normalizer for a scalar reference coefficient. -/
theorem constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
    {d : ℕ} [NeZero d] {σ : ℝ} (hσ : 0 < σ) :
    Ch02.constantFullBlockMatrixInvSqrt (scalarMatrix (d := d) σ) =
      Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag (d := d) σ σ) := by
  dsimp [Ch02.constantFullBlockMatrixInvSqrt]
  rw [constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt hσ]
  rw [Matrix.inv_diagonal]
  rw [ringInverse_scalarFullBlockSqrtDiag_eq_scalarFullBlockInvSqrtDiag hσ]

/-- Pointwise version of the finite-basis normalization step for sampled
coefficient fields. -/
theorem limitNormalizedJProbeSum_le_four_normalizedProbeSum_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) :
    limitNormalizedJProbeSum hP hStruct Q a ≤
      4 * limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
  classical
  have hplus :
      ∀ α β : BlockCoord d,
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockPlusProbe α β) a =
          4 * limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a := by
    intro α β
    let M : FullBlockMat d := limitNormalizedBlockJMatrix hP hStruct Q a
    have hraw :
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockPlusProbe α β) a =
          fullBlockQuadratic M (fullBlockPlusProbe α β) := by
      simpa [M] using
        limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
          hP hStruct hΓ ha Q (fullBlockPlusProbe α β)
    have hscaled :
        limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a =
          fullBlockQuadratic M ((1 / 2 : ℝ) • fullBlockPlusProbe α β) := by
      simpa [M] using
        limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
          hP hStruct hΓ ha Q ((1 / 2 : ℝ) • fullBlockPlusProbe α β)
    rw [hraw, hscaled, fullBlockQuadratic_vec_smul]
    ring
  have hminus :
      ∀ α β : BlockCoord d,
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockMinusProbe α β) a =
          4 * limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a := by
    intro α β
    let M : FullBlockMat d := limitNormalizedBlockJMatrix hP hStruct Q a
    have hraw :
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockMinusProbe α β) a =
          fullBlockQuadratic M (fullBlockMinusProbe α β) := by
      simpa [M] using
        limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
          hP hStruct hΓ ha Q (fullBlockMinusProbe α β)
    have hscaled :
        limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a =
          fullBlockQuadratic M ((1 / 2 : ℝ) • fullBlockMinusProbe α β) := by
      simpa [M] using
        limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
          hP hStruct hΓ ha Q ((1 / 2 : ℝ) • fullBlockMinusProbe α β)
    rw [hraw, hscaled, fullBlockQuadratic_vec_smul]
    ring
  unfold limitNormalizedJProbeSum limitNormalizedJNormalizedProbeSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro α _hα
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro β _hβ
  rw [hplus α β, hminus α β]
  have hcoord_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        (fullBlockCoordinateProbe α) a := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_nonneg Q
        (scalarLimitInvSqrtBlockVec hP hStruct (fullBlockCoordinateProbe α))
        (scalarLimitSqrtBlockVec hP hStruct (fullBlockCoordinateProbe α)) a
  have hplus_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_nonneg Q
        (scalarLimitInvSqrtBlockVec hP hStruct
          ((1 / 2 : ℝ) • fullBlockPlusProbe α β))
        (scalarLimitSqrtBlockVec hP hStruct
          ((1 / 2 : ℝ) • fullBlockPlusProbe α β)) a
  have hminus_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_nonneg Q
        (scalarLimitInvSqrtBlockVec hP hStruct
          ((1 / 2 : ℝ) • fullBlockMinusProbe α β))
        (scalarLimitSqrtBlockVec hP hStruct
          ((1 / 2 : ℝ) • fullBlockMinusProbe α β)) a
  nlinarith

/-- One-cube bridge from the Chapter 2 normalized block-response maximum to the
Section 5.7 finite normalized probe sum. -/
theorem normalizedBlockResponseMax_scalarMatrix_le_limitNormalizedJNormalizedProbeSum_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) :
    Ch02.normalizedBlockResponseMax Q
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      (4 * (Fintype.card (BlockCoord d) : ℝ)) *
        limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let σ : ℝ := barSigmaLimit hP hStruct
  have hσ : 0 < σ := by
    simpa [σ] using hΓ.barSigmaLimit_pos
  unfold Ch02.normalizedBlockResponseMax
  refine csSup_le (Ch02.normalizedBlockResponseValueSet_nonempty Q F
    (scalarMatrix (d := d) σ)) ?_
  rintro x ⟨e, he, rfl⟩
  have he_dot : dotProduct e e ≤ 1 := by
    have hdot_eq : dotProduct e e = 1 := by
      simpa [Ch02.fullBlockVecNormSq, dotProduct, pow_two] using he
    exact le_of_eq hdot_eq
  have hJ :
      Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (ofFullBlockVec
            (Matrix.mulVec
              (Ch02.constantFullBlockMatrixInvSqrt
                (scalarMatrix (d := d) σ)) e))
          (ofFullBlockVec
            (Matrix.mulVec
              (Ch02.constantFullBlockMatrixSqrt
                (scalarMatrix (d := d) σ)) e)) =
        limitNormalizedBlockJObservable hP hStruct Q e a := by
    have hInv :=
      constantFullBlockMatrixInvSqrt_scalarMatrix_eq_scalarFullBlockInvSqrt
        (d := d) hσ
    have hSqrt :=
      constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
        (d := d) hσ
    rw [hInv, hSqrt]
    simpa [F, σ, limitNormalizedBlockJObservable,
      scalarLimitInvSqrtBlockVec, scalarLimitSqrtBlockVec,
      scalarLimitInvSqrtMatrix, scalarLimitSqrtMatrix] using
      Ch04.doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
        (a := a) ha Q
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e)
  have hunit :=
    limitNormalizedBlockJObservable_le_probeSum_of_aelocallyUniformlyEllipticField
      hP hStruct hΓ ha Q e he_dot
  have hprobe :=
    limitNormalizedJProbeSum_le_four_normalizedProbeSum_of_aelocallyUniformlyEllipticField
      hP hStruct hΓ ha Q
  have hcard_nonneg : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) := by
    positivity
  calc
    Ch02.doubledResponseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (ofFullBlockVec
            (Matrix.mulVec
              (Ch02.constantFullBlockMatrixInvSqrt
                (scalarMatrix (d := d) σ)) e))
          (ofFullBlockVec
            (Matrix.mulVec
              (Ch02.constantFullBlockMatrixSqrt
                (scalarMatrix (d := d) σ)) e))
        = limitNormalizedBlockJObservable hP hStruct Q e a := hJ
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          limitNormalizedJProbeSum hP hStruct Q a := hunit
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          (4 * limitNormalizedJNormalizedProbeSum hP hStruct Q a) := by
        exact mul_le_mul_of_nonneg_left hprobe hcard_nonneg
    _ =
        (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
        ring

/-- A descendant's normalized finite-probe sum is bounded by the localized
maximum over all descendants at the same scale. -/
theorem limitNormalizedJNormalizedProbeSum_le_localizedLimitNormalizedJNormalizedProbeSumMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ))
    (a : RegCoeffField d) :
    limitNormalizedJNormalizedProbeSum hP hStruct R a ≤
      localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty := ⟨R, by simpa [D] using hR⟩
  dsimp [localizedLimitNormalizedJNormalizedProbeSumMax]
  simp only [D, hD, dite_true]
  exact Finset.le_sup' (s := D)
    (f := fun S => limitNormalizedJNormalizedProbeSum hP hStruct S a)
    (b := R) (by simpa [D] using hR)

/-- Localized bridge from the Chapter 2 descendant response maximum to the
Section 5.7 finite normalized-probe maximum. -/
theorem maxDescendantNormalizedBlockResponseAtScale_originCube_scalarMatrix_le_localizedNormalizedProbeJMax_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℕ} (hnm : n ≤ m) :
    Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
          (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
        localizedNormalizedProbeJMax hP hStruct m n a := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let σ : ℝ := barSigmaLimit hP hStruct
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  unfold Ch02.maxDescendantNormalizedBlockResponseAtScale Ch02.finsetSupReal
  refine csSup_le ?_ ?_
  · rcases hD with ⟨R, hR⟩
    exact ⟨Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ),
      ⟨R, by simpa [D] using hR, rfl⟩⟩
  · rintro x ⟨R, hR, rfl⟩
    have hRmem :
        R ∈ descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ) := by
      simpa [D] using hR
    have hone :=
      normalizedBlockResponseMax_scalarMatrix_le_limitNormalizedJNormalizedProbeSum_of_aelocallyUniformlyEllipticField
        hP hStruct hΓ ha R
    have hloc :=
      limitNormalizedJNormalizedProbeSum_le_localizedLimitNormalizedJNormalizedProbeSumMax
        hP hStruct hRmem a
    have hprobe :=
      localizedLimitNormalizedJNormalizedProbeSumMax_le_probeJMax
        hP hStruct hnm a
    calc
      Ch02.normalizedBlockResponseMax R F (scalarMatrix (d := d) σ)
          ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
              limitNormalizedJNormalizedProbeSum hP hStruct R a := hone
      _ ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
            localizedLimitNormalizedJNormalizedProbeSumMax hP hStruct m n a := by
          exact mul_le_mul_of_nonneg_left hloc (by positivity)
      _ ≤ (4 * (Fintype.card (BlockCoord d) : ℝ)) *
            ((Fintype.card (NormalizedProbeIndex d) : ℝ) *
              localizedNormalizedProbeJMax hP hStruct m n a) := by
          exact mul_le_mul_of_nonneg_left hprobe (by positivity)
      _ =
          (4 * (Fintype.card (BlockCoord d) : ℝ) *
              (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n a := by
          ring

/-- If every normalized finite probe satisfies a weighted localized estimate,
then the finite-probe maximum satisfies the same weighted estimate. -/
theorem weighted_localizedNormalizedProbeJMax_le_of_forall_probe
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} (a : RegCoeffField d) {W R : ℝ}
    (hW : 0 < W)
    (hprobe : ∀ i : NormalizedProbeIndex d,
      W * localizedLimitNormalizedJMax hP hStruct m n
          (normalizedProbeVec i) a ≤ R) :
    W * localizedNormalizedProbeJMax hP hStruct m n a ≤ R := by
  classical
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  have hsup_le :
      localizedNormalizedProbeJMax hP hStruct m n a ≤ R / W := by
    dsimp [localizedNormalizedProbeJMax]
    change S.sup' hS (fun i =>
      localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec i) a) ≤ R / W
    refine Finset.sup'_le hS _ ?_
    intro i _hi
    exact (le_div_iff₀ hW).2 (by simpa [mul_comm] using hprobe i)
  calc
    W * localizedNormalizedProbeJMax hP hStruct m n a ≤ W * (R / W) :=
      mul_le_mul_of_nonneg_left hsup_le hW.le
    _ = R := by
      field_simp [hW.ne']

/-- The limiting-normalized block response is nonnegative. -/
theorem limitNormalizedBlockJObservable_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) (e : FullBlockVec d) (a : RegCoeffField d) :
    0 ≤ limitNormalizedBlockJObservable hP hStruct Q e a := by
  simpa [limitNormalizedBlockJObservable] using
    Ch04.blockJObservableCubeSetBlockVec_nonneg Q
      (scalarLimitInvSqrtBlockVec hP hStruct e)
      (scalarLimitSqrtBlockVec hP hStruct e) a

/-- Localized limiting-normalized maxima are nonnegative. -/
theorem localizedLimitNormalizedJMax_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} (hnm : n ≤ m) (e : FullBlockVec d) (a : RegCoeffField d) :
    0 ≤ localizedLimitNormalizedJMax hP hStruct m n e a := by
  classical
  let D : Finset (TriadicCube d) :=
    descendantsAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
  have hD : D.Nonempty :=
    descendantsAtScale_originCube_nat_nonempty (d := d) (m := m) (n := n) hnm
  rcases hD with ⟨R, hR⟩
  have hR_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct R e a :=
    limitNormalizedBlockJObservable_nonneg hP hStruct R e a
  have hR_le :
      limitNormalizedBlockJObservable hP hStruct R e a ≤
        localizedLimitNormalizedJMax hP hStruct m n e a :=
    limitNormalizedBlockJObservable_le_localizedLimitNormalizedJMax
      hP hStruct e (by simpa [D] using hR) a
  exact hR_nonneg.trans hR_le

/-- The finite normalized-probe maximum is nonnegative. -/
theorem localizedNormalizedProbeJMax_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {m n : ℕ} (hnm : n ≤ m) (a : RegCoeffField d) :
    0 ≤ localizedNormalizedProbeJMax hP hStruct m n a := by
  classical
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  have hS : S.Nonempty := by
    let α : BlockCoord d := Classical.choice inferInstance
    exact ⟨(α, α, NormalizedProbeKind.coord), by simp [S]⟩
  rcases hS with ⟨i, hi⟩
  have hi_nonneg :
      0 ≤ localizedLimitNormalizedJMax hP hStruct m n
        (normalizedProbeVec i) a :=
    localizedLimitNormalizedJMax_nonneg hP hStruct hnm (normalizedProbeVec i) a
  have hi_le :
      localizedLimitNormalizedJMax hP hStruct m n
          (normalizedProbeVec i) a ≤
        localizedNormalizedProbeJMax hP hStruct m n a := by
    dsimp [localizedNormalizedProbeJMax]
    exact Finset.le_sup' (s := S)
      (f := fun j =>
        localizedLimitNormalizedJMax hP hStruct m n (normalizedProbeVec j) a)
      hi
  exact hi_nonneg.trans hi_le

/-- Natural-scale response control from the localized finite normalized-probe
maximum. -/
theorem scaleResponseAtScale_originCube_nat_le_sqrt_const_mul_localizedNormalizedProbeJMax
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m n : ℕ} (hnm : n ≤ m) :
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
      Real.sqrt
        ((4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a) := by
  let Cprobe : ℝ :=
    4 * (Fintype.card (BlockCoord d) : ℝ) *
      (Fintype.card (NormalizedProbeIndex d) : ℝ)
  have hk : ((n : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by
    exact_mod_cast hnm
  have hmax :=
    maxDescendantNormalizedBlockResponseAtScale_originCube_scalarMatrix_le_localizedNormalizedProbeJMax_of_aelocallyUniformlyEllipticField
      hP hStruct hΓ ha hnm
  have hsqrt :
      Real.sqrt
          (Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
            (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
            (scalarMatrix (d := d) (barSigmaLimit hP hStruct))) ≤
        Real.sqrt (Cprobe * localizedNormalizedProbeJMax hP hStruct m n a) := by
    simpa [Cprobe] using Real.sqrt_le_sqrt hmax
  calc
    Ch02.scaleResponseAtScale (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
        Ch02.MultiscaleExponent.infinity
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
        (scalarMatrix (d := d) (barSigmaLimit hP hStruct))
        =
          Real.sqrt
            (Ch02.maxDescendantNormalizedBlockResponseAtScale
              (originCube d ((m : ℕ) : ℤ)) ((n : ℕ) : ℤ)
              (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha)
              (scalarMatrix (d := d) (barSigmaLimit hP hStruct))) := by
            rw [Ch02.scaleResponseAtScale_infinity_eq]
            simp [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (Cprobe * localizedNormalizedProbeJMax hP hStruct m n a) :=
        hsqrt
    _ =
      Real.sqrt
        ((4 * (Fintype.card (BlockCoord d) : ℝ) *
            (Fintype.card (NormalizedProbeIndex d) : ℝ)) *
          localizedNormalizedProbeJMax hP hStruct m n a) := by
        rfl

/-- A deterministic finite-`q` summation principle for the Chapter 2
homogenization error.

The hypothesis `hterm` is exactly the pointwise weighted scale-row estimate
which comes from the localized `J` minimal-scale bound after choosing
`delta = r - tau / 2`.  The conclusion is the finite-`q` `\ell^q` norm bound
in the definition of `HomogenizationErrorFinite`. -/
theorem homogenizationErrorFinite_infinity_le_rpow_of_weighted_geometric_bound
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r delta q B : ℝ}
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hB : 0 ≤ B)
    (hterm : ∀ l : ℕ,
      Ch02.geometricWeight r q l *
          Real.rpow
            (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
              Ch02.MultiscaleExponent.infinity a a0) q ≤
        Ch02.geometricWeight delta q l * B) :
    Ch02.HomogenizationErrorFinite Q n r
        Ch02.MultiscaleExponent.infinity q a a0 ≤
      Real.rpow B (1 / q) := by
  let f : ℕ → ℝ := fun l =>
    Ch02.geometricWeight r q l *
      Real.rpow
        (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0) q
  let g : ℕ → ℝ := fun l => Ch02.geometricWeight delta q l * B
  have hf_nonneg : ∀ l : ℕ, 0 ≤ f l := by
    intro l
    have hk : n - (l : ℤ) ≤ Q.scale :=
      (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
    exact mul_nonneg
      (by
        simpa [Ch02.geometricWeight_eq_old] using
          Homogenization.geometricWeight_nonneg (s := r) (q := q) l hrq)
      (Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q hk a a0) q)
  have hg_nonneg : ∀ l : ℕ, 0 ≤ g l := by
    intro l
    exact mul_nonneg
      (by
        simpa [Ch02.geometricWeight_eq_old] using
          Homogenization.geometricWeight_nonneg
            (s := delta) (q := q) l hdeltaq.le)
      hB
  have hg_summable : Summable g := by
    have hbase :
        Summable (fun l : ℕ => Homogenization.geometricWeight delta q l) :=
      Homogenization.summable_geometricWeight hdeltaq
    have hscaled :
        Summable (fun l : ℕ =>
          B * Homogenization.geometricWeight delta q l) :=
      hbase.mul_left B
    simpa [g, Ch02.geometricWeight_eq_old, mul_comm, mul_left_comm, mul_assoc]
      using hscaled
  have hf_summable : Summable f :=
    Summable.of_nonneg_of_le hf_nonneg
      (by
        intro l
        simpa [f, g] using hterm l)
      hg_summable
  have hsum_le : (∑' l : ℕ, f l) ≤ ∑' l : ℕ, g l :=
    Summable.tsum_le_tsum
      (by
        intro l
        simpa [f, g] using hterm l)
      hf_summable hg_summable
  have hg_tsum : (∑' l : ℕ, g l) = B := by
    have hbase :
        Summable (fun l : ℕ => Homogenization.geometricWeight delta q l) :=
      Homogenization.summable_geometricWeight hdeltaq
    calc
      (∑' l : ℕ, g l)
          = ∑' l : ℕ, B * Homogenization.geometricWeight delta q l := by
              simp [g, Ch02.geometricWeight_eq_old, mul_comm]
      _ = B * ∑' l : ℕ, Homogenization.geometricWeight delta q l := by
              simpa using hbase.tsum_mul_left B
      _ = B := by
              rw [Homogenization.tsum_geometricWeight_eq_one hdeltaq]
              ring
  have hf_tsum_nonneg : 0 ≤ ∑' l : ℕ, f l :=
    tsum_nonneg hf_nonneg
  have hf_tsum_le_B : (∑' l : ℕ, f l) ≤ B := by
    simpa [hg_tsum] using hsum_le
  unfold Ch02.HomogenizationErrorFinite
  change Real.rpow (∑' l : ℕ, f l) (1 / q) ≤ Real.rpow B (1 / q)
  exact Real.rpow_le_rpow hf_tsum_nonneg hf_tsum_le_B
    (by positivity)

/-- Convert a pointwise response bound with discount `tau / 2` into the
weighted geometric row bound used by
`homogenizationErrorFinite_infinity_le_rpow_of_weighted_geometric_bound`.

This is the deterministic algebra behind the phrase "give up some `t` to get
finite `q`": if `delta = r - tau / 2` is positive, the extra
`3^{tau l / 2}` from taking the square root of a `J`-bound is absorbed by the
`r`-geometric weight. -/
theorem weighted_scaleResponse_term_le_of_scaleResponse_le
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ} {l : ℕ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale :
      Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    Ch02.geometricWeight r q l *
          Real.rpow
            (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
              Ch02.MultiscaleExponent.infinity a a0) q ≤
        Ch02.geometricWeight delta q l *
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount delta q)⁻¹ *
            Real.rpow A q * Real.rpow R q) := by
  have hk : n - (l : ℤ) ≤ Q.scale :=
    (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
  have hresp_nonneg :
      0 ≤ Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 :=
    Ch02.scaleResponseAtScale_infinity_nonneg Q hk a a0
  have hpow_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) := by
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hscale_rhs_nonneg :
      0 ≤ A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R := by
    exact mul_nonneg (mul_nonneg hA hpow_nonneg) hR
  have hresp_pow_le :
      Real.rpow
          (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
            Ch02.MultiscaleExponent.infinity a a0) q ≤
        Real.rpow
          (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) q :=
    Real.rpow_le_rpow hresp_nonneg hscale hq.le
  have hweight_r_nonneg : 0 ≤ Ch02.geometricWeight r q l := by
    simpa [Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_nonneg (s := r) (q := q) l hrq
  have hdisc_delta_pos : 0 < Ch02.geometricDiscount delta q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hdeltaq
  have hpow_expand :
      Real.rpow
          (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) q =
          Real.rpow A q *
          Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) *
          Real.rpow R q := by
    have hmul₁ :
        Real.rpow (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) q =
          Real.rpow (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ))) q *
            Real.rpow R q := by
      simpa using
        (Real.mul_rpow
          (x := A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)))
          (y := R) (z := q) (mul_nonneg hA hpow_nonneg) hR)
    have hmul₂ :
        Real.rpow (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ))) q =
          Real.rpow A q *
            Real.rpow (Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ))) q := by
      simpa using
        (Real.mul_rpow
          (x := A) (y := Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)))
          (z := q) hA hpow_nonneg)
    have hpow :
        Real.rpow (Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ))) q =
          Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) := by
      simpa using
        (Real.rpow_mul (x := (3 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3)
          ((tau / 2) * (l : ℝ)) q).symm
    rw [hmul₁, hmul₂, hpow]
  have hweight_identity :
      Ch02.geometricWeight r q l *
          (Real.rpow A q *
            Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) *
            Real.rpow R q) =
        Ch02.geometricWeight delta q l *
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount delta q)⁻¹ *
            Real.rpow A q * Real.rpow R q) := by
    have hpow_exp :
        Real.rpow (3 : ℝ) (-r * q * (l : ℝ)) *
            Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) =
          Real.rpow (3 : ℝ) (-delta * q * (l : ℝ)) := by
      have hadd :
          Real.rpow (3 : ℝ)
              ((-r * q * (l : ℝ)) + (((tau / 2) * (l : ℝ)) * q)) =
            Real.rpow (3 : ℝ) (-r * q * (l : ℝ)) *
              Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) := by
        simpa using
          Real.rpow_add (by norm_num : (0 : ℝ) < 3)
            (-r * q * (l : ℝ)) (((tau / 2) * (l : ℝ)) * q)
      rw [← hadd]
      congr 1
      rw [hdelta]
      ring
    unfold Ch02.geometricWeight
    calc
      Ch02.geometricDiscount r q *
            Real.rpow (3 : ℝ) (-r * q * (l : ℝ)) *
          (Real.rpow A q *
            Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q) *
            Real.rpow R q)
          =
        Ch02.geometricDiscount r q *
          (Real.rpow (3 : ℝ) (-r * q * (l : ℝ)) *
            Real.rpow (3 : ℝ) (((tau / 2) * (l : ℝ)) * q)) *
          Real.rpow A q * Real.rpow R q := by
            ring
      _ =
        Ch02.geometricDiscount r q *
          Real.rpow (3 : ℝ) (-delta * q * (l : ℝ)) *
          Real.rpow A q * Real.rpow R q := by
            rw [hpow_exp]
      _ =
        (Ch02.geometricDiscount delta q *
            Real.rpow (3 : ℝ) (-delta * q * (l : ℝ))) *
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount delta q)⁻¹ *
            Real.rpow A q * Real.rpow R q) := by
            field_simp [hdisc_delta_pos.ne']
  calc
    Ch02.geometricWeight r q l *
          Real.rpow
            (Ch02.scaleResponseAtScale Q (n - (l : ℤ))
              Ch02.MultiscaleExponent.infinity a a0) q
        ≤ Ch02.geometricWeight r q l *
            Real.rpow
              (A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) q := by
            exact mul_le_mul_of_nonneg_left hresp_pow_le hweight_r_nonneg
    _ =
        Ch02.geometricWeight delta q l *
          (Ch02.geometricDiscount r q *
            (Ch02.geometricDiscount delta q)⁻¹ *
            Real.rpow A q * Real.rpow R q) := by
            rw [hpow_expand, hweight_identity]

/-- Finite-`q` deterministic `\mathcal E` control from a scale-by-scale
response estimate.

This is the packaged geometric summation step used by the Section 5.7
minimal-scale corollary.  The constant is explicit: it is only the ratio of
the two geometric normalizations, multiplied by the `q`-power of the
scale-response prefactor. -/
theorem homogenizationErrorFinite_infinity_le_of_scaleResponse_le
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {r tau delta q A R : ℝ}
    (hdelta : delta = r - tau / 2)
    (hrq : 0 ≤ r * q) (hdeltaq : 0 < delta * q) (hq : 0 < q)
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hscale : ∀ l : ℕ,
      Ch02.scaleResponseAtScale Q (n - (l : ℤ))
          Ch02.MultiscaleExponent.infinity a a0 ≤
        A * Real.rpow (3 : ℝ) ((tau / 2) * (l : ℝ)) * R) :
    Ch02.HomogenizationErrorFinite Q n r
        Ch02.MultiscaleExponent.infinity q a a0 ≤
      Real.rpow
        (Ch02.geometricDiscount r q *
          (Ch02.geometricDiscount delta q)⁻¹ *
          Real.rpow A q * Real.rpow R q)
        (1 / q) := by
  let B : ℝ :=
    Ch02.geometricDiscount r q *
      (Ch02.geometricDiscount delta q)⁻¹ *
      Real.rpow A q * Real.rpow R q
  have hdisc_r_nonneg : 0 ≤ Ch02.geometricDiscount r q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq
  have hdisc_delta_pos : 0 < Ch02.geometricDiscount delta q := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hdeltaq
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  exact
    homogenizationErrorFinite_infinity_le_rpow_of_weighted_geometric_bound
      (Q := Q) (n := n) hn a a0 hrq hdeltaq hq hB
      (by
        intro l
        simpa [B] using
          weighted_scaleResponse_term_le_of_scaleResponse_le
            (Q := Q) (n := n) hn a a0
            (r := r) (tau := tau) (delta := delta) (q := q)
            (A := A) (R := R) (l := l)
            hdelta hrq hdeltaq hq hA hR (hscale l))

/-- Square-root form of the `p = infinity` scale response: a bound on the
underlying descendant maximum by `B^2` gives a bound on the scale response by
`B`. -/
theorem scaleResponseAtScale_infinity_le_of_maxDescendant_le_sq
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (_hk : k ≤ Q.scale)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {B : ℝ} (hB : 0 ≤ B)
    (hmax :
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a a0 ≤
        B ^ (2 : ℕ)) :
    Ch02.scaleResponseAtScale Q k
        Ch02.MultiscaleExponent.infinity a a0 ≤ B := by
  have hsqrt :
      Real.sqrt
          (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a a0) ≤
        Real.sqrt (B ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt hmax
  calc
    Ch02.scaleResponseAtScale Q k Ch02.MultiscaleExponent.infinity a a0
        =
          Real.sqrt
            (Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a a0) := by
            rw [Ch02.scaleResponseAtScale_infinity_eq]
            simp [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (B ^ (2 : ℕ)) := hsqrt
    _ = B := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]

end

end Section57
end Ch05
end Book
end Homogenization
