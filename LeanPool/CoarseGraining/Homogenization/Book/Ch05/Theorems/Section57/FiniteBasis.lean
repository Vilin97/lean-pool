/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.LocalizedMax
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.FiniteNet

/-! # Finite Basis -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open Section54.VarianceBoundGoodScale
open scoped BigOperators

/-!
# Finite-basis reduction for the quenched unit-vector maximum

This file records the deterministic finite-dimensional reduction used in
Theorem `t.homogenization.quenched`: because the normalized block response is a
nonnegative quadratic form of the full-block vector, the maximum over unit
vectors is controlled by finitely many coordinate and pair probes.
-/

noncomputable section

private theorem fullBlockQuadratic_add
    {d : ℕ} (M N : FullBlockMat d) (q : FullBlockVec d) :
    fullBlockQuadratic (M + N) q =
      fullBlockQuadratic M q + fullBlockQuadratic N q := by
  unfold fullBlockQuadratic
  rw [Matrix.add_mulVec, dotProduct_add]

private theorem fullBlockQuadratic_smul
    {d : ℕ} (c : ℝ) (M : FullBlockMat d) (q : FullBlockVec d) :
    fullBlockQuadratic (c • M) q = c * fullBlockQuadratic M q := by
  unfold fullBlockQuadratic
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp [smul_eq_mul]

theorem fullBlockQuadratic_vec_smul
    {d : ℕ} (M : FullBlockMat d) (c : ℝ) (q : FullBlockVec d) :
    fullBlockQuadratic M (c • q) =
      c ^ (2 : ℕ) * fullBlockQuadratic M q := by
  unfold fullBlockQuadratic
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [pow_two, smul_eq_mul, mul_assoc]

private theorem fullBlockReflect_isSymm
    {d : ℕ} {M : FullBlockMat d} (hM : M.IsSymm) :
    (Ch04.fullBlockReflect M).IsSymm := by
  rw [Matrix.IsSymm]
  ext α β
  cases α <;> cases β
  all_goals
    simp [Ch04.fullBlockReflect, toFullBlockMat, ofFullBlockMat, blockReflect,
      Matrix.transpose_apply]
    try
      exact hM.apply _ _
    try
      exact (hM.apply _ _).symm

/-- The full-block matrix whose quadratic form is
`J(Q,\overline A^{-1/2}e,\overline A^{1/2}e)`. -/
noncomputable def limitNormalizedBlockJMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) (a : RegCoeffField d) : FullBlockMat d :=
  let M : FullBlockMat d := toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)
  let S : FullBlockMat d := scalarLimitInvSqrtMatrix hP hStruct
  let T : FullBlockMat d := scalarLimitSqrtMatrix hP hStruct
  (1 / 2 : ℝ) • (S * M * S) +
    (1 / 2 : ℝ) • (T * Ch04.fullBlockReflect M * T) -
      (1 : FullBlockMat d)

theorem limitNormalizedBlockJMatrix_isSymm_of_isSymmetricBlockMat
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {Q : TriadicCube d} {a : RegCoeffField d}
    (hA : IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) :
    (limitNormalizedBlockJMatrix hP hStruct Q a).IsSymm := by
  let M : FullBlockMat d := toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)
  let S : FullBlockMat d := scalarLimitInvSqrtMatrix hP hStruct
  let T : FullBlockMat d := scalarLimitSqrtMatrix hP hStruct
  have hM : M.IsSymm := by
    simpa [M] using isSymm_toFullBlockMat_of_isSymmetricBlockMat hA
  have hSM : (S * M * S).IsSymm := by
    simpa [S, scalarLimitInvSqrtMatrix] using
      isSymm_diagonal_mul_fullBlockMat_mul_diagonal
        (Ch04.scalarFullBlockInvSqrtDiag
          (d := d) (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))
        hM
  have hTM : (T * Ch04.fullBlockReflect M * T).IsSymm := by
    simpa [T, scalarLimitSqrtMatrix] using
      isSymm_diagonal_mul_fullBlockMat_mul_diagonal
        (Section56.scalarFullBlockSqrtDiag
          (d := d) (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))
        (fullBlockReflect_isSymm hM)
  simpa [limitNormalizedBlockJMatrix, M, S, T] using
    ((hSM.smul (1 / 2 : ℝ)).add (hTM.smul (1 / 2 : ℝ))).sub Matrix.isSymm_one

theorem limitNormalizedBlockJMatrix_isSymm_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) :
    ∀ᵐ a ∂P, (limitNormalizedBlockJMatrix hP hStruct Q a).IsSymm := by
  filter_upwards
    [isSymmetricBlockMat_coarseBlockMatrix_cubeSet_ae hP Q] with a hA
  exact limitNormalizedBlockJMatrix_isSymm_of_isSymmetricBlockMat
    hP hStruct hA

theorem limitNormalizedBlockJMatrix_quadratic_eq_blockJQuadratic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (e : FullBlockVec d) (a : RegCoeffField d) :
    fullBlockQuadratic (limitNormalizedBlockJMatrix hP hStruct Q a) e =
      Ch04.blockJQuadraticFullBlockMat
        (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e) := by
  let M : FullBlockMat d := toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)
  let A : BlockMat d := coarseBlockMatrix (cubeSet Q) a.toFun
  let S : FullBlockMat d := scalarLimitInvSqrtMatrix hP hStruct
  let T : FullBlockMat d := scalarLimitSqrtMatrix hP hStruct
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hP hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hP hStruct e
  have hfirst :
      fullBlockQuadratic (S * M * S) e =
        Ch04.fullBlockQuadraticCh04 M (toFullBlockVec Pvec) := by
    have hdiag :=
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
        (Ch04.scalarFullBlockInvSqrtDiag
          (d := d) (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))
        A e
    have hch4 :=
      (Ch04.fullBlockQuadraticCh04_toFullBlockMat A Pvec).symm
    calc
      fullBlockQuadratic (S * M * S) e =
          blockVecDot Pvec (blockMatVecMul A Pvec) := by
            simpa [S, M, A, Pvec, scalarLimitInvSqrtMatrix,
              scalarLimitInvSqrtBlockVec] using hdiag
      _ = Ch04.fullBlockQuadraticCh04 M (toFullBlockVec Pvec) := by
            simpa [M, A] using hch4
  have hsecond :
      fullBlockQuadratic (T * Ch04.fullBlockReflect M * T) e =
        Ch04.fullBlockQuadraticCh04 (Ch04.fullBlockReflect M)
          (toFullBlockVec Qvec) := by
    let Aref : BlockMat d := blockReflect (ofFullBlockMat M)
    have href : Ch04.fullBlockReflect M = toFullBlockMat Aref := by
      simp [Aref, Ch04.fullBlockReflect]
    have hdiag :=
      fullBlockQuadratic_diagonal_toFullBlockMat_eq_blockVecDot
        (Section56.scalarFullBlockSqrtDiag
          (d := d) (barSigmaLimit hP hStruct) (barSigmaLimit hP hStruct))
        Aref e
    have hch4 :=
      (Ch04.fullBlockQuadraticCh04_toFullBlockMat Aref Qvec).symm
    calc
      fullBlockQuadratic (T * Ch04.fullBlockReflect M * T) e =
          fullBlockQuadratic (T * toFullBlockMat Aref * T) e := by
            rw [href]
      _ = blockVecDot Qvec (blockMatVecMul Aref Qvec) := by
            simpa [T, Aref, Qvec, scalarLimitSqrtMatrix,
              scalarLimitSqrtBlockVec] using hdiag
      _ =
          Ch04.fullBlockQuadraticCh04 (Ch04.fullBlockReflect M)
            (toFullBlockVec Qvec) := by
            simpa [href] using hch4
  have hpair :
      blockVecDot Pvec Qvec = dotProduct e e := by
    simpa [Pvec, Qvec] using hΓ.scalarLimit_normalizers_pairing_eq_dotProduct e
  calc
    fullBlockQuadratic (limitNormalizedBlockJMatrix hP hStruct Q a) e =
        (1 / 2 : ℝ) * fullBlockQuadratic (S * M * S) e +
          (1 / 2 : ℝ) *
            fullBlockQuadratic (T * Ch04.fullBlockReflect M * T) e -
          dotProduct e e := by
          simp [limitNormalizedBlockJMatrix, M, S, T,
            fullBlockQuadratic_add, fullBlockQuadratic_smul,
            fullBlockQuadratic_sub, fullBlockQuadratic_one]
    _ =
        Ch04.blockJQuadraticFullBlockMat M Pvec Qvec := by
          simp [Ch04.blockJQuadraticFullBlockMat, hfirst, hsecond, hpair]
    _ =
        Ch04.blockJQuadraticFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
          (scalarLimitInvSqrtBlockVec hP hStruct e)
          (scalarLimitSqrtBlockVec hP hStruct e) := by
          rfl

theorem limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (e : FullBlockVec d) :
    limitNormalizedBlockJObservable hP hStruct Q e =ᵐ[P]
      fun a : RegCoeffField d =>
        fullBlockQuadratic (limitNormalizedBlockJMatrix hP hStruct Q a) e := by
  have hJ :
      limitNormalizedBlockJObservable hP hStruct Q e =ᵐ[P]
        fun a : RegCoeffField d =>
          Ch04.blockJQuadraticFullBlockMat
            (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
            (scalarLimitInvSqrtBlockVec hP hStruct e)
            (scalarLimitSqrtBlockVec hP hStruct e) := by
    simpa [limitNormalizedBlockJObservable] using
      Ch04.blockJObservableCubeSetBlockVec_ae_eq_blockJQuadraticFullBlockMat
        hP Q
        (scalarLimitInvSqrtBlockVec hP hStruct e)
        (scalarLimitSqrtBlockVec hP hStruct e)
  filter_upwards [hJ] with a hJ_a
  rw [hJ_a]
  exact (limitNormalizedBlockJMatrix_quadratic_eq_blockJQuadratic
    hP hStruct hΓ Q e a).symm

theorem limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (e : FullBlockVec d) :
    limitNormalizedBlockJObservable hP hStruct Q e a =
      fullBlockQuadratic (limitNormalizedBlockJMatrix hP hStruct Q a) e := by
  calc
    limitNormalizedBlockJObservable hP hStruct Q e a =
        Ch04.blockJQuadraticFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
          (scalarLimitInvSqrtBlockVec hP hStruct e)
          (scalarLimitSqrtBlockVec hP hStruct e) := by
          simpa [limitNormalizedBlockJObservable] using
            Ch04.blockJObservableCubeSetBlockVec_eq_blockJQuadraticFullBlockMat_of_aelocallyUniformlyEllipticField
              ha Q
              (scalarLimitInvSqrtBlockVec hP hStruct e)
              (scalarLimitSqrtBlockVec hP hStruct e)
    _ =
        fullBlockQuadratic (limitNormalizedBlockJMatrix hP hStruct Q a) e :=
          (limitNormalizedBlockJMatrix_quadratic_eq_blockJQuadratic
            hP hStruct hΓ Q e a).symm

theorem limitNormalizedBlockJObservable_smul_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (c : ℝ) (e : FullBlockVec d) :
    limitNormalizedBlockJObservable hP hStruct Q (c • e) =ᵐ[P]
      fun a : RegCoeffField d =>
        c ^ (2 : ℕ) * limitNormalizedBlockJObservable hP hStruct Q e a := by
  have hEq_ce :=
    limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
      hP hStruct hΓ Q (c • e)
  have hEq_e :=
    limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
      hP hStruct hΓ Q e
  filter_upwards [hEq_ce, hEq_e] with a hce he
  rw [hce, he]
  exact fullBlockQuadratic_vec_smul
    (limitNormalizedBlockJMatrix hP hStruct Q a) c e

/-- Finite coordinate and pair probes for the limiting-normalized `J`
quadratic on one cube. -/
noncomputable def limitNormalizedJProbeSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) : RegCoeffField d → ℝ :=
  fun a =>
    ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      (limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockCoordinateProbe α) a +
        limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockPlusProbe α β) a +
        limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockMinusProbe α β) a)

/-- The normalized finite probe sum: coordinate probes are unchanged, while
plus/minus pair probes are scaled by `1/2` so their Euclidean square norm is at
most one. -/
noncomputable def limitNormalizedJNormalizedProbeSum
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) : RegCoeffField d → ℝ :=
  fun a =>
    ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      (limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockCoordinateProbe α) a +
        limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a +
        limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a)

private theorem limitNormalizedBlockJObservable_probe_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (Q : TriadicCube d) (e : FullBlockVec d) (a : RegCoeffField d) :
    0 ≤ limitNormalizedBlockJObservable hP hStruct Q e a := by
  simpa [limitNormalizedBlockJObservable] using
    Ch04.blockJObservableCubeSetBlockVec_nonneg Q
      (scalarLimitInvSqrtBlockVec hP hStruct e)
      (scalarLimitSqrtBlockVec hP hStruct e) a

/-- Pointwise finite-basis control for a sampled coefficient field carrying an
a.e.-ellipticity witness.  This is the simultaneous version needed when the
unit-vector supremum is packaged into a Chapter 2 scale response. -/
theorem limitNormalizedBlockJObservable_le_probeSum_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    {a : RegCoeffField d} (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (e : FullBlockVec d)
    (he : dotProduct e e ≤ 1) :
    limitNormalizedBlockJObservable hP hStruct Q e a ≤
      (Fintype.card (BlockCoord d) : ℝ) *
        limitNormalizedJProbeSum hP hStruct Q a := by
  classical
  let card : ℝ := (Fintype.card (BlockCoord d) : ℝ)
  let K : RegCoeffField d → FullBlockMat d :=
    fun a => limitNormalizedBlockJMatrix hP hStruct Q a
  let M : FullBlockMat d := K a
  have hA :
      IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) := by
    let F : Ch02.TriadicCoeffFamily d :=
      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    have hcoarse :
        coarseBlockMatrix (cubeSet Q) a.toFun =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
      simpa [F] using
        Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
          (a := a) ha Q
    rw [hcoarse]
    exact Ch02.isSymmetricBlockMat_coarseBlockMatrix
      (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hKsymm : M.IsSymm := by
    simpa [M, K] using
      limitNormalizedBlockJMatrix_isSymm_of_isSymmetricBlockMat
        hP hStruct hA
  have hEqe :
      limitNormalizedBlockJObservable hP hStruct Q e a =
        fullBlockQuadratic M e := by
    simpa [M, K] using
      limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
        hP hStruct hΓ ha Q e
  have hcoord :
      ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockCoordinateProbe α) a =
          fullBlockQuadratic M (fullBlockCoordinateProbe α) := by
    intro α _hα
    simpa [M, K] using
      limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
        hP hStruct hΓ ha Q (fullBlockCoordinateProbe α)
  have hplus :
      ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockPlusProbe α β) a =
          fullBlockQuadratic M (fullBlockPlusProbe α β) := by
    intro α _hα β _hβ
    simpa [M, K] using
      limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
        hP hStruct hΓ ha Q (fullBlockPlusProbe α β)
  have hminus :
      ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockMinusProbe α β) a =
          fullBlockQuadratic M (fullBlockMinusProbe α β) := by
    intro α _hα β _hβ
    simpa [M, K] using
      limitNormalizedBlockJObservable_eq_limitNormalizedBlockJMatrix_quadratic_of_aelocallyUniformlyEllipticField
        hP hStruct hΓ ha Q (fullBlockMinusProbe α β)
  have hquad_abs :
      |fullBlockQuadratic M e| ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := by
    have hsq :=
      fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq M e
    have hdot_nonneg : 0 ≤ dotProduct e e := dotProduct_self_nonneg e
    have hright_nonneg :
        0 ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := mul_nonneg (norm_nonneg _) hdot_nonneg
    have hsq' :
        |fullBlockQuadratic M e| ^ (2 : ℕ) ≤
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
            dotProduct e e) ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    exact (sq_le_sq₀ (abs_nonneg _) hright_nonneg).1 hsq'
  have hop :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ≤
        card * fullBlockProbeAbsSum M := by
    simpa [M, card] using fullBlock_operatorNorm_le_probeAbsSum hKsymm
  have hprobe_nonneg : 0 ≤ fullBlockProbeAbsSum M :=
    fullBlockProbeAbsSum_nonneg M
  have hcard_nonneg : 0 ≤ card := by
    dsimp [card]
    positivity
  have hprobe_eq :
      fullBlockProbeAbsSum M =
        limitNormalizedJProbeSum hP hStruct Q a := by
    unfold fullBlockProbeAbsSum limitNormalizedJProbeSum
    refine Finset.sum_congr rfl ?_
    intro α _hα
    refine Finset.sum_congr rfl ?_
    intro β _hβ
    have hcoord_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockCoordinateProbe α) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockCoordinateProbe α) a
    have hplus_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockPlusProbe α β) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockPlusProbe α β) a
    have hminus_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockMinusProbe α β) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockMinusProbe α β) a
    rw [← hcoord α (Finset.mem_univ α),
      ← hplus α (Finset.mem_univ α) β (Finset.mem_univ β),
      ← hminus α (Finset.mem_univ α) β (Finset.mem_univ β)]
    simp [abs_of_nonneg hcoord_nonneg, abs_of_nonneg hplus_nonneg,
      abs_of_nonneg hminus_nonneg]
  calc
    limitNormalizedBlockJObservable hP hStruct Q e a =
        fullBlockQuadratic M e := hEqe
    _ ≤ |fullBlockQuadratic M e| := le_abs_self _
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := hquad_abs
    _ ≤ (card * fullBlockProbeAbsSum M) * dotProduct e e :=
        mul_le_mul_of_nonneg_right hop (dotProduct_self_nonneg e)
    _ ≤ (card * fullBlockProbeAbsSum M) * 1 := by
        exact mul_le_mul_of_nonneg_left he
          (mul_nonneg hcard_nonneg hprobe_nonneg)
    _ = card * limitNormalizedJProbeSum hP hStruct Q a := by
        rw [hprobe_eq]
        ring

theorem limitNormalizedJProbeSum_le_four_normalizedProbeSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) :
    (limitNormalizedJProbeSum hP hStruct Q) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        4 * limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
  classical
  have hPlus :
      ∀ᵐ a ∂P, ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockPlusProbe α β) a =
          4 * limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a := by
    rw [Filter.eventually_all_finset]
    intro α _hα
    rw [Filter.eventually_all_finset]
    intro β _hβ
    have h :=
      limitNormalizedBlockJObservable_smul_ae hP hStruct hΓ Q
        (2 : ℝ) ((1 / 2 : ℝ) • fullBlockPlusProbe α β)
    filter_upwards [h] with a ha
    calc
      limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockPlusProbe α β) a =
        2 * 2 * limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a := by
          simpa [smul_smul, pow_two] using ha
      _ =
        4 * limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a := by
          ring
  have hMinus :
      ∀ᵐ a ∂P, ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockMinusProbe α β) a =
          4 * limitNormalizedBlockJObservable hP hStruct Q
            ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a := by
    rw [Filter.eventually_all_finset]
    intro α _hα
    rw [Filter.eventually_all_finset]
    intro β _hβ
    have h :=
      limitNormalizedBlockJObservable_smul_ae hP hStruct hΓ Q
        (2 : ℝ) ((1 / 2 : ℝ) • fullBlockMinusProbe α β)
    filter_upwards [h] with a ha
    calc
      limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockMinusProbe α β) a =
        2 * 2 * limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a := by
          simpa [smul_smul, pow_two] using ha
      _ =
        4 * limitNormalizedBlockJObservable hP hStruct Q
          ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a := by
          ring
  filter_upwards [hPlus, hMinus] with a hplus hminus
  unfold limitNormalizedJProbeSum limitNormalizedJNormalizedProbeSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro α _hα
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro β _hβ
  rw [hplus α (Finset.mem_univ α) β (Finset.mem_univ β),
    hminus α (Finset.mem_univ α) β (Finset.mem_univ β)]
  have hcoord_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        (fullBlockCoordinateProbe α) a :=
    limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
      (fullBlockCoordinateProbe α) a
  have hplus_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a :=
    limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
      ((1 / 2 : ℝ) • fullBlockPlusProbe α β) a
  have hminus_nonneg :
      0 ≤ limitNormalizedBlockJObservable hP hStruct Q
        ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a :=
    limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
      ((1 / 2 : ℝ) • fullBlockMinusProbe α β) a
  nlinarith

theorem limitNormalizedBlockJObservable_le_probeSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (e : FullBlockVec d)
    (he : dotProduct e e ≤ 1) :
    (limitNormalizedBlockJObservable hP hStruct Q e) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        (Fintype.card (BlockCoord d) : ℝ) *
          limitNormalizedJProbeSum hP hStruct Q a := by
  classical
  let card : ℝ := (Fintype.card (BlockCoord d) : ℝ)
  let K : RegCoeffField d → FullBlockMat d :=
    fun a => limitNormalizedBlockJMatrix hP hStruct Q a
  have hEq_e :
      limitNormalizedBlockJObservable hP hStruct Q e =ᵐ[P]
        fun a : RegCoeffField d => fullBlockQuadratic (K a) e := by
    simpa [K] using
      limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
        hP hStruct hΓ Q e
  have hEq_coord :
      ∀ᵐ a ∂P, ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockCoordinateProbe α) a =
          fullBlockQuadratic (K a) (fullBlockCoordinateProbe α) := by
    rw [Filter.eventually_all_finset]
    intro α _hα
    simpa [K] using!
      limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
        hP hStruct hΓ Q (fullBlockCoordinateProbe α)
  have hEq_plus :
      ∀ᵐ a ∂P, ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockPlusProbe α β) a =
          fullBlockQuadratic (K a) (fullBlockPlusProbe α β) := by
    rw [Filter.eventually_all_finset]
    intro α _hα
    rw [Filter.eventually_all_finset]
    intro β _hβ
    simpa [K] using!
      limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
        hP hStruct hΓ Q (fullBlockPlusProbe α β)
  have hEq_minus :
      ∀ᵐ a ∂P, ∀ α ∈ (Finset.univ : Finset (BlockCoord d)),
        ∀ β ∈ (Finset.univ : Finset (BlockCoord d)),
        limitNormalizedBlockJObservable hP hStruct Q
            (fullBlockMinusProbe α β) a =
          fullBlockQuadratic (K a) (fullBlockMinusProbe α β) := by
    rw [Filter.eventually_all_finset]
    intro α _hα
    rw [Filter.eventually_all_finset]
    intro β _hβ
    simpa [K] using!
      limitNormalizedBlockJObservable_ae_eq_limitNormalizedBlockJMatrix_quadratic
        hP hStruct hΓ Q (fullBlockMinusProbe α β)
  filter_upwards
    [hEq_e, limitNormalizedBlockJMatrix_isSymm_ae hP hStruct Q,
      hEq_coord, hEq_plus, hEq_minus] with
    a hEqe hKsymm hcoord hplus hminus
  let M : FullBlockMat d := K a
  have hquad_abs :
      |fullBlockQuadratic M e| ≤
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := by
    have hsq :=
      fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq M e
    have hdot_nonneg : 0 ≤ dotProduct e e := dotProduct_self_nonneg e
    have hright_nonneg :
        0 ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := mul_nonneg (norm_nonneg _) hdot_nonneg
    have hsq' :
        |fullBlockQuadratic M e| ^ (2 : ℕ) ≤
          (‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
            dotProduct e e) ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    exact (sq_le_sq₀ (abs_nonneg _) hright_nonneg).1 hsq'
  have hop :
      ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ≤
        card * fullBlockProbeAbsSum M := by
    simpa [M, card] using fullBlock_operatorNorm_le_probeAbsSum hKsymm
  have hprobe_nonneg : 0 ≤ fullBlockProbeAbsSum M :=
    fullBlockProbeAbsSum_nonneg M
  have hcard_nonneg : 0 ≤ card := by
    dsimp [card]
    positivity
  have hprobe_eq :
      fullBlockProbeAbsSum M =
        limitNormalizedJProbeSum hP hStruct Q a := by
    unfold fullBlockProbeAbsSum limitNormalizedJProbeSum
    refine Finset.sum_congr rfl ?_
    intro α _hα
    refine Finset.sum_congr rfl ?_
    intro β _hβ
    have hcoord_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockCoordinateProbe α) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockCoordinateProbe α) a
    have hplus_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockPlusProbe α β) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockPlusProbe α β) a
    have hminus_nonneg :
        0 ≤ limitNormalizedBlockJObservable hP hStruct Q
          (fullBlockMinusProbe α β) a :=
      limitNormalizedBlockJObservable_probe_nonneg hP hStruct Q
        (fullBlockMinusProbe α β) a
    rw [← hcoord α (Finset.mem_univ α),
      ← hplus α (Finset.mem_univ α) β (Finset.mem_univ β),
      ← hminus α (Finset.mem_univ α) β (Finset.mem_univ β)]
    simp [abs_of_nonneg hcoord_nonneg, abs_of_nonneg hplus_nonneg,
      abs_of_nonneg hminus_nonneg]
  calc
    limitNormalizedBlockJObservable hP hStruct Q e a =
        fullBlockQuadratic M e := by
          simpa [M] using hEqe
    _ ≤ |fullBlockQuadratic M e| := le_abs_self _
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          dotProduct e e := hquad_abs
    _ ≤ (card * fullBlockProbeAbsSum M) * dotProduct e e :=
        mul_le_mul_of_nonneg_right hop (dotProduct_self_nonneg e)
    _ ≤ (card * fullBlockProbeAbsSum M) * 1 := by
        exact mul_le_mul_of_nonneg_left he
          (mul_nonneg hcard_nonneg hprobe_nonneg)
    _ = card * limitNormalizedJProbeSum hP hStruct Q a := by
        rw [hprobe_eq]
        ring

theorem limitNormalizedBlockJObservable_le_normalizedProbeSum_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (Q : TriadicCube d) (e : FullBlockVec d)
    (he : dotProduct e e ≤ 1) :
    (limitNormalizedBlockJObservable hP hStruct Q e) ≤ᵐ[P]
      fun a : RegCoeffField d =>
        (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
  have hle :=
    limitNormalizedBlockJObservable_le_probeSum_ae hP hStruct hΓ Q e he
  have hprobe :=
    limitNormalizedJProbeSum_le_four_normalizedProbeSum_ae hP hStruct hΓ Q
  filter_upwards [hle, hprobe] with a hle_a hprobe_a
  have hcard_nonneg : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) := by
    positivity
  calc
    limitNormalizedBlockJObservable hP hStruct Q e a
        ≤ (Fintype.card (BlockCoord d) : ℝ) *
            limitNormalizedJProbeSum hP hStruct Q a := hle_a
    _ ≤ (Fintype.card (BlockCoord d) : ℝ) *
          (4 * limitNormalizedJNormalizedProbeSum hP hStruct Q a) := by
        exact mul_le_mul_of_nonneg_left hprobe_a hcard_nonneg
    _ =
        (4 * (Fintype.card (BlockCoord d) : ℝ)) *
          limitNormalizedJNormalizedProbeSum hP hStruct Q a := by
        ring

end

end Section57
end Ch05
end Book
end Homogenization
