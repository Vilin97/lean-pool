/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.BlockExpectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.WrapAround
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FluctuationIntegrability
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScaleCompression
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.NoncommRing

/-! # Basic -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

/-!
# Section 5.6: variance triangle for normalized block fluctuations

This file records the part of Lemma `l.variance.estimate.quadratic` in which
the manuscript variance is interpreted by the Section 5.4 squared
Euclidean-operator-norm fluctuation observable.
-/

/-- Entrywise descendant average of full block matrices. -/
noncomputable def descendantsAverageFullBlockMat {d : ℕ}
    (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → FullBlockMat d) : FullBlockMat d :=
  fun α β => descendantsAverage Q j (fun R => F R α β)

/-- The normalized fluctuation matrix of the descendant-average coarse block. -/
noncomputable def descendantsAverageNormalizedFluctuationMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    FullBlockMat d :=
  descendantsAverageFullBlockMat Q j
    (fun R =>
      Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
        hP hStruct center (cubeSet R) a)

/-- Squared operator norm of the normalized descendant-average fluctuation. -/
noncomputable def descendantsAverageNormalizedFluctuationOperatorNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a)‖ ^
    (2 : ℕ)

/-- Normalized difference between the parent fluctuation and the descendant
average fluctuation.  This is the operator-norm error term before it is
estimated by block `J`. -/
noncomputable def normalizedCoarseAverageErrorMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    FullBlockMat d :=
  Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct center (cubeSet Q) a -
    descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a

/-- The positive coarse-average defect, with the sign used by block
subadditivity. Its squared operator norm is the same as
`normalizedCoarseAverageErrorMatrix`. -/
noncomputable def normalizedCoarseAveragePositiveErrorMatrix
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    FullBlockMat d :=
  descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a -
    Section54.VarianceBoundGoodScale.fullBlockNormalizedFluctuationMatrix
      hP hStruct center (cubeSet Q) a

/-- Squared operator norm of the normalized parent-minus-descendant-average
error. -/
noncomputable def normalizedCoarseAverageErrorOperatorNormSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (normalizedCoarseAverageErrorMatrix hP hStruct center Q j a)‖ ^
    (2 : ℕ)

/-- Full-block fluctuation normalized by an arbitrary deterministic matrix.
For the manuscript lemma, take `S = B^{-1/2}`; the congruence is written as
`Sᵀ M S`, which agrees with `B^{-1/2} M B^{-1/2}` for the symmetric positive
definite square root. -/
noncomputable def fullBlockFluctuationMatrixWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) : FullBlockMat d :=
  let A := coarseBlockMatrix U a
  let Abar := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  Matrix.transpose S * (toFullBlockMat A - toFullBlockMat Abar) * S

/-- Squared operator norm of the arbitrary-normalizer full-block fluctuation. -/
noncomputable def fullBlockFluctuationOperatorNormSqWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (U : Set (Vec d))
    (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (fullBlockFluctuationMatrixWithNormalizer hP hStruct center S U a)‖ ^
    (2 : ℕ)

/-- Arbitrary-normalizer full-block fluctuation on a triadic cube. -/
noncomputable def fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d)
    (a : RegCoeffField d) : ℝ :=
  fullBlockFluctuationOperatorNormSqWithNormalizer
    hP hStruct center S (cubeSet Q) a

/-- Descendant average of arbitrary-normalizer full-block fluctuation
matrices. -/
noncomputable def descendantsAverageFluctuationMatrixWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : FullBlockMat d :=
  descendantsAverageFullBlockMat Q j
    (fun R =>
      fullBlockFluctuationMatrixWithNormalizer hP hStruct center S
        (cubeSet R) a)

/-- Squared operator norm of the descendant-average arbitrary-normalizer
fluctuation matrix. -/
noncomputable def descendantsAverageFluctuationOperatorNormSqWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct center S Q j a)‖ ^ (2 : ℕ)

/-- Parent-minus-descendant-average error for an arbitrary normalizer. -/
noncomputable def coarseAverageErrorMatrixWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : FullBlockMat d :=
  fullBlockFluctuationMatrixWithNormalizer hP hStruct center S (cubeSet Q) a -
    descendantsAverageFluctuationMatrixWithNormalizer hP hStruct center S Q j a

/-- Descendant-average-minus-parent error for an arbitrary normalizer, with the
sign used by block subadditivity. -/
noncomputable def coarseAveragePositiveErrorMatrixWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : FullBlockMat d :=
  descendantsAverageFluctuationMatrixWithNormalizer hP hStruct center S Q j a -
    fullBlockFluctuationMatrixWithNormalizer hP hStruct center S (cubeSet Q) a

/-- Squared operator norm of the arbitrary-normalizer parent-minus-descendant
average error. -/
noncomputable def coarseAverageErrorOperatorNormSqWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
      (coarseAverageErrorMatrixWithNormalizer hP hStruct center S Q j a)‖ ^
    (2 : ℕ)

/-- The Ch4 block response observable, repackaged using the two block vectors
`P` and `Q`.  The ordering matches the doubled formalism:
`BlockJ (p,q) (qStar,pStar)` is stored as
`blockJObservableCubeSet Q p pStar q qStar`. -/
noncomputable def blockJObservableCubeSetBlockVec {d : ℕ}
    (Q : TriadicCube d) (P Qv : BlockVec d) : RegCoeffField d → ℝ :=
  Ch04.blockJObservableCubeSet Q P.1 Qv.2 P.2 Qv.1

/-- Coordinate probe associated with an arbitrary full-block matrix. -/
noncomputable def fullBlockMatrixProbe {d : ℕ}
    (S : FullBlockMat d) (α : BlockCoord d) : BlockVec d :=
  ofFullBlockVec (Matrix.mulVec S (Pi.single α 1))

/-- The trace-type descendant-average `J` budget with arbitrary deterministic
normalizers.  In the manuscript case, use `S = B^{-1/2}` and `T = B^{1/2}`. -/
noncomputable def blockJTraceAverageWithNormalizers
    {d : ℕ} (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  descendantsAverage Q j
    (fun R =>
      ∑ α : BlockCoord d,
        blockJObservableCubeSetBlockVec R
          (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a)

/-- Squared trace-type descendant-average `J` budget with arbitrary
normalizers. -/
noncomputable def blockJTraceAverageSqWithNormalizers
    {d : ℕ} (S T : FullBlockMat d) (Q : TriadicCube d) (j : ℕ)
    (a : RegCoeffField d) : ℝ :=
  blockJTraceAverageWithNormalizers S T Q j a ^ (2 : ℕ)

/-- Diagonal square-root multiplier dual to `Ch04.scalarFullBlockInvSqrtDiag`.
For the lower starred block the scalar block is `c⁻¹`, hence the square-root
multiplier is `(sqrt c)⁻¹`. -/
noncomputable def scalarFullBlockSqrtDiag {d : ℕ} (b c : ℝ) :
    BlockCoord d → ℝ
  | Sum.inl _ => Real.sqrt b
  | Sum.inr _ => (Real.sqrt c)⁻¹

/-- Coordinate probe `B^{-1/2} e_α` for the scalar block normalization at the
center scale. -/
noncomputable def normalizedInvSqrtBlockProbe
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α : BlockCoord d) : BlockVec d :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  ofFullBlockVec (Pi.single α (Ch04.scalarFullBlockInvSqrtDiag b c α))

/-- Coordinate probe `B^{1/2} e_α` for the scalar block normalization at the
center scale. -/
noncomputable def normalizedSqrtBlockProbe
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (α : BlockCoord d) : BlockVec d :=
  let b := hP.barSigmaAtScale hStruct center
  let c := hP.barSigmaStarAtScale hStruct center
  ofFullBlockVec (Pi.single α (scalarFullBlockSqrtDiag b c α))

/-- The manuscript trace-type descendant average
`avg_R sum_i J(R,B^{-1/2}e_i,B^{1/2}e_i)`, written for the scalar block
normalization used by the Section 5.4 fluctuation observable. -/
noncomputable def normalizedBlockJTraceAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  descendantsAverage Q j
    (fun R =>
      ∑ α : BlockCoord d,
        blockJObservableCubeSetBlockVec R
          (normalizedInvSqrtBlockProbe hP hStruct center α)
          (normalizedSqrtBlockProbe hP hStruct center α) a)

/-- The upper-coordinate part of `normalizedBlockJTraceAverage`.  The
wrap-around trace estimate naturally produces this half of the full block
trace budget; the lower half is nonnegative and is added back below. -/
noncomputable def normalizedUpperBlockJTraceAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  descendantsAverage Q j
    (fun R =>
      ∑ i : Fin d,
        blockJObservableCubeSetBlockVec R
          (normalizedInvSqrtBlockProbe hP hStruct center (Sum.inl i))
          (normalizedSqrtBlockProbe hP hStruct center (Sum.inl i)) a)

/-- Squared trace-type descendant average of the normalized block responses. -/
noncomputable def normalizedBlockJTraceAverageSq
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) : ℝ :=
  normalizedBlockJTraceAverage hP hStruct center Q j a ^ (2 : ℕ)

theorem blockJObservableCubeSetBlockVec_nonneg {d : ℕ}
    (Q : TriadicCube d) (P Qv : BlockVec d) (a : RegCoeffField d) :
    0 ≤ blockJObservableCubeSetBlockVec Q P Qv a := by
  rcases P with ⟨p, q⟩
  rcases Qv with ⟨qStar, pStar⟩
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (Ch04.restrictionResponseJObservableCubeSet_nonneg Q (p - pStar) (qStar - q) a))
    (mul_nonneg (by norm_num)
      (Ch04.restrictionResponseJObservableCubeSet_nonneg Q (pStar + p) (qStar + q)
        (adjointReg a)))

theorem normalizedBlockJTraceAverage_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    0 ≤ normalizedBlockJTraceAverage hP hStruct center Q j a := by
  classical
  unfold normalizedBlockJTraceAverage
  exact descendantsAverage_nonneg Q j
    (fun R =>
      ∑ α : BlockCoord d,
        blockJObservableCubeSetBlockVec R
          (normalizedInvSqrtBlockProbe hP hStruct center α)
          (normalizedSqrtBlockProbe hP hStruct center α) a)
    (fun R _hR =>
      Finset.sum_nonneg fun α _hα =>
        blockJObservableCubeSetBlockVec_nonneg R
          (normalizedInvSqrtBlockProbe hP hStruct center α)
          (normalizedSqrtBlockProbe hP hStruct center α) a)

theorem normalizedUpperBlockJTraceAverage_le_normalizedBlockJTraceAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    normalizedUpperBlockJTraceAverage hP hStruct center Q j a ≤
      normalizedBlockJTraceAverage hP hStruct center Q j a := by
  classical
  unfold normalizedUpperBlockJTraceAverage normalizedBlockJTraceAverage
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R _hR
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _hi =>
      blockJObservableCubeSetBlockVec_nonneg R
        (normalizedInvSqrtBlockProbe hP hStruct center (Sum.inr i))
        (normalizedSqrtBlockProbe hP hStruct center (Sum.inr i)) a)

theorem normalizedBlockJTraceAverageSq_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) (a : RegCoeffField d) :
    0 ≤ normalizedBlockJTraceAverageSq hP hStruct center Q j a := by
  unfold normalizedBlockJTraceAverageSq
  exact sq_nonneg _

theorem memLp_two_comp_adjointCoeffField
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {X : RegCoeffField d → ℝ}
    (hAdj : Ch04.RestrictionAdjointInvariantLaw P) (hX : MemLp X (2 : ENNReal) P) :
    MemLp (fun a : RegCoeffField d => X (adjointReg a)) (2 : ENNReal) P := by
  have hmap : MemLp X (2 : ENNReal) (Measure.map adjointReg P) := by
    exact hAdj.symm ▸ hX
  exact hmap.comp_of_map measurable_adjointReg.aemeasurable

theorem memLp_two_blockJObservableCubeSetBlockVec_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (R : TriadicCube d) (hR_nonneg : 0 ≤ R.scale) (Pvec Qvec : BlockVec d) :
    MemLp (blockJObservableCubeSetBlockVec R Pvec Qvec) (2 : ENNReal) P := by
  rcases Pvec with ⟨p, q⟩
  rcases Qvec with ⟨qStar, pStar⟩
  have hJ₁ :
      MemLp (Ch04.restrictionResponseJObservableCubeSet R (p - pStar) (qStar - q))
        (2 : ENNReal) P :=
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.memLp_two_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
        hP hStruct.stationary hStruct hP4 R hR_nonneg (p - pStar) (qStar - q)
  have hJ₂base :
      MemLp (Ch04.restrictionResponseJObservableCubeSet R (pStar + p) (qStar + q))
        (2 : ENNReal) P :=
    Homogenization.Book.Ch05.Section53.JUpperBoundCoarseFluctuations.memLp_two_restrictionResponseJObservableCubeSet_cubeSet_from_P4_of_stationary
        hP hStruct.stationary hStruct hP4 R hR_nonneg (pStar + p) (qStar + q)
  have hJ₂ :
      MemLp
        (fun a : RegCoeffField d =>
          Ch04.restrictionResponseJObservableCubeSet R (pStar + p) (qStar + q)
            (adjointReg a))
        (2 : ENNReal) P :=
    memLp_two_comp_adjointCoeffField hStruct.adjoint_invariant hJ₂base
  have hsum :
      MemLp
        (fun a : RegCoeffField d =>
          (1 / 2 : ℝ) *
              Ch04.restrictionResponseJObservableCubeSet R (p - pStar) (qStar - q) a +
            (1 / 2 : ℝ) *
              Ch04.restrictionResponseJObservableCubeSet R (pStar + p) (qStar + q)
                (adjointReg a))
        (2 : ENNReal) P :=
    (hJ₁.const_mul (1 / 2 : ℝ)).add (hJ₂.const_mul (1 / 2 : ℝ))
  change
    MemLp
      (fun a : RegCoeffField d =>
        (1 / 2 : ℝ) *
            Ch04.restrictionResponseJObservableCubeSet R (p - pStar) (qStar - q) a +
          (1 / 2 : ℝ) *
            Ch04.restrictionResponseJObservableCubeSet R (pStar + p) (qStar + q)
              (adjointReg a))
      (2 : ENNReal) P
  exact hsum

theorem memLp_two_normalizedBlockJTraceAverage_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (_hk : k ≤ n) :
    MemLp
      (normalizedBlockJTraceAverage hP hStruct (m : ℤ)
        (originCube d (n : ℤ)) (n - k))
      (2 : ENNReal) P := by
  classical
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  have hchild :
      ∀ R, R ∈ descendantsAtDepth Q j →
        MemLp
          (fun a : RegCoeffField d =>
            ∑ α : BlockCoord d,
              blockJObservableCubeSetBlockVec R
                (normalizedInvSqrtBlockProbe hP hStruct (m : ℤ) α)
                (normalizedSqrtBlockProbe hP hStruct (m : ℤ) α) a)
          (2 : ENNReal) P := by
    intro R hR
    have hR_nonneg : 0 ≤ R.scale := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      have hQscale : Q.scale = (n : ℤ) := by simp [Q, originCube]
      rw [hscale, hQscale]
      have hj_le : j ≤ n := by
        dsimp [j]
        exact Nat.sub_le n k
      exact sub_nonneg.mpr (by exact_mod_cast hj_le)
    exact MeasureTheory.memLp_finsetSum Finset.univ
      (fun α _hα =>
        memLp_two_blockJObservableCubeSetBlockVec_from_P4_of_stationary
          hP hStruct hP4 R hR_nonneg
          (normalizedInvSqrtBlockProbe hP hStruct (m : ℤ) α)
          (normalizedSqrtBlockProbe hP hStruct (m : ℤ) α))
  change
    MemLp
      (fun a : RegCoeffField d =>
        descendantsAverage (originCube d (n : ℤ)) (n - k)
          (fun R =>
            ∑ α : BlockCoord d,
              blockJObservableCubeSetBlockVec R
                (normalizedInvSqrtBlockProbe hP hStruct (m : ℤ) α)
                (normalizedSqrtBlockProbe hP hStruct (m : ℤ) α) a))
      (2 : ENNReal) P
  simpa [Q, j] using
    Ch04.memLp_descendantsAverage (P := P) (Q := Q) (j := j)
      (F := fun R a =>
        ∑ α : BlockCoord d,
          blockJObservableCubeSetBlockVec R
            (normalizedInvSqrtBlockProbe hP hStruct (m : ℤ) α)
            (normalizedSqrtBlockProbe hP hStruct (m : ℤ) α) a)
      hchild

theorem integrable_normalizedBlockJTraceAverageSq_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) :
    Integrable
      (normalizedBlockJTraceAverageSq hP hStruct (m : ℤ)
        (originCube d (n : ℤ)) (n - k)) P := by
  have hmem :=
    memLp_two_normalizedBlockJTraceAverage_from_P4_of_stationary
      hP hStruct hP4 m n k hk
  simpa [normalizedBlockJTraceAverageSq, Real.norm_eq_abs, sq_abs] using!
    hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

theorem doubledResponseJ_eq_blockJObservableCubeSetBlockVec_of_aelocallyUniformlyEllipticField
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d)
    (P Qv : BlockVec d) :
    Ch02.doubledResponseJ (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)
        P Qv =
      blockJObservableCubeSetBlockVec Q P Qv a := by
  rcases P with ⟨p, q⟩
  rcases Qv with ⟨qStar, pStar⟩
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hresp₁ :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (p - pStar) (qStar - q) =
        Ch04.restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q)
          (p - pStar) (qStar - q)
          = ResponseJ (openCubeSet Q) (p - pStar) (qStar - q) a.toFun := by
              simpa [F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                Ch04.coeffOnOfAEEllipticOn_toCoeffField, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q) (p - pStar) (qStar - q)
      _ = Ch04.restrictionResponseJObservableCubeSet Q (p - pStar) (qStar - q) a := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
              (p - pStar) (qStar - q) a.toFun]
            rfl
  have hresp₂ :
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
          (pStar + p) (qStar + q) =
        Ch04.restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q)
          (adjointReg a) := by
    calc
      Ch02.responseJ (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
          (pStar + p) (qStar + q)
          = ResponseJ (openCubeSet Q) (pStar + p) (qStar + q)
              (adjointCoeffField a.toFun) := by
              have hAdj :
                  ((F.coeffOn Q).transpose).toCoeffField = adjointCoeffField a.toFun := by
                funext x
                simp [F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
                  Ch04.coeffOnOfAEEllipticOn_toCoeffField, adjointCoeffField]
              simpa [F, hAdj, Ch02.cubeDomain_coe] using
                Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
                  (Ch02.cubeDomain Q) (F.coeffOn Q).transpose
                  (pStar + p) (qStar + q)
      _ = Ch04.restrictionResponseJObservableCubeSet Q (pStar + p) (qStar + q)
            (adjointReg a) := by
            rw [← responseJ_cubeSet_eq_openCubeSet_of_triadicCube Q
              (pStar + p) (qStar + q) (adjointCoeffField a.toFun)]
            rfl
  rw [Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  simp [blockJObservableCubeSetBlockVec, F, hresp₁, hresp₂]
end

end Section56
end Ch05
end Book
end Homogenization
