/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.ProbeMoment
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.BudgetAbsorption

/-!
# Block-variance bound (`t.block.variance`)

This is the final bridge corollary supplying the variance input consumed by the
entry-scale assembly (`Homogenization.HighContrast.EntryScale`).  That consumer
integrates the concrete Chapter 4 observable
`Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct n (originCube d n)`
over the origin cube at the same centre scale `n`; the theorem below bounds
exactly that integral by `Cd·Θ⁶·(3^n)^{-(d-2)/(d-1)}` under a
`ThetaEllipticLaw Θ P` and the structural law.

## Proof route

The observable is controlled a.s. by finitely many quadratic probes of the
normalized fluctuation matrix `H = D·(A_n − Ā_n)·D`
(`fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae`).  Each
probe's second moment is the centered second moment
(`probe_sq_integral_le`), uniformly `≤ 64·Cd·Θ⁶·(3^n)^{-β}`.  Summing the
`(2d)`-dimensional finite probe net absorbs the dimensional counting into the
constant `Cd`.  RestrictionObservable integrability is *not* required: the pointwise budget
bound is combined through `integral_mono_of_nonneg` since the observable is a
square, hence nonnegative.

The finite-probe linearity is kept generic in the matrix family so that the
heavy `fullBlockNormalizedFluctuationMatrix` definition is never unfolded during
the summation algebra.
-/

namespace Homogenization

open Homogenization MeasureTheory
open Homogenization.Book.Ch04
  (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw fullBlockNormalizedFluctuationOperatorNormSqAtScale)
open Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale
  (fullBlockNormalizedFluctuationMatrix fullBlockQuadratic fullBlockProbeSqBudget
    fullBlockCoordinateProbe fullBlockPlusProbe fullBlockMinusProbe
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg
    dotProduct_coordinateProbe_self dotProduct_plusProbe_self_le_four
    dotProduct_minusProbe_self_le_four)

variable {d : ℕ}

/-- Integrability of the finite probe square budget, generic in the matrix
family. -/
theorem integrable_fullBlockProbeSqBudget {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {M : RegCoeffField d → FullBlockMat d}
    (hint : ∀ q : FullBlockVec d,
      Integrable (fun a => (fullBlockQuadratic (M a) q) ^ 2) P) :
    Integrable (fun a => fullBlockProbeSqBudget (M a)) P := by
  unfold fullBlockProbeSqBudget
  refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
  intro α _hα
  refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
  intro β _hβ
  exact (((hint _).add (hint _)).add (hint _)).const_mul 3

/-- The finite probe square budget integrates to a finite sum of per-probe
second moments, generic in the matrix family. -/
theorem integral_fullBlockProbeSqBudget_eq {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {M : RegCoeffField d → FullBlockMat d}
    (hint : ∀ q : FullBlockVec d,
      Integrable (fun a => (fullBlockQuadratic (M a) q) ^ 2) P) :
    ∫ a, fullBlockProbeSqBudget (M a) ∂P =
      (Fintype.card (BlockCoord d) : ℝ) *
        ∑ α : BlockCoord d, (Fintype.card (BlockCoord d) : ℝ) *
          ∑ β : BlockCoord d, 3 *
            (∫ a, (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P +
              ∫ a, (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P +
              ∫ a, (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P) := by
  have hterm_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          3 * ((fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
            (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
            (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ))) P :=
    fun α β => (((hint _).add (hint _)).add (hint _)).const_mul 3
  unfold fullBlockProbeSqBudget
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun α _ => (MeasureTheory.integrable_finsetSum _
    (fun β _ => hterm_int α β)).const_mul _)]
  congr 1
  ext α
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun β _ => hterm_int α β)]
  congr 1
  ext β
  rw [integral_const_mul]
  congr 1
  calc
    ∫ a, (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
          (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
        (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P
        = ∫ a, ((fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ)) ∂P +
            ∫ a, (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P :=
          integral_add ((hint (fullBlockCoordinateProbe α)).add (hint (fullBlockPlusProbe α β)))
            (hint (fullBlockMinusProbe α β))
    _ = (∫ a, (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P +
            ∫ a, (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P) +
          ∫ a, (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P := by
          rw [integral_add (hint (fullBlockCoordinateProbe α)) (hint (fullBlockPlusProbe α β))]
    _ = ∫ a, (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) ∂P +
            ∫ a, (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) ∂P +
          ∫ a, (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ) ∂P := by ring

/-- The finite probe square budget integral is bounded by a uniform per-probe
bound `K` (valid on probes of Euclidean square norm `≤ 4`), generic in `M`. -/
theorem integral_fullBlockProbeSqBudget_le {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {M : RegCoeffField d → FullBlockMat d} (K : ℝ)
    (hint : ∀ q : FullBlockVec d,
      Integrable (fun a => (fullBlockQuadratic (M a) q) ^ 2) P)
    (hbd : ∀ q : FullBlockVec d, dotProduct q q ≤ 4 →
      (∫ a, (fullBlockQuadratic (M a) q) ^ 2 ∂P) ≤ K) :
    ∫ a, fullBlockProbeSqBudget (M a) ∂P ≤
      (Fintype.card (BlockCoord d) : ℝ) *
        ∑ _α : BlockCoord d, (Fintype.card (BlockCoord d) : ℝ) *
          ∑ _β : BlockCoord d, 3 * (K + K + K) := by
  rw [integral_fullBlockProbeSqBudget_eq hint]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.sum_le_sum ?_
  intro α _hα
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.sum_le_sum ?_
  intro β _hβ
  have hc := hbd (fullBlockCoordinateProbe α)
    (by rw [dotProduct_coordinateProbe_self]; norm_num)
  have hp := hbd (fullBlockPlusProbe α β) (dotProduct_plusProbe_self_le_four α β)
  have hmm := hbd (fullBlockMinusProbe α β) (dotProduct_minusProbe_self_le_four α β)
  nlinarith [hc, hp, hmm]

/-- **Finite-probe assembly for the fluctuation observable.**  The observable is
nonnegative and a.s. dominated by the probe square budget, so
`integral_mono_of_nonneg` gives the bound without observable integrability. -/
theorem integral_observable_le_of_probeBounds [NeZero d] {P : RestrictionCoeffLaw d}
    [IsProbabilityMeasure P] (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P)
    (m : ℤ) (K : ℝ)
    (hint : ∀ q : FullBlockVec d,
      Integrable (fun a : RegCoeffField d => (fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q)
          ^ 2) P)
    (hbd : ∀ q : FullBlockVec d, dotProduct q q ≤ 4 →
      (∫ a : RegCoeffField d, (fullBlockQuadratic
        (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) q)
          ^ 2 ∂P) ≤ K) :
    (∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m (originCube d m) a ∂P)
      ≤ ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          ((Fintype.card (BlockCoord d) : ℝ) *
            ∑ _α : BlockCoord d, (Fintype.card (BlockCoord d) : ℝ) *
              ∑ _β : BlockCoord d, 3 * (K + K + K)) := by
  have hpoint :=
    fullBlockNormalizedFluctuationOperatorNormSqAtScale_le_probeSqBudget_ae
      hP hStruct m (originCube d m)
  have hnonneg :
      (0 : RegCoeffField d → ℝ) ≤ᵐ[P]
        fun a => fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m
          (originCube d m) a :=
    Filter.Eventually.of_forall fun a =>
      fullBlockNormalizedFluctuationOperatorNormSqAtScale_nonneg hP hStruct m (originCube d m) a
  have hbudget_int := integrable_fullBlockProbeSqBudget
    (M := fun a => fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a)
    hint
  calc
    (∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m
        (originCube d m) a ∂P)
        ≤ ∫ a, ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget
              (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) ∂P :=
          integral_mono_of_nonneg hnonneg (hbudget_int.const_mul _) hpoint
    _ = ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          ∫ a, fullBlockProbeSqBudget
            (fullBlockNormalizedFluctuationMatrix hP hStruct m (cubeSet (originCube d m)) a) ∂P := by
          rw [integral_const_mul]
    _ ≤ ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
          ((Fintype.card (BlockCoord d) : ℝ) *
            ∑ _α : BlockCoord d, (Fintype.card (BlockCoord d) : ℝ) *
              ∑ _β : BlockCoord d, 3 * (K + K + K)) :=
        mul_le_mul_of_nonneg_left (integral_fullBlockProbeSqBudget_le K hint hbd) (sq_nonneg _)

/-- **Block-variance bound (`t.block.variance`).**  The normalized full-block
fluctuation observable at centre scale `m`, integrated over the origin cube at
the same scale, is bounded by `Cd·Θ⁶·(3^m)^{-(d-2)/(d-1)}` under a
`ThetaEllipticLaw Θ P` and the structural law.  The constant `Cd` depends only on
the dimension `d`.

This is the variance input consumed by the entry-scale assembly
(`Homogenization.HighContrast.EntryScale`), which integrates the same observable
at the same origin-cube scale.  See the high-moment paper (Armstrong–Kuusi–Loher,
to appear). -/
theorem integral_fullBlockNormalizedFluctuation_le [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
      (hP : RestrictionLawCarrier P) (hStruct : RestrictionStructuralLaw P) (_hLaw : ThetaEllipticLaw Θ P)
      {m : ℤ} (_hm : 0 ≤ m),
      ∫ a, fullBlockNormalizedFluctuationOperatorNormSqAtScale hP hStruct m (originCube d m) a ∂P
        ≤ Cd * Θ ^ 6 * ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) := by
  obtain ⟨Cd, hCd0, hprobe⟩ := probe_sq_integral_le hd
  refine ⟨576 * (Fintype.card (BlockCoord d) : ℝ) ^ 6 * Cd,
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hCd0, ?_⟩
  intro Θ hΘ P _ hP hStruct hLaw m hm
  set t : ℝ := ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1)) with htdef
  have hbound := integral_observable_le_of_probeBounds hP hStruct m (64 * Cd * Θ ^ 6 * t)
    (fun q => integrable_fluctuation_probe_sq hΘ hP hStruct hLaw m q)
    (fun q hq => hprobe hm hΘ hP hStruct hLaw q hq)
  refine le_trans hbound (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Homogenization
