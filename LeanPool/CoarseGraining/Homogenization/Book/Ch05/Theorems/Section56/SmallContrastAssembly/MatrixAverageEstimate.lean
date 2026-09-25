/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAssembly.MatrixAveragePackaging
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.PartitionAverage
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ProbeVariance

/-! # Matrix Average Estimate -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAssembly

open Section54.VarianceBoundGoodScale

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

private def fullBlockQuadraticLinearMap
    {d : ℕ} (q : FullBlockVec d) : FullBlockMat d →ₗ[ℝ] ℝ where
  toFun M := fullBlockQuadratic M q
  map_add' M N := fullBlockQuadratic_add M N q
  map_smul' c M := fullBlockQuadratic_smul c M q

theorem fullBlockQuadratic_descendantsAverageFullBlockMat
    {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → FullBlockMat d) (q : FullBlockVec d) :
    fullBlockQuadratic (descendantsAverageFullBlockMat Q j F) q =
      descendantsAverage Q j (fun R => fullBlockQuadratic (F R) q) := by
  classical
  let L := fullBlockQuadraticLinearMap q
  calc
    fullBlockQuadratic (descendantsAverageFullBlockMat Q j F) q
        = L (descendantsAverageFullBlockMat Q j F) := rfl
    _ =
      L (((descendantsAtDepth Q j).card : ℝ)⁻¹ •
          (descendantsAtDepth Q j).sum F) := by
          rw [descendantsAverageFullBlockMat_eq_smul_sum]
    _ =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, fullBlockQuadratic (F R) q := by
          simp [L, fullBlockQuadraticLinearMap]
    _ = descendantsAverage Q j (fun R => fullBlockQuadratic (F R) q) := by
          rfl

theorem integral_origin_fullBlockNormalizedQuadraticObservable_self_eq_dotProduct
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m : ℕ) (q : FullBlockVec d) :
    (∫ a,
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
        (cubeSet (originCube d (m : ℤ))) a.toFun ∂P) =
      dotProduct q q := by
  let b := hP.barSigmaAtScale hStruct (m : ℤ)
  let c := hP.barSigmaStarAtScale hStruct (m : ℤ)
  let D : FullBlockMat d := Matrix.diagonal (Ch04.scalarFullBlockInvSqrtDiag b c)
  have hInt :=
    integral_origin_fullBlockNormalizedQuadraticObservable_eq_annealedBlockMatrixAtScale_from_P4
      hP hStruct hP4 (m : ℤ) (m : ℤ)
      (by exact_mod_cast Nat.zero_le m) q
  have hAnnealed :
      D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (m : ℤ)) * D = 1 := by
    simpa [D, b, c] using
      normalizedAnnealedBlockMatrix_self_eq_one hP hStruct hP4 m
  calc
    (∫ a,
      fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
        (cubeSet (originCube d (m : ℤ))) a.toFun ∂P)
        = fullBlockQuadratic
            (D * toFullBlockMat (Ch04.annealedBlockMatrixAtScale P (m : ℤ)) * D) q := by
          simpa [D, b, c] using hInt
    _ = fullBlockQuadratic (1 : FullBlockMat d) q := by rw [hAnnealed]
    _ = dotProduct q q := fullBlockQuadratic_one q

theorem fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_eq_restrictionCenteredDescendantAverage
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {child parent : ℕ} (hchild_parent : child ≤ parent)
    (q : FullBlockVec d) (a : RegCoeffField d) :
    fullBlockQuadratic
        (descendantsAverageNormalizedFluctuationMatrix
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a) q =
      Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ)
        (fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q) a := by
  classical
  let Q : TriadicCube d := originCube d (parent : ℤ)
  let depth : ℕ := parent - child
  have hscale_le : (child : ℤ) ≤ (parent : ℤ) := by exact_mod_cast hchild_parent
  have hdepth_scale :
      descendantsAtDepth Q depth = descendantsAtScale Q (child : ℤ) := by
    simpa [Q, depth, originCube] using
      (descendantsAtScale_eq_descendantsAtDepth
        (originCube d (parent : ℤ)) hscale_le).symm
  have hmean :
      (∫ b,
        fullBlockNormalizedQuadraticObservable hP hStruct (child : ℤ) q
          (cubeSet (originCube d (child : ℤ))) b.toFun ∂P) =
        dotProduct q q :=
    integral_origin_fullBlockNormalizedQuadraticObservable_self_eq_dotProduct
      hP hStruct hP4 child q
  calc
    fullBlockQuadratic
        (descendantsAverageNormalizedFluctuationMatrix
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a) q
        =
      descendantsAverage Q depth
        (fun R =>
          fullBlockQuadratic
            (fullBlockNormalizedFluctuationMatrix hP hStruct (child : ℤ)
              (cubeSet R) a) q) := by
          simpa [Q, depth, descendantsAverageNormalizedFluctuationMatrix] using
            fullBlockQuadratic_descendantsAverageFullBlockMat
              (Q := Q) (j := depth)
              (F := fun R =>
                fullBlockNormalizedFluctuationMatrix hP hStruct (child : ℤ)
                  (cubeSet R) a) q
    _ =
      Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ)
        (fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q) a := by
          unfold descendantsAverage Ch04.restrictionCenteredDescendantAverage
          rw [hdepth_scale]
          apply congrArg
            (fun s : ℝ =>
              ((descendantsAtScale Q (child : ℤ)).card : ℝ)⁻¹ * s)
          refine Finset.sum_congr rfl ?_
          intro R hR
          have hquad :=
            fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
              hP hStruct hP4 child q (cubeSet R) a
          simp only [fullBlockNormalizedQuadraticObservableR]
          rw [← hquad, hmean]

theorem aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a) P := by
  rcases
      exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
        hP hStruct center q Q with
    ⟨Y, hY_local, hY_eq⟩
  exact (hP.aemeasurable_of_isLocalRandomVariable hY_local).congr hY_eq.symm

theorem aemeasurable_fullBlockNormalizedQuadraticObservable_descendants_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      AEMeasurable
        (fun a : RegCoeffField d =>
          fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet R) a) P := by
  intro R _hR
  exact aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet_of_P4
    hP hStruct center q R

noncomputable def normalizedQuadraticProbeAverageRootBound
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (child parent : ℕ) (q : FullBlockVec d) : ℝ :=
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q
  let K : ℝ :=
    (∫ a, |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ) ∂P) ^
      (1 / (2 : ℝ))
  let N : ℝ := ((descendantsAtScale (originCube d (parent : ℤ)) (child : ℤ)).card : ℝ)
  N⁻¹ *
    (Ch04.rosenthalDescendantsAtScaleLpConst d (child : ℤ) 2 *
        N ^ (1 / (2 : ℝ)) * K +
      Ch04.rosenthalDescendantsAtScaleSqrtConst d (child : ℤ) 2 *
        Real.sqrt N * K)

theorem fullBlockNormalizedQuadraticObservable_centeredOrigin_sq_integrable_at_self
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (child : ℕ) (q : FullBlockVec d) :
    Integrable
      (fun a : RegCoeffField d =>
        |Ch04.restrictionCenteredOriginObservable P (child : ℤ)
          (fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q) a| ^
          (2 : ℕ)) P := by
  have hsub :=
    integrable_abs_sub_dotProduct_sq_fullBlockNormalizedQuadraticObservable_from_P4
      hP hStruct hP4 child child q
  refine hsub.congr ?_
  filter_upwards with a
  rw [Ch04.restrictionCenteredOriginObservable]
  simp only [fullBlockNormalizedQuadraticObservableR]
  rw [
    integral_origin_fullBlockNormalizedQuadraticObservable_self_eq_dotProduct
      hP hStruct hP4 child q]

theorem fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_sq_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {child parent : ℕ} (hchild_parent : child ≤ parent)
    (q : FullBlockVec d) :
    Integrable
      (fun a : RegCoeffField d =>
        (fullBlockQuadratic
          (descendantsAverageNormalizedFluctuationMatrix
            hP hStruct (child : ℤ) (originCube d (parent : ℤ))
              (parent - child) a) q) ^ (2 : ℕ)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q
  have hZ_int :
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ)) P := by
    refine
      Ch04.integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary
        (d := d) (n := (child : ℤ)) (m := (parent : ℤ)) (P := P)
        (p := 2) (by exact_mod_cast Nat.zero_le child)
        (by exact_mod_cast hchild_parent) hStruct.stationary X
        ?_ ?_ ?_ (by norm_num) ?_
    · exact Ch04.isRestrictionTranslationCovariant_comp_toFun
        (fullBlockNormalizedQuadraticObservable_translation_covariant
          hP hStruct (child : ℤ) q)
    · simpa [X] using!
        aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet_of_P4
          hP hStruct (child : ℤ) q (originCube d (child : ℤ))
    · simpa [X] using!
        aemeasurable_fullBlockNormalizedQuadraticObservable_descendants_of_P4
          hP hStruct (child : ℤ) q (originCube d (parent : ℤ)) (child : ℤ)
    · simpa [X] using
        fullBlockNormalizedQuadraticObservable_centeredOrigin_sq_integrable_at_self
          hP hStruct hP4 child q
  refine hZ_int.congr ?_
  filter_upwards with a
  have hEq :=
    fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_eq_restrictionCenteredDescendantAverage
      hP hStruct hP4 hchild_parent q a
  rw [hEq]
  exact
    sq_abs (Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a)

theorem fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_integral_sq_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {child parent : ℕ} (hchild_parent : child ≤ parent)
    (q : FullBlockVec d) :
    ∫ a,
        (fullBlockQuadratic
          (descendantsAverageNormalizedFluctuationMatrix
            hP hStruct (child : ℤ) (originCube d (parent : ℤ))
              (parent - child) a) q) ^ (2 : ℕ) ∂P ≤
      (normalizedQuadraticProbeAverageRootBound hP hStruct child parent q) ^ (2 : ℕ) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct (child : ℤ) q
  let K : ℝ :=
    (∫ a, |Ch04.restrictionCenteredOriginObservable P (child : ℤ) X a| ^ (2 : ℕ) ∂P) ^
      (1 / (2 : ℝ))
  let B : ℝ := normalizedQuadraticProbeAverageRootBound hP hStruct child parent q
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
          (2 : ℕ) ∂P) ^
        (1 / (2 : ℝ)) ≤ B := by
    have hraw :=
      integral_abs_restrictionCenteredDescendantAverage_pow_rpow_inv_le_of_restrictionUnitRangeDependentLaw_of_ae_eq_local
        (d := d) (n := (child : ℤ)) (m := (parent : ℤ)) (P := P)
        (p := 2) (K := K) hP
        (by exact_mod_cast Nat.zero_le child)
        (by exact_mod_cast hchild_parent) hStruct.stationary hStruct.unit_range X
        (by
          simpa [X] using!
            fullBlockNormalizedQuadraticObservable_descendants_localRep
              hP hStruct (child : ℤ) q (originCube d (parent : ℤ)) (child : ℤ))
        (Ch04.isRestrictionTranslationCovariant_comp_toFun
          (fullBlockNormalizedQuadraticObservable_translation_covariant
            hP hStruct (child : ℤ) q))
        (by
          simpa [X] using!
            aemeasurable_fullBlockNormalizedQuadraticObservable_cubeSet_of_P4
              hP hStruct (child : ℤ) q (originCube d (child : ℤ)))
        (by
          simpa [X] using!
            aemeasurable_fullBlockNormalizedQuadraticObservable_descendants_of_P4
              hP hStruct (child : ℤ) q (originCube d (parent : ℤ)) (child : ℤ))
        (by norm_num) hK_nonneg
        (by
          simpa [X] using
            fullBlockNormalizedQuadraticObservable_centeredOrigin_sq_integrable_at_self
              hP hStruct hP4 child q)
        (by rfl)
    simpa [B, normalizedQuadraticProbeAverageRootBound, X, K] using hraw
  have hI_nonneg :
      0 ≤
        ∫ a,
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ) ∂P :=
    integral_nonneg fun a => pow_nonneg (abs_nonneg _) (2 : ℕ)
  have hroot_nonneg :
      0 ≤
        (∫ a,
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ) ∂P) ^
          (1 / (2 : ℝ)) := by
    positivity
  have hsq := pow_le_pow_left₀ hroot_nonneg hroot 2
  have hroot_sq :
      ((∫ a,
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ) ∂P) ^
          (1 / (2 : ℝ))) ^ (2 : ℕ) =
        ∫ a,
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ) ∂P := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hI_nonneg]
  have hcenter_eq :
      ∫ a,
          (fullBlockQuadratic
            (descendantsAverageNormalizedFluctuationMatrix
              hP hStruct (child : ℤ) (originCube d (parent : ℤ))
                (parent - child) a) q) ^ (2 : ℕ) ∂P =
        ∫ a,
          |Ch04.restrictionCenteredDescendantAverage P (child : ℤ) (parent : ℤ) X a| ^
            (2 : ℕ) ∂P := by
    apply integral_congr_ae
    filter_upwards with a
    have hEq :=
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_eq_restrictionCenteredDescendantAverage
        hP hStruct hP4 hchild_parent q a
    rw [hEq]
    exact (sq_abs _).symm
  rw [hroot_sq] at hsq
  simpa [hcenter_eq, B] using hsq

theorem descendantsAverageNormalizedFluctuationMatrix_isSymm_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) :
    ∀ᵐ a ∂P,
      (descendantsAverageNormalizedFluctuationMatrix hP hStruct center Q j a).IsSymm := by
  have hchild :
      ∀ R ∈ descendantsAtDepth Q j,
        ∀ᵐ a ∂P,
          (fullBlockNormalizedFluctuationMatrix
            hP hStruct center (cubeSet R) a.toFun).IsSymm := by
    intro R _hR
    exact fullBlockNormalizedFluctuationMatrix_isSymm_ae hP hStruct center R
  have hall :
      ∀ᵐ a ∂P, ∀ R, R ∈ descendantsAtDepth Q j →
        (fullBlockNormalizedFluctuationMatrix
          hP hStruct center (cubeSet R) a.toFun).IsSymm :=
    Ch04.ae_forall_mem_finset (P := P) (descendantsAtDepth Q j) hchild
  filter_upwards [hall] with a ha
  simpa [descendantsAverageNormalizedFluctuationMatrix] using
    descendantsAverageFullBlockMat_isSymm (Q := Q) (j := j)
      (F := fun R =>
        fullBlockNormalizedFluctuationMatrix hP hStruct center (cubeSet R) a) ha

theorem descendantsAverageNormalizedFluctuationOperatorNormSq_le_probeSqBudget_ae
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (Q : TriadicCube d) (j : ℕ) :
    (fun a : RegCoeffField d =>
      descendantsAverageNormalizedFluctuationOperatorNormSq
        hP hStruct center Q j a)
      ≤ᵐ[P]
    fun a : RegCoeffField d =>
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        fullBlockProbeSqBudget
          (descendantsAverageNormalizedFluctuationMatrix
            hP hStruct center Q j a) := by
  filter_upwards
    [descendantsAverageNormalizedFluctuationMatrix_isSymm_ae
      hP hStruct center Q j] with a hM
  simpa [descendantsAverageNormalizedFluctuationOperatorNormSq] using
    fullBlock_operatorNorm_sq_le_probeSqBudget hM

noncomputable def normalizedMatrixAverageProbeRootBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (child parent : ℕ) : ℝ :=
  ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
    ((Fintype.card (BlockCoord d) : ℝ) *
      ∑ α : BlockCoord d,
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ β : BlockCoord d,
            3 *
              ((normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                (normalizedQuadraticProbeAverageRootBound hP hStruct child parent
                    (fullBlockMinusProbe α β)) ^ (2 : ℕ)))

theorem descendantsAverageNormalizedFluctuationOperatorNormSq_integral_le_probeRootBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {child parent : ℕ} (hchild_parent : child ≤ parent) :
    ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a ∂P ≤
      normalizedMatrixAverageProbeRootBudget hP hStruct child parent := by
  classical
  let Q : TriadicCube d := originCube d (parent : ℤ)
  let j : ℕ := parent - child
  let M : RegCoeffField d → FullBlockMat d :=
    fun a =>
      descendantsAverageNormalizedFluctuationMatrix hP hStruct (child : ℤ) Q j a
  let Root : FullBlockVec d → ℝ :=
    normalizedQuadraticProbeAverageRootBound hP hStruct child parent
  have hF_int :
      Integrable
        (descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) Q j) P := by
    simpa [Q, j] using
      integrable_descendantsAverageNormalizedFluctuationOperatorNormSq_from_P4_of_stationary
        hP hStruct hP4 child parent child hchild_parent
  have hcoord_int :
      ∀ α : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^
              (2 : ℕ)) P := by
    intro α
    simpa [M, Q, j] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_sq_integrable
        hP hStruct hP4 hchild_parent (fullBlockCoordinateProbe α)
  have hplus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^
              (2 : ℕ)) P := by
    intro α β
    simpa [M, Q, j] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_sq_integrable
        hP hStruct hP4 hchild_parent (fullBlockPlusProbe α β)
  have hminus_int :
      ∀ α β : BlockCoord d,
        Integrable
          (fun a : RegCoeffField d =>
            (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^
              (2 : ℕ)) P := by
    intro α β
    simpa [M, Q, j] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_sq_integrable
        hP hStruct hP4 hchild_parent (fullBlockMinusProbe α β)
  have hcoord :
      ∀ α : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^
            (2 : ℕ) ∂P) ≤
          (Root (fullBlockCoordinateProbe α)) ^ (2 : ℕ) := by
    intro α
    simpa [M, Q, j, Root] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_integral_sq_le
        hP hStruct hP4 hchild_parent (fullBlockCoordinateProbe α)
  have hplus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^
            (2 : ℕ) ∂P) ≤
          (Root (fullBlockPlusProbe α β)) ^ (2 : ℕ) := by
    intro α β
    simpa [M, Q, j, Root] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_integral_sq_le
        hP hStruct hP4 hchild_parent (fullBlockPlusProbe α β)
  have hminus :
      ∀ α β : BlockCoord d,
        (∫ a,
          (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^
            (2 : ℕ) ∂P) ≤
          (Root (fullBlockMinusProbe α β)) ^ (2 : ℕ) := by
    intro α β
    simpa [M, Q, j, Root] using
      fullBlockQuadratic_descendantsAverageNormalizedFluctuationMatrix_integral_sq_le
        hP hStruct hP4 hchild_parent (fullBlockMinusProbe α β)
  have hterm_int : ∀ α β : BlockCoord d,
      Integrable
        (fun a : RegCoeffField d =>
          3 *
            ((fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
              (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ))) P := by
    intro α β
    exact ((hcoord_int α).add (hplus_int α β) |>.add (hminus_int α β)).const_mul 3
  have hbudget_int :
        Integrable
          (fun a : RegCoeffField d => fullBlockProbeSqBudget (M a)) P := by
    unfold fullBlockProbeSqBudget
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro α _hα
    refine (MeasureTheory.integrable_finsetSum _ ?_).const_mul _
    intro β _hβ
    simpa [M] using hterm_int α β
  have hpoint :
      (fun a : RegCoeffField d =>
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) Q j a)
      ≤ᵐ[P]
        fun a : RegCoeffField d =>
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) := by
    simpa [M, Q, j] using
      descendantsAverageNormalizedFluctuationOperatorNormSq_le_probeSqBudget_ae
        hP hStruct (child : ℤ) Q j
  have hfirst :
      ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) Q j a ∂P ≤
        ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) ∂P :=
    integral_mono_ae hF_int (hbudget_int.const_mul _) hpoint
  have hbudget_eval :
      ∫ a, fullBlockProbeSqBudget (M a) ∂P =
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 *
                  (∫ a,
                      (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^
                        (2 : ℕ) ∂P +
                    ∫ a,
                      (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^
                        (2 : ℕ) ∂P) := by
    unfold fullBlockProbeSqBudget
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum]
    · congr
      ext α
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      · congr
        ext β
        let f : RegCoeffField d → ℝ :=
          fun a => (fullBlockQuadratic (M a) (fullBlockCoordinateProbe α)) ^ (2 : ℕ)
        let g : RegCoeffField d → ℝ :=
          fun a => (fullBlockQuadratic (M a) (fullBlockPlusProbe α β)) ^ (2 : ℕ)
        let h : RegCoeffField d → ℝ :=
          fun a => (fullBlockQuadratic (M a) (fullBlockMinusProbe α β)) ^ (2 : ℕ)
        have hf_int : Integrable f P := by simpa [f] using hcoord_int α
        have hg_int : Integrable g P := by simpa [g] using hplus_int α β
        have hh_int : Integrable h P := by simpa [h] using hminus_int α β
        change
          ∫ a, 3 * (f a + g a + h a) ∂P =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        rw [integral_const_mul]
        change
          3 * ∫ a, (fun a => f a + g a) a + h a ∂P =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        have hfg_fun : (fun a : RegCoeffField d => f a + g a) = f + g := by
          ext a
          rfl
        rw [hfg_fun]
        rw [integral_add (hf_int.add hg_int) hh_int]
        change
          3 * (∫ a, f a + g a ∂P + ∫ a, h a ∂P) =
            3 * (∫ a, f a ∂P + ∫ a, g a ∂P + ∫ a, h a ∂P)
        rw [integral_add hf_int hg_int]
      · intro β _hβ
        exact hterm_int α β
    · intro α _hα
      exact (MeasureTheory.integrable_finsetSum _ fun β _hβ =>
        hterm_int α β).const_mul _
  have hbudget_bound :
      ∫ a, fullBlockProbeSqBudget (M a) ∂P ≤
        (Fintype.card (BlockCoord d) : ℝ) *
          ∑ α : BlockCoord d,
            (Fintype.card (BlockCoord d) : ℝ) *
              ∑ β : BlockCoord d,
                3 *
                  ((Root (fullBlockCoordinateProbe α)) ^ (2 : ℕ) +
                    (Root (fullBlockPlusProbe α β)) ^ (2 : ℕ) +
                    (Root (fullBlockMinusProbe α β)) ^ (2 : ℕ)) := by
    rw [hbudget_eval]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum ?_
    intro α _hα
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum ?_
    intro β _hβ
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [hcoord α, hplus α β, hminus α β])
      (by norm_num)
  calc
    ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) (originCube d (parent : ℤ))
            (parent - child) a ∂P
        =
      ∫ a,
        descendantsAverageNormalizedFluctuationOperatorNormSq
          hP hStruct (child : ℤ) Q j a ∂P := by
          rfl
    _ ≤
      ∫ a,
          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
            fullBlockProbeSqBudget (M a) ∂P := hfirst
    _ =
      ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)) *
        ∫ a, fullBlockProbeSqBudget (M a) ∂P := by
          rw [integral_const_mul]
    _ ≤
      normalizedMatrixAverageProbeRootBudget hP hStruct child parent := by
          simpa [normalizedMatrixAverageProbeRootBudget, Root] using
            mul_le_mul_of_nonneg_left hbudget_bound (sq_nonneg _)

end SmallContrastAssembly

end

end Section56
end Ch05
end Book
end Homogenization
