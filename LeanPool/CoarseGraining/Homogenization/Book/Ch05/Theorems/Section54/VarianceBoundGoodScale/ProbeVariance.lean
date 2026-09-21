/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.ScalarL2

/-! # Probe Variance -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open MeasureTheory

noncomputable section

/-!
# Scalar probe variance inputs

This file records the internal integrability bridge for scalar quadratic
probes.  It keeps the public variance-bound theorem free of extra
measurability or integrability assumptions: `(P4)` controls the full normalized
fluctuation, and the deterministic operator-norm bound controls each scalar
quadratic probe.
-/

private theorem fullBlockNormalizedQuadraticObservable_cubeSet_regular
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet Q) a) P := by
  rcases exists_isRestrictionLocalRandomVariable_ae_eq_fullBlockNormalizedQuadraticObservable_cubeSet
      hP hStruct center q Q with ⟨Y, hY_local, hY_eq⟩
  exact (hP.aemeasurable_of_isLocalRandomVariable hY_local).congr hY_eq.symm

private theorem fullBlockNormalizedQuadraticObservable_descendants_regular
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (q : FullBlockVec d) (Q : TriadicCube d) (n : ℤ) :
    ∀ R ∈ descendantsAtScale Q n,
      AEMeasurable
        (fun a : RegCoeffField d =>
          fullBlockNormalizedQuadraticObservable hP hStruct center q (cubeSet R) a) P := by
  intro R hR
  exact
    fullBlockNormalizedQuadraticObservable_cubeSet_regular
      hP hStruct center q R

private theorem fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_regular
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center n m : ℤ) (q : FullBlockVec d) :
    AEMeasurable
      (Ch04.restrictionCenteredDescendantAverage P n m
        (fullBlockNormalizedQuadraticObservableR hP hStruct center q)) P := by
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  let μ0 : ℝ := ∫ b, X (cubeSet (originCube d n)) b ∂P
  let S : RegCoeffField d → ℝ :=
    fun a => ∑ R ∈ descendantsAtScale (originCube d m) n, (X (cubeSet R) a - μ0)
  have hdesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        AEMeasurable (fun a : RegCoeffField d => X (cubeSet R) a) P := by
    simpa [X] using!
      fullBlockNormalizedQuadraticObservable_descendants_regular
        hP hStruct center q (originCube d m) n
  have hS : AEMeasurable S P := by
    have hS' :
        AEMeasurable
          (∑ R ∈ descendantsAtScale (originCube d m) n,
            fun a : RegCoeffField d => X (cubeSet R) a - μ0) P :=
      Finset.aemeasurable_sum _ fun R hR =>
        (hdesc R hR).sub aemeasurable_const
    refine hS'.congr ?_
    filter_upwards with a
    simp [S, Finset.sum_apply]
  have hcenter :
      Ch04.restrictionCenteredDescendantAverage P n m X =
        fun a => ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ * S a := by
    funext a
    simp [Ch04.restrictionCenteredDescendantAverage, S, μ0]
  simpa [X, hcenter] using! aemeasurable_const.mul hS

/-- `(P4)` gives the L2 integrability of a centered normalized scalar
quadratic probe on an origin cube. -/
theorem integrable_abs_sub_dotProduct_sq_fullBlockNormalizedQuadraticObservable_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) (q : FullBlockVec d) :
    Integrable
      (fun a : RegCoeffField d =>
        |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
            (cubeSet (originCube d (j : ℤ))) a - dotProduct q q| ^ (2 : ℕ)) P := by
  let F : RegCoeffField d → ℝ := fun a =>
    Ch04.fullBlockNormalizedFluctuationOperatorNormSqAtScale
      hP hStruct (m : ℤ) (originCube d (j : ℤ)) a
  have hF_int : Integrable F P := by
    simpa [F] using
      integrable_origin_fullBlockNormalizedFluctuationOperatorNormSqAtScale_from_P4
        hP hStruct hP4 (m : ℤ) j
  have hR_int : Integrable
      (fun a : RegCoeffField d => F a * (dotProduct q q) ^ (2 : ℕ)) P :=
    hF_int.mul_const _
  refine Integrable.mono' hR_int ?_ ?_
  · have hX_meas :=
      fullBlockNormalizedQuadraticObservable_cubeSet_regular
        hP hStruct (m : ℤ) q (originCube d (j : ℤ))
    exact (((hX_meas.sub aemeasurable_const).norm.pow_const (2 : ℕ)).aestronglyMeasurable)
  · filter_upwards with a
    have hquad :=
      fullBlockNormalizedQuadraticObservable_sub_dotProduct_eq_fluctuationQuadratic
        hP hStruct hP4 m q (cubeSet (originCube d (j : ℤ))) a
    have hbound :=
      fullBlockQuadratic_abs_sq_le_operatorNorm_sq_mul_dotProduct_sq
        (fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
          (cubeSet (originCube d (j : ℤ))) a) q
    rw [hquad]
    let M : FullBlockMat d :=
      fullBlockNormalizedFluctuationMatrix hP hStruct (m : ℤ)
        (cubeSet (originCube d (j : ℤ))) a
    have hleft_nonneg : 0 ≤ |fullBlockQuadratic M q| ^ (2 : ℕ) :=
      pow_nonneg (abs_nonneg _) (2 : ℕ)
    show |(|fullBlockQuadratic M q| ^ (2 : ℕ))| ≤
      F a * (dotProduct q q) ^ (2 : ℕ)
    rw [abs_of_nonneg hleft_nonneg]
    calc
      |fullBlockQuadratic M q| ^ (2 : ℕ)
          ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ) *
              (dotProduct q q) ^ (2 : ℕ) := by
            simpa [M] using hbound
      _ = F a * (dotProduct q q) ^ (2 : ℕ) := by
            rw [← fullBlockNormalizedFluctuationOperatorNormSq_eq_norm_sq]
            rfl

/-- `(P4)` also gives the L1 integrability inputs for one normalized scalar
quadratic probe on an origin cube. -/
theorem integrable_fullBlockNormalizedQuadraticObservable_and_abs_sub_dotProduct_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m j : ℕ) (q : FullBlockVec d) :
    Integrable
        (fun a : RegCoeffField d =>
          fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
            (cubeSet (originCube d (j : ℤ))) a) P ∧
      Integrable
        (fun a : RegCoeffField d =>
          |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
            (cubeSet (originCube d (j : ℤ))) a - dotProduct q q|) P ∧
      Integrable
        (fun a : RegCoeffField d =>
          |fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
            (cubeSet (originCube d (j : ℤ))) a - dotProduct q q| ^ (2 : ℕ)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : RegCoeffField d → ℝ := fun a =>
    fullBlockNormalizedQuadraticObservable hP hStruct (m : ℤ) q
      (cubeSet (originCube d (j : ℤ))) a
  let Y : RegCoeffField d → ℝ := fun a => X a - dotProduct q q
  have hSq :
      Integrable (fun a : RegCoeffField d => |Y a| ^ (2 : ℕ)) P := by
    simpa [X, Y] using
      integrable_abs_sub_dotProduct_sq_fullBlockNormalizedQuadraticObservable_from_P4
        hP hStruct hP4 m j q
  have hX_regular : AEMeasurable X P := by
    simpa [X] using
      fullBlockNormalizedQuadraticObservable_cubeSet_regular
        hP hStruct (m : ℤ) q (originCube d (j : ℤ))
  have hY_strong : AEStronglyMeasurable Y P :=
    (hX_regular.sub aemeasurable_const).aestronglyMeasurable
  have hY_mem2 : MemLp Y (2 : ENNReal) P := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hY_strong]
    simpa [Y, sq_abs] using hSq
  have hY_int : Integrable Y P :=
    hY_mem2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hX_int : Integrable X P := by
    have hsum : Integrable (fun a : RegCoeffField d => Y a + dotProduct q q) P :=
      hY_int.add (integrable_const _)
    simpa [Y, X, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hY_abs_int : Integrable (fun a : RegCoeffField d => |Y a|) P := by
    simpa [Real.norm_eq_abs] using hY_int.norm
  exact ⟨by simpa [X] using hX_int, by simpa [X, Y] using hY_abs_int,
    by simpa [X, Y] using hSq⟩

/-- Convert the Section 5.4 Rosenthal root bound for a normalized quadratic
probe descendant average into the L1 and L2 estimates used by the scalar
variance reduction. -/
theorem fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (q : FullBlockVec d) {K : ℝ}
    (hOriginMoment_int :
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P n
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              hP4.xi) P)
    (hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P n m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K) :
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P n m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P n m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^ (2 : ℕ) ∂P
          ≤ K ^ (2 : ℕ)) := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  let Z : RegCoeffField d → ℝ := Ch04.restrictionCenteredDescendantAverage P n m X
  have hX0 :
      AEMeasurable (fun a : RegCoeffField d => X (cubeSet (originCube d n)) a) P := by
    simpa [X] using!
      fullBlockNormalizedQuadraticObservable_cubeSet_regular
        hP hStruct center q (originCube d n)
  have hXdesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        AEMeasurable (fun a : RegCoeffField d => X (cubeSet R) a) P := by
    simpa [X] using!
      fullBlockNormalizedQuadraticObservable_descendants_regular
        hP hStruct center q (originCube d m) n
  have hZ_regular : AEMeasurable Z P := by
    simpa [Z, X] using
      fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_regular
        hP hStruct center n m q
  have hxi_one : 1 ≤ hP4.xi :=
    Nat.le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hZξ_int : Integrable (fun a => |Z a| ^ hP4.xi) P := by
    simpa [Z, X] using
      Ch04.integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary
        (d := d) (n := n) (m := m) (P := P) (p := hP4.xi)
        hn hnm hStruct.stationary X
        (Ch04.isRestrictionTranslationCovariant_comp_toFun
      (fullBlockNormalizedQuadraticObservable_translation_covariant hP hStruct center q))
        hX0 hXdesc hxi_one
        (by simpa [X] using hOriginMoment_int)
  simpa [Z, X] using
    integral_abs_and_sq_le_of_annealedMomentRoot_le
      (μ := P) hP4.two_le_xi hZ_regular hZξ_int
      (by simpa [Z, X] using hroot)

/-- Integrability of the L1 and L2 sizes of the normalized quadratic-probe
descendant average, derived internally from the origin `L^ξ` moment supplied by
`(P4)`. -/
theorem fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_integrable
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center n m : ℤ} (hn : 0 ≤ n) (hnm : n ≤ m) (q : FullBlockVec d)
    (hOriginMoment_int :
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredOriginObservable P n
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              hP4.xi) P) :
    Integrable
        (fun a =>
          |Ch04.restrictionCenteredDescendantAverage P n m
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a|) P ∧
      Integrable
        (fun a =>
          |Ch04.restrictionCenteredDescendantAverage P n m
            (fullBlockNormalizedQuadraticObservableR hP hStruct center q) a| ^
              (2 : ℕ)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let X : Set (Vec d) → RegCoeffField d → ℝ :=
    fullBlockNormalizedQuadraticObservableR hP hStruct center q
  let Z : RegCoeffField d → ℝ := Ch04.restrictionCenteredDescendantAverage P n m X
  have hX0 :
      AEMeasurable (fun a : RegCoeffField d => X (cubeSet (originCube d n)) a) P := by
    simpa [X] using!
      fullBlockNormalizedQuadraticObservable_cubeSet_regular
        hP hStruct center q (originCube d n)
  have hXdesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n,
        AEMeasurable (fun a : RegCoeffField d => X (cubeSet R) a) P := by
    simpa [X] using!
      fullBlockNormalizedQuadraticObservable_descendants_regular
        hP hStruct center q (originCube d m) n
  have hZ_regular : AEMeasurable Z P := by
    simpa [Z, X] using
      fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_regular
        hP hStruct center n m q
  have hxi_one : 1 ≤ hP4.xi :=
    Nat.le_trans (by norm_num : 1 ≤ 2) hP4.two_le_xi
  have hZξ_int : Integrable (fun a => |Z a| ^ hP4.xi) P := by
    simpa [Z, X] using
      Ch04.integrable_abs_pow_restrictionCenteredDescendantAverage_of_stationary
        (d := d) (n := n) (m := m) (P := P) (p := hP4.xi)
        hn hnm hStruct.stationary X
        (Ch04.isRestrictionTranslationCovariant_comp_toFun
      (fullBlockNormalizedQuadraticObservable_translation_covariant hP hStruct center q))
        hX0 hXdesc hxi_one
        (by simpa [X] using hOriginMoment_int)
  have hZ_memξ : MemLp Z (hP4.xi : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hZ_regular.aestronglyMeasurable
      (by exact_mod_cast hP4.xi_pos.ne') (by simp)]
    simpa [Real.norm_eq_abs] using hZξ_int
  have hZ_mem2 : MemLp Z (2 : ENNReal) P :=
    hZ_memξ.mono_exponent (by exact_mod_cast hP4.two_le_xi)
  have hZ_int : Integrable Z P :=
    hZ_mem2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hZ_sq_int : Integrable (fun a => |Z a| ^ (2 : ℕ)) P := by
    simpa [Real.norm_eq_abs] using
      hZ_mem2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact ⟨by simpa [Z, X, Real.norm_eq_abs] using hZ_int.norm,
    by simpa [Z, X] using hZ_sq_int⟩

/-- L1/L2 descendant-average bounds for normalized coordinate probes. -/
theorem coordinateProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) (α : BlockCoord d) :
    let K :=
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) *
              (2 * coordinateProbeFactor hP hStruct center α *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
              (2 * coordinateProbeFactor hP hStruct center α *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockCoordinateProbe α)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockCoordinateProbe α)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
  classical
  dsimp only
  let K :=
    ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
          ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
            (1 / (hP4.xi : ℝ)) *
            (2 * coordinateProbeFactor hP hStruct center α *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
          Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
            (2 * coordinateProbeFactor hP hStruct center α *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
  have hOrigin :=
    coordinateProbe_centeredOrigin_momentRoot_le_factorSum hP hStruct hP4 center α
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockCoordinateProbe α)) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K := by
    simpa [K] using
      coordinateProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
        hP hStruct hP4 hm α
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
      hP hStruct hP4 (q := fullBlockCoordinateProbe α)
      (center := center) (n := 0) (m := m) (by norm_num) hm hOrigin.1 hroot

/-- L1/L2 descendant-average bounds for normalized plus-pair probes. -/
theorem plusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K :=
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) *
              (2 * pairProbeFactor hP hStruct center α β *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
              (2 * pairProbeFactor hP hStruct center α β *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockPlusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockPlusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
  classical
  dsimp only
  let K :=
    ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
          ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
            (1 / (hP4.xi : ℝ)) *
            (2 * pairProbeFactor hP hStruct center α β *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
          Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
            (2 * pairProbeFactor hP hStruct center α β *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
  have hOrigin :=
    plusProbe_centeredOrigin_momentRoot_le_factorSum hP hStruct hP4 center hαβ
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockPlusProbe α β)) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K := by
    simpa [K] using
      plusProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
        hP hStruct hP4 hm hαβ
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
      hP hStruct hP4 (q := fullBlockPlusProbe α β)
      (center := center) (n := 0) (m := m) (by norm_num) hm hOrigin.1 hroot

/-- L1/L2 descendant-average bounds for normalized minus-pair probes. -/
theorem minusProbe_restrictionCenteredDescendantAverage_abs_and_sq_le
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {center m : ℤ} (hm : 0 ≤ m) {α β : BlockCoord d} (hαβ : α ≠ β) :
    let K :=
      ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
        (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
              (1 / (hP4.xi : ℝ)) *
              (2 * pairProbeFactor hP hStruct center α β *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
          Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
              (2 * pairProbeFactor hP hStruct center α β *
                (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                  Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
    (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockMinusProbe α β)) a| ∂P ≤ K) ∧
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockMinusProbe α β)) a| ^ (2 : ℕ) ∂P ≤ K ^ (2 : ℕ)) := by
  classical
  dsimp only
  let K :=
    ((descendantsAtScale (originCube d m) 0).card : ℝ)⁻¹ *
      (Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
          ((descendantsAtScale (originCube d m) 0).card : ℝ) ^
            (1 / (hP4.xi : ℝ)) *
            (2 * pairProbeFactor hP hStruct center α β *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)) +
        Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
          Real.sqrt ((descendantsAtScale (originCube d m) 0).card : ℝ) *
            (2 * pairProbeFactor hP hStruct center α β *
              (Ch04.LambdaMomentAtScale P 0 hP4.sUpper hP4.xi +
                Ch04.lambdaInvMomentAtScale P 0 hP4.sLower hP4.xi)))
  have hOrigin :=
    minusProbe_centeredOrigin_momentRoot_le_factorSum hP hStruct hP4 center hαβ
  have hroot :
      (∫ a,
        |Ch04.restrictionCenteredDescendantAverage P 0 m
          (fullBlockNormalizedQuadraticObservableR hP hStruct center
            (fullBlockMinusProbe α β)) a| ^
          hP4.xi ∂P) ^
        (1 / (hP4.xi : ℝ)) ≤ K := by
    simpa [K] using
      minusProbe_restrictionCenteredDescendantAverage_pow_rpow_inv_le
        hP hStruct hP4 hm hαβ
  exact
    fullBlockNormalizedQuadraticObservable_restrictionCenteredDescendantAverage_abs_and_sq_le_of_root
      hP hStruct hP4 (q := fullBlockMinusProbe α β)
      (center := center) (n := 0) (m := m) (by norm_num) hm hOrigin.1 hroot

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
