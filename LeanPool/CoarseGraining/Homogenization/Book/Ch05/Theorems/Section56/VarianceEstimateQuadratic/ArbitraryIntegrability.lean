/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.Triangle

/-! # Arbitrary Integrability -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

/-- Translation covariance of the arbitrary-normalizer full-block fluctuation
observable. -/
theorem fullBlockFluctuationOperatorNormSqWithNormalizer_translation_covariant
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) :
    Ch04.IsRestrictionTranslationCovariant
      (fun U : Set (Vec d) => fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S U a) := by
  have hraw : IsTranslationCovariant
      (fun U : Set (Vec d) => fun b : CoeffField d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
            (Matrix.transpose S *
              (toFullBlockMat (coarseBlockMatrix U b) -
                toFullBlockMat
                  (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)) *
              S)‖ ^ (2 : ℕ)) := by
    intro U z b
    simp [translateByInt, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  exact Ch04.isRestrictionTranslationCovariant_comp_toFun hraw

theorem section56_norm_toEuclideanCLM_le_sum_abs_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M‖ ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, |M i j| := by
  classical
  let S : ℝ := ∑ i : ι, ∑ j : ι, |M i j|
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) ?_
  intro x
  have hcoord :
      ∀ i : ι,
        ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ≤
          S * ‖x‖ := by
    intro i
    calc
      ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖
          = |∑ j : ι, M i j * x.ofLp j| := by
              simp [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
      _ ≤ ∑ j : ι, |M i j * x.ofLp j| :=
            Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun j => M i j * x.ofLp j)
      _ = ∑ j : ι, |M i j| * ‖x.ofLp j‖ := by
            simp [abs_mul, Real.norm_eq_abs]
      _ ≤ ∑ j : ι, |M i j| * ‖x‖ := by
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg _)
      _ = (∑ j : ι, |M i j|) * ‖x‖ := by
            rw [Finset.sum_mul]
      _ ≤ S * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right
              (Finset.single_le_sum
                (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
                (Finset.mem_univ i))
              (norm_nonneg x)
  have hnorm_sq :
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2 ≤
        (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
    calc
      ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x‖ ^ 2
          = ∑ i : ι,
              ‖((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M) x).ofLp i‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
      _ ≤ ∑ i : ι, (S * ‖x‖) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ ≤ (∑ _i : ι, S * ‖x‖) ^ 2 := by
            exact Finset.sum_sq_le_sq_sum_of_nonneg
              (fun _ _ => mul_nonneg hS_nonneg (norm_nonneg x))
      _ = (((Fintype.card ι : ℝ) * S) * ‖x‖) ^ 2 := by
            simp [Finset.sum_const]
            ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hS_nonneg) (norm_nonneg x))).mp hnorm_sq

theorem section56_norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two
    {d : ℕ} {P : Ch04.RestrictionCoeffLaw d} {Z : RegCoeffField d → FullBlockMat d}
    (hZ_aemeas : AEMeasurable Z P)
    (hZ_entry : ∀ α β : BlockCoord d, MemLp (fun a => Z a α β) (2 : ENNReal) P) :
    Integrable
      (fun a : RegCoeffField d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) (Z a)‖ ^ 2) P := by
  classical
  let S : RegCoeffField d → ℝ := fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d, |Z a α β|
  have hS_mem : MemLp S (2 : ENNReal) P := by
    dsimp [S]
    refine memLp_finsetSum _ ?_
    intro α _hα
    refine memLp_finsetSum _ ?_
    intro β _hβ
    simpa [Real.norm_eq_abs] using (hZ_entry α β).norm
  have hS_sq_int : Integrable (fun a => S a ^ 2) P := by
    simpa [Real.norm_eq_abs, S] using
      hS_mem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let C : ℝ := Fintype.card (BlockCoord d)
  let L :
      FullBlockMat d →ₗ[ℝ]
        (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) := {
    toFun := fun M => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
    map_add' := by
      intro A B
      exact map_add (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) A B
    map_smul' := by
      intro r A
      exact map_smul (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) r A
  }
  have hCS_sq_int : Integrable (fun a => (C * S a) ^ 2) P := by
    convert hS_sq_int.const_mul (C * C) using 1
    ext a
    ring
  refine Integrable.mono' hCS_sq_int ?_ ?_
  · exact ((continuous_norm.measurable.comp_aemeasurable
        (L.continuous_of_finiteDimensional.measurable.comp_aemeasurable hZ_aemeas)).pow_const
          2).aestronglyMeasurable
  · filter_upwards with a
    have hnorm :=
      section56_norm_toEuclideanCLM_le_sum_abs_entries (Z a)
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    simpa [S, C, Real.norm_eq_abs] using hpow

theorem integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (S : FullBlockMat d) (n : ℕ) :
    Integrable
      (fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
          (cubeSet (originCube d (n : ℤ))) a) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let Q : TriadicCube d := originCube d (n : ℤ)
  let Abar : BlockMat d := Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center
  let Z : RegCoeffField d → FullBlockMat d :=
    fun a =>
      Matrix.transpose S *
        (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) - toFullBlockMat Abar) * S
  have hZ_entry : ∀ α β : BlockCoord d, MemLp (fun a => Z a α β) (2 : ENNReal) P := by
    intro α β
    dsimp [Z]
    have hsum :
        MemLp
          (fun a : RegCoeffField d =>
            ∑ γ : BlockCoord d,
              (∑ δ : BlockCoord d,
                Matrix.transpose S α δ *
                  (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                    toFullBlockMat Abar δ γ)) *
                S γ β)
          (2 : ENNReal) P := by
      refine memLp_finsetSum (s := (Finset.univ : Finset (BlockCoord d)))
        (p := (2 : ENNReal)) ?_
      intro γ _hγ
      have hinner :
          MemLp
            (fun a : RegCoeffField d =>
              ∑ δ : BlockCoord d,
                Matrix.transpose S α δ *
                  (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                    toFullBlockMat Abar δ γ))
            (2 : ENNReal) P := by
        refine memLp_finsetSum (s := (Finset.univ : Finset (BlockCoord d)))
          (p := (2 : ENNReal)) ?_
        intro δ _hδ
        have hbase :
            MemLp
              (fun a : RegCoeffField d =>
                toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ -
                  toFullBlockMat Abar δ γ)
              (2 : ENNReal) P := by
          have hentry :
              MemLp
                (fun a : RegCoeffField d =>
                  toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) δ γ)
                (2 : ENNReal) P := by
            simpa [Q, toFullBlockMat, blockMatEntry] using
              Homogenization.Book.Ch05.Section52.memLp_two_blockMatEntry_coarseBlockMatrix_cubeSet_from_P4
                hP hStruct hP4 n δ γ
          simpa using! hentry.sub
            (memLp_const
              (c := toFullBlockMat Abar δ γ) (μ := P) (p := (2 : ENNReal)))
        exact hbase.const_mul (Matrix.transpose S α δ)
      simpa [mul_comm] using hinner.const_mul (S γ β)
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun a => by
      simp [Matrix.mul_apply]) hsum
  have hZ_aemeas : AEMeasurable Z P := by
    refine aemeasurable_pi_lambda Z ?_
    intro α
    refine aemeasurable_pi_lambda (fun a => Z a α) ?_
    intro β
    exact (hZ_entry α β).aestronglyMeasurable.aemeasurable
  change
    Integrable
      (fun a : RegCoeffField d =>
        ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)
          (Matrix.transpose S *
            (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun) - toFullBlockMat Abar) *
              S)‖ ^ 2) P
  exact section56_norm_toEuclideanCLM_sq_integrable_of_entry_memLp_two hZ_aemeas hZ_entry

theorem integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_originCube_from_P4_of_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (S : FullBlockMat d) (n : ℤ) (hn : 0 ≤ n) :
    Integrable
      (fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
          (cubeSet (originCube d n)) a) P := by
  have hnat :=
    integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_originCube_from_P4
      hP hStruct hP4 center S (Int.toNat n)
  simpa [Int.toNat_of_nonneg hn] using hnat

theorem integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_from_P4_of_nonneg_scale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (center : ℤ) (S : FullBlockMat d) (R : TriadicCube d)
    (hR_nonneg : 0 ≤ R.scale) :
    Integrable
      (fun a : RegCoeffField d =>
          fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
          (cubeSet R) a) P := by
  let z : Fin d → ℤ := Ch04.scaleTranslationShift R.scale R
  have hset :
      cubeSet R =
        translateSet (intVecToRealVec z) (cubeSet (originCube d R.scale)) := by
    simpa [z] using
      Ch04.cubeSet_eq_translateSet_originCube_of_nonneg_scale (R := R) hR_nonneg
  have hOrigin :
      Integrable
        (fun a : RegCoeffField d =>
          fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
            (cubeSet (originCube d R.scale)) a) P :=
    integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_originCube_from_P4_of_nonneg
      hP hStruct hP4 center S R.scale hR_nonneg
  have hcomp :
      Integrable
        (fun a : RegCoeffField d =>
          fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
            (cubeSet (originCube d R.scale)) (translateReg (intVecToRealVec z) a)) P := by
    have hOrigin_map :
        Integrable
          (fun a : RegCoeffField d =>
            fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
              (cubeSet (originCube d R.scale)) a)
          (Measure.map (translateReg (intVecToRealVec z)) P) := by
      simpa [hStruct.stationary z] using hOrigin
    simpa [Function.comp_def] using
      hOrigin_map.comp_measurable (measurable_translateReg (intVecToRealVec z))
  have hae :
      (fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
          (cubeSet R) a) =ᵐ[P]
      fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqWithNormalizer hP hStruct center S
          (cubeSet (originCube d R.scale)) (translateReg (intVecToRealVec z) a) := by
    filter_upwards with a
    rw [hset]
    exact
      fullBlockFluctuationOperatorNormSqWithNormalizer_translation_covariant
        hP hStruct center S (cubeSet (originCube d R.scale)) z a
  exact hcomp.congr hae.symm

theorem integrable_descendantsAverage_fullBlockFluctuationOperatorNormSqWithNormalizer_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (_hk : k ≤ n) (S : FullBlockMat d) :
    Integrable
      (fun a : RegCoeffField d =>
        descendantsAverage (originCube d (n : ℤ)) (n - k)
          (fun R =>
            fullBlockFluctuationOperatorNormSqWithNormalizer
              hP hStruct (m : ℤ) S (cubeSet R) a)) P := by
  classical
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  refine Ch04.integrable_descendantsAverage ?_
  intro R hR
  have hR_nonneg : 0 ≤ R.scale := by
    have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hQscale : Q.scale = (n : ℤ) := by simp [Q, originCube]
    rw [hscale, hQscale]
    have hj_le : j ≤ n := by
      dsimp [j]
      exact Nat.sub_le n k
    exact sub_nonneg.mpr (by exact_mod_cast hj_le)
  simpa [Q, j] using
    integrable_fullBlockFluctuationOperatorNormSqWithNormalizer_from_P4_of_nonneg_scale
      hP hStruct hP4 (m : ℤ) S R hR_nonneg

theorem aemeasurable_fullBlockFluctuationMatrixWithNormalizer_cubeSet
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        fullBlockFluctuationMatrixWithNormalizer hP hStruct center S
          (cubeSet Q) a) P := by
  let Abar : FullBlockMat d :=
    toFullBlockMat (Ch04.scalarAnnealedBlockMatrixAtScale hP hStruct center)
  let g : FullBlockMat d → FullBlockMat d := fun M => Matrix.transpose S * (M - Abar) * S
  have hg : Measurable g := by
    have hcont : Continuous g := by
      dsimp [g]
      fun_prop
    exact hcont.measurable
  have hM :
      AEMeasurable
        (fun a : RegCoeffField d =>
          toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  simpa [fullBlockFluctuationMatrixWithNormalizer, Abar, g] using! hg.comp_aemeasurable hM

theorem aemeasurable_descendantsAverageFluctuationMatrixWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverageFluctuationMatrixWithNormalizer
          hP hStruct center S Q j a) P := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      AEMeasurable
        (fun a : RegCoeffField d =>
          ∑ R ∈ D,
            fullBlockFluctuationMatrixWithNormalizer hP hStruct center S
              (cubeSet R) a) P := by
    refine (Finset.aemeasurable_sum D (fun R _hR =>
        aemeasurable_fullBlockFluctuationMatrixWithNormalizer_cubeSet
          hP hStruct center S R)).congr ?_
    filter_upwards with a
    simp
  have hscaled :
      AEMeasurable
        (fun a : RegCoeffField d =>
          ((D.card : ℝ)⁻¹) •
            (∑ R ∈ D,
              fullBlockFluctuationMatrixWithNormalizer hP hStruct center S
                (cubeSet R) a)) P :=
    hsum.const_smul ((D.card : ℝ)⁻¹)
  refine hscaled.congr ?_
  filter_upwards with a
  rw [descendantsAverageFluctuationMatrixWithNormalizer,
    descendantsAverageFullBlockMat_eq_smul_sum]

theorem aemeasurable_descendantsAverageFluctuationOperatorNormSqWithNormalizer
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (center : ℤ) (S : FullBlockMat d) (Q : TriadicCube d) (j : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        descendantsAverageFluctuationOperatorNormSqWithNormalizer
          hP hStruct center S Q j a) P := by
  let g : FullBlockMat d → ℝ :=
    fun M => ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ ^ (2 : ℕ)
  have hg : Measurable g := by
    let L :
        FullBlockMat d →ₗ[ℝ]
          (EuclideanSpace ℝ (BlockCoord d) →L[ℝ] EuclideanSpace ℝ (BlockCoord d)) := {
      toFun := fun M => Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
      map_add' := by
        intro A B
        exact map_add (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) A B
      map_smul' := by
        intro r A
        exact map_smul (Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ)) r A
    }
    have hcont : Continuous g :=
      ((continuous_norm.comp L.continuous_of_finiteDimensional).pow 2)
    exact hcont.measurable
  simpa [descendantsAverageFluctuationOperatorNormSqWithNormalizer, g] using!
    hg.comp_aemeasurable
      (aemeasurable_descendantsAverageFluctuationMatrixWithNormalizer
        hP hStruct center S Q j)

theorem integrable_descendantsAverageFluctuationOperatorNormSqWithNormalizer_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) (S : FullBlockMat d) :
    Integrable
      (descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k)) P := by
  classical
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  have hdomInt :
      Integrable
        (fun a : RegCoeffField d =>
          descendantsAverage Q j
            (fun R =>
              fullBlockFluctuationOperatorNormSqWithNormalizer
                hP hStruct (m : ℤ) S (cubeSet R) a)) P := by
    simpa [Q, j] using
      integrable_descendantsAverage_fullBlockFluctuationOperatorNormSqWithNormalizer_from_P4_of_stationary
        hP hStruct hP4 m n k hk S
  refine Integrable.mono' hdomInt
    (aemeasurable_descendantsAverageFluctuationOperatorNormSqWithNormalizer
      hP hStruct (m : ℤ) S Q j).aestronglyMeasurable ?_
  filter_upwards with a
  have hle :=
    descendantsAverageFluctuationOperatorNormSqWithNormalizer_le_descendantsAverage
      hP hStruct (m : ℤ) S Q j a
  have hleft_nonneg :
      0 ≤ descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct (m : ℤ) S Q j a := by
    simp [descendantsAverageFluctuationOperatorNormSqWithNormalizer]
  rw [Real.norm_of_nonneg (by simpa [Q, j] using hleft_nonneg)]
  simpa [Q, j] using hle

theorem memLp_two_blockJTraceAverageWithNormalizers_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (_m n k : ℕ) (_hk : k ≤ n) (S T : FullBlockMat d) :
    MemLp
      (blockJTraceAverageWithNormalizers S T
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
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a)
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
          (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α))
  change
    MemLp
      (fun a : RegCoeffField d =>
        descendantsAverage (originCube d (n : ℤ)) (n - k)
          (fun R =>
            ∑ α : BlockCoord d,
              blockJObservableCubeSetBlockVec R
                (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a))
      (2 : ENNReal) P
  simpa [Q, j, blockJTraceAverageWithNormalizers] using
    Ch04.memLp_descendantsAverage (P := P) (Q := Q) (j := j)
      (F := fun R a =>
        ∑ α : BlockCoord d,
          blockJObservableCubeSetBlockVec R
            (fullBlockMatrixProbe S α) (fullBlockMatrixProbe T α) a)
      hchild

theorem integrable_blockJTraceAverageSqWithNormalizers_from_P4_of_stationary
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) (S T : FullBlockMat d) :
    Integrable
      (blockJTraceAverageSqWithNormalizers S T
        (originCube d (n : ℤ)) (n - k)) P := by
  have hmem :=
    memLp_two_blockJTraceAverageWithNormalizers_from_P4_of_stationary
      hP hStruct hP4 m n k hk S T
  simpa [blockJTraceAverageSqWithNormalizers, Real.norm_eq_abs, sq_abs] using!
    hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- Integrated Section 5.6 variance estimate with quadratic `J` error and
arbitrary deterministic normalizers.  The manuscript specialization is
`S = B^{-1/2}` and `T = B^{1/2}`. -/
theorem fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_integral_le_two_descendantsAverageWithNormalizer_add_eight_blockJTraceAverageSqWithNormalizers
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (m n k : ℕ) (hk : k ≤ n) (S T : FullBlockMat d) :
    ∫ a,
        fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          hP hStruct (m : ℤ) S (originCube d (n : ℤ)) a ∂P ≤
      2 *
        ∫ a,
          descendantsAverageFluctuationOperatorNormSqWithNormalizer
            hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a ∂P +
      8 *
        ∫ a,
          blockJTraceAverageSqWithNormalizers S T
            (originCube d (n : ℤ)) (n - k) a ∂P := by
  let Q : TriadicCube d := originCube d (n : ℤ)
  let j : ℕ := n - k
  let F : RegCoeffField d → ℝ :=
    fun a =>
      descendantsAverageFluctuationOperatorNormSqWithNormalizer
        hP hStruct (m : ℤ) S Q j a
  let J : RegCoeffField d → ℝ :=
    fun a => blockJTraceAverageSqWithNormalizers S T Q j a
  have hFInt : Integrable F P := by
    simpa [F, Q, j] using
      integrable_descendantsAverageFluctuationOperatorNormSqWithNormalizer_from_P4_of_stationary
        hP hStruct hP4 m n k hk S
  have hJInt : Integrable J P := by
    simpa [J, Q, j] using
      integrable_blockJTraceAverageSqWithNormalizers_from_P4_of_stationary
        hP hStruct hP4 m n k hk S T
  have hRhsInt : Integrable (fun a : RegCoeffField d => 2 * F a + 8 * J a) P :=
    (hFInt.const_mul (2 : ℝ)).add (hJInt.const_mul (8 : ℝ))
  have hpoint :
      (fun a : RegCoeffField d =>
        fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          hP hStruct (m : ℤ) S Q a)
        ≤ᵐ[P]
      fun a : RegCoeffField d => 2 * F a + 8 * J a := by
    simpa [F, J, Q, j] using
      fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer_le_two_descendantsAverageWithNormalizer_add_eight_blockJTraceAverageSqWithNormalizers_ae
        hP hStruct (m : ℤ) S T Q j
  have hmono :
      ∫ a,
          fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
            hP hStruct (m : ℤ) S Q a ∂P ≤
        ∫ a, 2 * F a + 8 * J a ∂P := by
    refine integral_mono_of_nonneg ?_ hRhsInt hpoint
    filter_upwards with a
    simp [fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer,
      fullBlockFluctuationOperatorNormSqWithNormalizer]
  calc
    ∫ a,
        fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
          hP hStruct (m : ℤ) S (originCube d (n : ℤ)) a ∂P
        = ∫ a,
            fullBlockFluctuationOperatorNormSqAtScaleWithNormalizer
              hP hStruct (m : ℤ) S Q a ∂P := by
          rfl
    _ ≤ ∫ a, 2 * F a + 8 * J a ∂P := hmono
    _ = ∫ a, 2 * F a ∂P + ∫ a, 8 * J a ∂P := by
          rw [integral_add (hFInt.const_mul (2 : ℝ)) (hJInt.const_mul (8 : ℝ))]
    _ = 2 * ∫ a, F a ∂P + 8 * ∫ a, J a ∂P := by
          rw [integral_const_mul, integral_const_mul]
    _ =
      2 *
        ∫ a,
          descendantsAverageFluctuationOperatorNormSqWithNormalizer
            hP hStruct (m : ℤ) S (originCube d (n : ℤ)) (n - k) a ∂P +
      8 *
        ∫ a,
          blockJTraceAverageSqWithNormalizers S T
            (originCube d (n : ℤ)) (n - k) a ∂P := by
          rfl
end

end Section56
end Ch05
end Book
end Homogenization
