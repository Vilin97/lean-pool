/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Scalar
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.AnnealedDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks

/-!
# Centered second moments of the block matrix

From the scalar estimate `scalar_block_variance` we pass to the *centered*
block matrix `A_m − Ā_m`, where `Ā_m = annealedBlockMatrixAtScale L m` is the
entrywise annealed matrix.

* `integrable_blockMatEntry_coarse` — each entry of the coarse block matrix is
  integrable (its a.s. symmetry turns the C4 quadratic bounds at `blockBasis`
  vectors into an a.s. entry bound).
* `mean_zero_coarse_blockQuadratic` — `𝔼[w·A_m w] = w·Ā_m w` (integral
  linearity of the finite block quadratic form).
* `centered_quadratic_second_moment` — for arbitrary `w`,
  `𝔼[(w·(A_m − Ā_m)w)²] = Var[w·A_m w] ≤ Cd·(Θ|w.1|²+|w.2|²)²·min{1, Θ²3^{-βm}}`.
-/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier annealedBlockMatrixAtScale)

variable {d : ℕ}

/-- **Entrywise integrability of the coarse block matrix.**  Uses a.s. symmetry
plus the C4 quadratic bounds at the `blockBasis` vectors. -/
theorem integrable_blockMatEntry_coarse [NeZero d]
    {L : RestrictionCoeffLaw d} {Θ : ℝ} (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) (α β : BlockCoord d) :
    Integrable
      (fun a => blockMatEntry (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) α β) L := by
  have : IsProbabilityMeasure L := hP.isProbability
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hAEM : AEMeasurable
      (fun a => blockMatEntry (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) α β) L := by
    cases α with
    | inl i => cases β with
      | inl j => exact hP.aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet (originCube d m) i j
      | inr j => exact hP.aemeasurable_coarseBlockMatrix_upperRight_apply_cubeSet (originCube d m) i j
    | inr i => cases β with
      | inl j => exact hP.aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet (originCube d m) i j
      | inr j => exact hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet (originCube d m) i j
  -- abbreviations for the three `M²` bounds
  set Ms : ℝ := Θ * vecNormSq (blockBasis α + blockBasis β).1
      + vecNormSq (blockBasis α + blockBasis β).2 with hMsdef
  set Ma : ℝ := Θ * vecNormSq (blockBasis α (d := d)).1
      + vecNormSq (blockBasis α (d := d)).2 with hMadef
  set Mb : ℝ := Θ * vecNormSq (blockBasis β (d := d)).1
      + vecNormSq (blockBasis β (d := d)).2 with hMbdef
  have hMs0 : (0 : ℝ) ≤ Ms := by
    rw [hMsdef]; exact add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hMa0 : (0 : ℝ) ≤ Ma := by
    rw [hMadef]; exact add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hMb0 : (0 : ℝ) ≤ Mb := by
    rw [hMbdef]; exact add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  refine (integrable_const (Ms + Ma + Mb)).mono' hAEM.aestronglyMeasurable ?_
  filter_upwards [ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m
        (blockBasis α + blockBasis β),
      ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m (blockBasis α),
      ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m (blockBasis β),
      Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale.isSymmetricBlockMat_coarseBlockMatrix_cubeSet_ae
        hP (originCube d m)]
    with a hsum hα hβ hsymm
  have hQsum := blockBasis_sum_pairing (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) α β
  have hQα := blockBasis_pairing (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) α α
  have hQβ := blockBasis_pairing (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) β β
  have hsymαβ := hsymm α β
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [hQsum, hQα, hQβ, hsymαβ, hsum.1, hα.2, hβ.2, hMs0, hMa0, hMb0]
  · linarith [hQsum, hQα, hQβ, hsymαβ, hsum.2, hα.1, hβ.1, hMs0, hMa0, hMb0]

/-- **Mean-zero.**  `𝔼[w·A_m w] = w·Ā_m w`. -/
theorem mean_zero_coarse_blockQuadratic [NeZero d]
    {L : RestrictionCoeffLaw d} {Θ : ℝ} (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) (w : BlockVec d) :
    (∫ a, blockVecDot w
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) w) ∂L)
      = blockVecDot w (blockMatVecMul (annealedBlockMatrixAtScale L m) w) := by
  rw [Homogenization.Book.Ch04.integral_blockVecDot_blockMatVecMul_eq_of_integrable_entries
    (fun α β => integrable_blockMatEntry_coarse hΘ hP hLaw m α β) w w]
  rfl

/-- **Centered second moment for an arbitrary doubled vector.**  Equal to
`Var[w·A_m w]`, hence bounded by the scalar estimate.  The constant is the one
from `scalar_block_variance`, uniform in all parameters. -/
theorem centered_quadratic_second_moment [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} (_hm : 0 ≤ m) {Θ : ℝ} (_hΘ : 1 ≤ Θ) {L : RestrictionCoeffLaw d}
        [IsProbabilityMeasure L] (_hP : RestrictionLawCarrier L)
        (_hURD : IsRestrictionUnitRangeDependentR L)
        (_hLaw : ThetaEllipticLaw Θ L) (w : BlockVec d),
      (∫ a, (blockVecDot w (blockMatVecMul (ofFullBlockMat
            (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun)
              - toFullBlockMat (annealedBlockMatrixAtScale L m))) w)) ^ 2 ∂L)
        ≤ Cd * (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2
            * min 1 (Θ ^ 2 * ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1))) := by
  obtain ⟨Cd, hCd0, hN1⟩ := scalar_block_variance (d := d) hd
  refine ⟨Cd, hCd0, ?_⟩
  intro m hm Θ hΘ L _ hP hURD hLaw w
  set c : ℝ := blockVecDot w (blockMatVecMul (annealedBlockMatrixAtScale L m) w) with hcdef
  have hXaem : AEMeasurable
      (fun a => blockVecDot w
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) w)) L :=
    (aestronglyMeasurable_coarseBlockQuadratic_cubeSet hP m w).aemeasurable
  have hmean := mean_zero_coarse_blockQuadratic hΘ hP hLaw m w
  -- the integrand is `(X − c)²`
  have hpt : ∀ a : RegCoeffField d, (blockVecDot w (blockMatVecMul (ofFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun)
            - toFullBlockMat (annealedBlockMatrixAtScale L m))) w)) ^ 2
        = (blockVecDot w
              (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) w) - c) ^ 2 := by
    intro a
    rw [blockVecDot_blockMatVecMul_ofFullBlockMat_sub, hcdef]
  calc (∫ a, (blockVecDot w (blockMatVecMul (ofFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun)
            - toFullBlockMat (annealedBlockMatrixAtScale L m))) w)) ^ 2 ∂L)
      = ∫ a, (blockVecDot w
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) w) - c) ^ 2 ∂L := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Var[fun a => blockVecDot w
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) w); L] := by
        rw [variance_eq_integral hXaem, hmean]
    _ ≤ Cd * (Θ * vecNormSq w.1 + vecNormSq w.2) ^ 2
          * min 1 (Θ ^ 2 * ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1))) :=
        hN1 hm hΘ hP hURD hLaw w

end Homogenization
