/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Polarize
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Averaging
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich

/-!
# Scalar normalization bounds for the fluctuation bridge

The fluctuation observable normalizes the centered coarse block matrix
by the diagonal `D = diag(scalarFullBlockInvSqrtDiag b c)`, where
`b = barSigmaAtScale` and `c = barSigmaStarAtScale` are the structural-law scalars.

Here we pin down the two-sided bounds on `b` and `c` that make the diagonal
normalization uniformly bounded:

* `ae_coarseBlockQuadratic_lower_of_thetaEllipticLaw` — the a.s. lower `C1`
  Loewner bound (mirroring the upper bound `ae_coarseBlockQuadratic_bounds_...`).
* `half_le_barSigmaAtScale` — `1/2 ≤ b`.
* `barSigmaStarAtScale_pos` / `barSigmaStarAtScale_le_two_mul_Theta` — `0 < c` and
  `c ≤ 2Θ`.

The `b` and `c` values are read off the isotropic annealed block matrix
(`annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale`), whose diagonal
basis pairings equal `b` and `c⁻¹`, integrated against the a.s. `C1′` sandwich
(`mean_zero_coarse_blockQuadratic`).
-/

namespace Homogenization

open Homogenization MeasureTheory
open Homogenization.Book.Ch04
  (RestrictionCoeffLaw RestrictionLawCarrier RestrictionStructuralLaw annealedBlockMatrixAtScale
    scalarAnnealedBlockMatrixAtScale scalarFullBlockInvSqrtDiag)
open Homogenization.Book.Ch05.Section54.VarianceBoundGoodScale
  (annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale)

variable {d : ℕ}

/-- **C1 (lower, a.s.).**  Under the amended `ThetaEllipticLaw Θ L`, the coarse
block observable a.s. dominates the lower diagonal quadratic form
`½|p|² + (2Θ)⁻¹|q|²`.  Proved by routing each realization through the C2
truncation bridge to an everywhere-`(1,Θ)`-elliptic representative and applying
the deterministic lower Loewner sandwich, exactly as
`ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw` does for the upper bound. -/
theorem ae_coarseBlockQuadratic_lower_of_thetaEllipticLaw [NeZero d] {L : RestrictionCoeffLaw d}
    {Θ : ℝ} (hΘ : 1 ≤ Θ) (hell : ThetaEllipticLaw Θ L) (m : ℤ) (P : BlockVec d) :
    ∀ᵐ a ∂L,
      (1 / 2 : ℝ) * vecNormSq P.1 + (2 * Θ)⁻¹ * vecNormSq P.2 ≤
        blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P) := by
  classical
  filter_upwards [hell] with a haeEll
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  have hmeasA :
      Measurable (fun x => fun i j =>
        if x ∈ cubeSet (originCube d m) then a x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Set.indicator] using! (a.entry_measurable i j).indicator hU
  have haeU : ∀ᵐ x ∂(volume.restrict (cubeSet (originCube d m))),
      IsEllipticMatrix 1 Θ (a x) := ae_restrict_of_ae haeEll
  obtain ⟨a', hEll', _, hcoarse, _⟩ := exists_ellipticFieldOn_ae_eq hU hΘ hmeasA haeU
  rw [← hcoarse]
  have hlow := blockDiag_blockMatLoewnerLE_coarseBlockMatrix_cube hEll' P
  obtain ⟨p, q⟩ := P
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one (1 / 2 : ℝ) ((2 * Θ)⁻¹) p q] at hlow
  simpa using hlow

/-- Integrability of the coarse block quadratic form for a fixed probe vector,
under any `ThetaEllipticLaw` on a probability law. -/
theorem integrable_coarseBlockQuadratic_of_thetaEllipticLaw [NeZero d] {L : RestrictionCoeffLaw d}
    {Θ : ℝ} (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hLaw : ThetaEllipticLaw Θ L)
    (m : ℤ) (P : BlockVec d) :
    Integrable
      (fun a => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)) L := by
  have : IsProbabilityMeasure L := hP.isProbability
  refine (integrable_const (2 * (Θ * vecNormSq P.1 + vecNormSq P.2))).mono'
    (aestronglyMeasurable_coarseBlockQuadratic_cubeSet hP m P) ?_
  filter_upwards [ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m P] with a ha
  rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
  exact ha.2

private theorem vecNormSq_single_one (i : Fin d) :
    vecNormSq (Pi.single i 1 : Vec d) = 1 := by
  rw [vecNormSq, vecDot, Finset.sum_eq_single i]
  · simp
  · intro j _ hij; simp [Pi.single_eq_of_ne hij]
  · simp

/-- **`1/2 ≤ b`.**  The structural-law scalar `\bar\sigma_m` is at least `1/2`:
it is the annealed diagonal upper-left entry, which the integrated lower `C1`
sandwich bounds below by `1/2`. -/
theorem half_le_barSigmaAtScale [NeZero d] {L : RestrictionCoeffLaw d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) :
    (1 / 2 : ℝ) ≤ hP.barSigmaAtScale hStruct m := by
  have : IsProbabilityMeasure L := hP.isProbability
  have i0 : Fin d := ⟨0, NeZero.pos d⟩
  set P0 : BlockVec d := blockBasis (Sum.inl i0) with hP0
  have hmean := mean_zero_coarse_blockQuadratic hΘ hP hLaw m P0
  have hEntry :
      blockVecDot P0 (blockMatVecMul (annealedBlockMatrixAtScale L m) P0)
        = hP.barSigmaAtScale hStruct m := by
    rw [annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct m,
      hP0, blockBasis_pairing]
    simp [scalarAnnealedBlockMatrixAtScale, Homogenization.Book.Ch02.blockDiag,
      blockMatEntry, Matrix.one_apply_eq]
  have hInt := integrable_coarseBlockQuadratic_of_thetaEllipticLaw hΘ hP hLaw m P0
  have hlow : ∀ᵐ a ∂L,
      (1 / 2 : ℝ) ≤ blockVecDot P0
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P0) := by
    filter_upwards [ae_coarseBlockQuadratic_lower_of_thetaEllipticLaw hΘ hLaw m P0] with a ha
    have h1 : vecNormSq P0.1 = 1 := by rw [hP0]; simp [blockBasis, vecNormSq_single_one]
    have h2 : vecNormSq P0.2 = 0 := by rw [hP0]; simp [blockBasis, vecNormSq, vecDot]
    rw [h1, h2] at ha
    simpa using ha
  calc (1 / 2 : ℝ) = ∫ _a, (1 / 2 : ℝ) ∂L := by simp
    _ ≤ ∫ a, blockVecDot P0
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P0) ∂L :=
        integral_mono_ae (integrable_const _) hInt hlow
    _ = blockVecDot P0 (blockMatVecMul (annealedBlockMatrixAtScale L m) P0) := hmean
    _ = hP.barSigmaAtScale hStruct m := hEntry

/-- The annealed diagonal lower-right entry equals `c⁻¹`, and is sandwiched in
`[(2Θ)⁻¹, 2]` by the integrated `C1′` bounds. -/
private theorem barSigmaStarInv_mem [NeZero d] {L : RestrictionCoeffLaw d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) :
    (2 * Θ)⁻¹ ≤ (hP.barSigmaStarAtScale hStruct m)⁻¹ ∧
      (hP.barSigmaStarAtScale hStruct m)⁻¹ ≤ 2 := by
  have : IsProbabilityMeasure L := hP.isProbability
  have i0 : Fin d := ⟨0, NeZero.pos d⟩
  set P1 : BlockVec d := blockBasis (Sum.inr i0) with hP1
  have hmean := mean_zero_coarse_blockQuadratic hΘ hP hLaw m P1
  have hEntry :
      blockVecDot P1 (blockMatVecMul (annealedBlockMatrixAtScale L m) P1)
        = (hP.barSigmaStarAtScale hStruct m)⁻¹ := by
    rw [annealedBlockMatrixAtScale_eq_scalarAnnealedBlockMatrixAtScale hP hStruct m,
      hP1, blockBasis_pairing]
    simp [scalarAnnealedBlockMatrixAtScale, Homogenization.Book.Ch02.blockDiag,
      blockMatEntry, Matrix.one_apply_eq]
  have hInt := integrable_coarseBlockQuadratic_of_thetaEllipticLaw hΘ hP hLaw m P1
  have h1 : vecNormSq P1.1 = 0 := by rw [hP1]; simp [blockBasis, vecNormSq, vecDot]
  have h2 : vecNormSq P1.2 = 1 := by rw [hP1]; simp [blockBasis, vecNormSq_single_one]
  constructor
  · have hlow : ∀ᵐ a ∂L,
        (2 * Θ)⁻¹ ≤ blockVecDot P1
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P1) := by
      filter_upwards [ae_coarseBlockQuadratic_lower_of_thetaEllipticLaw hΘ hLaw m P1] with a ha
      rw [h1, h2] at ha
      simpa using ha
    calc (2 * Θ)⁻¹ = ∫ _a, (2 * Θ)⁻¹ ∂L := by simp
      _ ≤ ∫ a, blockVecDot P1
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P1) ∂L :=
          integral_mono_ae (integrable_const _) hInt hlow
      _ = (hP.barSigmaStarAtScale hStruct m)⁻¹ := by rw [hmean, hEntry]
  · have hup : ∀ᵐ a ∂L,
        blockVecDot P1
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P1) ≤ 2 := by
      filter_upwards [ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m P1] with a ha
      rw [h1, h2] at ha
      simpa using ha.2
    calc (hP.barSigmaStarAtScale hStruct m)⁻¹
          = ∫ a, blockVecDot P1
              (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P1) ∂L := by
            rw [hmean, hEntry]
      _ ≤ ∫ _a, (2 : ℝ) ∂L := integral_mono_ae hInt (integrable_const _) hup
      _ = 2 := by simp

/-- **`0 < c`.** -/
theorem barSigmaStarAtScale_pos [NeZero d] {L : RestrictionCoeffLaw d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) :
    0 < hP.barSigmaStarAtScale hStruct m := by
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  obtain ⟨hlow, _⟩ := barSigmaStarInv_mem hΘ hP hStruct hLaw m
  have hpos_inv : 0 < (hP.barSigmaStarAtScale hStruct m)⁻¹ :=
    lt_of_lt_of_le (by positivity) hlow
  exact inv_pos.mp hpos_inv

/-- **`c ≤ 2Θ`.** -/
theorem barSigmaStarAtScale_le_two_mul_Theta [NeZero d] {L : RestrictionCoeffLaw d} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) (hP : RestrictionLawCarrier L) (hStruct : RestrictionStructuralLaw L)
    (hLaw : ThetaEllipticLaw Θ L) (m : ℤ) :
    hP.barSigmaStarAtScale hStruct m ≤ 2 * Θ := by
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hc0 : 0 < hP.barSigmaStarAtScale hStruct m :=
    barSigmaStarAtScale_pos hΘ hP hStruct hLaw m
  obtain ⟨hlow, _⟩ := barSigmaStarInv_mem hΘ hP hStruct hLaw m
  have h2Θ : (0 : ℝ) < 2 * Θ := by positivity
  -- (2Θ)⁻¹ ≤ c⁻¹  ⟹  c ≤ 2Θ
  exact (inv_le_inv₀ h2Θ hc0).mp hlow

end Homogenization
