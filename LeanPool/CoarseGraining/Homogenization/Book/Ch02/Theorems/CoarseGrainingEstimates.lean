/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.CoarseGrainingEstimates
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-! # Coarse Graining Estimates -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem for `l.cg.response.estimates.basic.definitions`. -/
theorem responseCoarseGrainingEstimatesTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ResponseCoarseGrainingEstimatesTheory U a :=
  Homogenization.Internal.Ch02.BookCh02.responseCoarseGrainingEstimatesTheory U a

/-- The averaged gradient is controlled by the `σ_*^{-1}` operator norm times
the quadratic variation energy. -/
theorem vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (w : Solution U a) :
    vecNormSq (averageGradient U a w) ≤
      matrixNorm (sigmaStarInvCoarse U a) * variationEnergyValue U a w := by
  let avgGrad := averageGradient U a w
  have henergy :
      vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) ≤
        variationEnergyValue U a w := by
    have hraw :=
      (responseCoarseGrainingEstimatesTheory U a).average_gradient_energy w
    simpa [avgGrad] using (show
      vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) ≤
        variationEnergyValue U a w from by
          nlinarith [hraw])
  have hleft :
      ∀ ξ : Vec d,
        matVecMul (sigmaStarInvCoarse U a)
          (matVecMul (sigmaStarCoarse U a) ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul,
      sigmaStarInvCoarse_mul_sigmaStarCoarse
        (isUnit_det_sigmaStarInvCoarse U a)]
    funext i
    unfold matVecMul
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      have hij : i ≠ j := by
        intro h
        exact hji h.symm
      simp [hij]
    · simp
  have hnorm :
      vecNormSq avgGrad ≤
        matrixNorm (sigmaStarInvCoarse U a) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse U a) avgGrad) :=
    vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := sigmaStarCoarse U a) (B := sigmaStarInvCoarse U a)
      (sigmaStarInvCoarse_posDef U a).posSemidef hleft avgGrad
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left henergy (matrixNorm_nonneg _))

/-- The averaged flux is controlled by the `b` operator norm times the
quadratic variation energy. -/
theorem vecNormSq_averageFlux_le_matrixNorm_bCoarse_mul_variationEnergyValue
    {d : ℕ} (U : Domain d) (a : CoeffOn U) (w : Solution U a) :
    vecNormSq (averageFlux U a w) ≤
      matrixNorm (bCoarse U a) * variationEnergyValue U a w := by
  let avgFlux := averageFlux U a w
  have henergy :
      vecDot avgFlux (matVecMul ((bCoarse U a)⁻¹) avgFlux) ≤
        variationEnergyValue U a w := by
    have hraw :=
      (responseCoarseGrainingEstimatesTheory U a).average_flux_energy w
    simpa [avgFlux] using (show
      vecDot avgFlux (matVecMul ((bCoarse U a)⁻¹) avgFlux) ≤
        variationEnergyValue U a w from by
          nlinarith [hraw])
  have hdet : IsUnit (bCoarse U a).det :=
    (Matrix.isUnit_iff_isUnit_det (A := bCoarse U a)).mp
      (bCoarse_posDef U a).isUnit
  have hleft :
      ∀ ξ : Vec d,
        matVecMul (bCoarse U a) (matVecMul ((bCoarse U a)⁻¹) ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hdet]
    funext i
    unfold matVecMul
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      have hij : i ≠ j := by
        intro h
        exact hji h.symm
      simp [hij]
    · simp
  have hnorm :
      vecNormSq avgFlux ≤
        matrixNorm (bCoarse U a) *
          vecDot avgFlux (matVecMul ((bCoarse U a)⁻¹) avgFlux) :=
    vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := (bCoarse U a)⁻¹) (B := bCoarse U a)
      (bCoarse_posDef U a).posSemidef hleft avgFlux
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left henergy (matrixNorm_nonneg _))

end

end Ch02
end Book
end Homogenization
