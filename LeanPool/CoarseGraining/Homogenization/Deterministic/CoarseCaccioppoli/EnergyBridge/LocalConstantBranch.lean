/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.SingleCubeRhs

/-! # Local Constant Branch -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local constant branch coefficient helpers

This file isolates the bounded coefficient step for the constant branch in the
small-cube Caccioppoli route.  The local `L²` norm of `u` has already been
factored out by the descendant summation argument, so the target is the
single-cube base coefficient.
-/

/-- Constant-branch local coefficient comparison from separated coefficient
factor bounds and an `L∞` bound for the cutoff gradient.

The final scalar hypothesis is the remaining deterministic adequacy comparison
between the bounded exact coefficient/cutoff expression and the local
single-cube base coefficient at scale `kR - j`. -/
theorem
    coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds
    {d : ℕ} (R : TriadicCube d) (a : CoeffField d)
    (ξ : Vec d → Vec d) {B Ceff kR Aavg Aflux1 Xi : ℝ} (j : ℕ)
    (hB_nonneg : 0 ≤ B)
    (hAavg : Real.sqrt (coarseBBlockNorm R a) ≤ Aavg)
    (hAflux1 :
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq R (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) ≤ Aflux1)
    (hξ : cubeLpNorm R ∞ ξ ≤ Xi)
    (hbounded :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R Aavg Aflux1 *
          (B + cubeBesovScaleWeight 1 R * Xi) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff
          (kR - (j : ℝ))) :
    coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
        (B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff
        (kR - (j : ℝ)) := by
  have hAavg_nonneg : 0 ≤ Aavg :=
    le_trans (Real.sqrt_nonneg _) hAavg
  have hdisc1_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * (1 : ℝ))
  have hLambda1_nonneg : 0 ≤ LambdaSq R (1 : ℝ) (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg R (1 : ℝ) a (by norm_num)
  have hAflux1_nonneg : 0 ≤ Aflux1 := by
    exact le_trans
      (mul_nonneg (inv_nonneg.mpr hdisc1_pos.le)
        (Real.rpow_nonneg hLambda1_nonneg _))
      hAflux1
  have hcoeff :
      coarseCaccioppoliFluxEnergyExactConstantCoeff R a ≤
        coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R Aavg Aflux1 :=
    coarseCaccioppoliFluxEnergyExactConstantCoeff_le_factorBound R a hAavg hAflux1
  have hfactor_nonneg :
      0 ≤ coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R Aavg Aflux1 :=
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_nonneg R
      hAavg_nonneg hAflux1_nonneg
  have hcutoff :
      B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ ≤
        B + cubeBesovScaleWeight 1 R * Xi := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left
      (mul_le_mul_of_nonneg_left hξ (cubeBesovScaleWeight_nonneg 1 R)) B
  have hcutoff_nonneg :
      0 ≤ B + cubeBesovScaleWeight 1 R * cubeLpNorm R ∞ ξ := by
    exact add_nonneg hB_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg 1 R) (cubeLpNorm_nonneg R ∞ ξ))
  exact le_trans
    (mul_le_mul hcoeff hcutoff hcutoff_nonneg hfactor_nonneg)
    hbounded

/-- Descendant version for a parent quantitative cutoff.  The `L∞` cutoff
gradient input is supplied by the standard descendant-local quantitative
cutoff bound. -/
theorem
    coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_cutoffGradient_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (a : CoeffField d)
    {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    {B Ceff kR Aavg Aflux1 : ℝ}
    (hB_nonneg : 0 ≤ B)
    (hAavg : Real.sqrt (coarseBBlockNorm R a) ≤ Aavg)
    (hAflux1 :
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
          Real.rpow (LambdaSq R (1 : ℝ) (.finite 1) a) (1 / 2 : ℝ) ≤ Aflux1)
    (hbounded :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R Aavg Aflux1 *
          (B + cubeBesovScaleWeight 1 R *
            (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q))) ≤
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff
          (kR - (j : ℝ))) :
    coarseCaccioppoliFluxEnergyExactConstantCoeff R a *
        (B + cubeBesovScaleWeight 1 R *
          cubeLpNorm R ∞ (scalarCutoffGradientField η)) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff
        (kR - (j : ℝ)) := by
  exact
    coarseCaccioppoliFluxEnergyExactConstantCoeff_mul_le_singleCubeBoundaryConstantBaseCoeff_of_factor_bounds
      R a (scalarCutoffGradientField η) j hB_nonneg hAavg hAflux1
      (quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le_on_descendant hR η)
      hbounded

end

end Homogenization
