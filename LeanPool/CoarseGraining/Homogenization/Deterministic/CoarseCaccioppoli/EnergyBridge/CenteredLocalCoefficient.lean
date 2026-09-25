/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.SingleCubeRhs

/-! # Centered Local Coefficient -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/-!
# Centered local coefficient bridge

This module isolates the centered small-cube coefficient bookkeeping used by
the descendant Caccioppoli summation.  The final scalar comparison is left as a
single adequacy hypothesis, while the exact coefficient is reduced to the
existing average, Besov, and cutoff-gradient factor bounds.
-/

/-- Centered exact coefficient domination from separated scalar factors.

The hypothesis `hcentered` is the remaining scalar algebraic comparison
against the note-facing centered single-cube coefficient. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_of_separated_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ)
    {Aavg AfluxS Xi D A1 AS T : ℝ}
    (hs0 : 0 < s) (hC : 0 ≤ C)
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hAavg : Real.sqrt (coarseBBlockNorm Q a) ≤ Aavg)
    (hAfluxS :
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤ AfluxS)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) Aavg Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s Aavg AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤ T) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤ T := by
  have hAavg_nonneg : 0 ≤ Aavg := by
    exact le_trans (Real.sqrt_nonneg _) hAavg
  have hXi_nonneg : 0 ≤ Xi := by
    exact le_trans (cubeLpNorm_nonneg Q ∞ ξ) hξ
  have hD_nonneg : 0 ≤ D := by
    exact le_trans hB_nonneg hB
  have hdiscS_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs0)
  have hLambdaS_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hAfluxS_nonneg : 0 ≤ AfluxS := by
    exact le_trans
      (mul_nonneg (inv_nonneg.mpr hdiscS_pos.le)
        (Real.rpow_nonneg hLambdaS_nonneg _))
      hAfluxS
  let BgCent : ℝ :=
    coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C
  have hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_nonneg
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hB_nonneg hC
  have hBgCent :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤ BgCent := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hD_nonneg hC
        hξ hB hAcirc1 hAcircS
  have havgCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤
        coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) Aavg Xi A1 C := by
    exact
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ hAavg_nonneg hXi_nonneg hAcirc1_nonneg hC
        hAavg hξ hAcirc1
  have hbesovCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s Aavg AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) := by
    simpa [BgCent] using
      (coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
        Q a s ξ hAavg_nonneg hAfluxS_nonneg hBgCentCoeff_nonneg
        hAavg hAfluxS hBgCent)
  rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
  exact le_trans (add_le_add havgCoeff_le hbesovCoeff_le) hcentered

theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_singleCubeBoundaryCenteredCoeff_of_separated_factor_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C k h : ℝ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ)
    {Aavg AfluxS Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hC : 0 ≤ C)
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hAavg : Real.sqrt (coarseBBlockNorm Q a) ≤ Aavg)
    (hAfluxS :
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤ AfluxS)
    (hξ : cubeLpNorm Q ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) Aavg Xi A1 C +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s Aavg AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff Q a s ξ Acirc1 AcircS B C ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C k h := by
  have hAavg_nonneg : 0 ≤ Aavg := by
    exact le_trans (Real.sqrt_nonneg _) hAavg
  have hXi_nonneg : 0 ≤ Xi := by
    exact le_trans (cubeLpNorm_nonneg Q ∞ ξ) hξ
  have hD_nonneg : 0 ≤ D := by
    exact le_trans hB_nonneg hB
  have hdiscS_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs0)
  have hLambdaS_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs0.le
  have hAfluxS_nonneg : 0 ≤ AfluxS := by
    exact le_trans
      (mul_nonneg (inv_nonneg.mpr hdiscS_pos.le)
        (Real.rpow_nonneg hLambdaS_nonneg _))
      hAfluxS
  let BgCent : ℝ :=
    coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C
  have hBgCentCoeff_nonneg :
      0 ≤ coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_nonneg
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hB_nonneg hC
  have hBgCent :
      coarseCaccioppoliCenteredCutoffCoeff Q s ξ Acirc1 AcircS B C ≤ BgCent := by
    exact
      coarseCaccioppoliCenteredCutoffCoeff_le_factorBound
        Q ξ hs0 hAcirc1_nonneg hAcircS_nonneg hXi_nonneg hD_nonneg hC
        hξ hB hAcirc1 hAcircS
  have havgCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff Q a ξ Acirc1 C ≤
        coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) Aavg Xi A1 C := by
    exact
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeff_le_factorBound
        Q a ξ hAavg_nonneg hXi_nonneg hAcirc1_nonneg hC
        hAavg hξ hAcirc1
  have hbesovCoeff_le :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff Q a s ξ Acirc1 AcircS B C ≤
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound Q s Aavg AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound Q s Xi D A1 AS C) := by
    simpa [BgCent] using
      (coarseCaccioppoliFluxEnergyExactCenteredBesovCoeff_le_factorBound
        Q a s ξ hAavg_nonneg hAfluxS_nonneg hBgCentCoeff_nonneg
        hAavg hAfluxS hBgCent)
  rw [coarseCaccioppoliFluxEnergyExactCenteredCoeff_eq_average_add_besov]
  exact le_trans (add_le_add havgCoeff_le hbesovCoeff_le) hcentered

/-- Local small-cube version of
`coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_singleCubeBoundaryCenteredCoeff_of_separated_factor_bounds`.

The conclusion has the descendant-local scale `kR - j` and height `j`, which is
the exact centered branch consumed by the small-cube summation layer. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_local_singleCubeBoundaryCenteredCoeff_of_separated_factor_bounds
    {d : ℕ} (R : TriadicCube d) (a : CoeffField d) (s Ceff kR : ℝ) (j : ℕ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ)
    {Aavg AfluxS Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hCeff : 0 ≤ Ceff)
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hAavg : Real.sqrt (coarseBBlockNorm R a) ≤ Aavg)
    (hAfluxS :
      (geometricDiscount s 1)⁻¹ *
          Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤ AfluxS)
    (hξ : cubeLpNorm R ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) Aavg Xi A1 Ceff +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s Aavg AfluxS
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s Xi D A1 AS Ceff) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
            (kR - (j : ℝ)) (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ Acirc1 AcircS B Ceff ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
        (kR - (j : ℝ)) (j : ℝ) := by
  exact
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_singleCubeBoundaryCenteredCoeff_of_separated_factor_bounds
      R a s Ceff (kR - (j : ℝ)) (j : ℝ) ξ Acirc1 AcircS B
      hs0 hCeff hB_nonneg hAcirc1_nonneg hAcircS_nonneg hAavg hAfluxS
      hξ hB hAcirc1 hAcircS hcentered

/-- Canonical-factor local small-cube centered coefficient bound.

This fills the average and flux slots with `coarseCaccioppoliLambdaFactor` and
uses the descendant cutoff-gradient bound supplied as `hξ`. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_local_singleCubeBoundaryCenteredCoeff_of_canonical_factor_bounds
    {d : ℕ} (R : TriadicCube d) (a : CoeffField d) (s Ceff kR : ℝ) (j : ℕ)
    (ξ : Vec d → Vec d) (Acirc1 AcircS B : ℝ)
    {Xi D A1 AS : ℝ}
    (hs0 : 0 < s) (hCeff : 0 ≤ Ceff)
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hB_nonneg : 0 ≤ B) (hAcirc1_nonneg : 0 ≤ Acirc1)
    (hAcircS_nonneg : 0 ≤ AcircS)
    (hξ : cubeLpNorm R ∞ ξ ≤ Xi)
    (hB : B ≤ D) (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s) Xi A1 Ceff +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s Xi D A1 AS Ceff) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
            (kR - (j : ℝ)) (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s ξ Acirc1 AcircS B Ceff ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
        (kR - (j : ℝ)) (j : ℝ) := by
  exact
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_local_singleCubeBoundaryCenteredCoeff_of_separated_factor_bounds
      R a s Ceff kR j ξ Acirc1 AcircS B hs0 hCeff
      hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a hs0 hsumS)
      (by simp [coarseCaccioppoliLambdaFactor])
      hξ hB hAcirc1 hAcircS hcentered

/-- Quantitative parent-cutoff specialization on a depth-`j` descendant.

The `L^\infty` bound for the gradient field is supplied by
`quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le_on_descendant`; the
only remaining cutoff-size comparison is the scalar Hessian bound `hB`. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_local_singleCubeBoundaryCenteredCoeff_of_quantitativeCutoff_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (a : CoeffField d)
    (s Ceff kR : ℝ) {ρ₁ ρ₂ : ℝ} (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (Acirc1 AcircS B : ℝ) {D A1 AS : ℝ}
    (hs0 : 0 < s) (hCeff : 0 ≤ Ceff)
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hB_nonneg : 0 ≤ B) (hB : B ≤ D)
    (hAcirc1_nonneg : 0 ≤ Acirc1) (hAcircS_nonneg : 0 ≤ AcircS)
    (hAcirc1 : Acirc1 ≤ A1) (hAcircS : AcircS ≤ AS)
    (hcentered :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q))
          A1 Ceff +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q))
            D A1 AS Ceff) ≤
          coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
            (kR - (j : ℝ)) (j : ℝ)) :
    coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s
        (scalarCutoffGradientField η) Acirc1 AcircS B Ceff ≤
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff R a s Ceff
        (kR - (j : ℝ)) (j : ℝ) := by
  exact
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_local_singleCubeBoundaryCenteredCoeff_of_canonical_factor_bounds
      R a s Ceff kR j (scalarCutoffGradientField η) Acirc1 AcircS B
      hs0 hCeff hsumS hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      (quantitativeCubeCutoff_cubeLpNorm_infty_gradientField_le_on_descendant hR η)
      hB hAcirc1 hAcircS hcentered

end

end Homogenization
