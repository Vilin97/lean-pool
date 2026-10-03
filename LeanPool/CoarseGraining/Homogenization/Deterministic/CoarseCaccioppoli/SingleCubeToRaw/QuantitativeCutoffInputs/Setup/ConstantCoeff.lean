/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup.ScaleBounds

/-! # Constant Coeff -/

@[expose] public section

namespace Homogenization

/-!
# Quantitative cutoff inputs: constant coefficient comparisons
-/

noncomputable section

open scoped ENNReal

/-- Constant-branch exact coefficient comparison on a descendant cube, after
the parent cutoff constants have been converted to the note's triadic scale.

The only scalar input is the expected fixed-constant calibration: the local
constant `Ceff` dominates the dimension/geometric-discount factor times the
parent-radius cutoff front. -/
theorem
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_parent_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d)
    {Ceff : ℝ} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        ((quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          quantitativeCubeCutoffGradientConst d / cubeRadius Q) ≤ Ceff) :
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
  let K : ℝ :=
    (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
        (cubeRadius Q) ^ (2 : ℕ)) +
      quantitativeCubeCutoffGradientConst d / cubeRadius Q
  let P : ℝ := (3 : ℝ) ^ k
  let L : ℝ := Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)
  let A0 : ℝ :=
    (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹
  let S : ℝ :=
    cubeBesovScaleWeight (-1) R *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
  have hcutoff : S ≤ K * P := by
    simpa [S, K, P] using
      (cubeBesovScaleWeight_neg_one_mul_parent_cutoff_terms_le_radiusConst_mul_pow
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hdisc_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0]
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (inv_nonneg.mpr hdisc_pos.le)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg
      (multiscale_ellipticity_LambdaSq_one_nonneg R 1 a (by norm_num)) _
  have hAL_nonneg : 0 ≤ A0 * L := mul_nonneg hA0_nonneg hL_nonneg
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hPL_nonneg : 0 ≤ P * L := mul_nonneg hP_nonneg hL_nonneg
  have hlarge' : A0 * K ≤ Ceff := by
    simpa [A0, K, mul_assoc] using hlarge
  have hleft_eq :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂) =
        (A0 * L) * S := by
    dsimp [A0, L, S]
    unfold coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound
      coarseCaccioppoliLambdaFactor
    simp
    ring_nf
  have hright_eq :
      Ceff * (P * L) =
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
    dsimp [P, L]
    unfold coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff
    simp [Real.rpow_natCast]
    ring
  calc
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂ +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
        = (A0 * L) * S := hleft_eq
    _ ≤ (A0 * L) * (K * P) :=
          mul_le_mul_of_nonneg_left hcutoff hAL_nonneg
    _ = (A0 * K) * (P * L) := by ring
    _ ≤ Ceff * (P * L) :=
          mul_le_mul_of_nonneg_right hlarge' hPL_nonneg
    _ = coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) :=
          hright_eq

/-- Buffered constant-branch exact coefficient comparison on a descendant cube.
The midpoint cutoff uses the full-gap triadic scale but requires the inflated
fixed cutoff front `4 * Hessian + 2 * Gradient`. -/
theorem
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound_mul_parent_buffered_cutoff_terms_le_singleCubeBoundaryConstantBaseCoeff_of_descendant
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d)
    {Ceff : ℝ} {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hlarge :
      (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (geometricDiscount (1 : ℝ) 1)⁻¹ *
        (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
              (cubeRadius Q) ^ (2 : ℕ)) +
          2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)) ≤ Ceff) :
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) ≤
      coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
  let K : ℝ :=
    4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
        (cubeRadius Q) ^ (2 : ℕ)) +
      2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q)
  let P : ℝ := (3 : ℝ) ^ k
  let L : ℝ := Real.rpow (LambdaSq R 1 (.finite 1) a) (1 / 2 : ℝ)
  let A0 : ℝ :=
    (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹
  let S : ℝ :=
    cubeBesovScaleWeight (-1) R *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
  have hcutoff : S ≤ K * P := by
    simpa [S, K, P] using
      (cubeBesovScaleWeight_neg_one_mul_parent_buffered_cutoff_terms_le_radiusConst_mul_pow
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hdisc_pos : 0 < geometricDiscount (1 : ℝ) 1 :=
    geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hA0_nonneg : 0 ≤ A0 := by
    dsimp [A0]
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (inv_nonneg.mpr hdisc_pos.le)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg
      (multiscale_ellipticity_LambdaSq_one_nonneg R 1 a (by norm_num)) _
  have hAL_nonneg : 0 ≤ A0 * L := mul_nonneg hA0_nonneg hL_nonneg
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hPL_nonneg : 0 ≤ P * L := mul_nonneg hP_nonneg hL_nonneg
  have hlarge' : A0 * K ≤ Ceff := by
    simpa [A0, K, mul_assoc] using hlarge
  have hleft_eq :
      coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
          (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
          cubeBesovScaleWeight 1 R *
            coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
              (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂)) =
        (A0 * L) * S := by
    dsimp [A0, L, S]
    unfold coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound
      coarseCaccioppoliLambdaFactor
    simp
    ring_nf
  have hright_eq :
      Ceff * (P * L) =
        coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) := by
    dsimp [P, L]
    unfold coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff
    simp [Real.rpow_natCast]
    ring
  calc
    coarseCaccioppoliFluxEnergyExactConstantCoeffFactorBound R
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ))
        (coarseCaccioppoliLambdaFactor R a (1 : ℝ)) *
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁
          (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂) +
        cubeBesovScaleWeight 1 R *
          coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁
            (coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂))
        = (A0 * L) * S := hleft_eq
    _ ≤ (A0 * L) * (K * P) :=
          mul_le_mul_of_nonneg_left hcutoff hAL_nonneg
    _ = (A0 * K) * (P * L) := by ring
    _ ≤ Ceff * (P * L) :=
          mul_le_mul_of_nonneg_right hlarge' hPL_nonneg
    _ = coarseCaccioppoliSingleCubeBoundaryConstantBaseCoeff R a Ceff (k : ℝ) :=
          hright_eq

end

end Homogenization
