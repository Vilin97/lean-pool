/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyCore

/-! # Assembly Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace WeakNormsMaximizer

/-!
# Final assembly for the weak-norm maximizer lemma

This file finishes the deterministic weak-norm maximizer theorem from the
scale-geometric core estimates.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

private theorem fluxScaleGeometricRHS_le_two_fluxRHSAtScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    {k m : ℤ} {t t' : ℝ}
    (ht : 0 < t) (ht_le : t ≤ 1)
    (hgap : 0 < t - t') (hgap_le : t - t' ≤ 1)
    (p q q0 : Vec d) :
      2 *
        (fluxAverageTermAtScale m k t p q q0 a +
          2 * fluxMismatchTermAtScale m k t t' p q a) +
      2 *
        (((2 * Real.sqrt
              (Ch04.LambdaSqCoeffField (originCube d m) t' (.finite 1) a)) *
            (Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹) *
              Real.sqrt (Ch04.restrictionResponseJObservableCubeSet (originCube d m) p q a)) +
          (Real.rpow (3 : ℝ) (-t * (Int.toNat (m - k) : ℝ)) *
              (1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
            Real.sqrt (vecNormSq (-q0))) ≤
        2 *
          fluxRHSAtScale (section53WeakNormMaximizerConst d)
            m k t t' p q q0 a := by
  let C : ℝ := section53WeakNormMaximizerConst d
  let Q : TriadicCube d := originCube d m
  let A : ℝ := fluxAverageTermAtScale m k t p q q0 a
  let M : ℝ := fluxMismatchTermAtScale m k t t' p q a
  let Low : ℝ := fluxLowScaleTailAtScale m k t t' p q a
  let Const : ℝ := fluxConstantTailAtScale m k t q0
  let lam : ℝ := Real.sqrt (Ch04.LambdaSqCoeffField Q t' (.finite 1) a)
  let tailGap : ℝ := Real.rpow (3 : ℝ) (-(t - t') * (Int.toNat (m - k) : ℝ))
  let discGap : ℝ := (1 - Real.rpow (3 : ℝ) (-(t - t')))⁻¹
  let sqrtJ : ℝ := Real.sqrt (Ch04.restrictionResponseJObservableCubeSet Q p q a)
  let tailT : ℝ := Real.rpow (3 : ℝ) (-t * (Int.toNat (m - k) : ℝ))
  let discT : ℝ := (1 - Real.rpow (3 : ℝ) (-t))⁻¹
  let sqrtQ : ℝ := Real.sqrt (vecNormSq (-q0))
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using fluxMismatchTermAtScale_nonneg m k t t' p q a
  have hM_le : 2 * M ≤ C * M := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [C] using two_le_section53WeakNormMaximizerConst d) hM_nonneg
  have hdiscGap : discGap ≤ 5 * (t - t')⁻¹ := by
    simpa [discGap] using inv_one_sub_rpow_three_neg_le_five_inv hgap hgap_le
  have hdiscT : discT ≤ 5 * t⁻¹ := by
    simpa [discT] using inv_one_sub_rpow_three_neg_le_five_inv ht ht_le
  have htailGap_nonneg : 0 ≤ tailGap := by
    dsimp [tailGap]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact Real.sqrt_nonneg _
  have hsqrtJ_nonneg : 0 ≤ sqrtJ := by
    dsimp [sqrtJ]
    exact Real.sqrt_nonneg _
  have hLowBase_nonneg : 0 ≤ (t - t')⁻¹ * tailGap * lam * sqrtJ := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr hgap.le) htailGap_nonneg) hlam_nonneg)
      hsqrtJ_nonneg
  have hLowGeom_le :
      (2 * lam) * (tailGap * discGap) * sqrtJ ≤ C * Low := by
    have hstep :
        (2 * lam) * (tailGap * discGap) * sqrtJ ≤
          (2 * lam) * (tailGap * (5 * (t - t')⁻¹)) * sqrtJ := by
      gcongr
    calc
      (2 * lam) * (tailGap * discGap) * sqrtJ
          ≤ (2 * lam) * (tailGap * (5 * (t - t')⁻¹)) * sqrtJ := hstep
      _ = 10 * ((t - t')⁻¹ * tailGap * lam * sqrtJ) := by ring
      _ ≤ C * ((t - t')⁻¹ * tailGap * lam * sqrtJ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [C] using ten_le_section53WeakNormMaximizerConst d)
            hLowBase_nonneg
      _ = C * Low := by
          simp [Low, fluxLowScaleTailAtScale, Q, lam, tailGap, sqrtJ]
  have hsqrtQ : sqrtQ ≤ ((d : ℝ) + 1) * ‖q0‖ := by
    simpa [sqrtQ, norm_neg] using sqrt_vecNormSq_le_succ_mul_norm (-q0)
  have htailT_nonneg : 0 ≤ tailT := by
    dsimp [tailT]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have htailT_discBound_nonneg : 0 ≤ tailT * (5 * t⁻¹) := by
    exact mul_nonneg htailT_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (5 : ℝ)) (inv_nonneg.mpr ht.le))
  have hConstBase_nonneg : 0 ≤ t⁻¹ * tailT * ‖q0‖ := by
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr ht.le) htailT_nonneg) (norm_nonneg q0)
  have hConstGeom_le :
      tailT * discT * sqrtQ ≤ C * Const := by
    calc
      tailT * discT * sqrtQ
          ≤ tailT * (5 * t⁻¹) * (((d : ℝ) + 1) * ‖q0‖) := by
            gcongr
      _ = (5 * ((d : ℝ) + 1)) * (t⁻¹ * tailT * ‖q0‖) := by ring
      _ ≤ C * (t⁻¹ * tailT * ‖q0‖) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa [C] using five_mul_succ_le_section53WeakNormMaximizerConst d)
            hConstBase_nonneg
      _ = C * Const := by
          simp [Const, fluxConstantTailAtScale, tailT]
  have hmain :
      2 * (A + 2 * M) + 2 *
          (((2 * lam) * (tailGap * discGap) * sqrtJ) +
            tailT * discT * sqrtQ) ≤
        2 * (A + C * M + C * Low + C * Const) := by
    nlinarith [hM_le, hLowGeom_le, hConstGeom_le]
  simpa [C, Q, A, M, Low, Const, lam, tailGap, discGap, sqrtJ, tailT, discT, sqrtQ,
    fluxRHSAtScale, mul_assoc] using hmain

/-- Deterministic gradient weak-norm bound for the scalar response maximizer
at homogenization scale.  The leading factor `2` records the current
high/low split normalization and is absorbed harmlessly in later constants. -/
theorem weakNormsMaximizerGradient_homogenizationScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (hkm : k < m) {s s' : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hs'_low : s / 2 ≤ s') (hs'_high : s' < s)
    (p q p0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet
        (originCube d m) s p q p0 a ≤
      2 *
        gradientRHSAtScale (section53WeakNormMaximizerConst d)
          m k s s' p q p0 a := by
  have hs'_pos : 0 < s' := by linarith
  have hgap : 0 < s - s' := sub_pos.mpr hs'_high
  have hgap_le : s - s' ≤ 1 := by linarith
  exact
    (gradientWeakNorm_le_scaleGeometricRHS a ha hkm.le hs hs'_pos hgap p q p0).trans
      (gradientScaleGeometricRHS_le_two_gradientRHSAtScale
        a hs hs_le hgap hgap_le p q p0)

/-- Deterministic flux weak-norm bound for the scalar response maximizer at
homogenization scale.  The leading factor `2` records the accepted split
loss and is absorbed harmlessly in later constants. -/
theorem weakNormsMaximizerFlux_homogenizationScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (hkm : k < m) {t t' : ℝ}
    (ht : 0 < t) (ht_le : t ≤ 1)
    (ht'_low : t / 2 ≤ t') (ht'_high : t' < t)
    (p q q0 : Vec d) :
    Ch04.canonicalScalarResponseFluxWeakNormCubeSet
        (originCube d m) t p q q0 a ≤
      2 *
        fluxRHSAtScale (section53WeakNormMaximizerConst d)
          m k t t' p q q0 a := by
  have ht'_pos : 0 < t' := by linarith
  have hgap : 0 < t - t' := sub_pos.mpr ht'_high
  have hgap_le : t - t' ≤ 1 := by linarith
  exact
    (fluxWeakNorm_le_scaleGeometricRHS a ha hkm.le ht ht'_pos hgap p q q0).trans
      (fluxScaleGeometricRHS_le_two_fluxRHSAtScale
        a ht ht_le hgap hgap_le p q q0)

/-- The paired deterministic weak-norm maximizer estimate, in the manuscript
parameter regime. -/
theorem weakNormsMaximizer_homogenizationScale
    {d : ℕ} [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    {k m : ℤ} (hkm : k < m)
    {s s' t t' : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hs'_low : s / 2 ≤ s') (hs'_high : s' < s)
    (ht : 0 < t) (ht_le : t ≤ 1)
    (ht'_low : t / 2 ≤ t') (ht'_high : t' < t)
    (p q p0 q0 : Vec d) :
    Ch04.canonicalScalarResponseGradientWeakNormCubeSet
        (originCube d m) s p q p0 a ≤
          2 *
            gradientRHSAtScale (section53WeakNormMaximizerConst d)
              m k s s' p q p0 a ∧
      Ch04.canonicalScalarResponseFluxWeakNormCubeSet
        (originCube d m) t p q q0 a ≤
          2 *
            fluxRHSAtScale (section53WeakNormMaximizerConst d)
              m k t t' p q q0 a := by
  constructor
  · exact weakNormsMaximizerGradient_homogenizationScale
      a ha hkm hs hs_le hs'_low hs'_high p q p0
  · exact weakNormsMaximizerFlux_homogenizationScale
      a ha hkm ht ht_le ht'_low ht'_high p q q0

end

end WeakNormsMaximizer
end Section53
end Ch05
end Book
end Homogenization
