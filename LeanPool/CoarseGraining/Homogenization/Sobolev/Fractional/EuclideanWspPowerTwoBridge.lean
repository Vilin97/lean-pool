/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity

/-!
# The exact `p = 2` Euclidean fractional full-norm bridge

This module identifies the `p = 2` Euclidean `W^{s,p}` seminorm on an origin
cube with the established physical centered-cube Euclidean `H^s` seminorm.
Their full norms differ only by the elementary comparison between
`sqrt (A^2 + B^2)` and `A + B`.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- On an origin cube, the `p = 2` power weight is the square of the exact
root weight used by the physical Euclidean `H^s` full norm. -/
theorem cubeEuclideanWspScalePowerWeight_originCube_two {d : ℕ} (m : ℤ)
    (s : FractionalOrder) :
    cubeEuclideanWspScalePowerWeight (originCube d m) s
        FiniteLpExponent.two =
      (exactOverlapRootWeight (originCube d m) s.1) ^ (2 : ℝ) := by
  rw [exactOverlapRootWeight_originCube_eq_scale_rpow]
  simp only [cubeEuclideanWspScalePowerWeight,
    cubeScaleFactor_originCube, FiniteLpExponent.two_exponent,
    centeredCubeScale]
  norm_num
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring

private theorem cubeEuclideanWspKernel_two_enorm_rpow_eq_centeredCubeEuclideanHsIntegrand
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel s FiniteLpExponent.two F z‖ₑ ^ (2 : ℝ) =
      centeredCubeEuclideanHsIntegrand s F z := by
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
  rw [norm_cubeEuclideanWspKernel]
  norm_num
  unfold centeredCubeEuclideanHsIntegrand
  rcases z with ⟨x, y⟩
  let a : ℝ := s.1 * 2 + (d : ℝ)
  rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
  rw [show -((d : ℝ) / 2) + -s.1 = -a / 2 by dsimp [a]; ring]
  rw [euclideanNorm_eq_norm_ofVec]
  by_cases hxy : x = y
  · subst y
    simp
  · have heuclideanDist : 0 < euclideanDist x y := by
      apply lt_of_le_of_ne (euclideanDist_nonneg x y)
      intro hzero
      exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
    have hpower :
        (euclideanDist x y ^ (-a / 2)) ^ 2 =
          (euclideanDist x y) ^ (-a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul heuclideanDist.le]
      congr 1
      ring
    rw [mul_pow, hpower]
    have hneg : (euclideanDist x y) ^ (-a) =
        ((euclideanDist x y) ^ a)⁻¹ := Real.rpow_neg heuclideanDist.le a
    rw [hneg, div_eq_mul_inv]
    congr 1
    exact mul_comm _ _

/-- At `p = 2`, the Euclidean `W^{s,p}` seminorm on an origin cube is exactly
the physical centered-cube Euclidean `H^s` seminorm. -/
theorem cubeEuclideanWspESeminorm_originCube_two_eq_centeredCubeEuclideanHsESeminorm
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    cubeEuclideanWspESeminorm (originCube d m) s FiniteLpExponent.two F =
      centeredCubeEuclideanHsESeminorm s F := by
  rw [cubeEuclideanWspESeminorm_eq_lintegral]
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  change (∫⁻ z, ‖cubeEuclideanWspKernel s FiniteLpExponent.two F z‖ₑ ^ (2 : ℝ)
      ∂Gagliardo.gagliardoCubeMeasure (originCube d m)) ^ (1 / (2 : ℝ)) =
    centeredCubeEuclideanHsESeminorm s F
  rw [show Gagliardo.gagliardoCubeMeasure (originCube d m) =
      centeredCubeEuclideanHsProductMeasure d m by
    exact (centeredCubeEuclideanHsProductMeasure_eq_gagliardoCubeMeasure d m).symm]
  simp_rw [cubeEuclideanWspKernel_two_enorm_rpow_eq_centeredCubeEuclideanHsIntegrand]
  change (∫⁻ z, centeredCubeEuclideanHsIntegrand s F z
      ∂centeredCubeEuclideanHsProductMeasure d m) ^ (1 / (2 : ℝ)) =
    (∫⁻ z, centeredCubeEuclideanHsIntegrand s F z
      ∂centeredCubeEuclideanHsProductMeasure d m) ^ ((2 : ℝ)⁻¹)
  ring_nf

private theorem cubeEuclideanWsp_originCube_two_l2_eq {d : ℕ} (m : ℤ)
    (F : CenteredCubeEuclideanL2Field d m) :
    (cubeBoundedMeasurableDomain (originCube d m)).normalizedEuclideanLpENorm
        FiniteLpExponent.two.exponent F =
      (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  simp only [FiniteLpExponent.two_exponent]
  rfl

private theorem cubeEuclideanWspFullENorm_originCube_two_eq_l2Combination
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    cubeEuclideanWspFullENorm (originCube d m) s FiniteLpExponent.two F =
      ((exactOverlapRootWeight (originCube d m) s.1 *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ (2 : ℝ) +
        (centeredCubeEuclideanHsESeminorm s F) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  unfold cubeEuclideanWspFullENorm
  rw [cubeEuclideanWspScalePowerWeight_originCube_two,
    cubeEuclideanWsp_originCube_two_l2_eq,
    cubeEuclideanWspESeminorm_originCube_two_eq_centeredCubeEuclideanHsESeminorm]
  norm_num only [FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ zero_le_two]

private theorem l2Combination_le_add (a b : ℝ≥0∞) :
    (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ a + b := by
  calc
    (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤
        ((a + b) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow
        (ENNReal.add_rpow_le_rpow_add (p := (2 : ℝ)) a b (by norm_num))
        (by norm_num)
    _ = a + b := by
      rw [← ENNReal.rpow_mul]
      norm_num

private theorem add_le_two_mul_l2Combination (a b : ℝ≥0∞) :
    a + b ≤ 2 * (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have ha_sq : a ^ (2 : ℝ) ≤ a ^ (2 : ℝ) + b ^ (2 : ℝ) := le_add_right le_rfl
  have hb_sq : b ^ (2 : ℝ) ≤ a ^ (2 : ℝ) + b ^ (2 : ℝ) := le_add_left le_rfl
  have ha : a ≤ (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    calc
      a = (a ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow ha_sq (by norm_num)
  have hb : b ≤ (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    calc
      b = (b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow hb_sq (by norm_num)
  rw [show (2 : ℝ≥0∞) * (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) +
        (a ^ (2 : ℝ) + b ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) by ring]
  exact add_le_add ha hb

/-- The power-sum Euclidean `W^{s,2}` full norm and the additive physical
centered-cube Euclidean `H^s` full norm are uniformly equivalent. -/
theorem exists_centeredCubeEuclideanPowerFullENorm_two_equivalence
    (d : ℕ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (s : FractionalOrder)
        (F : CenteredCubeEuclideanL2Field d m),
        cubeEuclideanWspFullENorm (originCube d m) s
            FiniteLpExponent.two F ≤
          C * centeredCubeEuclideanHsFullENorm s F ∧
        centeredCubeEuclideanHsFullENorm s F ≤
          C * cubeEuclideanWspFullENorm (originCube d m) s
            FiniteLpExponent.two F := by
  refine ⟨2, by norm_num, ?_⟩
  intro m s F
  let A : ℝ≥0∞ := exactOverlapRootWeight (originCube d m) s.1 *
    (centeredCubeDomain d m).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let B : ℝ≥0∞ := centeredCubeEuclideanHsESeminorm s F
  have hW : cubeEuclideanWspFullENorm (originCube d m) s
      FiniteLpExponent.two F =
      (A ^ (2 : ℝ) + B ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa only [A, B] using cubeEuclideanWspFullENorm_originCube_two_eq_l2Combination s F
  have hH : centeredCubeEuclideanHsFullENorm s F = A + B := by
    rfl
  constructor
  · rw [hW, hH]
    calc
      (A ^ (2 : ℝ) + B ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ A + B :=
        l2Combination_le_add A B
      _ ≤ 2 * (A + B) := by
        simpa [mul_comm] using
          (mul_le_mul_left (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (A + B))
  · rw [hW, hH]
    exact add_le_two_mul_l2Combination A B

end
