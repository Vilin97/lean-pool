/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightSummation

/-!
# Weighted Cauchy--Schwarz for the actual high contribution

The free positive weight can be chosen as `B_k` for the full operator, or as
`log₁(B_k)²` for the lacunary optimization. This is the last analytic bound
in the paper's high-height argument, with the fixed exponent `β = 1/10`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration

theorem ennreal_sqrt_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_mul_natCast]
  norm_num

theorem ennreal_sq_sqrt (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast_mul]
  norm_num

theorem tsum_sqrt_mul_sq_le (a b : ℕ → ℝ≥0∞) :
    (∑' k, a k ^ (1 / 2 : ℝ) * b k ^ (1 / 2 : ℝ)) ^ 2 ≤
      (∑' k, a k) * ∑' k, b k := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq Measure.count
    Real.HolderConjugate.two_two
    (f := fun k ↦ a k ^ (1 / 2 : ℝ)) (g := fun k ↦ b k ^ (1 / 2 : ℝ))
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two, ennreal_sqrt_sq, lintegral_count] at h
  have hp := pow_le_pow_left₀ bot_le h 2
  simpa only [mul_pow, ennreal_sqrt_sq] using hp

theorem weighted_level_factor (A d W : ℝ) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hW : 0 < W) (M : ℝ≥0∞) :
    ENNReal.ofReal d * (ENNReal.ofReal (4 * A) * M) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (4 * A * d ^ 2 / W) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal W * M) ^ (1 / 2 : ℝ) := by
  have hc : ENNReal.ofReal d ^ 2 * ENNReal.ofReal (4 * A) =
      ENNReal.ofReal (4 * A * d ^ 2 / W) * ENNReal.ofReal W := by
    rw [← ENNReal.ofReal_pow hd,
      ← ENNReal.ofReal_mul (sq_nonneg d),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * A * d ^ 2 / W)]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal d ^ 2) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (4 * A) * M) ^ (1 / 2 : ℝ) := by rw [ennreal_sq_sqrt]
    _ = (ENNReal.ofReal d ^ 2 * (ENNReal.ofReal (4 * A) * M)) ^ (1 / 2 : ℝ) :=
      (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
    _ = (ENNReal.ofReal (4 * A * d ^ 2 / W) * (ENNReal.ofReal W * M)) ^ (1 / 2 : ℝ) := by
      rw [← mul_assoc, hc, mul_assoc]
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

theorem weighted_level_sum_sq_le (A d W : ℕ → ℝ) (M : ℕ → ℝ≥0∞)
    (hA : ∀ k, 0 ≤ A k) (hd : ∀ k, 0 ≤ d k) (hW : ∀ k, 0 < W k) :
    (∑' k, ENNReal.ofReal (d k) * (ENNReal.ofReal (4 * A k) * M k) ^ (1 / 2 : ℝ)) ^ 2 ≤
      (∑' k, ENNReal.ofReal (4 * A k * d k ^ 2 / W k)) *
        ∑' k, ENNReal.ofReal (W k) * M k := by
  have hp (k : ℕ) := weighted_level_factor (A k) (d k) (W k) (hA k) (hd k) (hW k) (M k)
  simp_rw [hp]
  exact tsum_sqrt_mul_sq_le _ _

/-- The paper's high level-set estimate for genuine atoms and arbitrary
positive weights, using the proved quadratic decay exponent `1/10`. -/
theorem paperHighContribution_disjointLevelAtoms_weighted_levelSet_le
    {ι : Type*} [Countable ι] {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k)
    (B : ℕ → ℕ) (W : ℕ → ℝ) (hW : ∀ k, 0 < W k)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperHighContribution B (fun k ↦ disjointLevelAtomSum A f k z R) x} ≤
      highHeightTailConstant ^ 2 *
        (∑' k, ENNReal.ofReal (4 * A k *
          (2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 5) / W k)) *
        ∑' k, ENNReal.ofReal (W k) * magnitudeLevelL1Mass volume A f k := by
  apply (paperHighContribution_disjointLevelAtoms_levelSet_le hA B hf hfi z R hR hdisj).trans
  rw [mul_pow, mul_assoc]
  apply mul_le_mul' le_rfl
  have h := weighted_level_sum_sq_le A
    (fun k ↦ (2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) W
    (magnitudeLevelL1Mass volume A f) hA (fun _ ↦ by positivity) hW
  have hp (k : ℕ) : ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) ^ 2 =
      (2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 5) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [hp] using h

end PositiveHighHeightEstimate
end QuadraticCarleson
