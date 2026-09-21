/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightTail
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# The high contribution summed over magnitude levels

The maximal complex tails are the paper's actual high terms. A measurable
majorant permits a level-set bound without assuming that their unrestricted
real-parameter supremum is measurable. All fixed-height bounds are supplied
by the proved quadratic theorem.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

open CalderonZygmundLevelAtoms PositiveLevelIntegration

noncomputable def paperHighContribution (B : ℕ → ℕ) (b : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, paperHighHeightTail (B k) (b k) x

noncomputable def highContributionMajorant (B : ℕ → ℕ) (b : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, highHeightMajorant (B k) (b k) x

theorem paperHighContribution_le_majorant (B : ℕ → ℕ) (b : ℕ → ℝ → ℂ) (x : ℝ) :
    paperHighContribution B b x ≤ highContributionMajorant B b x :=
  ENNReal.tsum_le_tsum (fun k ↦ paperHighHeightTail_le_majorant (B k) (b k) x)

theorem measurable_highContributionMajorant
    (B : ℕ → ℕ) {b : ℕ → ℝ → ℂ} (hb : ∀ k, MemLp (b k) 2) :
    Measurable (highContributionMajorant B b) :=
  Measurable.tsum (fun k ↦ measurable_highHeightMajorant (B k) (hb k))

theorem highContributionMajorant_eLpNorm_le
    (B : ℕ → ℕ) {b : ℕ → ℝ → ℂ} (hb : ∀ k, MemLp (b k) 2) :
    eLpNorm (highContributionMajorant B b) 2 ≤
      highHeightTailConstant * ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) * eLpNorm (b k) 2 := by
  have hp (k : ℕ) : eLpNorm (highHeightMajorant (B k) (b k)) 2 ≤
      highHeightTailConstant * ENNReal.ofReal ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) *
        eLpNorm (b k) 2 := highHeightMajorant_eLpNorm_le (B k) (hb k)
  have hs := ENNReal.tsum_le_tsum hp
  simp_rw [mul_assoc] at hs
  rw [ENNReal.tsum_mul_left] at hs
  exact (eLpNorm_tsum_two_le (fun k ↦ highHeightMajorant (B k) (b k))
    (fun k ↦ measurable_highHeightMajorant (B k) (hb k))).trans hs

/-- The countable sum of actual high tails is measurable for L² inputs. -/
theorem measurable_paperHighContribution
    (B : ℕ → ℕ) {b : ℕ → ℝ → ℂ} (hb : ∀ k, MemLp (b k) 2) :
    Measurable (paperHighContribution B b) :=
  Measurable.tsum (fun k ↦ measurable_paperHighHeightTail (B k) (hb k))

theorem paperHighContribution_eLpNorm_le
    (B : ℕ → ℕ) {b : ℕ → ℝ → ℂ} (hb : ∀ k, MemLp (b k) 2) :
    eLpNorm (paperHighContribution B b) 2 ≤
      highHeightTailConstant * ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) * eLpNorm (b k) 2 := by
  apply (eLpNorm_mono_enorm (f := paperHighContribution B b) (g := highContributionMajorant B b)
    (measurable_paperHighContribution B hb).aestronglyMeasurable
    (fun x ↦ paperHighContribution_le_majorant B b x)).trans
  exact highContributionMajorant_eLpNorm_le B hb

/-- Chebyshev for the measurable majorant gives a genuine outer-measure
estimate for the paper's high level set. -/
theorem paperHighContribution_levelSet_le
    (B : ℕ → ℕ) {b : ℕ → ℝ → ℂ} (hb : ∀ k, MemLp (b k) 2) :
    volume {x | 1 < paperHighContribution B b x} ≤
      (highHeightTailConstant * ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) * eLpNorm (b k) 2) ^ 2 := by
  have hset : volume {x | 1 < paperHighContribution B b x} ≤
      volume {x | 1 ≤ highContributionMajorant B b x} := by
    apply measure_mono
    intro x hx
    exact (hx.trans_le (paperHighContribution_le_majorant B b x)).le
  have hcheb : volume {x | 1 ≤ highContributionMajorant B b x} ≤
      eLpNorm (highContributionMajorant B b) 2 ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, enorm_eq_self, ENNReal.one_rpow,
      one_mul, one_pow, ENNReal.rpow_two] using mul_meas_ge_le_pow_eLpNorm' volume
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (f := highContributionMajorant B b) (1 : ℝ≥0∞)
  exact hset.trans (hcheb.trans
    (pow_le_pow_left₀ bot_le (highContributionMajorant_eLpNorm_le B hb) 2))

theorem disjointLevelAtomSum_eLpNorm_le {ι : Type*} [Countable ι]
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    eLpNorm (disjointLevelAtomSum A f k z R) 2 ≤
      (ENNReal.ofReal (4 * A k) * magnitudeLevelL1Mass volume A f k) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_disjointLevelAtomSum (A := A) hf k z R).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (disjointLevelAtomSum_sq_lintegral_le hf hAk z R hR hdisj)
    (by norm_num)

/-- The full countable high contribution for the actual level atoms in an
explicit countable disjoint interval family, before numerical optimization. -/
theorem paperHighContribution_disjointLevelAtoms_levelSet_le
    {ι : Type*} [Countable ι] {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k)
    (B : ℕ → ℕ) {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    volume {x | 1 < paperHighContribution B (fun k ↦ disjointLevelAtomSum A f k z R) x} ≤
      (highHeightTailConstant * ∑' k : ℕ,
        ENNReal.ofReal ((2 : ℝ) ^ (-((B k : ℕ) : ℝ) / 10)) *
          (ENNReal.ofReal (4 * A k) * magnitudeLevelL1Mass volume A f k) ^ (1 / 2 : ℝ)) ^ 2 := by
  apply (paperHighContribution_levelSet_le B
    (fun k ↦ memLp_disjointLevelAtomSum hf hfi (hA k) z R hR hdisj)).trans
  apply pow_le_pow_left₀ bot_le ?_ 2
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro k
  exact mul_le_mul' le_rfl (disjointLevelAtomSum_eLpNorm_le hf (hA k) z R hR hdisj)

end PositiveHighHeightEstimate
end QuadraticCarleson
