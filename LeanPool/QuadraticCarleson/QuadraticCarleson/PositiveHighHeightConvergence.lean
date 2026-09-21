/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveHighHeightTail

/-!
# Genuine convergence of the high complex series

The measurable majorant is finite almost everywhere for every L² input.
Outside one null set, the strict high-height series converges absolutely for
every real modulation simultaneously. Thus the tail definitions do not rely
on the default value of a nonsummable complex `tsum`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Function

namespace QuadraticCarleson
namespace PositiveHighHeightEstimate

theorem memLp_highHeightMajorant (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    MemLp (highHeightMajorant B b) 2 := by
  refine ⟨(measurable_highHeightMajorant B hb).aestronglyMeasurable,
    (highHeightMajorant_eLpNorm_le B hb).trans_lt ?_⟩
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top highHeightTailConstant_lt_top (by finiteness)) hb.eLpNorm_lt_top

theorem ae_highHeightMajorant_lt_top (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    ∀ᵐ x, highHeightMajorant B b x < ∞ := by
  have hnorm := (memLp_highHeightMajorant B hb).eLpNorm_lt_top
  have hsq : (∫⁻ x, highHeightMajorant B b x ^ 2) < ∞ := by
    simpa only [eLpNorm_two_sq_lintegral, enorm_eq_self] using ENNReal.pow_lt_top (n := 2) hnorm
  have ha := ae_lt_top ((measurable_highHeightMajorant B hb).pow_const 2) hsq.ne
  filter_upwards [ha] with x hx
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx

/-- Absolute convergence holds outside one null set simultaneously for all
nonzero real modulation parameters. -/
theorem ae_summable_norm_highHeightIntegrals (B : ℕ) {b : ℝ → ℂ} (hb : MemLp b 2) :
    ∀ᵐ x, ∀ lam : {lam : ℝ // lam ≠ 0}, Summable (fun n : ℕ ↦
      ‖∫ t, b (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.val (B + n + 1) lam.property) t : ℂ) *
          phase (lam.val * t ^ 2)‖) := by
  filter_upwards [ae_highHeightMajorant_lt_top B hb] with x hx
  intro lam
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  apply ne_of_lt
  apply lt_of_le_of_lt ?_ hx
  apply ENNReal.tsum_le_tsum
  intro n
  exact le_iSup (fun μ : {μ : ℝ // μ ≠ 0} ↦ ‖∫ t, b (x - t) *
    (dyadicPsi (oscillatoryScaleIndex μ.val (B + n + 1) μ.property) t : ℂ) *
      phase (μ.val * t ^ 2)‖ₑ) lam

/-- For the actual level atoms, one exceptional null set works for every
magnitude level and every real modulation at once. -/
theorem ae_summable_norm_highHeightLevelAtomIntegrals
    {ι : Type*} [Countable ι] {A : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k)
    (B : ℕ → ℕ) {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    ∀ᵐ x, ∀ k : ℕ, ∀ lam : {lam : ℝ // lam ≠ 0}, Summable (fun n : ℕ ↦
      ‖∫ t, disjointLevelAtomSum A f k z R (x - t) *
        (dyadicPsi (oscillatoryScaleIndex lam.val (B k + n + 1) lam.property) t : ℂ) *
          phase (lam.val * t ^ 2)‖) := by
  apply ae_all_iff.mpr
  intro k
  exact ae_summable_norm_highHeightIntegrals (B k)
    (memLp_disjointLevelAtomSum hf hfi (hA k) z R hR hdisj)

end PositiveHighHeightEstimate
end QuadraticCarleson
