/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportWeightedIBP
public import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportOscillatoryConstants

/-!
# Arbitrary-order off-support decay of the quadratic wave packet

This completes the full displayed off-support lemma, not only the two-fold
estimate used by the negative endpoint. The proof iterates integration by parts
in the original packet variable and includes both signs of nonzero modulation.
-/

@[expose] public section

open MeasureTheory Set

namespace QuadraticCarleson


/-- Every weighted packet derivative admits arbitrary-order oscillatory decay. -/
theorem offSupportWeightedAction_norm_le_all_orders (k r q : ℕ) {lam s t x : ℝ}
    (hlam : lam ≠ 0) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportWeightedAction lam r q s t x‖ ≤
      offSupportDecayConstant k r q /
        (|lam| ^ k * t ^ (k + r) * |x - s| ^ (k + q)) := by
  have hd : 0 < |x - s| :=
    lt_of_lt_of_le (half_pos ht) (half_length_le_abs_center ht hx)
  have htd : t ≤ 2 * |x - s| := by
    linarith [half_length_le_abs_center ht hx]
  exact offSupportDecay_bound_of_step
    (fun r q ↦ ‖offSupportWeightedAction lam r q s t x‖)
    (abs_pos.mpr hlam) ht hd htd
    (fun r q ↦ offSupportWeightedAction_norm_le_zero r q ht hx)
    (fun r q ↦ offSupportWeightedAction_norm_le_step r q hlam ht hx) k r q

/-- The full rapid-decay branch of the paper's off-support wave-packet lemma. -/
theorem offSupportOscillatoryAction_norm_le_all_orders (k : ℕ) {lam s t x : ℝ}
    (hlam : lam ≠ 0) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportOscillatoryAction lam s t x‖ ≤
      offSupportDecayConstant k 0 1 / (|lam| ^ k * t ^ k * |x - s| ^ (k + 1)) := by
  simpa only [offSupportWeightedAction, iteratedWavePacketDeriv_zero, pow_one,
    offSupportOscillatoryAction, add_zero] using
    offSupportWeightedAction_norm_le_all_orders k 0 1 hlam ht hx

/-- An explicit universal constant for each order, independent of every
modulation, interval, and off-support evaluation point. -/
theorem offSupportOscillatoryAction_rapid_decay (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam s t x : ℝ), lam ≠ 0 → 0 < t →
      x ∉ Icc (s - t / 2) (s + t / 2) →
        ‖offSupportOscillatoryAction lam s t x‖ ≤
          C / (|lam| ^ k * t ^ k * |x - s| ^ (k + 1)) :=
  ⟨offSupportDecayConstant k 0 1, offSupportDecayConstant_nonneg k 0 1,
    fun _ _ _ _ hlam ht hx ↦ offSupportOscillatoryAction_norm_le_all_orders k hlam ht hx⟩


end QuadraticCarleson
