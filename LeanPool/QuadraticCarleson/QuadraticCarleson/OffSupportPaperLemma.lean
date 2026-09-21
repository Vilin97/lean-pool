/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleOperatorAction
import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportOscillatoryAllOrders

/-!
# The paper's off-support wave-packet lemma

Both displayed estimates are stated directly for the canonical principal-value
operator applied to the fixed normalized packet. The approximation estimate
includes zero modulation. The rapid-decay estimate applies to nonzero modulation,
the natural domain of its inverse powers of the modulation parameter.
-/

open Set
open scoped SchwartzMap

namespace QuadraticCarleson


/-- The first branch of the paper's lemma, including the literal maximum in
its error bound, for the genuine principal-value action. -/
theorem quadraticHilbertSchwartz_wavePacket_sub_main_le {lam s t x : ℝ}
    (ht : 0 < t) (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖quadraticHilbertSchwartz lam (wavePacketSchwartz s t ht) x -
      phase (lam * (x - s) ^ 2) / ((x - s : ℝ) : ℂ)‖ ≤
        7 * max (|lam| * t) (t / |x - s| ^ 2) := by
  rw [quadraticHilbertSchwartz_wavePacket_eq_offSupportKernelAction ht hx]
  exact offSupportKernelAction_sub_main_le ht hx

/-- The second branch at every order and both signs of nonzero modulation,
with a constant independent of modulation, center, length, and evaluation point. -/
theorem quadraticHilbertSchwartz_wavePacket_norm_le_all_orders (k : ℕ)
    {lam s t x : ℝ} (hlam : lam ≠ 0) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖quadraticHilbertSchwartz lam (wavePacketSchwartz s t ht) x‖ ≤
      offSupportDecayConstant k 0 1 /
        (|lam| ^ k * t ^ k * |x - s| ^ (k + 1)) := by
  rw [quadraticHilbertSchwartz_wavePacket_eq_offSupportKernelAction ht hx]
  simpa only [offSupportOscillatoryAction_eq_offSupportKernelAction] using
    offSupportOscillatoryAction_norm_le_all_orders k hlam ht hx

/-- A direct entry point for both displayed estimates in the paper's first
lemma of Section 3. The constants are uniform in every interval and modulation;
the rapid-decay constant may depend only on the order and the fixed initial bump.
The first estimate also holds at zero modulation. -/
theorem offSupportPaperLemma (k : ℕ) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ (lam s t x : ℝ) (ht : 0 < t),
      x ∉ Icc (s - t / 2) (s + t / 2) →
        (‖quadraticHilbertSchwartz lam (wavePacketSchwartz s t ht) x -
          phase (lam * (x - s) ^ 2) / ((x - s : ℝ) : ℂ)‖ ≤
            7 * max (|lam| * t) (t / |x - s| ^ 2)) ∧
        (lam ≠ 0 → ‖quadraticHilbertSchwartz lam (wavePacketSchwartz s t ht) x‖ ≤
          Ck / (|lam| ^ k * t ^ k * |x - s| ^ (k + 1))) := by
  refine ⟨offSupportDecayConstant k 0 1, offSupportDecayConstant_nonneg k 0 1, ?_⟩
  intro lam s t x ht hx
  exact ⟨quadraticHilbertSchwartz_wavePacket_sub_main_le ht hx,
    fun hlam ↦ quadraticHilbertSchwartz_wavePacket_norm_le_all_orders k hlam ht hx⟩


end QuadraticCarleson
