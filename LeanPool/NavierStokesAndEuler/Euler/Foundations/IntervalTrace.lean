/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.TerminalEnergy
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity.Finset

/-!
# Interval Trace
-/

@[expose] public section

noncomputable section

namespace EulerIntervalTrace

open Set MeasureTheory EulerTerminalEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_sub_sq_le_interval_energy (f v : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ^ 2 ≤ (b - a) * ∫ r in a..b, ‖v r‖ ^ 2 := by
  have hvi : IntervalIntegrable (fun r => ‖v r‖ ^ 2) volume a b :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hab
  have hpos : 0 ≤ ∫ r in a..b, ‖v r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun r _ => sq_nonneg _)
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (le_of_lt (lt_of_not_ge hst))
    simpa only [norm_sub_rev] using h
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hf r (hsub ((uIcc_of_le hst) ▸ hr)))
    ((hv.mono hsub).intervalIntegrable_of_Icc hst)
  have hq := norm_integral_sq_le_length_mul v hst (hv.mono hsub)
  rw [he] at hq
  have hi := intervalIntegral.integral_mono_interval hs.1 hst ht.2
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖v r‖)) hvi
  exact hq.trans ((mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hst)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2] : t - s ≤ b - a) hpos))

/-- Point evaluation on an interval is bounded by the actual zeroth and first derivative energies.
-/
theorem pointwise_H1_trace (f v : ℝ → E) (a b : ℝ) (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ 2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfi := (hc.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  let V := ∫ s in a..b, ‖v s‖ ^ 2
  have hp (s : ℝ) (hs : s ∈ Icc a b) :
      ‖f t‖ ^ 2 ≤ 2 * ‖f s‖ ^ 2 + 2 * (b - a) * V := by
    have hd := norm_sub_sq_le_interval_energy f v a b hab.le hv hf s t hs ht
    have hn : ‖f t‖ ≤ ‖f t - f s‖ + ‖f s‖ := by
      calc
        _ = ‖(f t - f s) + f s‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp [V]
    nlinarith [norm_nonneg (f t), norm_nonneg (f s), norm_nonneg (f t - f s),
      sq_nonneg (‖f t - f s‖ - ‖f s‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (intervalIntegrable_const (c := ‖f t‖ ^ 2))
    ((hfi.const_mul 2).add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hfi.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hlen : 0 < b - a := sub_pos.mpr hab
  apply (mul_le_mul_iff_right₀ hlen).mp
  dsimp [V] at hi ⊢
  have he : (b - a) * (2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) =
      2 * (∫ s in a..b, ‖f s‖ ^ 2) + (b - a) *
        (2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) := by
    field_simp [hlen.ne']
  rw [he]
  exact hi

end EulerIntervalTrace
