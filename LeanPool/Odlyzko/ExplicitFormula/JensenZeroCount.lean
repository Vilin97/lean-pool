/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Jensen Zero Count

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

open Classical in
theorem card_le_finsum_of_subset_support_of_nonneg
    {α : Type*} (D : α → ℤ)
    (hfin : Function.support D |>.Finite)
    (S : Finset α) (hS : (S : Set α) ⊆ Function.support D)
    (hD : ∀ x, 0 ≤ D x) :
    (S.card : ℝ) ≤ ((∑ᶠ x, D x : ℤ) : ℝ) := by
  let F := hfin.toFinset
  have hSF : S ⊆ F := by
    intro x hx
    exact hfin.mem_toFinset.mpr (hS hx)
  calc
    (S.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_le_card hSF
    _ = ∑ x ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ F, (D x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxD : D x ≠ 0 := Function.mem_support.mp
        (hfin.mem_toFinset.mp hx)
      have hxnonneg := hD x
      exact_mod_cast (show (1 : ℤ) ≤ D x by lia)
    _ = ((∑ᶠ x, D x : ℤ) : ℝ) := by
      rw [finsum_eq_sum_of_support_subset D (by
        intro x hx
        exact hfin.mem_toFinset.mpr hx)]
      norm_cast

open Classical in
theorem AnalyticOnNhd.card_zeros_le
    {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (hr : 0 < |r|)
    (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |R|))
    (hc : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ M)
    (S : Finset ℂ)
    (hSsupport : ∀ z ∈ S,
      z ∈ Function.support
        (MeromorphicOn.divisor f (Metric.closedBall c |r|))) :
    (S.card : ℝ) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  let D : ℂ → ℤ := fun z ↦
    MeromorphicOn.divisor f (Metric.closedBall c |r|) z
  have hDnonneg (z : ℂ) : 0 ≤ D z := by
    dsimp [D]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono (Metric.closedBall_subset_closedBall hrR.le)) z
  have hDfin : (Function.support D).Finite := by
    exact (MeromorphicOn.divisor f (Metric.closedBall c |r|)).finiteSupport
      (isCompact_closedBall c |r|)
  have hSsupport' : (S : Set ℂ) ⊆ Function.support D := by grind
  refine
    (card_le_finsum_of_subset_support_of_nonneg D hDfin S hSsupport' hDnonneg).trans ?_
  simpa [D] using hf.sum_divisor_le hr hrR hM hc f_bound

end NumberField.Odlyzko
