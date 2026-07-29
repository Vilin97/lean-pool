/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Finite Zero Sum Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

open Classical in
theorem norm_finsum_div_sub_le_finsum_div
    {D : ℂ → ℤ} (hfin : D.support.Finite)
    (hD : ∀ u, 0 ≤ D u) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖) :
    ‖∑ᶠ u, (D u : ℂ) / (z - u)‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / δ := by
  let S := hfin.toFinset
  have hsupp : D.support ⊆ S := fun u hu ↦ hfin.mem_toFinset.mpr hu
  have hterm :
      (fun u ↦ (D u : ℂ) / (z - u)).support ⊆ S := by
    intro u hu
    simp_all
  have hsumC :
      ∑ᶠ u, (D u : ℂ) / (z - u) =
        ∑ u ∈ S, (D u : ℂ) / (z - u) :=
    finsum_eq_sum_of_support_subset _ hterm
  have hsumZ : ∑ᶠ u, D u = ∑ u ∈ S, D u :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsumC, hsumZ]
  calc
    ‖∑ u ∈ S, (D u : ℂ) / (z - u)‖ ≤
        ∑ u ∈ S, ‖(D u : ℂ) / (z - u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (D u : ℝ) / δ := by
      apply Finset.sum_le_sum
      intro u hu
      have huD : 0 ≤ (D u : ℝ) := by simp_all
      by_cases hDu : D u = 0
      · simp [hDu]
      · rw [norm_div, norm_intCast, abs_of_nonneg huD]
        exact div_le_div₀ huD le_rfl hδ
          (hsep u (Function.mem_support.mpr hDu))
    _ = ((∑ u ∈ S, D u : ℤ) : ℝ) / δ := by
      rw [Int.cast_sum]
      rw [Finset.sum_div]

end NumberField.Odlyzko
