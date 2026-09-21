/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import LeanPool.LiCriterion.Lc.LiCriterion.Basic
import LeanPool.LiCriterion.Hadamard.OrderOne.SummabilityMultiplicity

/-!
# Hadamard Summability Bridge

This file builds the clean bridge from Hadamard order-`≤ 1` hypotheses for `riemannXi`
to the genus-one summability statements used by the Li-criterion development.
-/

open Complex
open scoped Topology

namespace LiCriterion

/-- The nontrivial zeros of `ζ` viewed as a `Hadamard.ZeroSet` for `riemannXi`. -/
noncomputable def xiZeroSet : Hadamard.ZeroSet riemannXi where
  Zero := NontrivialZero
  z := fun ρ => ρ.val
  isZero := by
    intro ρ
    exact (xi_zeros_are_nontrivial_zeros (s := ρ.val)).2 ⟨ρ, rfl⟩

/-- Genus-1 summability from the order-`≤ 1` Hadamard hypotheses for `riemannXi`.

This is the clean replacement path for the old zero-counting bridge: use the multiplicity-aware
Hadamard summability theorem and then compare termwise with the unweighted series, noting that every
zero has multiplicity at least `1`. -/
theorem xi_weighted_genus_one_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    Summable (fun ρ : NontrivialZero =>
      (analyticOrderNatAt riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  let Z : Hadamard.ZeroSet riemannXi := xiZeroSet
  have : Countable Z.Zero := by
    dsimp [Z, xiZeroSet]
    infer_instance
  have h_zeros_only : ∀ s : ℂ, riemannXi s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ := by
    intro s
    simpa [Z, xiZeroSet] using (xi_zeros_are_nontrivial_zeros (s := s))
  have h_inj : Function.Injective Z.z := by
    intro ρ ρ' h
    exact Subtype.ext h
  have h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0 := by
    intro ρ
    simpa [Z, xiZeroSet] using ρ.ne_zero
  have hsum_mult :
      Summable
        (fun ρ : Z.Zero => (analyticOrderNatAt riemannXi (Z.z ρ) : ℝ) / ‖Z.z ρ‖ ^ 2) :=
    Hadamard.OrderOne.summable_analyticOrderNatAt_div_norm_sq_of_order_le_one
      (f := riemannXi) (hf_entire := xi_entire) (hf_finite := hfinite) (hf_order_le := horder)
      (Z := Z) (h_zeros_only := h_zeros_only) (h_inj := h_inj) (h_z_ne_zero := h_z_ne_zero)
  simpa [Z, xiZeroSet] using hsum_mult

theorem xi_genus_one_of_hadamard_order_one
    (hfinite : Hadamard.hasFiniteOrder riemannXi)
    (horder : Hadamard.order riemannXi ≤ 1) :
    Summable (fun (ρ : NontrivialZero) => (1 : ℝ) / ‖ρ.val‖ ^ 2) := by
  exact genus_one_of_weighted_genus (xi_weighted_genus_one_of_hadamard_order_one hfinite horder)

end LiCriterion
