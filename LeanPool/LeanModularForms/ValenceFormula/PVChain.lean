/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.PVChain.Assembly
import LeanPool.LeanModularForms.ValenceFormula.PVChain.Assembly.ResidueSide

/-!
# PV Chain: Residue Side and Modular Side

Bridge theorems connecting the ε-truncated integral of `f'/f`
to the generalized winding number sum and the modular transformation.

The key identity `pv_chain_identity` follows by uniqueness of limits:
both sides are limits of the same ε-truncated integral, so they are equal.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf in
/-- The PV chain identity: equate residue and modular sides via
uniqueness of limits, then cancel `2πi`. -/
theorem pv_chain_identity (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      ∑ s ∈ S, generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ) *
        (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  obtain ⟨H₁, hH₁, h_res⟩ := cpv_residue_side_tendsto f hf S hS hS_complete
  obtain ⟨H₂, hH₂, h_mod⟩ := cpv_modular_side_tendsto f hf S hS hS_complete
  refine ⟨max H₁ H₂, lt_of_lt_of_le hH₁ (le_max_left _ _), fun {H} hH => ?_⟩
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  have h_eq :
      2 * ↑Real.pi * I *
        ∑ s ∈ S, generalizedWindingNumber' (fdBoundaryH H) 0 5 (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
    tendsto_nhds_unique
      (h_res (le_trans (le_max_left _ _) hH))
      (h_mod (le_trans (le_max_right _ _) hH))
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]
  rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) =
    2 * ↑Real.pi * I * (-((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) from by ring] at h_eq
  exact mul_left_cancel₀ hpi h_eq

end
