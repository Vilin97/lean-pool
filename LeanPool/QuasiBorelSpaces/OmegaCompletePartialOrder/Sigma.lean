/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.Data.Sigma.Order
import Mathlib.Order.OmegaCompletePartialOrder
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sigma

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Sigma

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Sigma`.
-/


namespace OmegaCompletePartialOrder.Sigma

variable {I : Type*} {P : I → Type*} [∀ i, OmegaCompletePartialOrder (P i)]

instance instSigmaLeanPool : OmegaCompletePartialOrder ((i : I) × P i) where
  ωSup c := (Chain.Sigma.distrib c).map id fun _ ↦ ωSup
  le_ωSup c i := by
    cases c using Chain.Sigma.distrib_cases
    rename_i j d
    change (⟨j, d i⟩ : Sigma P) ≤ Sigma.map id (fun _ ↦ ωSup) ⟨j, d⟩
    simp only [Sigma.map_mk, id_eq, Sigma.mk_le_mk_iff]
    exact le_ωSup _ _
  ωSup_le := by
    rintro c ⟨x, y⟩ h
    cases c using Chain.Sigma.distrib_cases
    rename_i d
    have h0 := h 0
    rw [Chain.Sigma.inj_coe] at h0
    cases h0
    change Sigma.map id (fun _ ↦ ωSup) ⟨x, d⟩ ≤ ⟨x, y⟩
    simp only [Sigma.map_mk, id_eq, Sigma.mk_le_mk_iff]
    refine ωSup_le _ _ ?_
    intro i
    have := h i
    rw [Chain.Sigma.inj_coe] at this
    exact (Sigma.mk_le_mk_iff.mp this)

@[simp]
lemma ωSup_inj {i} (c : Chain (P i)) : ωSup (Chain.Sigma.inj c) = ⟨i, ωSup c⟩ := rfl

end OmegaCompletePartialOrder.Sigma
