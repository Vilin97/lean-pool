/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities
import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

noncomputable section

open ModularForm UpperHalfPlane Matrix MatrixGroups ModularGroup

namespace SlashInvariantFormClass

variable {Γ : Subgroup SL(2, ℤ)} {F : Type*} (f : F) (k : ℤ)
  [FunLike F ℍ ℂ] [hF : SlashInvariantFormClass F Γ k] {n : ℤ}

include hF -- necessary because `k` is not inferrable from the statements

theorem vAdd_width_periodic (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f ((n : ℝ) +ᵥ τ) = f τ := by
  rw [← modular_T_zpow_smul τ, SlashInvariantForm.slash_action_eqn_SL'' (k := k) f
    (Γ.T_zpow_mem_iff.mpr hn)]
  have hdenom : denom (SpecialLinearGroup.toGL ((SpecialLinearGroup.map (Int.castRingHom ℝ))
      (ModularGroup.T ^ n))) (↑τ : ℂ) = 1 := by
    simp only [denom, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.map_apply_coe, coe_T_zpow, RingHom.mapMatrix_apply, Int.coe_castRingHom,
      map_apply, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_zero,
      Complex.ofReal_zero, zero_mul, Int.cast_one, Complex.ofReal_one, zero_add]
  rw [hdenom]; simp

theorem T_zpow_width_invariant (hn : ↑Γ.width ∣ n) (τ : ℍ) :
    f (ModularGroup.T ^ n • τ) = f τ := by
  simpa [-sl_moeb, modular_T_zpow_smul] using vAdd_width_periodic f k hn τ

end SlashInvariantFormClass
