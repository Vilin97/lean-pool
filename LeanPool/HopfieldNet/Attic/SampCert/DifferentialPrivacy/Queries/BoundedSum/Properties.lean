/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes
import Init.Data.Int.Order
import LeanPool.HopfieldNet.SampCert.DifferentialPrivacy.Queries.BoundedSum.Code

/-!
# ``privNoisedBoundedSum`` Properties

This file proves abstract differential privacy for ``privNoisedBoundedSum``.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]

/--
Sensitivity of the bounded sum is equal to the bound.
-/
theorem exactBoundedSum_sensitivity (U : ℕ+) : sensitivity (exactBoundedSum U) U := by
  simp [sensitivity, exactBoundedSum]
  intros l₁ l₂ H
  have A : ∀ n : ℕ, (@min ℤ instMin (n : ℤ) (U : ℤ) = n) ∨ (@min ℤ instMin n U = U) := by
    intro n
    simp
    exact Nat.le_total n ↑U
  cases H
  · rename_i l l' n h1 h2
    subst h1 h2
    simp
    cases A n
    · rename_i h
      rw [h]
      simp at *
      trivial
    · rename_i h
      rw [h]
      simp
  · rename_i l n l' h1 h2
    subst h1 h2
    simp
    cases A n
    · rename_i h
      rw [h]
      simp at *
      trivial
    · rename_i h
      rw [h]
      simp
  · rename_i l n l' m h1 h2
    subst h1 h2
    simp
    cases A n
    · rename_i h
      cases A m
      · rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le h h'
      · rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le h le_rfl
    · rename_i h
      cases A m
      · rename_i h'
        rw [h, h']
        simp at *
        apply Int.natAbs_coe_sub_coe_le_of_le le_rfl h'
      · rename_i h'
        rw [h, h']
        simp at *

/--
The noised bounded sum satisfies the DP property of the DP system.
-/
@[simp]
theorem privNoisedBoundedSum_DP (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedBoundedSum U ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  apply dps.noise_prop
  apply exactBoundedSum_sensitivity

end SLang
