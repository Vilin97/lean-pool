/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Archimedean
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

open Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup

open scoped MatrixGroups Real

variable {Γ : Subgroup SL(2, ℤ)}

namespace Subgroup
/-!
## Width of a subgroup

These results are in the `Subgroup` namespace to enable dot-notation, although they are specific
to the case of subgroups of the modular group.
-/
variable (Γ)

/-- The width of the cusp `∞` for a subgroup of `SL(2, ℤ)`, i.e. the least `n > 0` such that
`[1, n; 0, 1] ∈ Γ`. -/
noncomputable def width : ℕ := Subgroup.relIndex Γ (.zpowers ModularGroup.T)

lemma width_ne_zero [Γ.FiniteIndex] : Γ.width ≠ 0 :=
  FiniteIndex.index_ne_zero

lemma T_pow_width_mem : T ^ Γ.width ∈ Γ :=
  (Γ.subgroupOf <| .zpowers T).pow_index_mem ⟨_, mem_zpowers _⟩

/-- The integers `n` such that `[1, n; 0, 1] ∈ Γ` are precisely the multiples of `Γ.width`. -/
lemma T_zpow_mem_iff {n : ℤ} : T ^ n ∈ Γ ↔ ↑Γ.width ∣ n := by
  let A : AddSubgroup ℤ := (Γ.comap (zpowersHom _ T)).toAddSubgroup'
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic A
  have h₁ : (Γ.comap (zpowersHom _ T)).index = Γ.width := Γ.index_comap _
  have h₂ : Γ.width = A.index := by simpa [A, h₁] using A.index_toSubgroup
  rw [h₂, (by rfl : T ^ n ∈ Γ ↔ n ∈ A), hm, ← AddSubgroup.zmultiples_eq_closure,
    Int.mem_zmultiples_iff, Int.index_zmultiples, Int.natAbs_dvd]

/-- The integers `n` such that `[1, n; 0, 1] ∈ Γ` are precisely the multiples of `Γ.width`. -/
lemma T_pow_mem_iff (n : ℕ) : T ^ n ∈ Γ ↔ Γ.width ∣ n := by
  simpa [Int.natCast_dvd_natCast] using Γ.T_zpow_mem_iff (n := n)

variable (N : ℕ)

@[simp] lemma Gamma_width : Γ(N).width = N := by
  simp [← Nat.dvd_right_iff_eq, ← Subgroup.T_pow_mem_iff, ← zpow_natCast,
    ModularGroup.coe_T_zpow, ZMod.natCast_eq_zero_iff]

lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) : T ^ M ∈ Gamma N.natAbs := by
  rwa [Subgroup.T_zpow_mem_iff, Gamma_width, Int.natAbs_dvd]

end Subgroup
