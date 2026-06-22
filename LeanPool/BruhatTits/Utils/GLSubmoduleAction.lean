/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Utils.Matrix

/-!
# LeanPool.BruhatTits.Utils.GLSubmoduleAction
-/

open Module

variable {K : Type*} [Field K]
variable {R : Subring K}

namespace BruhatTits
open Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scalar_smul_GL_smul (M : Submodule R (ι → K))
    (a : K) (g : GL ι K) : a • g • M = g • a • M := by
  ext x
  simp only [Matrix.GeneralLinearGroup.mem_smul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨a • z, ?_, ?_⟩
    · use z, hz
      rfl
    · simp [Matrix.mulVec_smul]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simp only [DistribSMul.toLinearMap_apply, Matrix.mulVec_smul]
    refine ⟨g.val.mulVec z, ?_, rfl⟩
    simp only [SetLike.mem_coe, Matrix.GeneralLinearGroup.mem_smul]
    use z, hz

lemma smul_GL_mono {M L : Submodule R (ι → K)} (g : GL ι K) (hML : M ≤ L) : g • M ≤ g • L := by
  intro x
  simp only [Matrix.GeneralLinearGroup.mem_smul, forall_exists_index, and_imp]
  rintro y hy rfl
  use y, (hML hy)

lemma smul_le_iff {M L : Submodule R (ι → K)} (g : GL ι K) : g • M ≤ g • L ↔ M ≤ L := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_GL_mono _ h⟩
  rw [← one_smul (GL ι K) M, ← one_smul (GL ι K) L, ← inv_mul_cancel g, mul_smul, mul_smul]
  exact smul_GL_mono _ h

lemma smul_eq_iff (g : GL ι K) (M L : Submodule R (ι → K)) :
    g • M = g • L ↔ M = L := by
  refine ⟨fun h ↦ le_antisymm ?_ ?_, by rintro rfl; rfl⟩ <;>
  · rw [← smul_le_iff g]
    first | exact le_of_eq h | exact ge_of_eq h

lemma smul_lt_iff (g : GL ι K) (M L : Submodule R (ι → K)) : g • M < g • L ↔ M < L := by
  constructor
  · intro h
    by_contra hnotlt
    simp [eq_of_le_of_not_lt ((smul_le_iff g).mp (le_of_lt h)) hnotlt] at h
  · intro h
    by_contra hnotlt
    have := eq_of_le_of_not_lt ((smul_le_iff g).mpr (le_of_lt h)) hnotlt
    rw [smul_eq_iff] at this
    simp [this] at h

end BruhatTits
