/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Subgroup.Ker
/-!
# Images of subgroups in restriction kernels

This file isolates a group-theoretic criterion for identifying the image of
a subgroup with the kernel of a homomorphism after a surjective quotient.
-/

@[expose] public section

namespace Subgroup

/-- Suppose `φ` is surjective, the kernel of `ψ.comp φ` is `Z ⊔ U`, and `Z`
is already killed by `φ`. Then the image of `U` is exactly the kernel of `ψ`.
-/
theorem map_eq_ker_of_comp_ker_eq_sup_of_left_le_ker
    {A G H : Type*} [Group A] [Group G] [Group H]
    (φ : A →* G) (ψ : G →* H) (Z U : Subgroup A)
    (hφ : Function.Surjective φ)
    (hker : (ψ.comp φ).ker = Z ⊔ U)
    (hZ : Z ≤ φ.ker) :
    U.map φ = ψ.ker := by
  have hmapKer : (ψ.comp φ).ker.map φ = ψ.ker := by
    rw [← MonoidHom.comap_ker]
    exact Subgroup.map_comap_eq_self_of_surjective hφ ψ.ker
  calc
    U.map φ = ⊥ ⊔ U.map φ := by simp
    _ = Z.map φ ⊔ U.map φ := by
      rw [(Subgroup.map_eq_bot_iff Z).2 hZ]
    _ = (Z ⊔ U).map φ := (Subgroup.map_sup Z U φ).symm
    _ = (ψ.comp φ).ker.map φ := by rw [hker]
    _ = ψ.ker := hmapKer

end Subgroup
