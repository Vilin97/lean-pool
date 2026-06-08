/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Operations

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Operations`.
-/

open Function

namespace TwoSidedIdeal
variable {F R S : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S]

attribute [simp] mem_comap

lemma comap_injective (f : F) (hf : Surjective f) : Injective (comap f) := by
  simp [Function.Injective, SetLike.ext_iff, hf.forall]

/-- The order isomorphism on two-sided ideals induced by a ring equivalence. -/
@[simp]
def orderIsoOfRingEquiv {F : Type*} [EquivLike F R S] [RingEquivClass F R S] (f : F) :
    TwoSidedIdeal R ≃o TwoSidedIdeal S where
  toFun := comap (RingEquivClass.toRingEquiv f).symm
  invFun := comap (RingEquivClass.toRingEquiv f)
  left_inv I := by
    have := TwoSidedIdeal.comap_comap (R := R) (S := S) I
        (RingEquivClass.toRingEquiv f) (RingEquivClass.toRingEquiv f).symm
    simp at this
    erw [TwoSidedIdeal.comap_comap _ (RingEquivClass.toRingEquiv f).toRingHom
      (RingEquivClass.toRingEquiv f).symm.toRingHom]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv I := SetLike.ext fun x ↦ by simp only [mem_comap, RingEquiv.apply_symm_apply]
  map_rel_iff' := by
    intro I J
    rw [le_iff, le_iff]
    constructor
    · rintro h x hx
      specialize @h (RingEquivClass.toRingEquiv f x) (by simpa [TwoSidedIdeal.mem_comap])
      simpa [TwoSidedIdeal.mem_comap] using h
    · intro h x hx
      simp only [Equiv.coe_fn_mk, SetLike.mem_coe, mem_comap] at hx ⊢
      exact h hx
end TwoSidedIdeal
