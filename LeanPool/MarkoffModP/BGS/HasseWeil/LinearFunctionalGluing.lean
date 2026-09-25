/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Gluing and extending linear functionals

This file isolates the linear-algebra step used by the cotrace construction
of a Weil functional.  A functional on a subspace `U` which vanishes on
`U ∩ V` glues with the zero functional on `V`; over a field the glued
functional then extends to the ambient vector space.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable {k E F : Type*} [Field k]
  [AddCommGroup E] [Module k E]
  [AddCommGroup F] [Module k F]

/-- A linear map on `U` which vanishes whenever its argument also lies in
`V` extends to the ambient space while vanishing on all of `V`. -/
theorem exists_linearMap_extending_eq_zero_on
    (U V : Submodule k E) (f : U →ₗ[k] F)
    (hUV : ∀ x : U, (x : E) ∈ V → f x = 0) :
    ∃ g : E →ₗ[k] F, g.comp U.subtype = f ∧ V ≤ LinearMap.ker g := by
  let pf : LinearPMap (RingHom.id k) E F := ⟨U, f⟩
  let pzero : LinearPMap (RingHom.id k) E F := ⟨V, 0⟩
  have hagree : ∀ (x : pf.domain) (y : pzero.domain),
      (x : E) = y → pf x = pzero y := by
    intro x y hxy
    change f x = 0
    apply hUV x
    exact hxy ▸ y.property
  let glued := pf.sup pzero hagree
  obtain ⟨g, hg⟩ := LinearMap.exists_extend glued.toFun
  refine ⟨g, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    let x' : glued.domain := ⟨x, Submodule.mem_sup_left x.property⟩
    have hpf := (pf.left_le_sup pzero hagree).2
      (x := x) (y := x') rfl
    have hgx := LinearMap.congr_fun hg x'
    exact hgx.trans hpf.symm
  · intro x hx
    rw [LinearMap.mem_ker]
    let x' : glued.domain := ⟨x, Submodule.mem_sup_right hx⟩
    have hpzero := (pf.right_le_sup pzero hagree).2
      (x := ⟨x, hx⟩) (y := x') rfl
    have hgx := LinearMap.congr_fun hg x'
    exact hgx.trans (hpzero.symm.trans (by rfl))

/-- Intersection-subtype form of
`exists_linearMap_extending_eq_zero_on`. -/
theorem exists_linearMap_extending_eq_zero_on_inf
    (U V : Submodule k E) (f : U →ₗ[k] F)
    (hUV : ∀ x : ↥(U ⊓ V), f ⟨x, x.property.1⟩ = 0) :
    ∃ g : E →ₗ[k] F, g.comp U.subtype = f ∧ V ≤ LinearMap.ker g := by
  apply exists_linearMap_extending_eq_zero_on U V f
  intro x hx
  exact hUV ⟨x, x.property, hx⟩

/-- If the original functional is nonzero, the ambient extension can be
chosen nonzero as well. -/
theorem exists_ne_zero_linearMap_extending_eq_zero_on_inf
    (U V : Submodule k E) (f : U →ₗ[k] F)
    (hUV : ∀ x : ↥(U ⊓ V), f ⟨x, x.property.1⟩ = 0)
    (hf : f ≠ 0) :
    ∃ g : E →ₗ[k] F,
      g.comp U.subtype = f ∧ V ≤ LinearMap.ker g ∧ g ≠ 0 := by
  obtain ⟨g, hgU, hgV⟩ :=
    exists_linearMap_extending_eq_zero_on_inf U V f hUV
  refine ⟨g, hgU, hgV, ?_⟩
  intro hg
  apply hf
  rw [← hgU, hg]
  rfl

end

end BGS.HasseWeil
