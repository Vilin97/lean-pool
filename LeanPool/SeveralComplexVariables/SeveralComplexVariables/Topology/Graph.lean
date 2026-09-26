/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Graphs characterized by equations

An equation determining a unique fiber value gives uniqueness of solution maps. For a continuous
solution, projection from the zero set is a homeomorphism onto its parameter domain. Neither
result requires differentiability.

## Main definitions

* `Homeomorph.implicitGraph`: A continuous graph characterization makes projection a homeomorphism.

## Main results

* `Set.eqOn_of_forall_mem_eq_iff`: A graph characterization gives uniqueness among all solution maps
  staying in the specified fiber neighborhood; no regularity assumption on the competing solution is
  needed.
-/

public section
open Set
variable {P Q R : Type*}

/-- A graph characterization gives uniqueness among all solution maps staying in the specified fiber
neighborhood; no regularity assumption on the competing solution is needed. -/
theorem Set.eqOn_of_forall_mem_eq_iff {U : Set P} {V : Set Q} {f : P × Q → R} {c : R}
    {g h : P → Q} (hgraph : ∀ x ∈ U, ∀ y ∈ V, f (x, y) = c ↔ y = g x)
    (hh : MapsTo h U V) (hsol : ∀ x ∈ U, f (x, h x) = c) : EqOn h g U :=
  fun x hx => (hgraph x hx (h x) (hh hx)).mp (hsol x hx)

variable [TopologicalSpace P] [TopologicalSpace Q] [Zero R]

/-- A continuous graph characterization makes projection a homeomorphism. -/
@[expose] def Homeomorph.implicitGraph {U : Set P} {V : Set Q} {f : P × Q → R} {g : P → Q}
    (hg : ContinuousOn g U) (hm : MapsTo g U V)
    (hgraph : ∀ x ∈ U, ∀ y ∈ V, f (x, y) = 0 ↔ y = g x) :
    {p : P × Q // p ∈ U ×ˢ V ∧ f p = 0} ≃ₜ U where
  toFun p := ⟨p.val.1, p.property.1.1⟩
  invFun x := ⟨(x.val, g x), ⟨⟨x.property, hm x.property⟩,
    (hgraph x x.property (g x) (hm x.property)).mpr rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, g p.val.1) = p.val
    apply Prod.ext
    · rfl
    · exact ((hgraph p.val.1 p.property.1.1 p.val.2 p.property.1.2).mp p.property.2).symm
  right_inv x := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk hg.domRestrict).subtype_mk _

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
