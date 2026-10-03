/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
/-!
# Induced groups of equivariant functions

For a subgroup `H` of `G` acting on a commutative group `B`, the induced
group consists of functions satisfying `f (h * x) = h • f x`. Right
translation gives its `G`-action. Evaluation at the identity is an
`H`-equivariant epimorphism, without any finite-index assumption.
-/

@[expose] public section

namespace ProCGroups.InducedFunctions

universe uG uB

variable {G : Type uG} {B : Type uB}

/-- The subgroup of equivariant functions defining the induced group. -/
def inducedSubgroup [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] : Subgroup (G → B) where
  carrier := {f | ∀ (h : H) (x : G), f (h.1 * x) = h • f x}
  one_mem' := by
    intro h x
    exact (smul_one h).symm
  mul_mem' := by
    intro f k hf hk h x
    simp only [Pi.mul_apply, hf h x, hk h x]
    exact (MulDistribMulAction.smul_mul h (f x) (k x)).symm
  inv_mem' := by
    intro f hf h x
    simp only [Pi.inv_apply, hf h x]
    exact (map_inv (MulDistribMulAction.toMonoidHom B h) (f x)).symm

/-- The commutative group of equivariant functions. -/
abbrev InducedModule [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :=
  inducedSubgroup (G := G) (B := B) H

/-- The canonical right-translation action on equivariant functions. -/
instance inducedMulDistribMulAction [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    MulDistribMulAction G (InducedModule (B := B) H) where
  smul g f := ⟨fun x ↦ f.1 (x * g), by
    intro h x
    simpa only [mul_assoc] using f.2 h (x * g)⟩
  one_smul := by
    intro f
    apply Subtype.ext
    funext x
    change f.1 (x * 1) = f.1 x
    rw [mul_one]
  mul_smul := by
    intro g k f
    apply Subtype.ext
    funext x
    change f.1 (x * (g * k)) = f.1 ((x * g) * k)
    rw [mul_assoc]
  smul_mul := by
    intro g f k
    ext x
    rfl
  smul_one := by
    intro g
    ext x
    rfl

/-- Evaluation at the identity element of the ambient group. -/
def inducedEvaluation [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] :
    InducedModule (B := B) H →* B where
  toFun f := f.1 1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem inducedEvaluation_apply [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] (f : InducedModule (B := B) H) :
    inducedEvaluation H f = f.1 1 :=
  rfl

/-- Evaluation intertwines the restricted translation action and the
original subgroup action. -/
theorem inducedEvaluation_smul [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] (h : H) (f : InducedModule (B := B) H) :
    inducedEvaluation H ((h : G) • f) = h • inducedEvaluation H f := by
  change f.1 (1 * (h : G)) = h • f.1 1
  simpa only [one_mul, mul_one] using f.2 h 1

/-- An arbitrary value at the identity extends to an equivariant function:
use the original action on `H` and the identity value outside `H`. -/
theorem inducedEvaluation_surjective [Group G] (H : Subgroup G) [CommGroup B]
    [MulDistribMulAction H B] : Function.Surjective (inducedEvaluation (B := B) H) := by
  classical
  intro b
  let f : G → B := fun x => if hx : x ∈ H then (⟨x, hx⟩ : H) • b else 1
  have hf : f ∈ inducedSubgroup (B := B) H := by
    intro h x
    by_cases hx : x ∈ H
    · have hhx : (h : G) * x ∈ H := H.mul_mem h.property hx
      simp only [f, dite_eq_left hhx, dite_eq_left hx]
      change (h * (⟨x, hx⟩ : H)) • b = h • ((⟨x, hx⟩ : H) • b)
      exact mul_smul h (⟨x, hx⟩ : H) b
    · have hhx : (h : G) * x ∉ H := fun hmem => hx ((H.mul_mem_cancel_left h.property).mp hmem)
      simp only [f, dite_eq_right hhx, dite_eq_right hx, smul_one]
  refine ⟨⟨f, hf⟩, ?_⟩
  change f 1 = b
  simp only [f, dite_eq_left H.one_mem]
  exact one_smul H b

end ProCGroups.InducedFunctions
