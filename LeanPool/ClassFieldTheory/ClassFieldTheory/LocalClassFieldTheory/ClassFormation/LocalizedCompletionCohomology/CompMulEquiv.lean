/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.Invariants
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.NormImage
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.TateH0.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldLocalization
public import Mathlib.FieldTheory.Galois.Infinite
/-!
# The local class-field axiom for decomposition-group blocks

This file supplies the localized-completion input for the class formation. First it
proves change-of-group equivalences for low-degree multiplicative Tate
cohomology. It then applies the canonical algebraic-localization results:
the algebraic localization of a finite Galois extension is finite Galois over
the completed base, and the localization equivalence identifies its Galois group with the
decomposition group.

For a nonarchimedean locally compact base completion, the concrete local
class-field axiom then gives:

* `H⁰` is the actual field-norm quotient;
* `H⁻¹` is trivial;
* the cardinality and Herbrand quotient equal the local degree.
-/

@[expose] public section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable
section

namespace LocalClassFieldTheory

universe uH uG uA

variable {H : Type uH} {G : Type uG} {A : Type uA}
    [Group H] [Fintype H] [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A]

theorem tateNorm_compMulEquiv (e : H ≃* G) (a : A) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    tateNorm H A a = tateNorm G A a := by
  let := MulDistribMulAction.compHom A e.toMonoidHom
  change (∏ h : H, e h • a) = ∏ g : G, g • a
  exact e.toEquiv.prod_comp fun g ↦ g • a

/-- Transport of the fixed subgroup along an isomorphism of acting groups. -/
noncomputable def fixedSubgroupCompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    fixedSubgroup H A ≃* fixedSubgroup G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  exact
    { toFun := fun x ↦ ⟨x.1, fun g ↦ by
          have hx := x.2 (e.symm g)
          change e (e.symm g) • x.1 = x.1 at hx
          simpa using hx⟩
      invFun := fun x ↦ ⟨x.1, fun h ↦ x.2 (e h)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- Transport of the Tate norm kernel along an isomorphism of acting groups. -/
noncomputable def normKernelCompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    normKernelSubgroup H A ≃* normKernelSubgroup G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  exact
    { toFun := fun x ↦ ⟨x.1, by
          change tateNorm G A x.1 = 1
          rw [← tateNorm_compMulEquiv e]
          exact x.2⟩
      invFun := fun x ↦ ⟨x.1, by
          change tateNorm H A x.1 = 1
          rw [tateNorm_compMulEquiv e]
          exact x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

/-- Change of acting group for multiplicative degree-zero Herbrand
cohomology. -/
noncomputable def herbrandH0CompMulEquiv (e : H ≃* G) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    HerbrandH0 H A ≃* HerbrandH0 G A := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  let f := fixedSubgroupCompMulEquiv (A := A) e
  let N :=
    (tateNormSubgroup H A).subgroupOf (fixedSubgroup H A)
  let M :=
    (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      change tateNorm G A a = x.1
      rw [← tateNorm_compMulEquiv e]
      exact ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      change tateNorm H A a = y.1
      rw [tateNorm_compMulEquiv e]
      exact ha)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

/-- Change of acting group for multiplicative degree-minus-one Herbrand
cohomology. -/
noncomputable def herbrandHMinusOneCompMulEquiv
    (e : H ≃* G) (σ : H) :
    letI := MulDistribMulAction.compHom A e.toMonoidHom
    HerbrandHMinusOne H A σ ≃*
      HerbrandHMinusOne G A (e σ) := by
  letI := MulDistribMulAction.compHom A e.toMonoidHom
  let f := normKernelCompMulEquiv (A := A) e
  let N :=
    (augmentationSubgroup H A σ).subgroupOf
      (normKernelSubgroup H A)
  let M :=
    (augmentationSubgroup G A (e σ)).subgroupOf
      (normKernelSubgroup G A)
  exact quotientMulEquivOfSplit N M
    f.toMonoidHom f.symm.toMonoidHom
    (fun y ↦ f.apply_symm_apply y)
    (fun x hx ↦ by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rcases hx with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      exact ha)
    (fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rcases hy with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      exact ha)
    (fun x hx ↦ by
      have hx1 : x = 1 := by
        apply f.injective
        simpa [f] using hx
      rw [hx1]
      exact N.one_mem)

end LocalClassFieldTheory
