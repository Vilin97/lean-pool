/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerCyclicOperator

/-! # Kummer Global Operator -/
namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: descending the global operator

This file constructs, rather than assumes, the endomorphism of `A_L` induced
by a global equivariant endomorphism `wp : A ⟶ A`.  It also embeds a
`G_K`-fixed global kernel element into the invariant subtype defining `A_L`
and supplies these constructions to the finite cyclic single-radical theorem.

The result remains only the finite cyclic step of the finite abelian Kummer decomposition, not the
full abelian Kummer correspondence.
-/

noncomputable section

open CategoryTheory

/-- The endomorphism of `A_L` induced functorially by a global equivariant
endomorphism `wp : A ⟶ A`: first restrict to `G_K`, then pass to the
`G_L`-invariants and the quotient action. -/
noncomputable def extensionFixedEndomorphism
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) :
    extensionFixedRepresentation A K L hLK hnormal ⟶
      extensionFixedRepresentation A K L hLK hnormal :=
  (Rep.quotientToInvariantsFunctor (k := ℤ) (extensionSubgroup K L hLK)).map
    ((Rep.resFunctor K.toSubgroup.subtype).map wp)

/-- A global element fixed by `G_K`, viewed in the invariant subtype which
is the carrier of `A_L`. -/
noncomputable def extensionFixedKernelElement
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedRepresentation A K L hLK hnormal).V :=
  ⟨xi, by
    intro s
    change A.ρ s.1.1 xi = xi
    exact hxi_fixed s.1⟩

/-- The underlying value of the fixed kernel element is the selected global kernel element. -/
@[simp]
theorem extensionFixedKernelElement_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    (extensionFixedKernelElement A K L hLK xi hxi_fixed).1 = xi := rfl

/-- The extension-fixed endomorphism acts on underlying values by the global operator. -/
@[simp]
theorem extensionFixedEndomorphism_apply_val
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) (x : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedEndomorphism A K L hLK wp).hom x).1 = wp.hom x.1 := by
  rfl

/-- The additive order of the fixed kernel element is inherited from its ambient value. -/
theorem extensionFixedKernelElement_addOrderOf
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi) :
    addOrderOf (extensionFixedKernelElement A K L hLK xi hxi_fixed) = addOrderOf xi := by
  let incl : (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  calc
    addOrderOf (extensionFixedKernelElement A K L hLK xi hxi_fixed) =
        addOrderOf (incl (extensionFixedKernelElement A K L hLK xi hxi_fixed)) :=
      (addOrderOf_injective incl (fun _ _ h => Subtype.ext h)
        (extensionFixedKernelElement A K L hLK xi hxi_fixed)).symm
    _ = addOrderOf xi := by rfl

/-- The selected fixed element lies in the kernel of the extension-fixed endomorphism. -/
theorem extensionFixedKernelElement_in_kernel
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (wp : A ⟶ A) (xi : A.V)
    (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
    (hxi_kernel : wp.hom xi = 0) :
    (extensionFixedEndomorphism A K L hLK wp).hom
      (extensionFixedKernelElement A K L hLK xi hxi_fixed) = 0 := by
  apply Subtype.ext
  change wp.hom xi = 0
  exact hxi_kernel

/-- Every element of the extension subgroup fixes the selected kernel element. -/
theorem extensionFixedKernelElement_fixed
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    (xi : A.V) (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    (extensionFixedRepresentation A K L hLK hnormal).ρ q
        (extensionFixedKernelElement A K L hLK xi hxi_fixed) =
      extensionFixedKernelElement A K L hLK xi hxi_fixed := by
  refine QuotientGroup.induction_on q ?_
  intro k
  apply Subtype.ext
  exact hxi_fixed k

/-- The finite cyclic single-radical step with a genuinely global operator.
The endomorphism on `A_L` and its distinguished kernel element are both
constructed in the proof, not supplied as hypotheses. -/
theorem cyclicGlobalOperator_singleRadical
    {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G) (hAxiom : SatisfiesCyclicNormKernelVanishing A)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (wp : A ⟶ A) (n : ℕ+) (xi : A.V)
    (hxi_order : addOrderOf xi = (n : ℕ))
    (hxi_kernel : wp.hom xi = 0)
    (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
    (hexponent : ∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
      q ^ (n : ℕ) = 1) :
    ∃ a : (extensionFixedRepresentation A K L hLK hnormal).V,
      (∀ q : K.toSubgroup ⧸ extensionSubgroup K L hLK,
        (extensionFixedRepresentation A K L hLK hnormal).ρ q
            ((extensionFixedEndomorphism A K L hLK wp).hom a) =
          (extensionFixedEndomorphism A K L hLK wp).hom a) ∧
      representationStabilizer (extensionFixedRepresentation A K L hLK hnormal) a = ⊥ := by
  let xiL := extensionFixedKernelElement A K L hLK xi hxi_fixed
  apply cyclicOperator_singleRadical_of_normKernelVanishing
    A hAxiom K L hLK g hg (extensionFixedEndomorphism A K L hLK wp)
    n xiL
  · simpa [xiL, extensionFixedKernelElement_addOrderOf] using hxi_order
  · exact extensionFixedKernelElement_in_kernel
      A K L hLK wp xi hxi_fixed hxi_kernel
  · exact extensionFixedKernelElement_fixed A K L hLK xi hxi_fixed
  · exact hexponent

end
end KummerTheory
