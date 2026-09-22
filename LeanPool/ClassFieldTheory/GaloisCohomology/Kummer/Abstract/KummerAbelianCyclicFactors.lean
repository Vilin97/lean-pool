/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Abstract.KummerGlobalOperator

/-! # Kummer Abelian Cyclic Factors -/
namespace KummerTheory

open CyclicCohomology

/-!
# finite abelian Kummer theory, the finite abelian Kummer decomposition: cyclic factors of a
  finite abelian extension

The proof of the finite abelian Kummer decomposition reduces a finite abelian extension to cyclic
subextensions.  This file supplies the group-theoretic source for that step.
A finite commutative group is written as a finite product of cyclic `ZMod`
groups.  The kernels of its coordinate maps have trivial intersection.
Pulling those kernels back along a quotient map produces intermediate
subgroups whose quotients are finite cyclic and whose intersection is the
original normal subgroup.

No radical generators or field-lattice endpoint are asserted here.
-/

noncomputable section

section FiniteAbelianCyclicFactors

/-- Coordinate characters obtained from the structure theorem separate the
elements of a finite commutative group. -/
theorem finiteCommGroup_exists_jointlyFaithful_cyclic_factors
    (Q : Type*) [CommGroup Q] [Finite Q] :
    ∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let f : ∀ i, Q →* Multiplicative (ZMod (m i)) := fun i =>
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e
  refine ⟨ι, hι, m, hm, f, ?_, ?_⟩
  · intro i
    exact (Function.surjective_eval i).comp e.surjective
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply e.injective
      ext i
      have hxi : x ∈ MonoidHom.ker (f i) :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

section Pullback

variable {P C : Type*} [Group P] [Group C]
  (H : Subgroup P) [H.Normal]

/-- Pull a quotient-factor kernel back to the original group. -/
def cyclicFactorSubgroup (f : (P ⧸ H) →* C) : Subgroup P :=
  MonoidHom.ker (f.comp (QuotientGroup.mk' H))

/-- The kernel subgroup attached to a cyclic quotient factor is normal. -/
instance cyclicFactorSubgroup_normal (f : (P ⧸ H) →* C) :
    (cyclicFactorSubgroup H f).Normal :=
  MonoidHom.normal_ker _

/-- The original normal subgroup lies in every pulled-back factor kernel. -/
theorem le_cyclicFactorSubgroup (f : (P ⧸ H) →* C) :
    H ≤ cyclicFactorSubgroup H f := by
  intro x hx
  rw [cyclicFactorSubgroup, MonoidHom.mem_ker, MonoidHom.comp_apply]
  have hmk : (x : P ⧸ H) = 1 :=
    (QuotientGroup.eq_one_iff (N := H) x).2 hx
  exact (congrArg f hmk).trans (map_one f)

/-- A surjective cyclic factor gives a cyclic quotient of the original
group by its pulled-back kernel. -/
theorem cyclic_cyclicFactorSubgroup_quotient
    [IsCyclic C] (f : (P ⧸ H) →* C) (hf : Function.Surjective f) :
    IsCyclic (P ⧸ cyclicFactorSubgroup H f) := by
  let F : P →* C := f.comp (QuotientGroup.mk' H)
  have hF : Function.Surjective F :=
    hf.comp (QuotientGroup.mk'_surjective H)
  let e : (P ⧸ MonoidHom.ker F) ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective F hF
  change IsCyclic (P ⧸ MonoidHom.ker F)
  exact (e.isCyclic).2 inferInstance

/-- If the cyclic factor is finite, so is the corresponding quotient. -/
theorem finite_cyclicFactorSubgroup_quotient
    [Finite C] (f : (P ⧸ H) →* C) (hf : Function.Surjective f) :
    Finite (P ⧸ cyclicFactorSubgroup H f) := by
  let F : P →* C := f.comp (QuotientGroup.mk' H)
  have hF : Function.Surjective F :=
    hf.comp (QuotientGroup.mk'_surjective H)
  let e : (P ⧸ MonoidHom.ker F) ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective F hF
  change Finite (P ⧸ MonoidHom.ker F)
  exact Finite.of_equiv C e.symm.toEquiv

variable {ι : Type*} {Cι : ι → Type*} [∀ i, Group (Cι i)]

/-- Jointly faithful quotient factors pull back to subgroups whose
intersection is exactly the original normal subgroup. -/
theorem iInf_cyclicFactorSubgroup_eq
    (f : ∀ i, (P ⧸ H) →* Cι i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥) :
    (⨅ i, cyclicFactorSubgroup H (f i)) = H := by
  apply le_antisymm
  · intro x hx
    have hq : (x : P ⧸ H) ∈ ⨅ i, MonoidHom.ker (f i) := by
      rw [Subgroup.mem_iInf]
      intro i
      exact (Subgroup.mem_iInf.mp hx) i
    rw [hfaithful, Subgroup.mem_bot] at hq
    exact (QuotientGroup.eq_one_iff x).1 hq
  · exact le_iInf fun i => le_cyclicFactorSubgroup H (f i)

end Pullback

end FiniteAbelianCyclicFactors

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A closed abstract field subgroup `G_L` remains closed when regarded as
a subgroup of the larger abstract field subgroup `G_K`. -/
theorem extensionSubgroup_isClosed
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup) := by
  change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))
  exact L.isClosed'.preimage continuous_subtype_val

variable [IsTopologicalGroup G]

/-- A pulled-back cyclic factor kernel is closed inside `G_K`: the finite
quotient by `G_L` is discrete, and the factor kernel is pulled back along the
continuous quotient map. -/
theorem cyclicFactorSubgroup_isClosed
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    IsClosed
      (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
        Set K.toSubgroup) := by
  let H := extensionSubgroup (G := G) K L hLK
  let : IsClosed (H : Set K.toSubgroup) := extensionSubgroup_isClosed K L hLK
  change IsClosed
    ((QuotientGroup.mk' H) ⁻¹' (MonoidHom.ker f : Set (K.toSubgroup ⧸ H)))
  exact (isClosed_discrete _).preimage QuotientGroup.continuous_mk

/-- The closed abstract intermediate field attached to one cyclic coordinate
factor of `G_K/G_L`. -/
def closedCyclicFactorSubgroup
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    ClosedSubgroup G where
  toSubgroup :=
    (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f).map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
          Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (cyclicFactorSubgroup_isClosed K L hLK f)

/-- The cyclic-factor intermediate subgroup lies below the base subgroup
`G_K`. -/
theorem closedCyclicFactorSubgroup_le_base
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    (closedCyclicFactorSubgroup K L hLK f).toSubgroup ≤ K.toSubgroup := by
  rintro x ⟨y, hy, rfl⟩
  exact y.property

/-- The original subgroup `G_L` lies below every cyclic-factor intermediate
subgroup.  Finiteness is needed by the closed intermediate object itself:
it makes the quotient discrete, hence its pulled-back kernel closed. -/
theorem le_closedCyclicFactorSubgroup
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    L.toSubgroup ≤
      (closedCyclicFactorSubgroup (hfinite := hfinite) K L hLK f).toSubgroup := by
  intro x hx
  let y : K.toSubgroup := ⟨x, hLK hx⟩
  have hyH : y ∈ extensionSubgroup (G := G) K L hLK := by
    exact hx
  have hyS : y ∈ cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :=
    le_cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f hyH
  exact ⟨y, hyS, rfl⟩

/-- Viewed inside `G_K`, the closed cyclic-factor subgroup has exactly the
pulled-back coordinate kernel as its extension subgroup. -/
theorem extensionSubgroup_closedCyclicFactorSubgroup_eq
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
        (closedCyclicFactorSubgroup_le_base K L hLK f) =
      cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f := by
  ext x
  simp only [extensionSubgroup, closedCyclicFactorSubgroup]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The extension subgroup of a closed cyclic factor is normal in `G_K`. -/
instance extensionSubgroup_closedCyclicFactorSubgroup_normal
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    (extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
      (closedCyclicFactorSubgroup_le_base K L hLK f)).Normal := by
  rw [extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK f]
  infer_instance

/-- The quotient attached to a surjective finite cyclic coordinate is
finite. -/
theorem finite_extensionSubgroup_closedCyclicFactorSubgroup_quotient
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C] [Finite C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)
    (hf : Function.Surjective f) :
    Finite
      (K.toSubgroup ⧸
        extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
          (closedCyclicFactorSubgroup_le_base K L hLK f)) := by
  rw [extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK f]
  exact finite_cyclicFactorSubgroup_quotient
    (extensionSubgroup (G := G) K L hLK) f hf

/-- The quotient attached to a surjective cyclic coordinate is cyclic. -/
theorem cyclic_extensionSubgroup_closedCyclicFactorSubgroup_quotient
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C] [IsCyclic C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)
    (hf : Function.Surjective f) :
    IsCyclic
      (K.toSubgroup ⧸
        extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
          (closedCyclicFactorSubgroup_le_base K L hLK f)) := by
  let e := QuotientGroup.quotientMulEquivOfEq
    (extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK f)
  exact e.isCyclic.2
    (cyclic_cyclicFactorSubgroup_quotient
      (extensionSubgroup (G := G) K L hLK) f hf)

/-- An exponent bound on `G_K/G_L` descends to the quotient attached to a
closed cyclic coordinate. -/
theorem extensionSubgroup_closedCyclicFactorSubgroup_quotient_pow_eq_one
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C)
    {n : ℕ}
    (hexponent : ∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK,
      q ^ n = 1) :
    ∀ q : K.toSubgroup ⧸
        extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
          (closedCyclicFactorSubgroup_le_base K L hLK f),
      q ^ n = 1 := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  change (QuotientGroup.mk'
      (extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
        (closedCyclicFactorSubgroup_le_base K L hLK f))) x ^ n = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (N :=
    extensionSubgroup (G := G) K (closedCyclicFactorSubgroup K L hLK f)
      (closedCyclicFactorSubgroup_le_base K L hLK f)) (x ^ n)).2
  rw [extensionSubgroup_closedCyclicFactorSubgroup_eq K L hLK f]
  change f ((QuotientGroup.mk'
    (extensionSubgroup (G := G) K L hLK)) (x ^ n)) = 1
  rw [map_pow, hexponent, map_one]

end ClosedCyclicSubextensions

end
end KummerTheory
