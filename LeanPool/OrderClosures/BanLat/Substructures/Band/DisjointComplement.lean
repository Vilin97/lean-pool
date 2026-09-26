/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Disjoint
public import LeanPool.OrderClosures.BanLat.Substructures.Band.Basic


/-!
# Disjoint complements

The **disjoint complement** `Aᵈ` of a set `A ⊆ X` consists of all elements of
`X` disjoint from every member of `A`. It is always a band, and behaves
naturally with respect to inclusion, union, and double complementation.

In a normed vector lattice, every disjoint complement is norm closed: it is
an intersection of zero-sets of the continuous maps `x ↦ |x| ⊓ |a|`.
-/

@[expose] public section

variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### The disjoint complement as a set -/

/-- The **disjoint complement** of a set `A ⊆ X` is the set of all elements
disjoint from every member of `A`. -/
def disjointComplement (A : Set X) : Set X :=
  {x : X | ∀ a ∈ A, IsVLDisjoint x a}

@[inherit_doc]
postfix:max "ᵈ" => disjointComplement

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Membership in the disjoint complement: `x ∈ Aᵈ` iff `x` is disjoint from
every member of `A`. -/
theorem mem_disjointComplement_iff {A : Set X} {x : X} :
    x ∈ Aᵈ ↔ ∀ a ∈ A, IsVLDisjoint x a := Iff.rfl

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Disjoint complementation is anti-monotone: `A ⊆ B` implies `Bᵈ ⊆ Aᵈ`. -/
theorem disjointComplement_anti {A B : Set X} (h : A ⊆ B) :
    Bᵈ ⊆ Aᵈ := fun _ hx a ha => hx a (h ha)

omit [VectorLattice X] in
/-- The intersection of a set with its disjoint complement is contained in
`{0}`. -/
theorem disjointComplement_inter_eq_zero (A : Set X) :
    A ∩ Aᵈ ⊆ {0} := by
  rintro a ⟨ha, had⟩
  have hd : |a| ⊓ |a| = 0 := had a ha
  rw [inf_idem] at hd
  exact (abs_eq_zero_iff_zero a).mp hd

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Every set is contained in its double disjoint complement. -/
theorem subset_disjointComplement_disjointComplement (A : Set X) :
    A ⊆ Aᵈᵈ := fun a ha _ hy => isVLDisjoint_comm.mp (hy a ha)

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The triple disjoint complement equals the single disjoint complement. -/
theorem disjointComplement_disjointComplement_disjointComplement (A : Set X) :
    Aᵈᵈᵈ = Aᵈ :=
  Set.Subset.antisymm
    (disjointComplement_anti (subset_disjointComplement_disjointComplement A))
    (subset_disjointComplement_disjointComplement Aᵈ)

omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- The disjoint complement of a union is the intersection of the disjoint
complements. -/
theorem disjointComplement_union (A B : Set X) :
    (A ∪ B)ᵈ = Aᵈ ∩ Bᵈ := by
  ext x
  refine ⟨fun hx => ⟨fun a ha => hx a (Or.inl ha), fun b hb => hx b (Or.inr hb)⟩,
    fun ⟨hA, hB⟩ _ hy => ?_⟩
  rcases hy with hy | hy
  · exact hA _ hy
  · exact hB _ hy

omit [VectorLattice X] in
/-- The disjoint complement of a set together with its disjoint complement is
the singleton `{0}`. -/
theorem disjointComplement_union_disjointComplement_eq_singleton (A : Set X) :
    (A ∪ Aᵈ)ᵈ = ({0} : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxA : x ∈ Aᵈ := fun a ha => hx a (Or.inl ha)
    have hxAd : x ∈ Aᵈᵈ := fun a ha => hx a (Or.inr ha)
    exact disjointComplement_inter_eq_zero Aᵈ ⟨hxA, hxAd⟩
  · rintro x rfl a _
    exact isVLDisjoint_zero_left a

namespace Band

/-! ### The disjoint complement is a band -/

/-- The disjoint complement of any set is a band. -/
def disjointComplement (A : Set X) : Band X :=
  Band.ofPosDirectedSSupMem
    (.ofSolid
      { carrier := Aᵈ
        add_mem' := fun {_ _} hx hy a ha => (hx a ha).add_left (hy a ha)
        zero_mem' := fun a _ => isVLDisjoint_zero_left a
        smul_mem' := fun c {_} hx a ha => (hx a ha).smul_left c }
      (fun _ _ hx hxy a ha => (hx a ha).mono_left hxy))
    (by
      intro S hSJ hpos _ hne y hy a ha
      have hy_nn : 0 ≤ y := by
        obtain ⟨s, hs⟩ := hne
        exact (hpos s hs).trans (hy.1 hs)
      have key : IsLUB ((fun z => |a| ⊓ z) '' S) (|a| ⊓ y) := isLUB_inf_const _ hy
      have hzero : ∀ s ∈ S, |a| ⊓ s = 0 := by
        intro s hs
        have h : |s| ⊓ |a| = 0 := hSJ hs a ha
        rw [abs_of_nonneg (hpos s hs), inf_comm] at h
        exact h
      have h_le : |a| ⊓ y ≤ 0 :=
        key.2 (by rintro _ ⟨s, hs, rfl⟩; exact (hzero s hs).le)
      have h_ge : 0 ≤ |a| ⊓ y := le_inf (abs_nonneg _) hy_nn
      have hay : |a| ⊓ y = 0 := le_antisymm h_le h_ge
      change |y| ⊓ |a| = 0
      rw [abs_of_nonneg hy_nn, inf_comm]; exact hay)

end Band

/-! ### Closedness in normed vector lattices -/

section Normed

variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

/-- In a normed vector lattice, the disjoint complement of any set is norm
closed: it is the intersection of the zero-sets of the continuous maps
`x ↦ |x| ⊓ |a|`. -/
theorem isClosed_disjointComplement (A : Set X) : IsClosed (Aᵈ) := by
  have heq : (Aᵈ : Set X) = ⋂ a ∈ A, (fun x : X => |x| ⊓ |a|) ⁻¹' {0} := by
    ext x
    simp [disjointComplement, IsVLDisjoint]
  rw [heq]
  refine isClosed_iInter (fun a => isClosed_iInter (fun _ => ?_))
  exact isClosed_singleton.preimage
    (NormedVectorLattice.lipschitzWith_abs.continuous.inf continuous_const)

end Normed
