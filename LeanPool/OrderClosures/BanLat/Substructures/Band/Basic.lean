/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Substructures.Ideal
public import LeanPool.OrderClosures.BanLat.OrderComplete


/-!
# Bands

A **band** in a vector lattice is an order ideal that is **order closed**:
whenever a subset of the band has a supremum in the ambient space, that
supremum also lies in the band.

This file defines the bundled structure `Band`, relates bands to order ideals
and vector sublattices, proves the basic closure properties, and records that
order completeness passes from the ambient vector lattice to a band.
-/

@[expose] public section

section MainVariables
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

/-! ### The band structure -/

/-- A **band** in a vector lattice is an order ideal that is **order closed**:
whenever a subset of the band has a supremum in `X`, that supremum also lies
in the band. -/
structure Band (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X]
    extends OrderIdeal X where
  sSup_mem' :
    ∀ (S : Set X), S ⊆ carrier → S.Nonempty → ∀ x, IsLUB S x → x ∈ carrier

namespace Band

instance : SetLike (Band X) X where
  coe B := B.carrier
  coe_injective p q h := by
    cases p; cases q; congr
    exact SetLike.ext' h

variable (B : Band X)

/-! ### A band is an ideal and a vector sublattice -/

/-- Every band is an order ideal. -/
def toOrderIdeal' : OrderIdeal X := B.toOrderIdeal

/-! ### Closure under suprema -/

/-- A band is closed under suprema: if a subset of the band has a supremum in
`X`, the supremum lies in the band. -/
theorem sSup_mem {S : Set X} (hS : S ⊆ (B : Set X)) (hne : S.Nonempty)
    {x : X} (hx : IsLUB S x) : x ∈ B :=
  B.sSup_mem' S hS hne x hx

/-! ### Basic membership lemmas inherited from the underlying ideal -/

/-- A band is closed under `⊔`. -/
theorem sup_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊔ y ∈ B :=
  B.toOrderIdeal.sup_mem hx hy

/-- A band is closed under `⊓`. -/
theorem inf_mem {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    x ⊓ y ∈ B :=
  B.toOrderIdeal.inf_mem hx hy

/-- A band is solid. -/
theorem solid {x y : X} (hx : x ∈ B) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    y ∈ B :=
  B.toOrderIdeal.solid hx hy0 hyx

/-- A band is closed under absolute value. -/
theorem abs_mem {x : X} (hx : x ∈ B) : |x| ∈ B :=
  B.toOrderIdeal.abs_mem hx

/-- Membership in a band is equivalent to membership of the absolute value. -/
theorem mem_of_abs_mem {x : X} (h : |x| ∈ B) : x ∈ B :=
  B.toOrderIdeal.mem_of_abs_mem h

/-- Solidity in terms of absolute value. -/
theorem mem_of_abs_le_abs {x y : X} (hx : x ∈ B) (h : |y| ≤ |x|) :
    y ∈ B :=
  B.toOrderIdeal.mem_of_abs_le_abs hx h

/-! ### Construction from the positive directed closure condition

It suffices to test the closure condition on positive directed subsets:
an order ideal closed under suprema of positive directed subsets is
automatically a band. -/

/-- An order ideal is a band as soon as every directed subset of positive
elements with supremum in `X` has its supremum in the ideal. -/
def ofPosDirectedSSupMem (J : OrderIdeal X)
    (h : ∀ S, S ⊆ (J : Set X) → (∀ x ∈ S, 0 ≤ x) → DirectedOn (· ≤ ·) S
      → S.Nonempty → ∀ x, IsLUB S x → x ∈ J) : Band X where
  toOrderIdeal := J
  sSup_mem' := by
    classical
    intro S hSJ hne y hy
    obtain ⟨s₀, hs₀⟩ := hne
    have hs₀J : s₀ ∈ J := hSJ hs₀
    have finsup_mem : ∀ (F : Finset X) (hF : F.Nonempty), ↑F ⊆ S →
        F.sup' hF id ∈ J := by
      intro F hF hFS
      induction hF using Finset.Nonempty.cons_induction with
      | singleton x =>
        rw [Finset.sup'_singleton]
        exact hSJ (hFS (by simp))
      | cons x F hxF hFne ih =>
        rw [Finset.sup'_cons hFne id]
        refine J.sup_mem (hSJ (hFS ?_)) (ih ?_)
        · simp
        · intro a ha; exact hFS (by simp [ha])
    set T : Set X :=
      { z | ∃ F : Finset X, ∃ hF : F.Nonempty, ↑F ⊆ S ∧ s₀ ∈ F ∧
        z = F.sup' hF id - s₀ }
    have hT_J : T ⊆ (J : Set X) := by
      rintro z ⟨F, hF, hFS, _, rfl⟩
      exact J.toSubmodule.sub_mem (finsup_mem F hF hFS) hs₀J
    have hT_pos : ∀ z ∈ T, 0 ≤ z := by
      rintro z ⟨F, hF, hFS, hs₀F, rfl⟩
      exact sub_nonneg.mpr (Finset.le_sup' id hs₀F)
    have hT_dir : DirectedOn (· ≤ ·) T := by
      rintro a ⟨Fa, hFa, hFaS, hs₀a, rfl⟩ b ⟨Fb, hFb, hFbS, hs₀b, rfl⟩
      refine ⟨(Fa ∪ Fb).sup' (hFa.mono Finset.subset_union_left) id - s₀,
        ⟨Fa ∪ Fb, hFa.mono Finset.subset_union_left, ?_, ?_, rfl⟩, ?_, ?_⟩
      · rw [Finset.coe_union]; exact Set.union_subset hFaS hFbS
      · exact Finset.mem_union.mpr (Or.inl hs₀a)
      · exact sub_le_sub_right
          (Finset.sup'_mono id Finset.subset_union_left hFa) s₀
      · exact sub_le_sub_right
          (Finset.sup'_mono id Finset.subset_union_right hFb) s₀
    have hT_ne : T.Nonempty :=
      ⟨0, ⟨{s₀}, Finset.singleton_nonempty s₀, by
        intro a ha; rw [Finset.coe_singleton, Set.mem_singleton_iff] at ha
        rw [ha]; exact hs₀,
        Finset.mem_singleton_self _, by
        rw [Finset.sup'_singleton]; exact (sub_self s₀).symm⟩⟩
    have hT_lub : IsLUB T (y - s₀) := by
      refine ⟨?_, ?_⟩
      · rintro z ⟨F, hF, hFS, _, rfl⟩
        exact sub_le_sub_right
          (Finset.sup'_le hF id (fun a ha => hy.1 (hFS ha))) s₀
      · intro c hc
        rw [sub_le_iff_le_add]
        apply hy.2
        intro s hs
        have hF : ({s, s₀} : Finset X).Nonempty := ⟨s, by simp⟩
        have hFS : (↑({s, s₀} : Finset X) : Set X) ⊆ S := by
          intro a ha
          rw [Finset.coe_insert, Finset.coe_singleton] at ha
          rcases ha with rfl | rfl
          · exact hs
          · exact hs₀
        have hs₀mem : s₀ ∈ ({s, s₀} : Finset X) := by simp
        have hT_elt : ({s, s₀} : Finset X).sup' hF id - s₀ ∈ T :=
          ⟨_, hF, hFS, hs₀mem, rfl⟩
        have hle : ({s, s₀} : Finset X).sup' hF id - s₀ ≤ c := hc hT_elt
        have hsup_ge : s ≤ ({s, s₀} : Finset X).sup' hF id :=
          Finset.le_sup' id (by simp : s ∈ ({s, s₀} : Finset X))
        have : ({s, s₀} : Finset X).sup' hF id ≤ c + s₀ :=
          sub_le_iff_le_add.mp hle
        exact hsup_ge.trans this
    have hu : y - s₀ ∈ J := h T hT_J hT_pos hT_dir hT_ne (y - s₀) hT_lub
    have hres : y - s₀ + s₀ ∈ J := J.toSubmodule.add_mem hu hs₀J
    change y ∈ J
    rw [sub_add_cancel] at hres
    exact hres

end Band

end MainVariables

section CCLSubtype

variable {X : Type*} [AddCommGroup X] [ConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

namespace Band

/-! ### Order completeness of the underlying subtype -/

/-- A band in an order complete vector lattice is itself order complete. -/
noncomputable instance instConditionallyCompleteLatticeSubtype
    (B : Band X) :
    ConditionallyCompleteLattice ↥B.toSubmodule := by
  letI : Nonempty ↥B.toSubmodule := ⟨0⟩
  refine conditionallyCompleteLatticeOfPosSet ↥B.toSubmodule ?_
  intro S _ hne hbdd
  set T : Set X := Subtype.val '' S with hT_def
  have hT_sub : T ⊆ (B : Set X) := by
    rintro _ ⟨⟨a, ha⟩, _, rfl⟩; exact ha
  have hT_ne : T.Nonempty := hne.image _
  obtain ⟨u, hu⟩ := hbdd
  have hT_bdd : BddAbove T :=
    ⟨u.1, by rintro _ ⟨v, hv, rfl⟩; exact hu hv⟩
  have hT_lub : IsLUB T (sSup T) := isLUB_csSup hT_ne hT_bdd
  refine ⟨⟨sSup T, B.sSup_mem hT_sub hT_ne hT_lub⟩, ?_, ?_⟩
  · rintro a ha
    change a.1 ≤ sSup T
    exact hT_lub.1 ⟨a, ha, rfl⟩
  · rintro a hub
    change sSup T ≤ a.1
    exact hT_lub.2 (by rintro _ ⟨b, hb, rfl⟩; exact hub hb)

end Band

end CCLSubtype
