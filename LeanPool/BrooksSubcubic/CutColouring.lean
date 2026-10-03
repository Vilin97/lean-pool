/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.ColouringGlue
public import LeanPool.BrooksSubcubic.NonRegular

/-!
# Subcubic Brooks theorem: CutColouring

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Induced degree never exceeds the ambient degree. -/
theorem induce_degree_le (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    [DecidablePred (· ∈ S)] [DecidableRel (G.induce S).Adj] (w : ↥S) :
    (G.induce S).degree w ≤ G.degree w.val := by
  classical
  have hsub : ((G.induce S).neighborFinset w).image Subtype.val ⊆ G.neighborFinset w.val := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [mem_neighborFinset] at hy ⊢
    simpa [SimpleGraph.induce, SimpleGraph.comap] using hy
  calc (G.induce S).degree w
      = ((G.induce S).neighborFinset w).card := ((G.induce S).card_neighborFinset_eq_degree w).symm
    _ = (((G.induce S).neighborFinset w).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.neighborFinset w.val).card := Finset.card_le_card hsub
    _ = G.degree w.val := G.card_neighborFinset_eq_degree _

omit [DecidableEq V] in
/-- An outside neighbour supplies the low-degree vertex needed to colour a connected piece. -/
private theorem colorable_induce_of_outside_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (hconn : (G.induce S).Connected)
    (hdeg : ∀ v, G.degree v ≤ 3) (x : ↥S) (z : V)
    (hz : z ∉ S) (hadj : G.Adj x.val z) : (G.induce S).Colorable 3 := by
  classical
  apply connected_colorable_three_of_exists_degree_lt _ hconn
  · intro v
    exact (induce_degree_le G S v).trans (hdeg v.val)
  · refine ⟨x, ?_⟩
    have hsub : ((G.induce S).neighborFinset x).image Subtype.val
        ⊆ (G.neighborFinset x.val).erase z := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, ?_⟩
      · intro h
        exact hz (h ▸ w.property)
      · rw [mem_neighborFinset] at hw
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hw
    have hzmem : z ∈ G.neighborFinset x.val := by rw [mem_neighborFinset]; exact hadj
    calc (G.induce S).degree x
        = ((G.induce S).neighborFinset x).card :=
          ((G.induce S).card_neighborFinset_eq_degree x).symm
      _ = (((G.induce S).neighborFinset x).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ ((G.neighborFinset x.val).erase z).card := Finset.card_le_card hsub
      _ = G.degree x.val - 1 := by
          rw [Finset.card_erase_of_mem hzmem, G.card_neighborFinset_eq_degree]
      _ < 3 := by have := hdeg x.val; omega

/-- **B, cut-vertex reduction (structural half).** Given a 3-regular `G`, a vertex `x`, and a
partition of `V∖{x}` into nonempty `A₀,B₀` with no edge crossing between them, such that both
`G[{x}∪A₀]` and `G[{x}∪B₀]` are connected, `G` is 3-colourable: each side has `x` at degree `< 3`
(it has a neighbour on the other side), so the non-regular case colours it, and the glue lemma
merges them at `x`. This discharges everything downstream of the Lovász cut-existence step. -/
theorem colorable_of_cut_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3)
    (x : V) (A₀ B₀ : Finset V)
    (hAne : A₀.Nonempty) (hBne : B₀.Nonempty)
    (hxnA : x ∉ A₀) (hxnB : x ∉ B₀)
    (hdisj : Disjoint A₀ B₀)
    (hcov : insert x (A₀ ∪ B₀) = Finset.univ)
    (hnocross : ∀ a ∈ A₀, ∀ b ∈ B₀, ¬ G.Adj a b)
    (hAconn : (G.induce ((insert x A₀ : Finset V) : Set V)).Connected)
    (hBconn : (G.induce ((insert x B₀ : Finset V) : Set V)).Connected) :
    G.Colorable 3 := by
  classical
  set A : Finset V := insert x A₀ with hA
  set B : Finset V := insert x B₀ with hB
  have hxA : x ∈ A := Finset.mem_insert_self _ _
  have hxB : x ∈ B := Finset.mem_insert_self _ _
  have hcover : A ∪ B = Finset.univ := by
    rw [hA, hB, Finset.insert_union, Finset.union_insert, ← hcov]
    rw [Finset.insert_idem]
  have : DecidableRel (G.induce ((A : Finset V) : Set V)).Adj := Classical.decRel _
  have : DecidableRel (G.induce ((B : Finset V) : Set V)).Adj := Classical.decRel _
  have hxneighbor : ∀ (C₀ : Finset V), C₀.Nonempty → x ∉ C₀ →
      (G.induce ((insert x C₀ : Finset V) : Set V)).Connected →
      ∃ z ∈ C₀, G.Adj x z := by
    intro C₀ hCne hxnC hCconn
    obtain ⟨c₀, hc₀⟩ := hCne
    have hxmem : x ∈ ((insert x C₀ : Finset V) : Set V) := by
      simp
    have hcmem : c₀ ∈ ((insert x C₀ : Finset V) : Set V) := by
      simp [hc₀]
    have hne : (⟨x, hxmem⟩ : ↥((insert x C₀ : Finset V) : Set V)) ≠ ⟨c₀, hcmem⟩ := by
      intro h
      apply hxnC
      have : x = c₀ := congrArg Subtype.val h
      rw [this]; exact hc₀
    obtain ⟨p⟩ := hCconn.preconnected ⟨x, hxmem⟩ ⟨c₀, hcmem⟩
    cases p with
    | nil => exact absurd rfl hne
    | cons hadj q =>
        rename_i z
        refine ⟨z.val, ?_, ?_⟩
        · have hzmem := z.property
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hzmem
          have hzx : z.val ≠ x := by
            intro h
            have : G.Adj x x := by
              have : G.Adj x z.val := by simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
              rw [h] at this
              exact this
            exact this.ne rfl
          rcases hzmem with h | h
          · exact absurd h hzx
          · exact h
        · simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
  obtain ⟨bz, hbz0, hxbz⟩ := hxneighbor B₀ hBne hxnB hBconn
  obtain ⟨az, haz0, hxaz⟩ := hxneighbor A₀ hAne hxnA hAconn
  have hbznotA : bz ∉ A := by
    rw [hA, Finset.mem_insert]; push Not
    exact ⟨fun h => hxnB (h ▸ hbz0), fun h => (Finset.disjoint_left.mp hdisj h) hbz0⟩
  have haznotB : az ∉ B := by
    rw [hB, Finset.mem_insert]; push Not
    exact ⟨fun h => hxnA (h ▸ haz0), fun h => (Finset.disjoint_right.mp hdisj h) haz0⟩
  have hdeg : ∀ v, G.degree v ≤ 3 := fun v => le_of_eq (hreg v)
  have hApiece := colorable_induce_of_outside_neighbor G (A : Set V) hAconn
    hdeg ⟨x, hxA⟩ bz hbznotA hxbz
  have hBpiece := colorable_induce_of_outside_neighbor G (B : Set V) hBconn
    hdeg ⟨x, hxB⟩ az haznotB hxaz
  have hcross : ∀ u ∈ A, ∀ w ∈ B, u ≠ x → w ≠ x → ¬ G.Adj u w := by
    intro u hu w hw hux hwx
    have huA0 : u ∈ A₀ := by
      rw [hA, Finset.mem_insert] at hu; exact hu.resolve_left hux
    have hwB0 : w ∈ B₀ := by
      rw [hB, Finset.mem_insert] at hw; exact hw.resolve_left hwx
    exact hnocross u huA0 w hwB0
  exact colorable_glue_at_vertex G A B x hcover hxA hxB hcross hApiece hBpiece

end BrooksSubcubic
end
