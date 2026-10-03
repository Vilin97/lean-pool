/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.ComponentAttachments

/-!
# Subcubic Brooks theorem: CutPartition

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A union of components of the vertex-deleted graph, each attached to the deleted vertex,
becomes connected when that vertex is inserted. -/
lemma connected_induce_insert_of_component_neighbors (G : SimpleGraph V)
    (x : V) (A : Finset V)
    (P : (G.induce ({x}ᶜ : Set V)).ConnectedComponent → Prop)
    (hmem : ∀ v, v ∈ A ↔ ∃ hv : v ≠ x,
      P ((G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hv⟩))
    (hneigh : ∀ C, P C → ∃ z, G.Adj x z ∧ ∃ hz : z ≠ x,
      (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨z, hz⟩ = C) :
    (G.induce ((insert x A : Finset V) : Set V)).Connected := by
  classical
  have hx_reach : ∀ (v : V) (hv : v ∈ A),
      (G.induce (↑(insert x A))).Reachable ⟨x, by simp⟩ ⟨v, by simp [hv]⟩ := by
    intro v hvA
    obtain ⟨hvx, hPC⟩ := (hmem v).mp hvA
    obtain ⟨z, hxz, hzx, hzcomp⟩ := hneigh _ hPC
    have hzA : z ∈ A := (hmem z).mpr ⟨hzx, hzcomp ▸ hPC⟩
    obtain ⟨p⟩ := ConnectedComponent.eq.mp hzcomp
    have hpA : ∀ w ∈ p.support, w.val ∈ A := by
      intro w hw
      apply (hmem w.val).mpr
      refine ⟨w.property, ?_⟩
      have hcomp := ConnectedComponent.eq.mpr (p.takeUntil w hw).reachable
      rw [← hcomp, hzcomp]
      exact hPC
    let q := p.map (Embedding.induce ({x}ᶜ : Set V)).toHom
    have hq : ∀ w ∈ q.support, w ∈ (↑(insert x A) : Set V) := by
      intro w hw
      change w ∈ (p.map (Embedding.induce ({x}ᶜ : Set V)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      exact Finset.mem_insert_of_mem (hpA w' hw')
    have hzv : (G.induce (↑(insert x A))).Reachable
        ⟨z, by simp [hzA]⟩ ⟨v, by simp [hvA]⟩ := ⟨q.induce _ hq⟩
    exact (show (G.induce (↑(insert x A))).Adj
      ⟨x, by simp⟩ ⟨z, by simp [hzA]⟩ from hxz).reachable.trans hzv
  rw [connected_iff]
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    simp only [Finset.mem_insert, Finset.mem_coe] at hu hv
    rcases hu with rfl | huA <;> rcases hv with rfl | hvA
    · exact Reachable.rfl
    · exact hx_reach v hvA
    · exact (hx_reach u huA).symm
    · exact (hx_reach u huA).symm.trans (hx_reach v hvA)
  · exact ⟨⟨x, by simp⟩⟩

theorem cut_partition_of_unreachable (G : SimpleGraph V)
    (hconn : G.Connected) (x d e : V) (hd : d ≠ x) (he : e ≠ x)
    (hsep : ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩) :
    ∃ (A₀ B₀ : Finset V), A₀.Nonempty ∧ B₀.Nonempty ∧ x ∉ A₀ ∧ x ∉ B₀ ∧
      Disjoint A₀ B₀ ∧ insert x (A₀ ∪ B₀) = Finset.univ ∧
      (∀ a ∈ A₀, ∀ b ∈ B₀, ¬ G.Adj a b) ∧
      (G.induce ((insert x A₀ : Finset V) : Set V)).Connected ∧
      (G.induce ((insert x B₀ : Finset V) : Set V)).Connected := by
  classical
  let preB₀ : Finset {v : V // v ≠ x} :=
    Finset.univ.filter (fun v => (G.induce ({x}ᶜ : Set V)).Reachable ⟨e, he⟩ v)
  let B₀ : Finset V := preB₀.map ⟨Subtype.val, Subtype.val_injective⟩
  let A₀ : Finset V := (Finset.univ \ {x}) \ B₀
  have hB₀_mem : ∀ v, v ∈ B₀ ↔ ∃ (w : {v : V // v ≠ x}), w ∈ preB₀ ∧ w.val = v :=
    fun v => Finset.mem_map
  have hA₀_mem : ∀ v, v ∈ A₀ ↔ v ≠ x ∧ v ∉ B₀ := fun v => by simp [A₀]
  refine ⟨A₀, B₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · use d
    simp only [hA₀_mem]
    refine ⟨hd, ?_⟩
    simp only [hB₀_mem]
    intro ⟨w, hw_mem, hw_eq⟩
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
    have hw_eq' : w = ⟨d, hd⟩ := Subtype.ext hw_eq
    rw [hw_eq'] at hw_mem
    exact hsep hw_mem.symm
  · use e
    simp only [hB₀_mem]
    use ⟨e, he⟩
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact SimpleGraph.Reachable.rfl
  · rw [hA₀_mem]
    simp
  · rw [hB₀_mem]
    intro ⟨w, _, hw_eq⟩
    have : w.val = x := hw_eq
    exact w.property this
  · rw [Finset.disjoint_left]
    intro a haA haB
    rw [hA₀_mem] at haA
    exact haA.2 haB
  · ext v
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hvx : v = x
    case pos => left; exact hvx
    case neg =>
      by_cases hvB₀ : v ∈ B₀
      · right; exact Or.inr hvB₀
      · right
        rw [hA₀_mem]
        exact Or.inl ⟨hvx, hvB₀⟩
  · intro a haA b hbB hab
    rw [hA₀_mem] at haA
    rw [hB₀_mem] at hbB
    obtain ⟨⟨vb, hvb⟩, hve_mem, hvb_eq⟩ := hbB
    simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hve_mem
    have h_a_in_B₀ : a ∈ B₀ := by
      rw [hB₀_mem]
      use ⟨a, haA.1⟩
      simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      have hb_eq : b = vb := hvb_eq.symm
      have hab' : (G.induce ({x}ᶜ : Set V)).Adj ⟨a, haA.1⟩ ⟨vb, hvb⟩ := by
        rw [hb_eq] at hab
        change G.Adj a vb
        exact hab
      exact SimpleGraph.Reachable.trans hve_mem hab'.reachable.symm
    exact haA.2 h_a_in_B₀
  · apply connected_induce_insert_of_component_neighbors G x A₀
      (fun C => C ≠ (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩)
    · intro v
      rw [hA₀_mem]
      apply Iff.intro
      · intro ⟨hvx, hvB₀⟩
        refine ⟨hvx, ?_⟩
        intro h
        apply hvB₀
        apply (hB₀_mem v).mpr
        refine ⟨⟨v, hvx⟩, ?_, rfl⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ConnectedComponent.eq.mp h.symm
      · intro ⟨hvx, hPC⟩
        refine ⟨hvx, ?_⟩
        intro hvB₀
        rw [hB₀_mem] at hvB₀
        obtain ⟨w, hw_mem, hw_eq⟩ := hvB₀
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
        have h_mk_eq : (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩ =
            (G.induce ({x}ᶜ : Set V)).connectedComponentMk w :=
          ConnectedComponent.eq.mpr hw_mem
        have hw_eq' : w = (⟨v, hvx⟩ : {v : V // v ≠ x}) := Subtype.ext hw_eq
        rw [hw_eq'] at h_mk_eq
        exact hPC h_mk_eq.symm
    · intro C hC
      obtain ⟨⟨v, hv⟩, hv_rep⟩ := C.exists_rep
      have hvx : v ≠ x := hv
      have hC_eq : C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨v, hvx⟩ := by
        rw [← hv_rep]
        rfl
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn hvx
      refine ⟨z, hzx, hzx_ne, ?_⟩
      exact Eq.trans hz_comp.symm hC_eq.symm
  · apply connected_induce_insert_of_component_neighbors G x B₀
      (fun C => C = (G.induce ({x}ᶜ : Set V)).connectedComponentMk ⟨e, he⟩)
    · intro v
      rw [hB₀_mem]
      constructor
      · rintro ⟨⟨w, hw⟩, hw_mem, hw_eq⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and] at hw_mem
        have hw_ne : v ≠ x := hw_eq ▸ hw
        refine ⟨hw_ne, ?_⟩
        simp only [← hw_eq]
        exact (ConnectedComponent.eq.mpr hw_mem.symm)
      · rintro ⟨hvx, hPC⟩
        use ⟨v, hvx⟩
        simp only [preB₀, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (ConnectedComponent.eq.mp hPC).symm
    · intro C hCeq
      rw [hCeq]
      obtain ⟨z, hzx, hzx_ne, hz_comp⟩ := exists_adj_in_class G hconn he
      exact ⟨z, hzx, hzx_ne, hz_comp.symm⟩

end BrooksSubcubic
end
