/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.ComponentAttachments

/-!
# Subcubic Brooks theorem: CutVertex

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- `x` is a cut vertex of `G` when deleting it disconnects `G`. -/
def IsCutVertex (G : SimpleGraph V) (x : V) : Prop :=
  ¬ (G.induce ({x}ᶜ : Set V)).Connected

omit [Fintype V] in
/-- A cut vertex with nonempty complement yields two mutually unreachable vertices. -/
theorem exists_unreachable_of_cutVertex (G : SimpleGraph V) (x : V)
    (w : V) (hw : w ≠ x) (hcut : IsCutVertex G x) :
    ∃ (d e : V) (hd : d ≠ x) (he : e ≠ x),
      ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have hwmem : w ∈ ({x}ᶜ : Set V) := by simpa using hw
  have : Nonempty ↥({x}ᶜ : Set V) := ⟨⟨w, hwmem⟩⟩
  have hnp : ¬ (G.induce ({x}ᶜ : Set V)).Preconnected := by
    intro hp
    exact hcut ((SimpleGraph.connected_iff _).mpr ⟨hp, inferInstance⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, v, huv⟩ := hnp
  exact ⟨u.val, v.val, u.property, v.property, huv⟩

omit [Fintype V] in
/-- If deleting a set `S` disconnects `G` (and `Sᶜ` is nonempty via
`w ∉ S`), there are two vertices outside `S` that are mutually unreachable in `G − S`. The 2-cut
case `S = {a₀, y}` feeds the endblock analysis of Lovász Case 2. -/
theorem exists_unreachable_of_notConnected (G : SimpleGraph V)
    (S : Set V) (w : V) (hw : w ∉ S)
    (hdis : ¬ (G.induce (Sᶜ : Set V)).Connected) :
    ∃ (d e : V) (hd : d ∉ S) (he : e ∉ S),
      ¬ (G.induce (Sᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have : Nonempty ↥(Sᶜ : Set V) := ⟨⟨w, hw⟩⟩
  have hnp : ¬ (G.induce (Sᶜ : Set V)).Preconnected := by
    intro hp
    exact hdis ((SimpleGraph.connected_iff _).mpr ⟨hp, inferInstance⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hnp
  obtain ⟨u, v, huv⟩ := hnp
  exact ⟨u.val, v.val, u.property, v.property, huv⟩

omit [Fintype V] in
/-- **Component touches the cut.** In a connected `G`, for any separating set `S` (nonempty, witness
`s0 ∈ S`) and any `d ∉ S`, the `G−S`-component of `d` contains a vertex adjacent to some cut vertex
`s ∈ S`. (Else that component is closed under all `G`-adjacency, hence unreachable from `S`,
contradicting connectedness.) With `S = {a₀, y}` this says every component of `G−{a₀,y}` touches
`a₀` or `y` — the entry point to Lovász's endblock analysis. -/
theorem class_touches_cut (G : SimpleGraph V) (hconn : G.Connected)
    (S : Set V) {d : V} (hd : d ∉ S) {s0 : V} (hs0 : s0 ∈ S) :
    ∃ (w : ↥(Sᶜ : Set V)) (s : V), s ∈ S ∧ G.Adj w.val s ∧
      (G.induce (Sᶜ : Set V)).connectedComponentMk w =
      (G.induce (Sᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := (G.induce (Sᶜ : Set V)).connectedComponentMk ⟨d, hd⟩ with hDdef
  set W : Set V := {v | ∃ hv : v ∈ (Sᶜ : Set V),
      (G.induce (Sᶜ : Set V)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdW : d ∈ W := ⟨hd, rfl⟩
  have hs0W : s0 ∉ W := by rintro ⟨hv, _⟩; exact hv hs0
  have hclosed : ∀ w ∈ W, ∀ y, G.Adj w y → y ∈ W := by
    rintro w ⟨hwS, hwD⟩ y hadj
    by_cases hyS : y ∈ S
    · exact absurd hwD (hcon ⟨w, hwS⟩ y hyS hadj)
    · have hyc : y ∈ (Sᶜ : Set V) := hyS
      refine ⟨hyc, ?_⟩
      have hadj' : (G.induce (Sᶜ : Set V)).Adj ⟨w, hwS⟩ ⟨y, hyc⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hconn.preconnected d s0
  exact hs0W (mem_of_walk_closed G W hclosed p hdW)

omit [Fintype V] in
/-- **`a₀` reaches every component of `G−{a₀,y}`.** If `G−y` is connected and `a₀ ≠ y`, then for
every `d ∉ {a₀,y}`, `a₀` has a neighbour in `d`'s `G−{a₀,y}`-component. (In `H = G−y`, `a₀` is a
cut vertex and every component of `H−a₀ = G−{a₀,y}` hangs off `a₀`.) This yields the candidate pair
`a,b ∈ N(a₀)` in two distinct components for Lovász Case 2. -/
theorem a0_adj_component (G : SimpleGraph V)
    {a0 y : V} (hay : a0 ≠ y) (hHconn : (G.induce ({y}ᶜ : Set V)).Connected)
    {d : V} (hd : d ∈ (({a0, y} : Set V)ᶜ)) :
    ∃ (z : V) (hz : z ∈ (({a0, y} : Set V)ᶜ)), G.Adj a0 z ∧
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ =
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ with hDdef
  set W : Set V := {v | ∃ hv : v ∈ (({a0, y} : Set V)ᶜ),
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨v, hv⟩ = D} with hWdef
  have hdy : d ≠ y := fun h => hd (by rw [h]; exact Or.inr rfl)
  have hay' : a0 ≠ y := hay
  set W' : Set ↥({y}ᶜ : Set V) := {v' | v'.val ∈ W} with hW'def
  have hdmem : d ∈ ({y}ᶜ : Set V) := hdy
  have hdW' : (⟨d, hdmem⟩ : ↥({y}ᶜ : Set V)) ∈ W' := ⟨hd, rfl⟩
  have hamem : a0 ∈ ({y}ᶜ : Set V) := hay'
  have haW' : (⟨a0, hamem⟩ : ↥({y}ᶜ : Set V)) ∉ W' := by
    rintro ⟨hv, _⟩
    exact hv (Or.inl rfl)
  have hclosed : ∀ w' ∈ W', ∀ z', (G.induce ({y}ᶜ : Set V)).Adj w' z' → z' ∈ W' := by
    rintro w' ⟨hwS, hwD⟩ z' hadj
    have hadjG : G.Adj w'.val z'.val := by
      simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
    have hz'y : z'.val ≠ y := z'.property
    by_cases hz'a0 : z'.val = a0
    · -- a0 adjacent to w'.val ∈ D's class ⇒ contradicts hcon
      exfalso
      have : G.Adj a0 w'.val := by rw [← hz'a0]; exact hadjG.symm
      exact (hcon w'.val hwS this) hwD.symm
    · have hz'mem : z'.val ∈ (({a0, y} : Set V)ᶜ) := by
        intro hmem; rcases hmem with h | h
        · exact hz'a0 h
        · exact hz'y h
      refine ⟨hz'mem, ?_⟩
      have hadj' : (G.induce (({a0, y} : Set V)ᶜ)).Adj ⟨w'.val, hwS⟩ ⟨z'.val, hz'mem⟩ := by
        simpa [SimpleGraph.induce, SimpleGraph.comap] using hadjG
      rw [← hwD]
      exact (ConnectedComponent.eq.mpr hadj'.reachable).symm
  obtain ⟨p⟩ := hHconn.preconnected ⟨d, hdmem⟩ ⟨a0, hamem⟩
  exact haW' (mem_of_walk_closed _ W' hclosed p hdW')

omit [Fintype V] in
/-- **Candidate pair for Lovász Case 2.** If `{a₀,y}` is a 2-cut (`G−{a₀,y}` disconnected, witnessed
by `w ∉ {a₀,y}`) and `G−y` is connected, then `a₀` has two neighbours `a,b` in distinct
`G−{a₀,y}`-components — hence `a ≠ b` and `¬ G.Adj a b`. Everything of Lovász Case 2 except
`G−{a,b}` connected (the leaf/non-cut refinement). -/
theorem exists_cut_candidate_pair (G : SimpleGraph V)
    {a0 y : V} (hay : a0 ≠ y)
    (hHy : (G.induce ({y}ᶜ : Set V)).Connected)
    (w : V) (hw : w ∉ ({a0, y} : Set V))
    (hcut : ¬ (G.induce (({a0, y} : Set V)ᶜ)).Connected) :
    ∃ a b, G.Adj a0 a ∧ G.Adj a0 b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  obtain ⟨d, e, hd, he, huv⟩ := exists_unreachable_of_notConnected G ({a0, y} : Set V) w hw hcut
  obtain ⟨a, ha_mem, hAa, hcomp_a⟩ := a0_adj_component G hay hHy hd
  obtain ⟨b, hb_mem, hAb, hcomp_b⟩ := a0_adj_component G hay hHy he
  have hde : (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ ≠
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨e, he⟩ :=
    fun h => huv (ConnectedComponent.eq.mp h)
  have hab_comp : (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha_mem⟩ ≠
      (G.induce (({a0, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb_mem⟩ := by
    rw [← hcomp_a, ← hcomp_b]; exact hde
  refine ⟨a, b, hAa, hAb, ?_, ?_⟩
  · -- a ≠ b
    intro h; apply hab_comp; subst h
    congr 1
  · -- ¬ G.Adj a b
    intro hadj
    apply hab_comp
    have hadj' : (G.induce (({a0, y} : Set V)ᶜ)).Adj ⟨a, ha_mem⟩ ⟨b, hb_mem⟩ := by
      simpa [SimpleGraph.induce, SimpleGraph.comap] using hadj
    exact ConnectedComponent.eq.mpr hadj'.reachable

end BrooksSubcubic
end
