/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.ComponentAttachments

/-!
# Subcubic Brooks theorem: CandidatePair

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- **P2 (distance-2 candidate).** In a connected `G`, if `x` has a non-neighbour `w ≠ x`, then `x`
has a neighbour `u` which has a neighbour `b` with `¬ G.Adj x b` and `b ≠ x`. (I.e. a vertex `b` at
distance 2 from `x`, with common neighbour `u`.) Proof: the set `{x} ∪ N(x)` is not closed under
adjacency (it omits `w` yet `x` reaches `w`), so some neighbour of `x` has an edge leaving it. -/
theorem exists_dist2_pair (G : SimpleGraph V) (hconn : G.Connected)
    {x w : V} (hwx : w ≠ x) (hxw : ¬ G.Adj x w) :
    ∃ u b, G.Adj x u ∧ G.Adj u b ∧ ¬ G.Adj x b ∧ b ≠ x := by
  classical
  set S : Set V := {y | y = x ∨ G.Adj x y} with hSdef
  have hxS : x ∈ S := Or.inl rfl
  have hwS : w ∉ S := by
    intro hmem; rcases hmem with heq | hadj
    · exact hwx heq
    · exact hxw hadj
  have hnotclosed : ¬ ∀ s ∈ S, ∀ y, G.Adj s y → y ∈ S := by
    intro hcl
    obtain ⟨p⟩ := hconn.preconnected x w
    exact hwS (mem_of_walk_closed G S hcl p hxS)
  push Not at hnotclosed
  obtain ⟨s, hsS, y, hsy, hyS⟩ := hnotclosed
  have hyx : y ≠ x := by rintro rfl; exact hyS (Or.inl rfl)
  have hxy : ¬ G.Adj x y := fun h => hyS (Or.inr h)
  rcases hsS with rfl | hxs
  · exact absurd hsy hxy
  · exact ⟨s, y, hxs, hsy, hxy, hyx⟩

omit [Fintype V] in
/-- G ≠ ⊤ ⇒ some vertex has a non-neighbour (≠ itself). -/
theorem exists_nonneighbor_of_ne_top (G : SimpleGraph V)
    (hne : G ≠ ⊤) : ∃ x w, w ≠ x ∧ ¬ G.Adj x w := by
  classical
  by_contra hcon
  push Not at hcon
  apply hne
  ext u v
  simp only [SimpleGraph.top_adj]
  constructor
  · exact fun h => h.ne
  · intro huv
    exact hcon u v huv.symm

omit [Fintype V] in
/-- **Reduction of the bad-graph lemma to its kernel.** Contrapositive shape: if `G` is connected,
`G ≠ ⊤`, and `G` has no good triple, then every good-triple *candidate* `(v₀,a,b)` has `G−{a,b}`
disconnected. In particular a candidate exists (via `exists_dist2_pair`), so the residual content
is purely: "every distance-2 pair is a 2-cut ⇒ `G` is 2-regular". -/
theorem exists_candidate_of_ne_top (G : SimpleGraph V)
    (hconn : G.Connected) (hne : G ≠ ⊤) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b := by
  classical
  obtain ⟨x, w, hwx, hxw⟩ := exists_nonneighbor_of_ne_top G hne
  obtain ⟨u, b, hxu, hub, hxb, hbx⟩ := exists_dist2_pair G hconn hwx hxw
  exact ⟨u, x, b, hxu.symm, hub, hbx.symm, hxb⟩

end BrooksSubcubic
end
