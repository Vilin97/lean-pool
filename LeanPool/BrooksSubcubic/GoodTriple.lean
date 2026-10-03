/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.NoCutTriple

/-!
# Subcubic Brooks theorem: GoodTriple

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section
open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- A bad induced path can be moved across its first endpoint: deleting its endpoints gives
a 2-cut, and `exists_cut_candidate_pair` supplies a new induced path centred at that endpoint. -/
theorem next_cut_candidate
    (G : SimpleGraph V)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set V)).Connected)
    (v a b : V) (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (hcut : ¬ (G.induce (({a, b} : Set V)ᶜ)).Connected) :
    ∃ c d, G.Adj a c ∧ G.Adj a d ∧ c ≠ d ∧ ¬ G.Adj c d := by
  classical
  have hvab : v ∉ ({a, b} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hva.ne, hvb.ne⟩
  exact exists_cut_candidate_pair G hab (hdel b) v hvab hcut

/-- Contrapositive form of the Lovász lemma specialized to cubic K₄-free graphs. -/
theorem good_triple_of_all_vertex_deletions_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected :=
  cubic_good_triple_of_no_cut G hconn hreg hK4 hdel

/-- **Lovász cut-existence step.** A connected cubic K₄-free graph with no good triple
has a cut vertex, presented directly by two unreachable vertices after deletion. -/
theorem cut_witness_of_no_good_triple
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v, G.degree v = 3) (hK4 : G.CliqueFree 4)
    (hng : ¬ ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected) :
    ∃ (x d e : V) (hd : d ≠ x) (he : e ≠ x),
      ¬ (G.induce ({x}ᶜ : Set V)).Reachable ⟨d, hd⟩ ⟨e, he⟩ := by
  classical
  have hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set V)).Connected := by
    by_contra h
    push Not at h
    exact hng (good_triple_of_all_vertex_deletions_connected G hconn hreg hK4 h)
  obtain ⟨x, hx⟩ := hcut
  obtain ⟨a, b, hxa, hxb, hab, hnab⟩ :=
    exists_nonadj_pair_of_cubic_K4free G hK4 (hreg x)
  obtain ⟨d, e, hd, he, hde⟩ := exists_unreachable_of_cutVertex G x a hxa.ne' hx
  exact ⟨x, d, e, hd, he, hde⟩

end BrooksSubcubic
end
