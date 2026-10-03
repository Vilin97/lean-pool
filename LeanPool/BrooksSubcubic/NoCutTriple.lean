/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.CandidatePair
public import LeanPool.BrooksSubcubic.Endblock
public import LeanPool.BrooksSubcubic.K4Free

/-!
# A good triple in a cubic graph without cut vertices

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section
open SimpleGraph Finset

namespace BrooksSubcubic

theorem cubic_good_triple_of_no_cut {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v : V, G.degree v = 3)
    (hK4 : G.CliqueFree 4)
    (hnocut : ∀ x : V, (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  classical
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨a₀, b₀, hva, hvb, hab, hnab⟩ :=
    BrooksSubcubic.exists_nonadj_pair_of_cubic_K4free G hK4 (hreg v)
  obtain ⟨u, b, hua, hub, hnab', hba⟩ :=
    BrooksSubcubic.exists_dist2_pair G hconn hab.symm hnab
  by_cases hall : ∀ y, y ≠ a₀ → (G.induce (({a₀, y} : Set V)ᶜ)).Connected
  · exact ⟨u, a₀, b, hua.symm, hub, hba.symm, hnab', hall b hba⟩
  · push Not at hall
    obtain ⟨y, hay, hcut⟩ := hall
    by_cases hb0y : b₀ = y
    · have hvay : v ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hva.ne, fun hvy => hvb.ne (hvy.trans hb0y.symm)⟩
      exact BrooksSubcubic.good_triple_of_two_cut G hreg hnocut a₀ y v hay.symm hvay hcut
    · have hb0ay : b₀ ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hab.symm, hb0y⟩
      exact BrooksSubcubic.good_triple_of_two_cut G hreg hnocut a₀ y b₀ hay.symm hb0ay hcut
end BrooksSubcubic
end
