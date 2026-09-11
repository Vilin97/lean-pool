/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

/-!
# Elementary clique-number facts

These lemmas make the paper's assumptions `n ≥ 1` and `ω ≥ 1` explicit and
isolate the edgeless `ω = 1` case. The Turán factor is the coefficient
`1 - 1 / ω(G)` in Turán-type bounds.

This module is copied, up to the namespace, from `SqOmega/Graph.lean` in
<https://github.com/ShengtongZhang-alt/SqOmega> (Liu, Tang, Zhang).
-/

namespace BollobasNikiforov

variable {V : Type*}

/-- The coefficient `1 - 1 / ω(G)` appearing in Turán-type bounds. -/
noncomputable def turanFactor (G : SimpleGraph V) : ℝ :=
  1 - 1 / (G.cliqueNum : ℝ)

namespace SimpleGraph

variable [Finite V]

/-- A graph on a nonempty finite vertex type has clique number at least one. -/
lemma one_le_cliqueNum (G : SimpleGraph V) [Nonempty V] :
    1 ≤ G.cliqueNum := by
  classical
  let v : V := Classical.choice inferInstance
  have hc : G.IsClique (↑({v} : Finset V) : Set V) :=
    by simp
  simpa using hc.card_le_cliqueNum

/-- The endpoints of an edge give a two-vertex clique. -/
lemma two_le_cliqueNum_of_adj (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) :
    2 ≤ G.cliqueNum := by
  classical
  have hc : G.IsClique (↑({u, v} : Finset V) : Set V) :=
    by simpa using G.isClique_pair.mpr (fun _ ↦ huv)
  simpa [huv.ne] using hc.card_le_cliqueNum

/-- On a nonempty graph, clique number one forces the graph to be edgeless. -/
lemma eq_bot_of_cliqueNum_eq_one (G : SimpleGraph V)
    (hω : G.cliqueNum = 1) :
    G = ⊥ := by
  rw [SimpleGraph.eq_bot_iff_forall_not_adj]
  intro u v huv
  have htwo := two_le_cliqueNum_of_adj G huv
  omega

/-- On a nonempty graph, clique number is one exactly in the edgeless case. -/
lemma cliqueNum_eq_one_iff_eq_bot (G : SimpleGraph V) [Nonempty V] :
    G.cliqueNum = 1 ↔ G = ⊥ := by
  classical
  constructor
  · exact eq_bot_of_cliqueNum_eq_one G
  · rintro rfl
    apply le_antisymm
    · obtain ⟨s, hs⟩ := (⊥ : SimpleGraph V).exists_isNClique_cliqueNum
      have hsub := hs.isClique.subsingleton
      have hcard : s.card ≤ 1 :=
        Finset.card_le_one_iff_subsingleton.mpr hsub
      rwa [hs.card_eq] at hcard
    · exact one_le_cliqueNum (⊥ : SimpleGraph V)

end SimpleGraph

/-- The Turán coefficient is nonnegative for a graph with at least one vertex. -/
lemma turanFactor_nonneg (G : SimpleGraph V) [Finite V] [Nonempty V] :
    0 ≤ turanFactor G := by
  have hω : 1 ≤ (G.cliqueNum : ℝ) := by
    exact_mod_cast SimpleGraph.one_le_cliqueNum G
  have hωpos : 0 < (G.cliqueNum : ℝ) :=
    zero_lt_one.trans_le hω
  have hinv : (G.cliqueNum : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ hωpos).2 hω
  simpa [turanFactor, one_div] using sub_nonneg.mpr hinv

/-- The Turán coefficient is positive when the clique number is at least two. -/
lemma turanFactor_pos (G : SimpleGraph V) (hω : 2 ≤ G.cliqueNum) :
    0 < turanFactor G := by
  have hωr : 1 < (G.cliqueNum : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hω)
  have hinv : (G.cliqueNum : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hωr
  simpa [turanFactor, one_div] using sub_pos.mpr hinv

end BollobasNikiforov
