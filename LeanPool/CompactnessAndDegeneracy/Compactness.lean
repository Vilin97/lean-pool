/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import Mathlib

namespace CompactnessConjecture

noncomputable section Foundations

open Filter Finset SimpleGraph
open scoped Topology

structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

def CompactnessConjectureStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family → IsCompactFamily family

theorem FamilyFree.member {family : Finset FiniteGraph}
    {forbidden : FiniteGraph} (hmem : forbidden ∈ family)
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree family host) : forbidden.graph.Free host :=
  hfree forbidden hmem

end Foundations

noncomputable section DensityReduction

open Finset SimpleGraph
open scoped Classical

lemma edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))

lemma degree_eq_natCard_neighborSet {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.card_neighborSet_eq_degree G v).symm

def booleanCut {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : SimpleGraph V :=
  G ⊓ (⊤ : SimpleGraph Bool).comap color

@[simp]
lemma booleanCut_adj {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v :=
  Iff.rfl

instance booleanCutDecidableRel {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) :
    DecidableRel (booleanCut G color).Adj :=
  inferInstanceAs
    (DecidableRel fun u v => G.Adj u v ∧ color u ≠ color v)

lemma booleanCut_le {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : booleanCut G color ≤ G := by
  intro u v huv
  exact huv.1

lemma booleanCut_isBipartite {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : (booleanCut G color).IsBipartite := by
  simpa only [Fintype.card_bool] using
    (SimpleGraph.Coloring.mk (G := booleanCut G color) color (fun h => h.2)).colorable

def flipBooleanColor {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) : V → Bool :=
  Function.update color v (! color v)

@[simp]
lemma flipBooleanColor_self {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by
  simp only [flipBooleanColor, Function.update_self]

lemma booleanCut_deleteIncidence_flip
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).deleteIncidenceSet v =
      (booleanCut G color).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, booleanCut_adj]
  by_cases hx : x = v
  · subst x
    simp only [flipBooleanColor_self, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_eq_not, not_true_eq_false, false_and,
      and_false]
  by_cases hy : y = v
  · subst y
    simp only [flipBooleanColor_self, ne_eq, Bool.not_eq_not, not_true_eq_false, and_false]
  simp only [flipBooleanColor, ne_eq, hx, not_false_eq_true, Function.update_of_ne, hy, and_self, and_true]

lemma booleanCut_flip_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).neighborFinset v =
      G.neighborFinset v \ (booleanCut G color).neighborFinset v := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    booleanCut_adj]
  by_cases hwv : w = v
  · subst w
    simp only [SimpleGraph.irrefl, flipBooleanColor_self, ne_eq, not_true_eq_false, and_self, not_false_eq_true,
      and_true]
  · cases hcv : color v <;> cases hcw : color w <;>
      simp [flipBooleanColor, hwv, hcv, hcw]

lemma booleanCut_flip_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).degree v +
        (booleanCut G color).degree v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      booleanCut_flip_neighborFinset]
  apply Finset.card_sdiff_add_card_eq_card
  intro w hw
  have hadj : (booleanCut G color).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw
  simpa only [SimpleGraph.mem_neighborFinset] using hadj.1

theorem exists_maximum_booleanCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ color : V → Bool, ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card := by
  classical
  obtain ⟨color, _, hcolor⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool))
    (fun candidate => (booleanCut G candidate).edgeFinset.card)
    (Finset.univ_nonempty)
  exact ⟨color, fun other => hcolor other (Finset.mem_univ other)⟩

lemma maximum_booleanCut_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hmax : ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card)
    (v : V) :
    G.degree v ≤ 2 * (booleanCut G color).degree v := by
  classical
  let flipped := flipBooleanColor color v
  have hflipped := hmax flipped
  have hdeleted := congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet)
    (booleanCut_deleteIncidence_flip G color v)
  have hedge :
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v := by
    calc
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        ((booleanCut G flipped).deleteIncidenceSet v).edgeFinset.card :=
        (SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G flipped) v).symm
      _ = Nat.card ((booleanCut G flipped).deleteIncidenceSet v).edgeSet :=
        edgeFinset_card_eq_natCard _
      _ = Nat.card ((booleanCut G color).deleteIncidenceSet v).edgeSet :=
        hdeleted
      _ = ((booleanCut G color).deleteIncidenceSet v).edgeFinset.card :=
        (edgeFinset_card_eq_natCard _).symm
      _ = (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v :=
        SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G color) v
  have hflipDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G flipped) v
  have hcutDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G color) v
  have hpartition := booleanCut_flip_degree_add G color v
  change (booleanCut G flipped).degree v +
    (booleanCut G color).degree v = G.degree v at hpartition
  omega

theorem exists_bipartite_half_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ B : SimpleGraph V,
      B.IsBipartite ∧ B ≤ G ∧
      G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  obtain ⟨color, hmax⟩ := exists_maximum_booleanCut G
  refine ⟨booleanCut G color, booleanCut_isBipartite G color,
    booleanCut_le G color, ?_⟩
  have hsum :
      2 * G.edgeFinset.card ≤
        2 * (2 * (booleanCut G color).edgeFinset.card) := by
    calc
      2 * G.edgeFinset.card = ∑ v : V, G.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
      _ ≤ ∑ v : V, 2 * (booleanCut G color).degree v :=
        Finset.sum_le_sum fun v _ =>
          maximum_booleanCut_degree G color hmax v
      _ = 2 * (2 * (booleanCut G color).edgeFinset.card) := by
        rw [← Finset.mul_sum,
          SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hhalf := Nat.le_of_mul_le_mul_left hsum (by omega)
  simpa only [edgeFinset_card_eq_natCard] using hhalf

lemma natCard_support_le_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.support ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Finite.card_subtype_le (fun v : V => v ∈ G.support))

lemma natCard_support_deleteIncidence_add_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : v ∈ G.support) :
    Nat.card (G.deleteIncidenceSet v).support + 1 ≤
      Nat.card G.support := by
  have hdrop := SimpleGraph.card_support_deleteIncidenceSet G hv
  have hpositive : 0 < Nat.card G.support :=
    Finite.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  simp only [Nat.card_eq_fintype_card] at hpositive ⊢
  omega

noncomputable def sharpPruningPotential {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * Fintype.card V * Nat.card H.edgeSet +
    originalEdges * (Fintype.card V - Nat.card H.support)

noncomputable def sharpPruningScore {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * sharpPruningPotential originalEdges H +
    (if 0 < Nat.card H.edgeSet then 1 else 0)

theorem exists_maximum_sharp_pruning_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (base : SimpleGraph V) (originalEdges : ℕ) :
    ∃ H : SimpleGraph V, H ≤ base ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningPotential originalEdges D ≤
          sharpPruningPotential originalEdges H) ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningScore originalEdges D ≤
          sharpPruningScore originalEdges H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => H ≤ base)
  have hnonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp only [mem_filter, mem_univ, bot_le, and_self, candidates]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    candidates (sharpPruningScore originalEdges) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2, ?_, ?_⟩
  · intro D hD
    have hscore := hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
    unfold sharpPruningScore at hscore
    split_ifs at hscore <;> omega
  · intro D hD
    exact hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)

lemma maximum_sharp_pruning_subgraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (base H : SimpleGraph V) [DecidableRel H.Adj]
    (originalEdges : ℕ) (hHB : H ≤ base)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningPotential originalEdges D ≤
        sharpPruningPotential originalEdges H)
    {v : V} (hv : v ∈ H.support) :
    originalEdges ≤ 2 * Fintype.card V * H.degree v := by
  classical
  let D := H.deleteIncidenceSet v
  have hDB : D ≤ base :=
    le_trans (SimpleGraph.deleteIncidenceSet_le H v) hHB
  have hscore := hmax D hDB
  have hdrop : Nat.card D.support + 1 ≤ Nat.card H.support :=
    natCard_support_deleteIncidence_add_one_le H hv
  have hsupport : Nat.card H.support ≤ Fintype.card V :=
    natCard_support_le_card H
  have hcomplement :
      Fintype.card V - Nat.card H.support + 1 ≤
        Fintype.card V - Nat.card D.support := by
    omega
  have hweightedComplement :
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges ≤
        originalEdges * (Fintype.card V - Nat.card D.support) := by
    calc
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges =
        originalEdges * (Fintype.card V - Nat.card H.support + 1) := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Nat.mul_add, mul_one]
      _ ≤ originalEdges * (Fintype.card V - Nat.card D.support) :=
        Nat.mul_le_mul_left originalEdges hcomplement
  have hdeleted :
      Nat.card D.edgeSet =
        Nat.card H.edgeSet - Nat.card (H.neighborSet v) := by
    simpa only [D, edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.card_edgeFinset_deleteIncidenceSet H v)
  have hdegreeEdges :
      Nat.card (H.neighborSet v) ≤ Nat.card H.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.degree_le_card_edgeFinset H v)
  have hedgeAdd :
      Nat.card D.edgeSet + Nat.card (H.neighborSet v) =
        Nat.card H.edgeSet := by
    omega
  have hweightedEdges :
      2 * Fintype.card V * Nat.card H.edgeSet =
        2 * Fintype.card V * Nat.card D.edgeSet +
          2 * Fintype.card V * Nat.card (H.neighborSet v) := by
    rw [← hedgeAdd, mul_add]
  change
    2 * Fintype.card V * Nat.card D.edgeSet +
        originalEdges * (Fintype.card V - Nat.card D.support) ≤
      2 * Fintype.card V * Nat.card H.edgeSet +
        originalEdges * (Fintype.card V - Nat.card H.support)
    at hscore
  simp only [degree_eq_natCard_neighborSet]
  omega

lemma maximum_sharp_pruning_subgraph_edge_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (original base H : SimpleGraph V) [DecidableRel original.Adj]
    (hpositive : 0 < original.edgeFinset.card)
    (hhalf : original.edgeFinset.card ≤ 2 * base.edgeFinset.card)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningScore (Nat.card original.edgeSet) D ≤
        sharpPruningScore (Nat.card original.edgeSet) H) :
    0 < Nat.card H.edgeSet := by
  classical
  have hpositiveNat : 0 < Nat.card original.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hpositive
  have hhalfNat :
      Nat.card original.edgeSet ≤ 2 * Nat.card base.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hhalf
  have hbasePositive : 0 < Nat.card base.edgeSet := by
    omega
  have hbaseScore := hmax base (le_refl base)
  by_contra hnot
  have hHzero : Nat.card H.edgeSet = 0 := by
    omega
  have hHedge : H.edgeFinset.card = 0 := by
    simpa only [edgeFinset_card_eq_natCard] using hHzero
  have hHbot : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    exact Finset.card_eq_zero.mp hHedge
  have hsharpBase :
      Nat.card original.edgeSet * Fintype.card V ≤
        sharpPruningPotential (Nat.card original.edgeSet) base := by
    have hcross :
        Nat.card original.edgeSet * Fintype.card V ≤
          2 * Fintype.card V * Nat.card base.edgeSet := by
      calc
        Nat.card original.edgeSet * Fintype.card V =
            Fintype.card V * Nat.card original.edgeSet := by
          ac_rfl
        _ ≤ Fintype.card V * (2 * Nat.card base.edgeSet) :=
          Nat.mul_le_mul_left (Fintype.card V) hhalfNat
        _ = 2 * Fintype.card V * Nat.card base.edgeSet := by
          ac_rfl
    unfold sharpPruningPotential
    omega
  have hHscore :
      sharpPruningScore (Nat.card original.edgeSet) H =
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    rw [hHbot]
    simp only [sharpPruningScore, sharpPruningPotential, edgeSet_bot, Nat.card_eq_fintype_card,
      Fintype.card_eq_zero, mul_zero, Fintype.card_ofFinset, support_bot, tsub_zero, zero_add, lt_self_iff_false,
      ↓reduceIte, add_zero]
  have hscoreContradiction :
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 ≤
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    calc
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 =
          sharpPruningScore (Nat.card original.edgeSet) base := by
        unfold sharpPruningScore
        rw [if_pos hbasePositive]
      _ ≤ sharpPruningScore (Nat.card original.edgeSet) H :=
        hbaseScore
      _ = 2 * (Nat.card original.edgeSet * Fintype.card V) :=
        hHscore
  omega

theorem exists_bipartite_min_degree_supported_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ H : SimpleGraph V,
      H.IsBipartite ∧ H ≤ G ∧ 0 < Nat.card H.edgeSet ∧
      ∀ v : V, v ∈ H.support →
        G.edgeFinset.card ≤ 2 * Fintype.card V * H.degree v := by
  classical
  obtain ⟨cut, hcutBipartite, hcutSubgraph, hcutEdges⟩ :=
    exists_bipartite_half_edges G
  obtain ⟨H, hH, hpotential, hscore⟩ :=
    exists_maximum_sharp_pruning_subgraph cut (Nat.card G.edgeSet)
  refine ⟨H, SimpleGraph.Colorable.mono_left hH hcutBipartite,
    le_trans hH hcutSubgraph,
    maximum_sharp_pruning_subgraph_edge_positive
      G cut H hpositive hcutEdges hscore, ?_⟩
  intro v hv
  simpa only [edgeFinset_card_eq_natCard,
    degree_eq_natCard_neighborSet] using
    (maximum_sharp_pruning_subgraph_degree
      cut H (Nat.card G.edgeSet) hH hpotential hv)

theorem exists_bipartite_min_degree_subgraph
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ (N : ℕ) (B : SimpleGraph (Fin N)) (f : Fin N ↪ Fin n),
      0 < N ∧ N ≤ n ∧ B.IsBipartite ∧ B.map f ≤ G ∧
      G.edgeFinset.card ≤ 2 * n * B.minDegree ∧
      ∀ v : Fin N, G.edgeFinset.card ≤ 2 * n * B.degree v := by
  classical
  obtain ⟨H, hHbip, hHG, hHpositive, hminimum⟩ :=
    exists_bipartite_min_degree_supported_subgraph G hpositive
  have hsupportPositive : 0 < Nat.card H.support := by
    apply Finite.card_pos_iff.mpr
    obtain ⟨⟨edge, hedge⟩⟩ := Finite.card_pos_iff.mp hHpositive
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using hedge
      exact ⟨⟨u, huv.mem_support_left⟩⟩
  let N := Nat.card H.support
  let supportEquiv : Fin N ≃ H.support :=
    (Finite.equivFin H.support).symm
  let f : Fin N ↪ Fin n :=
    supportEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun v : Fin n => v ∈ H.support))
  let B : SimpleGraph (Fin N) :=
    (H.induce H.support).comap supportEquiv.toEmbedding
  have hBcomap : B = H.comap f := by
    ext u v
    rfl
  have hBbip : B.IsBipartite := by
    rw [hBcomap]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap f H) hHbip
  have hmap : B.map f ≤ G := by
    calc
      B.map f ≤ H := by
        rw [hBcomap]
        exact SimpleGraph.map_comap_le f H
      _ ≤ G := hHG
  let supportIso : B ≃g H.induce H.support :=
    SimpleGraph.Iso.comap supportEquiv (H.induce H.support)
  have hdegrees : ∀ v : Fin N,
      G.edgeFinset.card ≤ 2 * n * B.degree v := by
    intro v
    have hdegree := hminimum (f v) (supportEquiv v).property
    have hBdegree :
        Nat.card (B.neighborSet v) =
          Nat.card (H.neighborSet (f v)) := by
      calc
        Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet
              (supportEquiv v)) := by
          change Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet (supportIso v))
          exact Nat.card_congr (supportIso.mapNeighborSet v)
        _ = Nat.card (H.neighborSet (f v)) := by
          change Nat.card ((H.induce H.support).neighborSet
            (supportEquiv v)) =
              Nat.card (H.neighborSet (supportEquiv v : Fin n))
          simpa only [degree_eq_natCard_neighborSet] using
            (SimpleGraph.degree_induce_support (G := H)
              (supportEquiv v))
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet, Fintype.card_fin, hBdegree]
      using hdegree
  have hNn : N ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
  letI : Nonempty (Fin N) := ⟨⟨0, hsupportPositive⟩⟩
  obtain ⟨v, hv⟩ := B.exists_minimal_degree_vertex
  have hmin : G.edgeFinset.card ≤ 2 * n * B.minDegree := by
    rw [hv]
    exact hdegrees v
  exact ⟨N, B, f, hsupportPositive, hNn,
    hBbip, hmap, hmin, hdegrees⟩

end DensityReduction

noncomputable section Patterns

open SimpleGraph

abbrev SubdivisionVertex (k : ℕ) :=
  (Fin 3 ⊕ Fin k) ⊕ (Fin 3 × Fin k)

def subdivisionRelation (k : ℕ) :
    SubdivisionVertex k → SubdivisionVertex k → Prop
  | .inl (.inl base), .inr (otherBase, _) => base = otherBase
  | .inl (.inr center), .inr (_, otherCenter) => center = otherCenter
  | _, _ => False

def SubdivisionGraph (k : ℕ) : SimpleGraph (SubdivisionVertex k) :=
  SimpleGraph.fromRel (subdivisionRelation k)

def subdivisionColor (k : ℕ) : SubdivisionVertex k → Bool
  | .inl _ => false
  | .inr _ => true

abbrev thetaGraph : SimpleGraph (SubdivisionVertex 2) :=
  SubdivisionGraph 2

abbrev gammaGraph : SimpleGraph (SubdivisionVertex 3) :=
  SubdivisionGraph 3

end Patterns

noncomputable section Quotients

open Finset SimpleGraph

abbrev JVertex :=
  (Fin 4 ⊕ (Fin 2 × Fin 2)) ⊕
    ((Fin 2 × (Fin 3 × Fin 2)) ⊕ Unit)

def jBase (copy : Fin 2) (base : Fin 3) : Fin 4 :=
  if base = 0 then
    if copy = 0 then 0 else 1
  else if base = 1 then 2 else 3

def jTemplateRelation : JVertex → JVertex → Prop
  | .inl (.inl base), .inr (.inl (copy, (i, _))) =>
      base = jBase copy i
  | .inl (.inr (copy, center)), .inr (.inl (copy', (_, center'))) =>
      copy = copy' ∧ center = center'
  | .inl (.inl base), .inr (.inr _) =>
      base = 0 ∨ base = 1
  | _, _ => False

def jTemplate : SimpleGraph JVertex :=
  SimpleGraph.fromRel jTemplateRelation

def jColor : JVertex → Bool
  | .inl _ => false
  | .inr _ => true

def InJCopy (copy : Fin 2) : JVertex → Prop
  | .inl (.inl base) => ∃ i : Fin 3, base = jBase copy i
  | .inl (.inr (copy', _)) => copy = copy'
  | .inr (.inl (copy', _)) => copy = copy'
  | .inr (.inr _) => False

abbrev KVertex := Fin 2 × SubdivisionVertex 3

def kSpecifiedCenter : SubdivisionVertex 3 :=
  .inl (.inr 0)

def kTemplateRelation (u v : KVertex) : Prop :=
  (u.1 = v.1 ∧ subdivisionRelation 3 u.2 v.2) ∨
    (u.1 = 0 ∧ v.1 = 1 ∧
      u.2 = kSpecifiedCenter ∧ v.2 = kSpecifiedCenter)

def kTemplate : SimpleGraph KVertex :=
  SimpleGraph.fromRel kTemplateRelation

def kColor (v : KVertex) : Bool :=
  if v.1 = 0 then subdivisionColor 3 v.2
  else !(subdivisionColor 3 v.2)

def ColorRespecting {α : Type*}
    (color : α → Bool) (f : α → α) : Prop :=
  ∀ u v, f u = f v → color u = color v

def JAdmissible (f : JVertex → JVertex) : Prop :=
  ColorRespecting jColor f ∧
    Function.Injective
      (fun base : Fin 4 => f (.inl (.inl base))) ∧
    ∀ copy : Fin 2, Set.InjOn f {v | InJCopy copy v}

def KAdmissible (f : KVertex → KVertex) : Prop :=
  ColorRespecting kColor f ∧
    ∀ copy : Fin 2,
      Set.InjOn f {v : KVertex | v.1 = copy}

def quotientRelation {α : Type*}
    (graph : SimpleGraph α) (f : α → α)
    (u v : Set.range f) : Prop :=
  ∃ x y : α, f x = (u : α) ∧ f y = (v : α) ∧ graph.Adj x y

def quotientGraph {α : Type*}
    (graph : SimpleGraph α) (f : α → α) :
    SimpleGraph (Set.range f) :=
  SimpleGraph.fromRel (quotientRelation graph f)

noncomputable def encodeFiniteGraph {α : Type*} [Fintype α]
    (graph : SimpleGraph α) : FiniteGraph :=
  ⟨Fintype.card α,
    graph.map (Fintype.equivFin α).toEmbedding⟩

noncomputable def jQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : JVertex → JVertex // JAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph jTemplate (f : JVertex → JVertex)))).toFinset

theorem jQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ jQuotients ↔
      ∃ f : JVertex → JVertex, JAdmissible f ∧
        encodeFiniteGraph (quotientGraph jTemplate f) = graph := by
  rw [jQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

noncomputable def kQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : KVertex → KVertex // KAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph kTemplate (f : KVertex → KVertex)))).toFinset

theorem kQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by
  rw [kQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

def finiteCycle (n : ℕ) : FiniteGraph :=
  ⟨n, SimpleGraph.cycleGraph n⟩

noncomputable def proposedFamily : Finset FiniteGraph := by
  classical
  exact {finiteCycle 4, finiteCycle 6} ∪ jQuotients ∪ kQuotients

theorem proposedFamily_mem_iff {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by
  classical
  simp only [proposedFamily, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, jQuotients_mem_iff, kQuotients_mem_iff]

theorem proposedFamily_induction {P : FiniteGraph → Prop}
    (hfour : P (finiteCycle 4)) (hsix : P (finiteCycle 6))
    (hj : ∀ f : JVertex → JVertex, JAdmissible f →
      P (encodeFiniteGraph (quotientGraph jTemplate f)))
    (hk : ∀ f : KVertex → KVertex, KAdmissible f →
      P (encodeFiniteGraph (quotientGraph kTemplate f))) :
    ∀ graph ∈ proposedFamily, P graph := by
  intro graph hgraph
  rcases proposedFamily_mem_iff.mp hgraph with
    ((rfl | rfl) | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
  · exact hfour
  · exact hsix
  · exact hj f hf
  · exact hk f hf

theorem four_cycle_mem_proposedFamily :
    finiteCycle 4 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inl rfl)))

theorem proposedFamily_nonempty : proposedFamily.Nonempty :=
  ⟨finiteCycle 4, four_cycle_mem_proposedFamily⟩

theorem six_cycle_mem_proposedFamily : finiteCycle 6 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inr rfl)))

theorem proposedFamilyFree_four_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 4).Free host := by
  simpa only [not_nonempty_iff, finiteCycle] using FamilyFree.member four_cycle_mem_proposedFamily hfree

theorem proposedFamilyFree_six_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by
  simpa only [not_nonempty_iff, finiteCycle] using FamilyFree.member six_cycle_mem_proposedFamily hfree

lemma jQuotient_mem_proposedFamily
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inr ⟨f, hf, rfl⟩))

lemma kQuotient_mem_proposedFamily
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inr ⟨f, hf, rfl⟩)

end Quotients

noncomputable section Geometry

open SimpleGraph

section SymplecticGeometry

variable (K : Type*) [Field K]

abbrev SymplecticVector := Fin 4 → K

def standardSymplecticForm
    (u v : SymplecticVector K) : K :=
  u 0 * v 1 - u 1 * v 0 +
    (u 2 * v 3 - u 3 * v 2)

theorem standardSymplecticForm_self
    (u : SymplecticVector K) :
    standardSymplecticForm K u u = 0 := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_swap
    (u v : SymplecticVector K) :
    standardSymplecticForm K u v =
      -standardSymplecticForm K v u := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_add_left
    (u v w : SymplecticVector K) :
    standardSymplecticForm K (u + v) w =
      standardSymplecticForm K u w + standardSymplecticForm K v w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_add_right
    (u v w : SymplecticVector K) :
    standardSymplecticForm K u (v + w) =
      standardSymplecticForm K u v + standardSymplecticForm K u w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_smul_left
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K (a • u) v =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

lemma standardSymplecticForm_smul_right
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K u (a • v) =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

theorem standardSymplecticForm_nondegenerate_left
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K u v = 0) : u = 0 := by
  funext i
  fin_cases i
  · simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Pi.zero_apply, standardSymplecticForm,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_one, mul_zero, sub_zero, Matrix.cons_val, sub_self, add_zero] using
      h ![0, 1, 0, 0]
  · simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Pi.zero_apply, standardSymplecticForm,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, mul_one, zero_sub, Matrix.cons_val, sub_self, add_zero,
      neg_eq_zero] using h ![1, 0, 0, 0]
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, Pi.zero_apply, standardSymplecticForm,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, sub_self, Matrix.cons_val, mul_one, sub_zero, zero_add] using
      h ![0, 0, 0, 1]
  · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, Pi.zero_apply, standardSymplecticForm,
      Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, sub_self, Matrix.cons_val, mul_one, zero_sub, zero_add,
      neg_eq_zero] using h ![0, 0, 1, 0]

theorem standardSymplecticForm_nondegenerate_right
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K v u = 0) : u = 0 := by
  apply standardSymplecticForm_nondegenerate_left K u
  intro v
  rw [standardSymplecticForm_swap, h v, neg_zero]

def standardSymplecticBilin :
    LinearMap.BilinForm K (SymplecticVector K) :=
  LinearMap.mk₂ K (standardSymplecticForm K)
    (standardSymplecticForm_add_left K)
    (fun a u v => by
      simpa only [smul_eq_mul] using standardSymplecticForm_smul_left K a u v)
    (standardSymplecticForm_add_right K)
    (fun a u v => by
      simpa only [smul_eq_mul] using standardSymplecticForm_smul_right K a u v)

theorem standardSymplecticBilin_nondegenerate :
    (standardSymplecticBilin K).Nondegenerate := by
  constructor
  · intro u hu
    exact standardSymplecticForm_nondegenerate_left K u hu
  · intro u hu
    exact standardSymplecticForm_nondegenerate_right K u hu

theorem standardSymplecticBilin_isAlt :
    (standardSymplecticBilin K).IsAlt := by
  intro u
  exact standardSymplecticForm_self K u

abbrev SymplecticPoint :=
  {P : Submodule K (SymplecticVector K) //
    Module.finrank K P = 1}

abbrev SymplecticLine :=
  {L : Submodule K (SymplecticVector K) //
    Module.finrank K L = 2 ∧
      ∀ u ∈ L, ∀ v ∈ L, standardSymplecticForm K u v = 0}

abbrev SymplecticPointOrthogonal (p : SymplecticPoint K) :=
  (standardSymplecticBilin K).orthogonal p.1

lemma symplecticPoint_le_orthogonal (p : SymplecticPoint K) :
    p.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  by_cases hx0 : x = 0
  · simp only [standardSymplecticForm, Fin.isValue, hx0, Pi.zero_apply, mul_zero, sub_self, add_zero]
  · have hxsub : (⟨x, hx⟩ : p.1) ≠ 0 := by
      intro h
      apply hx0
      simpa only [ZeroMemClass.coe_zero] using congrArg Subtype.val h
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hxsub (⟨y, hy⟩ : p.1)
    have hav : a • x = y := congrArg Subtype.val ha
    rw [← hav, standardSymplecticForm_smul_left,
      standardSymplecticForm_self, mul_zero]

lemma symplecticPointOrthogonal_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointOrthogonal K p) = 3 := by
  change Module.finrank K
    ((standardSymplecticBilin K).orthogonal p.1) = 3
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K), p.2]
  simp only [SymplecticVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.add_one_sub_one]

abbrev SymplecticPointRadical (p : SymplecticPoint K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype p.1

lemma symplecticPointRadical_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointRadical K p) = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticPoint_le_orthogonal K p)).finrank_eq.trans p.2

abbrev SymplecticPointQuotient (p : SymplecticPoint K) :=
  (SymplecticPointOrthogonal K p) ⧸ (SymplecticPointRadical K p)

lemma symplecticPointQuotient_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointQuotient K p) = 2 := by
  change Module.finrank K
    (↥(SymplecticPointOrthogonal K p) ⧸
      SymplecticPointRadical K p) = 2
  have h := Submodule.finrank_quotient_add_finrank
    (SymplecticPointRadical K p)
  rw [symplecticPointRadical_finrank K p,
    symplecticPointOrthogonal_finrank K p] at h
  omega

lemma quotient_map_finrank
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (R S : Submodule K W) (hRS : R ≤ S) :
    Module.finrank K (Submodule.map R.mkQ S) +
      Module.finrank K R = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (R.mkQ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hRS).finrank_eq] at h
  exact h

lemma symplecticLine_le_pointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) : L.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  exact L.2.2 y (hpL hy) x hx

lemma symplectic_two_plane_isotropic
    {p : SymplecticPoint K}
    {S : Submodule K (SymplecticVector K)}
    (hdim : Module.finrank K S = 2)
    (hpS : p.1 ≤ S)
    (hSorth : S ≤ SymplecticPointOrthogonal K p) :
    ∀ u ∈ S, ∀ v ∈ S, standardSymplecticForm K u v = 0 := by
  intro u hu v hv
  by_cases huP : u ∈ p.1
  · exact hSorth hv u huP
  · have hle : p.1 ⊔ K ∙ u ≤ S := by
      apply sup_le hpS
      exact (Submodule.span_le).mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hu)
    have hspan : p.1 ⊔ K ∙ u = S :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        rw [Submodule.finrank_sup_span_singleton huP, p.2, hdim])
    have hvspan : v ∈ p.1 ⊔ K ∙ u := hspan.symm ▸ hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have horth : standardSymplecticForm K a u = 0 :=
      hSorth hu a ha
    have hreverse : standardSymplecticForm K u a = 0 := by
      rw [standardSymplecticForm_swap, horth, neg_zero]
    rw [standardSymplecticForm_add_right,
      standardSymplecticForm_smul_right,
      standardSymplecticForm_self,
      hreverse, mul_zero, add_zero]

abbrev SymplecticLinesOnPoint (p : SymplecticPoint K) :=
  {L : SymplecticLine K // p.1 ≤ L.1}

abbrev SymplecticLineInPointOrthogonal
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype L.1

lemma symplecticLineInPointOrthogonal_finrank
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    Module.finrank K (SymplecticLineInPointOrthogonal K p L) = 2 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticLine_le_pointOrthogonal K hpL)).finrank_eq.trans L.2.1

lemma symplecticPointRadical_le_lineInPointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    SymplecticPointRadical K p ≤
      SymplecticLineInPointOrthogonal K p L :=
  Submodule.comap_mono hpL

noncomputable def symplecticLinesOnPointEquivSubmodule
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      {S : Submodule K (SymplecticPointQuotient K p) //
        Module.finrank K S = 1} where
  toFun L :=
    ⟨Submodule.map (SymplecticPointRadical K p).mkQ
       (SymplecticLineInPointOrthogonal K p L.1), by
       change Module.finrank K
         (Submodule.map (SymplecticPointRadical K p).mkQ
           (SymplecticLineInPointOrthogonal K p L.1)) = 1
       have h := quotient_map_finrank K
         (SymplecticPointRadical K p)
         (SymplecticLineInPointOrthogonal K p L.1)
         (symplecticPointRadical_le_lineInPointOrthogonal K L.2)
       rw [symplecticPointRadical_finrank K p,
         symplecticLineInPointOrthogonal_finrank K L.2] at h
       omega⟩
  invFun Q := by
    let T : Submodule K (SymplecticPointOrthogonal K p) :=
      Submodule.comap (SymplecticPointRadical K p).mkQ Q.1
    have hrad : SymplecticPointRadical K p ≤ T :=
      Submodule.le_comap_mkQ (SymplecticPointRadical K p) Q.1
    have hmap :
        Submodule.map (SymplecticPointRadical K p).mkQ T = Q.1 := by
      apply Submodule.map_comap_eq_self
      rw [Submodule.range_mkQ]
      exact le_top
    have hdimT : Module.finrank K T = 2 := by
      have h := quotient_map_finrank K
        (SymplecticPointRadical K p) T hrad
      rw [hmap, Q.2, symplecticPointRadical_finrank K p] at h
      omega
    let S : Submodule K (SymplecticVector K) :=
      Submodule.map (SymplecticPointOrthogonal K p).subtype T
    have hdimS : Module.finrank K S = 2 := by
      exact (Submodule.finrank_map_subtype_eq
        (SymplecticPointOrthogonal K p) T).trans hdimT
    have hSorth : S ≤ SymplecticPointOrthogonal K p := by
      intro x hx
      rcases hx with ⟨y, _, rfl⟩
      exact y.2
    have hpS : p.1 ≤ S := by
      intro x hx
      have hxorth : x ∈ SymplecticPointOrthogonal K p :=
        symplecticPoint_le_orthogonal K p hx
      have hxrad :
          (⟨x, hxorth⟩ : SymplecticPointOrthogonal K p) ∈
            SymplecticPointRadical K p := hx
      exact ⟨⟨x, hxorth⟩, hrad hxrad, rfl⟩
    exact ⟨⟨S, hdimS,
      symplectic_two_plane_isotropic K hdimS hpS hSorth⟩, hpS⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointRadical K p).mkQ
        (Submodule.map (SymplecticPointRadical K p).mkQ
          (SymplecticLineInPointOrthogonal K p L.1))) = L.1.1
    rw [Submodule.comap_map_mkQ,
      sup_eq_right.mpr
        (symplecticPointRadical_le_lineInPointOrthogonal K L.2)]
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        L.1.1) = L.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr
      (symplecticLine_le_pointOrthogonal K L.2)
  right_inv Q := by
    apply Subtype.ext
    change Submodule.map (SymplecticPointRadical K p).mkQ
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        (Submodule.map (SymplecticPointOrthogonal K p).subtype
          (Submodule.comap (SymplecticPointRadical K p).mkQ
            Q.1))) = Q.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr
        (SymplecticPointOrthogonal K p).subtype_injective,
      sup_bot_eq]
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_mkQ]
    exact le_top

noncomputable def symplecticLinesOnPointEquiv
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      Projectivization K (SymplecticPointQuotient K p) :=
  (symplecticLinesOnPointEquivSubmodule K p).trans
    (Projectivization.equivSubmodule K
      (SymplecticPointQuotient K p)).symm

lemma symplecticLinesOnPoint_card [Finite K]
    (p : SymplecticPoint K) :
    Nat.card (SymplecticLinesOnPoint K p) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticLinesOnPointEquiv K p)]
  exact Projectivization.card_of_finrank_two K
    (SymplecticPointQuotient K p)
    (symplecticPointQuotient_finrank K p)

abbrev SymplecticPointsOnLine (L : SymplecticLine K) :=
  {p : SymplecticPoint K // p.1 ≤ L.1}

noncomputable def symplecticPointsOnLineEquivSubmodule
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃
      {S : Submodule K L.1 // Module.finrank K S = 1} where
  toFun p :=
    ⟨Submodule.comap L.1.subtype p.1.1,
      (Submodule.comapSubtypeEquivOfLe p.2).finrank_eq.trans p.1.2⟩
  invFun S :=
    ⟨⟨Submodule.map L.1.subtype S.1,
       (Submodule.finrank_map_subtype_eq L.1 S.1).trans S.2⟩,
      by
        intro x hx
        rcases hx with ⟨y, _, rfl⟩
        exact y.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map L.1.subtype
      (Submodule.comap L.1.subtype p.1.1) = p.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr p.2
  right_inv S := by
    apply Subtype.ext
    change Submodule.comap L.1.subtype
      (Submodule.map L.1.subtype S.1) = S.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr L.1.subtype_injective, sup_bot_eq]

noncomputable def symplecticPointsOnLineEquiv
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃ Projectivization K L.1 :=
  (symplecticPointsOnLineEquivSubmodule K L).trans
    (Projectivization.equivSubmodule K L.1).symm

lemma symplecticPointsOnLine_card [Finite K]
    (L : SymplecticLine K) :
    Nat.card (SymplecticPointsOnLine K L) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticPointsOnLineEquiv K L)]
  exact Projectivization.card_of_finrank_two K L.1 L.2.1

lemma symplecticPoint_sup_finrank
    {p q : SymplecticPoint K} (hpq : p ≠ q) :
    Module.finrank K
      (p.1 ⊔ q.1 : Submodule K (SymplecticVector K)) = 2 := by
  have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  have hd : Disjoint p.1 q.1 :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr p.2).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr q.2) hne
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
  rw [hd.eq_bot, finrank_bot, p.2, q.2] at hrank
  omega

lemma symplecticLine_eq_of_points
    {p q : SymplecticPoint K} (hpq : p ≠ q)
    {L M : SymplecticLine K}
    (hpL : p.1 ≤ L.1) (hqL : q.1 ≤ L.1)
    (hpM : p.1 ≤ M.1) (hqM : q.1 ≤ M.1) : L = M := by
  have hsupL : p.1 ⊔ q.1 ≤ L.1 := sup_le hpL hqL
  have hsupM : p.1 ⊔ q.1 ≤ M.1 := sup_le hpM hqM
  have hL : p.1 ⊔ q.1 = L.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupL
      ((symplecticPoint_sup_finrank K hpq).trans L.2.1.symm)
  have hM : p.1 ⊔ q.1 = M.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupM
      ((symplecticPoint_sup_finrank K hpq).trans M.2.1.symm)
  exact Subtype.ext (hL.symm.trans hM)

lemma symplectic_isotropic_finrank_le_two
    (S : Submodule K (SymplecticVector K))
    (hS : ∀ u ∈ S, ∀ v ∈ S,
      standardSymplecticForm K u v = 0) :
    Module.finrank K S ≤ 2 := by
  have hle : S ≤ (standardSymplecticBilin K).orthogonal S := by
    intro x hx
    change ∀ y ∈ S, standardSymplecticForm K y x = 0
    intro y hy
    exact hS y hy x hx
  have hrank := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K)] at hrank
  have hambient : Module.finrank K (SymplecticVector K) = 4 := by
    simp only [SymplecticVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hambient] at hrank
  omega

lemma symplectic_triangle_points_collinear
    {p q r : SymplecticPoint K} (hpq : p ≠ q)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    r.1 ≤ Lpq.1 := by
  let T : Submodule K (SymplecticVector K) :=
    (p.1 ⊔ q.1) ⊔ r.1
  have hiso : ∀ u ∈ T, ∀ v ∈ T,
      standardSymplecticForm K u v = 0 := by
    intro u hu v hv
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨de, hde, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hde
    have had := Lpq.2.2 a (hpLpq ha) d (hpLpq hd)
    have hae := Lpq.2.2 a (hpLpq ha) e (hqLpq he)
    have haf := Lpr.2.2 a (hpLpr ha) f (hrLpr hf)
    have hbd := Lpq.2.2 b (hqLpq hb) d (hpLpq hd)
    have hbe := Lpq.2.2 b (hqLpq hb) e (hqLpq he)
    have hbf := Lqr.2.2 b (hqLqr hb) f (hrLqr hf)
    have hcd := Lpr.2.2 c (hrLpr hc) d (hpLpr hd)
    have hce := Lqr.2.2 c (hrLqr hc) e (hqLqr he)
    have hcf := Lpr.2.2 c (hrLpr hc) f (hrLpr hf)
    simp only [standardSymplecticForm_add_right, standardSymplecticForm_add_left, had, hbd, add_zero, hcd, hae,
      hbe, hce, haf, hbf, hcf]
  have hbound : Module.finrank K T ≤ 2 :=
    symplectic_isotropic_finrank_le_two K T hiso
  have hspan : p.1 ⊔ q.1 = T :=
    Submodule.eq_of_le_of_finrank_le le_sup_left
      (by simpa only [symplecticPoint_sup_finrank K hpq] using hbound)
  exact (show r.1 ≤ T from le_sup_right).trans
    (hspan.symm ▸ sup_le hpLpq hqLpq)

lemma symplectic_triangle_lines_eq
    {p q r : SymplecticPoint K}
    (hpq : p ≠ q) (hqr : q ≠ r)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    Lpq = Lqr := by
  have hrLpq : r.1 ≤ Lpq.1 := symplectic_triangle_points_collinear K hpq
    hpLpq hqLpq hpLpr hrLpr hqLqr hrLqr
  exact symplecticLine_eq_of_points K hqr hqLpq hrLpq hqLqr hrLqr

abbrev QuadrangleVertex :=
  SymplecticPoint K ⊕ SymplecticLine K

def quadrangleIncidence :
    QuadrangleVertex K → QuadrangleVertex K → Prop
  | .inl point, .inr line => (point.1 : Submodule K _) ≤ line.1
  | _, _ => False

def symplecticQuadrangle : SimpleGraph (QuadrangleVertex K) :=
  SimpleGraph.fromRel (quadrangleIncidence K)

theorem symplecticQuadrangle_incidence_adj
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticQuadrangle K).Adj (.inl p) (.inr L) ↔ p.1 ≤ L.1 := by
  simp only [symplecticQuadrangle, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, quadrangleIncidence,
    or_false, true_and]

theorem symplecticQuadrangle_adjacent_to_point
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by
  rcases v with q | L
  · simp only [symplecticQuadrangle, fromRel_adj, ne_eq, Sum.inl.injEq, quadrangleIncidence, or_self,
      and_false] at h
  · exact ⟨L, rfl, (symplecticQuadrangle_incidence_adj K p L).mp h⟩

theorem symplecticQuadrangle_adjacent_to_line
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by
  rcases v with p | M
  · exact ⟨p, rfl,
      (symplecticQuadrangle_incidence_adj K p L).mp h.symm⟩
  · simp only [symplecticQuadrangle, fromRel_adj, ne_eq, Sum.inr.injEq, quadrangleIncidence, or_self,
      and_false] at h

theorem symplecticQuadrangle_common_neighbor_unique
    {u v : QuadrangleVertex K} (huv : u ≠ v)
    {w z : QuadrangleVertex K}
    (huw : (symplecticQuadrangle K).Adj u w)
    (hvw : (symplecticQuadrangle K).Adj v w)
    (huz : (symplecticQuadrangle K).Adj u z)
    (hvz : (symplecticQuadrangle K).Adj v z) : w = z := by
  rcases u with p | L <;>
    rcases v with q | M <;>
    rcases w with r | R <;>
    rcases z with s | S <;>
    simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at huw hvw huz hvz
  · apply congrArg Sum.inr
    apply symplecticLine_eq_of_points K
      (fun hpq => huv (congrArg Sum.inl hpq))
    · exact huw
    · exact hvw
    · exact huz
    · exact hvz
  · apply congrArg Sum.inl
    by_contra hrs
    have hlines : L = M := symplecticLine_eq_of_points K hrs
      huw huz hvw hvz
    exact huv (congrArg Sum.inr hlines)

theorem symplecticQuadrangle_four_cycle_free :
    (SimpleGraph.cycleGraph 4).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h21 : (symplecticQuadrangle K).Adj (copy 2) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h03 : (symplecticQuadrangle K).Adj (copy 0) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h02 : copy 0 ≠ copy 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (copy.injective h)
  have h13 : copy 1 = copy 3 :=
    symplecticQuadrangle_common_neighbor_unique K h02 h01 h21 h03 h23
  exact (by decide : (1 : Fin 4) ≠ 3) (copy.injective h13)

theorem symplecticQuadrangle_six_cycle_free :
    (SimpleGraph.cycleGraph 6).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 0 1 by decide)
  have h12 : (symplecticQuadrangle K).Adj (copy 1) (copy 2) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 1 2 by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 2 3 by decide)
  have h34 : (symplecticQuadrangle K).Adj (copy 3) (copy 4) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 3 4 by decide)
  have h45 : (symplecticQuadrangle K).Adj (copy 4) (copy 5) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 4 5 by decide)
  have h50 : (symplecticQuadrangle K).Adj (copy 5) (copy 0) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 5 0 by decide)
  cases h0 : copy 0 with
  | inl p =>
      rw [h0] at h01 h50
      obtain ⟨L, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_point K h01
      rw [h1] at h12
      obtain ⟨q, h2, hqL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h12
      rw [h2] at h23
      obtain ⟨M, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h23
      rw [h3] at h34
      obtain ⟨r, h4, hrM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h34
      rw [h4] at h45
      obtain ⟨N, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h45
      rw [h5] at h50
      have hpN : p.1 ≤ N.1 :=
        (symplecticQuadrangle_incidence_adj K p N).mp h50.symm
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (0 : Fin 6) ≠ 2)
        apply copy.injective
        change copy 0 = copy 2
        rw [h0, h2, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (2 : Fin 6) ≠ 4)
        apply copy.injective
        change copy 2 = copy 4
        rw [h2, h4, heq]
      have hLM : L = M := symplectic_triangle_lines_eq K hpq hqr
        hpL hqL hpN hrN hqM hrM
      apply (by decide : (1 : Fin 6) ≠ 3)
      apply copy.injective
      change copy 1 = copy 3
      rw [h1, h3, hLM]
  | inr L =>
      rw [h0] at h01 h50
      obtain ⟨p, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h01
      rw [h1] at h12
      obtain ⟨M, h2, hpM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h12
      rw [h2] at h23
      obtain ⟨q, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h23
      rw [h3] at h34
      obtain ⟨N, h4, hqN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h34
      rw [h4] at h45
      obtain ⟨r, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_line K h45
      rw [h5] at h50
      have hrL : r.1 ≤ L.1 :=
        (symplecticQuadrangle_incidence_adj K r L).mp h50
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (1 : Fin 6) ≠ 3)
        apply copy.injective
        change copy 1 = copy 3
        rw [h1, h3, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (3 : Fin 6) ≠ 5)
        apply copy.injective
        change copy 3 = copy 5
        rw [h3, h5, heq]
      have hMN : M = N := symplectic_triangle_lines_eq K hpq hqr
        hpM hqM hpL hrL hqN hrN
      apply (by decide : (2 : Fin 6) ≠ 4)
      apply copy.injective
      change copy 2 = copy 4
      rw [h2, h4, hMN]

lemma symplecticPoint_card [Finite K] :
    Nat.card (SymplecticPoint K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  calc
    Nat.card (SymplecticPoint K) =
        Nat.card (Projectivization K (SymplecticVector K)) :=
      Nat.card_congr
        (Projectivization.equivSubmodule K (SymplecticVector K)).symm
    _ = ∑ i ∈ Finset.range 4, (Nat.card K) ^ i :=
      Projectivization.card_of_finrank K (SymplecticVector K) (by simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
    _ = (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one]
      ring

abbrev SymplecticIncidence :=
  {x : SymplecticPoint K × SymplecticLine K // x.1.1 ≤ x.2.1}

def symplecticIncidenceEquivSigmaPoints :
    SymplecticIncidence K ≃
      (Σ p : SymplecticPoint K, SymplecticLinesOnPoint K p) where
  toFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨p, ⟨L, h⟩⟩
    rfl

def symplecticIncidenceEquivSigmaLines :
    SymplecticIncidence K ≃
      (Σ L : SymplecticLine K, SymplecticPointsOnLine K L) where
  toFun i := ⟨i.1.2, ⟨i.1.1, i.2⟩⟩
  invFun s := ⟨(s.2.1, s.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨L, ⟨p, h⟩⟩
    rfl

lemma symplecticIncidence_card_by_points [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ p : SymplecticPoint K,
          SymplecticLinesOnPoint K p) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaPoints K)
    _ = ∑ p : SymplecticPoint K,
          Nat.card (SymplecticLinesOnPoint K p) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
      simp_rw [symplecticLinesOnPoint_card]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

lemma symplecticIncidence_card_by_lines [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
  classical
  letI : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  letI : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ L : SymplecticLine K,
          SymplecticPointsOnLine K L) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaLines K)
    _ = ∑ L : SymplecticLine K,
          Nat.card (SymplecticPointsOnLine K L) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
      simp_rw [symplecticPointsOnLine_card]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

lemma symplecticLine_card [Finite K] :
    Nat.card (SymplecticLine K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  have hcounts :
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) =
        Nat.card (SymplecticLine K) * (Nat.card K + 1) :=
    (symplecticIncidence_card_by_points K).symm.trans
      (symplecticIncidence_card_by_lines K)
  have hline : Nat.card (SymplecticPoint K) =
      Nat.card (SymplecticLine K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hcounts
  rw [← hline, symplecticPoint_card]

lemma symplecticIncidence_card [Finite K] :
    Nat.card (SymplecticIncidence K) =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [symplecticIncidence_card_by_points, symplecticPoint_card]
  ring

theorem symplecticQuadrangle_vertex_card [Finite K] :
    Nat.card (QuadrangleVertex K) =
      2 * (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  rw [Nat.card_sum, symplecticPoint_card, symplecticLine_card]
  ring

def symplecticIncidenceToEdge :
    SymplecticIncidence K → (symplecticQuadrangle K).edgeSet :=
  fun i =>
    ⟨s(Sum.inl i.1.1, Sum.inr i.1.2),
      (symplecticQuadrangle_incidence_adj K i.1.1 i.1.2).mpr i.2⟩

lemma symplecticIncidenceToEdge_injective :
    Function.Injective (symplecticIncidenceToEdge K) := by
  intro i j h
  have hedges := congrArg Subtype.val h
  change s(Sum.inl i.1.1, Sum.inr i.1.2) =
    s(Sum.inl j.1.1, Sum.inr j.1.2) at hedges
  rcases Sym2.eq_iff.mp hedges with ⟨hp, hL⟩ | ⟨hbad, _⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl_injective hp
    · exact Sum.inr_injective hL
  · cases hbad

lemma symplecticIncidenceToEdge_surjective :
    Function.Surjective (symplecticIncidenceToEdge K) := by
  intro e
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.1
  change s(u, v) = e.1 at huv
  have hadj : (symplecticQuadrangle K).Adj u v := by
    apply (symplecticQuadrangle K).mem_edgeSet.mp
    rw [huv]
    exact e.2
  rcases u with p | L <;> rcases v with q | M
  · simp only [symplecticQuadrangle, fromRel_adj, ne_eq, Sum.inl.injEq, quadrangleIncidence, or_self,
      and_false] at hadj
  · refine ⟨⟨(p, M),
        (symplecticQuadrangle_incidence_adj K p M).mp hadj⟩, ?_⟩
    apply Subtype.ext
    exact huv
  · refine ⟨⟨(q, L),
        (symplecticQuadrangle_incidence_adj K q L).mp hadj.symm⟩, ?_⟩
    apply Subtype.ext
    exact Sym2.eq_swap.trans huv
  · simp only [symplecticQuadrangle, fromRel_adj, ne_eq, Sum.inr.injEq, quadrangleIncidence, or_self,
      and_false] at hadj

noncomputable def symplecticIncidenceEquivEdge :
    SymplecticIncidence K ≃ (symplecticQuadrangle K).edgeSet :=
  Equiv.ofBijective (symplecticIncidenceToEdge K)
    ⟨symplecticIncidenceToEdge_injective K,
      symplecticIncidenceToEdge_surjective K⟩

theorem symplecticQuadrangle_edge_card [Finite K] :
    Nat.card (symplecticQuadrangle K).edgeSet =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [← Nat.card_congr (symplecticIncidenceEquivEdge K),
    symplecticIncidence_card]

end SymplecticGeometry

section NumericalParameters

def quadrangleVertexCount (q : ℕ) : ℕ :=
  2 * (q + 1) * (q ^ 2 + 1)

def quadrangleEdgeCount (q : ℕ) : ℕ :=
  (q + 1) ^ 2 * (q ^ 2 + 1)

theorem quadrangle_density_certificate (q : ℕ) :
    (quadrangleVertexCount q : ℝ) ^ 4 ≤
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 := by
  have hnonneg :
      0 ≤ 32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
        ((q : ℝ) ^ 2 + 1) ^ 3 := by
    positivity
  have hidentity :
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 -
          (quadrangleVertexCount q : ℝ) ^ 4 =
        32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
          ((q : ℝ) ^ 2 + 1) ^ 3 := by
    simp only [quadrangleVertexCount, quadrangleEdgeCount,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  linarith

theorem quadrangle_rpow_density (q : ℕ) :
    (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  apply ((by decide : Odd 3).strictMono_pow.le_iff_le).mp
  have hcubed :
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (quadrangleVertexCount q : ℝ) ^ 4 / 16 := by
    rw [mul_pow,
      ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))
        (-((4 : ℝ) / 3)) 3,
      ← Real.rpow_mul_natCast
        (by exact_mod_cast (Nat.zero_le (quadrangleVertexCount q)))
        ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hcubed]
  nlinarith [quadrangle_density_certificate q]

theorem quadrangleVertexCount_mul_le
    (q t : ℕ) (ht : 1 ≤ t) :
    quadrangleVertexCount (t * q) ≤
      t ^ 3 * quadrangleVertexCount q := by
  have hfirst : t * q + 1 ≤ t * (q + 1) := by
    nlinarith
  have hsecond : (t * q) ^ 2 + 1 ≤ t ^ 2 * (q ^ 2 + 1) := by
    nlinarith [sq_nonneg (t - 1)]
  unfold quadrangleVertexCount
  calc
    2 * (t * q + 1) * ((t * q) ^ 2 + 1) ≤
        2 * (t * (q + 1)) * (t ^ 2 * (q ^ 2 + 1)) := by
      gcongr
    _ = t ^ 3 * (2 * (q + 1) * (q ^ 2 + 1)) := by
      ring

end NumericalParameters

end Geometry

noncomputable section Cyclicity

open Finset SimpleGraph

def thetaCycleVertex : Fin 8 → SubdivisionVertex 2 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def thetaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) thetaGraph := by
  refine ⟨⟨thetaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [thetaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def jThetaVertex (copy : Fin 2) : SubdivisionVertex 2 → JVertex
  | .inl (.inl base) => .inl (.inl (jBase copy base))
  | .inl (.inr center) => .inl (.inr (copy, center))
  | .inr (base, center) => .inr (.inl (copy, (base, center)))

def jThetaCopy (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph jTemplate := by
  refine ⟨⟨jThetaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 2) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · left
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · right
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
  · fin_cases copy <;> decide

lemma jThetaVertex_mem (copy : Fin 2)
    (v : SubdivisionVertex 2) :
    InJCopy copy (jThetaVertex copy v) := by
  rcases v with (base | center) | pair
  · exact ⟨base, rfl⟩
  · simp only [InJCopy, jThetaVertex]
  · simp only [InJCopy, jThetaVertex, Prod.mk.eta]

def gammaCycleVertex : Fin 8 → SubdivisionVertex 3 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def gammaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) gammaGraph := by
  refine ⟨⟨gammaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [gammaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def kGammaVertex (copy : Fin 2)
    (v : SubdivisionVertex 3) : KVertex := (copy, v)

def kGammaCopy (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph kTemplate := by
  refine ⟨⟨kGammaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 3) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · left
        exact Or.inl ⟨rfl, hforward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · right
        exact Or.inl ⟨rfl, hbackward⟩
  · intro u v h
    exact congrArg Prod.snd h

def copyToQuotient {α β : Type*}
    (source : SimpleGraph β) (target : SimpleGraph α)
    (f : α → α) (copy : SimpleGraph.Copy source target)
    (hinj : Function.Injective (fun v : β => f (copy v))) :
    SimpleGraph.Copy source (quotientGraph target f) := by
  refine ⟨⟨fun v => ⟨f (copy v), ⟨copy v, rfl⟩⟩, ?_⟩, ?_⟩
  · intro u v hadj
    apply (SimpleGraph.fromRel_adj
      (quotientRelation target f) _ _).mpr
    constructor
    · intro heq
      exact hadj.ne (hinj (congrArg Subtype.val heq))
    · left
      exact ⟨copy u, copy v, rfl, rfl, copy.toHom.map_rel hadj⟩
  · intro u v heq
    exact hinj (congrArg Subtype.val heq)

lemma not_acyclic_of_eight_cycle_copy
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by
  intro hacyclic
  have hcycle : (SimpleGraph.cycleGraph 8).IsAcyclic :=
    hacyclic.comap copy.toHom copy.injective
  exact hcycle (SimpleGraph.cycleGraph.cycle 5)
    (SimpleGraph.cycleGraph.isCycle_cycle)

lemma encodeFiniteGraph_not_acyclic
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded

lemma jTheta_quotient_injective
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by
  intro u v heq
  have htemplate : jThetaVertex copy u = jThetaVertex copy v :=
    hf.2.2 copy (jThetaVertex_mem copy u)
      (jThetaVertex_mem copy v) heq
  exact (jThetaCopy copy).injective htemplate

theorem jQuotient_not_acyclic
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient thetaGraph jTemplate f (jThetaCopy 0)
    (jTheta_quotient_injective hf 0)).comp thetaCycleCopy

lemma kGamma_quotient_injective
    {f : KVertex → KVertex} (hf : KAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 3 =>
      f (kGammaVertex copy v)) := by
  intro u v heq
  have htemplate : kGammaVertex copy u = kGammaVertex copy v :=
    hf.2 copy (show (kGammaVertex copy u).1 = copy from rfl)
      (show (kGammaVertex copy v).1 = copy from rfl) heq
  exact (kGammaCopy copy).injective htemplate

theorem kQuotient_not_acyclic
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient gammaGraph kTemplate f (kGammaCopy 0)
    (kGamma_quotient_injective hf 0)).comp gammaCycleCopy

theorem four_cycle_not_acyclic :
    ¬ (finiteCycle 4).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 1)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem six_cycle_not_acyclic :
    ¬ (finiteCycle 6).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 3)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem proposedFamily_isCyclic : IsCyclicFamily proposedFamily :=
  proposedFamily_induction (P := fun graph => ¬ graph.graph.IsAcyclic)
    four_cycle_not_acyclic six_cycle_not_acyclic
    (fun _ hf => jQuotient_not_acyclic hf)
    (fun _ hf => kQuotient_not_acyclic hf)

end Cyclicity

noncomputable section CharacteristicAvoidance

open SimpleGraph

section PointClass

variable (K : Type*) [Field K]

def SymplecticPointRelated (p q : SymplecticPoint K) : Prop :=
  p ≠ q ∧ ∃ L : SymplecticLine K, p.1 ≤ L.1 ∧ q.1 ≤ L.1

lemma symplecticPointRelated_symm
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by
  obtain ⟨hpq, L, hpL, hqL⟩ := h
  exact ⟨Ne.symm hpq, L, hqL, hpL⟩

lemma symplecticPointRelated_iff_orthogonal
    (p q : SymplecticPoint K) :
    SymplecticPointRelated K p q ↔
      p ≠ q ∧ p.1 ≤ SymplecticPointOrthogonal K q := by
  constructor
  · rintro ⟨hpq, L, hpL, hqL⟩
    refine ⟨hpq, ?_⟩
    intro x hx
    change ∀ y ∈ q.1, standardSymplecticForm K y x = 0
    intro y hy
    exact L.2.2 y (hqL hy) x (hpL hx)
  · rintro ⟨hpq, hporth⟩
    let U : Submodule K (SymplecticVector K) := p.1 ⊔ q.1
    have hdim : Module.finrank K U = 2 :=
      symplecticPoint_sup_finrank K hpq
    have hqU : q.1 ≤ U := le_sup_right
    have hUorth : U ≤ SymplecticPointOrthogonal K q :=
      sup_le hporth (symplecticPoint_le_orthogonal K q)
    exact ⟨hpq,
      ⟨U, hdim, symplectic_two_plane_isotropic K hdim hqU hUorth⟩,
      le_sup_left, le_sup_right⟩

lemma symplecticPointRelated_of_quadrangle_common_neighbor
    {p q : SymplecticPoint K}
    (hpq : p ≠ q) {v : QuadrangleVertex K}
    (hpv : (symplecticQuadrangle K).Adj (.inl p) v)
    (hqv : (symplecticQuadrangle K).Adj (.inl q) v) :
    SymplecticPointRelated K p q := by
  obtain ⟨L, hv, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hpv
  rw [hv] at hqv
  exact ⟨hpq, L, hpL,
    (symplecticQuadrangle_incidence_adj K q L).mp hqv⟩

lemma subdivisionGraph_base_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

lemma subdivisionGraph_center_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

lemma subdivisionPoint_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    ∃ L : SymplecticLine K,
      copy (.inr (base, center)) = .inr L ∧
        p.1 ≤ L.1 ∧ c.1 ≤ L.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨L, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K c L).mp hcenteradj⟩

lemma subdivisionPoint_center_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨c, hc, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj.symm
  exact ⟨c, hc⟩

lemma subdivisionPoint_base_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ q : SymplecticPoint K,
      copy (.inl (.inl otherBase)) = .inl q := by
  obtain ⟨c, hc⟩ := subdivisionPoint_center_of_point_base K
    copy (center := center) hbase
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (otherBase, center))) at hcenteradj
  rw [hc] at hcenteradj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj
  have hotheradj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl otherBase)))
    (copy (.inr (otherBase, center))) at hotheradj
  rw [hpair] at hotheradj
  obtain ⟨q, hq, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hotheradj.symm
  exact ⟨q, hq⟩

lemma subdivisionPoint_base_center_related
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by
  obtain ⟨L, _, hpL, hcL⟩ :=
    subdivisionPoint_pair_incidence K copy hbase hcenter
  refine ⟨?_, L, hpL, hcL⟩
  intro hpc
  have hvertex :
      (Sum.inl (Sum.inl base) : SubdivisionVertex k) =
        .inl (.inr center) := by
    apply copy.injective
    change copy (.inl (.inl base)) =
      copy (.inl (.inr center))
    rw [hbase, hcenter, hpc]
  cases hvertex

lemma subdivisionPoint_bases_unrelated
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (p : Fin 3 → SymplecticPoint K)
    (c : Fin k → SymplecticPoint K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inl (c center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    ¬ SymplecticPointRelated K (p i) (p j) := by
  obtain ⟨Li, hi_pair, hpiLi, hcLi⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase i)
      (hcenter center)
  obtain ⟨Lj, hj_pair, hpjLj, hcLj⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase j)
      (hcenter center)
  have hic : SymplecticPointRelated K (p i) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase i)
      (hcenter center)
  have hjc : SymplecticPointRelated K (p j) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase j)
      (hcenter center)
  rintro ⟨_, Lij, hpiLij, hpjLij⟩
  have hlines : Li = Lj :=
    symplectic_triangle_lines_eq K hic.1
      (symplecticPointRelated_symm K hjc).1
      hpiLi hcLi hpiLij hpjLij hcLj hpjLj
  have hpair :
      copy (.inr (i, center)) = copy (.inr (j, center)) := by
    rw [hi_pair, hj_pair, hlines]
  have hsource :
      (Sum.inr (i, center) : SubdivisionVertex k) =
        .inr (j, center) := copy.injective hpair
  exact hij (congrArg Prod.fst (Sum.inr.inj hsource))

lemma symplecticPointSpan_orthogonal_finrank
    {y z : SymplecticPoint K} (hyz : y ≠ z) :
    Module.finrank K
      ((standardSymplecticBilin K).orthogonal
        (y.1 ⊔ z.1)) = 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K),
    symplecticPoint_sup_finrank K hyz]
  simp only [SymplecticVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.reduceSub]

lemma symplecticPoint_centers_span_orthogonal
    {y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    c.1 ⊔ d.1 =
      (standardSymplecticBilin K).orthogonal (y.1 ⊔ z.1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hcy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hcz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hdy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hdz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
  · rw [symplecticPoint_sup_finrank K hcd,
      symplecticPointSpan_orthogonal_finrank K hyz]

lemma symplecticPoint_mem_span_of_two_centers
    {x y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcx : c.1 ≤ SymplecticPointOrthogonal K x)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdx : d.1 ≤ SymplecticPointOrthogonal K x)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    x.1 ≤ y.1 ⊔ z.1 := by
  have hcenters := symplecticPoint_centers_span_orthogonal K
    hyz hcd hcy hcz hdy hdz
  have hxorth :
      x.1 ≤ (standardSymplecticBilin K).orthogonal (c.1 ⊔ d.1) := by
    intro w hw
    change ∀ u ∈ c.1 ⊔ d.1,
      standardSymplecticForm K u w = 0
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [standardSymplecticForm_add_left]
    have haorth : standardSymplecticForm K a w = 0 := by
      have h := hcx ha w hw
      change standardSymplecticForm K w a = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    have hborth : standardSymplecticForm K b w = 0 := by
      have h := hdx hb w hw
      change standardSymplecticForm K w b = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    rw [haorth, hborth, add_zero]
  rw [hcenters,
    LinearMap.BilinForm.orthogonal_orthogonal
      (standardSymplecticBilin_nondegenerate K)
      (standardSymplecticBilin_isAlt K).isRefl] at hxorth
  exact hxorth

theorem symplecticPoint_point_class_avoidance
    {x x' y z c d c' d' : SymplecticPoint K}
    (hyz : y ≠ z)
    (hyz_unrelated : ¬ SymplecticPointRelated K y z)
    (hxx' : x ≠ x')
    (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hcx : SymplecticPointRelated K c x)
    (hcy : SymplecticPointRelated K c y)
    (hcz : SymplecticPointRelated K c z)
    (hdx : SymplecticPointRelated K d x)
    (hdy : SymplecticPointRelated K d y)
    (hdz : SymplecticPointRelated K d z)
    (hc'x' : SymplecticPointRelated K c' x')
    (hc'y : SymplecticPointRelated K c' y)
    (hc'z : SymplecticPointRelated K c' z)
    (hd'x' : SymplecticPointRelated K d' x')
    (hd'y : SymplecticPointRelated K d' y)
    (hd'z : SymplecticPointRelated K d' z) :
    ¬ SymplecticPointRelated K x x' := by
  have hxspan : x.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hcd
      ((symplecticPointRelated_iff_orthogonal K c x).mp hcx).2
      ((symplecticPointRelated_iff_orthogonal K c y).mp hcy).2
      ((symplecticPointRelated_iff_orthogonal K c z).mp hcz).2
      ((symplecticPointRelated_iff_orthogonal K d x).mp hdx).2
      ((symplecticPointRelated_iff_orthogonal K d y).mp hdy).2
      ((symplecticPointRelated_iff_orthogonal K d z).mp hdz).2
  have hx'span : x'.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hc'd'
      ((symplecticPointRelated_iff_orthogonal K c' x').mp hc'x').2
      ((symplecticPointRelated_iff_orthogonal K c' y).mp hc'y).2
      ((symplecticPointRelated_iff_orthogonal K c' z).mp hc'z).2
      ((symplecticPointRelated_iff_orthogonal K d' x').mp hd'x').2
      ((symplecticPointRelated_iff_orthogonal K d' y).mp hd'y).2
      ((symplecticPointRelated_iff_orthogonal K d' z).mp hd'z).2
  intro hrelated
  obtain ⟨_, L, hxL, hx'L⟩ := hrelated
  have hspan : x.1 ⊔ x'.1 = y.1 ⊔ z.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hxspan hx'span)
    rw [symplecticPoint_sup_finrank K hxx',
      symplecticPoint_sup_finrank K hyz]
  have hyzL : y.1 ⊔ z.1 ≤ L.1 := by
    rw [← hspan]
    exact sup_le hxL hx'L
  exact hyz_unrelated
    ⟨hyz, L, le_sup_left.trans hyzL, le_sup_right.trans hyzL⟩

def colorRespectingQuotientProjectionHom
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    graph →g quotientGraph graph f := by
  refine ⟨fun v => ⟨f v, v, rfl⟩, ?_⟩
  intro u v hadj
  apply (SimpleGraph.fromRel_adj
    (quotientRelation graph f)
    (⟨f u, u, rfl⟩ : Set.range f)
    (⟨f v, v, rfl⟩ : Set.range f)).mpr
  constructor
  · intro heq
    exact hproper hadj
      (hf u v (congrArg Subtype.val heq))
  · left
    exact ⟨u, v, rfl, rfl, hadj⟩

lemma jTemplate_adj_color_ne
    {u v : JVertex} (h : jTemplate.Adj u v) :
    jColor u ≠ jColor v := by
  rcases u with (u | u) | (u | u) <;>
    rcases v with (v | v) | (v | v) <;>
    simp_all [jTemplate, SimpleGraph.fromRel_adj,
      jTemplateRelation, jColor]

lemma kTemplate_adj_color_ne
    {u v : KVertex} (h : kTemplate.Adj u v) :
    kColor u ≠ kColor v := by
  rcases u with ⟨u, (u | u) | u⟩ <;>
    rcases v with ⟨v, (v | v) | v⟩ <;>
    simp_all [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kColor, subdivisionColor,
      subdivisionRelation, kSpecifiedCenter]
  all_goals aesop

def jQuotientProjectionHom
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    jTemplate →g quotientGraph jTemplate f :=
  colorRespectingQuotientProjectionHom jTemplate jColor
    (fun _ _ h => jTemplate_adj_color_ne h) f hf.1

def kQuotientProjectionHom
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    kTemplate →g quotientGraph kTemplate f :=
  colorRespectingQuotientProjectionHom kTemplate kColor
    (fun _ _ h => kTemplate_adj_color_ne h) f hf.1

def jThetaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : jTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph host := by
  refine ⟨hom.comp (jThetaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (jThetaVertex copy u) =
    hom (jThetaVertex copy v) at huv
  apply (jThetaCopy copy).injective
  exact hcopies copy (jThetaVertex_mem copy u)
    (jThetaVertex_mem copy v) huv

theorem symplecticQuadrangle_no_point_jTemplate
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (p : Fin 4 → SymplecticPoint K)
    (c : Fin 2 → Fin 2 → SymplecticPoint K)
    (hbase : ∀ base : Fin 4,
      hom (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ (copy center : Fin 2),
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center)) : False := by
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) (base : Fin 3) :
      θ copy (.inl (.inl base)) =
        .inl (p (jBase copy base)) := by
    change hom (jThetaVertex copy (.inl (.inl base))) = _
    simpa only [jThetaVertex] using hbase (jBase copy base)
  have hθcenter (copy center : Fin 2) :
      θ copy (.inl (.inr center)) =
        .inl (c copy center) := by
    change hom (jThetaVertex copy (.inl (.inr center))) = _
    simpa only [jThetaVertex] using hcenter copy center
  have hcenters_inj (copy : Fin 2) :
      Function.Injective (c copy) := by
    intro i j hij
    have himage :
        θ copy (.inl (.inr i)) =
          θ copy (.inl (.inr j)) := by
      rw [hθcenter copy i, hθcenter copy j, hij]
    have hsource :
        (Sum.inl (Sum.inr i) : SubdivisionVertex 2) =
          .inl (.inr j) := (θ copy).injective himage
    exact Sum.inr.inj (Sum.inl.inj hsource)
  have hpoints_inj : Function.Injective p := by
    intro i j hij
    apply hbase_inj
    change hom (.inl (.inl i)) = hom (.inl (.inl j))
    rw [hbase i, hbase j, hij]
  have hyz : p 2 ≠ p 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hpoints_inj h)
  have hxx' : p 0 ≠ p 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hpoints_inj h)
  have hyz_unrelated :
      ¬ SymplecticPointRelated K (p 2) (p 3) := by
    have h := subdivisionPoint_bases_unrelated K (θ 0)
      (fun base => p (jBase 0 base)) (c 0)
      (hθbase 0) (hθcenter 0)
      (by decide : (1 : Fin 3) ≠ 2) 0
    simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte, Fin.reduceEq] using h
  have hrelated (copy : Fin 2) (base : Fin 3)
      (center : Fin 2) :
      SymplecticPointRelated K
        (c copy center) (p (jBase copy base)) :=
    symplecticPointRelated_symm K
      (subdivisionPoint_base_center_related K
        (θ copy) (hθbase copy base) (hθcenter copy center))
  have hcd : c 0 0 ≠ c 0 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 0 h)
  have hc'd' : c 1 0 ≠ c 1 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 1 h)
  have havoid := symplecticPoint_point_class_avoidance K
    (x := p 0) (x' := p 1) (y := p 2) (z := p 3)
    (c := c 0 0) (d := c 0 1)
    (c' := c 1 0) (d' := c 1 1)
    hyz hyz_unrelated hxx' hcd hc'd'
    (by simpa only [Fin.isValue, jBase, ↓reduceIte] using hrelated 0 0 0)
    (by simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hrelated 0 1 0)
    (by simpa only [Fin.isValue, jBase, Fin.reduceEq, ↓reduceIte] using hrelated 0 2 0)
    (by simpa only [Fin.isValue, jBase, ↓reduceIte] using hrelated 0 0 1)
    (by simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hrelated 0 1 1)
    (by simpa only [Fin.isValue, jBase, Fin.reduceEq, ↓reduceIte] using hrelated 0 2 1)
    (by simpa only [Fin.isValue, jBase, ↓reduceIte, one_ne_zero] using hrelated 1 0 0)
    (by simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hrelated 1 1 0)
    (by simpa only [Fin.isValue, jBase, Fin.reduceEq, ↓reduceIte] using hrelated 1 2 0)
    (by simpa only [Fin.isValue, jBase, ↓reduceIte, one_ne_zero] using hrelated 1 0 1)
    (by simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hrelated 1 1 1)
    (by simpa only [Fin.isValue, jBase, Fin.reduceEq, ↓reduceIte] using hrelated 1 2 1)
  have hjoin0 : jTemplate.Adj
      (.inl (.inl (0 : Fin 4)))
      (.inr (.inr ())) := by
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      zero_ne_one, or_false, and_self]
  have hjoin1 : jTemplate.Adj
      (.inl (.inl (1 : Fin 4)))
      (.inr (.inr ())) := by
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      one_ne_zero, or_true, or_false, and_self]
  have hleft := hom.map_rel hjoin0
  have hright := hom.map_rel hjoin1
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hleft
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hright
  rw [hbase 0] at hleft
  rw [hbase 1] at hright
  exact havoid
    (symplecticPointRelated_of_quadrangle_common_neighbor K
      hxx' hleft hright)

theorem symplecticQuadrangle_no_point_jTemplate_of_bases
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hpoint : ∀ base : Fin 4,
      ∃ p : SymplecticPoint K,
        hom (.inl (.inl base)) = .inl p) : False := by
  classical
  let p : Fin 4 → SymplecticPoint K :=
    fun base => Classical.choose (hpoint base)
  have hp (base : Fin 4) :
      hom (.inl (.inl base)) = .inl (p base) :=
    Classical.choose_spec (hpoint base)
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) :
      θ copy (.inl (.inl (0 : Fin 3))) =
        .inl (p (jBase copy 0)) := by
    change hom (jThetaVertex copy (.inl (.inl 0))) = _
    simpa only [jThetaVertex, Fin.isValue] using hp (jBase copy 0)
  have hcenter_exists (copy center : Fin 2) :
      ∃ q : SymplecticPoint K,
        hom (.inl (.inr (copy, center))) = .inl q := by
    have h := subdivisionPoint_center_of_point_base K
      (θ copy) (center := center) (hθbase copy)
    change ∃ q : SymplecticPoint K,
      hom (jThetaVertex copy (.inl (.inr center))) = .inl q at h
    simpa only [Subtype.exists, jThetaVertex] using h
  let c : Fin 2 → Fin 2 → SymplecticPoint K :=
    fun copy center => Classical.choose (hcenter_exists copy center)
  have hc (copy center : Fin 2) :
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center) :=
    Classical.choose_spec (hcenter_exists copy center)
  exact symplecticQuadrangle_no_point_jTemplate K hom
    hbase_inj hcopies p c hp hc

theorem symplecticQuadrangle_no_point_jTemplate_of_first_base
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hfirst : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (0 : Fin 4))) = .inl p) : False := by
  obtain ⟨p₀, hp₀⟩ := hfirst
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hx : θ 0 (.inl (.inl (0 : Fin 3))) = .inl p₀ := by
    change hom (jThetaVertex 0 (.inl (.inl 0))) = _
    simpa only [jThetaVertex, jBase, Fin.isValue, ↓reduceIte] using hp₀
  have hy : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (2 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (1 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) = .inl p at h
    simpa only [Fin.isValue, Subtype.exists, jThetaVertex, jBase, one_ne_zero, ↓reduceIte] using h
  have hz : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (3 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (2 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) = .inl p at h
    simpa only [Fin.isValue, Subtype.exists, jThetaVertex, jBase, Fin.reduceEq, ↓reduceIte] using h
  obtain ⟨py, hpy⟩ := hy
  have hy' : θ 1 (.inl (.inl (1 : Fin 3))) = .inl py := by
    change hom (jThetaVertex 1 (.inl (.inl 1))) = _
    simpa only [jThetaVertex, jBase, Fin.isValue, one_ne_zero, ↓reduceIte] using hpy
  have hx' : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (1 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 1)
      (otherBase := (0 : Fin 3)) 0 hy'
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) = .inl p at h
    simpa only [Fin.isValue, Subtype.exists, jThetaVertex, jBase, ↓reduceIte, one_ne_zero] using h
  apply symplecticQuadrangle_no_point_jTemplate_of_bases K
    hom hbase_inj hcopies
  intro base
  fin_cases base
  · exact ⟨p₀, hp₀⟩
  · exact hx'
  · exact ⟨py, hpy⟩
  · exact hz

theorem symplecticQuadrangle_jTemplate_first_base_is_line
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) :
    ∃ L : SymplecticLine K,
      hom (.inl (.inl (0 : Fin 4))) = .inr L := by
  cases h : hom (.inl (.inl (0 : Fin 4))) with
  | inl p =>
      exact False.elim
        (symplecticQuadrangle_no_point_jTemplate_of_first_base K
          hom hbase_inj hcopies ⟨p, h⟩)
  | inr L => exact ⟨L, rfl⟩

def kGammaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : kTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy})
    (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph host := by
  refine ⟨hom.comp (kGammaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (kGammaVertex copy u) =
    hom (kGammaVertex copy v) at huv
  apply (kGammaCopy copy).injective
  exact hcopies copy (show (kGammaVertex copy u).1 = copy from rfl)
    (show (kGammaVertex copy v).1 = copy from rfl) huv

theorem symplecticQuadrangle_kTemplate_has_line_gamma
    (hom : kTemplate →g symplecticQuadrangle K)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) :
    ∃ (i : Fin 2) (L : SymplecticLine K),
      (kGammaHomCopy hom hcopies i) kSpecifiedCenter = .inr L := by
  have hjoin : kTemplate.Adj
      ((0 : Fin 2), kSpecifiedCenter)
      ((1 : Fin 2), kSpecifiedCenter) := by
    simp only [kTemplate, Fin.isValue, kSpecifiedCenter, fromRel_adj, ne_eq, Prod.mk.injEq, zero_ne_one, and_true,
      not_false_eq_true, kTemplateRelation, false_and, and_self, or_true, one_ne_zero, or_self, or_false]
  have hadj := hom.map_rel hjoin
  change (symplecticQuadrangle K).Adj
    (hom ((0 : Fin 2), kSpecifiedCenter))
    (hom ((1 : Fin 2), kSpecifiedCenter)) at hadj
  cases hzero : hom ((0 : Fin 2), kSpecifiedCenter) with
  | inl p =>
      rw [hzero] at hadj
      obtain ⟨L, hL, _⟩ :=
        symplecticQuadrangle_adjacent_to_point K hadj
      refine ⟨1, L, ?_⟩
      change hom (kGammaVertex 1 kSpecifiedCenter) = .inr L
      simpa only [kGammaVertex, Fin.isValue] using hL
  | inr L =>
      refine ⟨0, L, ?_⟩
      change hom (kGammaVertex 0 kSpecifiedCenter) = .inr L
      simpa only [kGammaVertex, Fin.isValue] using hzero

end PointClass

end CharacteristicAvoidance

noncomputable section SubdivisionLineExtraction

open SimpleGraph

variable (K : Type*) [Field K]

lemma subdivisionLine_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L C : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L)
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ p : SymplecticPoint K,
      copy (.inr (base, center)) = .inl p ∧
        p.1 ≤ L.1 ∧ p.1 ≤ C.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨p, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K p C).mp hcenteradj.symm⟩

lemma subdivisionLine_center_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨C, hC, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj.symm
  exact ⟨C, hC⟩

lemma subdivisionLine_base_of_line_center
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {C : SymplecticLine K}
    (hcenter : copy (.inl (.inr center)) = .inr C) :
    ∃ L : SymplecticLine K,
      copy (.inl (.inl base)) = .inr L := by
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter] at hcenteradj
  obtain ⟨p, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hpair] at hbaseadj
  obtain ⟨L, hL, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj.symm
  exact ⟨L, hL⟩

lemma subdivisionLine_base_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ M : SymplecticLine K,
      copy (.inl (.inl otherBase)) = .inr M := by
  obtain ⟨C, hC⟩ := subdivisionLine_center_of_line_base K
    copy (center := center) hbase
  exact subdivisionLine_base_of_line_center K
    copy (base := otherBase) hC

lemma subdivisionLine_centers_injective
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]

lemma subdivisionLine_bases_disjoint
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by
  apply Submodule.disjoint_def.mpr
  intro x hxi hxj
  by_contra hx
  let p : SymplecticPoint K :=
    ⟨K ∙ x, finrank_span_singleton hx⟩
  have hpLi : p.1 ≤ (L i).1 :=
    (Submodule.span_le).mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hxi)
  have hpLj : p.1 ≤ (L j).1 :=
    (Submodule.span_le).mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hxj)
  obtain ⟨pi, hpairi, hpiLi, hpiC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase i) (hcenter center)
  obtain ⟨pj, hpairj, hpjLj, hpjC⟩ :=
    subdivisionLine_pair_incidence K copy (hbase j) (hcenter center)
  have hpipj : pi ≠ pj := by
    intro heq
    apply hij
    have hsource :
        (Sum.inr (i, center) : SubdivisionVertex k) =
          .inr (j, center) := by
      apply copy.injective
      change copy (.inr (i, center)) =
        copy (.inr (j, center))
      rw [hpairi, hpairj, heq]
    exact congrArg Prod.fst (Sum.inr.inj hsource)
  have hcenterNeBase (base : Fin 3) : C center ≠ L base := by
    intro heq
    have hsource :
        (Sum.inl (Sum.inr center) : SubdivisionVertex k) =
          .inl (.inl base) := by
      apply copy.injective
      change copy (.inl (.inr center)) =
        copy (.inl (.inl base))
      rw [hcenter center, hbase base, heq]
    cases Sum.inl.inj hsource
  have hpjp : pj ≠ p := by
    intro heq
    have hpjLi : pj.1 ≤ (L i).1 := by
      simpa only [heq] using hpLi
    have hline : C center = L i :=
      symplecticLine_eq_of_points K hpipj
        hpiC hpjC hpiLi hpjLi
    exact hcenterNeBase i hline
  have hline : C center = L j :=
    symplectic_triangle_lines_eq K hpipj hpjp
      hpiC hpjC hpiLi hpLi hpjLj hpLj
  exact hcenterNeBase j hline

end SubdivisionLineExtraction

noncomputable section Padding

open SimpleGraph

def GraphHasNoIsolated {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ u : V, ∃ v : V, graph.Adj u v

lemma free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa only [Fintype.card_fin] using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa only [ge_iff_le, Fintype.card_fin] using hbound

lemma cycleGraph_no_isolated (k : ℕ) :
    ∀ u : Fin (k + 2),
      ∃ v : Fin (k + 2),
        (SimpleGraph.cycleGraph (k + 2)).Adj u v := by
  intro u
  refine ⟨u + 1, ?_⟩
  change u + 1 ∈
    (SimpleGraph.cycleGraph (k + 2)).neighborSet u
  rw [SimpleGraph.cycleGraph_neighborSet]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

lemma quotientGraph_no_isolated
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v)
    (f : V → V) (hf : ColorRespecting color f) :
    ∀ u : Set.range f,
      ∃ v : Set.range f, (quotientGraph graph f).Adj u v := by
  rintro ⟨_, ⟨u, rfl⟩⟩
  obtain ⟨v, huv⟩ := hneighbors u
  refine ⟨⟨f v, v, rfl⟩, ?_⟩
  exact (colorRespectingQuotientProjectionHom
    graph color hproper f hf).map_rel huv

lemma map_equiv_no_isolated
    {V W : Type*} (graph : SimpleGraph V) (e : V ≃ W)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    ∀ u : W, ∃ v : W, (graph.map e.toEmbedding).Adj u v := by
  intro u
  obtain ⟨v, huv⟩ := hneighbors (e.symm u)
  refine ⟨e v, ?_⟩
  have h :=
    (SimpleGraph.map_adj_apply
      (G := graph) (f := e.toEmbedding)
      (a := e.symm u) (b := v)).mpr huv
  simpa only [Function.Embedding.coeFn_mk, Equiv.apply_symm_apply] using h

lemma encodeFiniteGraph_no_isolated
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by
  classical
  exact map_equiv_no_isolated graph (Fintype.equivFin V) hneighbors

lemma jTemplate_no_isolated :
    GraphHasNoIsolated jTemplate := by
  intro u
  rcases u with (base | ⟨copy, center⟩) |
    (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · refine ⟨.inr (.inr ()), ?_⟩
      simp only [jTemplate, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq,
        not_false_eq_true, jTemplateRelation, zero_ne_one, or_false, and_self]
    · refine ⟨.inr (.inr ()), ?_⟩
      simp only [jTemplate, Nat.reduceAdd, Fin.mk_one, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq,
        not_false_eq_true, jTemplateRelation, one_ne_zero, or_true, or_false, and_self]
    · refine ⟨.inr (.inl (0, (1, 0))), ?_⟩
      simp only [jTemplate, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq,
        not_false_eq_true, jTemplateRelation, jBase, one_ne_zero, ↓reduceIte, or_false, and_self]
    · refine ⟨.inr (.inl (0, (2, 0))), ?_⟩
      simp only [jTemplate, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq,
        not_false_eq_true, jTemplateRelation, jBase, Fin.reduceEq, ↓reduceIte, or_false, and_self]
  · refine ⟨.inr (.inl (copy, (0, center))), ?_⟩
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      and_self, or_false]
  · refine ⟨.inl (.inl (jBase copy base)), ?_⟩
    simp only [jTemplate, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation, or_true,
      and_self]
  · refine ⟨.inl (.inl 0), ?_⟩
    cases lastVertex
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      zero_ne_one, or_false, or_true, and_self]

lemma kTemplate_no_isolated :
    GraphHasNoIsolated kTemplate := by
  intro u
  rcases u with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · refine ⟨(copy, .inr (base, 0)), ?_⟩
    simp only [kTemplate, Fin.isValue, fromRel_adj, ne_eq, Prod.mk.injEq, reduceCtorEq, and_false,
      not_false_eq_true, kTemplateRelation, subdivisionRelation, and_self, true_or, false_or]
  · refine ⟨(copy, .inr (0, center)), ?_⟩
    simp only [kTemplate, Fin.isValue, fromRel_adj, ne_eq, Prod.mk.injEq, reduceCtorEq, and_false,
      not_false_eq_true, kTemplateRelation, subdivisionRelation, and_self, true_or, false_or]
  · refine ⟨(copy, .inl (.inl base)), ?_⟩
    simp only [kTemplate, fromRel_adj, ne_eq, Prod.mk.injEq, reduceCtorEq, and_false, not_false_eq_true,
      kTemplateRelation, subdivisionRelation, Fin.isValue, false_or, and_self, true_or, or_true]

lemma encodedJQuotient_no_isolated
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph jTemplate f)
    (quotientGraph_no_isolated jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h)
      jTemplate_no_isolated f hf.1)

lemma encodedKQuotient_no_isolated
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph kTemplate f)
    (quotientGraph_no_isolated kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h)
      kTemplate_no_isolated f hf.1)

theorem proposedFamily_member_no_isolated
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    GraphHasNoIsolated forbidden.graph :=
  proposedFamily_induction (P := fun graph => GraphHasNoIsolated graph.graph)
    (cycleGraph_no_isolated 2) (cycleGraph_no_isolated 4)
    (fun _ hf => encodedJQuotient_no_isolated hf)
    (fun _ hf => encodedKQuotient_no_isolated hf)
    forbidden hforbidden

lemma nat_le_pow_of_two_le
    {t : ℕ} (ht : 2 ≤ t) (j : ℕ) : j ≤ t ^ j := by
  exact (Nat.lt_pow_self (show 1 < t by omega)).le

theorem quadrangleVertexCount_parameter_lt (q : ℕ) :
    q < quadrangleVertexCount q := by
  unfold quadrangleVertexCount
  nlinarith [sq_nonneg q]

theorem quadrangle_prime_power_bracketing
    {t n : ℕ} (ht : 2 ≤ t)
    (hn : quadrangleVertexCount t ≤ n) :
    ∃ j : ℕ, 0 < j ∧
      quadrangleVertexCount (t ^ j) ≤ n ∧
      n < t ^ 3 * quadrangleVertexCount (t ^ j) := by
  let P : ℕ → Prop := fun j =>
    quadrangleVertexCount (t ^ j) ≤ n
  let j := Nat.findGreatest P (n + 1)
  have hone : P 1 := by
    simpa [P] using hn
  have hjfit : P j :=
    Nat.findGreatest_spec (P := P)
      (show 1 ≤ n + 1 by omega) hone
  have hjpositive : 0 < j := by
    have hle : 1 ≤ j := Nat.le_findGreatest
      (show 1 ≤ n + 1 by omega) hone
    omega
  have hjn : j ≤ n := by
    have hpow := nat_le_pow_of_two_le ht j
    have hvertex := quadrangleVertexCount_parameter_lt (t ^ j)
    change quadrangleVertexCount (t ^ j) ≤ n at hjfit
    omega
  have hnext : ¬ P (j + 1) :=
    Nat.findGreatest_is_greatest (P := P)
      (show j < j + 1 by omega)
      (show j + 1 ≤ n + 1 by omega)
  have hnnext :
      n < quadrangleVertexCount (t * t ^ j) := by
    have h := Nat.lt_of_not_ge hnext
    change n < quadrangleVertexCount (t ^ (j + 1)) at h
    simpa only [gt_iff_lt, pow_succ, Nat.mul_comm] using h
  have hgap := quadrangleVertexCount_mul_le (t ^ j) t
    (show 1 ≤ t by omega)
  exact ⟨j, hjpositive, hjfit, lt_of_lt_of_le hnnext hgap⟩

theorem quadrangle_extremal_lower_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hfree : forbidden.Free (symplecticQuadrangle K)) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber
        (quadrangleVertexCount (Nat.card K)) forbidden := by
  classical
  letI : Fintype (QuadrangleVertex K) := Fintype.ofFinite _
  have hvertex : Fintype.card (QuadrangleVertex K) =
      quadrangleVertexCount (Nat.card K) := by
    rw [← Nat.card_eq_fintype_card, symplecticQuadrangle_vertex_card]
    rfl
  calc
    quadrangleEdgeCount (Nat.card K) =
        (symplecticQuadrangle K).edgeFinset.card := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
        symplecticQuadrangle_edge_card]
      rfl
    _ ≤ SimpleGraph.extremalNumber
          (Fintype.card (QuadrangleVertex K)) forbidden :=
      SimpleGraph.card_edgeFinset_le_extremalNumber hfree
    _ = SimpleGraph.extremalNumber
          (quadrangleVertexCount (Nat.card K)) forbidden := by
      rw [hvertex]

theorem quadrangle_extremal_lower_padded_of_free
    (K : Type*) [Field K] [Finite K]
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (hfree : forbidden.Free (symplecticQuadrangle K))
    {n : ℕ} (hn : quadrangleVertexCount (Nat.card K) ≤ n) :
    quadrangleEdgeCount (Nat.card K) ≤
      SimpleGraph.extremalNumber n forbidden := by
  exact (quadrangle_extremal_lower_of_free K forbidden hfree).trans
    (extremalNumber_monotone_of_no_isolated forbidden hneighbors hn)

theorem quadrangle_manuscript_scaled_density_of_gap
    (q n : ℕ)
    (hgap : n ≤ 27 * quadrangleVertexCount q) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  have hreal :
      (n : ℝ) ≤ (27 : ℝ) * (quadrangleVertexCount q : ℝ) := by
    exact_mod_cast hgap
  calc
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        (n : ℝ) ^ ((4 : ℝ) / 3) ≤
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
        ((27 : ℝ) * (quadrangleVertexCount q : ℝ)) ^
          ((4 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hreal (by positivity))
        (by positivity)
    _ = (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      have hcancel :
          (27 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ ((4 : ℝ) / 3) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 27)]
        norm_num
      calc
        ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
            ((27 : ℝ) ^ ((4 : ℝ) / 3) *
              (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) =
          (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
            ((27 : ℝ) ^ (-((4 : ℝ) / 3)) *
              (27 : ℝ) ^ ((4 : ℝ) / 3)) *
                (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) := by
          ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (quadrangleEdgeCount q : ℝ) := quadrangle_rpow_density q

theorem quadrangle_uniform_lower_of_prime_power_avoidance
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.Free (symplecticQuadrangle (GaloisField t j)))
    {n : ℕ} (hn : quadrangleVertexCount t ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
  obtain ⟨j, hj, hfit, hgap⟩ :=
    quadrangle_prime_power_bracketing ht hn
  let K := GaloisField t j
  have hcard : Nat.card K = t ^ j :=
    GaloisField.card t j (Nat.ne_of_gt hj)
  have hfitK : quadrangleVertexCount (Nat.card K) ≤ n := by
    simpa only [hcard] using hfit
  have havoid : forbidden.Free (symplecticQuadrangle K) :=
    hfree j hj
  have hedge := quadrangle_extremal_lower_padded_of_free K
    forbidden hneighbors havoid hfitK
  have hedge' :
      (quadrangleEdgeCount (t ^ j) : ℝ) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by
    exact_mod_cast (show quadrangleEdgeCount (t ^ j) ≤
      SimpleGraph.extremalNumber n forbidden by
        simpa only [hcard] using hedge)
  have hfactor :
      t ^ 3 * quadrangleVertexCount (t ^ j) ≤
        27 * quadrangleVertexCount (t ^ j) :=
    Nat.mul_le_mul_right (quadrangleVertexCount (t ^ j)) htgap
  have hgap27 : n ≤ 27 * quadrangleVertexCount (t ^ j) :=
    (Nat.le_of_lt hgap).trans hfactor
  exact (quadrangle_manuscript_scaled_density_of_gap
    (t ^ j) n hgap27).trans hedge'

theorem four_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 4)
    (by simpa only [Nat.reduceAdd] using cycleGraph_no_isolated 2)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_four_cycle_free _) hn

theorem six_cycle_uniform_manuscript_lower
    {n : ℕ} (hn : quadrangleVertexCount 3 ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  exact quadrangle_uniform_lower_of_prime_power_avoidance
    (SimpleGraph.cycleGraph 6)
    (by simpa only [Nat.reduceAdd] using cycleGraph_no_isolated 4)
    3 (by norm_num) (by norm_num)
    (fun _ _ => symplecticQuadrangle_six_cycle_free _) hn

end Padding

noncomputable section LocalGeometry

open SimpleGraph

theorem common_neighbor_unique_of_four_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x)
    (huy : G.Adj u y) (hvy : G.Adj v y) : x = y := by
  by_contra hxy
  apply hfree
  let f : Fin 4 → V := ![u, x, v, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [f, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero] <;>
      first
      | exact hux
      | exact hux.symm
      | exact hvx
      | exact hvx.symm
      | exact huy
      | exact huy.symm
      | exact hvy
      | exact hvy.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, huv, huv.symm, hxy, Ne.symm hxy,
        hux.ne, hux.symm.ne, hvx.ne, hvx.symm.ne,
        huy.ne, huy.symm.ne, hvy.ne, hvy.symm.ne] at hij ⊢

def CommonNeighborRelated {V : Type*} (G : SimpleGraph V)
    (u v : V) : Prop :=
  u ≠ v ∧ ∃ w : V, G.Adj u w ∧ G.Adj v w

lemma commonNeighborRelated_symm
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : CommonNeighborRelated G u v) :
    CommonNeighborRelated G v u := by
  obtain ⟨hne, w, huw, hvw⟩ := h
  exact ⟨hne.symm, w, hvw, huw⟩

lemma bipartite_coloring_eq_of_common_neighbor
    {V : Type*} {G : SimpleGraph V}
    (color : G.Coloring (Fin 2)) {u v w : V}
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    color u = color v := by
  have hu := color.valid huw
  have hv := color.valid hvw
  apply Fin.ext
  omega

theorem common_neighbors_triangle_eq_of_cycle_free
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v w a b c : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hwb : G.Adj w b)
    (hwc : G.Adj w c) (huc : G.Adj u c) :
    a = b ∧ b = c := by
  by_cases hab : a = b
  · subst b
    refine ⟨rfl, ?_⟩
    exact common_neighbor_unique_of_four_cycle_free hfour huw
      hua hwb huc hwc
  by_cases hbc : b = c
  · subst c
    have hac : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour huv
        hua hva huc hvb
    exact (hab hac).elim
  by_cases hac : a = c
  · subst c
    have hab' : a = b :=
      common_neighbor_unique_of_four_cycle_free hfour hvw
        hva hwc hvb hwb
    exact (hab hab').elim
  obtain ⟨color⟩ := hbip
  have hcolor_uv : color u = color v :=
    bipartite_coloring_eq_of_common_neighbor color hua hva
  have hcolor_vw : color v = color w :=
    bipartite_coloring_eq_of_common_neighbor color hvb hwb
  have hub : u ≠ b := by
    intro h
    subst b
    exact color.valid hvb hcolor_uv.symm
  have hvc : v ≠ c := by
    intro h
    subst c
    exact color.valid huc hcolor_uv
  have hwa : w ≠ a := by
    intro h
    subst a
    exact color.valid hva hcolor_vw
  exfalso
  apply hsix
  let f : Fin 6 → V := ![u, a, v, b, w, c]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [f, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero] <;>
      first
      | exact hua
      | exact hua.symm
      | exact hva
      | exact hva.symm
      | exact hvb
      | exact hvb.symm
      | exact hwb
      | exact hwb.symm
      | exact hwc
      | exact hwc.symm
      | exact huc
      | exact huc.symm
      | exact False.elim ((of_decide_eq_false rfl) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, huv, huv.symm, hvw, hvw.symm, huw, huw.symm,
        hab, Ne.symm hab, hbc, Ne.symm hbc, hac, Ne.symm hac,
        hua.ne, hua.symm.ne, hva.ne, hva.symm.ne,
        hvb.ne, hvb.symm.ne, hwb.ne, hwb.symm.ne,
        hwc.ne, hwc.symm.ne, huc.ne, huc.symm.ne,
        hub, hub.symm, hvc, hvc.symm, hwa, hwa.symm] at hij ⊢

theorem common_second_neighbors_pairwise_unrelated
    {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v x y : V} (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (hxu : CommonNeighborRelated G x u)
    (hxv : CommonNeighborRelated G x v)
    (hyu : CommonNeighborRelated G y u)
    (hyv : CommonNeighborRelated G y v) :
    ¬ CommonNeighborRelated G x y := by
  rintro ⟨hxy, b, hxb, hyb⟩
  obtain ⟨hxu_ne, a, hxa, hua⟩ := hxu
  obtain ⟨hxv_ne, d, hxd, hvd⟩ := hxv
  obtain ⟨hyu_ne, c, hyc, huc⟩ := hyu
  obtain ⟨hyv_ne, e, hye, hve⟩ := hyv
  have habc : a = c ∧ c = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxu_ne (Ne.symm hyu_ne) hxy
      hxa hua huc hyc hyb hxb
  have hdeb : d = e ∧ e = b :=
    common_neighbors_triangle_eq_of_cycle_free hbip hfour hsix
      hxv_ne (Ne.symm hyv_ne) hxy
      hxd hvd hve hye hyb hxb
  apply hunrelated
  refine ⟨huv, b, ?_, ?_⟩
  · rwa [habc.1.trans habc.2] at hua
  · rwa [hdeb.1.trans hdeb.2] at hvd

section FourPathCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingNeighbor (G : SimpleGraph V)
    (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}

lemma card_nonbacktrackingNeighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by
  classical
  calc
    Fintype.card (NonbacktrackingNeighbor G previous current) =
        ((G.neighborFinset current).erase previous).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext next
      simp only [ne_eq, and_comm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        mem_neighborFinset]
    _ = G.degree current - 1 := by
      rw [Finset.card_erase_of_mem]
      · rfl
      · simpa only [mem_neighborFinset] using hedge

abbrev NonbacktrackingFourPath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
        NonbacktrackingNeighbor G (w : V) (b : V)

lemma fintype_card_sigma_lower
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by
  classical
  rw [Fintype.card_sigma]
  calc
    baseLower * fiberLower ≤ Fintype.card α * fiberLower :=
      Nat.mul_le_mul_right fiberLower hbase
    _ = ∑ _a : α, fiberLower := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ ∑ a : α, Fintype.card (β a) :=
      Finset.sum_le_sum fun a _ => hfiber a

lemma card_nonbacktrackingFourPath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (NonbacktrackingFourPath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hthird (a : G.neighborSet u)
      (w : NonbacktrackingNeighbor G u (a : V)) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
            NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep w.property.1.symm
    · intro b
      exact hstep b.property.1.symm
  have hsecond (a : G.neighborSet u) :
      (d - 1) * ((d - 1) * (d - 1)) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
              NonbacktrackingNeighbor G (w : V) (b : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · exact hthird a
  have hfirst : d ≤ Fintype.card (G.neighborSet u) := by
    simpa only [G.card_neighborSet_eq_degree] using hdegree u
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        Σ b : NonbacktrackingNeighbor G (a : V) (w : V),
          NonbacktrackingNeighbor G (w : V) (b : V))
    hfirst hsecond
  have hpow : d * (d - 1) ^ 3 =
      d * ((d - 1) * ((d - 1) * (d - 1))) := by ring
  rw [hpow]
  exact hcount

def nonbacktrackingFourPathPair
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingFourPath G u) : V × V :=
  (path.2.2.2.1, path.2.1.1)

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_ne
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    u ≠ (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change u ≠ (v : V)
  intro huv
  have hub : G.Adj u (b : V) := by
    simpa only [huv] using v.property.1.symm
  have hab : (a : V) = (b : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm a.property w.property.1.symm
      hub b.property.1
  exact b.property.2 hab.symm

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPath_endpoint_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    ¬ CommonNeighborRelated G u
      (nonbacktrackingFourPathPair G path).1 := by
  rcases path with ⟨a, w, b, v⟩
  change ¬ CommonNeighborRelated G u (v : V)
  rintro ⟨_, c, huc, hvc⟩
  have huv : u ≠ (v : V) :=
    nonbacktrackingFourPath_endpoint_ne G hfour
      ⟨a, w, b, v⟩
  have hab := common_neighbors_triangle_eq_of_cycle_free
    hbip hfour hsix w.property.2.symm
    v.property.2.symm huv
    a.property w.property.1.symm
    b.property.1 v.property.1.symm hvc huc
  exact b.property.2 hab.1.symm

abbrev FourPathEndpointWitness (G : SimpleGraph V) (u : V) :=
  {pair : V × V //
    u ≠ pair.1 ∧
      ¬ CommonNeighborRelated G u pair.1 ∧
      CommonNeighborRelated G u pair.2 ∧
      CommonNeighborRelated G pair.1 pair.2}

noncomputable instance fourPathEndpointWitnessFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (FourPathEndpointWitness G u) :=
  Fintype.ofFinite _

def nonbacktrackingFourPathWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} (path : NonbacktrackingFourPath G u) :
    FourPathEndpointWitness G u := by
  refine ⟨nonbacktrackingFourPathPair G path,
    nonbacktrackingFourPath_endpoint_ne G hfour path,
    nonbacktrackingFourPath_endpoint_unrelated G hbip hfour hsix path,
    ?_, ?_⟩
  · refine ⟨path.2.1.property.2.symm, path.1,
      path.1.property, path.2.1.property.1.symm⟩
  · refine ⟨path.2.2.2.property.2, path.2.2.1,
      path.2.2.2.property.1.symm,
      path.2.2.1.property.1⟩

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathPair_injective
    (G : SimpleGraph V)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathPair G
        (u := u)) := by
  rintro ⟨a, w, b, v⟩ ⟨a', w', b', v'⟩ hpair
  change ((v : V), (w : V)) =
    ((v' : V), (w' : V)) at hpair
  have hv : (v : V) = (v' : V) :=
    congrArg Prod.fst hpair
  have hw : (w : V) = (w' : V) :=
    congrArg Prod.snd hpair
  have hwa' : G.Adj (w : V) (a' : V) := by
    rw [hw]
    exact w'.property.1.symm
  have haa' : (a : V) = (a' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      w.property.2.symm
      a.property w.property.1.symm
      a'.property hwa'
  have ha : a = a' := Subtype.ext haa'
  subst a'
  have hw' : w = w' := Subtype.ext hw
  subst w'
  have hvb' : G.Adj (v : V) (b' : V) := by
    rw [hv]
    exact v'.property.1.symm
  have hbb' : (b : V) = (b' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      v.property.2.symm
      b.property.1 v.property.1.symm
      b'.property.1 hvb'
  have hb : b = b' := Subtype.ext hbb'
  subst b'
  have hv' : v = v' := Subtype.ext hv
  subst v'
  rfl

omit [Fintype V] [DecidableEq V] in
lemma nonbacktrackingFourPathWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingFourPathWitness G hbip hfour hsix
        (u := u)) := by
  intro p q hpq
  apply nonbacktrackingFourPathPair_injective G hfour
  exact congrArg Subtype.val hpq

lemma four_path_endpoint_witness_count_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (FourPathEndpointWitness G u) := by
  calc
    d * (d - 1) ^ 3 ≤
        Fintype.card (NonbacktrackingFourPath G u) :=
      card_nonbacktrackingFourPath_lower G d hdegree u
    _ ≤ Fintype.card (FourPathEndpointWitness G u) :=
      Fintype.card_le_of_injective
        (nonbacktrackingFourPathWitness G hbip hfour hsix)
        (nonbacktrackingFourPathWitness_injective G hbip hfour hsix)

abbrev UnrelatedFourPathEndpoint (G : SimpleGraph V) (u : V) :=
  {v : V // u ≠ v ∧ ¬ CommonNeighborRelated G u v}

abbrev CommonSecondNeighbor (G : SimpleGraph V) (u v : V) :=
  {w : V //
    CommonNeighborRelated G u w ∧ CommonNeighborRelated G v w}

noncomputable instance unrelatedFourPathEndpointFintype
    (G : SimpleGraph V) (u : V) :
    Fintype (UnrelatedFourPathEndpoint G u) :=
  Fintype.ofFinite _

noncomputable instance commonSecondNeighborFintype
    (G : SimpleGraph V) (u v : V) :
    Fintype (CommonSecondNeighbor G u v) :=
  Fintype.ofFinite _

def fourPathEndpointWitnessEquiv
    (G : SimpleGraph V) (u : V) :
    FourPathEndpointWitness G u ≃
      Σ v : UnrelatedFourPathEndpoint G u,
        CommonSecondNeighbor G u (v : V) where
  toFun pair :=
    ⟨⟨pair.1.1, pair.2.1, pair.2.2.1⟩,
      ⟨pair.1.2, pair.2.2.2.1, pair.2.2.2.2⟩⟩
  invFun pair :=
    ⟨((pair.1 : V), (pair.2 : V)),
      pair.1.2.1, pair.1.2.2,
      pair.2.2.1, pair.2.2.2⟩
  left_inv pair := Subtype.ext rfl
  right_inv pair := by
    rcases pair with ⟨v, w⟩
    rfl

omit [DecidableEq V] in
lemma fourPathEndpointWitness_card_eq_sum
    (G : SimpleGraph V) (u : V) :
    Fintype.card (FourPathEndpointWitness G u) =
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [Fintype.card_congr (fourPathEndpointWitnessEquiv G u),
    Fintype.card_sigma]

theorem four_path_common_second_neighbor_sum_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [← fourPathEndpointWitness_card_eq_sum G u]
  exact four_path_endpoint_witness_count_lower
    G hbip hfour hsix d hdegree u

def CommonNeighborIndependent (G : SimpleGraph V)
    (vertices : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ vertices → y ∈ vertices → x ≠ y →
    ¬ CommonNeighborRelated G x y

omit [Fintype V] in
lemma commonNeighborIndependent_neighborhood_injective
    (G : SimpleGraph V) (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    Function.Injective
      (fun pair :
        (Σ x : {x : V // x ∈ vertices},
          G.neighborSet (x : V)) =>
          (pair.2 : V)) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ hab
  have hxy : (x : V) = (y : V) := by
    by_contra hne
    apply hindependent x.property y.property hne
    refine ⟨hne, (a : V), a.property, ?_⟩
    have hyb : G.Adj (y : V) (b : V) := b.property
    exact Eq.mp
      (congrArg (G.Adj (y : V)) hab.symm) hyb
  have hsub : x = y := Subtype.ext hxy
  subst y
  have hneighbor : a = b := Subtype.ext hab
  subst b
  rfl

lemma commonNeighborIndependent_sum_degree_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices) :
    (∑ x : {x : V // x ∈ vertices}, G.degree (x : V)) ≤
      Fintype.card V := by
  have hcard := Fintype.card_le_of_injective
    (fun pair :
      (Σ x : {x : V // x ∈ vertices},
        G.neighborSet (x : V)) =>
        (pair.2 : V))
    (commonNeighborIndependent_neighborhood_injective
      G vertices hindependent)
  simpa only [Fintype.card_sigma,
    SimpleGraph.card_neighborSet_eq_degree] using hcard

lemma commonNeighborIndependent_card_mul_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (vertices : Finset V)
    (hindependent : CommonNeighborIndependent G vertices)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) :
    vertices.card * d ≤ Fintype.card V := by
  calc
    vertices.card * d = ∑ _x : {x : V // x ∈ vertices}, d := by simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach, smul_eq_mul]
    _ ≤ ∑ x : {x : V // x ∈ vertices}, G.degree (x : V) :=
      Finset.sum_le_sum fun x _ => hdegree x
    _ ≤ Fintype.card V :=
      commonNeighborIndependent_sum_degree_le_card G vertices hindependent

end FourPathCounting

end LocalGeometry

noncomputable section BreadthFirstCounting

open SimpleGraph

section BreadthFirstPaths

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NonbacktrackingThreePath (G : SimpleGraph V) (u : V) :=
  Σ a : G.neighborSet u,
    Σ w : NonbacktrackingNeighbor G u (a : V),
      NonbacktrackingNeighbor G (a : V) (w : V)

def nonbacktrackingThreePathEndpoint
    (G : SimpleGraph V) {u : V}
    (path : NonbacktrackingThreePath G u) : V :=
  path.2.2.1

lemma card_nonbacktrackingThreePath_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    G.degree u * (d - 1) ^ 2 ≤
      Fintype.card (NonbacktrackingThreePath G u) := by
  have hstep {previous current : V}
      (hedge : G.Adj current previous) :
      d - 1 ≤ Fintype.card
        (NonbacktrackingNeighbor G previous current) := by
    rw [card_nonbacktrackingNeighbor G hedge]
    exact Nat.sub_le_sub_right (hdegree current) 1
  have hsecond (a : G.neighborSet u) :
      (d - 1) * (d - 1) ≤
        Fintype.card
          (Σ w : NonbacktrackingNeighbor G u (a : V),
            NonbacktrackingNeighbor G (a : V) (w : V)) := by
    apply fintype_card_sigma_lower
    · exact hstep a.property.symm
    · intro w
      exact hstep w.property.1.symm
  have hroot : G.degree u ≤ Fintype.card (G.neighborSet u) := by
    exact (G.card_neighborSet_eq_degree u).symm.le
  have hcount := fintype_card_sigma_lower
    (β := fun a : G.neighborSet u =>
      Σ w : NonbacktrackingNeighbor G u (a : V),
        NonbacktrackingNeighbor G (a : V) (w : V))
    hroot hsecond
  rw [pow_two]
  exact hcount

omit [Fintype V] in
lemma nonbacktrackingThreePathEndpoint_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingThreePathEndpoint G (u := u)) := by
  rintro ⟨a, w, b⟩ ⟨a', w', b'⟩ hb
  change (b : V) = (b' : V) at hb
  have haa : (a : V) = (a' : V) := by
    by_contra hne
    have hww : (w : V) ≠ (w' : V) := by
      intro heq
      have hwa' : G.Adj (w : V) (a' : V) :=
        Eq.mp
          (congrArg (fun x : V => G.Adj x (a' : V)) heq.symm)
          w'.property.1.symm
      have heqa : (a : V) = (a' : V) :=
        common_neighbor_unique_of_four_cycle_free hfour
          w.property.2.symm
          a.property w.property.1.symm
          a'.property hwa'
      exact hne heqa
    have hwb : G.Adj (w' : V) (b : V) :=
      Eq.mp (congrArg (G.Adj (w' : V)) hb.symm)
        b'.property.1
    have htriangle := common_neighbors_triangle_eq_of_cycle_free
      hbip hfour hsix
      w.property.2.symm hww w'.property.2.symm
      a.property w.property.1.symm
      b.property.1 hwb
      w'.property.1.symm a'.property
    exact b.property.2 htriangle.1.symm
  have ha : a = a' := Subtype.ext haa
  subst a'
  have hwb' : G.Adj (b : V) (w' : V) :=
    Eq.mp (congrArg (fun x : V => G.Adj x (w' : V)) hb.symm)
      b'.property.1.symm
  have hww : (w : V) = (w' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      b.property.2.symm
      w.property.1 b.property.1.symm
      w'.property.1 hwb'
  have hw : w = w' := Subtype.ext hww
  subst w'
  have hb' : b = b' := Subtype.ext hb
  subst b'
  rfl

theorem girthEight_degree_mul_pred_sq_le_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by
  calc
    G.degree u * (d - 1) ^ 2 ≤
        Fintype.card (NonbacktrackingThreePath G u) :=
      card_nonbacktrackingThreePath_lower G d hdegree u
    _ ≤ Fintype.card V :=
      Fintype.card_le_of_injective
        (nonbacktrackingThreePathEndpoint G)
        (nonbacktrackingThreePathEndpoint_injective
          G hbip hfour hsix)

end BreadthFirstPaths

end BreadthFirstCounting

noncomputable section SubdivisionCounting

open SimpleGraph

section SubdivisionCopies

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def subdivisionVertexImage
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V) : SubdivisionVertex k → V
  | .inl (.inl i) => base i
  | .inl (.inr j) => center j
  | .inr (i, j) => pair i j

lemma subdivisionPairVertex_injective
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective
      (fun ij : Fin 3 × Fin k => pair ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hpair
  have hi : i = i' := by
    by_contra hne
    apply hbase_unrelated hne
    refine ⟨fun h => hne (hbase h), pair i j,
      hpair_base i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (base i')) hpair.symm)
      (hpair_base i' j')
  subst i'
  have hj : j = j' := by
    by_contra hne
    apply hcenter_unrelated hne
    refine ⟨fun h => hne (hcenter h), pair i j,
      hpair_center i j, ?_⟩
    exact Eq.mp
      (congrArg (G.Adj (center j')) hpair.symm)
      (hpair_center i j')
  exact Prod.ext rfl hj

lemma subdivisionPairVertex_ne_base
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j : Fin k) (other : Fin 3) :
    pair i j ≠ base other := by
  obtain ⟨color⟩ := hbip
  have hfirst : color (base i) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i j) (hpair_center i j)
  have hother : color (base other) = color (center j) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base other j) (hpair_center other j)
  intro heq
  apply color.valid (hpair_base i j)
  exact hfirst.trans
    (hother.symm.trans (congrArg color heq).symm)

lemma subdivisionPairVertex_ne_center
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    (i : Fin 3) (j other : Fin k) :
    pair i j ≠ center other := by
  obtain ⟨color⟩ := hbip
  have hother : color (base i) = color (center other) :=
    bipartite_coloring_eq_of_common_neighbor color
      (hpair_base i other) (hpair_center i other)
  intro heq
  apply color.valid (hpair_base i j)
  exact hother.trans (congrArg color heq).symm

lemma subdivisionVertexImage_injective
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    Function.Injective (subdivisionVertexImage base center pair) := by
  intro u v huv
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩
  · change base i = base i' at huv
    exact congrArg (fun a : Fin 3 =>
      (Sum.inl (Sum.inl a) : SubdivisionVertex k)) (hbase huv)
  · change base i = center j' at huv
    exact False.elim (hbase_center i j' huv)
  · change base i = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i' j' i huv.symm)
  · change center j = base i' at huv
    exact False.elim (hbase_center i' j huv.symm)
  · change center j = center j' at huv
    exact congrArg (fun a : Fin k =>
      (Sum.inl (Sum.inr a) : SubdivisionVertex k)) (hcenter huv)
  · change center j = pair i' j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i' j' j huv.symm)
  · change pair i j = base i' at huv
    exact False.elim
      (subdivisionPairVertex_ne_base hbip base center pair
        hpair_base hpair_center i j i' huv)
  · change pair i j = center j' at huv
    exact False.elim
      (subdivisionPairVertex_ne_center hbip base center pair
        hpair_base hpair_center i j j' huv)
  · change pair i j = pair i' j' at huv
    have heq : (i, j) = (i', j') :=
      subdivisionPairVertex_injective base center pair
        hbase hcenter hbase_unrelated hcenter_unrelated
        hpair_base hpair_center huv
    exact congrArg
      (fun ij : Fin 3 × Fin k =>
        (Sum.inr ij : SubdivisionVertex k)) heq

lemma subdivisionVertexImage_map_relation
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j))
    {u v : SubdivisionVertex k}
    (hadj : (SubdivisionGraph k).Adj u v) :
    G.Adj (subdivisionVertexImage base center pair u)
      (subdivisionVertexImage base center pair v) := by
  rcases u with (i | j) | ⟨i, j⟩ <;>
    rcases v with (i' | j') | ⟨i', j'⟩ <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation, subdivisionVertexImage]
  all_goals
    first
    | exact (hpair_base _ _).symm
    | exact (hpair_center _ _).symm

def subdivisionCopyOfCommonNeighbors
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (pair : Fin 3 → Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_center : ∀ i j, base i ≠ center j)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hpair_base : ∀ i j, G.Adj (base i) (pair i j))
    (hpair_center : ∀ i j, G.Adj (center j) (pair i j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  refine ⟨⟨subdivisionVertexImage base center pair, ?_⟩, ?_⟩
  · intro u v huv
    exact subdivisionVertexImage_map_relation base center pair
      hpair_base hpair_center huv
  · exact subdivisionVertexImage_injective hbip base center pair
      hbase hcenter hbase_center hbase_unrelated
      hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfRelatedCenters
    (hbip : G.IsBipartite)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenter_unrelated : ∀ ⦃i j : Fin k⦄, i ≠ j →
      ¬ CommonNeighborRelated G (center i) (center j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  classical
  let pair : Fin 3 → Fin k → V :=
    fun i j => Classical.choose (hrelated i j).2
  have hpair_base (i : Fin 3) (j : Fin k) :
      G.Adj (base i) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).1
  have hpair_center (i : Fin 3) (j : Fin k) :
      G.Adj (center j) (pair i j) :=
    (Classical.choose_spec (hrelated i j).2).2
  exact subdivisionCopyOfCommonNeighbors hbip base center pair
    hbase hcenter (fun i j => (hrelated i j).1)
    hbase_unrelated hcenter_unrelated hpair_base hpair_center

noncomputable def subdivisionCopyOfGirthEightCenters
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin k → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    SimpleGraph.Copy (SubdivisionGraph k) G := by
  have hbase01 : base 0 ≠ base 1 := by
    intro heq
    exact (by decide : (0 : Fin 3) ≠ 1) (hbase heq)
  have hcenter_unrelated :
      ∀ ⦃i j : Fin k⦄, i ≠ j →
        ¬ CommonNeighborRelated G (center i) (center j) := by
    intro i j hij
    exact common_second_neighbors_pairwise_unrelated
      hbip hfour hsix hbase01
      (hbase_unrelated (by decide : (0 : Fin 3) ≠ 1))
      (commonNeighborRelated_symm (hrelated 0 i))
      (commonNeighborRelated_symm (hrelated 1 i))
      (commonNeighborRelated_symm (hrelated 0 j))
      (commonNeighborRelated_symm (hrelated 1 j))
  exact subdivisionCopyOfRelatedCenters hbip base center
    hbase hcenter hbase_unrelated hcenter_unrelated hrelated

end SubdivisionCopies

end SubdivisionCounting

noncomputable section QuotientWitnesses

open SimpleGraph

noncomputable def fiberRepresentative
    {α β : Type*} (g : α → β) (b : Set.range g) : α :=
  Classical.choose b.property

lemma fiberRepresentative_spec
    {α β : Type*} (g : α → β) (b : Set.range g) :
    g (fiberRepresentative g b) = b.1 :=
  Classical.choose_spec b.property

noncomputable def kernelNormalForm
    {α β : Type*} (g : α → β) (x : α) : α :=
  fiberRepresentative g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_spec
    {α β : Type*} (g : α → β) (x : α) :
    g (kernelNormalForm g x) = g x :=
  fiberRepresentative_spec g ⟨g x, ⟨x, rfl⟩⟩

lemma kernelNormalForm_eq_iff
    {α β : Type*} (g : α → β) (x y : α) :
    kernelNormalForm g x = kernelNormalForm g y ↔ g x = g y := by
  constructor
  · intro h
    calc
      g x = g (kernelNormalForm g x) :=
        (kernelNormalForm_spec g x).symm
      _ = g (kernelNormalForm g y) := congrArg g h
      _ = g y := kernelNormalForm_spec g y
  · intro h
    unfold kernelNormalForm
    congr 1
    exact Subtype.ext h

lemma kernelNormalForm_idempotent
    {α β : Type*} (g : α → β) (x : α) :
    kernelNormalForm g (kernelNormalForm g x) =
      kernelNormalForm g x := by
  apply (kernelNormalForm_eq_iff g _ _).mpr
  exact kernelNormalForm_spec g x

lemma kernelNormalForm_fixed
    {α β : Type*} (g : α → β)
    (u : Set.range (kernelNormalForm g)) :
    kernelNormalForm g u.1 = u.1 := by
  obtain ⟨x, hx⟩ := u.property
  rw [← hx]
  exact kernelNormalForm_idempotent g x

noncomputable def kernelQuotientCopy
    {α β : Type*} (source : SimpleGraph α)
    (target : SimpleGraph β) (hom : source →g target) :
    SimpleGraph.Copy
      (quotientGraph source (kernelNormalForm hom)) target := by
  refine ⟨⟨fun u => hom u.1, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (quotientRelation source (kernelNormalForm hom))
        u v).mp hadj with ⟨_, hforward | hbackward⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hforward
      have hu : hom u.1 = hom x := by
        calc
          hom u.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hv : hom v.1 = hom y := by
        calc
          hom v.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact hom.map_rel hxy
    · obtain ⟨x, y, hx, hy, hxy⟩ := hbackward
      have hv : hom v.1 = hom x := by
        calc
          hom v.1 = hom (kernelNormalForm hom x) :=
            congrArg hom hx.symm
          _ = hom x := kernelNormalForm_spec hom x
      have hu : hom u.1 = hom y := by
        calc
          hom u.1 = hom (kernelNormalForm hom y) :=
            congrArg hom hy.symm
          _ = hom y := kernelNormalForm_spec hom y
      change target.Adj (hom u.1) (hom v.1)
      rw [hu, hv]
      exact (hom.map_rel hxy).symm
  · intro u v huv
    apply Subtype.ext
    have h := (kernelNormalForm_eq_iff hom u.1 v.1).mpr huv
    rwa [kernelNormalForm_fixed hom u,
      kernelNormalForm_fixed hom v] at h

noncomputable def encodeFiniteGraphCopy
    {α β : Type*} [Fintype α]
    (source : SimpleGraph α) (target : SimpleGraph β)
    (copy : SimpleGraph.Copy source target) :
    SimpleGraph.Copy (encodeFiniteGraph source).graph target := by
  exact copy.comp
    (SimpleGraph.Iso.map (Fintype.equivFin α) source).symm.toCopy

lemma kernelNormalForm_jAdmissible
    {V : Type*} (g : JVertex → V)
    (hcolor : ∀ u v, g u = g v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => g (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v | InJCopy copy v}) :
    JAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro u v huv
    apply hbase
    exact (kernelNormalForm_eq_iff g _ _).mp huv
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

lemma kernelNormalForm_kAdmissible
    {V : Type*} (g : KVertex → V)
    (hcolor : ∀ u v, g u = g v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn g {v : KVertex | v.1 = copy}) :
    KAdmissible (kernelNormalForm g) := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    exact hcolor u v ((kernelNormalForm_eq_iff g u v).mp huv)
  · intro copy u hu v hv huv
    exact hcopies copy hu hv
      ((kernelNormalForm_eq_iff g _ _).mp huv)

theorem proposedFamilyFree_no_jTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : jTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) : False := by
  let f := kernelNormalForm hom
  have hf : JAdmissible f :=
    kernelNormalForm_jAdmissible hom hcolor hbase hcopies
  have hmember := jQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph jTemplate f) host
    (kernelQuotientCopy jTemplate host hom)⟩

theorem proposedFamilyFree_no_kTemplate
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : kTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) : False := by
  let f := kernelNormalForm hom
  have hf : KAdmissible f :=
    kernelNormalForm_kAdmissible hom hcolor hcopies
  have hmember := kQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph kTemplate f) host
    (kernelQuotientCopy kTemplate host hom)⟩

end QuotientWitnesses

section CommutativeRing

variable {K : Type*} [CommRing K]

def symmetricQuadratic (a b c x y : K) : K :=
  a * x ^ 2 + (2 : K) * b * x * y + c * y ^ 2

lemma symmetricQuadratic_eq_bilinear
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by
  unfold symmetricQuadratic
  ring

lemma symmetricDet_zero_diagonal_sub (b b' : K) :
    ((0 : K) * 0 - (b - b') ^ 2) = -((b - b') ^ 2) := by
  simp only [mul_zero, zero_sub]

end CommutativeRing

section CharacteristicTwo

variable {K : Type*} [Field K] [CharP K 2]

lemma symmetricQuadratic_char_two
    (a b c x y : K) :
    symmetricQuadratic a b c x y = a * x ^ 2 + c * y ^ 2 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp only [symmetricQuadratic, htwo, zero_mul, add_zero]

lemma symmetricQuadratic_char_two_eq_square
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by
  rw [symmetricQuadratic_char_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 =
        (r * x) ^ 2 + (s * y) ^ 2 := by ring
    _ = (r * x + s * y) ^ 2 := by
      rw [add_sq]
      simp only [htwo, zero_mul, add_zero]

lemma square_surjective_char_two [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨r, hr⟩ := (isSquare_of_charTwo' a).exists_sq
  exact ⟨r, hr.symm⟩

lemma symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    [Finite K] {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : symmetricQuadratic a b c x y = 0)
    (hsecond : symmetricQuadratic a b c x' y' = 0) :
    a = 0 ∧ c = 0 := by
  obtain ⟨r, hr⟩ := square_surjective_char_two a
  obtain ⟨s, hs⟩ := square_surjective_char_two c
  change r ^ 2 = a at hr
  change s ^ 2 = c at hs
  have hlinfirst : r * x + s * y = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa only [hr, hs] using hfirst
  have hlinsecond : r * x' + s * y' = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa only [hr, hs] using hsecond
  have hrdet : (x * y' - x' * y) * r = 0 := by
    linear_combination y' * hlinfirst - y * hlinsecond
  have hsdet : (x * y' - x' * y) * s = 0 := by
    linear_combination x * hlinsecond - x' * hlinfirst
  have hrzero : r = 0 := (mul_eq_zero.mp hrdet).resolve_left hind
  have hszero : s = 0 := (mul_eq_zero.mp hsdet).resolve_left hind
  constructor
  · simpa only [hrzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hr.symm
  · simpa only [hszero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hs.symm

end CharacteristicTwo

section Field

variable {K : Type*} [Field K]

def symmetricQuadraticEvaluationMatrix
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀ ^ 2, (2 : K) * x₀ * y₀, y₀ ^ 2;
     x₁ ^ 2, (2 : K) * x₁ * y₁, y₁ ^ 2;
     x₂ ^ 2, (2 : K) * x₂ * y₂, y₂ ^ 2]

lemma symmetricQuadraticEvaluationMatrix_det
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by
  rw [Matrix.det_fin_three]
  simp only [symmetricQuadraticEvaluationMatrix, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring

lemma symmetricQuadratic_no_three_independent_roots
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  let A := symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂
  have hdet : A.det ≠ 0 := by
    rw [symmetricQuadraticEvaluationMatrix_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo h01) h02) h12
  have hmul : A.mulVec ![a, b, c] = 0 := by
    funext i
    fin_cases i
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₀
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₁
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₂
  have hzero : ![a, b, c] = (0 : Fin 3 → K) :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have ha : a = 0 := congrFun hzero 0
  have hb : b = 0 := congrFun hzero 1
  have hc : c = 0 := congrFun hzero 2
  exact hcoeff.elim (fun h => h ha)
    (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))

lemma symmetricQuadratic_no_three_roots_of_det_ne_zero
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : (a * c - b ^ 2) ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  apply symmetricQuadratic_no_three_independent_roots
    htwo (a := a) (b := b) (c := c) (x₀ := x₀) (y₀ := y₀)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂)
    (h01 := h01) (h02 := h02) (h12 := h12)
    (hroot₀ := hroot₀) (hroot₁ := hroot₁) (hroot₂ := hroot₂)
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  apply hdet
  simp only [ha, hc, mul_zero, hb, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_self]

lemma symmetricDet_zero_diagonal_sub_ne_zero
    {b b' : K} (h : b ≠ b') :
    ((0 : K) * 0 - (b - b') ^ 2) ≠ 0 := by
  rw [symmetricDet_zero_diagonal_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr h))

end Field

noncomputable section Separation

open Filter Finset SimpleGraph
open scoped Topology

def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

lemma extremalScale_pos {n : ℕ} (hn : 0 < n) :
    0 < extremalScale n := by
  unfold extremalScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma extremalScale_nonneg (n : ℕ) :
    0 ≤ extremalScale n := by
  unfold extremalScale
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

def FamilyLittleO (family : Finset FiniteGraph) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (familyExtremal family n : ℝ) ≤ ε * extremalScale n

def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

structure SeparationCertificate (family : Finset FiniteGraph) where
  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  family_littleO : FamilyLittleO family
  member_lower : UniformMemberLower family lowerConstant

noncomputable def manuscriptLowerConstant : ℝ :=
  (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
    (27 : ℝ) ^ (-((4 : ℝ) / 3))

theorem manuscriptLowerConstant_pos : 0 < manuscriptLowerConstant := by
  unfold manuscriptLowerConstant
  positivity

lemma not_compact_of_separation
    {family : Finset FiniteGraph}
    (certificate : SeparationCertificate family) :
    ¬ IsCompactFamily family := by
  rintro ⟨forbidden, hmem, C, hC, hcomparison⟩
  have hepsilon : 0 < certificate.lowerConstant / (2 * C) := by
    exact div_pos certificate.lowerConstant_pos
      (mul_pos (by norm_num) hC)
  have hupper := certificate.family_littleO
    (certificate.lowerConstant / (2 * C)) hepsilon
  have hlower := certificate.member_lower forbidden hmem
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  have himpossible : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hcomparison, hpositive]
      with n hnupper hnlower hncomparison hnpositive
    have hs := extremalScale_pos hnpositive
    have hscaled :
        C * (familyExtremal family n : ℝ) ≤
          C * ((certificate.lowerConstant / (2 * C)) *
            extremalScale n) :=
      mul_le_mul_of_nonneg_left hnupper hC.le
    have hidentity :
        C * ((certificate.lowerConstant / (2 * C)) *
          extremalScale n) =
            (certificate.lowerConstant / 2) * extremalScale n := by
      field_simp
    rw [hidentity] at hscaled
    nlinarith [mul_pos certificate.lowerConstant_pos hs]
  exact himpossible.exists.elim (fun _ h => h)

theorem proposedFamily_not_compact_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by
  apply not_compact_of_separation
  exact
    { lowerConstant := manuscriptLowerConstant
      lowerConstant_pos := manuscriptLowerConstant_pos
      family_littleO := hupper
      member_lower := hlower }

lemma not_compactnessConjecture_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ CompactnessConjectureStatement := by
  intro hconjecture
  exact proposedFamily_not_compact_of_bounds hupper hlower
    (hconjecture proposedFamily proposedFamily_nonempty
      proposedFamily_isCyclic)

end Separation

noncomputable section Supersaturation

open Finset SimpleGraph

section FiniteHeavyFibers

def fourPathHeavyThreshold (N p : ℕ) : ℝ :=
  (p : ℝ) / (2 * (N : ℝ))

def finiteHeavyFiberMass {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ) : ℝ :=
  ∑ x : α,
    if fourPathHeavyThreshold N p ≤ (weight x : ℝ)
    then (weight x : ℝ) else 0

theorem finite_heavy_fiber_mass_half
    {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ)
    (hN : 0 < N)
    (hcapacity : Fintype.card α ≤ N)
    (htotal : p ≤ ∑ x : α, weight x) :
    (p : ℝ) / 2 ≤ finiteHeavyFiberMass weight N p := by
  classical
  let R : ℝ := fourPathHeavyThreshold N p
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hsum :
      (∑ x : α, (weight x : ℝ)) ≤
        (∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) +
          (Fintype.card α : ℝ) * R := by
    calc
      (∑ x : α, (weight x : ℝ)) ≤
          ∑ x : α,
            ((if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) + R) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · linarith
        · have : (weight x : ℝ) < R := lt_of_not_ge hx
          linarith
      _ = _ := by simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  have hcapacityReal : (Fintype.card α : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcapacity
  have hthreshold : (N : ℝ) * R = (p : ℝ) / 2 := by
    dsimp [R, fourPathHeavyThreshold]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  have htotalReal :
      (p : ℝ) ≤ ∑ x : α, (weight x : ℝ) := by
    exact_mod_cast htotal
  change (p : ℝ) / 2 ≤
    ∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0
  nlinarith [mul_le_mul_of_nonneg_right hcapacityReal hR]

end FiniteHeavyFibers

section ActualFourPathFibers

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma unrelated_four_path_endpoint_card_le
    (G : SimpleGraph V) (u : V) :
    Fintype.card (UnrelatedFourPathEndpoint G u) ≤ Fintype.card V := by
  exact Fintype.card_le_of_injective
    (fun v : UnrelatedFourPathEndpoint G u => (v : V))
    Subtype.val_injective

omit [Fintype V] [DecidableEq V] in
lemma common_second_neighbor_pairwise_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v : V}
    (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (x y : CommonSecondNeighbor G u v) :
    ¬ CommonNeighborRelated G (x : V) (y : V) := by
  exact common_second_neighbors_pairwise_unrelated
    hbip hfour hsix huv hunrelated
    (commonNeighborRelated_symm x.property.1)
    (commonNeighborRelated_symm x.property.2)
    (commonNeighborRelated_symm y.property.1)
    (commonNeighborRelated_symm y.property.2)

lemma four_path_heavy_common_second_neighbor_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 2 ≤
      finiteHeavyFiberMass
        (fun v : UnrelatedFourPathEndpoint G u =>
          Fintype.card (CommonSecondNeighbor G u (v : V)))
        (Fintype.card V) (d * (d - 1) ^ 3) := by
  apply finite_heavy_fiber_mass_half
  · exact Fintype.card_pos_iff.mpr ⟨u⟩
  · exact unrelated_four_path_endpoint_card_le G u
  · exact four_path_common_second_neighbor_sum_lower
      G hbip hfour hsix d hdegree u

end ActualFourPathFibers

section ActualThetaExtensions

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thetaBaseExtensions
    (G : SimpleGraph V) (y z : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ witness : SimpleGraph.Copy thetaGraph G,
      witness (.inl (.inl (0 : Fin 3))) = x ∧
      witness (.inl (.inl (1 : Fin 3))) = y ∧
      witness (.inl (.inl (2 : Fin 3))) = z

lemma mem_thetaBaseExtensions
    (G : SimpleGraph V) (x y z : V) :
    x ∈ thetaBaseExtensions G y z ↔
      ∃ witness : SimpleGraph.Copy thetaGraph G,
        witness (.inl (.inl (0 : Fin 3))) = x ∧
        witness (.inl (.inl (1 : Fin 3))) = y ∧
        witness (.inl (.inl (2 : Fin 3))) = z := by
  classical
  simp only [thetaBaseExtensions, Fin.isValue, mem_filter, mem_univ, true_and]

def gluedJBase {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G) : Fin 4 → V :=
  ![copies 0 (.inl (.inl (0 : Fin 3))),
    copies 1 (.inl (.inl (0 : Fin 3))),
    copies 0 (.inl (.inl (1 : Fin 3))),
    copies 0 (.inl (.inl (2 : Fin 3)))]

def gluedJVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V) : JVertex → V
  | .inl (.inl base) => gluedJBase copies base
  | .inl (.inr (copy, center)) =>
      copies copy (.inl (.inr center))
  | .inr (.inl (copy, (base, center))) =>
      copies copy (.inr (base, center))
  | .inr (.inr _) => joining

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_jBase
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (base : Fin 3) :
    gluedJBase copies (jBase copy base) =
      copies copy (.inl (.inl base)) := by
  fin_cases copy <;> fin_cases base <;>
    simp [gluedJBase, jBase, hfirst, hsecond]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_jThetaVertex
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (vertex : SubdivisionVertex 2) :
    gluedJVertex copies joining (jThetaVertex copy vertex) =
      copies copy vertex := by
  rcases vertex with (base | center) | pair
  · exact gluedJBase_jBase copies hfirst hsecond copy base
  · simp only [gluedJVertex, jThetaVertex]
  · simp only [gluedJVertex, jThetaVertex, Prod.mk.eta]

lemma inJCopy_iff_exists_jThetaVertex
    (copy : Fin 2) (vertex : JVertex) :
    InJCopy copy vertex ↔
      ∃ source : SubdivisionVertex 2,
        jThetaVertex copy source = vertex := by
  constructor
  · intro h
    rcases vertex with (base | center) | (pair | joining)
    · obtain ⟨source, hsource⟩ := h
      refine ⟨.inl (.inl source), ?_⟩
      simpa only [jThetaVertex, Sum.inl.injEq] using
        congrArg (fun value : Fin 4 => (Sum.inl (Sum.inl value) : JVertex)) hsource.symm
    · rcases center with ⟨index, center⟩
      change copy = index at h
      subst index
      exact ⟨.inl (.inr center), rfl⟩
    · rcases pair with ⟨index, base, center⟩
      change copy = index at h
      subst index
      exact ⟨.inr (base, center), rfl⟩
    · exact False.elim h
  · rintro ⟨source, rfl⟩
    exact jThetaVertex_mem copy source

lemma theta_base_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

lemma theta_center_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    {source target : JVertex}
    (hedge : jTemplateRelation source target) :
    G.Adj
      (gluedJVertex copies joining source)
      (gluedJVertex copies joining target) := by
  rcases source with (base | center) | (pair | star)
  · rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy, base', center'⟩
      change base = jBase copy base' at hedge
      subst base
      change G.Adj
        (gluedJBase copies (jBase copy base'))
        (copies copy (.inr (base', center')))
      rw [gluedJBase_jBase copies hfirst hsecond copy base']
      exact (copies copy).toHom.map_rel
        (theta_base_pair_adj base' center')
    · change base = 0 ∨ base = 1 at hedge
      rcases hedge with hbase | hbase
      · subst base
        simpa only [gluedJVertex, gluedJBase, Fin.isValue, Matrix.cons_val_zero] using hjoinFirst
      · subst base
        simpa only [gluedJVertex, gluedJBase, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] using
          hjoinSecond
  · rcases center with ⟨copy, center⟩
    rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy', base, center'⟩
      change copy = copy' ∧ center = center' at hedge
      obtain ⟨hcopy, hcenter⟩ := hedge
      subst copy'
      subst center'
      exact (copies copy).toHom.map_rel
        (theta_center_pair_adj base center)
    · exact False.elim hedge
  · exact False.elim hedge
  · exact False.elim hedge

def gluedJHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    jTemplate →g G where
  toFun := gluedJVertex copies joining
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      jTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedJVertex_map_relation copies joining hfirst hsecond
        hjoinFirst hjoinSecond hforward
    · exact (gluedJVertex_map_relation copies joining
        hfirst hsecond hjoinFirst hjoinSecond hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by
  intro left hleft right hright heq
  change InJCopy copy left at hleft
  change InJCopy copy right at hright
  obtain ⟨source, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy left).mp hleft
  obtain ⟨target, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy right).mp hright
  change
    gluedJVertex copies joining (jThetaVertex copy source) =
      gluedJVertex copies joining (jThetaVertex copy target) at heq
  rw [gluedJVertex_jThetaVertex copies joining hfirst hsecond copy,
    gluedJVertex_jThetaVertex copies joining hfirst hsecond copy] at heq
  have hequal := (copies copy).injective heq
  subst target
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_injective
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by
  have hcopy (index : Fin 2) {i j : Fin 3}
      (hij : i ≠ j) :
      copies index (.inl (.inl i)) ≠
        copies index (.inl (.inl j)) := by
    intro h
    apply hij
    simpa only [Sum.inl.injEq] using (copies index).injective h
  have h02 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) :=
    hcopy 0 (by decide)
  have h03 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h23 :
      copies 0 (.inl (.inl (1 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h12 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 1))
      (h.trans hfirst.symm)
  have h13 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 2))
      (h.trans hsecond.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [gluedJBase, hdistinct, hdistinct.symm, h02, h02.symm,
      h03, h03.symm, h23, h23.symm, h12, h12.symm,
      h13, h13.symm] at hij ⊢

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_center_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (first second : Fin 3) :
    color (copy (.inl (.inl first))) =
      color (copy (.inl (.inl second))) := by
  calc
    color (copy (.inl (.inl first))) =
        color (copy (.inl (.inr (0 : Fin 2)))) :=
      thetaCopy_base_center_color_eq color copy first 0
    _ = color (copy (.inl (.inl second))) :=
      (thetaCopy_base_center_color_eq color copy second 0).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedThetaBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (copy : Fin 2) (base : Fin 3) :
    color (copies copy (.inl (.inl base))) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases copy
  · exact thetaCopy_base_color_eq color (copies 0) base 0
  · calc
      color (copies 1 (.inl (.inl base))) =
          color (copies 1 (.inl (.inl (1 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 1) base 1
      _ = color (copies 0 (.inl (.inl (1 : Fin 3)))) :=
        congrArg color hfirst
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 0) 1 0

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (base : Fin 4) :
    color (gluedJBase copies base) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases base
  · rfl
  · exact gluedThetaBase_color_eq copies hfirst color 1 0
  · exact gluedThetaBase_color_eq copies hfirst color 0 1
  · exact gluedThetaBase_color_eq copies hfirst color 0 2

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (color : G.Coloring (Fin 2))
    (vertex : JVertex) :
    jColor vertex = false ↔
      color (gluedJVertex copies joining vertex) =
        color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  rcases vertex with (base | center) | (pair | star)
  · simpa only [jColor, gluedJVertex, Fin.isValue, true_iff] using gluedJBase_color_eq copies hfirst color base
  · rcases center with ⟨copy, center⟩
    simp only [jColor, gluedJVertex, true_iff]
    calc
      color (copies copy (.inl (.inr center))) =
          color (copies copy (.inl (.inl (0 : Fin 3)))) :=
        (thetaCopy_base_center_color_eq
          color (copies copy) 0 center).symm
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        gluedThetaBase_color_eq copies hfirst color copy 0
  · rcases pair with ⟨copy, base, center⟩
    simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    have hedge := (copies copy).toHom.map_rel
      (theta_base_pair_adj base center)
    have hvalid := color.valid hedge
    apply hvalid
    exact (gluedThetaBase_color_eq
      copies hfirst color copy base).trans heq.symm
  · simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    exact (color.valid hjoinFirst) heq.symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    ∀ left right,
      gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond left =
          gluedJHom copies joining hfirst hsecond
            hjoinFirst hjoinSecond right →
        jColor left = jColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hcolor :
      color (gluedJVertex copies joining left) =
        color (gluedJVertex copies joining right) :=
    congrArg color heq
  cases hleft : jColor left <;> cases hright : jColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mp hleft
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mpr
        (hcolor.symm.trans hbase)
    simp only [hright, Bool.true_eq_false] at hfalse
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mp hright
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mpr
        (hcolor.trans hbase)
    simp only [hleft, Bool.true_eq_false] at hfalse
  · rfl

lemma thetaBaseExtensions_commonNeighborIndependent
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (y z : Fin n) :
    CommonNeighborIndependent host (thetaBaseExtensions host y z) := by
  intro x x' hx hx' hdistinct
  rintro ⟨_, joining, hxjoin, hx'join⟩
  obtain ⟨first, hfirstX, hfirstY, hfirstZ⟩ :=
    (mem_thetaBaseExtensions host x y z).mp hx
  obtain ⟨second, hsecondX, hsecondY, hsecondZ⟩ :=
    (mem_thetaBaseExtensions host x' y z).mp hx'
  let copies : Fin 2 → SimpleGraph.Copy thetaGraph host :=
    ![first, second]
  have hsharedFirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    change second (.inl (.inl (1 : Fin 3))) =
      first (.inl (.inl (1 : Fin 3)))
    exact hsecondY.trans hfirstY.symm
  have hsharedSecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    change second (.inl (.inl (2 : Fin 3))) =
      first (.inl (.inl (2 : Fin 3)))
    exact hsecondZ.trans hfirstZ.symm
  have hjoinFirst :
      host.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (first (.inl (.inl (0 : Fin 3)))) joining
    rw [hfirstX]
    exact hxjoin
  have hjoinSecond :
      host.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (second (.inl (.inl (0 : Fin 3)))) joining
    rw [hsecondX]
    exact hx'join
  have hbaseDistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3))) := by
    change first (.inl (.inl (0 : Fin 3))) ≠
      second (.inl (.inl (0 : Fin 3)))
    rw [hfirstX, hsecondX]
    exact hdistinct
  apply proposedFamilyFree_no_jTemplate hfree
    (gluedJHom copies joining hsharedFirst hsharedSecond
      hjoinFirst hjoinSecond)
  · exact gluedJHom_color_respecting hbip copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond
  · change Function.Injective (gluedJBase copies)
    exact gluedJBase_injective copies hsharedFirst
      hsharedSecond hbaseDistinct
  · intro copy
    exact gluedJHom_injOn_marked_copy copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond copy

lemma thetaBaseExtensions_card_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (y z : Fin n) :
    (thetaBaseExtensions host y z).card * d ≤ n := by
  simpa only [Fintype.card_fin] using
    (commonNeighborIndependent_card_mul_degree_le host (thetaBaseExtensions host y z)
      (thetaBaseExtensions_commonNeighborIndependent host hfree hbip y z) d hdegree)

end ActualThetaExtensions

section ActualCommonCenterTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ i : Fin 3, CommonNeighborRelated G (base i) center

omit [DecidableEq V] in
lemma mem_tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) (center : V) :
    center ∈ tripleCommonCenters G base ↔
      ∀ i : Fin 3, CommonNeighborRelated G (base i) center := by
  classical
  simp only [tripleCommonCenters, mem_filter, mem_univ, true_and]

lemma mem_thetaBaseExtensions_of_girthEightCenters
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin 2 → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  refine (mem_thetaBaseExtensions G _ _ _).mpr ?_
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_, ?_, ?_⟩
  all_goals rfl

lemma mem_thetaBaseExtensions_of_two_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenters : 2 ≤ (tripleCommonCenters G base).card) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  classical
  have hcard : 1 < (tripleCommonCenters G base).card := by omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp hcard
  let center : Fin 2 → V := ![first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base first).mp hfirst i
    · exact (mem_tripleCommonCenters G base second).mp hsecond i
  exact mem_thetaBaseExtensions_of_girthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated

end ActualCommonCenterTriples

section CubicBinomialSupersaturation

lemma choose_three_factorial_identity (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by
  simpa only [Nat.mul_comm, Nat.mul_assoc, Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one,
    Nat.reduceMul, Nat.descFactorial, tsub_zero] using (Nat.descFactorial_eq_factorial_mul_choose t 3).symm

lemma choose_three_cubic_lower {t : ℕ} (ht : 3 ≤ t) :
    (t : ℝ) ^ 3 / 27 ≤ (t.choose 3 : ℝ) := by
  have hone : 1 ≤ t := by omega
  have htwo : 2 ≤ t := by omega
  have hidentity := congrArg (fun value : ℕ => (value : ℝ))
    (choose_three_factorial_identity t)
  norm_num [Nat.cast_sub hone, Nat.cast_sub htwo] at hidentity
  have htReal : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfactor :
      0 ≤ (t : ℝ) * ((t : ℝ) - 3) *
        (7 * (t : ℝ) - 6) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)
  nlinarith

end CubicBinomialSupersaturation

section ActualTripleSupersaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborTripleMass
    (G : SimpleGraph V) (u : V) : ℕ :=
  ∑ v : UnrelatedFourPathEndpoint G u,
    (Fintype.card (CommonSecondNeighbor G u (v : V))).choose 3

lemma four_path_common_second_neighbor_triple_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass G u : ℝ) := by
  classical
  let p : ℕ := d * (d - 1) ^ 3
  let R : ℝ := fourPathHeavyThreshold (Fintype.card V) p
  let weight : UnrelatedFourPathEndpoint G u → ℕ :=
    fun v => Fintype.card (CommonSecondNeighbor G u (v : V))
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hRthree : (3 : ℝ) ≤ R := by
    simpa only using hthreshold
  have hheavy :
      (p : ℝ) / 2 ≤
        finiteHeavyFiberMass weight (Fintype.card V) p := by
    exact four_path_heavy_common_second_neighbor_mass_lower
      G hbip hfour hsix d hdegree u
  have hpoint (v : UnrelatedFourPathEndpoint G u) :
      R ^ 2 *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) / 27 ≤
        ((weight v).choose 3 : ℝ) := by
    split_ifs with hv
    · have htReal : (3 : ℝ) ≤ (weight v : ℝ) := hRthree.trans hv
      have ht : 3 ≤ weight v := by exact_mod_cast htReal
      have hsquare : R ^ 2 ≤ (weight v : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hR
          (sub_nonneg.mpr hv),
          mul_nonneg (Nat.cast_nonneg (weight v))
            (sub_nonneg.mpr hv)]
      have hcubic :
          R ^ 2 * (weight v : ℝ) ≤ (weight v : ℝ) ^ 3 := by
        calc
          R ^ 2 * (weight v : ℝ) ≤
              (weight v : ℝ) ^ 2 * (weight v : ℝ) :=
            mul_le_mul_of_nonneg_right hsquare
              (Nat.cast_nonneg (weight v))
          _ = (weight v : ℝ) ^ 3 := by ring
      calc
        R ^ 2 * (weight v : ℝ) / 27 ≤
            (weight v : ℝ) ^ 3 / 27 := by linarith
        _ ≤ ((weight v).choose 3 : ℝ) :=
          choose_three_cubic_lower ht
    · simp only [mul_zero, zero_div, Nat.cast_nonneg]
  change R ^ 2 * (p : ℝ) / 54 ≤
    (commonSecondNeighborTripleMass G u : ℝ)
  calc
    R ^ 2 * (p : ℝ) / 54 =
        (R ^ 2 / 27) * ((p : ℝ) / 2) := by ring
    _ ≤ (R ^ 2 / 27) *
        finiteHeavyFiberMass weight (Fintype.card V) p :=
      mul_le_mul_of_nonneg_left hheavy (by positivity)
    _ = ∑ v : UnrelatedFourPathEndpoint G u,
          R ^ 2 *
            (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) /
              27 := by
      simp only [finiteHeavyFiberMass, Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro v hv
        change (R ^ 2 / 27) *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) = _
        ring
    _ ≤ ∑ v : UnrelatedFourPathEndpoint G u,
          ((weight v).choose 3 : ℝ) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (commonSecondNeighborTripleMass G u : ℝ) := by
      simp only [commonSecondNeighborTripleMass, weight, Nat.cast_sum]

theorem proposedFamilyFree_four_path_triple_mass_lower
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (u : Fin n)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass host u : ℝ) := by
  have hthreshold' : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card (Fin n))
        (d * (d - 1) ^ 3) := by
    simpa only [Fintype.card_fin] using hthreshold
  simpa only [Nat.cast_mul, Nat.cast_pow, ge_iff_le, Fintype.card_fin] using
    four_path_common_second_neighbor_triple_mass_lower host hbip (proposedFamilyFree_four_cycle hfree)
      (proposedFamilyFree_six_cycle hfree) d hdegree u hthreshold'

end ActualTripleSupersaturation

section OrderedThetaTripleCounting

noncomputable def orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n)) : ℕ :=
  ∑ y : Fin n, ∑ z : Fin n, (thetaBaseExtensions host y z).card

lemma orderedThetaTripleCount_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    orderedThetaTripleCount host * d ≤ n ^ 3 := by
  classical
  calc
    orderedThetaTripleCount host * d =
        ∑ y : Fin n, ∑ z : Fin n,
          (thetaBaseExtensions host y z).card * d := by
      simp only [orderedThetaTripleCount, sum_mul]
    _ ≤ ∑ _y : Fin n, ∑ _z : Fin n, n := by
      gcongr with y _ z _
      exact thetaBaseExtensions_card_mul_degree_le
        host hfree hbip d hdegree y z
    _ = n ^ 3 := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, pow_succ, pow_zero, one_mul, Nat.mul_assoc]

end OrderedThetaTripleCounting

section ActualGammaAndKForcing

variable {V : Type*} [Fintype V] [DecidableEq V]

def GammaGood (G : SimpleGraph V) (u : V) : Prop :=
  ∃ witness : SimpleGraph.Copy gammaGraph G,
    witness kSpecifiedCenter = u

lemma gammaGood_of_three_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    {u : V}
    (hu : u ∈ tripleCommonCenters G base)
    (hcenters : 3 ≤ (tripleCommonCenters G base).card) :
    GammaGood G u := by
  classical
  have herase :
      1 < ((tripleCommonCenters G base).erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp herase
  have hfirstne : first ≠ u := (Finset.mem_erase.mp hfirst).1
  have hsecondne : second ≠ u := (Finset.mem_erase.mp hsecond).1
  have hfirstmem : first ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hfirst).2
  have hsecondmem : second ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hsecond).2
  let center : Fin 3 → V := ![u, first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [center, hfirstne, hfirstne.symm, hsecondne,
        hsecondne.symm, hdistinct, hdistinct.symm] at hij ⊢
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base u).mp hu i
    · exact (mem_tripleCommonCenters G base first).mp hfirstmem i
    · exact (mem_tripleCommonCenters G base second).mp hsecondmem i
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_⟩
  rfl

lemma gamma_base_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

lemma gamma_center_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp only [SubdivisionGraph, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, subdivisionRelation,
    or_false, and_self]

omit [Fintype V] [DecidableEq V] in
lemma gammaCopy_vertex_color_false_iff
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (witness : SimpleGraph.Copy gammaGraph G)
    (vertex : SubdivisionVertex 3) :
    subdivisionColor 3 vertex = false ↔
      color (witness vertex) = color (witness kSpecifiedCenter) := by
  rcases vertex with (base | center) | pair
  · simp only [subdivisionColor, true_iff]
    exact bipartite_coloring_eq_of_common_neighbor color
      (witness.toHom.map_rel (gamma_base_pair_adj base 0))
      (witness.toHom.map_rel (gamma_center_pair_adj base 0))
  · simp only [subdivisionColor, true_iff]
    calc
      color (witness (.inl (.inr center))) =
          color (witness (.inl (.inl (0 : Fin 3)))) :=
        (bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 center))
          (witness.toHom.map_rel
            (gamma_center_pair_adj 0 center))).symm
      _ = color (witness kSpecifiedCenter) :=
        bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 0))
          (witness.toHom.map_rel (gamma_center_pair_adj 0 0))
  · rcases pair with ⟨base, center⟩
    simp only [subdivisionColor, Bool.true_eq_false, false_iff]
    intro heq
    have hbase :
        color (witness (.inl (.inl base))) =
          color (witness kSpecifiedCenter) :=
      bipartite_coloring_eq_of_common_neighbor color
        (witness.toHom.map_rel (gamma_base_pair_adj base 0))
        (witness.toHom.map_rel (gamma_center_pair_adj base 0))
    exact (color.valid
      (witness.toHom.map_rel (gamma_base_pair_adj base center)))
        (hbase.trans heq.symm)

def gluedKVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (vertex : KVertex) : V :=
  copies vertex.1 vertex.2

lemma subdivisionRelation_adj
    {k : ℕ} {source target : SubdivisionVertex k}
    (hedge : subdivisionRelation k source target) :
    (SubdivisionGraph k).Adj source target := by
  rcases source with (base | center) | pair <;>
    rcases target with (targetBase | targetCenter) | targetPair <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    {source target : KVertex}
    (hedge : kTemplateRelation source target) :
    G.Adj (gluedKVertex copies source)
      (gluedKVertex copies target) := by
  rcases hedge with hcopy | hjoin
  · obtain ⟨hindex, hsubdivision⟩ := hcopy
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = index' at hindex
    subst index'
    exact (copies index).toHom.map_rel
      (subdivisionRelation_adj hsubdivision)
  · obtain ⟨hsource, htarget, hvertex, hvertex'⟩ := hjoin
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = 0 at hsource
    change index' = 1 at htarget
    subst index
    subst index'
    change vertex = kSpecifiedCenter at hvertex
    change vertex' = kSpecifiedCenter at hvertex'
    subst vertex
    subst vertex'
    exact hjoining

def gluedKHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    kTemplate →g G where
  toFun := gluedKVertex copies
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      kTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedKVertex_map_relation copies hjoining hforward
    · exact (gluedKVertex_map_relation
        copies hjoining hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (index : Fin 2) :
    Set.InjOn (gluedKHom copies hjoining)
      {vertex : KVertex | vertex.1 = index} := by
  rintro ⟨leftIndex, leftVertex⟩ hleft
    ⟨rightIndex, rightVertex⟩ hright heq
  change leftIndex = index at hleft
  change rightIndex = index at hright
  subst leftIndex
  subst rightIndex
  change copies index leftVertex = copies index rightVertex at heq
  have hvertices := (copies index).injective heq
  subst rightVertex
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (color : G.Coloring (Fin 2))
    (vertex : KVertex) :
    kColor vertex = false ↔
      color (gluedKVertex copies vertex) =
        color (copies 0 kSpecifiedCenter) := by
  rcases vertex with ⟨index, vertex⟩
  fin_cases index
  · simpa only [kColor, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ↓reduceIte, gluedKVertex] using
      (gammaCopy_vertex_color_false_iff color (copies 0) vertex)
  · have hvalid :
        color (copies 0 kSpecifiedCenter) ≠
          color (copies 1 kSpecifiedCenter) :=
        color.valid hjoining
    change
      (if (1 : Fin 2) = 0 then subdivisionColor 3 vertex
        else !(subdivisionColor 3 vertex)) = false ↔
        color (copies 1 vertex) = color (copies 0 kSpecifiedCenter)
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    cases hcolor : subdivisionColor 3 vertex
    · simp only [Bool.not_false, Bool.true_eq_false, false_iff]
      intro heq
      have hsame :
          color (copies 1 vertex) =
            color (copies 1 kSpecifiedCenter) :=
        (gammaCopy_vertex_color_false_iff
          color (copies 1) vertex).mp hcolor
      exact hvalid (heq.symm.trans hsame)
    · simp only [Bool.not_true, true_iff]
      have hdistinct :
          color (copies 1 vertex) ≠
            color (copies 1 kSpecifiedCenter) := by
        intro heq
        have hfalse :=
          (gammaCopy_vertex_color_false_iff
            color (copies 1) vertex).mpr heq
        simp only [hcolor, Bool.true_eq_false] at hfalse
      apply Fin.ext
      omega

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    ∀ left right,
      gluedKHom copies hjoining left =
        gluedKHom copies hjoining right →
      kColor left = kColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hhostColor :
      color (gluedKVertex copies left) =
        color (gluedKVertex copies right) :=
    congrArg color heq
  cases hleft : kColor left <;> cases hright : kColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mp hleft
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mpr
        (hhostColor.symm.trans hbase)
    simp only [hright, Bool.true_eq_false] at hfalse
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mp hright
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mpr
        (hhostColor.trans hbase)
    simp only [hleft, Bool.true_eq_false] at hfalse
  · rfl

theorem proposedFamilyFree_not_adj_gammaGood
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hu : GammaGood host u) (hv : GammaGood host v) :
    ¬ host.Adj u v := by
  obtain ⟨first, hfirst⟩ := hu
  obtain ⟨second, hsecond⟩ := hv
  intro hedge
  let copies : Fin 2 → SimpleGraph.Copy gammaGraph host :=
    ![first, second]
  have hjoining :
      host.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter) := by
    change host.Adj (first kSpecifiedCenter)
      (second kSpecifiedCenter)
    rwa [hfirst, hsecond]
  exact proposedFamilyFree_no_kTemplate hfree
    (gluedKHom copies hjoining)
    (gluedKHom_color_respecting hbip copies hjoining)
    (gluedKHom_injOn_marked_copy copies hjoining)

end ActualGammaAndKForcing

section ActualBadVertexEdgeCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def gammaBadVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ GammaGood G v

omit [DecidableEq V] in
lemma mem_gammaBadVertices (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by
  classical
  simp only [gammaBadVertices, mem_filter, mem_univ, true_and]

theorem proposedFamilyFree_edge_has_gammaBad
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by
  classical
  by_cases hu : GammaGood host u
  · right
    apply (mem_gammaBadVertices host v).mpr
    intro hv
    exact proposedFamilyFree_not_adj_gammaGood
      host hfree hbip hu hv hedge
  · left
    exact (mem_gammaBadVertices host u).mpr hu

lemma edgeFinset_card_le_sum_degree_of_vertex_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover : Finset V)
    (hcover : ∀ ⦃u v : V⦄, G.Adj u v →
      u ∈ cover ∨ v ∈ cover) :
    G.edgeFinset.card ≤ ∑ v ∈ cover, G.degree v := by
  classical
  have hsubset :
      G.edgeFinset ⊆ cover.biUnion (fun v => G.incidenceFinset v) := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by
        simpa only [mem_edgeFinset, mem_edgeSet] using hedge
      rcases hcover hadj with hu | hv
      · exact Finset.mem_biUnion.mpr
          ⟨u, hu, (G.mem_incidenceFinset u _).mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨v, hv, (G.mem_incidenceFinset v _).mpr
            (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
  calc
    G.edgeFinset.card ≤
        (cover.biUnion fun v => G.incidenceFinset v).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ cover, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ cover, G.degree v := by
      simp only [card_incidenceFinset_eq_degree]

theorem proposedFamilyFree_edge_card_le_gammaBad_degree_sum
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite) :
    host.edgeFinset.card ≤
      ∑ v ∈ gammaBadVertices host, host.degree v :=
  edgeFinset_card_le_sum_degree_of_vertex_cover
    host (gammaBadVertices host)
    (fun _ _ hedge => proposedFamilyFree_edge_has_gammaBad
      host hfree hbip hedge)

end ActualBadVertexEdgeCounting

end Supersaturation

noncomputable section BadVertexCounting

open Finset SimpleGraph

noncomputable def finiteBadFiberMass
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop) : ℕ := by
  classical
  exact ∑ index : α,
    ((fibers index).filter fun vertex => ¬ good vertex).card

lemma finite_bad_fiber_card_le_two
    {α β : Type*} [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    [DecidablePred good]
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex)
    (index : α) :
    ((fibers index).filter fun vertex => ¬ good vertex).card ≤ 2 := by
  classical
  by_cases hlarge : 3 ≤ (fibers index).card
  · have hempty :
        (fibers index).filter (fun vertex => ¬ good vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro vertex hvertex hbad
      exact hbad (hgood index vertex hvertex hlarge)
    simp only [hempty, card_empty, zero_le]
  · have hcard :=
      Finset.card_filter_le (fibers index)
        (fun vertex => ¬ good vertex)
    omega

lemma finite_bad_fiber_mass_le_two
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex) :
    finiteBadFiberMass fibers good ≤ 2 * Fintype.card α := by
  classical
  simpa only [finiteBadFiberMass, Nat.mul_comm, card_univ, smul_eq_mul] using
    Finset.sum_le_card_nsmul Finset.univ (fun index => ((fibers index).filter fun vertex => ¬good vertex).card) 2
      (fun index _ => finite_bad_fiber_card_le_two fibers good hgood index)

section ActualIndependentTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ vertex ∈ base, CommonNeighborRelated G vertex center

lemma mem_commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) (center : V) :
    center ∈ commonCenterFinset G base ↔
      ∀ vertex ∈ base, CommonNeighborRelated G vertex center := by
  classical
  simp only [commonCenterFinset, mem_filter, mem_univ, true_and]

def IsIndependentThetaTriple
    (G : SimpleGraph V) (base : Finset V) : Prop :=
  base.card = 3 ∧
    (base : Set V).Pairwise
      (fun first second => ¬ CommonNeighborRelated G first second) ∧
    2 ≤ (commonCenterFinset G base).card

abbrev IndependentThetaTriple (G : SimpleGraph V) :=
  {base : Finset V // IsIndependentThetaTriple G base}

noncomputable instance independentThetaTripleFintype
    (G : SimpleGraph V) : Fintype (IndependentThetaTriple G) :=
  Fintype.ofFinite _

abbrev OrderedThetaWitness (G : SimpleGraph V) :=
  Σ first : V, Σ second : V,
    {third : V // third ∈ thetaBaseExtensions G first second}

noncomputable def independentThetaTripleBase
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Fin 3 → V :=
  fun index =>
    ((Finset.equivFinOfCardEq triple.property.1).symm index : triple.val)

lemma independentThetaTripleBase_injective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Function.Injective (independentThetaTripleBase G triple) := by
  intro first second heq
  apply (Finset.equivFinOfCardEq triple.property.1).symm.injective
  exact Subtype.ext heq

lemma independentThetaTripleBase_mem
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    (index : Fin 3) :
    independentThetaTripleBase G triple index ∈ triple.val :=
  ((Finset.equivFinOfCardEq triple.property.1).symm index).property

lemma independentThetaTripleBase_surjective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    {vertex : V} (hvertex : vertex ∈ triple.val) :
    ∃ index : Fin 3,
      independentThetaTripleBase G triple index = vertex := by
  let member : triple.val := ⟨vertex, hvertex⟩
  refine ⟨Finset.equivFinOfCardEq triple.property.1 member, ?_⟩
  change (((Finset.equivFinOfCardEq triple.property.1).symm
    (Finset.equivFinOfCardEq triple.property.1 member) : triple.val) : V) =
      vertex
  simp only [Equiv.symm_apply_apply, member]

lemma commonCenterFinset_eq_tripleCommonCenters
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    commonCenterFinset G triple.val =
      tripleCommonCenters G (independentThetaTripleBase G triple) := by
  classical
  ext center
  rw [mem_commonCenterFinset, mem_tripleCommonCenters]
  constructor
  · intro hcenter index
    exact hcenter _ (independentThetaTripleBase_mem G triple index)
  · intro hcenter vertex hvertex
    obtain ⟨index, rfl⟩ :=
      independentThetaTripleBase_surjective G triple hvertex
    exact hcenter index

lemma independentThetaTripleBase_unrelated
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    ⦃first second : Fin 3⦄ (hne : first ≠ second) :
    ¬ CommonNeighborRelated G
      (independentThetaTripleBase G triple first)
      (independentThetaTripleBase G triple second) := by
  apply triple.property.2.1
    (independentThetaTripleBase_mem G triple first)
    (independentThetaTripleBase_mem G triple second)
  exact fun heq =>
    hne (independentThetaTripleBase_injective G triple heq)

lemma gammaGood_of_independentThetaTriple_fiber
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) (vertex : V)
    (hvertex : vertex ∈ commonCenterFinset G triple.val)
    (hcard : 3 ≤ (commonCenterFinset G triple.val).card) :
    GammaGood G vertex := by
  apply gammaGood_of_three_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hvertex
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hcard

noncomputable def independentThetaTripleOrderedWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) : OrderedThetaWitness G := by
  refine ⟨independentThetaTripleBase G triple 1,
    independentThetaTripleBase G triple 2,
    ⟨independentThetaTripleBase G triple 0, ?_⟩⟩
  apply mem_thetaBaseExtensions_of_two_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  rw [← commonCenterFinset_eq_tripleCommonCenters]
  exact triple.property.2.2

lemma independentThetaTripleOrderedWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by
  intro left right heq
  have hbase : independentThetaTripleBase G left =
      independentThetaTripleBase G right := by
    funext index
    fin_cases index
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.2.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.1) heq
  apply Subtype.ext
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G left hvertex
    rw [hbase]
    exact independentThetaTripleBase_mem G right index
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G right hvertex
    rw [← hbase]
    exact independentThetaTripleBase_mem G left index

lemma orderedThetaWitness_card
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by
  classical
  simp only [OrderedThetaWitness, Fintype.card_sigma, Fintype.card_coe, orderedThetaTripleCount]

lemma independentThetaTriple_card_le_orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    Fintype.card (IndependentThetaTriple host) ≤
      orderedThetaTripleCount host := by
  calc
    Fintype.card (IndependentThetaTriple host) ≤
        Fintype.card (OrderedThetaWitness host) :=
      Fintype.card_le_of_injective
        (independentThetaTripleOrderedWitness host hbip hfour hsix)
        (independentThetaTripleOrderedWitness_injective
          host hbip hfour hsix)
    _ = orderedThetaTripleCount host := orderedThetaWitness_card host

theorem gamma_bad_triple_fiber_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by
  exact (finite_bad_fiber_mass_le_two _ _ (fun triple vertex hvertex hcard =>
    gammaGood_of_independentThetaTriple_fiber
      host hbip hfour hsix triple vertex hvertex hcard)).trans
    (Nat.mul_le_mul_left 2
      (independentThetaTriple_card_le_orderedThetaTripleCount
        host hbip hfour hsix))

end ActualIndependentTriples

end BadVertexCounting

noncomputable section TripleMassIncidence

open Finset SimpleGraph

section TripleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborFinset
    (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x

omit [DecidableEq V] in
lemma mem_commonSecondNeighborFinset
    (G : SimpleGraph V) (u v x : V) :
    x ∈ commonSecondNeighborFinset G u v ↔
      CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x := by
  classical
  simp only [commonSecondNeighborFinset, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
lemma commonSecondNeighborFinset_card
    (G : SimpleGraph V) (u v : V) :
    (commonSecondNeighborFinset G u v).card =
      Fintype.card (CommonSecondNeighbor G u v) := by
  classical
  rw [Fintype.card_subtype]
  rfl

abbrev BadFourPathTripleWitness (G : SimpleGraph V) :=
  Σ center : {u : V // ¬ GammaGood G u},
    Σ endpoint : UnrelatedFourPathEndpoint G (center : V),
      {base : Finset V //
        base ∈ (commonSecondNeighborFinset G
          (center : V) (endpoint : V)).powersetCard 3}

abbrev BadIndependentTripleWitness (G : SimpleGraph V) :=
  Σ triple : IndependentThetaTriple G,
    {center : V // center ∈ commonCenterFinset G triple.val ∧
      ¬ GammaGood G center}

noncomputable instance badFourPathTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadFourPathTripleWitness G) := by
  classical
  infer_instance

noncomputable instance badIndependentTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadIndependentTripleWitness G) := by
  classical
  infer_instance

noncomputable def fourPathTripleToIndependentThetaTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    IndependentThetaTriple G := by
  have hsubset :
      base.val ⊆ commonSecondNeighborFinset G u (endpoint : V) :=
    (Finset.mem_powersetCard.mp base.property).1
  refine ⟨base.val, ?_, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp base.property).2
  · intro x hx y hy hne
    have hx' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)
    have hy' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) y).mp (hsubset hy)
    exact common_second_neighbor_pairwise_unrelated
      G hbip hfour hsix endpoint.property.1 endpoint.property.2
      (⟨x, hx'⟩ : CommonSecondNeighbor G u (endpoint : V))
      (⟨y, hy'⟩ : CommonSecondNeighbor G u (endpoint : V))
  · have hu : u ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val u).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).1
    have hv : (endpoint : V) ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).2
    have hcard : 1 < (commonCenterFinset G base.val).card :=
      Finset.one_lt_card.mpr
        ⟨u, hu, (endpoint : V), hv, endpoint.property.1⟩
    omega

lemma fourPathTripleToIndependentThetaTriple_center_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    u ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change u ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val u).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).1

lemma fourPathTripleToIndependentThetaTriple_endpoint_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    (endpoint : V) ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change (endpoint : V) ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).2

lemma badIndependentThetaTriple_other_center_unique
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G)
    (u : V)
    (hu : u ∈ commonCenterFinset G triple.val)
    (hbad : ¬ GammaGood G u)
    {v w : V}
    (hv : v ∈ commonCenterFinset G triple.val)
    (hw : w ∈ commonCenterFinset G triple.val)
    (huv : u ≠ v) (huw : u ≠ w) :
    v = w := by
  classical
  by_contra hvw
  have hsubset :
      ({u, v, w} : Finset V) ⊆ commonCenterFinset G triple.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hcard : 3 ≤ (commonCenterFinset G triple.val).card := by
    calc
      3 = ({u, v, w} : Finset V).card := by
        simp only [mem_insert, huv, mem_singleton, huw, or_self, not_false_eq_true, card_insert_of_notMem, hvw,
          card_singleton, Nat.reduceAdd]
      _ ≤ (commonCenterFinset G triple.val).card :=
        Finset.card_le_card hsubset
  exact hbad (gammaGood_of_independentThetaTriple_fiber
    G hbip hfour hsix triple u hu hcard)

noncomputable def badFourPathTripleToBadIndependentTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    BadFourPathTripleWitness G → BadIndependentTripleWitness G := by
  rintro ⟨center, endpoint, base⟩
  refine ⟨fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix center endpoint base, ?_⟩
  refine ⟨center, ?_, center.property⟩
  exact fourPathTripleToIndependentThetaTriple_center_mem
    G hbip hfour hsix center endpoint base

lemma badFourPathTripleToBadIndependentTriple_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (badFourPathTripleToBadIndependentTriple
        G hbip hfour hsix) := by
  rintro ⟨u, v, base⟩ ⟨u', v', base'⟩ heq
  have hcenter := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      (witness.2 : V)) heq
  change (u : V) = (u' : V) at hcenter
  have husub : u = u' := Subtype.ext hcenter
  subst u'
  have hbase := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      witness.1.val) heq
  change base.val = base'.val at hbase
  let triple := fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix (u : V) v base
  have hu : (u : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_center_mem
      G hbip hfour hsix (u : V) v base
  have hv : (v : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v base
  have hv' : (v' : V) ∈ commonCenterFinset G triple.val := by
    change (v' : V) ∈ commonCenterFinset G base.val
    rw [hbase]
    exact fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v' base'
  have hendpoint : (v : V) = (v' : V) :=
    badIndependentThetaTriple_other_center_unique
      G hbip hfour hsix triple (u : V) hu u.property hv hv'
      v.property.1 v'.property.1
  have hvsub : v = v' := Subtype.ext hendpoint
  subst v'
  have hbasesub : base = base' := Subtype.ext hbase
  subst base'
  rfl

omit [DecidableEq V] in
lemma badFourPathTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadFourPathTripleWitness G) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe,
    Finset.card_powersetCard, commonSecondNeighborFinset_card]
  change
    (∑ u : {u : V // ¬ GammaGood G u},
      commonSecondNeighborTripleMass G u) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u
  symm
  apply Finset.sum_subtype
    (gammaBadVertices G)
    (fun u => (mem_gammaBadVertices G u))

lemma badIndependentTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadIndependentTripleWitness G) =
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  classical
  rw [Fintype.card_sigma]
  unfold finiteBadFiberMass
  apply Finset.sum_congr
  · rfl
  · intro triple htriple
    rw [Fintype.card_subtype]
    congr 1
    ext center
    simp only [mem_filter, mem_univ, true_and]

lemma gammaBad_four_path_triple_mass_le_bad_fiber_mass
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    (∑ u ∈ gammaBadVertices G,
      commonSecondNeighborTripleMass G u) ≤
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  rw [← badFourPathTripleWitness_card,
    ← badIndependentTripleWitness_card]
  exact Fintype.card_le_of_injective
    (badFourPathTripleToBadIndependentTriple
      G hbip hfour hsix)
    (badFourPathTripleToBadIndependentTriple_injective
      G hbip hfour hsix)

theorem gammaBad_four_path_triple_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    (∑ u ∈ gammaBadVertices host,
      commonSecondNeighborTripleMass host u) ≤
      2 * orderedThetaTripleCount host := by
  exact (gammaBad_four_path_triple_mass_le_bad_fiber_mass
    host hbip hfour hsix).trans
      (gamma_bad_triple_fiber_mass_le_two_orderedTheta
        host hbip hfour hsix)

lemma gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        (fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54) ≤
      2 * (orderedThetaTripleCount host : ℝ) := by
  classical
  let lower : ℝ :=
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54
  have hpoint (u : Fin n) :
      lower ≤ (commonSecondNeighborTripleMass host u : ℝ) := by
    exact proposedFamilyFree_four_path_triple_mass_lower
      host hfree hbip d hdegree u hthreshold
  change ((gammaBadVertices host).card : ℝ) * lower ≤
    2 * (orderedThetaTripleCount host : ℝ)
  calc
    ((gammaBadVertices host).card : ℝ) * lower =
        ∑ u ∈ gammaBadVertices host, lower := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ gammaBadVertices host,
        (commonSecondNeighborTripleMass host u : ℝ) := by
      gcongr with u hu
      exact hpoint u
    _ = ((∑ u ∈ gammaBadVertices host,
          commonSecondNeighborTripleMass host u) : ℝ) := by
      simp only
    _ ≤ ((2 * orderedThetaTripleCount host : ℕ) : ℝ) := by
      exact_mod_cast
        (gammaBad_four_path_triple_mass_le_two_orderedTheta
          host hbip (proposedFamilyFree_four_cycle hfree)
          (proposedFamilyFree_six_cycle hfree))
    _ = 2 * (orderedThetaTripleCount host : ℝ) := by
      norm_num

theorem gammaBad_card_mul_fourpath_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by
  have hn : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [fourPathHeavyThreshold] at hthreshold
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let p : ℕ := d * (d - 1) ^ 3
  let bad : ℕ := (gammaBadVertices host).card
  let theta : ℕ := orderedThetaTripleCount host
  have hmass :
      (bad : ℝ) *
        (fourPathHeavyThreshold n p ^ 2 *
          (p : ℝ) / 54) ≤ 2 * (theta : ℝ) := by
    exact gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
      host hfree hbip d hdegree hthreshold
  have hnormalized :
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) ≤ 2 * (theta : ℝ) := by
    calc
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) =
        (bad : ℝ) *
          (fourPathHeavyThreshold n p ^ 2 * (p : ℝ) / 54) := by
            unfold fourPathHeavyThreshold
            field_simp [ne_of_gt hnReal]
            ring
      _ ≤ 2 * (theta : ℝ) := hmass
  have hden : 0 < (216 : ℝ) * (n : ℝ) ^ 2 := by
    positivity
  have hclear := (div_le_iff₀ hden).mp hnormalized
  have hbadpoly :
      (bad : ℝ) * (p : ℝ) ^ 3 ≤
        432 * (theta : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have htheta :
      (theta : ℝ) * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast
      (orderedThetaTripleCount_mul_degree_le
        host hfree hbip d hdegree)
  have hfinal :
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 5 := by
    calc
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
          (432 * (theta : ℝ) * (n : ℝ) ^ 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbadpoly (Nat.cast_nonneg d)
      _ = 432 * ((theta : ℝ) * (d : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ 432 * (n : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
        gcongr
      _ = 432 * (n : ℝ) ^ 5 := by ring
  exact_mod_cast hfinal

theorem proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n := by
  classical
  calc
    host.edgeFinset.card * (d - 1) ^ 2 ≤
        (∑ u ∈ gammaBadVertices host, host.degree u) *
          (d - 1) ^ 2 :=
      Nat.mul_le_mul_right ((d - 1) ^ 2)
        (proposedFamilyFree_edge_card_le_gammaBad_degree_sum
          host hfree hbip)
    _ = ∑ u ∈ gammaBadVertices host,
        host.degree u * (d - 1) ^ 2 := by
      simp only [sum_mul]
    _ ≤ ∑ _u ∈ gammaBadVertices host, n := by
      gcongr with u hu
      simpa only [Fintype.card_fin] using
        girthEight_degree_mul_pred_sq_le_card host hbip (proposedFamilyFree_four_cycle hfree)
          (proposedFamilyFree_six_cycle hfree) d hdegree u
    _ = (gammaBadVertices host).card * n := by simp only [sum_const, smul_eq_mul]

lemma fourPathHeavyThreshold_low_degree_fourth_le
    (N d : ℕ)
    (hN : 0 < N)
    (hd : 2 ≤ d)
    (hlow : ¬ (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 4 ≤ 48 * (N : ℝ) := by
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hthreshold :
      fourPathHeavyThreshold N (d * (d - 1) ^ 3) < 3 :=
    lt_of_not_ge hlow
  have hp :
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) < 6 * (N : ℝ) := by
    unfold fourPathHeavyThreshold at hthreshold
    have hden : 0 < 2 * (N : ℝ) := by positivity
    have hclear := (div_lt_iff₀ hden).mp hthreshold
    nlinarith
  have hpredNat : d ≤ 2 * (d - 1) := by omega
  have hpredReal : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hpowers :
      (d : ℝ) ^ 3 ≤ (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 := by
    gcongr
  have hfourth :
      (d : ℝ) ^ 4 ≤
        8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
    calc
      (d : ℝ) ^ 4 = (d : ℝ) * (d : ℝ) ^ 3 := by ring
      _ ≤ (d : ℝ) *
          (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpowers (Nat.cast_nonneg d)
      _ = 8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
        push_cast
        ring
  nlinarith

end TripleIncidence

end TripleMassIncidence

noncomputable section QuantitativeBadVertexBound

open Finset SimpleGraph

lemma quantitative_minimum_degree_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    n * d ≤ 2 * host.edgeFinset.card := by
  simpa only [card_univ, Fintype.card_fin, smul_eq_mul, sum_degrees_eq_twice_card_edges] using
    Finset.card_nsmul_le_sum Finset.univ (fun vertex : Fin n => host.degree vertex) d (fun vertex _ => hdegree vertex)

lemma quantitative_bad_vertex_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n :=
  proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    host hfree hbip d hdegree

lemma quantitative_bad_vertex_heavy_triple_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
      432 * (n : ℝ) ^ 5 := by
  apply (mul_le_mul_iff_right₀
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  exact_mod_cast Nat.mul_le_mul_left n
    (gammaBad_card_mul_fourpath_power_le
      host hfree hbip d hdegree hthreshold)

theorem proposedFamilyFree_minDegree_polynomial_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdegreeReal :
      (n : ℝ) * (d : ℝ) ≤ 2 * (host.edgeFinset.card : ℝ) := by
    exact_mod_cast quantitative_minimum_degree_edge_bound
      host d hdegree
  have hedgeReal :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 ≤
        ((gammaBadVertices host).card : ℝ) * (n : ℝ) := by
    exact_mod_cast quantitative_bad_vertex_edge_bound
      host hfree hbip d hdegree
  have hbadReal := quantitative_bad_vertex_heavy_triple_bound
    host hn hfree hbip d hdegree hthreshold
  have hedgePolynomial :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 6 := by
    calc
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
          (((gammaBadVertices host).card : ℝ) * (n : ℝ)) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) := by
        gcongr
      _ = (((gammaBadVertices host).card : ℝ) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) *
            (n : ℝ) := by ring
      _ ≤ (432 * (n : ℝ) ^ 5) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hbadReal (Nat.cast_nonneg n)
      _ = 432 * (n : ℝ) ^ 6 := by ring
  apply (mul_le_mul_iff_right₀ hnreal).mp
  calc
    (n : ℝ) *
        ((d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3) =
        ((n : ℝ) * (d : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ (2 * (host.edgeFinset.card : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      gcongr
    _ = 2 *
          ((host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ 2 * (432 * (n : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hedgePolynomial (by norm_num)
    _ = (n : ℝ) * (864 * (n : ℝ) ^ 5) := by ring

theorem proposedFamilyFree_minDegree_sixteenth_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hd : 2 ≤ d)
    (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 16 ≤ 1769472 * (n : ℝ) ^ 5 := by
  have hraw := proposedFamilyFree_minDegree_polynomial_le
    host hn hfree hbip d hdegree hthreshold
  have hshape :
      (d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11 ≤
        864 * (n : ℝ) ^ 5 := by
    convert hraw using 1
    push_cast
    ring
  have hdone : 1 ≤ d := by omega
  have hhalf : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdone, Nat.cast_one]
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    (d : ℝ) ^ 16 = (d : ℝ) ^ 5 * (d : ℝ) ^ 11 := by ring
    _ ≤ (d : ℝ) ^ 5 *
        (2 * ((d - 1 : ℕ) : ℝ)) ^ 11 := by
      gcongr
    _ = 2 ^ (11 : ℕ) *
        ((d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11) := by ring
    _ ≤ 2 ^ (11 : ℕ) * (864 * (n : ℝ) ^ 5) := by
      gcongr
    _ = 1769472 * (n : ℝ) ^ 5 := by ring

end QuantitativeBadVertexBound

noncomputable section LineCoordinates

variable (K : Type*) [Field K]

def symplecticHorizontalVector (x y : K) : SymplecticVector K :=
  ![x, 0, y, 0]

def symplecticAnnihilatorVector (x y : K) : SymplecticVector K :=
  ![0, -y, 0, x]

def symmetricGraphVector (a b c x y : K) : SymplecticVector K :=
  ![x, a * x + b * y, y, b * x + c * y]

lemma symmetricGraphVector_orthogonal
    (a b c x y x' y' : K) :
    standardSymplecticForm K
      (symmetricGraphVector K a b c x y)
      (symmetricGraphVector K a b c x' y') = 0 := by
  simp only [standardSymplecticForm, symmetricGraphVector, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring

def coordinateCenterLinearMap (x y : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h :=
    h 0 • symplecticHorizontalVector K x y +
      h 1 • symplecticAnnihilatorVector K x y
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, smul_eq_mul] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, symplecticAnnihilatorVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

lemma coordinateCenterLinearMap_injective
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    Function.Injective (coordinateCenterLinearMap K x y) := by
  intro u v huv
  have hzero := congrFun huv 0
  have hone := congrFun huv 1
  have htwo := congrFun huv 2
  have hthree := congrFun huv 3
  simp [coordinateCenterLinearMap, symplecticHorizontalVector,
    symplecticAnnihilatorVector, smul_eq_mul]
    at hzero hone htwo hthree
  funext i
  fin_cases i
  · rcases hxy with hx | hy
    · exact hzero.resolve_right hx
    · exact htwo.resolve_right hy
  · rcases hxy with hx | hy
    · exact hthree.resolve_right hx
    · exact hone.resolve_right hy

def coordinateCenterLine (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) :
    SymplecticLine K :=
  ⟨LinearMap.range (coordinateCenterLinearMap K x y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (coordinateCenterLinearMap_injective K hxy)]
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp only [standardSymplecticForm, coordinateCenterLinearMap, Fin.isValue, symplecticHorizontalVector,
        Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, symplecticAnnihilatorVector, mul_neg, Matrix.add_cons,
        Matrix.head_cons, add_zero, Matrix.tail_cons, zero_add, Matrix.empty_add_empty, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, sub_neg_eq_add, Matrix.cons_val]
      ring⟩

def symmetricGraphLinearMap (a b c : K) :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun h := symmetricGraphVector K a b c (h 0) (h 1)
  map_add' u v := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.add_apply] <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;>
      simp [symmetricGraphVector, Pi.smul_apply, smul_eq_mul] <;> ring

lemma symmetricGraphLinearMap_injective
    (a b c : K) :
    Function.Injective (symmetricGraphLinearMap K a b c) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero] using congrFun huv 0
  · simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val] using congrFun huv 2

def symmetricGraphLine (a b c : K) : SymplecticLine K :=
  ⟨LinearMap.range (symmetricGraphLinearMap K a b c), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symmetricGraphLinearMap_injective K a b c)]
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact symmetricGraphVector_orthogonal K a b c
        (u' 0) (u' 1) (v' 0) (v' 1)⟩

lemma symmetricGraphVector_mem_center_span_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ s t : K,
      symmetricGraphVector K a b c x y =
        s • symplecticHorizontalVector K x y +
          t • symplecticAnnihilatorVector K x y) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨s, t, hvector⟩
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp only [symmetricGraphVector, Fin.isValue, Matrix.cons_val_zero, symplecticHorizontalVector,
      Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, symplecticAnnihilatorVector, mul_neg, Pi.add_apply,
      add_zero, Matrix.cons_val_one, zero_add, Matrix.cons_val] at hzero hone htwo hthree
    have hs : s = 1 := by
      rcases hxy with hx | hy
      · have hproduct : (s - 1) * x = 0 := by
          linear_combination -hzero
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hx)
      · have hproduct : (s - 1) * y = 0 := by
          linear_combination -htwo
        exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hy)
    subst s
    rw [symmetricQuadratic_eq_bilinear]
    linear_combination x * hone + y * hthree
  · intro hquadratic
    have hbilinear :
        x * (a * x + b * y) + y * (b * x + c * y) = 0 := by
      simpa only [symmetricQuadratic_eq_bilinear] using hquadratic
    rcases hxy with hx | hy
    · refine ⟨1, (b * x + c * y) / x, ?_⟩
      funext i
      fin_cases i
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          symplecticHorizontalVector, one_smul, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg,
          Matrix.smul_empty, Pi.add_apply, add_zero]
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero, symplecticHorizontalVector, one_smul, symplecticAnnihilatorVector, Matrix.smul_cons,
          smul_eq_mul, mul_zero, mul_neg, Matrix.smul_empty, Pi.add_apply, zero_add]
        field_simp [hx]
        linear_combination hbilinear
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, symplecticHorizontalVector,
          one_smul, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg, Matrix.smul_empty,
          Pi.add_apply, Fin.isValue, add_zero]
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, symplecticHorizontalVector,
          one_smul, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg, isUnit_iff_ne_zero, ne_eq,
          hx, not_false_eq_true, IsUnit.div_mul_cancel, Matrix.smul_empty, Pi.add_apply, Fin.isValue, zero_add]
    · refine ⟨1, -(a * x + b * y) / y, ?_⟩
      funext i
      fin_cases i
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          symplecticHorizontalVector, one_smul, neg_add_rev, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul,
          mul_zero, mul_neg, Matrix.smul_empty, Pi.add_apply, add_zero]
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
          Matrix.cons_val_zero, symplecticHorizontalVector, one_smul, neg_add_rev, symplecticAnnihilatorVector,
          Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg, isUnit_iff_ne_zero, ne_eq, hy, not_false_eq_true,
          IsUnit.div_mul_cancel, neg_neg, Matrix.smul_empty, Pi.add_apply, zero_add]
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, symplecticHorizontalVector,
          one_smul, neg_add_rev, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg,
          Matrix.smul_empty, Pi.add_apply, Fin.isValue, add_zero]
      · simp only [symmetricGraphVector, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, symplecticHorizontalVector,
          one_smul, neg_add_rev, symplecticAnnihilatorVector, Matrix.smul_cons, smul_eq_mul, mul_zero, mul_neg,
          Matrix.smul_empty, Pi.add_apply, Fin.isValue, zero_add]
        field_simp [hy]
        linear_combination hbilinear

lemma symmetricGraphLine_coordinateCenter_intersection_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ w : SymplecticVector K,
      w ≠ 0 ∧ w ∈ (symmetricGraphLine K a b c).1 ∧
        w ∈ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  constructor
  · rintro ⟨w, hw, hgraph, hcenter⟩
    obtain ⟨u, hu⟩ := hgraph
    obtain ⟨d, hd⟩ := hcenter
    have hvector :
        symmetricGraphVector K a b c (u 0) (u 1) =
          d 0 • symplecticHorizontalVector K x y +
            d 1 • symplecticAnnihilatorVector K x y := by
      exact hu.trans hd.symm
    have hzero := congrFun hvector 0
    have hone := congrFun hvector 1
    have htwo := congrFun hvector 2
    have hthree := congrFun hvector 3
    simp only [symmetricGraphVector, Fin.isValue, Matrix.cons_val_zero, symplecticHorizontalVector,
      Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, symplecticAnnihilatorVector, mul_neg, Pi.add_apply,
      add_zero, Matrix.cons_val_one, zero_add, Matrix.cons_val] at hzero hone htwo hthree
    have hdnonzero : d 0 ≠ 0 := by
      intro hd0
      have hu0 : u 0 = 0 := by
        simpa only [Fin.isValue, hd0, zero_mul] using hzero
      have hu1 : u 1 = 0 := by
        simpa only [Fin.isValue, hd0, zero_mul] using htwo
      apply hw
      rw [← hu]
      change symmetricGraphVector K a b c (u 0) (u 1) = 0
      funext i
      fin_cases i <;> simp [symmetricGraphVector, hu0, hu1]
    have hproduct : d 0 * symmetricQuadratic a b c x y = 0 := by
      rw [symmetricQuadratic_eq_bilinear]
      linear_combination x * hone + y * hthree -
        (a * x + b * y) * hzero -
        (b * x + c * y) * htwo
    exact (mul_eq_zero.mp hproduct).resolve_left hdnonzero
  · intro hquadratic
    obtain ⟨s, t, hvector⟩ :=
      (symmetricGraphVector_mem_center_span_iff K hxy).mpr hquadratic
    refine ⟨symmetricGraphVector K a b c x y, ?_, ?_, ?_⟩
    · intro hzero
      rcases hxy with hx | hy
      · apply hx
        simpa only [symmetricGraphVector, Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply] using congrFun hzero 0
      · apply hy
        simpa only [symmetricGraphVector, Fin.isValue, Matrix.cons_val, Pi.zero_apply] using congrFun hzero 2
    · refine ⟨![x, y], ?_⟩
      simp only [symmetricGraphLinearMap, symmetricGraphVector, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · refine ⟨![s, t], ?_⟩
      simpa only [coordinateCenterLinearMap, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using hvector.symm

lemma symmetricGraphLine_coordinateCenter_common_point_iff
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  rw [← symmetricGraphLine_coordinateCenter_intersection_iff K hxy]
  constructor
  · rintro ⟨p, hpgraph, hpcenter⟩
    have hpbot : p.1 ≠ ⊥ := by
      intro hbot
      have hrank := p.2
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨w, hw, hwne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hpbot
    exact ⟨w, hwne, hpgraph hw, hpcenter hw⟩
  · rintro ⟨w, hwne, hwgraph, hwcenter⟩
    let p : SymplecticPoint K :=
      ⟨K ∙ w, finrank_span_singleton hwne⟩
    refine ⟨p, ?_, ?_⟩
    · exact (Submodule.span_le).mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hwgraph)
    · exact (Submodule.span_le).mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using hwcenter)

lemma projectiveDirection_nonzero_left
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp only [hx, zero_mul, hy, mul_zero, sub_self]

lemma projectiveDirection_nonzero_right
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp only [hy, mul_zero, hx, zero_mul, sub_self]

lemma symmetricGraphLine_odd_no_three_actual_centers
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : (a * c - b ^ 2) ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hcenter₀ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₀ y₀
            (projectiveDirection_nonzero_left K h01)).1)
    (hcenter₁ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₁ y₁
            (projectiveDirection_nonzero_right K h01)).1)
    (hcenter₂ : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x₂ y₂
            (projectiveDirection_nonzero_right K h02)).1) :
    False := by
  apply symmetricQuadratic_no_three_roots_of_det_ne_zero
    htwo hdet h01 h02 h12
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K h01)).mp hcenter₀
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h01)).mp hcenter₁
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K h02)).mp hcenter₂

lemma symmetricGraphLines_disjoint_of_difference_det
    {a b c a' b' c' : K}
    (hdet : ((a - a') * (c - c') - (b - b') ^ 2) ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by
  apply Submodule.disjoint_def.mpr
  intro w hw hw'
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hw'
  have hvector :
      symmetricGraphVector K a b c (u 0) (u 1) =
        symmetricGraphVector K a' b' c' (v 0) (v 1) := by
    exact hu.trans hv.symm
  have hzero := congrFun hvector 0
  have htwo := congrFun hvector 2
  simp only [symmetricGraphVector, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val] at hzero htwo
  have huv : u = v := by
    funext i
    fin_cases i
    · exact hzero
    · exact htwo
  subst v
  have hone := congrFun hvector 1
  have hthree := congrFun hvector 3
  simp only [symmetricGraphVector, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val] at hone hthree
  have hdetx :
      ((a - a') * (c - c') - (b - b') ^ 2) * u 0 = 0 := by
    linear_combination (c - c') * hone - (b - b') * hthree
  have hdety :
      ((a - a') * (c - c') - (b - b') ^ 2) * u 1 = 0 := by
    linear_combination -(b - b') * hone + (a - a') * hthree
  have hx : u 0 = 0 :=
    (mul_eq_zero.mp hdetx).resolve_left hdet
  have hy : u 1 = 0 :=
    (mul_eq_zero.mp hdety).resolve_left hdet
  rw [← hu]
  change symmetricGraphVector K a b c (u 0) (u 1) = 0
  funext i
  fin_cases i <;> simp [symmetricGraphVector, hx, hy]

theorem symmetricGraphLine_zero_diagonal_disjoint
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by
  apply symmetricGraphLines_disjoint_of_difference_det K
  simpa only [sub_self, ne_eq] using symmetricDet_zero_diagonal_sub_ne_zero h

section CharacteristicTwo

variable [CharP K 2] [Finite K]

lemma symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
    {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x y
            (projectiveDirection_nonzero_left K hind)).1)
    (hsecond : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x' y'
            (projectiveDirection_nonzero_right K hind)).1) :
    a = 0 ∧ c = 0 := by
  apply symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    hind
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K hind)).mp hfirst
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K hind)).mp hsecond

end CharacteristicTwo

end LineCoordinates

noncomputable section ArbitraryLineNormalization

open SimpleGraph

variable (K : Type*) [Field K]

abbrev SymplecticAutomorphism :=
  (standardSymplecticBilin K).IsometryEquiv
    (standardSymplecticBilin K)

lemma symplecticAutomorphism_form
    (e : SymplecticAutomorphism K)
    (u v : SymplecticVector K) :
    standardSymplecticForm K (e u) (e v) =
      standardSymplecticForm K u v := by
  change
    standardSymplecticBilin K (e u) (e v) =
      standardSymplecticBilin K u v
  exact e.map_app' u v

def symplecticAutomorphismPoint
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) : SymplecticPoint K :=
  ⟨p.1.map e.toLinearEquiv.toLinearMap,
    (e.toLinearEquiv.finrank_map_eq p.1).trans p.2⟩

def symplecticAutomorphismLine
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) : SymplecticLine K := by
  refine ⟨L.1.map e.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · exact (e.toLinearEquiv.finrank_map_eq L.1).trans L.2.1
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_map.mp hu)
    obtain ⟨v', hv', rfl⟩ := (Submodule.mem_map.mp hv)
    change standardSymplecticForm K (e u') (e v') = 0
    exact (symplecticAutomorphism_form K e u' v').trans
      (L.2.2 u' hu' v' hv')

lemma symplecticAutomorphism_incidence_iff
    (e : SymplecticAutomorphism K)
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticAutomorphismPoint K e p).1 ≤
        (symplecticAutomorphismLine K e L).1 ↔
      p.1 ≤ L.1 := by
  change
    p.1.map e.toLinearEquiv.toLinearMap ≤
      L.1.map e.toLinearEquiv.toLinearMap ↔ p.1 ≤ L.1
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr e.toLinearEquiv.injective)

lemma symplecticAutomorphism_isotropic_iff
    (e : SymplecticAutomorphism K)
    (S : Submodule K (SymplecticVector K)) :
    (∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
      ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
        standardSymplecticForm K u v = 0) ↔
      (∀ u ∈ S, ∀ v ∈ S,
        standardSymplecticForm K u v = 0) := by
  constructor
  · intro h u hu v hv
    have hmap := h (e u) (Submodule.mem_map_of_mem hu)
      (e v) (Submodule.mem_map_of_mem hv)
    exact (symplecticAutomorphism_form K e u v).symm.trans hmap
  · intro h u hu v hv
    obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Submodule.mem_map.mp hv
    exact (symplecticAutomorphism_form K e u' v').trans
      (h u' hu' v' hv')

def symplecticAutomorphismLineEquiv
    (e : SymplecticAutomorphism K) :
    SymplecticLine K ≃ SymplecticLine K :=
  (Submodule.orderIsoMapComap e.toLinearEquiv).toEquiv.subtypeEquiv
    (fun S => by
      change
        (Module.finrank K S = 2 ∧
          ∀ u ∈ S, ∀ v ∈ S,
            standardSymplecticForm K u v = 0) ↔
        (Module.finrank K
            (S.map e.toLinearEquiv.toLinearMap) = 2 ∧
          ∀ u ∈ S.map e.toLinearEquiv.toLinearMap,
            ∀ v ∈ S.map e.toLinearEquiv.toLinearMap,
              standardSymplecticForm K u v = 0)
      rw [e.toLinearEquiv.finrank_map_eq,
        symplecticAutomorphism_isotropic_iff K e S])

@[simp]
lemma symplecticAutomorphismLineEquiv_apply
    (e : SymplecticAutomorphism K)
    (L : SymplecticLine K) :
    symplecticAutomorphismLineEquiv K e L =
      symplecticAutomorphismLine K e L := by
  apply Subtype.ext
  rfl

lemma symplecticLine_orthogonal_eq
    (L : SymplecticLine K) :
    (standardSymplecticBilin K).orthogonal L.1 = L.1 := by
  have hle :
      L.1 ≤ (standardSymplecticBilin K).orthogonal L.1 := by
    intro u hu
    change ∀ v ∈ L.1, standardSymplecticForm K v u = 0
    intro v hv
    exact L.2.2 v hv u hu
  have hdim :
      Module.finrank K
        ((standardSymplecticBilin K).orthogonal L.1) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal
      (standardSymplecticBilin_nondegenerate K), L.2.1]
    simp only [SymplecticVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Nat.reduceSub]
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (L.2.1.trans hdim.symm)).symm

lemma symplecticLine_isCompl_of_disjoint
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) : IsCompl L.1 M.1 := by
  apply (Submodule.isCompl_iff_disjoint L.1 M.1 ?_).mpr hLM
  simp only [SymplecticVector, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, L.2.1, M.2.1,
    Nat.reduceAdd, Std.le_refl]

def symplecticLinePairing
    (L M : SymplecticLine K) :
    M.1 →ₗ[K] Module.Dual K L.1 where
  toFun y :=
    { toFun := fun x =>
        standardSymplecticForm K
          (x : SymplecticVector K) (y : SymplecticVector K)
      map_add' := by
        intro x x'
        simpa only [Submodule.coe_add] using
          standardSymplecticForm_add_left K (x : SymplecticVector K) (x' : SymplecticVector K) (y : SymplecticVector K)
      map_smul' := by
        intro c x
        simpa only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul] using
          standardSymplecticForm_smul_left K c (x : SymplecticVector K) (y : SymplecticVector K) }
  map_add' := by
    intro y y'
    apply LinearMap.ext
    intro x
    simpa only [Submodule.coe_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply] using
      standardSymplecticForm_add_right K (x : SymplecticVector K) (y : SymplecticVector K) (y' : SymplecticVector K)
  map_smul' := by
    intro c y
    apply LinearMap.ext
    intro x
    simpa only [SetLike.val_smul, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
      smul_eq_mul] using standardSymplecticForm_smul_right K c (x : SymplecticVector K) (y : SymplecticVector K)

lemma symplecticLinePairing_injective
    {L M : SymplecticLine K}
    (hLM : Disjoint L.1 M.1) :
    Function.Injective (symplecticLinePairing K L M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro y hy
    have hpair : symplecticLinePairing K L M y = 0 := by
      exact LinearMap.mem_ker.mp hy
    have hyorth :
        (y : SymplecticVector K) ∈
          (standardSymplecticBilin K).orthogonal L.1 := by
      change
        ∀ x ∈ L.1,
          standardSymplecticForm K x
            (y : SymplecticVector K) = 0
      intro x hx
      have hz := DFunLike.congr_fun hpair (⟨x, hx⟩ : L.1)
      simpa only [symplecticLinePairing, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] using hz
    have hyL : (y : SymplecticVector K) ∈ L.1 := by
      rw [symplecticLine_orthogonal_eq K L] at hyorth
      exact hyorth
    have hyzero : (y : SymplecticVector K) = 0 := by
      have hbot :
          (y : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hLM.le_bot ⟨hyL, y.2⟩
      simpa only [ZeroMemClass.coe_eq_zero, Submodule.mem_bot] using hbot
    have hyzero' : y = 0 := by
      apply Subtype.ext
      simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] using hyzero
    exact (Submodule.mem_bot K).2 hyzero'
  · exact bot_le

lemma symplecticLinePairing_finrank
    (L M : SymplecticLine K) :
    Module.finrank K M.1 =
      Module.finrank K (Module.Dual K L.1) := by
  rw [Subspace.dual_finrank_eq, L.2.1, M.2.1]

def symplecticLinePairingEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] Module.Dual K L.1 :=
  (symplecticLinePairing K L M).linearEquivOfInjective
    (symplecticLinePairing_injective K hLM)
    (symplecticLinePairing_finrank K L M)

def symplecticLineBasis
    (L : SymplecticLine K) : Module.Basis (Fin 2) K L.1 :=
  Module.finBasisOfFinrankEq K L.1 L.2.1

def symplecticLineDualCoordinates
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    M.1 ≃ₗ[K] (Fin 2 → K) :=
  (symplecticLinePairingEquiv K L M hLM).trans
    (symplecticLineBasis K L).dualBasis.equivFun

@[simp]
lemma symplecticLineDualCoordinates_apply
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) (i : Fin 2) :
    symplecticLineDualCoordinates K L M hLM y i =
      standardSymplecticForm K
        ((symplecticLineBasis K L i : L.1) : SymplecticVector K)
        (y : SymplecticVector K) := by
  change
    (symplecticLineBasis K L).dualBasis.equivFun
        (symplecticLinePairingEquiv K L M hLM y) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  rfl

def symplecticCoordinateInterleave :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] SymplecticVector K where
  toFun x := ![x.1 0, x.2 0, x.1 1, x.2 1]
  invFun x := (![x 0, x 2], ![x 1, x 3])
  left_inv := by
    intro x
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticLineCoordinateEquiv
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticVector K ≃ₗ[K] SymplecticVector K :=
  ((L.1.prodEquivOfIsCompl M.1
      (symplecticLine_isCompl_of_disjoint K hLM)).symm.trans
      ((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))).trans
      (symplecticCoordinateInterleave K)

lemma symplecticLinePairing_coordinate_expansion
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
  let b := symplecticLineBasis K L
  have hsum :
      (∑ i : Fin 2, b.equivFun x i • b i) = x :=
    b.sum_equivFun x
  calc
    standardSymplecticForm K
        (x : SymplecticVector K) (y : SymplecticVector K) =
        symplecticLinePairing K L M y x := rfl
    _ = symplecticLinePairing K L M y
          (∑ i : Fin 2, b.equivFun x i • b i) :=
      congrArg (symplecticLinePairing K L M y) hsum.symm
    _ = ∑ i : Fin 2,
          b.equivFun x i *
            standardSymplecticForm K
              ((b i : L.1) : SymplecticVector K)
              (y : SymplecticVector K) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [Module.Basis.equivFun_apply, symplecticLinePairing, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    _ = (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y 0 +
        (symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y 1 := by
      simp only [Fin.sum_univ_two, b,
        symplecticLineDualCoordinates_apply]

lemma symplecticLineCoordinateEquiv_apply_add
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) (y : M.1) :
    symplecticLineCoordinateEquiv K L M hLM
        ((x : SymplecticVector K) + (y : SymplecticVector K)) =
      ![(symplecticLineBasis K L).equivFun x 0,
        symplecticLineDualCoordinates K L M hLM y 0,
        (symplecticLineBasis K L).equivFun x 1,
        symplecticLineDualCoordinates K L M hLM y 1] := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  have hsplit :
      (L.1.prodEquivOfIsCompl M.1 hcompl).symm
        ((x : SymplecticVector K) +
          (y : SymplecticVector K)) = (x, y) := by
    apply (L.1.prodEquivOfIsCompl M.1 hcompl).symm_apply_eq.mpr
    rfl
  change
    symplecticCoordinateInterleave K
      (((symplecticLineBasis K L).equivFun.prodCongr
        (symplecticLineDualCoordinates K L M hLM))
        ((L.1.prodEquivOfIsCompl M.1 hcompl).symm
          ((x : SymplecticVector K) +
            (y : SymplecticVector K)))) = _
  rw [hsplit]
  rfl

lemma symplecticLineCoordinateEquiv_form
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (u v : SymplecticVector K) :
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM u)
        (symplecticLineCoordinateEquiv K L M hLM v) =
      standardSymplecticForm K u v := by
  let hcompl := symplecticLine_isCompl_of_disjoint K hLM
  obtain ⟨⟨x, y⟩, hu⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective u
  obtain ⟨⟨x', y'⟩, hv⟩ :=
    (L.1.prodEquivOfIsCompl M.1 hcompl).surjective v
  rw [← hu, ← hv]
  change
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K))
  calc
    standardSymplecticForm K
        (symplecticLineCoordinateEquiv K L M hLM
          ((x : SymplecticVector K) + (y : SymplecticVector K)))
        (symplecticLineCoordinateEquiv K L M hLM
          ((x' : SymplecticVector K) + (y' : SymplecticVector K))) =
      (symplecticLineBasis K L).equivFun x 0 *
          symplecticLineDualCoordinates K L M hLM y' 0 -
        symplecticLineDualCoordinates K L M hLM y 0 *
          (symplecticLineBasis K L).equivFun x' 0 +
        ((symplecticLineBasis K L).equivFun x 1 *
          symplecticLineDualCoordinates K L M hLM y' 1 -
        symplecticLineDualCoordinates K L M hLM y 1 *
          (symplecticLineBasis K L).equivFun x' 1) := by
        rw [symplecticLineCoordinateEquiv_apply_add,
          symplecticLineCoordinateEquiv_apply_add]
        simp only [standardSymplecticForm, Fin.isValue,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    _ = standardSymplecticForm K
          (x : SymplecticVector K) (y' : SymplecticVector K) -
        standardSymplecticForm K
          (x' : SymplecticVector K) (y : SymplecticVector K) := by
        rw [symplecticLinePairing_coordinate_expansion K L M hLM x y',
          symplecticLinePairing_coordinate_expansion K L M hLM x' y]
        ring
    _ = standardSymplecticForm K
        ((x : SymplecticVector K) + (y : SymplecticVector K))
        ((x' : SymplecticVector K) + (y' : SymplecticVector K)) := by
        have hxx :
            standardSymplecticForm K
              (x : SymplecticVector K)
              (x' : SymplecticVector K) = 0 :=
          L.2.2 x x.2 x' x'.2
        have hyy :
            standardSymplecticForm K
              (y : SymplecticVector K)
              (y' : SymplecticVector K) = 0 :=
          M.2.2 y y.2 y' y'.2
        rw [standardSymplecticForm_add_left,
          standardSymplecticForm_add_right,
          standardSymplecticForm_add_right,
          hxx, hyy,
          standardSymplecticForm_swap K
            (y : SymplecticVector K)
            (x' : SymplecticVector K)]
        ring

def symplecticLineNormalizer
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    SymplecticAutomorphism K :=
  { symplecticLineCoordinateEquiv K L M hLM with
    map_app' := by
      intro u v
      change
        standardSymplecticForm K
            (symplecticLineCoordinateEquiv K L M hLM u)
            (symplecticLineCoordinateEquiv K L M hLM v) =
          standardSymplecticForm K u v
      exact symplecticLineCoordinateEquiv_form K L M hLM u v }

lemma symplecticLineNormalizer_apply_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) :
    symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    x (0 : M.1)
  simpa only [ZeroMemClass.coe_zero, add_zero, map_zero, Pi.zero_apply]
    using h

lemma symplecticLineNormalizer_apply_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) :
    symplecticLineNormalizer K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    (0 : L.1) y
  simpa only [ZeroMemClass.coe_zero, zero_add, map_zero, Pi.zero_apply]
    using h

def symplecticVerticalLinearMap :
    (Fin 2 → K) →ₗ[K] SymplecticVector K where
  toFun y := ![0, y 0, 0, y 1]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c y := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticVerticalLinearMap_injective :
    Function.Injective (symplecticVerticalLinearMap K) := by
  intro u v huv
  funext i
  fin_cases i
  · simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, symplecticVerticalLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_one, Matrix.cons_val_zero] using congrFun huv 1
  · simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, symplecticVerticalLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val] using congrFun huv 3

def symplecticVerticalLine : SymplecticLine K :=
  ⟨LinearMap.range (symplecticVerticalLinearMap K), by
    constructor
    · rw [LinearMap.finrank_range_of_inj
        (symplecticVerticalLinearMap_injective K)]
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    · intro u hu v hv
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      simp only [standardSymplecticForm, symplecticVerticalLinearMap, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, mul_zero, sub_self, Matrix.cons_val, add_zero]⟩

lemma symplecticLineNormalizer_map_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by
  apply Subtype.ext
  change
    L.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨(symplecticLineBasis K L).equivFun ⟨x, hx⟩, ?_⟩
    simpa only [symmetricGraphLinearMap, symmetricGraphVector, Fin.isValue, zero_mul, add_zero,
      Module.Basis.equivFun_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_coe,
      LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, Nat.succ_eq_add_one, Nat.reduceAdd] using
      (symplecticLineNormalizer_apply_left K L M hLM (⟨x, hx⟩ : L.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let x : L.1 := (symplecticLineBasis K L).equivFun.symm z
    have hx : symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) = ![z 0, 0, z 1, 0] := by
      rw [symplecticLineNormalizer_apply_left K L M hLM x,
        show (symplecticLineBasis K L).equivFun x = z from
          (symplecticLineBasis K L).equivFun.apply_symm_apply z]
    refine Submodule.mem_map.mpr
      ⟨(x : SymplecticVector K), x.2, ?_⟩
    simpa only [LinearEquiv.coe_coe, LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv, symmetricGraphLinearMap,
      symmetricGraphVector, Fin.isValue, zero_mul, add_zero, LinearMap.coe_mk, AddHom.coe_mk, Nat.succ_eq_add_one,
      Nat.reduceAdd] using hx

lemma symplecticLineNormalizer_map_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) M =
      symplecticVerticalLine K := by
  apply Subtype.ext
  change
    M.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symplecticVerticalLinearMap K)
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨symplecticLineDualCoordinates K L M hLM ⟨y, hy⟩, ?_⟩
    change
      symplecticVerticalLinearMap K
          (symplecticLineDualCoordinates K L M hLM ⟨y, hy⟩) =
        symplecticLineNormalizer K L M hLM
          ((⟨y, hy⟩ : M.1) : SymplecticVector K)
    rw [symplecticLineNormalizer_apply_right]
    rfl
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let y : M.1 :=
      (symplecticLineDualCoordinates K L M hLM).symm z
    refine Submodule.mem_map.mpr
      ⟨(y : SymplecticVector K), y.2, ?_⟩
    change
      symplecticLineNormalizer K L M hLM
          (y : SymplecticVector K) =
        symplecticVerticalLinearMap K z
    rw [symplecticLineNormalizer_apply_right]
    change
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] =
        ![0, z 0, 0, z 1]
    have hy : symplecticLineDualCoordinates K L M hLM y = z :=
      (symplecticLineDualCoordinates K L M hLM).apply_symm_apply z
    rw [hy]

def symplecticHorizontalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 0, v 2]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

def symplecticVerticalProjection :
    SymplecticVector K →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, v 3]
  map_add' u v := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp [smul_eq_mul]

lemma symplecticHorizontalProjection_ker :
    LinearMap.ker (symplecticHorizontalProjection K) =
      (symplecticVerticalLine K).1 := by
  apply le_antisymm
  · intro v hv
    have hzero := LinearMap.mem_ker.mp hv
    have hfirst := congrFun hzero 0
    have hthird := congrFun hzero 1
    simp only [symplecticHorizontalProjection, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
      Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hfirst hthird
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K)
    refine ⟨![v 1, v 3], ?_⟩
    funext i
    fin_cases i <;>
      simp [symplecticVerticalLinearMap, hfirst, hthird]
  · intro v hv
    change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
    obtain ⟨y, rfl⟩ := hv
    apply LinearMap.mem_ker.mpr
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalProjection,
        symplecticVerticalLinearMap]

lemma symplecticLineHorizontalProjection_injective
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    Function.Injective
      ((symplecticHorizontalProjection K).comp L.1.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    have hproj := LinearMap.mem_ker.mp hx
    change
      symplecticHorizontalProjection K
          (x : SymplecticVector K) = 0 at hproj
    have hxvertical :
        (x : SymplecticVector K) ∈
          (symplecticVerticalLine K).1 := by
      rw [← symplecticHorizontalProjection_ker K]
      exact LinearMap.mem_ker.mpr hproj
    have hxzero : (x : SymplecticVector K) = 0 := by
      have hbot :
          (x : SymplecticVector K) ∈
            (⊥ : Submodule K (SymplecticVector K)) :=
        hvertical.le_bot ⟨x.2, hxvertical⟩
      simpa only [ZeroMemClass.coe_eq_zero, Submodule.mem_bot] using hbot
    have hxsub : x = 0 := by
      apply Subtype.ext
      simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] using hxzero
    exact (Submodule.mem_bot K).2 hxsub
  · exact bot_le

def symplecticLineHorizontalProjectionEquiv
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    L.1 ≃ₗ[K] (Fin 2 → K) :=
  ((symplecticHorizontalProjection K).comp L.1.subtype).linearEquivOfInjective
      (symplecticLineHorizontalProjection_injective K L hvertical)
      (by simp only [L.2.1, Module.finrank_fintype_fun_eq_card, Fintype.card_fin])

def symplecticLineGraphMap
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (symplecticVerticalProjection K).comp
    (L.1.subtype.comp
      (symplecticLineHorizontalProjectionEquiv K L hvertical).symm.toLinearMap)

lemma symplecticLineGraphMap_horizontal
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by
  change
    symplecticVerticalProjection K
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm
        (symplecticLineHorizontalProjectionEquiv K L hvertical x) :
          SymplecticVector K) = _
  rw [LinearEquiv.symm_apply_apply]

lemma symplecticLineGraphMap_symmetric
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    symplecticLineGraphMap K L hvertical ![1, 0] 1 =
      symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![1, 0]
  let v : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm
      ![0, 1]
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = ![1, 0] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u =
        ![1, 0]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![1, 0]
  have hv :
      symplecticHorizontalProjection K
        (v : SymplecticVector K) = ![0, 1] := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical v =
        ![0, 1]
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply
        ![0, 1]
  have hu0 : (u : SymplecticVector K) 0 = 1 := by
    simpa only [Fin.isValue, symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd] using congrFun hu 0
  have hu2 : (u : SymplecticVector K) 2 = 0 := by
    simpa only [Fin.isValue, symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Nat.succ_eq_add_one, Nat.reduceAdd] using congrFun hu 1
  have hv0 : (v : SymplecticVector K) 0 = 0 := by
    simpa only [Fin.isValue, symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd] using congrFun hv 0
  have hv2 : (v : SymplecticVector K) 2 = 1 := by
    simpa only [Fin.isValue, symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Nat.succ_eq_add_one, Nat.reduceAdd] using congrFun hv 1
  have hu3 :
      (u : SymplecticVector K) 3 =
        symplecticLineGraphMap K L hvertical ![1, 0] 1 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical u) 1
    rw [hu] at h
    simpa only [Fin.isValue, symplecticVerticalProjection, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Nat.succ_eq_add_one, Nat.reduceAdd] using h.symm
  have hv1 :
      (v : SymplecticVector K) 1 =
        symplecticLineGraphMap K L hvertical ![0, 1] 0 := by
    have h := congrFun
      (symplecticLineGraphMap_horizontal K L hvertical v) 0
    rw [hv] at h
    simpa only [Fin.isValue, symplecticVerticalProjection, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
      Nat.succ_eq_add_one, Nat.reduceAdd] using h.symm
  have hpair := L.2.2
    (u : SymplecticVector K) u.2
    (v : SymplecticVector K) v.2
  have hzero :
      symplecticLineGraphMap K L hvertical ![0, 1] 0 -
        symplecticLineGraphMap K L hvertical ![1, 0] 1 = 0 := by
    rw [sub_eq_add_neg]
    simpa only [Fin.isValue, standardSymplecticForm, hu0, hv1, one_mul, hv0, mul_zero, sub_zero, hu2, zero_mul,
      hu3, hv2, mul_one, zero_sub] using hpair
  exact (sub_eq_zero.mp hzero).symm

lemma symplecticLineGraphMap_coordinate_expansion
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) (i : Fin 2) :
    symplecticLineGraphMap K L hvertical z i =
      symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
  have hz : z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext j
    fin_cases j <;> simp [smul_eq_mul]
  calc
    symplecticLineGraphMap K L hvertical z i =
        symplecticLineGraphMap K L hvertical
          (z 0 • ![1, 0] + z 1 • ![0, 1]) i := by
      rw [← hz]
    _ = symplecticLineGraphMap K L hvertical ![1, 0] i * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] i * z 1 := by
      rw [map_add, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

lemma symplecticLineGraphMap_graphVector
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (z : Fin 2 → K) :
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      ((symplecticLineHorizontalProjectionEquiv K L hvertical).symm z :
        SymplecticVector K) := by
  let u : L.1 :=
    (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z
  have hu :
      symplecticHorizontalProjection K
        (u : SymplecticVector K) = z := by
    change
      symplecticLineHorizontalProjectionEquiv K L hvertical u = z
    exact
      (symplecticLineHorizontalProjectionEquiv K L hvertical).apply_symm_apply z
  have hg :
      symplecticLineGraphMap K L hvertical z =
        symplecticVerticalProjection K
          (u : SymplecticVector K) := by
    rw [← hu]
    exact symplecticLineGraphMap_horizontal K L hvertical u
  change
    symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) =
      (u : SymplecticVector K)
  funext i
  fin_cases i
  · simpa only [symmetricGraphVector, Fin.isValue, Nat.reduceAdd, Fin.zero_eta, Matrix.cons_val_zero,
      symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk] using (congrFun hu 0).symm
  · have hg0 := congrFun hg 0
    change
      symplecticLineGraphMap K L hvertical z 0 =
        (u : SymplecticVector K) 1 at hg0
    change
      symplecticLineGraphMap K L hvertical ![1, 0] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 1 =
        (u : SymplecticVector K) 1
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 0).symm.trans hg0
  · simpa only [symmetricGraphVector, Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val,
      symplecticHorizontalProjection, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      (congrFun hu 1).symm
  · have hg1 := congrFun hg 1
    change
      symplecticLineGraphMap K L hvertical z 1 =
        (u : SymplecticVector K) 3 at hg1
    change
      symplecticLineGraphMap K L hvertical ![0, 1] 0 * z 0 +
        symplecticLineGraphMap K L hvertical ![0, 1] 1 * z 1 =
        (u : SymplecticVector K) 3
    rw [← symplecticLineGraphMap_symmetric K L hvertical]
    exact (symplecticLineGraphMap_coordinate_expansion
      K L hvertical z 1).symm.trans hg1

lemma symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1) :
    ∃ a b c : K, L = symmetricGraphLine K a b c := by
  let a := symplecticLineGraphMap K L hvertical ![1, 0] 0
  let b := symplecticLineGraphMap K L hvertical ![0, 1] 0
  let c := symplecticLineGraphMap K L hvertical ![0, 1] 1
  refine ⟨a, b, c, ?_⟩
  apply Subtype.ext
  change L.1 = LinearMap.range (symmetricGraphLinearMap K a b c)
  apply le_antisymm
  · intro w hw
    let x : L.1 := ⟨w, hw⟩
    let z := symplecticHorizontalProjection K
      (w : SymplecticVector K)
    refine ⟨z, ?_⟩
    change symmetricGraphVector K a b c (z 0) (z 1) = w
    have hgraph := symplecticLineGraphMap_graphVector
      K L hvertical z
    have hpreimage :
        (symplecticLineHorizontalProjectionEquiv K L hvertical).symm z =
          x := by
      apply
        (symplecticLineHorizontalProjectionEquiv K L hvertical).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) = w
    rw [hgraph, hpreimage]
  · intro w hw
    obtain ⟨z, rfl⟩ := hw
    change
      symmetricGraphVector K a b c (z 0) (z 1) ∈ L.1
    change
      symmetricGraphVector K
        (symplecticLineGraphMap K L hvertical ![1, 0] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 0)
        (symplecticLineGraphMap K L hvertical ![0, 1] 1)
        (z 0) (z 1) ∈ L.1
    rw [symplecticLineGraphMap_graphVector K L hvertical z]
    exact ((symplecticLineHorizontalProjectionEquiv
      K L hvertical).symm z).2

lemma symmetricGraphLine_det_ne_zero_of_disjoint_horizontal
    (a b c : K)
    (hhorizontal :
      Disjoint (symmetricGraphLine K a b c).1
        (symmetricGraphLine K 0 0 0).1) :
    (a * c - b ^ 2) ≠ 0 := by
  intro hdet
  have hkernel :
      ∃ x y : K,
        (x ≠ 0 ∨ y ≠ 0) ∧
          a * x + b * y = 0 ∧
          b * x + c * y = 0 := by
    by_cases ha : a = 0
    · have hb : b = 0 := by
        have hsq : b ^ 2 = 0 := by
          simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, ha, zero_mul,
            zero_sub, neg_eq_zero] using hdet
        exact eq_zero_of_pow_eq_zero hsq
      exact ⟨1, 0, Or.inl one_ne_zero, by simp only [ha, mul_one, hb, mul_zero, add_zero],
        by simp only [hb, mul_one, mul_zero, add_zero]⟩
    · refine ⟨b, -a, Or.inr (neg_ne_zero.mpr ha), ?_, ?_⟩
      · ring
      · linear_combination -hdet
  obtain ⟨x, y, hnonzero, hfirst, hsecond⟩ := hkernel
  let w := symmetricGraphVector K a b c x y
  have hwgraph : w ∈ (symmetricGraphLine K a b c).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K a b c)
    exact ⟨![x, y], rfl⟩
  have hwhorizontal : w ∈ (symmetricGraphLine K 0 0 0).1 := by
    change w ∈ LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    refine ⟨![x, y], ?_⟩
    funext i
    fin_cases i <;>
      simp [symmetricGraphLinearMap, symmetricGraphVector,
        w, hfirst, hsecond]
  have hwzero : w = (0 : SymplecticVector K) := by
    have hbot : w ∈ (⊥ : Submodule K (SymplecticVector K)) :=
      hhorizontal.le_bot ⟨hwgraph, hwhorizontal⟩
    simpa only [Submodule.mem_bot] using hbot
  have hxzero : x = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 0
  have hyzero : y = 0 := by
    simpa [w, symmetricGraphVector] using congrFun hwzero 2
  exact hnonzero.elim (fun h => h hxzero) (fun h => h hyzero)

lemma symplecticLine_eq_invertible_symmetricGraphLine
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (hhorizontal :
      Disjoint L.1 (symmetricGraphLine K 0 0 0).1) :
    ∃ a b c : K,
      L = symmetricGraphLine K a b c ∧
        (a * c - b ^ 2) ≠ 0 := by
  obtain ⟨a, b, c, hL⟩ :=
    symplecticLine_eq_symmetricGraphLine_of_disjoint_vertical
      K L hvertical
  refine ⟨a, b, c, hL, ?_⟩
  apply symmetricGraphLine_det_ne_zero_of_disjoint_horizontal K a b c
  rw [← hL]
  exact hhorizontal

lemma symplecticCanonicalLines_disjoint :
    Disjoint (symmetricGraphLine K 0 0 0).1
      (symplecticVerticalLine K).1 := by
  apply Submodule.disjoint_def.mpr
  intro w hwH hwV
  change w ∈ LinearMap.range
    (symmetricGraphLinearMap K 0 0 0) at hwH
  change w ∈ LinearMap.range
    (symplecticVerticalLinearMap K) at hwV
  obtain ⟨z, hz⟩ := hwH
  obtain ⟨t, ht⟩ := hwV
  have heq := hz.trans ht.symm
  have hz0 : z 0 = 0 := by
    simpa only [Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector, zero_mul, add_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_zero, symplecticVerticalLinearMap] using congrFun heq 0
  have hz1 : z 1 = 0 := by
    simpa only [Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector, zero_mul, add_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val, symplecticVerticalLinearMap] using congrFun heq 2
  rw [← hz]
  funext i
  fin_cases i <;>
    simp [symmetricGraphLinearMap, symmetricGraphVector,
      hz0, hz1]

lemma symplecticVertical_mem_coordinateCenter_of_orthogonal
    {x y : K} (hxy : x ≠ 0 ∨ y ≠ 0)
    {v : SymplecticVector K}
    (hv : v ∈ (symplecticVerticalLine K).1)
    (horth : standardSymplecticForm K
      (symplecticHorizontalVector K x y) v = 0) :
    v ∈ (coordinateCenterLine K x y hxy).1 := by
  change v ∈ LinearMap.range (symplecticVerticalLinearMap K) at hv
  obtain ⟨z, hz⟩ := hv
  have hv0 : v 0 = 0 := by
    simpa only [Fin.isValue, symplecticVerticalLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.cons_val_zero] using (congrFun hz 0).symm
  have hv2 : v 2 = 0 := by
    simpa only [Fin.isValue, symplecticVerticalLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val] using
      (congrFun hz 2).symm
  have heq : x * v 1 + y * v 3 = 0 := by
    simpa only [Fin.isValue, standardSymplecticForm, symplecticHorizontalVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, zero_mul, sub_zero, Matrix.cons_val] using horth
  change v ∈ LinearMap.range (coordinateCenterLinearMap K x y)
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      rcases hxy with h | h
      · exact False.elim (h hx)
      · exact h
    refine ⟨![0, -(v 1 / y)], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hy]
    linear_combination -heq
  · refine ⟨![0, v 3 / x], ?_⟩
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hv0, hv2] <;>
      field_simp [hx]
    linear_combination -heq

lemma symplecticLine_eq_coordinateCenterLine_of_common_points
    (C : SymplecticLine K)
    (p q : SymplecticPoint K)
    (hpH : p.1 ≤ (symmetricGraphLine K 0 0 0).1)
    (hpC : p.1 ≤ C.1)
    (hqV : q.1 ≤ (symplecticVerticalLine K).1)
    (hqC : q.1 ≤ C.1) :
    ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
      C = coordinateCenterLine K x y hxy := by
  have hpos : 0 < Module.finrank K p.1 := by
    rw [p.2]
    norm_num
  obtain ⟨u, hu⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have huhorizontal := hpH u.2
  change
    (u : SymplecticVector K) ∈
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
    at huhorizontal
  obtain ⟨z, hz⟩ := huhorizontal
  have hu1 : (u : SymplecticVector K) 1 = 0 := by
    simpa only [Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector, zero_mul, add_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val_one, Matrix.cons_val_zero] using (congrFun hz 1).symm
  have hu3 : (u : SymplecticVector K) 3 = 0 := by
    simpa only [Fin.isValue, symmetricGraphLinearMap, symmetricGraphVector, zero_mul, add_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.cons_val] using (congrFun hz 3).symm
  let x : K := (u : SymplecticVector K) 0
  let y : K := (u : SymplecticVector K) 2
  have huvector :
      (u : SymplecticVector K) =
        symplecticHorizontalVector K x y := by
    funext i
    fin_cases i <;>
      simp [symplecticHorizontalVector, x, y, hu1, hu3]
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    have hx : x = 0 :=
      Classical.byContradiction (fun hx => h (Or.inl hx))
    have hy : y = 0 :=
      Classical.byContradiction (fun hy => h (Or.inr hy))
    have huzero : (u : SymplecticVector K) = 0 := by
      rw [huvector, hx, hy]
      simp only [symplecticHorizontalVector, Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_self]
    apply hu
    apply Subtype.ext
    simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] using huzero
  have hpq : p ≠ q := by
    intro heq
    subst q
    have hbot :
        (u : SymplecticVector K) ∈
          (⊥ : Submodule K (SymplecticVector K)) :=
      (symplecticCanonicalLines_disjoint K).le_bot
        ⟨hpH u.2, hqV u.2⟩
    apply hu
    apply Subtype.ext
    simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero, Submodule.mem_bot] using hbot
  have hucenter :
      (u : SymplecticVector K) ∈
        (coordinateCenterLine K x y hxy).1 := by
    change
      (u : SymplecticVector K) ∈
        LinearMap.range (coordinateCenterLinearMap K x y)
    refine ⟨![1, 0], ?_⟩
    rw [huvector]
    simp only [coordinateCenterLinearMap, Fin.isValue, symplecticHorizontalVector, Matrix.smul_cons, smul_eq_mul,
      mul_zero, Matrix.smul_empty, symplecticAnnihilatorVector, mul_neg, Matrix.add_cons, Matrix.head_cons, add_zero,
      Matrix.tail_cons, zero_add, Matrix.empty_add_empty, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, one_mul,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, neg_zero]
  have hpcenter :
      p.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hu (⟨v, hv⟩ : p.1)
    have hav : a • (u : SymplecticVector K) = v :=
      congrArg Subtype.val ha
    rw [← hav]
    exact (coordinateCenterLine K x y hxy).1.smul_mem a hucenter
  have hqcenter :
      q.1 ≤ (coordinateCenterLine K x y hxy).1 := by
    intro v hv
    apply symplecticVertical_mem_coordinateCenter_of_orthogonal
      K hxy (hqV hv)
    rw [← huvector]
    exact C.2.2 (u : SymplecticVector K)
      (hpC u.2) v (hqC hv)
  refine ⟨x, y, hxy, ?_⟩
  apply Subtype.ext
  have hspanC : p.1 ⊔ q.1 = C.1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpC hqC)
      ((symplecticPoint_sup_finrank K hpq).trans C.2.1.symm)
  have hspanCenter :
      p.1 ⊔ q.1 = (coordinateCenterLine K x y hxy).1 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le hpcenter hqcenter)
      ((symplecticPoint_sup_finrank K hpq).trans
        (coordinateCenterLine K x y hxy).2.1.symm)
  exact hspanC.symm.trans hspanCenter

lemma coordinateCenterLine_direction_det_ne_zero_of_ne
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by
  intro hdet
  have hscale :
      ∃ t : K, t ≠ 0 ∧ x' = t * x ∧ y' = t * y := by
    rcases hxy with hx | hy
    · let t : K := x' / x
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hx]
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hx]
        linear_combination hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
    · let t : K := y' / y
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hy]
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hy]
        linear_combination -hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
  obtain ⟨t, ht, hfirst, hsecond⟩ := hscale
  apply hne
  apply Subtype.ext
  change
    LinearMap.range (coordinateCenterLinearMap K x y) =
      LinearMap.range (coordinateCenterLinearMap K x' y')
  have hmap (u : Fin 2 → K) :
      coordinateCenterLinearMap K x' y' u =
        t • coordinateCenterLinearMap K x y u := by
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hfirst, hsecond] <;>
      ring
  apply le_antisymm
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t⁻¹ • u, ?_⟩
    rw [hmap, map_smul]
    simp only [ne_eq, ht, not_false_eq_true, smul_inv_smul₀]
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t • u, ?_⟩
    rw [map_smul, ← hmap]

lemma symplecticAutomorphism_disjoint_iff
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K) :
    Disjoint (symplecticAutomorphismLine K e L).1
        (symplecticAutomorphismLine K e M).1 ↔
      Disjoint L.1 M.1 := by
  change
    Disjoint (L.1.map e.toLinearEquiv.toLinearMap)
        (M.1.map e.toLinearEquiv.toLinearMap) ↔
      Disjoint L.1 M.1
  rw [disjoint_iff,
    ← Submodule.map_inf e.toLinearEquiv.toLinearMap
      e.toLinearEquiv.injective,
    Submodule.map_eq_bot_iff,
    ← disjoint_iff]

lemma symplecticCanonical_line_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (X : SymplecticLine K)
    (hXH :
      Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV :
      Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  classical
  obtain ⟨a, b, c, hXgraph, hdet⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine
      K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 3) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hdir {i j : Fin 3} (hij : i ≠ j) :
      x i * y j - x j * y i ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy i) (hxy j)
    intro heq
    apply hij
    apply hcenters
    exact (hrepr i).trans (heq.trans (hrepr j).symm)
  have h01 : x 0 * y 1 - x 1 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 1)
  have h02 : x 0 * y 2 - x 2 * y 0 ≠ 0 :=
    hdir (by decide : (0 : Fin 3) ≠ 2)
  have h12 : x 1 * y 2 - x 2 * y 1 ≠ 0 :=
    hdir (by decide : (1 : Fin 3) ≠ 2)
  apply symmetricGraphLine_odd_no_three_actual_centers K
    htwo hdet h01 h02 h12
  · obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  · obtain ⟨p, hpX, hpC⟩ := hX 2
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 2]
      exact hpC

theorem symplecticLine_no_three_common_centers
    (htwo : (2 : K) ≠ 0)
    (Y Z X : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (centers : Fin 3 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hY : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (centers i).1)
    (hZ : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 3,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    False := by
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  have hleft :
      symplecticAutomorphismLine K e Y =
        symmetricGraphLine K 0 0 0 := by
    exact symplecticLineNormalizer_map_left K Y Z hYZ
  have hright :
      symplecticAutomorphismLine K e Z =
        symplecticVerticalLine K := by
    exact symplecticLineNormalizer_map_right K Y Z hYZ
  apply symplecticCanonical_line_no_three_common_centers K htwo
    (symplecticAutomorphismLine K e X)
    (centers := fun i =>
      symplecticAutomorphismLine K e (centers i))
  · rw [← hleft]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  · rw [← hright]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  · intro i j hij
    apply hcenters
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  · intro i
    obtain ⟨p, hpY, hpC⟩ := hY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hleft]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpZ, hpC⟩ := hZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← hright]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC
  · intro i
    obtain ⟨p, hpX, hpC⟩ := hX i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · exact (symplecticAutomorphism_incidence_iff K e p X).mpr hpX
    · exact
        (symplecticAutomorphism_incidence_iff K e p
          (centers i)).mpr hpC

theorem symplecticQuadrangle_no_line_gamma_of_odd
    (htwo : (2 : K) ≠ 0)
    (copy : SimpleGraph.Copy gammaGraph
      (symplecticQuadrangle K))
    (C : SymplecticLine K)
    (hC : copy kSpecifiedCenter = .inr C) :
    False := by
  classical
  have hspecified :
      copy (.inl (.inr (0 : Fin 3))) = .inr C := by
    simpa only [Fin.isValue, kSpecifiedCenter] using hC
  have hbase_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inl i)) = .inr L :=
    subdivisionLine_base_of_line_center K copy
      (base := i) (center := (0 : Fin 3)) hspecified
  choose bases hbase using hbase_exists
  have hcenter_exists (i : Fin 3) :
      ∃ L : SymplecticLine K,
        copy (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K copy
      (base := (0 : Fin 3)) (center := i) (hbase 0)
  choose centers hcenter using hcenter_exists
  apply symplecticLine_no_three_common_centers K htwo
    (bases 1) (bases 2) (bases 0)
    (centers := centers)
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (1 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 1) 0
  · exact subdivisionLine_bases_disjoint K copy bases centers
      hbase hcenter (by decide : (0 : Fin 3) ≠ 2) 0
  · exact subdivisionLine_centers_injective K copy centers hcenter
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 1) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 2) (hcenter i)
    exact ⟨p, hpB, hpC⟩
  · intro i
    obtain ⟨p, _, hpB, hpC⟩ := subdivisionLine_pair_incidence
      K copy (hbase 0) (hcenter i)
    exact ⟨p, hpB, hpC⟩

theorem symplecticQuadrangle_no_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (quotientGraph kTemplate f).Free
      (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  let hom : kTemplate →g symplecticQuadrangle K :=
    copy.toHom.comp (kQuotientProjectionHom hf)
  have hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = i} := by
    intro i u hu v hv huv
    change
      copy (⟨f u, u, rfl⟩ : Set.range f) =
        copy (⟨f v, v, rfl⟩ : Set.range f)
      at huv
    apply hf.2 i hu hv
    exact congrArg Subtype.val (copy.injective huv)
  obtain ⟨i, L, hL⟩ :=
    symplecticQuadrangle_kTemplate_has_line_gamma
      K hom hcopies
  exact symplecticQuadrangle_no_line_gamma_of_odd K htwo
    (kGammaHomCopy hom hcopies i) L hL

theorem symplecticQuadrangle_encodeFiniteGraph_free_iff
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (encodeFiniteGraph G).graph.Free
        (symplecticQuadrangle K) ↔
      G.Free (symplecticQuadrangle K) :=
  (SimpleGraph.free_congr_left
    (SimpleGraph.Iso.map (Fintype.equivFin V) G)).symm

theorem symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (htwo : (2 : K) ≠ 0)
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  (symplecticQuadrangle_encodeFiniteGraph_free_iff K
    (quotientGraph kTemplate f)).mpr
    (symplecticQuadrangle_no_kQuotient_of_odd K htwo hf)

end ArbitraryLineNormalization

noncomputable section JQuotientAvoidanceReduction

open SimpleGraph

lemma jQuotient_free_of_template_avoidance
    {V : Type*} (host : SimpleGraph V)
    (havoid : ∀ hom : jTemplate →g host,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (quotientGraph jTemplate f).Free host := by
  rintro ⟨copy⟩
  let hom : jTemplate →g host :=
    copy.toHom.comp (jQuotientProjectionHom hf)
  apply havoid hom
  · intro first second heq
    change
      copy (⟨f (.inl (.inl first)),
        .inl (.inl first), rfl⟩ : Set.range f) =
        copy (⟨f (.inl (.inl second)),
          .inl (.inl second), rfl⟩ : Set.range f)
      at heq
    apply hf.2.1
    exact congrArg Subtype.val (copy.injective heq)
  · intro index first hfirst second hsecond heq
    change
      copy (⟨f first, first, rfl⟩ : Set.range f) =
        copy (⟨f second, second, rfl⟩ : Set.range f)
      at heq
    apply hf.2.2 index hfirst hsecond
    exact congrArg Subtype.val (copy.injective heq)

theorem symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance
    (K : Type*) [Field K]
    (havoid : ∀ hom : jTemplate →g symplecticQuadrangle K,
      Function.Injective
          (fun base : Fin 4 => hom (.inl (.inl base))) →
      (∀ copy : Fin 2, Set.InjOn hom {vertex | InJCopy copy vertex}) →
      False)
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) := by
  exact
    (symplecticQuadrangle_encodeFiniteGraph_free_iff K
      (quotientGraph jTemplate f)).mpr
      (jQuotient_free_of_template_avoidance
        (symplecticQuadrangle K) havoid hf)

end JQuotientAvoidanceReduction

noncomputable section JTemplateLineAvoidanceReduction

open SimpleGraph

variable (K : Type*) [Field K]

def CharTwoLinePairAvoidance : Prop :=
  ∀ (Y Z X X' : SymplecticLine K),
    Disjoint Y.1 Z.1 →
    Disjoint X.1 Y.1 →
    Disjoint X.1 Z.1 →
    Disjoint X'.1 Y.1 →
    Disjoint X'.1 Z.1 →
    X ≠ X' →
    ∀ (C C' : Fin 2 → SymplecticLine K),
      Function.Injective C →
      Function.Injective C' →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X.1 ∧ p.1 ≤ (C i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1) →
      (∀ i : Fin 2,
        ∃ p : SymplecticPoint K,
          p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) →
      Disjoint X.1 X'.1

theorem symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    (havoid : CharTwoLinePairAvoidance K)
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun i : Fin 4 => hom (.inl (.inl i))))
    (hcopies : ∀ i : Fin 2,
      Set.InjOn hom {v | InJCopy i v}) :
    False := by
  classical
  let θ (i : Fin 2) := jThetaHomCopy hom hcopies i
  obtain ⟨X, hX⟩ :=
    symplecticQuadrangle_jTemplate_first_base_is_line
      K hom hbase_inj hcopies
  have hθ0X :
      θ 0 (.inl (.inl (0 : Fin 3))) = .inr X := by
    change
      hom (jThetaVertex 0 (.inl (.inl (0 : Fin 3)))) =
        .inr X
    simpa only [jThetaVertex, jBase, Fin.isValue, ↓reduceIte] using hX
  obtain ⟨Y, hθ0Y⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (1 : Fin 3)) (0 : Fin 2) hθ0X
  have hY :
      hom (.inl (.inl (2 : Fin 4))) = .inr Y := by
    change
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) =
        .inr Y at hθ0Y
    simpa only [Fin.isValue, jThetaVertex, jBase, one_ne_zero, ↓reduceIte] using hθ0Y
  obtain ⟨Z, hθ0Z⟩ :=
    subdivisionLine_base_of_line_base K (θ 0)
      (otherBase := (2 : Fin 3)) (0 : Fin 2) hθ0X
  have hZ :
      hom (.inl (.inl (3 : Fin 4))) = .inr Z := by
    change
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) =
        .inr Z at hθ0Z
    simpa only [Fin.isValue, jThetaVertex, jBase, Fin.reduceEq, ↓reduceIte] using hθ0Z
  have hθ1Y :
      θ 1 (.inl (.inl (1 : Fin 3))) = .inr Y := by
    change
      hom (jThetaVertex 1 (.inl (.inl (1 : Fin 3)))) =
        .inr Y
    simpa only [jThetaVertex, jBase, Fin.isValue, one_ne_zero, ↓reduceIte] using hY
  obtain ⟨X', hθ1X'⟩ :=
    subdivisionLine_base_of_line_base K (θ 1)
      (otherBase := (0 : Fin 3)) (0 : Fin 2) hθ1Y
  have hX' :
      hom (.inl (.inl (1 : Fin 4))) = .inr X' := by
    change
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) =
        .inr X' at hθ1X'
    simpa only [Fin.isValue, jThetaVertex, jBase, ↓reduceIte, one_ne_zero] using hθ1X'
  let B : Fin 3 → SymplecticLine K := ![X, Y, Z]
  let B' : Fin 3 → SymplecticLine K := ![X', Y, Z]
  have hθ1Z :
      θ 1 (.inl (.inl (2 : Fin 3))) = .inr Z := by
    change
      hom (jThetaVertex 1 (.inl (.inl (2 : Fin 3)))) =
        .inr Z
    simpa only [jThetaVertex, jBase, Fin.isValue, Fin.reduceEq, ↓reduceIte] using hZ
  have hB : ∀ i : Fin 3,
      θ 0 (.inl (.inl i)) = .inr (B i) := by
    intro i
    fin_cases i
    · simpa [B] using hθ0X
    · simpa [B] using hθ0Y
    · simpa [B] using hθ0Z
  have hB' : ∀ i : Fin 3,
      θ 1 (.inl (.inl i)) = .inr (B' i) := by
    intro i
    fin_cases i
    · simpa [B'] using hθ1X'
    · simpa [B'] using hθ1Y
    · simpa [B'] using hθ1Z
  have hC_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 0 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 0)
      (base := (0 : Fin 3)) (center := i) (hB 0)
  choose C hC using hC_exists
  have hC'_exists (i : Fin 2) :
      ∃ L : SymplecticLine K,
        θ 1 (.inl (.inr i)) = .inr L :=
    subdivisionLine_center_of_line_base K (θ 1)
      (base := (0 : Fin 3)) (center := i) (hB' 0)
  choose C' hC' using hC'_exists
  have hXX' : X ≠ X' := by
    intro heq
    have hbaseeq : (0 : Fin 4) = 1 := by
      apply hbase_inj
      change
        hom (.inl (.inl (0 : Fin 4))) =
          hom (.inl (.inl (1 : Fin 4)))
      rw [hX, hX', heq]
    exact (by decide : (0 : Fin 4) ≠ 1) hbaseeq
  have hYZ : Disjoint Y.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (1 : Fin 3) ≠ 2) (0 : Fin 2)
  have hXY : Disjoint X.1 Y.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hXZ : Disjoint X.1 Z.1 := by
    simpa [B] using
      subdivisionLine_bases_disjoint K (θ 0) B C hB hC
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hX'Y : Disjoint X'.1 Y.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 1) (0 : Fin 2)
  have hX'Z : Disjoint X'.1 Z.1 := by
    simpa [B'] using
      subdivisionLine_bases_disjoint K (θ 1) B' C' hB' hC'
        (by decide : (0 : Fin 3) ≠ 2) (0 : Fin 2)
  have hdisjoint : Disjoint X.1 X'.1 := by
    apply havoid Y Z X X'
      hYZ hXY hXZ hX'Y hX'Z hXX' C C'
      (subdivisionLine_centers_injective K (θ 0) C hC)
      (subdivisionLine_centers_injective K (θ 1) C' hC')
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 1) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 2) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 0) (hB 0) (hC i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 1) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 2) (hC' i)
      exact ⟨p, hpB, hpC⟩
    · intro i
      obtain ⟨p, _, hpB, hpC⟩ :=
        subdivisionLine_pair_incidence K (θ 1) (hB' 0) (hC' i)
      exact ⟨p, hpB, hpC⟩
  have hjoinX : jTemplate.Adj
      (.inl (.inl (0 : Fin 4))) (.inr (.inr ())) := by
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      zero_ne_one, or_false, and_self]
  have hjoinX' : jTemplate.Adj
      (.inl (.inl (1 : Fin 4))) (.inr (.inr ())) := by
    simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
      one_ne_zero, or_true, or_false, and_self]
  have hadjX := hom.map_rel hjoinX
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX
  rw [hX] at hadjX
  obtain ⟨p, hpjoin, hpX⟩ :=
    symplecticQuadrangle_adjacent_to_line K hadjX
  have hadjX' := hom.map_rel hjoinX'
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hadjX'
  rw [hX', hpjoin] at hadjX'
  have hpX' : p.1 ≤ X'.1 :=
    (symplecticQuadrangle_incidence_adj K p X').mp
      hadjX'.symm
  have hpzero :
      p.1 = (⊥ : Submodule K (SymplecticVector K)) :=
    eq_bot_iff.mpr
      ((le_inf hpX hpX').trans hdisjoint.le_bot)
  have hdim := p.2
  rw [hpzero] at hdim
  simp only [finrank_bot, zero_ne_one] at hdim

end JTemplateLineAvoidanceReduction

noncomputable section CharacteristicTwoLineAvoidance

open SimpleGraph

variable (K : Type*) [Field K] [CharP K 2] [Finite K]

lemma symplecticLine_char_two_canonical_zero_diagonal
    (X : SymplecticLine K)
    (hXH : Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV : Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 2 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    ∃ b : K, X = symmetricGraphLine K 0 b 0 := by
  classical
  obtain ⟨a, b, c, hXgraph, _⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 2) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hind : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy 0) (hxy 1)
    intro heq
    have hindex : (0 : Fin 2) = 1 := by
      apply hcenters
      exact (hrepr 0).trans (heq.trans (hrepr 1).symm)
    exact (by decide : (0 : Fin 2) ≠ 1) hindex
  have hfirst :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 0) (y 0)
              (projectiveDirection_nonzero_left K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  have hsecond :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 1) (y 1)
              (projectiveDirection_nonzero_right K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  obtain ⟨ha, hc⟩ :=
    symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
      K hind hfirst hsecond
  refine ⟨b, ?_⟩
  simpa only [ha, hc] using hXgraph

omit [CharP K 2] [Finite K] in
lemma symplecticAutomorphism_commonPoint
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K)
    (hpoint : ∃ p : SymplecticPoint K,
      p.1 ≤ L.1 ∧ p.1 ≤ M.1) :
    ∃ p : SymplecticPoint K,
      p.1 ≤ (symplecticAutomorphismLine K e L).1 ∧
        p.1 ≤ (symplecticAutomorphismLine K e M).1 := by
  obtain ⟨p, hpL, hpM⟩ := hpoint
  exact ⟨symplecticAutomorphismPoint K e p,
    (symplecticAutomorphism_incidence_iff K e p L).mpr hpL,
    (symplecticAutomorphism_incidence_iff K e p M).mpr hpM⟩

lemma symplecticLine_char_two_disjoint_of_two_common_center_pairs
    (Y Z X X' : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (hX'Y : Disjoint X'.1 Y.1)
    (hX'Z : Disjoint X'.1 Z.1)
    (hXX' : X ≠ X')
    (C C' : Fin 2 → SymplecticLine K)
    (hCinj : Function.Injective C)
    (hC'inj : Function.Injective C')
    (hCY : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1)
    (hCZ : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1)
    (hCX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (C i).1)
    (hC'Y : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1)
    (hC'Z : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1)
    (hC'X : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) :
    Disjoint X.1 X'.1 := by
  classical
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  let Xn : SymplecticLine K := symplecticAutomorphismLine K e X
  let X'n : SymplecticLine K := symplecticAutomorphismLine K e X'
  let Cn : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C i)
  let C'n : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C' i)
  have hXH : Disjoint Xn.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  have hXV : Disjoint Xn.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  have hX'H : Disjoint X'n.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Y).mpr hX'Y
  have hX'V : Disjoint X'n.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Z).mpr hX'Z
  have hCn : Function.Injective Cn := by
    intro i j hij
    apply hCinj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hC'n : Function.Injective C'n := by
    intro i j hij
    apply hC'inj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hCnH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hCY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hCZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ Xn.1 ∧ p.1 ≤ (Cn i).1 := by
    exact symplecticAutomorphism_commonPoint K e X (C i) (hCX i)
  have hC'nH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hC'Y i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hC'Z i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'n.1 ∧ p.1 ≤ (C'n i).1 := by
    exact symplecticAutomorphism_commonPoint K e X' (C' i) (hC'X i)
  obtain ⟨b, hb⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K Xn hXH hXV Cn hCn hCnH hCnV hCnX
  obtain ⟨b', hb'⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K X'n hX'H hX'V C'n hC'n hC'nH hC'nV hC'nX
  have hbb : b ≠ b' := by
    intro heq
    apply hXX'
    apply (symplecticAutomorphismLineEquiv K e).injective
    simp only [symplecticAutomorphismLineEquiv_apply]
    change Xn = X'n
    rw [hb, hb', heq]
  apply (symplecticAutomorphism_disjoint_iff K e X X').mp
  change Disjoint Xn.1 X'n.1
  rw [hb, hb']
  exact symmetricGraphLine_zero_diagonal_disjoint K hbb

lemma symplecticLine_char_two_pair_avoidance :
    CharTwoLinePairAvoidance K :=
  symplecticLine_char_two_disjoint_of_two_common_center_pairs K

theorem symplecticQuadrangle_no_jTemplate_of_char_two
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {vertex | InJCopy copy vertex}) :
    False :=
  symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    K (symplecticLine_char_two_pair_avoidance K) hom hbase hcopies

theorem symplecticQuadrangle_no_encoded_jQuotient_of_char_two
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
      (symplecticQuadrangle K) :=
  symplecticQuadrangle_no_encoded_jQuotient_of_template_avoidance K
    (symplecticQuadrangle_no_jTemplate_of_char_two K) hf

end CharacteristicTwoLineAvoidance

noncomputable section UpperBoundReduction

open Filter Finset SimpleGraph
open scoped Classical Topology

theorem familyExtremal_real_le_of_forall_free
    (family : Finset FiniteGraph) (n : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hfree : ∀ host : SimpleGraph (Fin n),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ≤ bound) :
    (familyExtremal family n : ℝ) ≤ bound := by
  classical
  have hnat : familyExtremal family n ≤ ⌊bound⌋₊ := by
    unfold familyExtremal
    apply Finset.sup_le
    intro host hhost
    apply Nat.le_floor
    simpa only [edgeFinset_card_eq_natCard] using
      hfree host (Finset.mem_filter.mp hhost).2
  have hcast : (familyExtremal family n : ℝ) ≤ (⌊bound⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le hbound)

lemma familyLittleO_of_eventual_host_bounds
    (family : Finset FiniteGraph)
    (hhost : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ host : SimpleGraph (Fin n),
          FamilyFree family host →
            (host.edgeFinset.card : ℝ) ≤ ε * extremalScale n) :
    FamilyLittleO family := by
  intro ε hε
  filter_upwards [hhost ε hε] with n hn
  exact familyExtremal_real_le_of_forall_free family n
    (mul_nonneg hε.le (extremalScale_nonneg n)) hn

end UpperBoundReduction

noncomputable section AsymptoticExtraction

open Filter Finset SimpleGraph
open scoped Classical Topology

lemma familyFree_of_embedded_subgraph
    {family : Finset FiniteGraph}
    {n N : ℕ} (host : SimpleGraph (Fin n))
    (subgraph : SimpleGraph (Fin N))
    (embedding : Fin N ↪ Fin n)
    (hsub : subgraph.map embedding ≤ host)
    (hfree : FamilyFree family host) :
    FamilyFree family subgraph := by
  intro forbidden hforbidden hcontained
  exact hfree forbidden hforbidden
    ((hcontained.trans
      ⟨(SimpleGraph.Embedding.map embedding subgraph).toCopy⟩).mono_right hsub)

lemma eventually_constant_le_positive_nat_rpow
    (constant coefficient exponent : ℝ)
    (hcoefficient : 0 < coefficient)
    (hexponent : 0 < exponent) :
    ∀ᶠ n : ℕ in Filter.atTop,
      constant ≤ coefficient * (n : ℝ) ^ exponent := by
  have hpower :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ exponent)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpower.eventually
    (Filter.eventually_ge_atTop (constant / coefficient))]
    with n hn
  calc
    constant = coefficient * (constant / coefficient) := by
      field_simp
    _ ≤ coefficient * (n : ℝ) ^ exponent :=
      mul_le_mul_of_nonneg_left hn hcoefficient.le

lemma extremalScale_sixteenth_power
    {n : ℕ} (hn : 0 < n) :
    (extremalScale n) ^ 16 =
      (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold extremalScale
  calc
    ((n : ℝ) ^ ((4 : ℝ) / 3)) ^ 16 =
        (n : ℝ) ^ (((4 : ℝ) / 3) * (16 : ℝ)) := by
      exact (Real.rpow_mul_natCast hnreal.le
        ((4 : ℝ) / 3) 16).symm
    _ = (n : ℝ) ^ ((21 : ℝ) + (1 : ℝ) / 3) := by
      congr 1
      norm_num
    _ = (n : ℝ) ^ 21 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      simp only [one_div, Real.rpow_add hnreal, Real.rpow_ofNat]

lemma familyLittleO_of_sixteenth_power_host_bound
    (family : Finset FiniteGraph) (constant : ℝ)
    (hbound : ∀ (n : ℕ) (host : SimpleGraph (Fin n)),
      FamilyFree family host →
        (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21) :
    FamilyLittleO family := by
  apply familyLittleO_of_eventual_host_bounds
  intro ε hε
  have hεpow : 0 < ε ^ (16 : ℕ) := pow_pos hε _
  have hconstant := eventually_constant_le_positive_nat_rpow
    constant (ε ^ (16 : ℕ)) ((1 : ℝ) / 3)
    hεpow (by norm_num)
  filter_upwards [hconstant, Filter.eventually_gt_atTop 0]
    with n hn hnpositive
  intro host hfree
  have hhost := hbound n host hfree
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have htarget :
      (host.edgeFinset.card : ℝ) ^ 16 ≤
        (ε * extremalScale n) ^ 16 := by
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          constant * (n : ℝ) ^ 21 := hhost
      _ ≤ (ε ^ (16 : ℕ) * (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (n : ℝ) ^ 21 :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (ε * extremalScale n) ^ 16 := by
        rw [mul_pow, extremalScale_sixteenth_power hnpositive]
        ring
  have hresult :
      (Nat.card host.edgeSet : ℝ) ≤ ε * extremalScale n := by
    apply le_of_pow_le_pow_left₀
      (by norm_num : (16 : ℕ) ≠ 0)
      (mul_nonneg hε.le (extremalScale_nonneg n))
    simpa only [edgeFinset_card_eq_natCard] using htarget
  simpa only [edgeFinset_card_eq_natCard] using hresult

noncomputable def compactnessDegreePowerConstant : ℝ :=
  (48 : ℝ) ^ (4 : ℕ) + 1769472 + 1

theorem proposedFamilyFree_minDegree_ambient_sixteenth_power_le
    {N n : ℕ} (host : SimpleGraph (Fin N))
    (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin N, d ≤ host.degree v) :
    (d : ℝ) ^ 16 ≤
      compactnessDegreePowerConstant * (n : ℝ) ^ 5 := by
  classical
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoefLow :
      (48 : ℝ) ^ (4 : ℕ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefHigh :
      (1769472 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefOne : (1 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  by_cases hd : 2 ≤ d
  · by_cases hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)
    · have hhigh := proposedFamilyFree_minDegree_sixteenth_power_le
        host hN hfree hbip d hd hdegree hthreshold
      calc
        (d : ℝ) ^ 16 ≤ 1769472 * (N : ℝ) ^ 5 := hhigh
        _ ≤ 1769472 * (n : ℝ) ^ 5 := by
          gcongr
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefHigh (by positivity)
    · have hlow := fourPathHeavyThreshold_low_degree_fourth_le
        N d hN hd hthreshold
      have hfour :
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        calc
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by gcongr
          _ = (n : ℝ) ^ 4 * 1 := by ring
          _ ≤ (n : ℝ) ^ 4 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnreal (by positivity)
          _ = (n : ℝ) ^ 5 := by ring
      calc
        (d : ℝ) ^ 16 = ((d : ℝ) ^ 4) ^ 4 := by ring
        _ ≤ (48 * (N : ℝ)) ^ 4 := by gcongr
        _ = (48 : ℝ) ^ 4 * (N : ℝ) ^ 4 := by ring
        _ ≤ (48 : ℝ) ^ 4 * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_left hfour (by positivity)
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefLow (by positivity)
  · have hdNat : d ≤ 1 := by omega
    have hdReal : (d : ℝ) ≤ 1 := by exact_mod_cast hdNat
    calc
      (d : ℝ) ^ 16 ≤ (1 : ℝ) ^ 16 := by gcongr
      _ = 1 ^ (5 : ℕ) := by norm_num
      _ ≤ (n : ℝ) ^ 5 := by gcongr
      _ = 1 * (n : ℝ) ^ 5 := by ring
      _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hcoefOne (by positivity)

noncomputable def compactnessHostPowerConstant : ℝ :=
  (2 : ℝ) ^ (16 : ℕ) * compactnessDegreePowerConstant

theorem proposedFamilyFree_sixteenth_power_host_bound
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  by_cases hzero : host.edgeFinset.card = 0
  · simp only [hzero, Nat.cast_zero, zero_pow (by norm_num : 16 ≠ 0)]
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  · have hpositive : 0 < host.edgeFinset.card :=
      Nat.pos_of_ne_zero hzero
    obtain ⟨N, B, f, hN, hNn, hBbip, hmap, hminimum,
      _hminimum_pointwise⟩ :=
      exists_bipartite_min_degree_subgraph host hpositive
    have hn : 0 < n := by
      omega
    have hBfree : FamilyFree proposedFamily B :=
      familyFree_of_embedded_subgraph host B f hmap hfree
    let d : ℕ := B.minDegree
    have hdegree : ∀ v : Fin N, d ≤ B.degree v := by
      intro v
      exact B.minDegree_le_degree v
    have hminimumNat :
        host.edgeFinset.card ≤ 2 * n * d := by
      simpa only [d] using hminimum
    have hminimumReal :
        (host.edgeFinset.card : ℝ) ≤
          2 * (n : ℝ) * (d : ℝ) := by
      exact_mod_cast hminimumNat
    have hdPower := proposedFamilyFree_minDegree_ambient_sixteenth_power_le
      B hN hn hNn hBfree hBbip d hdegree
    calc
      (host.edgeFinset.card : ℝ) ^ 16 ≤
          (2 * (n : ℝ) * (d : ℝ)) ^ 16 := by
        gcongr
      _ = (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 * (d : ℝ) ^ 16 := by
        ring
      _ ≤ (2 : ℝ) ^ 16 * (n : ℝ) ^ 16 *
          (compactnessDegreePowerConstant * (n : ℝ) ^ 5) := by
        gcongr
      _ = compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
        unfold compactnessHostPowerConstant
        ring

theorem proposedFamily_familyLittleO :
    FamilyLittleO proposedFamily :=
  familyLittleO_of_sixteenth_power_host_bound
    proposedFamily compactnessHostPowerConstant
    proposedFamilyFree_sixteenth_power_host_bound

end AsymptoticExtraction

noncomputable section CycleBounds

open Filter Finset SimpleGraph
open scoped Topology

theorem four_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 4) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa only [manuscriptLowerConstant, extremalScale] using four_cycle_uniform_manuscript_lower hn

theorem six_cycle_eventual_manuscript_lower :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n
          (SimpleGraph.cycleGraph 6) : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount 3)]
    with n hn
  simpa only [manuscriptLowerConstant, extremalScale] using six_cycle_uniform_manuscript_lower hn

theorem member_eventual_lower_of_prime_power_avoidance
    {forbidden : FiniteGraph}
    (hmember : forbidden ∈ proposedFamily)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.graph.Free
        (symplecticQuadrangle (GaloisField t j))) :
    ∀ᶠ n : ℕ in atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ) := by
  filter_upwards [eventually_ge_atTop (quadrangleVertexCount t)]
    with n hn
  simpa only [manuscriptLowerConstant, extremalScale] using
    quadrangle_uniform_lower_of_prime_power_avoidance forbidden.graph (proposedFamily_member_no_isolated hmember) t ht
      htgap hfree hn

theorem uniformMemberLower_of_characteristic_avoidance
    (hj : ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)))
    (hk : ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j))) :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  proposedFamily_induction
    (P := fun graph => ∀ᶠ n : ℕ in Filter.atTop,
      manuscriptLowerConstant * extremalScale n ≤
        (SimpleGraph.extremalNumber n graph.graph : ℝ))
    (by simpa only [finiteCycle, eventually_atTop] using four_cycle_eventual_manuscript_lower)
    (by simpa only [finiteCycle, eventually_atTop] using six_cycle_eventual_manuscript_lower)
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (jQuotient_mem_proposedFamily hf)
      2 (by norm_num) (by norm_num) (hj f hf))
    (fun f hf => member_eventual_lower_of_prime_power_avoidance
      (kQuotient_mem_proposedFamily hf)
      3 (by norm_num) (by norm_num) (hk f hf))

end CycleBounds

noncomputable section Counterexample

open SimpleGraph

theorem proposedFamily_odd_characteristic_avoidance :
    ∀ (f : KVertex → KVertex), KAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 3 j)) := by
  intro f hf j _
  exact symplecticQuadrangle_no_encoded_kQuotient_of_odd
    (GaloisField 3 j)
    ((CharP.cast_eq_zero_iff (GaloisField 3 j) 3 2).not.mpr (by norm_num)) hf

theorem proposedFamily_even_characteristic_avoidance :
    ∀ (f : JVertex → JVertex), JAdmissible f →
      ∀ j : ℕ, 0 < j →
        (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Free
          (symplecticQuadrangle (GaloisField 2 j)) :=
  fun _ hf j _ =>
    symplecticQuadrangle_no_encoded_jQuotient_of_char_two
      (GaloisField 2 j) hf

theorem proposedFamily_uniformMemberLower :
    UniformMemberLower proposedFamily manuscriptLowerConstant :=
  uniformMemberLower_of_characteristic_avoidance
    proposedFamily_even_characteristic_avoidance
    proposedFamily_odd_characteristic_avoidance

theorem proposedFamily_not_compact :
    ¬ IsCompactFamily proposedFamily :=
  proposedFamily_not_compact_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

theorem not_erdos_180 :
    ¬ CompactnessConjectureStatement :=
  not_compactnessConjecture_of_bounds
    proposedFamily_familyLittleO proposedFamily_uniformMemberLower

end Counterexample

noncomputable section Connectedness

open Finset SimpleGraph

lemma jTemplate_connected : jTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable jTemplate).2
  let root : JVertex := .inl (.inl (2 : Fin 4))
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inl (jBase copy base)))
        (.inr (.inl (copy, (base, center)))) := by
    simp only [jTemplate, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation, or_false,
      and_self]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inr (copy, center)))
        (.inr (.inl (copy, (base, center)))) := by
    simp only [jTemplate, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation, and_self,
      or_false]
  have hrootCenter (copy : Fin 2) (center : Fin 2) :
      jTemplate.Reachable root (.inl (.inr (copy, center))) := by
    have hfirst :
        jTemplate.Adj root
          (.inr (.inl (copy, ((1 : Fin 3), center)))) := by
      simpa only [Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hbasePair copy 1 center
    exact hfirst.reachable.trans
      (hcenterPair copy 1 center).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Reachable root
        (.inr (.inl (copy, (base, center)))) :=
    (hrootCenter copy center).trans (hcenterPair copy base center).reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      jTemplate.Reachable root (.inl (.inl (jBase copy base))) :=
    (hrootPair copy base 0).trans (hbasePair copy base 0).symm.reachable
  intro vertex
  rcases vertex with (base | ⟨copy, center⟩) |
      (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · simpa only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, jBase, ↓reduceIte] using hrootBase 0 0
    · simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, jBase, ↓reduceIte, one_ne_zero] using hrootBase 1 0
    · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, jBase, one_ne_zero, ↓reduceIte] using hrootBase 0 1
    · simpa only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, jBase, Fin.reduceEq, ↓reduceIte] using hrootBase 0 2
  · exact hrootCenter copy center
  · exact hrootPair copy base center
  · cases lastVertex
    have hjoin :
        jTemplate.Adj (.inl (.inl (0 : Fin 4)))
          (.inr (.inr ())) := by
      simp only [jTemplate, Fin.isValue, fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true, jTemplateRelation,
        zero_ne_one, or_false, and_self]
    have hzero :
        jTemplate.Reachable root (.inl (.inl (0 : Fin 4))) := by
      simpa only [Fin.isValue, jBase, ↓reduceIte] using hrootBase 0 0
    exact hzero.trans hjoin.reachable

lemma kTemplate_connected : kTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable kTemplate).2
  let root : KVertex := ((0 : Fin 2), kSpecifiedCenter)
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inl base))
        (copy, .inr (base, center)) := by
    simp only [kTemplate, fromRel_adj, ne_eq, Prod.mk.injEq, reduceCtorEq, and_false, not_false_eq_true,
      kTemplateRelation, subdivisionRelation, and_self, Fin.isValue, true_or, false_or]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inr center))
        (copy, .inr (base, center)) := by
    simp only [kTemplate, fromRel_adj, ne_eq, Prod.mk.injEq, reduceCtorEq, and_false, not_false_eq_true,
      kTemplateRelation, subdivisionRelation, and_self, Fin.isValue, true_or, false_or]
  have hbridge :
      kTemplate.Adj root ((1 : Fin 2), kSpecifiedCenter) := by
    simp only [kTemplate, Fin.isValue, kSpecifiedCenter, fromRel_adj, ne_eq, Prod.mk.injEq, zero_ne_one, and_true,
      not_false_eq_true, kTemplateRelation, subdivisionRelation, and_self, or_true, one_ne_zero, or_self, or_false, root]
  have hhub (copy : Fin 2) :
      kTemplate.Reachable root (copy, kSpecifiedCenter) := by
    fin_cases copy
    · exact SimpleGraph.Reachable.refl root
    · exact hbridge.reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inl base)) := by
    have hfirst :
        kTemplate.Reachable root (copy, .inr (base, (0 : Fin 3))) := by
      exact (hhub copy).trans
        (by
          simpa only [kSpecifiedCenter, Fin.isValue] using (hcenterPair copy base 0).reachable)
    exact hfirst.trans (hbasePair copy base 0).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inr (base, center)) :=
    (hrootBase copy base).trans (hbasePair copy base center).reachable
  have hrootCenter (copy : Fin 2) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inr center)) :=
    (hrootPair copy 0 center).trans
      (hcenterPair copy 0 center).symm.reachable
  intro vertex
  rcases vertex with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · exact hrootBase copy base
  · exact hrootCenter copy center
  · exact hrootPair copy base center

lemma quotientGraph_connected_of_colorRespecting
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f)
    (hconnected : graph.Connected) :
    (quotientGraph graph f).Connected := by
  refine SimpleGraph.Connected.map
    (colorRespectingQuotientProjectionHom graph color hproper f hf)
    ?_ hconnected
  rintro ⟨_, ⟨v, rfl⟩⟩
  exact ⟨v, rfl⟩

lemma encodeFiniteGraph_connected
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hconnected : graph.Connected) :
    (encodeFiniteGraph graph).graph.Connected := by
  change (graph.map (Fintype.equivFin V).toEmbedding).Connected
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.Iso.map (Fintype.equivFin V) graph)).mp hconnected

lemma encodedJQuotient_connected {f : JVertex → JVertex}
    (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1 jTemplate_connected)

lemma encodedKQuotient_connected {f : KVertex → KVertex}
    (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1 kTemplate_connected)

theorem finiteCycle_connected {n : ℕ} (hn : 0 < n) :
    (finiteCycle n).graph.Connected := by
  change (SimpleGraph.cycleGraph n).Connected
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨SimpleGraph.cycleGraph_preconnected⟩

theorem proposedFamily_member_connected
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.Connected :=
  proposedFamily_induction (P := fun graph => graph.graph.Connected)
    (finiteCycle_connected (by norm_num : 0 < (4 : ℕ)))
    (finiteCycle_connected (by norm_num : 0 < (6 : ℕ)))
    (fun _ hf => encodedJQuotient_connected hf)
    (fun _ hf => encodedKQuotient_connected hf)
    forbidden hforbidden

end Connectedness

noncomputable section Bipartiteness

open Finset SimpleGraph

lemma colorRespectingQuotient_isBipartite
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by
  classical
  let representative : Set.range f → V :=
    fun vertex => Classical.choose vertex.property
  have hrepresentative (vertex : Set.range f) :
      f (representative vertex) = (vertex : V) :=
    Classical.choose_spec vertex.property
  let quotientColor : Set.range f → Bool :=
    fun vertex => color (representative vertex)
  have hdirected {u v : Set.range f}
      (h : quotientRelation graph f u v) :
      quotientColor u ≠ quotientColor v := by
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change color (representative u) ≠ color (representative v)
    intro heq
    apply hproper hxy
    calc
      color x = color (representative u) :=
        (hf (representative u) x
          ((hrepresentative u).trans hx.symm)).symm
      _ = color (representative v) := heq
      _ = color y :=
        hf (representative v) y
          ((hrepresentative v).trans hy.symm)
  have hcoloring : (quotientGraph graph f).Coloring Bool :=
    SimpleGraph.Coloring.mk quotientColor (by
      intro u v hadj
      change (SimpleGraph.fromRel (quotientRelation graph f)).Adj u v at hadj
      rcases
          (SimpleGraph.fromRel_adj (quotientRelation graph f) u v).mp hadj with
        ⟨_, hforward | hbackward⟩
      · exact hdirected hforward
      · exact Ne.symm (hdirected hbackward))
  simpa only [Fintype.card_bool] using hcoloring.colorable

lemma encodeFiniteGraph_isBipartite
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hbipartite : graph.IsBipartite) :
    (encodeFiniteGraph graph).graph.IsBipartite := by
  classical
  exact SimpleGraph.Colorable.map
    (Fintype.equivFin V).toEmbedding hbipartite

lemma encodedJQuotient_isBipartite
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1)

lemma encodedKQuotient_isBipartite
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1)

theorem proposedFamily_member_isBipartite
    {forbidden : FiniteGraph}
    (hforbidden : forbidden ∈ proposedFamily) :
    forbidden.graph.IsBipartite :=
  proposedFamily_induction (P := fun graph => graph.graph.IsBipartite)
    (SimpleGraph.cycleGraph.bicoloring_of_even 4 (by decide)).colorable
    (SimpleGraph.cycleGraph.bicoloring_of_even 6 (by decide)).colorable
    (fun _ hf => encodedJQuotient_isBipartite hf)
    (fun _ hf => encodedKQuotient_isBipartite hf)
    forbidden hforbidden

end Bipartiteness

noncomputable section FamilyExtremal

open Finset SimpleGraph

theorem finiteNatSup_sixteenth_power_le
    {α : Type*} (s : Finset α) (weight : α → ℕ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hweight : ∀ a ∈ s, (weight a : ℝ) ^ 16 ≤ bound) :
    ((s.sup weight : ℕ) : ℝ) ^ 16 ≤ bound := by
  classical
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst s
    simpa only [sup_empty, Nat.bot_eq_zero, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] using hbound
  · obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup s hs weight
    simpa only [hmax] using hweight a ha

theorem proposedFamily_familyExtremal_sixteenth_power_le (n : ℕ) :
    (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
  classical
  have hbound :
      0 ≤ compactnessHostPowerConstant * (n : ℝ) ^ 21 := by
    unfold compactnessHostPowerConstant compactnessDegreePowerConstant
    positivity
  unfold familyExtremal
  apply finiteNatSup_sixteenth_power_le
    (Finset.univ.filter (FamilyFree proposedFamily))
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)
    (compactnessHostPowerConstant * (n : ℝ) ^ 21) hbound
  intro host hhost
  exact proposedFamilyFree_sixteenth_power_host_bound n host
    (Finset.mem_filter.mp hhost).2

end FamilyExtremal

noncomputable section MainTheorem

open Finset SimpleGraph
open scoped Classical

noncomputable def compactnessSharpHostPowerConstant : ℝ :=
  compactnessHostPowerConstant

theorem compactnessSharpHostPowerConstant_pos :
    0 < compactnessSharpHostPowerConstant := by
  unfold compactnessSharpHostPowerConstant compactnessHostPowerConstant
    compactnessDegreePowerConstant
  positivity

theorem checkedManuscriptCounterexample :
    proposedFamily.Nonempty ∧
      (∀ forbidden ∈ proposedFamily,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      (0 : ℝ) < manuscriptLowerConstant ∧
      UniformMemberLower proposedFamily manuscriptLowerConstant ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree proposedFamily host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤
            compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal proposedFamily n : ℝ) ^ 16 ≤
          compactnessHostPowerConstant * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily proposedFamily ∧
      ¬ CompactnessConjectureStatement := by
  refine ⟨proposedFamily_nonempty, ?_,
    manuscriptLowerConstant_pos, proposedFamily_uniformMemberLower,
    proposedFamilyFree_sixteenth_power_host_bound,
    proposedFamily_familyExtremal_sixteenth_power_le,
    by norm_num, by norm_num,
    proposedFamily_not_compact, not_erdos_180⟩
  intro forbidden hforbidden
  exact ⟨proposedFamily_member_connected hforbidden,
    proposedFamily_member_isBipartite hforbidden,
    proposedFamily_isCyclic forbidden hforbidden⟩

theorem quantitativeCompactnessCounterexample :
    ∃ (family : Finset FiniteGraph) (c C : ℝ),
      family.Nonempty ∧
      (∀ forbidden ∈ family,
        forbidden.graph.Connected ∧ forbidden.graph.IsBipartite ∧
          ¬ forbidden.graph.IsAcyclic) ∧
      0 < c ∧
      0 < C ∧
      UniformMemberLower family c ∧
      (∀ (n : ℕ) (host : SimpleGraph (Fin n)),
        FamilyFree family host →
          (host.edgeFinset.card : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (∀ n : ℕ,
        (familyExtremal family n : ℝ) ^ 16 ≤ C * (n : ℝ) ^ 21) ∧
      (0 : ℝ) < 1 / 48 ∧
      (21 : ℝ) / 16 = (4 : ℝ) / 3 - 1 / 48 ∧
      ¬ IsCompactFamily family ∧
      ¬ CompactnessConjectureStatement := by
  obtain ⟨hnonempty, hgeometry, hlower_pos, hlower, hhost, hfamily,
    hgap_pos, hexponents, hnot_compact, hconjecture⟩ :=
    checkedManuscriptCounterexample
  refine ⟨proposedFamily, manuscriptLowerConstant,
    compactnessHostPowerConstant, hnonempty, hgeometry, hlower_pos, ?_,
    hlower, hhost, hfamily, hgap_pos, hexponents, hnot_compact,
    hconjecture⟩
  simpa only [compactnessSharpHostPowerConstant] using compactnessSharpHostPowerConstant_pos

end MainTheorem

end CompactnessConjecture
