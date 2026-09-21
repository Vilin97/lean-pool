/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.NBCMatroid
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace HsVirial

open Set
open SimpleGraph
open scoped BigOperators

/-!
  Concrete graph data for the NBC layer.

  Mathlib has the graph-side notion of a simple cycle, but it does not provide
  the graphic matroid.  This file therefore stops at the interface that can be
  proved without importing an unproved graphic-matroid construction: cycles
  are represented by finite edge sets of actual `Walk.IsCycle` witnesses, and
  the final bridge is conditional on a matroid's ground, spanning, and circuit
  presentations.
 -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Finite edge and cycle sets -/

noncomputable def graphEdgeFinset (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ G.edgeSet)

omit [DecidableEq V] in
@[simp]
lemma mem_graphEdgeFinset {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdgeFinset G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdgeFinset]

omit [DecidableEq V] in
@[simp, norm_cast]
lemma coe_graphEdgeFinset (G : SimpleGraph V) :
    (graphEdgeFinset G : Set (Sym2 V)) = G.edgeSet := by
  ext e
  simp

def cycleEdgeFinset {G : SimpleGraph V} {v : V} (c : G.Walk v v) : Finset (Sym2 V) :=
  c.edges.toFinset

omit [Fintype V] in
@[simp]
lemma mem_cycleEdgeFinset {G : SimpleGraph V} {v : V} {c : G.Walk v v} {e : Sym2 V} :
    e ∈ cycleEdgeFinset c ↔ e ∈ c.edges := by
  simp [cycleEdgeFinset]

lemma walkEdgeFinset_subset_graphEdgeFinset {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} :
    cycleEdgeFinset c ⊆ graphEdgeFinset G := by
  intro e he
  apply mem_graphEdgeFinset.mpr
  apply c.edges_subset_edgeSet
  simpa [cycleEdgeFinset] using he

omit [Fintype V] in
lemma cycleEdgeFinset_card {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) : (cycleEdgeFinset c).card = c.length := by
  have hcard : c.edges.toFinset.card = c.edges.length :=
    List.toFinset_card_of_nodup hc.isTrail.edges_nodup
  simpa [cycleEdgeFinset, Walk.length_edges] using hcard

omit [Fintype V] in
lemma cycleEdgeFinset_nonempty {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) : (cycleEdgeFinset c).Nonempty := by
  change c.edges.toFinset.Nonempty
  rw [List.toFinset_nonempty_iff]
  exact Walk.edges_eq_nil.not.mpr hc.not_nil

/-!
  `IsGraphCycle` is deliberately an edge-set predicate rather than a predicate
  on a chosen walk.  Different orientations or starting points of one cycle
  consequently describe the same circuit candidate.
 -/
def IsGraphCycle (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ C = cycleEdgeFinset c

omit [Fintype V] in
lemma IsGraphCycle.nonempty {G : SimpleGraph V} {C : Finset (Sym2 V)}
    (hC : IsGraphCycle G C) : C.Nonempty := by
  rcases hC with ⟨v, c, hc, rfl⟩
  exact cycleEdgeFinset_nonempty hc

lemma IsGraphCycle.subset_ground {G : SimpleGraph V} {C : Finset (Sym2 V)}
    (hC : IsGraphCycle G C) : C ⊆ graphEdgeFinset G := by
  rcases hC with ⟨v, c, hc, rfl⟩
  exact walkEdgeFinset_subset_graphEdgeFinset

/-! ### Broken circuits and graph-side candidates -/

variable [LinearOrder (Sym2 V)]

/- The direct `Sym2` order is only partial.  These relations make every
   graph-side comparison use the supplied linear edge order, just as the
   generic NBC definitions do. -/
def graphEdgeLE (a b : Sym2 V) : Prop :=
  @LE.le (Sym2 V)
    ((inferInstance : LinearOrder (Sym2 V)).toPartialOrder.toPreorder.toLE) a b

def graphEdgeLT (a b : Sym2 V) : Prop :=
  @LT.lt (Sym2 V)
    ((inferInstance : LinearOrder (Sym2 V)).toPartialOrder.toPreorder.toLT) a b

omit [Fintype V] [DecidableEq V] in
lemma graphEdgeLT_iff {a b : Sym2 V} :
    graphEdgeLT a b ↔ graphEdgeLE a b ∧ ¬graphEdgeLE b a := by
  simpa [graphEdgeLE, graphEdgeLT] using
    ((inferInstance : LinearOrder (Sym2 V)).toPartialOrder.toPreorder.lt_iff_le_not_ge a b)

omit [Fintype V] [DecidableEq V] in
lemma graphEdgeLT_not_graphEdgeLE {a b : Sym2 V} (h : graphEdgeLT a b) :
    ¬graphEdgeLE b a := by
  exact (graphEdgeLT_iff.mp h).2

def IsGraphBrokenCircuit (G : SimpleGraph V) (B : Finset (Sym2 V)) : Prop :=
  ∃ (C : Finset (Sym2 V)) (e : Sym2 V),
    IsGraphCycle G C ∧ e ∈ C ∧ (∀ f ∈ C, graphEdgeLE f e) ∧ B = C.erase e

lemma IsGraphBrokenCircuit.subset_ground {G : SimpleGraph V} {B : Finset (Sym2 V)}
    (hB : IsGraphBrokenCircuit G B) : B ⊆ graphEdgeFinset G := by
  rcases hB with ⟨C, e, hC, heC, hmax, rfl⟩
  intro f hf
  exact hC.subset_ground (Finset.mem_of_mem_erase hf)

def IsGraphNBCandidate (G : SimpleGraph V) (A : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ (C : Finset (Sym2 V)),
    IsGraphCycle G C ∧
    e ∈ C ∧
    (∀ f ∈ C, graphEdgeLE f e) ∧
    ((C.erase e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ (A : Set (Sym2 V))

lemma graphNBCandidate_mem_ground {G : SimpleGraph V} {A : Finset (Sym2 V)} {e : Sym2 V}
    (h : IsGraphNBCandidate G A e) : e ∈ graphEdgeFinset G := by
  rcases h with ⟨C, hC, heC, _, _⟩
  exact hC.subset_ground heC

omit [Fintype V] in
lemma graphNBCandidate_has_brokenCircuit {G : SimpleGraph V} {A : Finset (Sym2 V)}
    {e : Sym2 V} (h : IsGraphNBCandidate G A e) :
    ∃ B : Finset (Sym2 V),
      IsGraphBrokenCircuit G B ∧ (B : Set (Sym2 V)) ⊆ (A : Set (Sym2 V)) := by
  rcases h with ⟨C, hC, heC, hmax, hsub⟩
  refine ⟨C.erase e, ?_, hsub⟩
  exact ⟨C, e, hC, heC, hmax, rfl⟩

omit [Fintype V] in
lemma graphBrokenCircuit_subset_isGraphNBCandidate
    {G : SimpleGraph V} {A B : Finset (Sym2 V)}
    (hB : IsGraphBrokenCircuit G B)
    (hBA : (B : Set (Sym2 V)) ⊆ (A : Set (Sym2 V))) :
    ∃ e, IsGraphNBCandidate G A e := by
  rcases hB with ⟨C, e, hC, heC, hmax, rfl⟩
  exact ⟨e, ⟨C, hC, heC, hmax, hBA⟩⟩

omit [Fintype V] in
lemma exists_graphNBCandidate_iff_exists_graphBrokenCircuit
    {G : SimpleGraph V} {A : Finset (Sym2 V)} :
    (∃ e, IsGraphNBCandidate G A e) ↔
      ∃ B, IsGraphBrokenCircuit G B ∧
        (B : Set (Sym2 V)) ⊆ (A : Set (Sym2 V)) := by
  constructor
  · rintro ⟨e, h⟩
    exact graphNBCandidate_has_brokenCircuit h
  · rintro ⟨B, hB, hBA⟩
    exact graphBrokenCircuit_subset_isGraphNBCandidate hB hBA

omit [Fintype V] in
lemma graphNBCandidate_toggleEdge {G : SimpleGraph V} {A : Finset (Sym2 V)} {e : Sym2 V}
    (h : IsGraphNBCandidate G A e) :
    IsGraphNBCandidate G (toggleEdge A e) e := by
  rcases h with ⟨C, hC, heC, hmax, hsub⟩
  refine ⟨C, hC, heC, hmax, ?_⟩
  intro x hx
  have hxA : x ∈ A := hsub hx
  have hxe : x ≠ e := by
    intro hxe
    subst x
    exact (Finset.ne_of_mem_erase hx) rfl
  by_cases heA : e ∈ A
  · simp [toggleEdge, heA, hxe, hxA]
  · simp [toggleEdge, heA, hxA]

omit [Fintype V] in
lemma graphNBCandidate_smaller_toggle_iff {G : SimpleGraph V} {A : Finset (Sym2 V)}
    {e f : Sym2 V} (hfe : graphEdgeLT f e) :
    IsGraphNBCandidate G (toggleEdge A e) f ↔ IsGraphNBCandidate G A f := by
  constructor
  · intro h
    rcases h with ⟨C, hC, hfC, hmax, hsub⟩
    refine ⟨C, hC, hfC, hmax, ?_⟩
    intro x hx
    have hxe : x ≠ e := by
      intro hxe
      subst x
      have heC : e ∈ C := Finset.mem_of_mem_erase hx
      have hle : graphEdgeLE e f := hmax e heC
      exact (graphEdgeLT_not_graphEdgeLE hfe) hle
    have hxt : x ∈ toggleEdge A e := hsub hx
    by_cases heA : e ∈ A
    · simpa [toggleEdge, heA, hxe] using hxt
    · rcases (by simpa [toggleEdge, heA] using hxt) with hxeq | hxa
      · exact (False.elim (hxe hxeq))
      · exact hxa
  · intro h
    rcases h with ⟨C, hC, hfC, hmax, hsub⟩
    refine ⟨C, hC, hfC, hmax, ?_⟩
    intro x hx
    have hxA : x ∈ A := hsub hx
    have hxe : x ≠ e := by
      intro hxe
      subst x
      have heC : e ∈ C := Finset.mem_of_mem_erase hx
      have hle : graphEdgeLE e f := hmax e heC
      exact (graphEdgeLT_not_graphEdgeLE hfe) hle
    by_cases heA : e ∈ A
    · simp [toggleEdge, heA, hxe, hxA]
    · simp [toggleEdge, heA, hxA]

/-!
  These are explicit interface theorems, not a proposed graphic-matroid
  definition: the graph predicates above remain concrete while the matroid
  construction is developed separately.
 -/
omit [Fintype V] in
lemma isNBCandidate_iff_graphCycle_circuits
    {G : SimpleGraph V} {M : Matroid (Sym2 V)} {A : Finset (Sym2 V)} {e : Sym2 V}
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C) :
    IsNBCandidate M A e ↔ IsGraphNBCandidate G A e := by
  simp only [IsNBCandidate, IsGraphNBCandidate]
  simp_rw [hcircuits]
  rfl

lemma mem_nbcCandidates_iff_graphCycle_circuits
    {G : SimpleGraph V} {M : Matroid (Sym2 V)} {A : Finset (Sym2 V)} {e : Sym2 V}
    (hground : M.E = G.edgeSet)
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C) :
    e ∈ nbcCandidates M A ↔
      e ∈ graphEdgeFinset G ∧ IsGraphNBCandidate G A e := by
  rw [mem_nbcCandidates, mem_matroidGround, hground, mem_graphEdgeFinset,
    isNBCandidate_iff_graphCycle_circuits hcircuits]

omit [Fintype V] in
lemma generic_candidate_toggle_of_graphCycle_circuits
    {G : SimpleGraph V} {M : Matroid (Sym2 V)} {A : Finset (Sym2 V)} {e : Sym2 V}
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C)
    (h : IsGraphNBCandidate G A e) :
    IsNBCandidate M (toggleEdge A e) e := by
  exact (isNBCandidate_iff_graphCycle_circuits hcircuits).2
    (graphNBCandidate_toggleEdge h)

lemma graph_nbcBad_iff_generic_nbcBad
    {G : SimpleGraph V} {M : Matroid (Sym2 V)} {A : Finset (Sym2 V)}
    (hground : M.E = G.edgeSet)
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C) :
    IsNBCBad M A ↔ ∃ e, IsGraphNBCandidate G A e := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, (mem_nbcCandidates_iff_graphCycle_circuits hground hcircuits).mp he |>.2⟩
  · rintro ⟨e, he⟩
    exact ⟨e, (mem_nbcCandidates_iff_graphCycle_circuits hground hcircuits).mpr
      ⟨graphNBCandidate_mem_ground he, he⟩⟩

omit [Fintype V] in
lemma graph_candidate_toggle_of_generic
    {G : SimpleGraph V} {M : Matroid (Sym2 V)} {A : Finset (Sym2 V)} {e : Sym2 V}
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C)
    (h : IsNBCandidate M A e) :
    IsGraphNBCandidate G (toggleEdge A e) e := by
  apply (isNBCandidate_iff_graphCycle_circuits hcircuits).1
  exact candidate_toggleEdge h

/-! ### Graph-side signed cancellation -/

def IsGraphSpanning (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Reachable = G.Reachable

def IsGraphNBCBad (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  ∃ e, IsGraphNBCandidate G A e

noncomputable def graphSpanningSubsets (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (graphEdgeFinset G).powerset.filter (IsGraphSpanning G)

noncomputable def graphNBCSpanningSubsets (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (graphSpanningSubsets G).filter (fun A => ¬IsGraphNBCBad G A)

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma graph_spanning_finset_eq_matroid_ground
    {G : SimpleGraph V} {M : Matroid (Sym2 V)}
    (hground : M.E = G.edgeSet) :
    matroidGround M = graphEdgeFinset G := by
  ext e
  rw [mem_matroidGround, mem_graphEdgeFinset, hground]

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma spanningSubsets_eq_graphSpanningSubsets
    {G : SimpleGraph V} {M : Matroid (Sym2 V)}
    (hground : M.E = G.edgeSet)
    (hspanning : ∀ (A : Finset (Sym2 V)),
      A ⊆ graphEdgeFinset G →
        (M.Spanning (A : Set (Sym2 V)) ↔ IsGraphSpanning G A)) :
    spanningSubsets M = graphSpanningSubsets G := by
  classical
  have hground_finset : matroidGround M = graphEdgeFinset G :=
    graph_spanning_finset_eq_matroid_ground hground
  ext A
  simp only [spanningSubsets, graphSpanningSubsets, Finset.mem_filter,
    Finset.mem_powerset]
  rw [hground_finset]
  constructor
  · rintro ⟨hA, hspan⟩
    have hiff := hspanning A hA
    exact ⟨hA, hiff.mp hspan⟩
  · rintro ⟨hA, hspan⟩
    have hiff := hspanning A hA
    exact ⟨hA, hiff.mpr hspan⟩

lemma nbcBaseSubsets_eq_graphNBCSpanningSubsets
    {G : SimpleGraph V} {M : Matroid (Sym2 V)}
    (hground : M.E = G.edgeSet)
    (hspanning : ∀ (A : Finset (Sym2 V)),
      A ⊆ graphEdgeFinset G →
        (M.Spanning (A : Set (Sym2 V)) ↔ IsGraphSpanning G A))
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C) :
    nbcBaseSubsets M = graphNBCSpanningSubsets G := by
  classical
  have hspan := spanningSubsets_eq_graphSpanningSubsets hground hspanning
  ext A
  rw [nbcBaseSubsets, graphNBCSpanningSubsets]
  simp only [Finset.mem_filter]
  rw [hspan]
  rw [graph_nbcBad_iff_generic_nbcBad hground hcircuits]
  simp [IsGraphNBCBad]

theorem graph_signed_spanning_eq_graph_signed_nbc
    {G : SimpleGraph V} {M : Matroid (Sym2 V)}
    (hground : M.E = G.edgeSet)
    (hspanning : ∀ (A : Finset (Sym2 V)),
      A ⊆ graphEdgeFinset G →
        (M.Spanning (A : Set (Sym2 V)) ↔ IsGraphSpanning G A))
    (hcircuits : ∀ C : Finset (Sym2 V),
      M.IsCircuit (C : Set (Sym2 V)) ↔ IsGraphCycle G C) :
    (∑ A ∈ graphSpanningSubsets G, matroidParitySign A.card) =
      ∑ A ∈ graphNBCSpanningSubsets G, matroidParitySign A.card := by
  rw [← spanningSubsets_eq_graphSpanningSubsets hground hspanning]
  rw [← nbcBaseSubsets_eq_graphNBCSpanningSubsets hground hspanning hcircuits]
  exact signed_spanning_eq_signed_nbc M

end HsVirial
