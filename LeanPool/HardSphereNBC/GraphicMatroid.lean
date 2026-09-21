/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.NBCGraph
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# GraphicMatroid

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

namespace HsVirial

open Set
open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- The finite edge set of a connected component. -/
def componentEdgeFinset {H : SimpleGraph V}
    (c : H.ConnectedComponent) : Finset (Sym2 c) :=
  (Set.toFinite c.toSimpleGraph.edgeSet).toFinset

omit [DecidableEq V] in
@[simp]
lemma mem_componentEdgeFinset {H : SimpleGraph V} {c : H.ConnectedComponent}
    {e : Sym2 c} : e ∈ componentEdgeFinset c ↔ e ∈ c.toSimpleGraph.edgeSet := by
  simp [componentEdgeFinset]

/-- The inclusion of unordered pairs from a vertex subset into the ambient vertex set. -/
def sym2SubtypeEmbedding {S : Set V} : Sym2 S ↪ Sym2 V where
  toFun := Sym2.map (fun x : S => (x : V))
  inj' := Sym2.map.injective Subtype.val_injective

omit [Fintype V] [DecidableEq V] in
lemma component_edge_map_mem {H : SimpleGraph V} {c : H.ConnectedComponent}
    {e : Sym2 c} (he : e ∈ c.toSimpleGraph.edgeSet) :
    sym2SubtypeEmbedding (S := c.supp) e ∈ H.edgeSet := by
  induction e using Sym2.ind with
  | h a b =>
    change s((a : V), (b : V)) ∈ H.edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact (ConnectedComponent.toSimpleGraph_adj c a.property b.property).mp
      (by simpa only [SimpleGraph.mem_edgeSet] using he)

lemma component_edge_card_bij (H : SimpleGraph V) [DecidableRel H.Adj] :
    (graphEdgeFinset H).card =
      ∑ c : H.ConnectedComponent, (componentEdgeFinset c).card := by
  classical
  rw [← Finset.card_sigma]
  apply Eq.symm
  apply Finset.card_bij
      (fun x _ => sym2SubtypeEmbedding (S := x.1.supp) x.2)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨_, hxedge⟩
    exact mem_graphEdgeFinset.mpr (component_edge_map_mem (mem_componentEdgeFinset.mp hxedge))
  · intro x hx y hy hxy
    rcases x with ⟨cx, ex⟩
    rcases y with ⟨cy, ey⟩
    have hex : ex ∈ componentEdgeFinset cx := (Finset.mem_sigma.mp hx).2
    have hey : ey ∈ componentEdgeFinset cy := (Finset.mem_sigma.mp hy).2
    induction ex using Sym2.ind with
    | h a b =>
      induction ey using Sym2.ind with
      | h c d =>
        simp only [sym2SubtypeEmbedding] at hxy
        have hcomp : cx = cy := by
          rcases (Sym2.eq_iff.mp hxy) with h | h
          · have hac : (a : V) = (c : V) := by simpa using h.1
            exact ConnectedComponent.eq_of_common_vertex a.property (hac ▸ c.property)
          · have had : (a : V) = (d : V) := by simpa using h.1
            exact ConnectedComponent.eq_of_common_vertex a.property (had ▸ d.property)
        subst cy
        apply Sigma.ext
        · rfl
        apply heq_of_eq
        exact (sym2SubtypeEmbedding (S := cx.supp)).injective hxy
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : H.Adj a b := (H.mem_edgeSet).mp (mem_graphEdgeFinset.mp he)
      let c := H.connectedComponentMk a
      have ha : a ∈ c := ConnectedComponent.connectedComponentMk_mem
      have hb : b ∈ c := by
        apply (ConnectedComponent.mem_supp_iff c b).2
        exact ConnectedComponent.sound hab.reachable.symm
      let e' : Sym2 c := s(⟨a, ha⟩, ⟨b, hb⟩)
      refine ⟨⟨c, e'⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
        exact mem_componentEdgeFinset.mpr ((ConnectedComponent.toSimpleGraph_adj c ha hb).2 hab)
      · rfl

omit [DecidableEq V] in
lemma component_edge_card_add_one (H : SimpleGraph V)
    (hH : H.IsAcyclic) (c : H.ConnectedComponent) :
    (componentEdgeFinset c).card + 1 = Nat.card c := by
  let : Fintype c := Fintype.ofFinite c
  let : Fintype c.toSimpleGraph.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  rw [componentEdgeFinset, Set.Finite.card_toFinset]
  simpa only [SimpleGraph.edgeFinset_card] using
    (hH.isTree_connectedComponent c).card_edgeFinset

lemma componentVerts_card (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∑ c : H.ConnectedComponent, Nat.card c = Fintype.card V := by
  let e : (Σ c : H.ConnectedComponent, c) ≃ V :=
    Equiv.sigmaFiberEquiv H.connectedComponentMk
  rw [← Nat.card_sigma, Nat.card_congr e]
  simp

lemma forest_edge_formula (H : SimpleGraph V) [DecidableRel H.Adj] (hH : H.IsAcyclic) :
    (graphEdgeFinset H).card + Fintype.card H.ConnectedComponent = Fintype.card V := by
  have hplus : ∀ c : H.ConnectedComponent,
      (componentEdgeFinset c).card + 1 = Nat.card c :=
    fun c => component_edge_card_add_one H hH c
  calc
    (graphEdgeFinset H).card + Fintype.card H.ConnectedComponent =
        (∑ c : H.ConnectedComponent, (componentEdgeFinset c).card) +
          ∑ _c : H.ConnectedComponent, 1 := by
      rw [component_edge_card_bij H]
      simp
    _ = ∑ c : H.ConnectedComponent, ((componentEdgeFinset c).card + 1) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ c : H.ConnectedComponent, Nat.card c := by
      simp_rw [hplus]
    _ = Fintype.card V := componentVerts_card H

/-- An edge subset of the graph whose induced graph is acyclic. -/
def IsGraphForest (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  (A : Set (Sym2 V)) ⊆ G.edgeSet ∧
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).IsAcyclic

/-- A nonforest edge subset that becomes a forest after deleting any edge. -/
def IsGraphCircuit (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  C ⊆ graphEdgeFinset G ∧
    ¬IsGraphForest G C ∧
      ∀ e ∈ C, IsGraphForest G (C.erase e)

omit [Fintype V] [DecidableEq V] in
lemma edgeSet_fromEdgeSet_of_subset {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).edgeSet = (A : Set (Sym2 V)) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  apply Set.Subset.antisymm
  · exact Set.sdiff_subset
  · intro e he
    exact ⟨he, G.not_isDiag_of_mem_edgeSet (hA he)⟩

omit [DecidableEq V] in
lemma graphEdgeFinset_fromEdgeSet {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    graphEdgeFinset (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))) = A := by
  apply Finset.coe_injective
  rw [coe_graphEdgeFinset, edgeSet_fromEdgeSet_of_subset hA]

omit [DecidableEq V] in
lemma graphEdgeFinset_fromEdgeSet_card {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : (A : Set (Sym2 V)) ⊆ G.edgeSet) :
    (graphEdgeFinset (SimpleGraph.fromEdgeSet (A : Set (Sym2 V)))).card = A.card := by
  rw [graphEdgeFinset_fromEdgeSet hA]

omit [Fintype V] [DecidableEq V] in
lemma IsGraphForest.empty (G : SimpleGraph V) : IsGraphForest G ∅ := by
  simp [IsGraphForest]

omit [Fintype V] [DecidableEq V] in
lemma IsGraphForest.subset {G : SimpleGraph V} {A B : Finset (Sym2 V)}
    (hB : IsGraphForest G B) (hAB : A ⊆ B) : IsGraphForest G A := by
  refine ⟨(Finset.coe_subset.2 hAB).trans hB.1, ?_⟩
  apply hB.2.anti
  exact SimpleGraph.fromEdgeSet_mono (by simpa using hAB)

omit [Fintype V] in
lemma IsGraphForest.insert_of_mem_forest {G F : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : IsGraphForest G A) (hAF : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ F)
    (hF : F.IsAcyclic) (e : Sym2 V) (heF : e ∈ F.edgeSet)
    (heG : e ∈ G.edgeSet) (heA : e ∉ A) :
    IsGraphForest G (insert e A) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact heG
    · exact hA.1 hx
  · apply hF.anti
    apply (SimpleGraph.fromEdgeSet_le F).mpr
    intro x hx
    rcases hx with ⟨hx, _⟩
    by_cases hxe : x = e
    · subst x
      exact heF
    · have hxA : x ∈ A := by simpa [Finset.mem_insert, hxe] using hx
      exact SimpleGraph.edgeSet_mono hAF (by
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨by simpa [hxe] using hxA, G.not_isDiag_of_mem_edgeSet (hA.1 hxA)⟩)

/-- Identification of components for graphs with the same reachability relation. -/
def connectedComponentEquivOfReachableEq {G H : SimpleGraph V}
    (h : G.Reachable = H.Reachable) :
    G.ConnectedComponent ≃ H.ConnectedComponent where
  toFun c := ConnectedComponent.lift (fun v => H.connectedComponentMk v)
    (fun _ _ p _ => ConnectedComponent.sound (h ▸ p.reachable)) c
  invFun c := ConnectedComponent.lift (fun v => G.connectedComponentMk v)
    (fun _ _ p _ => ConnectedComponent.sound (h.symm ▸ p.reachable)) c
  left_inv c := c.ind (fun _ => rfl)
  right_inv c := c.ind (fun _ => rfl)

lemma connectedComponent_card_eq_of_reachable_eq {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G.Reachable = H.Reachable) :
    Fintype.card G.ConnectedComponent = Fintype.card H.ConnectedComponent := by
  exact Fintype.card_congr (connectedComponentEquivOfReachableEq h)

omit [DecidableEq V] in
lemma finset_subset_graphEdgeFinset_of_fromEdgeSet_le
    {G F : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : IsGraphForest G A)
    (hAF : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ F) :
    A ⊆ graphEdgeFinset F := by
  intro e he
  apply mem_graphEdgeFinset.mpr
  apply SimpleGraph.edgeSet_mono hAF
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨by simpa using he, G.not_isDiag_of_mem_edgeSet (hA.1 he)⟩

lemma graphEdgeFinset_subset_of_le_fromEdgeSet_union
    {F : SimpleGraph V} {A B : Finset (Sym2 V)}
    (hF : F ≤ SimpleGraph.fromEdgeSet ((A ∪ B : Finset (Sym2 V)) : Set (Sym2 V))) :
    graphEdgeFinset F ⊆ A ∪ B := by
  intro e he
  have he' := SimpleGraph.edgeSet_mono hF (mem_graphEdgeFinset.mp he)
  rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
  simpa only [Finset.mem_union, Finset.mem_coe] using he'.1

omit [DecidableEq V] in
lemma graphEdgeFinset_card_eq_of_reachable_eq {F H : SimpleGraph V}
    (hF : F.IsAcyclic) (hH : H.IsAcyclic)
    (hreach : F.Reachable = H.Reachable) :
    (graphEdgeFinset F).card = (graphEdgeFinset H).card := by
  classical
  have hFcard := forest_edge_formula F hF
  have hHcard := forest_edge_formula H hH
  have hcomp := connectedComponent_card_eq_of_reachable_eq hreach
  omega

omit [Fintype V] in
lemma IsGraphForest.augment [Finite V] {G : SimpleGraph V} {I J : Finset (Sym2 V)}
    (hI : IsGraphForest G I) (hJ : IsGraphForest G J) (hcard : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ IsGraphForest G (insert e I) := by
  classical
  let := Fintype.ofFinite V
  let GI := SimpleGraph.fromEdgeSet (I : Set (Sym2 V))
  let GJ := SimpleGraph.fromEdgeSet (J : Set (Sym2 V))
  let K := SimpleGraph.fromEdgeSet ((I ∪ J : Finset (Sym2 V)) : Set (Sym2 V))
  have hIleK : GI ≤ K := by
    apply SimpleGraph.fromEdgeSet_mono
    intro e he
    simpa only [Finset.mem_union, Finset.mem_coe] using Or.inl he
  have hJleK : GJ ≤ K := by
    apply SimpleGraph.fromEdgeSet_mono
    intro e he
    simpa only [Finset.mem_union, Finset.mem_coe] using Or.inr he
  obtain ⟨F, hIF, hFK, hFacyc, hFreach⟩ :=
    K.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hIleK hI.2
  obtain ⟨L, hJL, hLK, hLacyc, hLreach⟩ :=
    K.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hJleK hJ.2
  have hFL : F.Reachable = L.Reachable := hFreach.trans hLreach.symm
  have hFLcard := graphEdgeFinset_card_eq_of_reachable_eq hFacyc hLacyc hFL
  have hIedge : I ⊆ graphEdgeFinset F :=
    finset_subset_graphEdgeFinset_of_fromEdgeSet_le hI hIF
  have hJedge : J ⊆ graphEdgeFinset L :=
    finset_subset_graphEdgeFinset_of_fromEdgeSet_le hJ hJL
  have hFedge : graphEdgeFinset F ⊆ I ∪ J :=
    graphEdgeFinset_subset_of_le_fromEdgeSet_union hFK
  have hFcard_gt : I.card < (graphEdgeFinset F).card := by
    have hIcard_le : I.card ≤ (graphEdgeFinset F).card :=
      Finset.card_le_card hIedge
    by_contra hnot
    have hFle : (graphEdgeFinset F).card ≤ I.card := le_of_not_gt hnot
    have hFeq : graphEdgeFinset F = I :=
      (Finset.eq_of_subset_of_card_le hIedge hFle).symm
    have hJcard_le : J.card ≤ (graphEdgeFinset L).card :=
      Finset.card_le_card hJedge
    have hJcard_le_I : J.card ≤ I.card := by
      calc
        J.card ≤ (graphEdgeFinset L).card := hJcard_le
        _ = (graphEdgeFinset F).card := hFLcard.symm
        _ = I.card := by rw [hFeq]
    exact (Nat.not_lt_of_ge hJcard_le_I) hcard
  obtain ⟨e, heF, heI⟩ := Finset.exists_mem_notMem_of_card_lt_card hFcard_gt
  have heJ : e ∈ J := by
    rcases Finset.mem_union.mp (hFedge heF) with heI' | heJ
    · exact (heI heI').elim
    · exact heJ
  have hKleG : K ≤ G := by
    apply (SimpleGraph.fromEdgeSet_le G).mpr
    intro e he
    rcases he with ⟨heIJ, _⟩
    rcases (by simpa only [Finset.mem_union, Finset.mem_coe] using heIJ) with heI' | heJ'
    · exact hI.1 heI'
    · exact hJ.1 heJ'
  have heG : e ∈ G.edgeSet :=
    SimpleGraph.edgeSet_mono hKleG
      (SimpleGraph.edgeSet_mono hFK (mem_graphEdgeFinset.mp heF))
  refine ⟨e, heJ, heI, ?_⟩
  exact IsGraphForest.insert_of_mem_forest hI hIF hFacyc e
    (mem_graphEdgeFinset.mp heF) heG heI

/-- The matroid whose independent edge sets are the forests of the graph. -/
def graphicMatroid (G : SimpleGraph V) : Matroid (Sym2 V) :=
  (IndepMatroid.ofFinset
    (E := G.edgeSet)
    (Indep := IsGraphForest G)
    (indep_empty := IsGraphForest.empty G)
    (indep_subset := by
      intro I J hJ hIJ
      exact IsGraphForest.subset hJ hIJ)
    (indep_aug := by
      intro I J hI hJ hcard
      exact IsGraphForest.augment hI hJ hcard)
    (subset_ground := by
      intro I hI
      exact hI.1)).matroid

@[simp]
lemma graphicMatroid_ground (G : SimpleGraph V) :
    (graphicMatroid G).E = G.edgeSet := by
  simp [graphicMatroid]

lemma graphicMatroid_indep_finset {G : SimpleGraph V} {A : Finset (Sym2 V)} :
    (graphicMatroid G).Indep (A : Set (Sym2 V)) ↔ IsGraphForest G A := by
  simp [graphicMatroid]

lemma graphicMatroid_isCircuit_iff_graphCircuit
    {G : SimpleGraph V} {C : Finset (Sym2 V)} :
    (graphicMatroid G).IsCircuit (C : Set (Sym2 V)) ↔
      IsGraphCircuit G C := by
  classical
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  constructor
  · rintro ⟨hdep, hind⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      have heM : e ∈ (graphicMatroid G).E :=
        hdep.subset_ground (by simpa using he)
      simpa [graphicMatroid_ground] using heM
    · intro hforest
      exact hdep.not_indep ((graphicMatroid_indep_finset).mpr hforest)
    · intro e he
      apply (graphicMatroid_indep_finset).mp
      simpa only [Finset.coe_erase] using hind e (by simpa using he)
  · rintro ⟨hCground, hdep, hmin⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro hI
        exact hdep ((graphicMatroid_indep_finset).mp hI)
      · intro x hx
        have hxG : x ∈ G.edgeSet :=
          mem_graphEdgeFinset.mp (hCground (by simpa using hx))
        simpa [graphicMatroid_ground] using hxG
    · intro e he
      have hi : (graphicMatroid G).Indep
          ((C.erase e : Finset (Sym2 V)) : Set (Sym2 V)) :=
        (graphicMatroid_indep_finset).mpr (hmin e he)
      simpa only [Finset.coe_erase] using hi

omit [Fintype V] [DecidableEq V] in
lemma fromEdgeSet_le_of_graphForest {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : IsGraphForest G A) :
    SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ G := by
  apply (SimpleGraph.fromEdgeSet_le G).mpr
  intro e he
  exact hA.1 he.1

lemma graphicMatroid_isBase_iff_reachable_eq
    {G : SimpleGraph V} {B : Finset (Sym2 V)}
    (hB : IsGraphForest G B) :
    (graphicMatroid G).IsBase (B : Set (Sym2 V)) ↔
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable = G.Reachable := by
  classical
  constructor
  · intro hBbase
    apply (SimpleGraph.maximal_isAcyclic_iff_reachable_eq
      (fromEdgeSet_le_of_graphForest hB) hB.2).mp
    rw [maximal_iff]
    refine ⟨⟨fromEdgeSet_le_of_graphForest hB, hB.2⟩, ?_⟩
    intro H hH hBH
    have hHedge : graphEdgeFinset H ⊆ graphEdgeFinset G := by
      intro e he
      apply mem_graphEdgeFinset.mpr
      exact SimpleGraph.edgeSet_mono hH.1 (mem_graphEdgeFinset.mp he)
    have hHforest : IsGraphForest G (graphEdgeFinset H) := by
      refine ⟨?_, ?_⟩
      · intro e he
        exact SimpleGraph.edgeSet_mono hH.1 (mem_graphEdgeFinset.mp he)
      · rw [show SimpleGraph.fromEdgeSet (graphEdgeFinset H : Set (Sym2 V)) = H by
          rw [coe_graphEdgeFinset]
          exact SimpleGraph.fromEdgeSet_edgeSet H]
        exact hH.2
    have hBsubH : B ⊆ graphEdgeFinset H :=
      finset_subset_graphEdgeFinset_of_fromEdgeSet_le hB hBH
    have hHind : (graphicMatroid G).Indep
        (graphEdgeFinset H : Set (Sym2 V)) :=
      (graphicMatroid_indep_finset).mpr hHforest
    have hmax := (maximal_subset_iff.mp
      (Matroid.isBase_iff_maximal_indep.mp hBbase)).2
    have hsetEq : (B : Set (Sym2 V)) =
        (graphEdgeFinset H : Set (Sym2 V)) :=
      hmax hHind (Finset.coe_subset.mpr hBsubH)
    apply SimpleGraph.edgeSet_inj.mp
    rw [edgeSet_fromEdgeSet_of_subset hB.1, ← coe_graphEdgeFinset H]
    exact hsetEq
  · intro hreach
    rw [Matroid.isBase_iff_maximal_indep, maximal_subset_iff]
    refine ⟨(graphicMatroid_indep_finset).mpr hB, ?_⟩
    intro I hI hBI
    let IF : Finset (Sym2 V) := (Set.toFinite I).toFinset
    have hIF : (IF : Set (Sym2 V)) = I := by
      exact (Set.toFinite I).coe_toFinset
    have hIForest : IsGraphForest G IF := by
      apply (graphicMatroid_indep_finset).mp
      rw [hIF]
      exact hI
    have hBsubIF : B ⊆ IF := by
      intro e he
      apply (Set.toFinite I).mem_toFinset.mpr
      exact hBI (by simpa using he)
    have hIFleG : SimpleGraph.fromEdgeSet (IF : Set (Sym2 V)) ≤ G :=
      fromEdgeSet_le_of_graphForest hIForest
    have hBgraph : SimpleGraph.fromEdgeSet (B : Set (Sym2 V)) ≤
        SimpleGraph.fromEdgeSet (IF : Set (Sym2 V)) := by
      apply SimpleGraph.fromEdgeSet_mono
      intro e he
      exact hBsubIF (by simpa using he)
    have hmax := (SimpleGraph.maximal_isAcyclic_iff_reachable_eq
      (fromEdgeSet_le_of_graphForest hB) hB.2).mpr hreach
    have hgraphEq : SimpleGraph.fromEdgeSet (B : Set (Sym2 V)) =
        SimpleGraph.fromEdgeSet (IF : Set (Sym2 V)) :=
      (maximal_iff.mp hmax).2 ⟨hIFleG, hIForest.2⟩ hBgraph
    have hsetEq : (B : Set (Sym2 V)) = (IF : Set (Sym2 V)) := by
      calc
        (B : Set (Sym2 V)) =
            (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).edgeSet :=
          (edgeSet_fromEdgeSet_of_subset hB.1).symm
        _ = (SimpleGraph.fromEdgeSet (IF : Set (Sym2 V))).edgeSet :=
          congrArg SimpleGraph.edgeSet hgraphEq
        _ = (IF : Set (Sym2 V)) :=
          edgeSet_fromEdgeSet_of_subset hIForest.1
    exact hsetEq.trans hIF

end

end HsVirial
