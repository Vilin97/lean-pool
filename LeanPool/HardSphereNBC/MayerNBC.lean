/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.GraphicMatroid
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

namespace HsVirial

open Set
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

/-!
  This file is the finite Mayer/NBC bridge.  The graph part is completely
  discrete.  The measure part is stated for an arbitrary configuration space;
  its only analytic input is measurability of the finitely many regions that
  occur in the finite tree sum.
-/

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder (Sym2 V)]

/-! ### The finite graph ledger -/

def connectedEdgeSubsets (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  (graphEdgeFinset G).powerset.filter
    (fun A => (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected)

def m (G : SimpleGraph V) : Int :=
  ∑ A ∈ connectedEdgeSubsets G, matroidParitySign A.card

def activeEdge (x : Sym2 V → Bool) (e : Sym2 V) : Prop :=
  e ∈ graphEdgeFinset (completeGraph V) ∧ x e = true

noncomputable def activeEdgeFinset (x : Sym2 V → Bool) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (activeEdge x)

/- The overlap graph is deliberately built with `fromEdgeSet`, rather than
   by hiding the active relation in an abstract graph structure. -/
def overlapGraph (x : Sym2 V → Bool) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (activeEdgeFinset x : Set (Sym2 V))

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma activeEdgeFinset_subset_complete (x : Sym2 V → Bool) :
    activeEdgeFinset x ⊆ graphEdgeFinset (completeGraph V) := by
  intro e he
  have he' : activeEdge x e := by
    simpa [activeEdgeFinset] using he
  exact he'.1

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma graphEdgeFinset_overlapGraph (x : Sym2 V → Bool) :
    graphEdgeFinset (overlapGraph x) = activeEdgeFinset x := by
  apply graphEdgeFinset_fromEdgeSet
  intro e he
  exact mem_graphEdgeFinset.mp
    (activeEdgeFinset_subset_complete x (by simpa using he))

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma edgeSet_overlapGraph (x : Sym2 V → Bool) :
    (overlapGraph x).edgeSet = (activeEdgeFinset x : Set (Sym2 V)) := by
  rw [← coe_graphEdgeFinset (overlapGraph x), graphEdgeFinset_overlapGraph]

lemma matroidParitySign_eq_neg_one_pow (n : Nat) :
    matroidParitySign n = (-1 : Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [matroidParitySign_succ, ih, pow_succ]
      ring

noncomputable def bond (x : Sym2 V → Bool) (e : Sym2 V) : Int := by
  classical
  exact if activeEdge x e then -1 else 0

def completeConnectedEdgeSubsets : Finset (Finset (Sym2 V)) :=
  connectedEdgeSubsets (completeGraph V)

def mayerKernel (x : Sym2 V → Bool) : Int :=
  ∑ A ∈ completeConnectedEdgeSubsets,
    ∏ e ∈ A, bond x e

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma bond_prod_of_subset_active {x : Sym2 V → Bool}
    {A : Finset (Sym2 V)} (hA : A ⊆ activeEdgeFinset x) :
    (∏ e ∈ A, bond x e) = matroidParitySign A.card := by
  calc
    (∏ e ∈ A, bond x e) = ∏ _e ∈ A, (-1 : Int) := by
      apply Finset.prod_congr rfl
      intro e he
      have he' := hA he
      have heactive : activeEdge x e := by
        simpa [activeEdgeFinset] using he'
      simp [bond, heactive]
    _ = (-1 : Int) ^ A.card := by simp
    _ = matroidParitySign A.card := by
      rw [matroidParitySign_eq_neg_one_pow]

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma bond_prod_eq_zero_of_not_subset_active {x : Sym2 V → Bool}
    {A : Finset (Sym2 V)} (hA : ¬ A ⊆ activeEdgeFinset x) :
    (∏ e ∈ A, bond x e) = 0 := by
  classical
  rcases Finset.not_subset.mp hA with ⟨e, heA, heactive⟩
  apply Finset.prod_eq_zero heA
  have heinactive : ¬activeEdge x e := by
    intro h
    apply heactive
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  simp [bond, heinactive]

/- The preceding zero proof is easier to use with the membership form of an
   inactive edge.  This auxiliary lemma avoids any Boolean simplification in
   later finite sums. -/
omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma bond_eq_zero_of_not_active {x : Sym2 V → Bool} {e : Sym2 V}
    (he : ¬ activeEdge x e) : bond x e = 0 := by
  classical
  simp [bond, he]

omit [LinearOrder (Sym2 V)] in
lemma connectedEdgeSubsets_overlap (x : Sym2 V → Bool) :
    connectedEdgeSubsets (overlapGraph x) =
      (completeConnectedEdgeSubsets).filter (fun A => A ⊆ activeEdgeFinset x) := by
  ext A
  simp only [connectedEdgeSubsets, completeConnectedEdgeSubsets,
    Finset.mem_filter, Finset.mem_powerset]
  rw [graphEdgeFinset_overlapGraph]
  constructor
  · rintro ⟨hactive, hconn⟩
    exact ⟨⟨hactive.trans (activeEdgeFinset_subset_complete x), hconn⟩, hactive⟩
  · rintro ⟨⟨_, hconn⟩, hactive⟩
    exact ⟨hactive, hconn⟩

omit [LinearOrder (Sym2 V)] in
lemma mayerKernel_eq_m (x : Sym2 V → Bool) :
    mayerKernel x = m (overlapGraph x) := by
  classical
  have hrestrict :
      (∑ A ∈ completeConnectedEdgeSubsets, ∏ e ∈ A, bond x e) =
        ∑ A ∈ (completeConnectedEdgeSubsets).filter
          (fun A => A ⊆ activeEdgeFinset x), ∏ e ∈ A, bond x e := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases h : A ⊆ activeEdgeFinset x
    · simp [h]
    · have hzero : (∏ e ∈ A, bond x e) = 0 := by
        exact bond_prod_eq_zero_of_not_subset_active h
      simp [h, hzero]
  calc
    mayerKernel x =
        ∑ A ∈ (completeConnectedEdgeSubsets).filter
          (fun A => A ⊆ activeEdgeFinset x), ∏ e ∈ A, bond x e := by
      exact hrestrict
    _ = ∑ A ∈ connectedEdgeSubsets (overlapGraph x),
          ∏ e ∈ A, bond x e := by
      rw [connectedEdgeSubsets_overlap]
    _ = m (overlapGraph x) := by
      rw [m]
      apply Finset.sum_congr rfl
      intro A hA
      have hAground : A ⊆ graphEdgeFinset (overlapGraph x) :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
      rw [graphEdgeFinset_overlapGraph] at hAground
      exact bond_prod_of_subset_active hAground

/-! ### Concrete NBC bases of the graphic matroid -/

def IsGraphCircuitNBCandidate (G : SimpleGraph V)
    (A : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ C : Finset (Sym2 V),
    IsGraphCircuit G C ∧ e ∈ C ∧ (∀ f ∈ C, graphEdgeLE f e) ∧
      ((C.erase e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ (A : Set (Sym2 V))

def IsGraphCircuitNBCBad (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  ∃ e, IsGraphCircuitNBCandidate G A e

def IsExplicitNBCBase (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  IsGraphForest G A ∧ IsGraphSpanning G A ∧ ¬IsGraphCircuitNBCBad G A

def IsExplicitNBCTree (G : SimpleGraph V) (A : Finset (Sym2 V)) : Prop :=
  IsGraphForest G A ∧
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected ∧
    ¬IsGraphCircuitNBCBad G A

noncomputable def graphNBCBaseSubsets (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (graphEdgeFinset G).powerset.filter (IsExplicitNBCBase G)

noncomputable def graphNBCTreeSubsets (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (graphEdgeFinset G).powerset.filter (IsExplicitNBCTree G)

def NBC (G : SimpleGraph V) : Nat :=
  (graphNBCTreeSubsets G).card

omit [LinearOrder (Sym2 V)] in
lemma graphicMatroid_spanning_iff_graphSpanning
    {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : A ⊆ graphEdgeFinset G) :
    (graphicMatroid G).Spanning (A : Set (Sym2 V)) ↔
      IsGraphSpanning G A := by
  classical
  constructor
  · intro hspan
    rcases (Matroid.spanning_iff_exists_isBase_subset'.mp hspan) with
      ⟨⟨B, hB, hBA⟩, hBground⟩
    let BF : Finset (Sym2 V) := (Set.toFinite B).toFinset
    have hBF : (BF : Set (Sym2 V)) = B := by
      exact (Set.toFinite B).coe_toFinset
    have hBFA : BF ⊆ A := by
      intro e he
      apply hBA
      have he' : e ∈ (Set.toFinite B).toFinset := by
        simpa [BF] using he
      exact (Set.toFinite B).mem_toFinset.mp he'
    have hBFind : (graphicMatroid G).Indep (BF : Set (Sym2 V)) := by
      rw [hBF]
      exact hB.indep
    have hBFforest : IsGraphForest G BF :=
      (graphicMatroid_indep_finset).mp hBFind
    have hBFbase : (graphicMatroid G).IsBase (BF : Set (Sym2 V)) := by
      rw [hBF]
      exact hB
    have hBFreach :=
      (graphicMatroid_isBase_iff_reachable_eq hBFforest).mp hBFbase
    have hBFAgraph :
        SimpleGraph.fromEdgeSet (BF : Set (Sym2 V)) ≤
          SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) := by
      apply SimpleGraph.fromEdgeSet_mono
      intro e he
      exact hBFA (by simpa using he)
    have hAG : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ G := by
      apply (SimpleGraph.fromEdgeSet_le G).mpr
      intro e he
      exact mem_graphEdgeFinset.mp (hA (by simpa using he.1))
    ext u v
    constructor
    · intro huv
      exact huv.mono hAG
    · intro huv
      have huvBF :
          (SimpleGraph.fromEdgeSet (BF : Set (Sym2 V))).Reachable u v := by
        rw [hBFreach]
        exact huv
      exact huvBF.mono hBFAgraph
  · intro hspan
    let H : SimpleGraph V := SimpleGraph.fromEdgeSet (A : Set (Sym2 V))
    obtain ⟨F, hFH, hFacyc, hFreach⟩ := H.exists_isAcyclic_reachable_eq_le
    let B : Finset (Sym2 V) := graphEdgeFinset F
    have hAedge : (A : Set (Sym2 V)) ⊆ G.edgeSet := by
      intro e he
      exact mem_graphEdgeFinset.mp (hA (by simpa using he))
    have hBFset : (B : Set (Sym2 V)) = F.edgeSet := by
      exact coe_graphEdgeFinset F
    have hBA : B ⊆ A := by
      intro e he
      have heF : e ∈ F.edgeSet := by simpa [B] using he
      have heH : e ∈ H.edgeSet := SimpleGraph.edgeSet_mono hFH heF
      rw [show H.edgeSet = (A : Set (Sym2 V)) by
        simpa [H] using (edgeSet_fromEdgeSet_of_subset hAedge)] at heH
      exact by simpa using heH
    have hBground : B ⊆ graphEdgeFinset G := hBA.trans hA
    have hBgroundSet : (B : Set (Sym2 V)) ⊆ G.edgeSet := by
      intro e he
      exact mem_graphEdgeFinset.mp (hBground (by simpa using he))
    have hBgraph :
        SimpleGraph.fromEdgeSet (B : Set (Sym2 V)) = F := by
      rw [hBFset]
      exact SimpleGraph.fromEdgeSet_edgeSet F
    have hBforest : IsGraphForest G B := by
      refine ⟨hBgroundSet, ?_⟩
      rw [hBgraph]
      exact hFacyc
    have hBreach :
        (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable = G.Reachable := by
      rw [hBgraph, hFreach]
      exact hspan
    have hBbase : (graphicMatroid G).IsBase (B : Set (Sym2 V)) :=
      (graphicMatroid_isBase_iff_reachable_eq hBforest).mpr hBreach
    have hAgroundM : (A : Set (Sym2 V)) ⊆ (graphicMatroid G).E := by
      rw [graphicMatroid_ground]
      exact hAedge
    exact hBbase.spanning.superset (hT := hAgroundM) (by
       intro e he
       exact hBA (by simpa using he))

omit [DecidableEq V] [LinearOrder (Sym2 V)] in
lemma graphSpanning_iff_connected_of_connected
    {G : SimpleGraph V} (hG : G.Connected) {A : Finset (Sym2 V)}
    (_hA : A ⊆ graphEdgeFinset G) :
    IsGraphSpanning G A ↔
      (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Connected := by
  constructor
  · intro hAspan
    letI : Nonempty V := hG.nonempty
    have hpre :
        (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Preconnected := by
      intro u v
      rw [hAspan]
      exact hG.preconnected u v
    exact SimpleGraph.Connected.mk hpre
  · intro hAconn
    funext u v
    apply propext
    constructor
    · intro huv
      exact hG.preconnected u v
    · intro huv
      exact hAconn.preconnected u v

lemma graphNBCTreeSubsets_eq_graphNBCBaseSubsets_of_connected
    {G : SimpleGraph V} (hG : G.Connected) :
    graphNBCTreeSubsets G = graphNBCBaseSubsets G := by
  classical
  ext A
  simp only [graphNBCTreeSubsets, graphNBCBaseSubsets, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨hA, hforest, hconn, hgood⟩
    have hspan :=
      (graphSpanning_iff_connected_of_connected hG hA).mpr hconn
    exact ⟨hA, hforest, hspan, hgood⟩
  · rintro ⟨hA, hforest, hspan, hgood⟩
    have hconn :=
      (graphSpanning_iff_connected_of_connected hG hA).mp hspan
    exact ⟨hA, hforest, hconn, hgood⟩

lemma nbcBaseSubsets_graphic_eq_graphNBCBaseSubsets
    (G : SimpleGraph V) :
    nbcBaseSubsets (graphicMatroid G) = graphNBCBaseSubsets G := by
  classical
  ext A
  constructor
  · intro hA
    have hA' := mem_nbcBaseSubsets hA
    have hground : A ⊆ graphEdgeFinset G := by
      have hground' : A ⊆ matroidGround (graphicMatroid G) := by
        exact Finset.mem_powerset.mp (Finset.mem_filter.mp hA'.1).1
      rw [graph_spanning_finset_eq_matroid_ground (graphicMatroid_ground G)] at hground'
      exact hground'
    have hbase := nbcBase_isBase hA
    have hforest : IsGraphForest G A := by
      apply (graphicMatroid_indep_finset).mp
      exact hbase.indep
    have hspan : IsGraphSpanning G A :=
      (graphicMatroid_spanning_iff_graphSpanning hground).mp
        (mem_spanningSubsets hA'.1)
    have hgood : ¬IsGraphCircuitNBCBad G A := by
      intro hbad
      rcases hbad with ⟨e, C, hC, heC, hmax, hsub⟩
      have hcandidate : IsNBCandidate (graphicMatroid G) A e :=
        ⟨C, (graphicMatroid_isCircuit_iff_graphCircuit).mpr hC,
          heC, hmax, hsub⟩
      exact hA'.2 ⟨e, mem_nbcCandidates.mpr
        ⟨nbcCandidate_mem_ground hcandidate, hcandidate⟩⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hground, hforest, hspan, hgood⟩
  · intro hA
    rcases Finset.mem_filter.mp hA with ⟨hground, hforest, hspan, hgood⟩
    have hground' : A ⊆ graphEdgeFinset G := Finset.mem_powerset.mp hground
    have hMspan : (graphicMatroid G).Spanning (A : Set (Sym2 V)) :=
      (graphicMatroid_spanning_iff_graphSpanning hground').mpr hspan
    have hspanSub : A ∈ spanningSubsets (graphicMatroid G) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hMspan⟩
      exact Finset.mem_powerset.mpr (by
        rw [graph_spanning_finset_eq_matroid_ground (graphicMatroid_ground G)]
        exact hground')
    have hnotbad : ¬IsNBCBad (graphicMatroid G) A := by
      intro hbad
      rcases hbad with ⟨e, he⟩
      have hcandidate := (mem_nbcCandidates.mp he).2
      rcases hcandidate with ⟨C, hC, heC, hmax, hsub⟩
      apply hgood
      exact ⟨e, C, (graphicMatroid_isCircuit_iff_graphCircuit).mp hC,
        heC, hmax, hsub⟩
    exact Finset.mem_filter.mpr ⟨hspanSub, hnotbad⟩

noncomputable def treeUniverse : Finset (Finset (Sym2 V)) := by
  classical
  exact (graphEdgeFinset (completeGraph V)).powerset.filter
    (fun T : Finset (Sym2 V) =>
      (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).IsTree)

lemma graphNBCTreeSubsets_subset_treeUniverse
    {G : SimpleGraph V} {A : Finset (Sym2 V)}
    (hA : A ∈ graphNBCTreeSubsets G) :
    A ∈ treeUniverse := by
  classical
  rcases Finset.mem_filter.mp hA with ⟨hAground, hforest, hconn, _⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_powerset.mpr
    intro e he
    apply mem_graphEdgeFinset.mpr
    exact SimpleGraph.edgeSet_mono (by simp)
      (mem_graphEdgeFinset.mp ((Finset.mem_powerset.mp hAground) he))
  · exact ⟨hconn, hforest.2⟩

/-! The signed matroid theorem is now applied to the concrete graphic
    construction.  The good sets on the right are a finite, explicit filter;
    `NBC` is its natural cardinality. -/

lemma graphNBCBaseSubsets_card_eq_NBC_of_connected
    {G : SimpleGraph V} (hG : G.Connected) :
    (graphNBCBaseSubsets G).card = NBC G := by
  rw [← graphNBCTreeSubsets_eq_graphNBCBaseSubsets_of_connected hG]
  rfl

lemma m_eq_signed_NBC_of_connected
    {G : SimpleGraph V} (hG : G.Connected) :
    m G = (-1 : Int) ^ (Fintype.card V - 1) * (NBC G : Int) := by
  classical
  have hground : (graphicMatroid G).E = G.edgeSet := graphicMatroid_ground G
  have hspan : ∀ A : Finset (Sym2 V), A ⊆ graphEdgeFinset G →
      ((graphicMatroid G).Spanning (A : Set (Sym2 V)) ↔ IsGraphSpanning G A) :=
    fun A hA => graphicMatroid_spanning_iff_graphSpanning hA
  have hspanEq := spanningSubsets_eq_graphSpanningSubsets hground hspan
  have hconnEq : connectedEdgeSubsets G = graphSpanningSubsets G := by
    ext A
    simp only [connectedEdgeSubsets, graphSpanningSubsets, Finset.mem_filter,
      Finset.mem_powerset]
    constructor
    · rintro ⟨hA, hconn⟩
      exact ⟨hA, (graphSpanning_iff_connected_of_connected hG hA).mpr hconn⟩
    · rintro ⟨hA, hspanA⟩
      exact ⟨hA, (graphSpanning_iff_connected_of_connected hG hA).mp hspanA⟩
  have hbaseEq := nbcBaseSubsets_graphic_eq_graphNBCBaseSubsets G
  have hsign : ∀ A ∈ graphNBCBaseSubsets G,
      matroidParitySign A.card = (-1 : Int) ^ (Fintype.card V - 1) := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hAground, hforest, hspanA, hgood⟩
    have hAground' : A ⊆ graphEdgeFinset G := Finset.mem_powerset.mp hAground
    have htree : (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).IsTree := by
      exact ⟨(graphSpanning_iff_connected_of_connected hG hAground').mp hspanA,
        hforest.2⟩
    letI : Fintype (SimpleGraph.fromEdgeSet
        (A : Set (Sym2 V))).edgeSet := Fintype.ofFinite _
    have hcard := htree.card_edgeFinset
    have hnative : graphEdgeFinset
        (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))) =
        (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).edgeFinset := by
      apply Finset.coe_injective
      simp
    rw [← hnative, graphEdgeFinset_fromEdgeSet hforest.1] at hcard
    have hcard' : A.card = Fintype.card V - 1 := by
      have : A.card + 1 = Fintype.card V := hcard
      omega
    rw [hcard', matroidParitySign_eq_neg_one_pow]
  calc
    m G = ∑ A ∈ graphSpanningSubsets G, matroidParitySign A.card := by
      rw [m, hconnEq]
    _ = signedSpanningSum (graphicMatroid G) := by
      rw [signedSpanningSum, hspanEq]
    _ = signedNBCSum (graphicMatroid G) := signed_spanning_eq_signed_nbc _
    _ = ∑ A ∈ graphNBCBaseSubsets G, matroidParitySign A.card := by
      rw [signedNBCSum, hbaseEq]
    _ = (-1 : Int) ^ (Fintype.card V - 1) * (NBC G : Int) := by
      rw [← graphNBCBaseSubsets_card_eq_NBC_of_connected hG]
      calc
        (∑ A ∈ graphNBCBaseSubsets G, matroidParitySign A.card) =
            ∑ _A ∈ graphNBCBaseSubsets G,
              (-1 : Int) ^ (Fintype.card V - 1) := by
          apply Finset.sum_congr rfl
          intro A hA
          exact hsign A hA
        _ = (-1 : Int) ^ (Fintype.card V - 1) *
              (graphNBCBaseSubsets G).card := by
          simp [Finset.sum_const, mul_comm]

/-! ### Pointwise finite tree decomposition -/

def nbcRegion {X : Type*} (active : X → Sym2 V → Bool)
    (T : Finset (Sym2 V)) : Set X :=
  {x | IsExplicitNBCTree (overlapGraph (active x)) T}

lemma mem_treeUniverse_of_mem_graphNBCTreeSubsets
    {x : Sym2 V → Bool} {T : Finset (Sym2 V)}
    (hT : T ∈ graphNBCTreeSubsets (overlapGraph x)) :
    T ∈ treeUniverse := by
  exact graphNBCTreeSubsets_subset_treeUniverse hT

lemma mem_graphNBCTreeSubsets_iff_mem_treeUniverse_and_region
    {X : Type*} (active : X → Sym2 V → Bool) (x : X)
    {T : Finset (Sym2 V)} (_hT : T ∈ treeUniverse) :
    T ∈ graphNBCTreeSubsets (overlapGraph (active x)) ↔
      x ∈ nbcRegion active T := by
  classical
  change T ∈ graphNBCTreeSubsets (overlapGraph (active x)) ↔
    IsExplicitNBCTree (overlapGraph (active x)) T
  constructor
  · intro hT
    exact (Finset.mem_filter.mp hT).2
  · intro hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, hT⟩
    intro e he
    apply mem_graphEdgeFinset.mpr
    have hforest : IsGraphForest (overlapGraph (active x)) T := hT.1
    exact hforest.1 (by simpa using he)

open Classical in
lemma nbc_tree_decomposition' (x : Sym2 V → Bool) :
    (if (overlapGraph x).Connected then NBC (overlapGraph x) else 0) =
      ∑ T ∈ treeUniverse,
        if T ∈ graphNBCTreeSubsets (overlapGraph x) then 1 else 0 := by
  classical
  by_cases hG : (overlapGraph x).Connected
  · rw [if_pos hG, NBC]
    have hsubset : graphNBCTreeSubsets (overlapGraph x) ⊆ treeUniverse := by
      intro T hT
      exact graphNBCTreeSubsets_subset_treeUniverse hT
    exact Finset.card_eq_sum_ite hsubset
  · have hzero : graphNBCTreeSubsets (overlapGraph x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      have hT' := Finset.mem_filter.mp hT
      have hle : SimpleGraph.fromEdgeSet (T : Set (Sym2 V)) ≤ overlapGraph x := by
        apply (SimpleGraph.fromEdgeSet_le (overlapGraph x)).mpr
        intro e he
        exact (hT'.2).1.1 he.1
      exact hG ((hT'.2).2.1.mono hle)
    rw [NBC, hzero]
    simp

/-! The Boolean region form of the same decomposition. -/
open Classical in
lemma nbc_tree_decomposition_region {X : Type*}
    (active : X → Sym2 V → Bool) (x : X) :
    (if (overlapGraph (active x)).Connected then
        NBC (overlapGraph (active x)) else 0) =
      ∑ T ∈ treeUniverse, if x ∈ nbcRegion active T then 1 else 0 := by
  classical
  calc
    (if (overlapGraph (active x)).Connected then
        NBC (overlapGraph (active x)) else 0) =
        ∑ T ∈ treeUniverse,
          if T ∈ graphNBCTreeSubsets (overlapGraph (active x)) then 1 else 0 :=
      nbc_tree_decomposition' (active x)
    _ = ∑ T ∈ treeUniverse, if x ∈ nbcRegion active T then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases h : T ∈ graphNBCTreeSubsets (overlapGraph (active x))
      · rw [if_pos h, if_pos
          ((mem_graphNBCTreeSubsets_iff_mem_treeUniverse_and_region active x hT).mp h)]
      · rw [if_neg h, if_neg
          ((mem_graphNBCTreeSubsets_iff_mem_treeUniverse_and_region active x hT).not.mp h)]

/-! For disconnected overlap graphs both sides vanish.  This is the finite
    form needed to turn the signed identity into a nonnegative integrand. -/
lemma graphNBC_zero_of_not_connected {G : SimpleGraph V}
    (hG : ¬G.Connected) : NBC G = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hA' := Finset.mem_filter.mp hA
  have hle : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ G := by
    apply (SimpleGraph.fromEdgeSet_le G).mpr
    intro e he
    exact (hA'.2).1.1 he.1
  exact hG ((hA'.2).2.1.mono hle)

def intMagnitude (z : Int) : ℝ≥0∞ := z.natAbs

lemma intMagnitude_signed_nat (n q : Nat) :
    intMagnitude ((-1 : Int) ^ n * (q : Int)) = (q : ℝ≥0∞) := by
  simp [intMagnitude, Int.natAbs_mul]

open Classical in
lemma abs_mayerKernel_eq_nbc (x : Sym2 V → Bool) :
    intMagnitude (mayerKernel x) =
      if (overlapGraph x).Connected then (NBC (overlapGraph x) : ℝ≥0∞) else 0 := by
  classical
  rw [mayerKernel_eq_m]
  by_cases hG : (overlapGraph x).Connected
  · rw [if_pos hG, m_eq_signed_NBC_of_connected hG]
    exact intMagnitude_signed_nat _ _
  · rw [if_neg hG]
    have hzero : connectedEdgeSubsets (overlapGraph x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      have hA' := Finset.mem_filter.mp hA
      have hle : SimpleGraph.fromEdgeSet (A : Set (Sym2 V)) ≤ overlapGraph x := by
        apply (SimpleGraph.fromEdgeSet_le (overlapGraph x)).mpr
        intro e he
        exact mem_graphEdgeFinset.mp
          ((Finset.mem_powerset.mp hA'.1) (by simpa using he.1))
      exact hG (SimpleGraph.Connected.mono hle hA'.2)
    simp [m, hzero, intMagnitude]

/-! ### Arbitrary measure spaces -/

def absMayerIntegrand {X : Type*} (active : X → Sym2 V → Bool) (x : X) : ℝ≥0∞ :=
  intMagnitude (mayerKernel (active x))

def absClusterCoefficient {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (active : X → Sym2 V → Bool) : ℝ≥0∞ :=
  ((Fintype.card V).factorial : ℝ≥0∞)⁻¹ *
    ∫⁻ x, absMayerIntegrand active x ∂μ

lemma measurable_nbcRegion_indicator {X : Type*}
    [MeasurableSpace X]
    (active : X → Sym2 V → Bool) {T : Finset (Sym2 V)}
    (_hT : T ∈ treeUniverse) (hmeas : MeasurableSet (nbcRegion active T)) :
    Measurable ((nbcRegion active T).indicator (fun _ : X => (1 : ℝ≥0∞))) := by
  exact measurable_const.indicator hmeas

theorem lintegral_abs_mayerKernel_eq_sum_NBC_region_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (active : X → Sym2 V → Bool)
    (hmeas : ∀ T ∈ treeUniverse, MeasurableSet (nbcRegion active T)) :
    (∫⁻ x, absMayerIntegrand active x ∂μ) =
      ∑ T ∈ treeUniverse, μ (nbcRegion active T) := by
  classical
  have hpoint : ∀ x : X,
      absMayerIntegrand active x =
        ∑ T ∈ treeUniverse,
          (nbcRegion active T).indicator (fun _ : X => (1 : ℝ≥0∞)) x := by
    intro x
    calc
      absMayerIntegrand active x = intMagnitude (mayerKernel (active x)) := rfl
      _ = if (overlapGraph (active x)).Connected then
          (NBC (overlapGraph (active x)) : ℝ≥0∞) else 0 :=
        abs_mayerKernel_eq_nbc (active x)
      _ = ((if (overlapGraph (active x)).Connected then
          NBC (overlapGraph (active x)) else 0 : Nat) : ℝ≥0∞) := by simp
      _ = ((∑ T ∈ treeUniverse,
          if x ∈ nbcRegion active T then 1 else 0 : Nat) : ℝ≥0∞) := by
        exact congrArg (fun n : Nat => (n : ℝ≥0∞))
          (nbc_tree_decomposition_region active x)
      _ = ∑ T ∈ treeUniverse,
          (nbcRegion active T).indicator (fun _ : X => (1 : ℝ≥0∞)) x := by
        simp [Set.indicator]
  rw [show (fun x => absMayerIntegrand active x) =
      (fun x => ∑ T ∈ treeUniverse,
        (nbcRegion active T).indicator (fun _ : X => (1 : ℝ≥0∞)) x) by
    funext x
    exact hpoint x]
  rw [MeasureTheory.lintegral_finsetSum treeUniverse]
  · apply Finset.sum_congr rfl
    intro T hT
    simpa using
      (MeasureTheory.lintegral_indicator_const (μ := μ)
        (s := nbcRegion active T) (hmeas T hT) 1)
  · intro T hT
    exact measurable_nbcRegion_indicator active hT (hmeas T hT)

theorem factorial_mul_absClusterCoefficient
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (active : X → Sym2 V → Bool)
    (hmeas : ∀ T ∈ treeUniverse, MeasurableSet (nbcRegion active T)) :
      ((Fintype.card V).factorial : ℝ≥0∞) *
        absClusterCoefficient μ active =
      ∑ T ∈ treeUniverse, μ (nbcRegion active T) := by
  have hfac : ((Fintype.card V).factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card V)
  have hfacTop : ((Fintype.card V).factorial : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  rw [absClusterCoefficient,
    lintegral_abs_mayerKernel_eq_sum_NBC_region_measure μ active hmeas,
    ← mul_assoc, ENNReal.mul_inv_cancel hfac hfacTop, one_mul]

/- The normalized nonnegative coefficient is the `|b_k|` representative used
   by the volume identity.  The signed pointwise theorem above supplies its
   Mayer interpretation without introducing a non-measurable real integral. -/
abbrev absBk {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (active : X → Sym2 V → Bool) : ℝ≥0∞ :=
  absClusterCoefficient μ active

abbrev nbcRegionVolume {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (active : X → Sym2 V → Bool)
    (T : Finset (Sym2 V)) : ℝ≥0∞ :=
  μ (nbcRegion active T)

theorem factorial_mul_absBk_eq_nbcVolumeSum
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (active : X → Sym2 V → Bool)
    (hmeas : ∀ T ∈ treeUniverse, MeasurableSet (nbcRegion active T)) :
    ((Fintype.card V).factorial : ℝ≥0∞) * absBk μ active =
      ∑ T ∈ treeUniverse, nbcRegionVolume μ active T := by
  exact factorial_mul_absClusterCoefficient μ active hmeas

/-! ### Hard-sphere activity, with no geometric factorization claim -/

abbrev HSPosition (d : Nat) := EuclideanSpace ℝ (Fin d)

def AnchoredHSConfiguration (k d : Nat) :=
  {r : Fin (k + 1) → HSPosition d // r 0 = 0}

def hardSphereActive {k d : Nat}
    (r : AnchoredHSConfiguration k d) : Sym2 (Fin (k + 1)) → Bool :=
  Sym2.lift ⟨fun i j => decide (‖r.1 i - r.1 j‖ < (1 : ℝ)), by
    intro i j
    change decide (‖r.1 i - r.1 j‖ < (1 : ℝ)) =
      decide (‖r.1 j - r.1 i‖ < (1 : ℝ))
    rw [norm_sub_rev]⟩

@[simp] lemma hardSphereActive_mk {k d : Nat}
    (r : AnchoredHSConfiguration k d) (i j : Fin (k + 1)) :
    hardSphereActive r s(i, j) = decide (‖r.1 i - r.1 j‖ < (1 : ℝ)) := by
  rfl

theorem hardSphere_mayerKernel_bridge {k d : Nat}
    [LinearOrder (Sym2 (Fin (k + 1)))]
    (r : AnchoredHSConfiguration k d) :
    mayerKernel (hardSphereActive r) =
      m (overlapGraph (hardSphereActive r)) :=
  mayerKernel_eq_m (hardSphereActive r)

theorem hardSphere_factorial_measure_bridge {k d : Nat}
    [LinearOrder (Sym2 (Fin (k + 1)))]
    [MeasurableSpace (AnchoredHSConfiguration k d)]
    (μ : Measure (AnchoredHSConfiguration k d))
    (hmeas : ∀ T ∈ treeUniverse (V := Fin (k + 1)),
      MeasurableSet (nbcRegion (V := Fin (k + 1))
        (hardSphereActive (k := k) (d := d)) T)) :
    ((Fintype.card (Fin (k + 1))).factorial : ℝ≥0∞) *
        absClusterCoefficient μ (hardSphereActive (k := k) (d := d)) =
      ∑ T ∈ treeUniverse (V := Fin (k + 1)),
      μ (nbcRegion (V := Fin (k + 1))
        (hardSphereActive (k := k) (d := d)) T) := by
  exact factorial_mul_absClusterCoefficient
    (V := Fin (k + 1)) (X := AnchoredHSConfiguration k d) μ
      (hardSphereActive (k := k) (d := d)) hmeas

end

end HsVirial
