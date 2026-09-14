/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.CommonSubdivision
import LeanPool.Schoenflies.CrosscutExists
import LeanPool.Schoenflies.FreshAccess
import LeanPool.Schoenflies.Graph.VertexSquares

/-!
# Finite transfer, direction (b): toward the Jordan domain

Direction (b) starts with an extension of the **target** realization and reproduces it on the
source side.  This module begins its construction with the target analogue of the common
subdivision from direction (a).  The graph-theoretic extension assumptions are exactly
`Schoenflies.IsSourceExtension`, applied to `P.tgt`: only the side on which the realization lives
changes.

The trace of the target extension supported on the old target skeleton is 2-connected.  Its
finitely many vertices are inserted by `GeneratedPair.exists_subdivideTargetSetData`; each target
point is transported backwards through the skeleton homeomorphism, and the resulting source
parameter is then carried forward by `SubdivData.realizeHomeo`.  Thus the same subdivision is
made on both sides and both refinement maps share one parent map.

The reverse ear bookkeeping is also completed here.  The ambient target path is injectively
renamed, realized as a target crosscut, and then matched to a polygonal source crosscut by
reversing `EarHomeo`.  Off the wild curve, endpoint accessibility is derived from
polygonal-side accessibility.  At a fresh anchor, this module constructs the compact carrier of
closed nonboundary edges and discharges compactness, cell absorption, and coverage before
applying `Schoenflies.polyAccessible_of_stronglyAccessible_in`.  `TargetBoundaryAnchored` and
the compatibility of the evolving skeleton map now supply strong accessibility automatically.
Consequently the only remaining input is `TargetEarFreshCombinatorics`: the prescribed ear
order must say that a wild-boundary endpoint is absent from the current nonboundary carrier and
incident with one unique current source face.

## Blueprint

* `Schoenflies.IsTargetPartialTransferOf`, `Schoenflies.TargetCommonSubdivision` — the
  target-to-source analogues of the direction-(a) transfer interfaces.
* `Schoenflies.targetCommonSubdivision` — step 1 of `thm:finite-transfer`(b).
* `Schoenflies.TargetEarStepData`, `Schoenflies.exists_targetSideEarStepData` — the complete
  target-path relabelling and split data for one reverse ear.
* `Schoenflies.TargetEarEndpointAccessibility`,
  `Schoenflies.targetEarStep_of_endpointAccessibility` — the reverse ear construction reduced
  to its exact source-side geometric invariant.
* `Schoenflies.GeneratedPair.sourceNonboundaryGraph`,
  `Schoenflies.GeneratedPair.source_polyAccessible_of_fresh` — the compact source carrier and
  the fresh-anchor accessibility theorem with all cellulation hypotheses discharged.
* `Schoenflies.TargetBoundaryAnchored`, `Schoenflies.TargetEarFreshCombinatorics`,
  `Schoenflies.targetEarFreshInvariant_of_boundaryAnchored` — the fixed anchor geometry split
  cleanly from the remaining prescribed-ear combinatorics.
* `Schoenflies.targetTransferOfEars`,
  `Schoenflies.finite_transfer_toward_source_of_freshInvariant` — the relative-ear induction
  and direction-(b) theorem assuming only that combinatorial invariant.
-/

open Set
open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- An intermediate target-to-source transfer: the target realization occupies the current
subgraph of the target extension, while both sides refine the original pair along one map. -/
structure IsTargetPartialTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop where
  /-- The new source realization refines the original source realization. -/
  refines_src : T.src.Refines P.src par
  /-- The new target realization refines the original target realization along the same map. -/
  refines_tgt : T.tgt.Refines P.tgt par
  /-- The evolving source skeleton contains the original source skeleton. -/
  sourceSkeletonSet_subset : P.src.skeletonSet ⊆ T.src.skeletonSet
  /-- On the original source skeleton, the evolving skeleton map is still the original map. -/
  homeo_eqOn : Set.EqOn T.homeo.toFun P.homeo.toFun P.src.skeletonSet
  /-- The new target skeleton occupies exactly the current target subgraph. -/
  skeletonSet_eq : T.tgt.skeletonSet = pointSet B Hdraw
  /-- Every current target-graph vertex is a 0-cell of the new pair. -/
  vertexSet_subset : V(B) ⊆ V(T.tgt.graph)

/-- The evolving target skeleton contains the original target skeleton.  This is transported
from the corresponding source inclusion through the two compatible skeleton homeomorphisms. -/
theorem IsTargetPartialTransferOf.targetSkeletonSet_subset
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    P.tgt.skeletonSet ⊆ T.tgt.skeletonSet := by
  intro y hy
  rw [← P.homeo.image_skeletonSet] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxT : x ∈ T.src.skeletonSet := hT.sourceSkeletonSet_subset hx
  have himage : T.homeo.toFun x ∈ T.tgt.skeletonSet := by
    rw [← T.homeo.image_skeletonSet]
    exact Set.mem_image_of_mem T.homeo.toFun hxT
  rwa [hT.homeo_eqOn hx] at himage

/-- A current abstract vertex lying over the original target skeleton has the original source
preimage.  This is the pointwise compatibility needed to recognize prescribed source anchors
after any number of reverse-ear insertions. -/
theorem IsTargetPartialTransferOf.source_pos_eq_invFun_target_pos
    {T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    (hT : IsTargetPartialTransferOf T P B Hdraw par) {v : γ}
    (hv : v ∈ V(T.str.skel)) (hvP : T.tgt.pos v ∈ P.tgt.skeletonSet) :
    T.src.pos v = P.homeo.invFun (T.tgt.pos v) := by
  have hinvP : P.homeo.invFun (T.tgt.pos v) ∈ P.src.skeletonSet := by
    rw [← P.homeo.symm.image_skeletonSet]
    exact ⟨T.tgt.pos v, hvP, rfl⟩
  apply T.homeo.injOn
  · exact T.src.pos_mem_skeletonSet hv
  · exact hT.sourceSkeletonSet_subset hinvP
  · rw [T.homeo.pos_apply hv, hT.homeo_eqOn hinvP,
      P.homeo.rightInvOn hvP]

/-- The final conclusion of direction (b): a target extension reproduced by an admissible
matched pair on both sides. -/
structure IsTargetTransferOf
    (T P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (par : γ → γ) : Prop
    extends IsTargetPartialTransferOf T P H Hdraw par where
  /-- The transferred source realization is admissible. -/
  src_isAdmissible : T.src.IsAdmissible srcOuter srcDom
  /-- The transferred target realization is admissible. -/
  tgt_isAdmissible : T.tgt.IsAdmissible tgtOuter tgtDom

/-- Step 1 of direction (b), as the interface consumed by its relative-ear induction. -/
def TargetCommonSubdivision
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
      (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsTargetPartialTransferOf T₀ P K Hdraw par₀

/-- One target ear insertion, expressed as the step consumed by relative-ear induction. -/
def TargetEarStep [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∃ (T' : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par' : γ → γ),
        IsTargetPartialTransferOf T' P (B.union (H.pathGraphOf a D)) Hdraw par'

/-- Complete constructor data for adjoining one target ear to a partial reverse transfer. -/
structure TargetEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a : Plane) (D : List γ) where
  /-- The common abstract face split. -/
  splitData : T.str.SplitData
  /-- The two realizations of its new ear. -/
  srcPos : γ → Plane
  srcDraw : γ → ℝ → Plane
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  /-- Each realized ear is a crosscut of the corresponding old face. -/
  srcCrosscut : splitData.EarCrosscut T.src srcPos srcDraw
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  /-- The source-to-target matching consumed by `GeneratedPair.split`. -/
  earHomeo : splitData.EarHomeo srcPos srcDraw tgtPos tgtDraw
  /-- Both realized ears have polygonal edges. -/
  srcEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc srcDraw e)
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  /-- The target ear realizes exactly the ambient target path. -/
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  /-- All vertices of the enlarged target graph occur in the split realization. -/
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

namespace TargetEarStepData

variable {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
  {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {a : Plane} {D : List γ}

/-- Assemble the generated pair exposed by one reverse-ear construction. -/
noncomputable def pair (w : TargetEarStepData T B H Hdraw a D) :
    GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom :=
  T.split T.str_combInvariants w.splitData w.srcPos w.srcDraw w.tgtPos w.tgtDraw
    w.srcCrosscut w.tgtCrosscut w.earHomeo w.srcEdgePolygonal w.tgtEdgePolygonal

@[simp] theorem pair_src (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.src =
      w.splitData.realize T.src w.srcPos w.srcDraw w.srcCrosscut := rfl

@[simp] theorem pair_tgt (w : TargetEarStepData T B H Hdraw a D) :
    w.pair.tgt =
      w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut := rfl

/-- The assembled pair realizes the enlarged target subgraph and refines the original pair. -/
theorem isTargetPartialTransferOf_pair
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom} {b : Plane}
    {par : γ → γ} (w : TargetEarStepData T B H Hdraw a D)
    (hdraw : H.IsDrawing Hdraw) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    IsTargetPartialTransferOf w.pair P (B.union (H.pathGraphOf a D)) Hdraw
      (par ∘ w.splitData.parent) where
  refines_src :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.srcCrosscut
      T.str_combInvariants T.src_isCellDecomposition T.src_isFaceJordan).2.2).trans
      hT.refines_src
  refines_tgt :=
    ((w.splitData.isCellDecomposition_and_isFaceJordan_realize w.tgtCrosscut
      T.str_combInvariants T.tgt_isCellDecomposition T.tgt_isFaceJordan).2.2).trans
      hT.refines_tgt
  sourceSkeletonSet_subset :=
    hT.sourceSkeletonSet_subset.trans
      (w.splitData.skeletonSet_subset_realize w.srcCrosscut)
  homeo_eqOn := by
    intro x hx
    calc
      w.pair.homeo.toFun x = T.homeo.toFun x :=
        w.splitData.splitHomeo_eqOn
          (g := T.homeo) (hE₁ := w.srcCrosscut) (hE₂ := w.tgtCrosscut)
          (m := w.earHomeo) (hT.sourceSkeletonSet_subset hx)
      _ = P.homeo.toFun x := hT.homeo_eqOn hx
  skeletonSet_eq := by
    change (w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).skeletonSet = _
    rw [w.splitData.skeletonSet_realize, hT.skeletonSet_eq, w.tgtEarSet_eq,
      Graph.pointSet_union, hdraw.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)]
  vertexSet_subset := by
    change V(B.union (H.pathGraphOf a D)) ⊆
      V((w.splitData.realize T.tgt w.tgtPos w.tgtDraw w.tgtCrosscut).graph)
    exact w.vertexSet_subset

end TargetEarStepData

/-- The nontrivial reverse-ear constructor, before the already-present-edge branch is folded
back in. -/
def TargetEarStepConstruction [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (_hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      Nonempty (TargetEarStepData T B H Hdraw a D)

/-- Fold the explicit nontrivial reverse-ear constructor into the total `TargetEarStep`
interface. -/
theorem targetEarStep_of_data [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hbuild : TargetEarStepConstruction P H Hdraw hH) :
    TargetEarStep P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint T par hT
  rcases Graph.ear_edges_notMem_or_union_eq hBH hpath hab haB hbB hint with hnew | hsame
  · obtain ⟨w⟩ := hbuild B a b D hB hBH hpath hab haB hbB hint hnew T par hT
    exact ⟨w.pair, par ∘ w.splitData.parent,
      w.isTargetPartialTransferOf_pair hH.isDrawing hpath hab hT⟩
  · refine ⟨T, par, ?_⟩
    rw [hsame]
    exact hT

/-! ### Locating and realizing the target half of a reverse ear -/

/-- A nontrivial target ear lies in one current target face and determines its two abstract
endpoint vertices. -/
theorem exists_target_face_of_ear
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hint : ∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    (hT : IsTargetPartialTransferOf T P B Hdraw par) :
    ∃ u v F, u ∈ V(T.str.skel) ∧ v ∈ V(T.str.skel) ∧ u ≠ v ∧
      T.tgt.pos u = a ∧ T.tgt.pos v = b ∧ F ∈ T.str.faces ∧
      Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F ∧
      T.str.sub u F ∧ T.str.sub v F := by
  have haT := hT.vertexSet_subset haB
  have hbT := hT.vertexSet_subset hbB
  rw [CellStructure.Realization.vertexSet_graph] at haT hbT
  obtain ⟨u, hu, hua⟩ := haT
  obtain ⟨v, hv, hvb⟩ := hbT
  have huv : u ≠ v := by
    intro huv
    apply hab
    rw [← hua, ← hvb, huv]
  have harc : IsArcBetween (Graph.edgesCover Hdraw D) a b :=
    hH.isDrawing.path_isArcBetween hpath (hpath.ne_nil hab)
  let N := Graph.edgesCover Hdraw D \ {a, b}
  have hNconn : IsPreconnected N := harc.isConnected_diff.isPreconnected
  have hNne : N.Nonempty := harc.isConnected_diff.nonempty
  have hND : N ⊆ tgtDom := by
    intro x hx
    exact hH.pointSet_subset
      (Graph.edgesCover_subset_pointSet (fun g hg => hpath.edge_mem hg) hx.1)
  have hNdisj : Disjoint N T.tgt.skeletonSet := by
    rw [hT.skeletonSet_eq]
    refine Set.disjoint_left.2 fun x hx hxB ↦ hx.2 ?_
    exact hH.isDrawing.edgesCover_inter_pointSet hBH hpath hint hnew ⟨hx.1, hxB⟩
  obtain ⟨F, hF, hNF, huF, hvF, -⟩ :=
    T.tgt_isCellDecomposition.exists_face_of_ear
      (T.tgt_isCellDecomposition.cellsAbsorb T.tgt_isFaceJordan)
      hNconn hNne hND hNdisj hu hv
      (hua ▸ harc.left_mem_closure_diff) (hvb ▸ harc.right_mem_closure_diff)
  exact ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hNF, huF, hvF⟩

/-- No edge of a genuine target ear is contained in the outer curve.  Such an edge would lie
simultaneously in the old target skeleton and in the open current face. -/
theorem target_ear_edge_not_outer
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F) :
    ∀ e ∈ D, ¬ Graph.edgeArc Hdraw e ⊆ tgtOuter := by
  intro e he houter
  have houterSkel : tgtOuter ⊆ T.tgt.skeletonSet := by
    intro z hz
    apply T.tgt.outerSet_subset_skeletonSet
    rw [T.tgt_isWeaklyAdmissible.outerSet_eq]
    exact hz
  have harcPair : edgeArc Hdraw e ⊆ ({a, b} : Set Plane) := by
    intro z hz
    by_contra hzpair
    have hzCell : z ∈ T.tgt.cell F :=
      hinside ⟨Graph.mem_edgesCover he hz, hzpair⟩
    have hzSkel : z ∈ T.tgt.skeletonSet := houterSkel (houter hz)
    exact Set.disjoint_left.1
      (T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF) hzCell hzSkel
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hpath.edge_mem he)
  have harc := hH.isDrawing.edge_isArcBetween hxy
  have hxyne := hH.isDrawing.ne_of_isLink hxy
  rcases harcPair harc.left_mem with rfl | rfl <;>
    rcases harcPair harc.right_mem with rfl | rfl
  · exact hxyne rfl
  · exact harc.not_subset_pair harcPair
  · exact harc.not_subset_pair (by simpa [Set.pair_comm] using harcPair)
  · exact hxyne rfl

/-- Every edge of a genuine target ear is polygonal. -/
theorem target_ear_edge_polygonal
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {F : γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hpath : H.IsPath a D b) (hF : F ∈ T.str.faces)
    (hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell F) :
    ∀ e ∈ D, IsPolygonal (Graph.edgeArc Hdraw e) := by
  intro e he
  rcases hH.edge_dichotomy (hpath.edge_mem he) with houter | hpoly
  · exact absurd houter (target_ear_edge_not_outer hH hpath hF hinside e he)
  · exact hpoly.1

/-- Every boundary endpoint of a nonouter ambient target edge comes from a strongly accessible
source anchor.  The stage construction will discharge this from the fresh-point list of its
anchored square mesh. -/
def TargetBoundaryAnchored {β : Type*}
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane β) (Hdraw : β → ℝ → Plane) : Prop :=
  ∀ {f : β} {y : Plane}, f ∈ E(H) → H.Inc f y → y ∈ tgtOuter →
    ¬ edgeArc Hdraw f ⊆ tgtOuter →
    StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun y)

/-- The relative anchoring condition used by reverse ear insertion.  Only genuinely new
ambient edges need to end at prescribed strongly accessible anchors; edges already covering
the original target skeleton are irrelevant to the next ear. -/
def NewTargetBoundaryAnchored {β : Type*}
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (base : Set Plane)
    (H : Graph Plane β) (Hdraw : β → ℝ → Plane) : Prop :=
  ∀ {B : Graph Plane β}, B ≤ H → base ⊆ pointSet B Hdraw →
    ∀ {f : β} {y : Plane}, f ∈ E(H) → f ∉ E(B) → H.Inc f y → y ∈ tgtOuter →
      ¬ edgeArc Hdraw f ⊆ tgtOuter →
      StronglyAccessible (srcDom \ srcOuter) (P.homeo.invFun y)

/-- Anchoring every nonouter boundary edge implies the relative new-edge condition. -/
theorem TargetBoundaryAnchored.new
    {β : Type*} {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane β} {Hdraw : β → ℝ → Plane}
    (h : TargetBoundaryAnchored P H Hdraw) (base : Set Plane) :
    NewTargetBoundaryAnchored P base H Hdraw := by
  intro B hBH _ f y hf _ hinc hy hnot
  exact h hf hinc hy hnot

/-- At a point of the distinguished boundary, there is at most one incident ambient edge not
contained in that boundary.  The ambient edge-name type is deliberately independent of the
cell-name type. -/
def NonouterIncidenceUniqueAtBoundary {β : Type*}
    (H : Graph Plane β) (Hdraw : β → ℝ → Plane) (outer : Set Plane) : Prop :=
  ∀ {z : Plane} {e f : β}, z ∈ outer → e ∈ E(H) → f ∈ E(H) →
    H.Inc e z → H.Inc f z →
    ¬ edgeArc Hdraw e ⊆ outer → ¬ edgeArc Hdraw f ⊆ outer → e = f

/-- The relative boundary-incidence condition actually used by reverse ear insertion.  A new
nonouter ambient edge cannot meet, at the distinguished boundary, a nonouter edge already in
the current trace.  Unlike `NonouterIncidenceUniqueAtBoundary`, this permits several old
nonouter edges at an old boundary vertex, which is essential for target-mesh overlays. -/
def NoNewNonouterIncidenceAtBoundary {β : Type*}
    (base : Set Plane) (H : Graph Plane β) (Hdraw : β → ℝ → Plane)
    (outer : Set Plane) : Prop :=
  ∀ {B : Graph Plane β}, B ≤ H → base ⊆ pointSet B Hdraw →
    ∀ {z : Plane} {e f : β}, z ∈ outer → e ∈ E(H) → f ∈ E(B) →
      H.Inc e z → B.Inc f z →
      ¬ edgeArc Hdraw e ⊆ outer → ¬ edgeArc Hdraw f ⊆ outer →
      e ∉ E(B) → False

/-- Global uniqueness implies the weaker relative no-new-incidence condition. -/
theorem NonouterIncidenceUniqueAtBoundary.noNew
    {β : Type*} {H : Graph Plane β} {Hdraw : β → ℝ → Plane} {outer : Set Plane}
    (h : NonouterIncidenceUniqueAtBoundary H Hdraw outer) (base : Set Plane) :
    NoNewNonouterIncidenceAtBoundary base H Hdraw outer := by
  intro B hBH _ z e f hz he hf heinc hfinc henot hfnot heNew
  have hfH : f ∈ E(H) := hBH.edgeSet_mono hf
  have hfincH : H.Inc f z := (hBH.inc_congr hf).1 hfinc
  have hef : e = f := h hz he hfH heinc hfincH henot hfnot
  exact heNew (hef ▸ hf)

/-- An edge of a plane graph whose whole carrier is already covered by a subgraph is itself an
edge of that subgraph.  An interior point of the arc cannot be a subgraph vertex, nor lie on a
different subgraph edge, by the drawing intersection axioms. -/
theorem edge_mem_of_edgeArc_subset_pointSet
    {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
    (hdraw : G.IsDrawing drawing) (hBG : B ≤ G) {e : β} (he : e ∈ E(G))
    (hsub : edgeArc drawing e ⊆ pointSet B drawing) : e ∈ E(B) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have harc := hdraw.edge_isArcBetween hxy
  obtain ⟨p, hpArc, hpEnds⟩ := not_subset.1 harc.not_subset_pair
  rcases hsub hpArc with hpV | hpE
  · rcases hdraw.vertex_mem_edgeArc hxy (hBG.vertexSet_mono hpV) hpArc with rfl | rfl
    · exact absurd (Or.inl rfl) hpEnds
    · exact absurd (Or.inr rfl) hpEnds
  · obtain ⟨f, hfB, hpf⟩ := Set.mem_iUnion₂.1 hpE
    by_cases hef : e = f
    · exact hef ▸ hfB
    · obtain ⟨hpV, -, -⟩ :=
        hdraw.edge_inter he (hBG.edgeSet_mono hfB) hef hpArc hpf
      rcases hdraw.vertex_mem_edgeArc hxy hpV hpArc with rfl | rfl
      · exact absurd (Or.inl rfl) hpEnds
      · exact absurd (Or.inr rfl) hpEnds

/-- In a plane drawing, an edge carrier cannot be contained in the carrier of a distinct
edge. -/
theorem eq_of_edgeArc_subset
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    (hdraw : G.IsDrawing drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hsub : edgeArc drawing e ⊆ edgeArc drawing f) : e = f := by
  by_contra hef
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have harc := hdraw.edge_isArcBetween hxy
  obtain ⟨p, hpArc, hpEnds⟩ := not_subset.1 harc.not_subset_pair
  obtain ⟨hpV, -, -⟩ := hdraw.edge_inter he hf hef hpArc (hsub hpArc)
  rcases hdraw.vertex_mem_edgeArc hxy hpV hpArc with rfl | rfl
  · exact hpEnds (Or.inl rfl)
  · exact hpEnds (Or.inr rfl)

/-- Boundary anchoring is geometric, hence survives an injective change of the ambient edge
names. -/
theorem TargetBoundaryAnchored.relabelEdges {β δ : Type*} [Nonempty β]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane β} {Hdraw : β → ℝ → Plane} {f : β → δ}
    (h : TargetBoundaryAnchored P H Hdraw) (hf : InjOn f E(H)) :
    TargetBoundaryAnchored P (H.relabelEdges f hf) (H.relabelDrawing f Hdraw) := by
  intro d y hd hinc hy hnot
  obtain ⟨e, he, rfl⟩ := hd
  obtain ⟨g, hg, hge, hginc⟩ :=
    (Graph.relabelEdges_inc H f hf (f e) y).1 hinc
  have hgeq : g = e := hf hg he hge
  subst g
  apply h he hginc hy
  intro hsub
  apply hnot
  rwa [Graph.edgeArc_relabelDrawing hf he]

/-- Uniqueness of the nonouter boundary edge is likewise invariant under injective edge
relabelling. -/
theorem NonouterIncidenceUniqueAtBoundary.relabelEdges {β δ : Type*} [Nonempty β]
    {H : Graph Plane β} {Hdraw : β → ℝ → Plane} {outer : Set Plane}
    {f : β → δ} (h : NonouterIncidenceUniqueAtBoundary H Hdraw outer)
    (hf : InjOn f E(H)) :
    NonouterIncidenceUniqueAtBoundary
      (H.relabelEdges f hf) (H.relabelDrawing f Hdraw) outer := by
  intro z d k hz hd hk hdinc hkinc hdnot hknot
  obtain ⟨e, he, rfl⟩ := hd
  obtain ⟨g, hg, rfl⟩ := hk
  obtain ⟨e', he', he'f, he'inc⟩ :=
    (Graph.relabelEdges_inc H f hf (f e) z).1 hdinc
  obtain ⟨g', hg', hg'f, hg'inc⟩ :=
    (Graph.relabelEdges_inc H f hf (f g) z).1 hkinc
  have he'e : e' = e := hf he' he he'f
  have hg'g : g' = g := hf hg' hg hg'f
  subst e'
  subst g'
  apply congrArg f
  apply h hz he hg he'inc hg'inc
  · intro hsub
    apply hdnot
    rwa [Graph.edgeArc_relabelDrawing hf he]
  · intro hsub
    apply hknot
    rwa [Graph.edgeArc_relabelDrawing hf hg]

/-- The one-sided constructor data obtained by realizing the ambient target path. -/
structure TargetSideEarStepData (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (B H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) (a b : Plane) (D : List γ) where
  splitData : T.str.SplitData
  tgtPos : γ → Plane
  tgtDraw : γ → ℝ → Plane
  tgtCrosscut : splitData.EarCrosscut T.tgt tgtPos tgtDraw
  tgtEdgePolygonal : ∀ ⦃e⦄, e ∈ E(splitData.ear) →
    IsPolygonal (Graph.edgeArc tgtDraw e)
  /-- The two old abstract endpoints retain the orientation of the ambient target path. -/
  target_pos_source : T.tgt.pos splitData.source = a
  target_pos_target : T.tgt.pos splitData.target = b
  tgtEarSet_eq : splitData.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D
  vertexSet_subset :
    V(B.union (H.pathGraphOf a D)) ⊆
      V((splitData.realize T.tgt tgtPos tgtDraw tgtCrosscut).graph)

/-- Injectively rename a nontrivial ambient target ear with fresh abstract cells and realize it
as a crosscut of the target face that contains its open arc. -/
theorem exists_targetSideEarStepData [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
      H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
      (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
      (∀ g ∈ D, g ∉ E(B)) →
      ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
        IsTargetPartialTransferOf T P B Hdraw par →
        Nonempty (TargetSideEarStepData T B H Hdraw a b D) := by
  classical
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨u, v, F, hu, hv, huv, hua, hvb, hF, hinside, huF, hvF⟩ :=
    exists_target_face_of_ear hH hBH hpath hab haB hbB hint hnew hT
  let paths := T.str_boundaryCycles.boundaryPaths F hF u v hu hv huF hvF huv
  let Q : Graph Plane γ := H.pathGraphOf a D
  have hQle : Q ≤ H := Graph.pathGraphOf_le hpath.isWalk
  have hQpath : Q.IsPathGraph a D b := hpath.isPathGraph_pathGraphOf
  have haQ : a ∈ V(Q) := Graph.mem_vertexSet_pathGraphOf_self
  have hbQ : b ∈ V(Q) := by
    rw [Graph.pathGraphOf_vertexSet]
    exact hpath.target_mem_walkVertices
  have hQfinV : V(Q).Finite := hpath.isWalk.finite_vertexSet_pathGraphOf
  have hQfinE : E(Q).Finite := hpath.isWalk.finite_edgeSet_pathGraphOf
  have huCell : u ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hu
  have hvCell : v ∈ T.str.cells := T.str.mem_cells_of_mem_vertexSet hv
  obtain ⟨vname, vname_a, vname_b, vname_inj, vname_fresh⟩ :=
    exists_injective_pinned_avoiding T.str.finite_cells huCell hvCell huv hQfinV hab
  let newVertices : Set γ := vname '' (V(Q) \ {a, b})
  have hnewVertices_fin : newVertices.Finite := hQfinV.sdiff.image vname
  have hnewVertices_avoid : Disjoint newVertices T.str.cells := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨hxQ, hxab⟩, rfl⟩ hzCell
    exact vname_fresh x hxQ (fun h => hxab (Or.inl h)) (fun h => hxab (Or.inr h)) hzCell
  let edgeUsed : Set γ := T.str.cells ∪ newVertices
  have hedgeUsed_fin : edgeUsed.Finite := T.str.finite_cells.union hnewVertices_fin
  let _ : Finite E(Q) := Set.finite_coe_iff.mpr hQfinE
  obtain ⟨freshEdge, freshEdge_inj, freshEdge_avoid⟩ :=
    exists_injective_avoiding edgeUsed hedgeUsed_fin E(Q)
  let ename : γ → γ := fun e => if he : e ∈ E(Q) then freshEdge ⟨e, he⟩ else u
  have ename_apply {e : γ} (he : e ∈ E(Q)) : ename e = freshEdge ⟨e, he⟩ := by
    simp [ename, he]
  have ename_inj : InjOn ename E(Q) := by
    intro e he f hf hef
    have hsub : (⟨e, he⟩ : E(Q)) = ⟨f, hf⟩ := by
      apply freshEdge_inj
      calc
        freshEdge ⟨e, he⟩ = ename e := (ename_apply he).symm
        _ = ename f := hef
        _ = freshEdge ⟨f, hf⟩ := ename_apply hf
    exact congrArg (fun z : E(Q) => z.1) hsub
  have ename_avoid {e : γ} (he : e ∈ E(Q)) : ename e ∉ edgeUsed := by
    rw [ename_apply he]
    exact freshEdge_avoid ⟨e, he⟩
  let newEdges : Set γ := ename '' E(Q)
  have hnewEdges_fin : newEdges.Finite := hQfinE.image ename
  have hnewEdges_avoid : Disjoint newEdges edgeUsed := by
    rw [Set.disjoint_left]
    rintro z ⟨e, he, rfl⟩
    exact ename_avoid he
  let faceUsed : Set γ := edgeUsed ∪ newEdges
  have hfaceUsed_fin : faceUsed.Finite := hedgeUsed_fin.union hnewEdges_fin
  obtain ⟨freshFace, freshFace_inj, freshFace_avoid⟩ :=
    exists_injective_avoiding faceUsed hfaceUsed_fin (Fin 2)
  let face₁ : γ := freshFace 0
  let face₂ : γ := freshFace 1
  let relabelled : Graph Plane γ := Q.relabelEdges ename ename_inj
  let ear : Graph γ γ := relabelled.map vname
  have hVear : V(ear) = vname '' V(Q) := by simp [ear, relabelled]
  have hEear : E(ear) = ename '' E(Q) := by simp [ear, relabelled]
  have hearPath : ear.IsPathGraph u (D.map ename) v := by
    have hrel := hQpath.relabelEdges ename_inj
    have hmap := hrel.map (by simpa [relabelled] using vname_inj)
    simpa [ear, relabelled, vname_a, vname_b] using hmap
  have hear_disjoint : Disjoint V(ear) E(ear) := by
    rw [Set.disjoint_left]
    rintro z hzV hzE
    rw [hVear] at hzV
    rw [hEear] at hzE
    obtain ⟨x, hxQ, rfl⟩ := hzV
    obtain ⟨e, heQ, heq⟩ := hzE
    have hedgeAvoid := ename_avoid heQ
    apply hedgeAvoid
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl (by rw [heq, vname_a]; exact huCell)
    rcases eq_or_ne x b with rfl | hxb
    · exact Or.inl (by rw [heq, vname_b]; exact hvCell)
    · exact Or.inr ⟨x, ⟨hxQ, by simp [hxa, hxb]⟩, heq.symm⟩
  have hvertex_inter : V(ear) ∩ V(T.str.skel) = {u, v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzEar, hzOld⟩
      rw [hVear] at hzEar
      obtain ⟨x, hxQ, rfl⟩ := hzEar
      rcases eq_or_ne x a with rfl | hxa
      · simp [vname_a]
      rcases eq_or_ne x b with rfl | hxb
      · simp [vname_b]
      exfalso
      exact vname_fresh x hxQ hxa hxb (T.str.mem_cells_of_mem_vertexSet hzOld)
    · rintro z (rfl | rfl)
      · exact ⟨hVear ▸ ⟨a, haQ, vname_a⟩, hu⟩
      · exact ⟨hVear ▸ ⟨b, hbQ, vname_b⟩, hv⟩
  have hface₁Avoid : face₁ ∉ faceUsed := freshFace_avoid 0
  have hface₂Avoid : face₂ ∉ faceUsed := freshFace_avoid 1
  let d : T.str.SplitData := {
    face := F
    face₁ := face₁
    face₂ := face₂
    ear := ear
    source := u
    target := v
    earWalk := D.map ename
    path₁ := paths.path₁
    path₂ := paths.path₂
    isPathGraph := hearPath
    isPath₁ := paths.isPath₁
    isPath₂ := paths.isPath₂
    ear_disjoint := hear_disjoint
    source_ne_target := huv
    face_mem := hF
    vertexSet_inter := hvertex_inter
    edge_fresh := by
      intro e he
      rw [hEear] at he
      obtain ⟨f, hf, rfl⟩ := he
      exact fun hmem => ename_avoid hf (Or.inl hmem)
    vertex_fresh := by
      intro z hz hzu hzv
      rw [hVear] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxa : x ≠ a := fun h => hzu (h ▸ vname_a)
      have hxb : x ≠ b := fun h => hzv (h ▸ vname_b)
      exact vname_fresh x hx hxa hxb
    face₁_notMem := fun h => hface₁Avoid (Or.inl (Or.inl h))
    face₂_notMem := fun h => hface₂Avoid (Or.inl (Or.inl h))
    face₁_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₁Avoid (Or.inl (Or.inl (show face₁ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₁Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₁Avoid (Or.inr hz)
    face₂_notMem_ear := by
      rintro (hz | hz)
      · rw [hVear] at hz
        obtain ⟨x, hx, heq⟩ := hz
        rcases eq_or_ne x a with rfl | hxa
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_a]; exact huCell)))
        rcases eq_or_ne x b with rfl | hxb
        · apply hface₂Avoid (Or.inl (Or.inl (show face₂ ∈ T.str.cells by
            rw [← heq, vname_b]; exact hvCell)))
        · exact hface₂Avoid (Or.inl (Or.inr ⟨x, ⟨hx, by simp [hxa, hxb]⟩, heq⟩))
      · rw [hEear] at hz
        exact hface₂Avoid (Or.inr hz)
    face_ne := fun h => Fin.zero_ne_one (freshFace_inj h)
    sub_face := paths.sub_face
    paths_meet := paths.paths_meet
  }
  let tgtPos : γ → Plane := Function.invFunOn vname V(Q)
  let tgtDraw : γ → ℝ → Plane := Graph.relabelDrawing Q ename Hdraw
  have hQdraw : Graph.IsDrawing Q Hdraw := hH.isDrawing.mono hQle
  have hrelDraw : Graph.IsDrawing relabelled tgtDraw := hQdraw.relabelEdges ename_inj
  have hearGraph : d.earGraph tgtPos = relabelled := by
    change (relabelled.map vname).map tgtPos = relabelled
    simpa [tgtPos, relabelled] using
      (Graph.map_map_invFunOn (G := relabelled) (f := vname)
        (by simpa [relabelled] using vname_inj))
  have htgtSet : d.earSet tgtPos tgtDraw = Graph.edgesCover Hdraw D := by
    rw [CellStructure.SplitData.earSet, hearGraph, Graph.pointSet_relabelEdges ename_inj]
    simpa [Q] using hH.isDrawing.pointSet_pathGraphOf hpath.isWalk (hpath.ne_nil hab)
  have htgtEdgeOrig := target_ear_edge_polygonal hH hpath hF hinside
  have htgtEdgePoly : ∀ ⦃e⦄, e ∈ E(d.ear) →
      IsPolygonal (Graph.edgeArc tgtDraw e) := by
    intro e he
    change e ∈ E(ear) at he
    rw [hEear] at he
    obtain ⟨f, hfQ, rfl⟩ := he
    rw [Graph.edgeArc_relabelDrawing ename_inj hfQ]
    apply htgtEdgeOrig f
    rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ
  have htgtPoly : IsPolygonal (d.earSet tgtPos tgtDraw) := by
    rw [htgtSet]
    exact hQdraw.isPolygonal_edgesCover
      (fun f hfQ => htgtEdgeOrig f (by
        rwa [Graph.pathGraphOf_edgeSet hpath.isWalk] at hfQ))
      hpath.pathGraphOf.isWalk (hpath.ne_nil hab)
  have htgt : d.EarCrosscut T.tgt tgtPos tgtDraw := {
    pos_source := by
      change tgtPos u = T.tgt.pos u
      rw [hua]
      change Function.invFunOn vname V(Q) u = a
      rw [← vname_a, vname_inj.leftInvOn_invFunOn haQ]
    pos_target := by
      change tgtPos v = T.tgt.pos v
      rw [hvb]
      change Function.invFunOn vname V(Q) v = b
      rw [← vname_b, vname_inj.leftInvOn_invFunOn hbQ]
    injOn := by
      change InjOn (Function.invFunOn vname V(Q)) V(ear)
      rw [hVear]
      exact Function.invFunOn_injOn_image vname V(Q)
    isDrawing := by rw [hearGraph]; exact hrelDraw
    subset_face := by
      rw [htgtSet]
      simpa [d, hua, hvb] using hinside
    disjoint_skeleton := T.tgt.disjoint_cell_skeletonSet T.tgt_isCellDecomposition hF
    polygonal := htgtPoly
  }
  refine ⟨{
    splitData := d
    tgtPos := tgtPos
    tgtDraw := tgtDraw
    tgtCrosscut := htgt
    tgtEdgePolygonal := htgtEdgePoly
    target_pos_source := hua
    target_pos_target := hvb
    tgtEarSet_eq := htgtSet
    vertexSet_subset := ?_
  }⟩
  change V(B.union (H.pathGraphOf a D)) ⊆
    V((T.str.splitFace d).skel.map (d.splitPos T.tgt tgtPos))
  rw [htgt.splitGraph_eq]
  intro x hx
  rcases hx with hxB | hxQ
  · exact Or.inl (hT.vertexSet_subset hxB)
  · apply Or.inr
    rw [hearGraph, Graph.vertexSet_relabelEdges]
    exact hxQ

/-- The skeleton homeomorphism sends an abstract vertex on the source outer curve to the
corresponding abstract vertex on the target outer curve. -/
theorem GeneratedPair.target_pos_mem_outer_of_source_pos_mem_outer
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v : γ}
    (hv : v ∈ V(T.str.skel)) (hx : T.src.pos v ∈ srcOuter) :
    T.tgt.pos v ∈ tgtOuter := by
  have hxOuter : T.src.pos v ∈ T.src.outerSet :=
    T.src_isWeaklyAdmissible.outerSet_eq.symm ▸ hx
  have himage : T.homeo.toFun (T.src.pos v) ∈ T.tgt.outerSet := by
    rw [← T.homeo.image_outerSet]
    exact Set.mem_image_of_mem T.homeo.toFun hxOuter
  rw [T.homeo.pos_apply hv] at himage
  rwa [T.tgt_isWeaklyAdmissible.outerSet_eq] at himage

/-- The relative anchored-boundary condition supplies the strong-accessibility half of
readiness at both outer endpoints of a nontrivial target ear.  Compatibility of the evolving
skeleton map with the original one identifies those endpoints with the original inverse
images. -/
theorem targetEarEndpointStronglyAccessible_of_newBoundaryAnchored
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    {a b : Plane} {D : List γ} {par : γ → γ}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hBH : B ≤ H) (hnew : ∀ g ∈ D, g ∉ E(B))
    (hpath : H.IsPath a D b) (hab : a ≠ b)
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (w : TargetSideEarStepData T B H Hdraw a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      StronglyAccessible (srcDom \ srcOuter) (T.src.pos w.splitData.source)) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      StronglyAccessible (srcDom \ srcOuter) (T.src.pos w.splitData.target)) := by
  let d := w.splitData
  have hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆ T.tgt.cell d.face := by
    intro x hx
    apply w.tgtCrosscut.subset_face
    refine ⟨?_, ?_⟩
    · rw [w.tgtEarSet_eq]
      exact hx.1
    · simpa only [w.target_pos_source, w.target_pos_target] using hx.2
  have hnotOuter := target_ear_edge_not_outer hH hpath d.face_mem hinside
  obtain ⟨eₛ, heₛ, hincₛ⟩ :=
    hpath.isWalk.exists_inc_source (hpath.ne_nil hab)
  obtain ⟨eₜ, heₜ, hincₜ⟩ :=
    hpath.reverse.isWalk.exists_inc_source (hpath.reverse.ne_nil (Ne.symm hab))
  have heₜD : eₜ ∈ D := by simpa using heₜ
  have target_mem_original : ∀ {v : γ}, T.tgt.pos v ∈ tgtOuter →
      T.tgt.pos v ∈ P.tgt.skeletonSet := by
    intro v hv
    apply P.tgt.outerSet_subset_skeletonSet
    exact (Set.ext_iff.mp P.tgt_isWeaklyAdmissible.outerSet_eq (T.tgt.pos v)).mpr hv
  constructor
  · intro hx
    have hy := T.target_pos_mem_outer_of_source_pos_mem_outer d.source_mem_skel hx
    have haOuter : a ∈ tgtOuter := by rwa [← w.target_pos_source]
    rw [hT.source_pos_eq_invFun_target_pos d.source_mem_skel
      (target_mem_original hy), w.target_pos_source]
    exact hanchor hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      (hpath.edge_mem heₛ) (hnew eₛ heₛ) hincₛ haOuter (hnotOuter eₛ heₛ)
  · intro hx
    have hy := T.target_pos_mem_outer_of_source_pos_mem_outer d.target_mem_skel hx
    have hbOuter : b ∈ tgtOuter := by rwa [← w.target_pos_target]
    rw [hT.source_pos_eq_invFun_target_pos d.target_mem_skel
      (target_mem_original hy), w.target_pos_target]
    exact hanchor hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      (hpath.edge_mem heₜD) (hnew eₜ heₜD) hincₜ hbOuter (hnotOuter eₜ heₜD)

/-! ### The exact geometric obligation on the source side -/

/-- An abstract skeleton vertex is outer-only when every current edge incident with it belongs
to the distinguished outer graph. -/
def CellStructure.OuterOnlyAt (S : CellStructure γ) (v : γ) : Prop :=
  ∀ {e : γ}, S.skel.Inc e v → e ∈ E(S.outerGraph)

/-- At most two distinct outer edges are incident with the vertex.  This is the exact local
consequence of "the distinguished outer graph is a cycle" used by reverse transfer. -/
def CellStructure.OuterIncidenceAtMostTwo (S : CellStructure γ) (v : γ) : Prop :=
  ∀ ⦃e f g : γ⦄, S.outerGraph.Inc e v → S.outerGraph.Inc f v →
    S.outerGraph.Inc g v → e = f ∨ e = g ∨ f = g

/-- The distinguished outer graph is locally at most two-branched at every vertex. -/
def CellStructure.OuterIncidenceAtMostTwoEverywhere (S : CellStructure γ) : Prop :=
  ∀ v, S.OuterIncidenceAtMostTwo v

/-- The edge set of the distinguished outer graph is exactly one simple cycle.  Isolated
vertices are intentionally irrelevant: reverse transfer only reads edge incidence. -/
def CellStructure.OuterEdgesFormCycle (S : CellStructure γ) : Prop :=
  ∃ e u v D, S.outerGraph.IsCycleThrough e u v D ∧
    E(S.outerGraph) = {f | f ∈ e :: D}

/-- A graph whose outer edges form one simple cycle is locally at most two-branched.  Rotate
the cycle to one incident edge; every other edge at that endpoint lies on the complementary
simple path, which has only one incident edge at either end. -/
theorem CellStructure.OuterEdgesFormCycle.outerIncidenceAtMostTwoEverywhere
    {S : CellStructure γ} (h : S.OuterEdgesFormCycle) :
    S.OuterIncidenceAtMostTwoEverywhere := by
  obtain ⟨e, u, v, D, hc, hE⟩ := h
  intro z f g k hf hg hk
  have hfC : f ∈ e :: D := by
    change f ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hf.edge_mem
  have hgC : g ∈ e :: D := by
    change g ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hg.edge_mem
  have hkC : k ∈ e :: D := by
    change k ∈ ({f | f ∈ e :: D} : Set γ)
    rw [← hE]
    exact hk.edge_mem
  obtain ⟨a, b, W, hrot, hperm⟩ := hc.rotate hfC
  have hg' : g = f ∨ g ∈ W := List.mem_cons.1 (hperm.mem_iff.2 hgC)
  have hk' : k = f ∨ k ∈ W := List.mem_cons.1 (hperm.mem_iff.2 hkC)
  rcases hf.eq_or_eq_of_isLink hrot.isLink with rfl | rfl
  · rcases hg' with rfl | hgW
    · exact Or.inl rfl
    rcases hk' with rfl | hkW
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr
        (hrot.isPath.inc_source_unique hgW hkW hg hk))
  · rcases hg' with rfl | hgW
    · exact Or.inl rfl
    rcases hk' with rfl | hkW
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hrot.isPath.reverse.inc_source_unique
        (by simpa using hgW) (by simpa using hkW) hg hk))

namespace CellStructure.SubdivData

/-- Every abstract walk admits the orientation-aware edge substitution prescribed by a
subdivision. -/
theorem exists_substWalk_of_isWalk {S : CellStructure γ} (d : S.SubdivData)
    {u v : γ} {W : List γ} (hW : S.skel.IsWalk u W v) :
  ∃ W', d.SubstWalk u W W' := by
  induction hW with
  | nil _ =>
      refine ⟨[], ?_⟩
      exact CellStructure.SubstWalk.nil (S := S) (edge := d.edge)
        (left := d.left) (right := d.right) (newEdge₁ := d.newEdge₁)
        (newEdge₂ := d.newEdge₂) _
  | @cons u w v f W hl hW ih =>
      obtain ⟨W', hsub⟩ := ih
      by_cases hfe : f = d.edge
      · subst f
        rcases hl.eq_and_eq_or_eq_and_eq d.isLink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨d.newEdge₁ :: d.newEdge₂ :: W', .forward hsub⟩
        · exact ⟨d.newEdge₂ :: d.newEdge₁ :: W', .backward hsub⟩
      · exact ⟨f :: W', .other hl hfe hsub⟩

/-- If the subdivided edge occurs in the input, both replacement edges occur in the output. -/
theorem SubstWalk.newEdges_mem_output_of_mem_input {S : CellStructure γ}
    {d : S.SubdivData} {u : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    d.newEdge₁ ∈ W' ∧ d.newEdge₂ ∈ W' := by
  induction hsub with
  | nil => simp at he
  | forward => simp
  | backward => simp
  | @other u w f W W' hl hne hs ih =>
      have heW : d.edge ∈ W := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hne
        · exact h
      exact ⟨List.mem_cons_of_mem _ (ih heW).1, List.mem_cons_of_mem _ (ih heW).2⟩

/-- With the subdivided edge present, the output edge names are exactly the two replacements
and the surviving input names. -/
theorem SubstWalk.mem_output_iff_of_mem_input {S : CellStructure γ}
    {d : S.SubdivData} {u x : γ} {W W' : List γ}
    (hsub : d.SubstWalk u W W') (he : d.edge ∈ W) :
    x ∈ W' ↔ x = d.newEdge₁ ∨ x = d.newEdge₂ ∨ (x ∈ W ∧ x ≠ d.edge) := by
  constructor
  · intro hx
    rcases hsub.mem_input_of_mem_output hx with rfl | rfl | hxW
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hxW, fun h => hsub.edge_notMem_output (h ▸ hx)⟩)
  · rintro (rfl | rfl | ⟨hxW, hne⟩)
    · exact (hsub.newEdges_mem_output_of_mem_input he).1
    · exact (hsub.newEdges_mem_output_of_mem_input he).2
    · exact hsub.mem_output_of_mem_input_of_ne hxW hne

/-- Edge subdivision preserves the fact that the distinguished outer edges form one simple
cycle.  When the subdivided edge is outer, substitute it in the closed cycle walk and pull the
resulting cycle down from the new skeleton to the new outer graph. -/
theorem outerEdgesFormCycle {S : CellStructure γ} (d : S.SubdivData)
    (hcycle : S.OuterEdgesFormCycle) :
    (S.subdivideEdge d).OuterEdgesFormCycle := by
  by_cases heOuter : d.edge ∈ E(S.outerGraph)
  · obtain ⟨e, u, v, D, hc, hE⟩ := hcycle
    have heList : d.edge ∈ e :: D := by
      change d.edge ∈ ({f | f ∈ e :: D} : Set γ)
      rw [← hE]
      exact heOuter
    have hclosedOuter : S.outerGraph.IsWalk v (e :: D) v :=
      .cons hc.isLink.symm hc.isPath.isWalk
    have hclosed : S.skel.IsWalk v (e :: D) v := hclosedOuter.mono S.outerGraph_le
    obtain ⟨W', hsub⟩ := d.exists_substWalk_of_isWalk hclosed
    obtain ⟨e', u', D', hW', hc'⟩ :=
      SubstWalk.exists_isCycleThrough hsub hclosed (hc.mono S.outerGraph_le)
    have houtput : ∀ f ∈ W', f ∈ E(d.outer) := by
      intro f hf
      rw [d.outer_edgeSet_of_mem heOuter]
      rcases (hsub.mem_output_iff_of_mem_input heList).1 hf with rfl | rfl | ⟨hfC, hfe⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · have hfOld : f ∈ E(S.outerGraph) := by
          rw [hE]
          exact hfC
        have hfDiff : f ∈ E(S.outerGraph) \ {d.edge} := ⟨hfOld, by simpa using hfe⟩
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hfDiff)
    have hcOuter : d.outer.IsCycleThrough e' u' v D' := by
      apply hc'.anti d.outer_le_skeleton
      intro f hf
      exact houtput f (hW' ▸ hf)
    refine ⟨e', u', v, D', hcOuter, ?_⟩
    have hEdges : E(d.outer) = {f | f ∈ W'} := by
      ext f
      rw [d.outer_edgeSet_of_mem heOuter]
      change (f = d.newEdge₁ ∨ f = d.newEdge₂ ∨
          (f ∈ E(S.outerGraph) ∧ f ≠ d.edge)) ↔ f ∈ W'
      rw [hsub.mem_output_iff_of_mem_input heList]
      constructor
      · rintro (h | h | ⟨hf, hne⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by
            change f ∈ ({f | f ∈ e :: D} : Set γ)
            rwa [← hE], hne⟩)
      · rintro (h | h | ⟨hf, hne⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by
            rw [hE]
            exact hf, hne⟩)
    simpa only [CellStructure.subdivideEdge_outerGraph, hW'] using hEdges
  · unfold CellStructure.OuterEdgesFormCycle
    rw [CellStructure.subdivideEdge_outerGraph, d.outer_eq heOuter]
    exact hcycle

end CellStructure.SubdivData

/-- Splitting a face leaves the distinguished outer graph unchanged. -/
theorem CellStructure.SplitData.outerEdgesFormCycle {S : CellStructure γ}
    (d : S.SplitData) (hcycle : S.OuterEdgesFormCycle) :
    (S.splitFace d).OuterEdgesFormCycle := by
  unfold CellStructure.OuterEdgesFormCycle
  rw [CellStructure.splitFace_outerGraph]
  exact hcycle

/-- Every generated structure keeps one simple cycle as its distinguished outer edge set. -/
theorem GeneratedStructure.outerEdgesFormCycle {S₀ S : CellStructure γ}
    (h : GeneratedStructure S₀ S) (h₀ : S₀.OuterEdgesFormCycle) :
    S.OuterEdgesFormCycle := by
  induction h with
  | base => exact h₀
  | subdivideEdge _ d ih => exact d.outerEdgesFormCycle ih
  | splitFace _ d ih => exact d.outerEdgesFormCycle ih

/-- The local two-branch condition needed by square-mesh reverse transfer is therefore a
generated-structure invariant as soon as the base outer edges form a simple cycle. -/
theorem GeneratedStructure.outerIncidenceAtMostTwoEverywhere
    {S₀ S : CellStructure γ} (h : GeneratedStructure S₀ S)
    (h₀ : S₀.OuterEdgesFormCycle) : S.OuterIncidenceAtMostTwoEverywhere :=
  (h.outerEdgesFormCycle h₀).outerIncidenceAtMostTwoEverywhere

/-- A vertex on a nonloop simple cycle has two distinct incident cycle edges.  The face-cycle
application obtains nonloopness from either geometric realization. -/
theorem CellStructure.FaceCycle.exists_distinct_incident_edges
    {S : CellStructure γ} {F v : γ} (c : S.FaceCycle F)
    (hloopless : ∀ ⦃e x y : γ⦄, S.skel.IsLink e x y → x ≠ y)
    (hv : v ∈ V(S.skel)) (hvF : S.sub v F) :
    ∃ e f, e ≠ f ∧ e ∈ c.edge :: c.walk ∧ f ∈ c.edge :: c.walk ∧
      S.skel.Inc e v ∧ S.skel.Inc f v := by
  have hvW := c.mem_walk_of_vertex_sub hv hvF
  have huv : c.source ≠ c.target := hloopless c.isCycle.isLink
  by_cases hvu : v = c.source
  · subst hvu
    obtain ⟨f, hf, hfinc⟩ :=
      c.isCycle.isPath.isWalk.exists_inc_source (c.isCycle.isPath.ne_nil huv)
    exact ⟨c.edge, f, fun hef => c.isCycle.notMem (hef ▸ hf),
      List.mem_cons_self, List.mem_cons_of_mem _ hf, c.isCycle.isLink.inc_left, hfinc⟩
  by_cases hvq : v = c.target
  · subst hvq
    obtain ⟨f, hf, hfinc⟩ := c.isCycle.isPath.reverse.isWalk.exists_inc_source
      (c.isCycle.isPath.reverse.ne_nil (Ne.symm huv))
    have hfD : f ∈ c.walk := by simpa using hf
    exact ⟨c.edge, f, fun hef => c.isCycle.notMem (hef ▸ hfD),
      List.mem_cons_self, List.mem_cons_of_mem _ hfD, c.isCycle.isLink.inc_right, hfinc⟩
  obtain ⟨W₁, W₂, hwalk, h₁, h₂, -⟩ := c.isCycle.isPath.split hvW
  obtain ⟨e, he, heinc⟩ :=
    h₁.reverse.isWalk.exists_inc_source (h₁.reverse.ne_nil hvu)
  obtain ⟨f, hf, hfinc⟩ := h₂.isWalk.exists_inc_source (h₂.ne_nil hvq)
  have heW₁ : e ∈ W₁ := by simpa using he
  have hef : e ≠ f := by
    intro heq
    have hnodup : (W₁ ++ W₂).Nodup := hwalk ▸ c.isCycle.isPath.nodup
    apply List.disjoint_of_nodup_append hnodup heW₁
    rwa [heq]
  have heD : e ∈ c.walk := hwalk ▸ List.mem_append_left W₂ heW₁
  have hfD : f ∈ c.walk := hwalk ▸ List.mem_append_right W₁ hf
  exact ⟨e, f, hef, List.mem_cons_of_mem _ heD, List.mem_cons_of_mem _ hfD, heinc, hfinc⟩

/-- A nonouter edge of the evolving abstract skeleton incident at a current ambient vertex
produces a nonouter edge of the ambient graph incident at the same geometric point.  No edge
labels need to agree: a sufficiently small vertex square meets only ambient edges incident at
that vertex, while the open cell of the abstract edge accumulates at its endpoint. -/
theorem IsTargetPartialTransferOf.exists_ambient_nonouter_incident
    {P T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {B : Graph Plane γ} {Hdraw : γ → ℝ → Plane} {par : γ → γ}
    [B.Finite]
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (hBdraw : B.IsDrawing Hdraw) {v e : γ}
    (hvB : T.tgt.pos v ∈ V(B)) (hvOuter : T.tgt.pos v ∈ tgtOuter)
    (hinc : T.str.skel.Inc e v) (heOuter : e ∉ E(T.str.outerGraph)) :
    ∃ f ∈ E(B), B.Inc f (T.tgt.pos v) ∧
      ¬ edgeArc Hdraw f ⊆ tgtOuter := by
  obtain ⟨w, hl⟩ := hinc
  have harc := T.tgt.isDrawing.edge_isArcBetween (hl.map T.tgt.pos)
  have hclosure : T.tgt.pos v ∈ closure (T.tgt.cell e) := by
    rw [T.tgt.cell_edge hl]
    exact harc.left_mem_closure_diff
  obtain ⟨r, hr, hvert, hedge⟩ := hBdraw.exists_square_at hvB
  obtain ⟨z, hzNear, hzCell⟩ := mem_closure_iff.1 hclosure
    (Plane.openSquare (T.tgt.pos v) r) (Plane.isOpen_openSquare _ _)
    (Plane.mem_openSquare_self hr)
  have hzClosed : z ∈ Plane.closedSquare (T.tgt.pos v) r :=
    Plane.openSquare_subset_closedSquare _ _ hzNear
  have hzOuter : z ∉ tgtOuter :=
    (T.tgt_isWeaklyAdmissible.cell_subset hl.edge_mem heOuter hzCell).2
  have hzSkel : z ∈ T.tgt.skeletonSet :=
    T.tgt.cell_subset_skeletonSet (Or.inr hl.edge_mem) hzCell
  have hzB : z ∈ pointSet B Hdraw := by
    rw [← hT.skeletonSet_eq]
    exact hzSkel
  rcases hzB with hzV | hzE
  · have hzv : z = T.tgt.pos v := by
      by_contra hne
      exact hvert z hzV hne hzClosed
    exact absurd (hzv ▸ hvOuter) hzOuter
  · obtain ⟨f, hf, hzf⟩ := Set.mem_iUnion₂.1 hzE
    have hfinc : B.Inc f (T.tgt.pos v) := by
      by_contra hninc
      exact Set.disjoint_left.1 (hedge f hf hninc) hzClosed hzf
    exact ⟨f, hf, hfinc, fun hsub => hzOuter (hsub hzf)⟩

/-- If no new nonouter ambient edge can coexist at the boundary with a nonouter edge of the
current trace, then both boundary endpoints of the next reverse ear are outer-only in the
current abstract skeleton.  Any current nonouter abstract edge would reflect to just such a
current ambient edge. -/
theorem targetEarEndpointsOuterOnly_of_noNewNonouterIncidence
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    {B : Graph Plane γ} {a b : Plane} {D : List γ} {par : γ → γ}
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (w : TargetSideEarStepData T B H Hdraw a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.source) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.target) := by
  let _ : H.Finite := hH.finite
  let _ : B.Finite := Graph.Finite.of_le hBH
  have hBdraw := hH.isDrawing.mono hBH
  have hinside : Graph.edgesCover Hdraw D \ {a, b} ⊆
      T.tgt.cell w.splitData.face := by
    intro x hx
    apply w.tgtCrosscut.subset_face
    refine ⟨?_, ?_⟩
    · rw [w.tgtEarSet_eq]
      exact hx.1
    · simpa only [w.target_pos_source, w.target_pos_target] using hx.2
  have hnotOuter := target_ear_edge_not_outer hH hpath w.splitData.face_mem hinside
  obtain ⟨eₛ, heₛ, hincₛ⟩ :=
    hpath.isWalk.exists_inc_source (hpath.ne_nil hab)
  obtain ⟨eₜ, heₜ, hincₜ⟩ :=
    hpath.reverse.isWalk.exists_inc_source (hpath.reverse.ne_nil (Ne.symm hab))
  have heₜD : eₜ ∈ D := by simpa using heₜ
  have endpoint_outerOnly : ∀ {v : γ} {y : Plane} {e : γ},
      v ∈ V(T.str.skel) → T.tgt.pos v = y → y ∈ V(B) →
      e ∈ D → H.Inc e y → ¬ edgeArc Hdraw e ⊆ tgtOuter →
      T.src.pos v ∈ srcOuter → T.str.OuterOnlyAt v := by
    intro v y e hv hpos hyB heD heinc henot hx
    have hyOuter : y ∈ tgtOuter := by
      rw [← hpos]
      exact T.target_pos_mem_outer_of_source_pos_mem_outer hv hx
    intro g hg
    by_contra hgOuter
    have hvB : T.tgt.pos v ∈ V(B) := by rwa [hpos]
    have hvOuter : T.tgt.pos v ∈ tgtOuter := by rwa [hpos]
    obtain ⟨f, hfB, hfincB, hfnot⟩ :=
      hT.exists_ambient_nonouter_incident hBdraw hvB hvOuter hg hgOuter
    exact hnoNew hBH (by rw [← hT.skeletonSet_eq]; exact hT.targetSkeletonSet_subset)
      hyOuter (hpath.edge_mem heD) hfB heinc
      (hpos ▸ hfincB) henot hfnot (hnew e heD)
  constructor
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.source) (y := a) (e := eₛ)
      w.splitData.source_mem_skel w.target_pos_source haB
      heₛ hincₛ (hnotOuter eₛ heₛ) hx
  · intro hx
    exact endpoint_outerOnly (v := w.splitData.target) (y := b) (e := eₜ)
      w.splitData.target_mem_skel w.target_pos_target hbB
      heₜD hincₜ (hnotOuter eₜ heₜD) hx

/-- Global uniqueness of the nonouter ambient edge is a convenient sufficient condition for
the relative boundary-incidence hypothesis used above. -/
theorem targetEarEndpointsOuterOnly_of_nonouterIncidenceUnique
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hunique : NonouterIncidenceUniqueAtBoundary H Hdraw tgtOuter)
    {B : Graph Plane γ} {a b : Plane} {D : List γ} {par : γ → γ}
    (hBH : B ≤ H) (hpath : H.IsPath a D b) (hab : a ≠ b)
    (haB : a ∈ V(B)) (hbB : b ∈ V(B))
    (hnew : ∀ g ∈ D, g ∉ E(B))
    {T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    (hT : IsTargetPartialTransferOf T P B Hdraw par)
    (w : TargetSideEarStepData T B H Hdraw a b D) :
    (T.src.pos w.splitData.source ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.source) ∧
    (T.src.pos w.splitData.target ∈ srcOuter →
      T.str.OuterOnlyAt w.splitData.target) :=
  targetEarEndpointsOuterOnly_of_noNewNonouterIncidence
    P hH (hunique.noNew P.tgt.skeletonSet) hBH hpath hab haB hbB hnew hT w

/-- At an outer-only vertex with at most two outer branches, the selected incident face is the
only incident face.  Each simple face boundary contributes two distinct edges at the vertex;
the two-branch bound forces two such face boundaries to share an outer edge, and
`CombInvariants.outerEdge_unique` then identifies their face names. -/
theorem GeneratedPair.unique_source_face_of_outerOnly
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v F : γ}
    (hv : v ∈ V(T.str.skel)) (hF : F ∈ T.str.faces) (hvF : T.str.sub v F)
    (houter : T.str.OuterOnlyAt v) (htwo : T.str.OuterIncidenceAtMostTwo v) :
    ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
      T.src.pos v ∈ closure R → R = T.src.cell F := by
  have hloopless : ∀ ⦃e x y : γ⦄, T.str.skel.IsLink e x y → x ≠ y := by
    intro e x y hxy hxyEq
    exact T.tgt.isDrawing.ne_of_isLink (hxy.map T.tgt.pos) (congrArg T.tgt.pos hxyEq)
  have face_edges : ∀ {Z : γ}, Z ∈ T.str.faces → T.str.sub v Z →
      ∃ e f, e ≠ f ∧ T.str.outerGraph.Inc e v ∧ T.str.outerGraph.Inc f v ∧
        T.str.sub e Z ∧ T.str.sub f Z := by
    intro Z hZ hvZ
    let c := T.str_boundaryCycles.faceCycle Z hZ
    obtain ⟨e, f, hef, heC, hfC, heinc, hfinc⟩ :=
      c.exists_distinct_incident_edges hloopless hv hvZ
    have heOuter : e ∈ E(T.str.outerGraph) := houter heinc
    have hfOuter : f ∈ E(T.str.outerGraph) := houter hfinc
    exact ⟨e, f, hef, (T.str.outerGraph_le.inc_congr heOuter).2 heinc,
      (T.str.outerGraph_le.inc_congr hfOuter).2 hfinc,
      c.sub_of_mem_pathCells (Or.inl heC), c.sub_of_mem_pathCells (Or.inl hfC)⟩
  obtain ⟨e₁, e₂, he₁₂, he₁inc, he₂inc, he₁F, -⟩ := face_edges hF hvF
  intro R hR hvR
  obtain ⟨Z, hZ, rfl⟩ := hR
  have hvZ : T.str.sub v Z :=
    T.src_isCellDecomposition.sub_of_pos_mem_closure_cell hv hZ hvR
  obtain ⟨f₁, f₂, hf₁₂, hf₁inc, hf₂inc, hf₁Z, hf₂Z⟩ := face_edges hZ hvZ
  have hcommon : e₁ = f₁ ∨ e₁ = f₂ := by
    rcases htwo he₁inc he₂inc hf₁inc with hbad | h | h
    · exact absurd hbad he₁₂
    · exact Or.inl h
    · rcases htwo he₁inc he₂inc hf₂inc with hbad | h' | hbad'
      · exact absurd hbad he₁₂
      · exact Or.inr h'
      · exact absurd (h.symm.trans hbad') hf₁₂
  have he₁Outer : e₁ ∈ E(T.str.outerGraph) := he₁inc.edge_mem
  obtain ⟨Q, hQ, huniq⟩ := T.str_combInvariants.outerEdge_unique he₁Outer
  have he₁Z : T.str.sub e₁ Z := hcommon.elim
    (fun h => h ▸ hf₁Z) (fun h => h ▸ hf₂Z)
  exact congrArg T.src.cell
    ((huniq Z ⟨hZ, he₁Z⟩).trans (huniq F ⟨hF, he₁F⟩).symm)

/-- Source vertices incident with a nonboundary edge.  Outer-only vertices are deliberately
excluded: a fresh anchor must not enter the compact set merely because it is already a vertex
of the outer cycle. -/
def GeneratedPair.sourceNonboundaryVertices
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Set Plane :=
  {x | ∃ e, e ∈ E(T.src.graph) ∧ e ∉ E(T.str.outerGraph) ∧ T.src.graph.Inc e x}

/-- The current source graph with outer edges and outer-only vertices removed.  Its point set is
the compact union of the closed nonboundary edges used in the fresh-anchor argument. -/
def GeneratedPair.sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) : Graph Plane γ :=
  (T.src.graph.deleteEdges E(T.str.outerGraph)).induce T.sourceNonboundaryVertices

theorem GeneratedPair.sourceNonboundaryGraph_le
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph ≤ T.src.graph := by
  apply (Graph.induce_le ?_).trans Graph.deleteEdges_le
  rintro x ⟨e, -, -, hinc⟩
  exact hinc.vertex_mem

instance GeneratedPair.sourceNonboundaryGraph_finite
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.sourceNonboundaryGraph.Finite :=
  Graph.Finite.of_le T.sourceNonboundaryGraph_le

/-- An outer-only abstract vertex is absent from the compact nonboundary-edge carrier.  The
point-set statement includes the possible case where the vertex lies on the arc of an edge;
the drawing axiom turns that case back into incidence with the same edge. -/
theorem GeneratedPair.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {v : γ}
    (hv : v ∈ V(T.str.skel)) (houter : T.str.OuterOnlyAt v) :
    T.src.pos v ∉ pointSet T.sourceNonboundaryGraph T.src.drawing := by
  have abstract_incident : ∀ {e : γ}, T.src.graph.Inc e (T.src.pos v) →
      T.str.skel.Inc e v := by
    intro e hinc
    change (T.str.skel.map T.src.pos).Inc e (T.src.pos v) at hinc
    rw [Graph.map_inc] at hinc
    obtain ⟨w, hincw, hvw⟩ := hinc
    have heq : v = w := T.src.injOn_pos hv hincw.vertex_mem hvw
    rwa [heq]
  intro hx
  rcases hx with hxV | hxE
  · change T.src.pos v ∈ T.sourceNonboundaryVertices at hxV
    obtain ⟨e, -, heOuter, hinc⟩ := hxV
    exact heOuter (houter (abstract_incident hinc))
  · obtain ⟨e, heCore, hxe⟩ := Set.mem_iUnion₂.1 hxE
    change e ∈ E((T.src.graph.deleteEdges E(T.str.outerGraph)).induce
      T.sourceNonboundaryVertices) at heCore
    obtain ⟨p, q, hpq⟩ :=
      (T.src.graph.deleteEdges E(T.str.outerGraph)).induce
        T.sourceNonboundaryVertices |>.exists_isLink_of_mem_edgeSet heCore
    have heDeleted : e ∈ E(T.src.graph.deleteEdges E(T.str.outerGraph)) := hpq.1.edge_mem
    obtain ⟨heSrc, heOuter⟩ := Graph.mem_edgeSet_deleteEdges_iff.1 heDeleted
    obtain ⟨x, y, hxy⟩ := T.src.graph.exists_isLink_of_mem_edgeSet heSrc
    have hvSrc : T.src.pos v ∈ V(T.src.graph) := by
      rw [CellStructure.Realization.vertexSet_graph]
      exact ⟨v, hv, rfl⟩
    have hinc : T.src.graph.Inc e (T.src.pos v) := by
      rcases T.src.isDrawing.vertex_mem_edgeArc hxy hvSrc hxe with h | h
      · exact h ▸ hxy.inc_left
      · exact h ▸ hxy.inc_right
    exact heOuter (houter (abstract_incident hinc))

/-- The source skeleton is the union of its compact nonboundary-edge carrier and its outer
curve. -/
theorem GeneratedPair.skeletonSet_eq_sourceNonboundaryGraph_union
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    T.src.skeletonSet = pointSet T.sourceNonboundaryGraph T.src.drawing ∪ srcOuter := by
  have hdecomp : T.src.skeletonSet =
      pointSet T.sourceNonboundaryGraph T.src.drawing ∪ T.src.outerSet := by
    apply Set.Subset.antisymm
    · intro x hx
      change x ∈ pointSet T.src.graph T.src.drawing at hx
      rcases hx with hxV | hxE
      · obtain ⟨e, he, hinc⟩ : ∃ e, e ∈ E(T.src.graph) ∧ T.src.graph.Inc e x := by
          obtain ⟨z, hz, hzx, -⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.hasThreeVertices.exists_ne_ne x x
          obtain ⟨D, hD⟩ :=
            T.src_isWeaklyAdmissible.isTwoConnected.connected.exists_isPath hxV hz
          obtain ⟨e, heD, hinc⟩ :=
            hD.isWalk.exists_inc_source (hD.ne_nil (Ne.symm hzx))
          exact ⟨e, hD.edge_mem heD, hinc⟩
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · apply Or.inr
          apply Graph.vertexSet_subset_pointSet
          have hOle : T.str.outerGraph.map T.src.pos ≤ T.src.graph :=
            T.str.outerGraph_le.map T.src.pos
          exact ((hOle.inc_congr (by rwa [Graph.edgeSet_map])).2 hinc).vertex_mem
        · apply Or.inl
          apply Graph.vertexSet_subset_pointSet
          exact ⟨e, he, heOuter, hinc⟩
      · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxE
        by_cases heOuter : e ∈ E(T.str.outerGraph)
        · exact Or.inr (Graph.edgeArc_subset_pointSet (by
            rw [Graph.edgeSet_map]
            exact heOuter) hxe)
        · apply Or.inl
          exact Graph.edgeArc_subset_pointSet (by
            obtain ⟨u, v, huv⟩ := T.src.graph.exists_isLink_of_mem_edgeSet he
            exact ⟨u, v, ⟨⟨huv, heOuter⟩,
              ⟨e, he, heOuter, huv.inc_left⟩, ⟨e, he, heOuter, huv.inc_right⟩⟩⟩) hxe
    · exact Set.union_subset
        (Graph.pointSet_mono T.sourceNonboundaryGraph_le)
        T.src.outerSet_subset_skeletonSet
  exact hdecomp.trans (congrArg (pointSet T.sourceNonboundaryGraph T.src.drawing ∪ ·)
    T.src_isWeaklyAdmissible.outerSet_eq)

theorem GeneratedPair.isCompact_sourceNonboundaryGraph
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    IsCompact (pointSet T.sourceNonboundaryGraph T.src.drawing) :=
  (T.src.isDrawing.mono T.sourceNonboundaryGraph_le).isCompact_pointSet

/-- Inside the open Jordan domain, avoiding the compact nonboundary-edge carrier is equivalent
to avoiding the whole current skeleton; the remaining part of the latter is the outer curve. -/
theorem GeneratedPair.source_cellsAbsorbIn_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) :
    CellsAbsorbIn (srcDom \ srcOuter)
      (pointSet T.sourceNonboundaryGraph T.src.drawing)
      {A | ∃ F ∈ T.str.faces, A = T.src.cell F} := by
  intro N hND hN hNdisj R hR hmeet
  apply (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    N hN ?_ R hR hmeet
  rw [Set.disjoint_left]
  intro x hxN hxSkel
  rw [T.skeletonSet_eq_sourceNonboundaryGraph_union] at hxSkel
  rcases hxSkel with hxCore | hxOuter
  · exact Set.disjoint_left.1 hNdisj hxN hxCore
  · exact (hND hxN).2 hxOuter

/-- Every point of the open source domain outside the compact nonboundary-edge carrier lies in
one current source face. -/
theorem GeneratedPair.exists_source_face_of_mem_interior_notMem_nonboundary
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) {x : Plane}
    (hx : x ∈ srcDom \ srcOuter)
    (hxCore : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing) :
    ∃ R ∈ {A : Set Plane | ∃ F ∈ T.str.faces, A = T.src.cell F}, x ∈ R := by
  have hxSkel : x ∉ T.src.skeletonSet := by
    rw [T.skeletonSet_eq_sourceNonboundaryGraph_union]
    rintro (hcore | houter)
    · exact hxCore hcore
    · exact hx.2 houter
  have hxDom : x ∈ ⋃ σ ∈ T.str.cells, T.src.cell σ := by
    rw [T.src_isCellDecomposition.iUnion_eq]
    exact hx.1
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hxDom
  have hσFace : σ ∈ T.str.faces := by
    rcases hσ with (hv | he) | hface
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inl hv) hxσ) hxSkel
    · exact absurd (T.src.cell_subset_skeletonSet (Or.inr he) hxσ) hxSkel
    · exact hface
  exact ⟨T.src.cell σ, ⟨σ, hσFace, rfl⟩, hxσ⟩

/-- A fresh strongly accessible boundary anchor is accessible from its unique incident current
source face.  Compactness, absorption, and coverage are all discharged from the generated-pair
invariants; the three hypotheses are exactly the data maintained by the prescribed ear order. -/
theorem GeneratedPair.source_polyAccessible_of_fresh
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane}
    (hstrong : StronglyAccessible (srcDom \ srcOuter) x)
    (hfresh : x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing)
    (hunique : ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
      x ∈ closure R → R = T.src.cell F) :
    PolyAccessible (T.src.cell F) x := by
  exact polyAccessible_of_stronglyAccessible_in hstrong
    T.isCompact_sourceNonboundaryGraph hfresh T.source_cellsAbsorbIn_nonboundary
    (fun _ hy hycore =>
      T.exists_source_face_of_mem_interior_notMem_nonboundary hy hycore) hunique

/-- A point in the closure of a current source face is polygonally accessible whenever it is
off the wild outer curve.  The polygonal graph used by `polygonal_side_accessibility` is the
current skeleton with its outer edges deleted; adjoining the compact outer curve recovers the
whole source skeleton. -/
theorem GeneratedPair.source_polyAccessible_of_notMem_outer
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {F : γ} {x : Plane} (hF : F ∈ T.str.faces) (hx : x ∈ closure (T.src.cell F))
    (hxOuter : x ∉ srcOuter) : PolyAccessible (T.src.cell F) x := by
  let G := T.src.graph.deleteEdges E(T.str.outerGraph)
  let O := T.str.outerGraph.map T.src.pos
  have hOle : O ≤ T.src.graph := T.str.outerGraph_le.map T.src.pos
  have hGunion : G.union O = T.src.graph := by
    apply Graph.eq_of_le_of_subset_subset (Graph.union_le Graph.deleteEdges_le hOle)
    · intro z hz
      exact Or.inl (by rwa [Graph.vertexSet_deleteEdges])
    · intro e he
      by_cases heOuter : e ∈ E(T.str.outerGraph)
      · exact Or.inr (by rwa [Graph.edgeSet_map])
      · exact Or.inl (Graph.mem_edgeSet_deleteEdges_iff.2 ⟨he, heOuter⟩)
  have hK : T.src.skeletonSet = pointSet G T.src.drawing ∪ srcOuter := by
    change pointSet T.src.graph T.src.drawing = _
    rw [← hGunion, Graph.pointSet_union]
    change pointSet G T.src.drawing ∪ T.src.outerSet = _
    rw [T.src_isWeaklyAdmissible.outerSet_eq]
  let _ : G.Finite := Graph.Finite.of_le Graph.deleteEdges_le
  have hGdraw : G.IsDrawing T.src.drawing := T.src.isDrawing.mono Graph.deleteEdges_le
  have hGpoly : ∀ e ∈ E(G), IsPolygonal (edgeArc T.src.drawing e) := by
    intro e he
    rw [Graph.mem_edgeSet_deleteEdges_iff] at he
    exact T.src_isWeaklyAdmissible.isPolygonal he.1 he.2
  let cells : Set (Set Plane) := {A | ∃ Z ∈ T.str.faces, A = T.src.cell Z}
  have hFcells : T.src.cell F ∈ cells := ⟨F, hF, rfl⟩
  have hdisj : Disjoint (T.src.cell F) T.src.skeletonSet :=
    T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition hF
  let _ : O.Finite := Graph.Finite.of_le hOle
  have houterCompact : IsCompact srcOuter := by
    rw [← T.src_isWeaklyAdmissible.outerSet_eq]
    exact T.src.isCompact_skeletonSet.of_isClosed_subset
      (T.src.isDrawing.mono hOle).isClosed_pointSet T.src.outerSet_subset_skeletonSet
  exact Graph.polygonal_side_accessibility hGdraw hGpoly
    houterCompact hK (T.src_isCellDecomposition.cellsAbsorb T.src_isFaceJordan)
    hFcells hdisj hx hxOuter

/-- The two ways a source endpoint is ready for a reverse ear: it is off the wild curve, or it
is a fresh strongly accessible anchor incident with one prescribed current face. -/
def GeneratedPair.SourceEndpointReady
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (x : Plane) : Prop :=
  x ∉ srcOuter ∨
    StronglyAccessible (srcDom \ srcOuter) x ∧
      x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing ∧
      ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
        x ∈ closure R → R = T.src.cell F

/-- The two genuinely evolving obligations at a wild-boundary endpoint: no nonboundary edge
has reached it yet, and the next ear's face is its unique incident current source face. -/
def GeneratedPair.SourceEndpointFreshCombinatorics
    (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (F : γ) (x : Plane) : Prop :=
  x ∈ srcOuter →
    x ∉ pointSet T.sourceNonboundaryGraph T.src.drawing ∧
      ∀ R ∈ {A : Set Plane | ∃ Z ∈ T.str.faces, A = T.src.cell Z},
        x ∈ closure R → R = T.src.cell F

/-- The remaining prescribed-ear combinatorics after boundary anchoring has supplied strong
accessibility: both outer endpoints are fresh and incident with the selected face alone. -/
def TargetEarFreshCombinatorics [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        T.SourceEndpointFreshCombinatorics w.splitData.face
            (T.src.pos w.splitData.source) ∧
        T.SourceEndpointFreshCombinatorics w.splitData.face
            (T.src.pos w.splitData.target)

/-- The relative no-new-incidence boundary condition, together with the static two-branch
invariant of generated outer graphs, supplies all reverse-ear fresh combinatorics. -/
theorem targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo
    [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (htwo : ∀ (S : CellStructure γ), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    TargetEarFreshCombinatorics P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceOuterOnly, htargetOuterOnly⟩ :=
    targetEarEndpointsOuterOnly_of_noNewNonouterIncidence P hH hnoNew hBH hpath hab
      haB hbB hnew hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have htwoT := htwo T.str T.generated
  constructor
  · intro hx
    have houter : T.str.OuterOnlyAt d.source := hsourceOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.source_mem_skel houter,
      T.unique_source_face_of_outerOnly d.source_mem_skel d.face_mem hsourceSub
        houter (htwoT d.source)⟩
  · intro hx
    have houter : T.str.OuterOnlyAt d.target := htargetOuterOnly hx
    exact ⟨T.source_pos_notMem_nonboundaryGraph_of_outerOnlyAt d.target_mem_skel houter,
      T.unique_source_face_of_outerOnly d.target_mem_skel d.face_mem htargetSub
        houter (htwoT d.target)⟩

/-- Global uniqueness is a sufficient special case of the relative no-new-incidence
condition. -/
theorem targetEarFreshCombinatorics_of_nonouterIncidenceUnique_of_outerIncidenceAtMostTwo
    [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hunique : NonouterIncidenceUniqueAtBoundary H Hdraw tgtOuter)
    (htwo : ∀ (S : CellStructure γ), GeneratedStructure S₀ S →
      S.OuterIncidenceAtMostTwoEverywhere) :
    TargetEarFreshCombinatorics P H Hdraw :=
  targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo
    P hH (hunique.noNew P.tgt.skeletonSet) htwo

/-- The relative no-new-incidence condition and an outer cycle on the base structure supply
the reverse-ear fresh combinatorics. -/
theorem targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    TargetEarFreshCombinatorics P H Hdraw :=
  targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerIncidenceAtMostTwo
    P hH hnoNew fun _ h => h.outerIncidenceAtMostTwoEverywhere hcycle

/-- The preceding reverse-ear combinatorics follows from the natural base invariant that the
distinguished outer edges form one simple cycle. -/
theorem targetEarFreshCombinatorics_of_nonouterIncidenceUnique_of_outerCycle [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hunique : NonouterIncidenceUniqueAtBoundary H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    TargetEarFreshCombinatorics P H Hdraw :=
  targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle
    P hH (hunique.noNew P.tgt.skeletonSet) hcycle

/-- The combinatorial/anchoring invariant still required from the prescribed target ear order:
both source endpoints selected by every nontrivial target ear are ready in the preceding sense. -/
def TargetEarFreshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.source) ∧
        T.SourceEndpointReady w.splitData.face (T.src.pos w.splitData.target)

/-- Relative anchoring of new ambient boundary edges and the remaining fresh-incidence
combinatorics together give the complete reverse-ear readiness invariant. -/
theorem targetEarFreshInvariant_of_newBoundaryAnchored [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    TargetEarFreshInvariant P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hstrongₛ, hstrongₜ⟩ :=
    targetEarEndpointStronglyAccessible_of_newBoundaryAnchored
      hH hanchor hBH hnew hpath hab hT w
  obtain ⟨hcombₛ, hcombₜ⟩ :=
    hcomb B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  constructor
  · by_cases hx : T.src.pos w.splitData.source ∈ srcOuter
    · obtain ⟨hfresh, hunique⟩ := hcombₛ hx
      exact Or.inr ⟨hstrongₛ hx, hfresh, hunique⟩
    · exact Or.inl hx
  · by_cases hx : T.src.pos w.splitData.target ∈ srcOuter
    · obtain ⟨hfresh, hunique⟩ := hcombₜ hx
      exact Or.inr ⟨hstrongₜ hx, hfresh, hunique⟩
    · exact Or.inl hx

/-- Anchoring every nonouter boundary edge is a sufficient special case of relative
new-edge anchoring. -/
theorem targetEarFreshInvariant_of_boundaryAnchored [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : TargetBoundaryAnchored P H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    TargetEarFreshInvariant P H Hdraw :=
  targetEarFreshInvariant_of_newBoundaryAnchored
    P H Hdraw hH (hanchor.new P.tgt.skeletonSet) hcomb

/-- Both source endpoints of every nontrivial target ear are polygonally accessible from the
source face selected by that ear.  This is the geometric invariant direction (b) must maintain:
off the wild curve it follows from polygonal-side accessibility, while a fresh wild-boundary
endpoint is supplied by `polyAccessible_of_stronglyAccessible`. -/
def TargetEarEndpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∀ (B : Graph Plane γ) (a b : Plane) (D : List γ), B.IsTwoConnected → B ≤ H →
    H.IsPath a D b → a ≠ b → a ∈ V(B) → b ∈ V(B) →
    (∀ y ∈ H.walkVertices a D, y ≠ a → y ≠ b → y ∉ V(B)) →
    (∀ g ∈ D, g ∉ E(B)) →
    ∀ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P B Hdraw par →
      ∀ w : TargetSideEarStepData T B H Hdraw a b D,
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.source) ∧
        PolyAccessible (T.src.cell w.splitData.face) (T.src.pos w.splitData.target)

/-- The fresh-anchor invariant implies the endpoint-accessibility invariant: the off-curve
branch uses polygonal-side accessibility, and the fresh branch uses the compact carrier and
unique-face theorem above. -/
theorem targetEarEndpointAccessibility_of_freshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    TargetEarEndpointAccessibility P H Hdraw := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  obtain ⟨hsourceReady, htargetReady⟩ :=
    hfresh B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hsourceSub : T.str.sub d.source d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.source_mem_cells₁))
  have htargetSub : T.str.sub d.target d.face :=
    d.sub_face.2 (Or.inr (Or.inl d.target_mem_cells₁))
  have hsourceClosure : T.src.pos d.source ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.source_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) hsourceSub
    rw [T.src.cell_vertex d.source_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  have htargetClosure : T.src.pos d.target ∈ closure (T.src.cell d.face) := by
    have hsub := T.src_isCellDecomposition.subset_closure
      (T.str.mem_cells_of_mem_vertexSet d.target_mem_skel)
      (T.str.mem_cells_of_mem_faces d.face_mem) htargetSub
    rw [T.src.cell_vertex d.target_mem_skel] at hsub
    exact hsub (Set.mem_singleton _)
  constructor
  · rcases hsourceReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem hsourceClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique
  · rcases htargetReady with houter | ⟨hstrong, hnew, hunique⟩
    · exact T.source_polyAccessible_of_notMem_outer d.face_mem htargetClosure houter
    · exact T.source_polyAccessible_of_fresh hstrong hnew hunique

/-- Endpoint accessibility supplies the missing source crosscut, after which the already-proved
arc matching and split constructor complete one nontrivial reverse ear. -/
theorem targetEarStepConstruction_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStepConstruction P H Hdraw hH := by
  intro B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨w⟩ := exists_targetSideEarStepData P H Hdraw hH
    B a b D hB hBH hpath hab haB hbB hint hnew T par hT
  obtain ⟨hsource, htarget⟩ :=
    haccess B a b D hB hBH hpath hab haB hbB hint hnew T par hT w
  let d := w.splitData
  have hends : T.src.pos d.source ≠ T.src.pos d.target := fun h =>
    d.source_ne_target (T.src.injOn_pos d.source_mem_skel d.target_mem_skel h)
  obtain ⟨A, hApoly, hAarc, hAsub⟩ :=
    exists_simple_arc_of_polyAccessible
      (T.src_isFaceJordan.isOpen d.face_mem)
      (T.src_isFaceJordan.isConnected d.face_mem).isPreconnected
      hends hsource htarget
  obtain ⟨srcPos, srcDraw, reverseHomeo, hsrc, hsrcEdgePoly⟩ :=
    w.tgtCrosscut.exists_matched_target hApoly hAarc hAsub
      (T.src.disjoint_cell_skeletonSet T.src_isCellDecomposition d.face_mem)
  exact ⟨{
    splitData := d
    srcPos := srcPos
    srcDraw := srcDraw
    tgtPos := w.tgtPos
    tgtDraw := w.tgtDraw
    srcCrosscut := hsrc
    tgtCrosscut := w.tgtCrosscut
    earHomeo := reverseHomeo.symm
    srcEdgePolygonal := hsrcEdgePoly
    tgtEdgePolygonal := w.tgtEdgePolygonal
    tgtEarSet_eq := w.tgtEarSet_eq
    vertexSet_subset := w.vertexSet_subset
  }⟩

/-- One reverse ear follows from the endpoint-accessibility invariant. -/
theorem targetEarStep_of_endpointAccessibility [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    TargetEarStep P H Hdraw :=
  targetEarStep_of_data hH
    (targetEarStepConstruction_of_endpointAccessibility P H Hdraw hH haccess)

/-- One reverse ear follows from the concrete fresh-anchor/unique-face invariant. -/
theorem targetEarStep_of_freshInvariant [Infinite γ]
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane)
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    TargetEarStep P H Hdraw :=
  targetEarStep_of_endpointAccessibility P H Hdraw hH
    (targetEarEndpointAccessibility_of_freshInvariant P H Hdraw hfresh)

/-- Explicit output data for the target common-subdivision construction. -/
structure TargetCommonSubdivisionData
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) where
  /-- The part of `H` supported on the old target skeleton. -/
  graph : Graph Plane γ
  /-- The matched pair after inserting every vertex of `graph`. -/
  pair : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom
  /-- The composite parent map from the subdivided pair to `P`. -/
  parent : γ → γ
  /-- The traced graph remains 2-connected. -/
  graph_isTwoConnected : graph.IsTwoConnected
  /-- The traced graph is a subgraph of the given target extension. -/
  graph_le : graph ≤ H
  /-- The refined pair realizes the traced target graph. -/
  isTargetPartialTransferOf : IsTargetPartialTransferOf pair P graph Hdraw parent

/-- Construct the target trace, its matched subdivision, and the composite parent map. -/
noncomputable def targetCommonSubdivisionData [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivisionData P H Hdraw := by
  classical
  let K := Graph.traceGraph H Hdraw P.tgt.skeletonSet
  have hKle : K ≤ H := Graph.traceGraph_le _
  let _ : H.Finite := hH.finite
  let _ : K.Finite := Graph.Finite.of_le hKle
  have hK2 : K.IsTwoConnected :=
    trace_isTwoConnected hH P.tgt_isWeaklyAdmissible.isTwoConnected
  have hvertices : V(K) ⊆ P.tgt.skeletonSet := by
    intro x hx
    rw [Graph.traceGraph_vertexSet] at hx
    exact hx.2
  let w := Classical.choice (GeneratedPair.exists_subdivideTargetSetData P
    (Graph.finite_vertexSet K) hvertices)
  exact {
    graph := K
    pair := w.pair
    parent := w.parent
    graph_isTwoConnected := hK2
    graph_le := hKle
    isTargetPartialTransferOf := {
      refines_src := w.refines_src
      refines_tgt := w.refines_tgt
      sourceSkeletonSet_subset := by
        rw [w.sourceSkeletonSet_eq]
      homeo_eqOn := w.homeo_eqOn
      skeletonSet_eq := w.skeletonSet_eq.trans (trace_pointSet hH).symm
      vertexSet_subset := w.vertexSet_subset
    }
  }

/-- **Step 1 of finite transfer, direction (b): construct the target common subdivision.** -/
theorem targetCommonSubdivision [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw) :
    TargetCommonSubdivision P H Hdraw := by
  let w := targetCommonSubdivisionData hH
  exact ⟨w.graph, w.pair, w.parent, w.graph_isTwoConnected, w.graph_le,
    w.isTargetPartialTransferOf⟩

/-- Iterate a target ear step from a common subdivision through the whole extension graph. -/
theorem targetTransferOfEars [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hsub : TargetCommonSubdivision P H Hdraw) (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetPartialTransferOf T P H Hdraw par := by
  let _ := hH.finite
  obtain ⟨K, T₀, par₀, hK, hKH, hbase⟩ := hsub
  refine hH.isTwoConnected.ear_decomposition
    (motive := fun B => ∃ T par, IsTargetPartialTransferOf T P B Hdraw par)
    (fun g x => hH.isDrawing.not_isLoopAt g x) hK hKH ⟨T₀, par₀, hbase⟩ ?_
  rintro B a b D hB - hBH ⟨T, par, hT⟩ hpath hab haB hbB hint
  exact hstep B a b D hB hBH hpath hab haB hbB hint T par hT

/-- Direction (b), assuming only the target ear step. -/
theorem finite_transfer_toward_source_of_targetEarStep [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hstep : TargetEarStep P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par := by
  obtain ⟨T, par, hT⟩ :=
    targetTransferOfEars hH (targetCommonSubdivision hH) hstep
  have hconnTgt : IsConnected T.tgt.nonboundary := by
    rw [CellStructure.Realization.nonboundary,
      T.tgt_isWeaklyAdmissible.outerSet_eq, hT.skeletonSet_eq]
    exact hH.isConnected
  have hconnSrc : IsConnected T.src.nonboundary :=
    T.homeo.isConnected_nonboundary_iff.2 hconnTgt
  exact ⟨T, par, hT, T.src_isAdmissible hconnSrc, T.tgt_isAdmissible hconnSrc⟩

/-- Direction (b), reduced to the precise geometric endpoint-accessibility invariant maintained
by the prescribed outer-cycle ear order. -/
theorem finite_transfer_toward_source_of_endpointAccessibility [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (haccess : TargetEarEndpointAccessibility P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_targetEarStep hH
    (targetEarStep_of_endpointAccessibility P H Hdraw hH haccess)

/-- Direction (b), reduced to the prescribed ear order's concrete fresh-anchor and
unique-incident-face invariant.  All geometric accessibility and reverse-split construction is
discharged. -/
theorem finite_transfer_toward_source_of_freshInvariant [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hfresh : TargetEarFreshInvariant P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_endpointAccessibility hH
    (targetEarEndpointAccessibility_of_freshInvariant P H Hdraw hfresh)

/-- Direction (b), with strong accessibility discharged by relative anchoring of new target
boundary edges.  The only remaining hypothesis is the fresh-carrier and unique-face
combinatorics of the ear order. -/
theorem finite_transfer_toward_source_of_newBoundaryAnchored [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_freshInvariant hH
    (targetEarFreshInvariant_of_newBoundaryAnchored P H Hdraw hH hanchor hcomb)

/-- Anchoring every nonouter target-boundary edge is a sufficient special case. -/
theorem finite_transfer_toward_source_of_boundaryAnchored [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : TargetBoundaryAnchored P H Hdraw)
    (hcomb : TargetEarFreshCombinatorics P H Hdraw) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_newBoundaryAnchored
    hH (hanchor.new P.tgt.skeletonSet) hcomb

/-- **Finite transfer, direction (b), from relative ambient boundary geometry.**  Boundary
endpoints must be anchored, and a genuinely new nonouter edge must not coexist there with a
nonouter edge already in the current trace.  The abstract base needs one distinguished outer
cycle. -/
theorem finite_transfer_toward_source_of_relativeBoundaryGeometry [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : NewTargetBoundaryAnchored P P.tgt.skeletonSet H Hdraw)
    (hnoNew : NoNewNonouterIncidenceAtBoundary
      P.tgt.skeletonSet H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_newBoundaryAnchored hH hanchor
    (targetEarFreshCombinatorics_of_noNewNonouterIncidence_of_outerCycle
      P hH hnoNew hcycle)

/-- **Finite transfer, direction (b), from name-independent ambient boundary geometry.**
Global uniqueness of the incident nonouter edge implies the relative condition used by reverse
ear insertion. -/
theorem finite_transfer_toward_source_of_boundaryGeometry [Infinite γ]
    {P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom}
    {H : Graph Plane γ} {Hdraw : γ → ℝ → Plane}
    (hH : IsSourceExtension P.tgt tgtOuter tgtDom H Hdraw)
    (hanchor : TargetBoundaryAnchored P H Hdraw)
    (hunique : NonouterIncidenceUniqueAtBoundary H Hdraw tgtOuter)
    (hcycle : S₀.OuterEdgesFormCycle) :
    ∃ (T : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom) (par : γ → γ),
      IsTargetTransferOf T P H Hdraw par :=
  finite_transfer_toward_source_of_relativeBoundaryGeometry
    hH (hanchor.new P.tgt.skeletonSet)
      (hunique.noNew P.tgt.skeletonSet) hcycle

end Schoenflies
