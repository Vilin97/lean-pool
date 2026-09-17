/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.RealizeSplit
import LeanPool.Schoenflies.FaceCycles

/-!
# The skeleton homeomorphism across a 2-cell split

`Schoenflies/RealizeSplit.lean` builds **one** realization of `S.splitFace d` from a realization
`R` of `S` and a drawing of the ear as a polygonal crosscut. A *matched* cellulation is two
realizations of one abstract structure together with the skeleton homeomorphism between them
(`def:matched-pair` clause 3), so the split has to be performed on both sides at once and the
skeleton homeomorphism has to be carried across. That is what this module does.

## Blueprint

* `def:matched-pair`, clause 3 — the chosen homeomorphism `g : |Γ| → |Γ'|`, recorded as
  `Schoenflies.CellStructure.SkeletonHomeo`, extended across one split.
* `def:generated-structure`, operation 2 — the 2-cell split, whose two realizations are the
  output of `Schoenflies.CellStructure.SplitData.realize`.

## What is constructed

* `Schoenflies.CellStructure.SplitData.skeletonSet_realize` — **the split's realized 1-skeleton
  is the old one together with the drawn ear**, as a point set. Everything else rests on this.
* `Schoenflies.CellStructure.SplitData.EarHomeo` — the chosen homeomorphism between the two
  drawn ears (see the next section).
* `Schoenflies.CellStructure.SplitData.EarHomeo.symm` — the same chosen matching with source
  and target reversed, used by finite-transfer direction (b).
* `Schoenflies.CellStructure.SplitData.splitMap` / `splitInvMap` — the transported map and its
  inverse, as plain functions `Plane → Plane`: `g` on the old skeleton, the ear map off it.
* `Schoenflies.CellStructure.SplitData.splitHomeo` — the `SkeletonHomeo` between the two split
  realizations. A `def` with lemmas, not an `∃`-packaged bundle.
* `Schoenflies.CellStructure.SplitData.splitHomeo_eqOn` — **the transported map agrees with `g`
  on the whole old skeleton.** This is exactly `Schoenflies.StageSequence.skelHomeo_succ` at a
  split step, and it is the reason the construction is "extend `g` by the ear map" rather than
  "rebuild a homeomorphism from scratch".

## How the ear map is presented, and why

Two shapes were available.

(a) **As data**: a map `Plane → Plane` (with an inverse) carrying the drawn source ear onto the
drawn target ear, vertex to corresponding vertex and edge arc to corresponding edge arc.

(b) **Built edge by edge** from the two `EarCrosscut`s, by composing one edge's parametrization
with the inverse of the other's.

This module takes **(a)**, as `EarHomeo`. The reason is the consumer, not the construction:
`def:matched-pair` clause 3 says that `g` *restricts to a fixed chosen homeomorphism* on each
corresponding pair of cells, so a caller assembling a matched pair is holding such a chosen
homeomorphism already — for the old cells it is `g` itself, and for the ear's cells it is
whatever the producer of the two crosscuts chose. Shape (b) would manufacture a second,
different homeomorphism from the two parametrizations, and the caller would then have to prove
that its own choice agrees with the manufactured one. It would also silently fix an orientation
of every ear edge: `Graph.IsDrawing.edge_param` is orientation-free, so `earDraw₁ f 0` and
`earDraw₂ f 0` need not be the ends that correspond, and (b) would need the `SubdivData.leftParam`
trick of `Schoenflies/RealizeSubdiv.lean` replayed per edge.

Every field of `EarHomeo` is therefore something the caller supplies, and none of them mentions
`R₁`, `R₂` or `g`: the ear map is a statement about the two drawn ears alone. In particular
**no compatibility hypothesis between `m` and `g` is asked for**, because none is needed: at the
ear's two ends `m.toFun` and `g.toFun` are *forced* to agree, both being pinned to
`R₂.pos d.source` and `R₂.pos d.target` — `m` by `earPos_apply` together with the two `pos_source`
/ `pos_target` clauses of the two `EarCrosscut`s, and `g` by its own `pos_apply`. That is
`EarHomeo.toFun_pos_source` / `toFun_pos_target` below.

## The proof, in one paragraph

The new skeleton is a union of two **closed** sets — the old realized skeleton
(`Realization.isCompact_skeletonSet`) and the drawn ear, which is an arc
(`EarCrosscut.isArcBetween_earSet`) and hence compact. Continuity of the transported map is the
pasting lemma `Schoenflies.Plane.continuousOn_union_of_isClosed` on those two pieces; the two
pieces meet exactly in the ear's two ends (`EarCrosscut.earSet_inter_skeletonSet`, which is
`SplitData.vertexSet_inter` made geometric), and there the two prescriptions agree. Injectivity
and the two inverse laws are injectivity on each piece plus the fact that the *images* also meet
only in the two images of the ends — for which the target-side
`EarCrosscut.earSet_inter_skeletonSet` is again what is spent. `pos_apply` and `edgeArc_image`
split into the old cells, where `g`'s own fields serve verbatim, and the ear's cells, where
`EarHomeo`'s two matching clauses are the statement.

## What is *not* here

The **subdivision** analogue — the transported skeleton homeomorphism across an edge
subdivision — is deliberately absent. It is being built concurrently on branch
`wt/arc-monotone`, where the missing ingredient (a homeomorphism between two arcs fixing their
ends is monotone, hence carries initial subarcs to initial subarcs — see the section
"What is *not* here" of `Schoenflies/RealizeSubdiv.lean`) is the actual content. Nothing below
depends on it, and nothing below should be duplicated there: this module is the split case only.

## The general lemma this needed

`Graph.pointSet_congr` — the point set of a plane graph depends on the drawing only through the
arcs of the graph's own edges. It is stated in the root `Graph` namespace next to
`Graph.pointSet_union` (which lives in `Schoenflies/FaceCycles.lean`); if a second consumer
appears it belongs there or in `Schoenflies/Graph/Drawing.lean`.
-/

open Set Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β}

/-- **The point set of a plane graph only sees the arcs of its own edges.** Two drawings that
agree, arc for arc, on `E(G)` give `G` the same point set. This is what makes the split's
`splitDrawing` — which is `R.drawing` on the old edges and `earDraw` on the ear's — restrict on
each half of the union to the drawing that half came with. -/
theorem pointSet_congr {drw drw' : β → ℝ → Plane}
    (h : ∀ ⦃e⦄, e ∈ E(G) → edgeArc drw e = edgeArc drw' e) :
    pointSet G drw = pointSet G drw' := by
  rw [pointSet, pointSet]
  exact congrArg _ (Set.iUnion₂_congr fun e he => h he)

end Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- **A realized 0-cell is a point of the realized 1-skeleton.** The inlined form of this
appears at least four times on `main` (`SkeletonHomeo.symm`, `Realization.disjoint_skeleton`
arguments in `Schoenflies/RealizeSplit.lean`, …); it belongs next to
`Realization.skeletonSet` in `Schoenflies/CombinatorialInvariance.lean`. -/
theorem Realization.pos_mem_skeletonSet (R : S.Realization) {v : γ} (hv : v ∈ V(S.skel)) :
    R.pos v ∈ R.skeletonSet :=
  Graph.vertexSet_subset_pointSet (by rw [Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

namespace SplitData

variable {d : S.SplitData}

/-! ## The realized 1-skeleton of a split

A 2-cell split adds the drawn ear to the drawn 1-skeleton and changes nothing else. This is the
geometric statement the whole module rests on: it turns every clause of `SkeletonHomeo`, which
quantifies over the *new* skeleton, into a pair of clauses over the two closed pieces. -/

/-- **The realized 1-skeleton after a 2-cell split is the old one together with the drawn ear.**

`EarCrosscut.splitGraph_eq` says the new drawn graph is the union of the old one with the drawn
ear; `Graph.pointSet_union` splits the point set of that union; and `Graph.pointSet_congr`
replaces the split drawing by the drawing each half came with. -/
theorem skeletonSet_realize {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) :
    (d.realize R earPos earDraw hE).skeletonSet = R.skeletonSet ∪ d.earSet earPos earDraw := by
  have hstep : (d.realize R earPos earDraw hE).skeletonSet =
      Graph.pointSet (R.graph.union (d.earGraph earPos)) (d.splitDrawing R earDraw) := by
    rw [← hE.splitGraph_eq]
    rfl
  rw [hstep, Graph.pointSet_union]
  congr 1
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_skel (by rwa [Realization.edgeSet_graph] at he)
  · exact Graph.pointSet_congr fun e he =>
      edgeArc_splitDrawing_of_mem_ear (by rwa [d.edgeSet_earGraph] at he)

/-- **A 2-cell split only grows the realized 1-skeleton.** This is the field
`Schoenflies.StageSequence.skeletonSet_mono` at a split step. -/
theorem skeletonSet_subset_realize {R : S.Realization} {earPos : γ → Plane}
    {earDraw : γ → ℝ → Plane} (hE : d.EarCrosscut R earPos earDraw) :
    R.skeletonSet ⊆ (d.realize R earPos earDraw hE).skeletonSet :=
  (skeletonSet_realize hE).symm ▸ Set.subset_union_left

/-- The drawn ear is closed: it is a simple arc, hence compact. -/
theorem isClosed_earSet {R : S.Realization} {earPos : γ → Plane} {earDraw : γ → ℝ → Plane}
    (hE : d.EarCrosscut R earPos earDraw) : IsClosed (d.earSet earPos earDraw) :=
  hE.isArcBetween_earSet.isArc.isCompact.isClosed

/-! ## The chosen homeomorphism between the two drawn ears -/

/-- **The chosen homeomorphism between two drawings of one abstract ear.**

This is `def:matched-pair` clause 3 restricted to the cells the split creates: a homeomorphism
between the two drawn ears which matches corresponding vertices and corresponding edges. It is
data, not a proposition, and it mentions neither realization: everything it says is a statement
about the two drawings of `d.ear`.

`earPos_apply` and `edgeArc_image` are the two matching clauses. Together they force
`toFun '' (source ear) = (target ear)` (`EarHomeo.image_earSet`), which is why no separate
surjectivity clause is asked for. The inverse is supplied as data, exactly as in
`CellStructure.SkeletonHomeo`, so that no compactness argument is needed to speak of a
homeomorphism. -/
structure EarHomeo (d : S.SplitData) (earPos₁ : γ → Plane) (earDraw₁ : γ → ℝ → Plane)
    (earPos₂ : γ → Plane) (earDraw₂ : γ → ℝ → Plane) where
  /-- The map. -/
  toFun : Plane → Plane
  /-- Its inverse. -/
  invFun : Plane → Plane
  /-- The map is continuous on the source ear. -/
  continuousOn_toFun : ContinuousOn toFun (d.earSet earPos₁ earDraw₁)
  /-- The inverse is continuous on the target ear. -/
  continuousOn_invFun : ContinuousOn invFun (d.earSet earPos₂ earDraw₂)
  /-- The inverse undoes the map. -/
  leftInvOn : LeftInvOn invFun toFun (d.earSet earPos₁ earDraw₁)
  /-- The map undoes the inverse. -/
  rightInvOn : RightInvOn invFun toFun (d.earSet earPos₂ earDraw₂)
  /-- Corresponding vertices of the ear correspond. -/
  earPos_apply : ∀ ⦃z⦄, z ∈ V(d.ear) → toFun (earPos₁ z) = earPos₂ z
  /-- Corresponding edges of the ear correspond. -/
  edgeArc_image : ∀ ⦃f⦄, f ∈ E(d.ear) →
    toFun '' Graph.edgeArc earDraw₁ f = Graph.edgeArc earDraw₂ f

namespace EarHomeo

variable {earPos₁ earPos₂ : γ → Plane} {earDraw₁ earDraw₂ : γ → ℝ → Plane}
  (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂)

/-- **The chosen map carries the source ear onto the target ear.** The point set of a drawn
graph is its vertices together with its edge arcs, and the two matching clauses handle those
two halves. -/
theorem image_earSet :
    m.toFun '' d.earSet earPos₁ earDraw₁ = d.earSet earPos₂ earDraw₂ := by
  rw [earSet, earSet, Graph.pointSet, Graph.pointSet, Set.image_union, Set.image_iUnion₂]
  congr 1
  · rw [d.vertexSet_earGraph, d.vertexSet_earGraph, ← Set.image_comp]
    exact Set.image_congr fun z hz => m.earPos_apply hz
  · rw [d.edgeSet_earGraph, d.edgeSet_earGraph]
    exact Set.iUnion₂_congr fun f hf => m.edgeArc_image hf

theorem injOn : InjOn m.toFun (d.earSet earPos₁ earDraw₁) := m.leftInvOn.injOn

theorem mapsTo :
    MapsTo m.toFun (d.earSet earPos₁ earDraw₁) (d.earSet earPos₂ earDraw₂) :=
  fun _ hx => m.image_earSet ▸ Set.mem_image_of_mem _ hx

/-- The inverse carries the target ear back into the source ear. Not a field: every point of
the target ear is the image of a point of the source ear, and there the inverse is a left
inverse. -/
theorem mapsTo_invFun :
    MapsTo m.invFun (d.earSet earPos₂ earDraw₂) (d.earSet earPos₁ earDraw₁) := by
  intro y hy
  rw [← m.image_earSet] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [m.leftInvOn hx]
  exact hx

/-- Reverse a chosen matching of two realized ears.  Direction (b) of finite transfer first
constructs the ear on the target side, so it naturally obtains the matching in the opposite
direction from the one consumed by `GeneratedPair.split`. -/
def symm : d.EarHomeo earPos₂ earDraw₂ earPos₁ earDraw₁ where
  toFun := m.invFun
  invFun := m.toFun
  continuousOn_toFun := m.continuousOn_invFun
  continuousOn_invFun := m.continuousOn_toFun
  leftInvOn := m.rightInvOn
  rightInvOn := m.leftInvOn
  earPos_apply := by
    intro z hz
    rw [← m.earPos_apply hz]
    apply m.leftInvOn
    exact Graph.vertexSet_subset_pointSet (by
      rw [d.vertexSet_earGraph]
      exact ⟨z, hz, rfl⟩)
  edgeArc_image := by
    intro f hf
    rw [← m.edgeArc_image hf]
    exact m.leftInvOn.image_image'
      (Graph.edgeArc_subset_pointSet (by rw [d.edgeSet_earGraph]; exact hf))

@[simp] theorem symm_toFun : m.symm.toFun = m.invFun := rfl

@[simp] theorem symm_invFun : m.symm.invFun = m.toFun := rfl

variable {R₁ R₂ : S.Realization}

/-- **At the ear's source end the chosen map is pinned to the old 0-cell's target position.**
This — with `SkeletonHomeo.pos_apply` — is why no compatibility hypothesis between the ear map
and `g` has to be asked for. -/
theorem toFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.source) = R₂.pos d.source := by
  rw [← hE₁.pos_source, m.earPos_apply d.source_mem_ear, hE₂.pos_source]

theorem toFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.toFun (R₁.pos d.target) = R₂.pos d.target := by
  rw [← hE₁.pos_target, m.earPos_apply d.target_mem_ear, hE₂.pos_target]

theorem invFun_pos_source (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.source) = R₁.pos d.source := by
  rw [← m.toFun_pos_source hE₁ hE₂, m.leftInvOn hE₁.pos_source_mem_earSet]

theorem invFun_pos_target (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁)
    (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂) :
    m.invFun (R₂.pos d.target) = R₁.pos d.target := by
  rw [← m.toFun_pos_target hE₁ hE₂, m.leftInvOn hE₁.pos_target_mem_earSet]

end EarHomeo

/-! ## The transported map -/

variable {R₁ R₂ : S.Realization} {earPos₁ earPos₂ : γ → Plane}
  {earDraw₁ earDraw₂ : γ → ℝ → Plane}

open scoped Classical in
/-- **The transported skeleton map**: `g` on the old realized skeleton, the chosen ear map off
it. Written with a test on the old skeleton rather than on the ear so that agreement with `g`
— `splitHomeo_eqOn`, i.e. `StageSequence.skelHomeo_succ` — holds by definition. -/
noncomputable def splitMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun x => if x ∈ R₁.skeletonSet then g.toFun x else m.toFun x

open scoped Classical in
/-- The transported inverse, by the same recipe on the target side. -/
noncomputable def splitInvMap (g : SkeletonHomeo R₁ R₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) : Plane → Plane :=
  fun y => if y ∈ R₂.skeletonSet then g.invFun y else m.invFun y

variable {g : SkeletonHomeo R₁ R₂} {m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂}

theorem splitMap_of_mem_skeletonSet {x : Plane} (hx : x ∈ R₁.skeletonSet) :
    splitMap g m x = g.toFun x := by
  classical
  simp only [splitMap, ite_eq_left hx]

theorem splitMap_eqOn_skeletonSet : EqOn (splitMap g m) g.toFun R₁.skeletonSet :=
  fun _ hx => splitMap_of_mem_skeletonSet hx

theorem splitInvMap_of_mem_skeletonSet {y : Plane} (hy : y ∈ R₂.skeletonSet) :
    splitInvMap g m y = g.invFun y := by
  classical
  simp only [splitInvMap, ite_eq_left hy]

theorem splitInvMap_of_notMem_skeletonSet {y : Plane} (hy : y ∉ R₂.skeletonSet) :
    splitInvMap g m y = m.invFun y := by
  classical
  simp only [splitInvMap, ite_eq_right hy]

variable (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)

include hE₁ hE₂

/-- **On the drawn ear the transported map is the chosen ear map** — including at the two ends,
where the two prescriptions agree because both are pinned to the target position of the old
0-cell. -/
theorem splitMap_of_mem_earSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁) :
    splitMap g m x = m.toFun x := by
  classical
  by_cases hs : x ∈ R₁.skeletonSet
  · rw [splitMap, ite_eq_left hs]
    have hends := hE₁.earSet_inter_skeletonSet ⟨hx, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · rw [g.pos_apply d.source_mem_skel, m.toFun_pos_source hE₁ hE₂]
    · rw [g.pos_apply d.target_mem_skel, m.toFun_pos_target hE₁ hE₂]
  · rw [splitMap, ite_eq_right hs]

theorem splitMap_eqOn_earSet : EqOn (splitMap g m) m.toFun (d.earSet earPos₁ earDraw₁) :=
  fun _ hx => splitMap_of_mem_earSet hE₁ hE₂ hx

/-- On the drawn target ear the transported inverse is the chosen ear map's inverse. -/
theorem splitInvMap_eqOn_earSet :
    EqOn (splitInvMap g m) m.invFun (d.earSet earPos₂ earDraw₂) := by
  classical
  intro y hy
  by_cases hs : y ∈ R₂.skeletonSet
  · rw [splitInvMap, ite_eq_left hs]
    have hends := hE₂.earSet_inter_skeletonSet ⟨hy, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
    rcases hends with rfl | rfl
    · have h : g.invFun (R₂.pos d.source) = R₁.pos d.source := g.symm.pos_apply d.source_mem_skel
      rw [h, m.invFun_pos_source hE₁ hE₂]
    · have h : g.invFun (R₂.pos d.target) = R₁.pos d.target := g.symm.pos_apply d.target_mem_skel
      rw [h, m.invFun_pos_target hE₁ hE₂]
  · rw [splitInvMap, ite_eq_right hs]

/-- **A point of the source ear off the old skeleton is carried off the old target skeleton.**
The image lies on the target ear, and the target ear meets the target skeleton only in the two
ends — whose preimages under the (injective) ear map are the two ends on the source side, which
*are* on the source skeleton. -/
theorem toFun_notMem_skeletonSet {x : Plane} (hx : x ∈ d.earSet earPos₁ earDraw₁)
    (hs : x ∉ R₁.skeletonSet) : m.toFun x ∉ R₂.skeletonSet := by
  intro hcon
  have hends := hE₂.earSet_inter_skeletonSet ⟨m.mapsTo hx, hcon⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  rcases hends with heq | heq
  · rw [← m.toFun_pos_source hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_source_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.source_mem_skel)
  · rw [← m.toFun_pos_target hE₁ hE₂] at heq
    exact hs (m.injOn hx hE₁.pos_target_mem_earSet heq ▸ R₁.pos_mem_skeletonSet d.target_mem_skel)

/-- The mirror statement on the target side, for the inverse. -/
theorem invFun_notMem_skeletonSet {y : Plane} (hy : y ∈ d.earSet earPos₂ earDraw₂)
    (hs : y ∉ R₂.skeletonSet) : m.invFun y ∉ R₁.skeletonSet := by
  intro hcon
  have hx : m.invFun y ∈ d.earSet earPos₁ earDraw₁ := m.mapsTo_invFun hy
  have hends := hE₁.earSet_inter_skeletonSet ⟨hx, hcon⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hends
  have hback : m.toFun (m.invFun y) = y := m.rightInvOn hy
  rcases hends with heq | heq
  · rw [heq, m.toFun_pos_source hE₁ hE₂] at hback
    exact hs (hback ▸ R₂.pos_mem_skeletonSet d.source_mem_skel)
  · rw [heq, m.toFun_pos_target hE₁ hE₂] at hback
    exact hs (hback ▸ R₂.pos_mem_skeletonSet d.target_mem_skel)

/-! ## The skeleton homeomorphism across the split -/

/-- **The skeleton homeomorphism, transported across a 2-cell split.**

Given two realizations of one abstract cell structure, the skeleton homeomorphism `g` between
them, a drawing of the ear as a polygonal crosscut on *each* side, and the chosen homeomorphism
between the two drawn ears, this is the skeleton homeomorphism between the two split
realizations — `def:matched-pair` clause 3 for the structure `S.splitFace d`.

It is an *extension* of `g`, not a new map: `splitHomeo_eqOn` says it agrees with `g` on the
whole old realized skeleton, which is precisely the field `StageSequence.skelHomeo_succ`. -/
noncomputable def splitHomeo (g : SkeletonHomeo R₁ R₂)
    (hE₁ : d.EarCrosscut R₁ earPos₁ earDraw₁) (hE₂ : d.EarCrosscut R₂ earPos₂ earDraw₂)
    (m : d.EarHomeo earPos₁ earDraw₁ earPos₂ earDraw₂) :
    SkeletonHomeo (d.realize R₁ earPos₁ earDraw₁ hE₁) (d.realize R₂ earPos₂ earDraw₂ hE₂) where
  toFun := splitMap g m
  invFun := splitInvMap g m
  continuousOn_toFun := by
    rw [skeletonSet_realize hE₁]
    refine Plane.continuousOn_union_of_isClosed R₁.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₁) (g.continuousOn_toFun.congr splitMap_eqOn_skeletonSet) ?_
    exact m.continuousOn_toFun.congr (splitMap_eqOn_earSet hE₁ hE₂)
  continuousOn_invFun := by
    rw [skeletonSet_realize hE₂]
    refine Plane.continuousOn_union_of_isClosed R₂.isCompact_skeletonSet.isClosed
      (isClosed_earSet hE₂) (g.continuousOn_invFun.congr fun _ hy =>
        splitInvMap_of_mem_skeletonSet hy) ?_
    exact m.continuousOn_invFun.congr (splitInvMap_eqOn_earSet hE₁ hE₂)
  leftInvOn := by
    rw [skeletonSet_realize hE₁]
    rintro x (hx | hx)
    · rw [splitMap_of_mem_skeletonSet hx,
        splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hx),
        g.leftInvOn hx]
    · by_cases hs : x ∈ R₁.skeletonSet
      · rw [splitMap_of_mem_skeletonSet hs,
          splitInvMap_of_mem_skeletonSet (g.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.leftInvOn hs]
      · rw [splitMap_of_mem_earSet hE₁ hE₂ hx,
          splitInvMap_of_notMem_skeletonSet (toFun_notMem_skeletonSet hE₁ hE₂ hx hs),
          m.leftInvOn hx]
  rightInvOn := by
    rw [skeletonSet_realize hE₂]
    rintro y (hy | hy)
    · rw [splitInvMap_of_mem_skeletonSet hy,
        splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hy),
        g.rightInvOn hy]
    · by_cases hs : y ∈ R₂.skeletonSet
      · rw [splitInvMap_of_mem_skeletonSet hs,
          splitMap_of_mem_skeletonSet (g.symm.image_skeletonSet ▸ Set.mem_image_of_mem _ hs),
          g.rightInvOn hs]
      · rw [splitInvMap_of_notMem_skeletonSet hs,
          splitMap_of_mem_earSet hE₁ hE₂ (m.mapsTo_invFun hy), m.rightInvOn hy]
  pos_apply := by
    intro v hv
    have hv' : v ∈ V(S.skel) ∪ V(d.ear) := hv
    rcases hv' with hv' | hv'
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [hE₁.splitPos_eq hv', hE₂.splitPos_eq hv',
        splitMap_of_mem_skeletonSet (R₁.pos_mem_skeletonSet hv'), g.pos_apply hv']
    · change splitMap g m (d.splitPos R₁ earPos₁ v) = d.splitPos R₂ earPos₂ v
      rw [splitPos_of_mem_ear hv', splitPos_of_mem_ear hv',
        splitMap_of_mem_earSet hE₁ hE₂ (EarCrosscut.mem_earSet_of_mem_ear hv'),
        m.earPos_apply hv']
  edgeArc_image := by
    intro e he
    have he' : e ∈ E(S.skel) ∪ E(d.ear) := he
    rcases he' with he' | he'
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_skel he', edgeArc_splitDrawing_of_mem_skel he',
        Set.image_congr (fun x hx => splitMap_of_mem_skeletonSet
          (Graph.edgeArc_subset_pointSet (by rwa [Realization.edgeSet_graph]) hx)),
        g.edgeArc_image he']
    · change splitMap g m '' Graph.edgeArc (d.splitDrawing R₁ earDraw₁) e =
        Graph.edgeArc (d.splitDrawing R₂ earDraw₂) e
      rw [edgeArc_splitDrawing_of_mem_ear he', edgeArc_splitDrawing_of_mem_ear he',
        Set.image_congr (fun x hx => splitMap_of_mem_earSet hE₁ hE₂
          (EarCrosscut.edgeArc_subset_earSet he' hx)),
        m.edgeArc_image he']

@[simp] theorem splitHomeo_toFun : (splitHomeo g hE₁ hE₂ m).toFun = splitMap g m := rfl

@[simp] theorem splitHomeo_invFun : (splitHomeo g hE₁ hE₂ m).invFun = splitInvMap g m := rfl

/-- **The transported map agrees with `g` on the whole old realized skeleton.**

This is the field `Schoenflies.StageSequence.skelHomeo_succ` at a 2-cell split step: consecutive
skeleton maps agree wherever both are defined. It holds by definition, which is the point of
building the map by extension rather than by rebuilding. -/
theorem splitHomeo_eqOn :
    EqOn (splitHomeo g hE₁ hE₂ m).toFun g.toFun R₁.skeletonSet :=
  splitMap_eqOn_skeletonSet

/-- On the drawn ear the transported map is the chosen ear map — the other half of
`def:matched-pair` clause 3 for a split. -/
theorem splitHomeo_eqOn_earSet :
    EqOn (splitHomeo g hE₁ hE₂ m).toFun m.toFun (d.earSet earPos₁ earDraw₁) :=
  splitMap_eqOn_earSet hE₁ hE₂

end SplitData

end CellStructure

end Schoenflies
