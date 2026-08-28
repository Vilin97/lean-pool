/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/

import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import LeanPool.FiniteGraphFundamentalGroup.Cover
import LeanPool.FiniteGraphFundamentalGroup.Realization

/-!
# Local charts and topological graph covers

This module verifies the local topology needed to realize the combinatorial path-lifting cover.
-/

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver
open unitInterval

noncomputable section

universe u

namespace FiniteGraphFreeGroup

/-!
# Local charts for graph realizations

The quotient realization has two kinds of local charts.  At a vertex we use
the vertex together with the two half-open germs of every incident edge.  At
an edge-interior point we use the open interval cell.  These sets are kept at
the prequotient level so that openness is checked by `isOpen_coinduced` and
the endpoint quotient is handled by a small saturation lemma.
-/

/-- The midpoint of the unit interval used to separate the two incident-edge stars. -/
def graphHalf : I :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

@[simp]
theorem graphHalf_coe : (graphHalf : ℝ) = (1 : ℝ) / 2 := rfl

@[simp]
theorem graphHalf_pos : (0 : I) < graphHalf := by
  change (0 : ℝ) < (1 : ℝ) / 2
  norm_num

@[simp]
theorem graphHalf_lt_one : graphHalf < (1 : I) := by
  change (1 : ℝ) / 2 < 1
  norm_num

theorem graphHalf_not_lt_zero : ¬graphHalf < (0 : I) := by
  exact not_lt_of_ge (le_of_lt graphHalf_pos)

@[simp]
theorem one_not_lt_graphHalf : ¬(1 : I) < graphHalf := by
  exact not_lt_of_ge (le_of_lt graphHalf_lt_one)

/-- Representatives of the open star of a vertex before taking the realization quotient. -/
def graphVertexStarPre {V : Type u} [Quiver.{u} V] (v : V) :
    Set (graphRealizationPre V) := {x | match x with
      | Sum.inl w => graphVertexUnderlying w = v
      | Sum.inr z =>
          let e := graphEdgeUnderlying z.1
          (e.left = v ∧ z.2 < graphHalf) ∨
            (e.right = v ∧ graphHalf < z.2)}

theorem graphVertexStarPre_isOpen {V : Type u} [Quiver.{u} V]
    (v : V) : IsOpen (graphVertexStarPre v) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_discrete _
  · rw [isOpen_sigma_iff]
    intro e
    change IsOpen {t : I |
      ((graphEdgeUnderlying e).left = v ∧ t < graphHalf) ∨
        ((graphEdgeUnderlying e).right = v ∧ graphHalf < t)}
    by_cases hleft : (graphEdgeUnderlying e).left = v
    · by_cases hright : (graphEdgeUnderlying e).right = v
      · simp only [hleft, hright, true_and]
        exact isOpen_Iio.union isOpen_Ioi
      · simp only [hleft, hright, true_and, false_and, or_false]
        exact isOpen_Iio
    · by_cases hright : (graphEdgeUnderlying e).right = v
      · simp only [hleft, hright, false_and, true_and, false_or]
        exact isOpen_Ioi
      · simp only [hleft, hright, false_and, false_or]
        exact isOpen_empty

theorem graphVertexStarPre_saturated {V : Type u} [Quiver.{u} V]
    (v : V) {x y : graphRealizationPre V}
    (h : Relation.EqvGen (graphRealizationGenerator (V := V)) x y) :
    (x ∈ graphVertexStarPre v ↔ y ∈ graphVertexStarPre v) := by
  induction h with
  | rel x y h =>
      cases h with
      | source e => simp [graphVertexStarPre]
      | target e => simp [graphVertexStarPre]
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem graphVertexStarPre_disjoint {V : Type u} [Quiver.{u} V]
    {v w : V} (hvw : v ≠ w) :
    Disjoint (graphVertexStarPre v) (graphVertexStarPre w) := by
  rw [Set.disjoint_left]
  intro z hzv hzw
  cases z with
  | inl z =>
      exact hvw (by
        have hv : graphVertexUnderlying z = v := by simpa [graphVertexStarPre] using hzv
        have hw : graphVertexUnderlying z = w := by simpa [graphVertexStarPre] using hzw
        exact hv.symm.trans hw)
  | inr z =>
      rcases z with ⟨z, t⟩
      change (((graphEdgeUnderlying z).left = v ∧ t < graphHalf) ∨
        ((graphEdgeUnderlying z).right = v ∧ graphHalf < t)) at hzv
      change (((graphEdgeUnderlying z).left = w ∧ t < graphHalf) ∨
        ((graphEdgeUnderlying z).right = w ∧ graphHalf < t)) at hzw
      rcases hzv with hzv | hzv <;> rcases hzw with hzw | hzw
      · exact hvw (hzv.1.symm.trans hzw.1)
      · exact (not_lt_of_ge (le_of_lt hzw.2)) hzv.2
      · exact (not_lt_of_ge (le_of_lt hzv.2)) hzw.2
      · exact hvw (hzv.1.symm.trans hzw.1)

/-- The open star of a vertex in the graph realization. -/
def graphVertexStar {V : Type u} [Quiver.{u} V] (v : V) :
    Set (graphRealization V) :=
  graphRealizationQuotient '' graphVertexStarPre v

theorem graphVertexStar_isOpen {V : Type u} [Quiver.{u} V]
    (v : V) : IsOpen (graphVertexStar v) :=
  graphRealization_image_isOpen_of_saturated
    (graphVertexStarPre_saturated v) (graphVertexStarPre_isOpen v)

theorem graphVertexStar_preimage {V : Type u} [Quiver.{u} V]
    (v : V) :
    graphRealizationQuotient ⁻¹' graphVertexStar v = graphVertexStarPre v :=
  graphRealization_image_preimage_eq_of_saturated (graphVertexStarPre_saturated v)

theorem graphVertex_mem_graphVertexStar {V : Type u} [Quiver.{u} V]
    (v : V) : graphVertex v ∈ graphVertexStar v := by
  exact ⟨Sum.inl (graphDiscreteVertex v), by simp [graphVertexStarPre], rfl⟩

/-- Representatives of an edge interior before taking the realization quotient. -/
def graphEdgeInteriorPre {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) : Set (graphRealizationPre V) :=
  {x | match x with
    | Sum.inl _ => False
    | Sum.inr z => z.1 = graphDiscreteEdge e ∧ z.2 ∈ Ioo (0 : I) 1}

theorem graphEdgeInteriorPre_isOpen {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) : IsOpen (graphEdgeInteriorPre e) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro e'
    by_cases h : e' = graphDiscreteEdge e
    · subst h
      change IsOpen {t : I |
        graphDiscreteEdge e = graphDiscreteEdge e ∧ t ∈ Ioo (0 : I) 1}
      simp only [true_and]
      exact isOpen_Ioo
    · simp [graphEdgeInteriorPre, h]

theorem graphEdgeInteriorPre_saturated {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) {x y : graphRealizationPre V}
    (h : Relation.EqvGen (graphRealizationGenerator (V := V)) x y) :
    (x ∈ graphEdgeInteriorPre e ↔ y ∈ graphEdgeInteriorPre e) := by
  induction h with
  | rel x y h =>
      cases h <;> simp [graphEdgeInteriorPre]
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The open interior of an edge in the graph realization. -/
def graphEdgeInterior {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) : Set (graphRealization V) :=
  graphRealizationQuotient '' graphEdgeInteriorPre e

theorem graphEdgeInterior_isOpen {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) : IsOpen (graphEdgeInterior e) :=
  graphRealization_image_isOpen_of_saturated
    (graphEdgeInteriorPre_saturated e) (graphEdgeInteriorPre_isOpen e)

theorem graphEdgeInterior_preimage {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) :
    graphRealizationQuotient ⁻¹' graphEdgeInterior e = graphEdgeInteriorPre e :=
  graphRealization_image_preimage_eq_of_saturated (graphEdgeInteriorPre_saturated e)

theorem graphEdgePath_mem_graphEdgeInterior {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) {t : I} (ht0 : 0 < t) (ht1 : t < 1) :
    graphEdgePath e t ∈ graphEdgeInterior e := by
  exact ⟨Sum.inr ⟨graphDiscreteEdge e, t⟩, by simp [graphEdgeInteriorPre, ht0, ht1], rfl⟩

/-- Records an interior edge representative and parameter, ignoring quotient endpoints. -/
def graphRealizationInteriorLabel {V : Type u} [Quiver.{u} V]
    : graphRealizationPre V → Option (Quiver.Total V × I)
  | Sum.inl _ => none
  | Sum.inr z =>
      if z.2 = 0 ∨ z.2 = 1 then none
      else some (graphEdgeUnderlying z.1, z.2)

theorem graphRealizationGenerator_interiorLabel {V : Type u}
    [Quiver.{u} V] {x y : graphRealizationPre V}
    (h : graphRealizationGenerator x y) :
    graphRealizationInteriorLabel x = graphRealizationInteriorLabel y := by
  cases h with
  | source e => simp [graphRealizationInteriorLabel]
  | target e => simp [graphRealizationInteriorLabel]

theorem graphRealization_eqvGen_interiorLabel {V : Type u}
    [Quiver.{u} V] {x y : graphRealizationPre V}
    (h : Relation.EqvGen (graphRealizationGenerator (V := V)) x y) :
    graphRealizationInteriorLabel x = graphRealizationInteriorLabel y := by
  induction h with
  | rel x y h => exact graphRealizationGenerator_interiorLabel h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem graphRealization_interior_eqvGen_eq {V : Type u}
    [Quiver.{u} V] {e e' : Quiver.Total V} {t t' : I}
    (ht0 : 0 < t) (ht1 : t < 1) (ht0' : 0 < t') (ht1' : t' < 1)
    (h : Relation.EqvGen (graphRealizationGenerator (V := V))
      (Sum.inr ⟨graphDiscreteEdge e, t⟩)
      (Sum.inr ⟨graphDiscreteEdge e', t'⟩)) :
    e = e' ∧ t = t' := by
  have hl := graphRealization_eqvGen_interiorLabel h
  have hne0 : t ≠ 0 := ne_of_gt ht0
  have hne1 : t ≠ 1 := ne_of_lt ht1
  have hne0' : t' ≠ 0 := ne_of_gt ht0'
  have hne1' : t' ≠ 1 := ne_of_lt ht1'
  simp only [graphRealizationInteriorLabel, hne0, hne1, hne0', hne1',
    false_or, ↓reduceIte, Option.some.injEq] at hl
  exact Prod.ext_iff.mp hl

theorem graphRealization_vertex_edge_endpoint {V : Type u} [Quiver.{u} V]
    {v : V} {e : Quiver.Total V} {t : I}
    (h : graphRealizationQuotient (Sum.inl (graphDiscreteVertex v)) =
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩)) :
    t = 0 ∨ t = 1 := by
  by_cases ht0 : t = 0
  · exact Or.inl ht0
  by_cases ht1 : t = 1
  · exact Or.inr ht1
  have hl := congrArg graphRealizationEndpointLabelQuotient h
  simp [graphRealizationEndpointLabelQuotient_mk,
    graphRealizationEndpointLabel, ht0, ht1] at hl

theorem graphRealization_vertex_edge_source {V : Type u} [Quiver.{u} V]
    {v : V} {e : Quiver.Total V} {t : I}
    (h : graphRealizationQuotient (Sum.inl (graphDiscreteVertex v)) =
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩))
    (ht : t = 0) : v = e.left := by
  simpa only [graphRealizationEndpointLabelQuotient_mk,
    graphRealizationEndpointLabel, ht, ↓reduceIte, Option.some.injEq] using
      congrArg graphRealizationEndpointLabelQuotient h

theorem graphRealization_vertex_edge_target {V : Type u} [Quiver.{u} V]
    {v : V} {e : Quiver.Total V} {t : I}
    (h : graphRealizationQuotient (Sum.inl (graphDiscreteVertex v)) =
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩))
    (ht : t = 1) : v = e.right := by
  simpa only [graphRealizationEndpointLabelQuotient_mk,
    graphRealizationEndpointLabel, ht, one_ne_zero, ↓reduceIte, Option.some.injEq] using
      congrArg graphRealizationEndpointLabelQuotient h

/-! The combinatorial cover viewed through the same geometric-realization
    construction. -/

/-- The realization of the canonical combinatorial cover based at `root`. -/
abbrev graphCoverRealization {V : Type u} [Quiver.{u} V] (root : V) :=
  graphRealization (graphCoverVertex root)

/-- The realization map induced by the canonical graph-cover projection. -/
def graphCoverRealizationProjection {V : Type u} [Quiver.{u} V] (root : V) :
    graphCoverRealization root → graphRealization V :=
  graphRealizationMap (graphCoverProjection root)

theorem continuous_graphCoverRealizationProjection
    {V : Type u} [Quiver.{u} V] (root : V) :
    Continuous (graphCoverRealizationProjection root) :=
  continuous_graphRealizationMap (graphCoverProjection root)

@[simp]
theorem graphRealizationMap_quotient {V W : Type u} [Quiver.{u} V]
    [Quiver.{u} W] (F : V ⥤q W) (x : graphRealizationPre V) :
    graphRealizationMap F (graphRealizationQuotient x) =
      graphRealizationQuotient (graphRealizationPreMap F x) := rfl

/-- The cover vertex represented by the identity path at the root. -/
def graphCoverRootVertex {V : Type u} [Quiver.{u} V] (root : V) :
    graphCoverVertex root :=
  ⟨root, 𝟙 _⟩

@[simp]
theorem graphCoverRootVertex_projection {V : Type u} [Quiver.{u} V]
    (root : V) : (graphCoverRootVertex root).1 = root := rfl

/-- The discrete fiber of cover vertices over a base vertex. -/
def graphCoverVertexOver {V : Type u} [Quiver.{u} V] (root v : V) :=
  {x : graphCoverVertex root // x.1 = v}

instance graphCoverVertexOverTopology {V : Type u} [Quiver.{u} V]
    (root v : V) : TopologicalSpace (graphCoverVertexOver root v) := ⊥

instance graphCoverVertexOver_discrete {V : Type u} [Quiver.{u} V]
    (root v : V) : DiscreteTopology (graphCoverVertexOver root v) := by
  exact discreteTopology_bot _

/-- The symmetric-edge prefunctor from the canonical cover into the base free groupoid. -/
def graphCoverSymmetricFreeGroupoidMap {V : Type u} [Quiver.{u} V]
    (root : V) :
    (Quiver.Symmetrify (graphCoverVertex root)) ⥤q
      Quiver.FreeGroupoid V :=
  Quiver.Symmetrify.lift
    ((graphCoverProjection root) ⋙q (Quiver.FreeGroupoid.of V))

theorem graphCoverSymmetricFreeGroupoidMap_map_pos
    {V : Type u} [Quiver.{u} V] (root : V) {x y : graphCoverVertex root}
    (e : x ⟶ y) :
    (graphCoverSymmetricFreeGroupoidMap root).map (Sum.inl e) =
      (Quiver.FreeGroupoid.of V).map e.1 := by
  rfl

theorem graphCoverVertexOver_nonempty {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] (root v : V) :
    Nonempty (graphCoverVertexOver root v) := by
  rcases WeaklyConnected.path root v with ⟨p⟩
  let φ := (graphCoverProjection root).symmetrify
  obtain ⟨q, hq⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨v, p⟩
  refine ⟨⟨q.1, ?_⟩⟩
  have hq' := congrArg Sigma.fst hq
  change q.1.1 = v at hq'
  exact hq'

theorem graphCoverPreMap_vertexStar_preimage {V : Type u} [Quiver.{u} V]
    {root v : V} :
    graphRealizationPreMap (graphCoverProjection root) ⁻¹'
        graphVertexStarPre v =
      ⋃ x : graphCoverVertexOver root v, graphVertexStarPre x.1 := by
  ext z
  cases z with
  | inl z =>
      constructor
      · intro hz
        have hz' : (graphVertexUnderlying z).1 = v := by
          simpa [graphRealizationPreMap, graphVertexStarPre,
            graphCoverProjection, graphVertexUnderlying,
            graphDiscreteVertex] using hz
        refine Set.mem_iUnion.mpr ?_
        refine ⟨⟨graphVertexUnderlying z, hz'⟩, ?_⟩
        simp [graphVertexStarPre]
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨x, hx⟩
        have hx' : graphVertexUnderlying z = x.1 := by
          simpa [graphVertexStarPre] using hx
        simp [graphRealizationPreMap, graphVertexStarPre,
          graphCoverProjection, graphVertexUnderlying,
          graphDiscreteVertex, hx', x.2]
  | inr z =>
      rcases z with ⟨z, t⟩
      let e : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying z
      constructor
      · intro hz
        change ((e.left.1 = v ∧ t < graphHalf) ∨
          (e.right.1 = v ∧ graphHalf < t)) at hz
        rcases hz with hz | hz
        · refine Set.mem_iUnion.mpr ⟨⟨e.left, hz.1⟩, ?_⟩
          simp only [graphVertexStarPre]
          exact Or.inl ⟨rfl, hz.2⟩
        · refine Set.mem_iUnion.mpr ⟨⟨e.right, hz.1⟩, ?_⟩
          simp only [graphVertexStarPre]
          exact Or.inr ⟨rfl, hz.2⟩
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨x, hx⟩
        change ((e.left.1 = v ∧ t < graphHalf) ∨
          (e.right.1 = v ∧ graphHalf < t))
        change (e.left = x.1 ∧ t < graphHalf) ∨
          (e.right = x.1 ∧ graphHalf < t) at hx
        rcases hx with hx | hx
        · exact Or.inl ⟨(by
            calc
              e.left.1 = x.1.1 := congrArg Sigma.fst hx.1
              _ = v := x.2), hx.2⟩
        · exact Or.inr ⟨(by
            calc
              e.right.1 = x.1.1 := congrArg Sigma.fst hx.1
              _ = v := x.2), hx.2⟩

theorem graphCoverVertexStarPre_union_saturated {V : Type u}
    [Quiver.{u} V] {root v : V}
    {x y : graphRealizationPre (graphCoverVertex root)}
    (h : Relation.EqvGen
      (graphRealizationGenerator (V := graphCoverVertex root)) x y) :
    ((x ∈ ⋃ z : graphCoverVertexOver root v, graphVertexStarPre z.1) ↔
      y ∈ ⋃ z : graphCoverVertexOver root v, graphVertexStarPre z.1) := by
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨z, (graphVertexStarPre_saturated z.1 h).mp hz⟩
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨z, (graphVertexStarPre_saturated z.1 h).mpr hz⟩

theorem graphCoverRealizationProjection_vertexStar_preimage
    {V : Type u} [Quiver.{u} V] {root v : V} :
    graphCoverRealizationProjection root ⁻¹' graphVertexStar v =
      ⋃ x : graphCoverVertexOver root v, graphVertexStar x.1 := by
  ext z
  refine Quotient.inductionOn z ?_
  intro z
  constructor
  · intro hz
    change graphRealizationMap (graphCoverProjection root)
        (graphRealizationQuotient z) ∈ graphVertexStar v at hz
    rw [graphRealizationMap_quotient] at hz
    have hz' : graphRealizationQuotient
        (graphRealizationPreMap (graphCoverProjection root) z) ∈
        graphVertexStar v := hz
    rcases hz' with ⟨y, hy, hzy⟩
    have hrel := Quotient.exact hzy
    have hpre : graphRealizationPreMap (graphCoverProjection root) z ∈
        graphVertexStarPre v := (graphVertexStarPre_saturated v hrel).mp hy
    have hzunion : z ∈
        ⋃ x : graphCoverVertexOver root v, graphVertexStarPre x.1 := by
      rw [← graphCoverPreMap_vertexStar_preimage]
      exact hpre
    rcases Set.mem_iUnion.mp hzunion with ⟨x, hx⟩
    exact Set.mem_iUnion.mpr ⟨x, ⟨z, hx, rfl⟩⟩
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨x, hx⟩
    rcases hx with ⟨y, hy, hzy⟩
    have hrel := Quotient.exact hzy
    have hyunion : y ∈
        ⋃ x : graphCoverVertexOver root v, graphVertexStarPre x.1 :=
      Set.mem_iUnion.mpr ⟨x, hy⟩
    have hzunion : z ∈
      ⋃ x : graphCoverVertexOver root v, graphVertexStarPre x.1 :=
      (graphCoverVertexStarPre_union_saturated hrel).mp hyunion
    have hpre : graphRealizationPreMap (graphCoverProjection root) z ∈
        graphVertexStarPre v := by
      have heq := (graphCoverPreMap_vertexStar_preimage (root := root) (v := v))
      change z ∈ graphRealizationPreMap (graphCoverProjection root) ⁻¹'
        graphVertexStarPre v
      rw [heq]
      exact hzunion
    change graphRealizationMap (graphCoverProjection root)
        (graphRealizationQuotient z) ∈ graphVertexStar v
    rw [graphRealizationMap_quotient]
    exact ⟨graphRealizationPreMap (graphCoverProjection root) z, hpre, rfl⟩

@[simp]
theorem graphCoverPreMap_vertex {V : Type u} [Quiver.{u} V]
    (root : V) (x : graphCoverVertex root) :
    graphRealizationPreMap (graphCoverProjection root)
        (Sum.inl (graphDiscreteVertex x)) =
      Sum.inl (graphDiscreteVertex x.1) := rfl

@[simp]
theorem graphCoverPreMap_edge {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) (t : I) :
    graphRealizationPreMap (graphCoverProjection root)
        (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
      Sum.inr ⟨graphDiscreteEdge
        ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩ := rfl

theorem graphVertexStar_disjoint {V : Type u} [Quiver.{u} V]
    {v w : V} (hvw : v ≠ w) :
    Disjoint (graphVertexStar v) (graphVertexStar w) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
  have hrel : Relation.EqvGen
      (graphRealizationGenerator (V := V)) b a :=
    Quotient.exact (hbz.trans haz.symm)
  have hba : b ∈ graphVertexStarPre v :=
    (graphVertexStarPre_saturated v hrel).mpr ha
  exact (Set.disjoint_left.mp
    (graphVertexStarPre_disjoint (v := w) (w := v) hvw.symm)) hb hba

theorem graphStar_total_injective {V : Type u} [Quiver.{u} V]
    {x : V} : Function.Injective (fun s : Quiver.Star x =>
      (⟨x, s.1, s.2⟩ : Quiver.Total V)) := by
  rintro ⟨y, e⟩ ⟨z, f⟩ h
  cases h
  rfl

theorem graphCostar_total_injective {V : Type u} [Quiver.{u} V]
    {x : V} : Function.Injective (fun s : Quiver.Costar x =>
      (⟨s.1, x, s.2⟩ : Quiver.Total V)) := by
  rintro ⟨y, e⟩ ⟨z, f⟩ h
  cases h
  rfl

theorem graphCoverStarEquiv_map_eq_of_total_eq
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root)
    (e f : Quiver.Total (graphCoverVertex root))
    (he : e.left = x) (hf : f.left = x)
    (htot : (⟨e.left.1, e.right.1, e.hom.1⟩ : Quiver.Total V) =
      ⟨f.left.1, f.right.1, f.hom.1⟩) :
    (graphCoverStarEquiv root x) ⟨e.right, he ▸ e.hom⟩ =
      (graphCoverStarEquiv root x) ⟨f.right, hf ▸ f.hom⟩ := by
  change (graphCoverProjection root).star x
      ⟨e.right, he ▸ e.hom⟩ =
    (graphCoverProjection root).star x
      ⟨f.right, hf ▸ f.hom⟩
  apply Sigma.ext
  · exact (Quiver.Total.ext_iff.mp htot).2.1
  · change (he ▸ e.hom).1 ≍ (hf ▸ f.hom).1
    have hecast : (he ▸ e.hom).1 ≍ e.hom.1 := by
      cases he
      exact HEq.rfl
    have hfcast : (hf ▸ f.hom).1 ≍ f.hom.1 := by
      cases hf
      exact HEq.rfl
    have hh := (Quiver.Total.ext_iff.mp htot).2.2
    exact hecast.trans (hh.trans hfcast.symm)

theorem graphCoverCostarEquiv_map_eq_of_total_eq
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root)
    (e f : Quiver.Total (graphCoverVertex root))
    (he : e.right = x) (hf : f.right = x)
    (htot : (⟨e.left.1, e.right.1, e.hom.1⟩ : Quiver.Total V) =
      ⟨f.left.1, f.right.1, f.hom.1⟩) :
    (graphCoverCostarEquiv root x) ⟨e.left, he ▸ e.hom⟩ =
      (graphCoverCostarEquiv root x) ⟨f.left, hf ▸ f.hom⟩ := by
  change (graphCoverProjection root).costar x
      ⟨e.left, he ▸ e.hom⟩ =
    (graphCoverProjection root).costar x
      ⟨f.left, hf ▸ f.hom⟩
  apply Sigma.ext
  · exact (Quiver.Total.ext_iff.mp htot).1
  · change (he ▸ e.hom).1 ≍ (hf ▸ f.hom).1
    have hecast : (he ▸ e.hom).1 ≍ e.hom.1 := by
      cases he
      exact HEq.rfl
    have hfcast : (hf ▸ f.hom).1 ≍ f.hom.1 := by
      cases hf
      exact HEq.rfl
    have hh := (Quiver.Total.ext_iff.mp htot).2.2
    exact hecast.trans (hh.trans hfcast.symm)

theorem graphCover_total_eq_of_star_eq
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root)
    (e f : Quiver.Total (graphCoverVertex root))
    (he : e.left = x) (hf : f.left = x)
    (hstar : (⟨e.right, he ▸ e.hom⟩ : Quiver.Star x) =
      ⟨f.right, hf ▸ f.hom⟩) : e = f := by
  have hright : e.right = f.right := congrArg Sigma.fst hstar
  have hhom := (Sigma.ext_iff.mp hstar).2
  change (he ▸ e.hom) ≍ (hf ▸ f.hom) at hhom
  have hecast : he ▸ e.hom ≍ e.hom := by
    exact eqRec_heq (φ := fun z : graphCoverVertex root => z ⟶ e.right)
      he e.hom
  have hfcast : hf ▸ f.hom ≍ f.hom := by
    exact eqRec_heq (φ := fun z : graphCoverVertex root => z ⟶ f.right)
      hf f.hom
  exact Quiver.Total.ext (he.trans hf.symm) hright
    (hecast.symm.trans (hhom.trans hfcast))

theorem graphCover_total_eq_of_costar_eq
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root)
    (e f : Quiver.Total (graphCoverVertex root))
    (he : e.right = x) (hf : f.right = x)
    (hcostar : (⟨e.left, he ▸ e.hom⟩ : Quiver.Costar x) =
      ⟨f.left, hf ▸ f.hom⟩) : e = f := by
  have hleft : e.left = f.left := congrArg Sigma.fst hcostar
  have hhom := (Sigma.ext_iff.mp hcostar).2
  change (he ▸ e.hom) ≍ (hf ▸ f.hom) at hhom
  have hecast : he ▸ e.hom ≍ e.hom := by
    exact eqRec_heq (φ := fun z : graphCoverVertex root => e.left ⟶ z)
      he e.hom
  have hfcast : hf ▸ f.hom ≍ f.hom := by
    exact eqRec_heq (φ := fun z : graphCoverVertex root => f.left ⟶ z)
      hf f.hom
  exact Quiver.Total.ext hleft (he.trans hf.symm)
    (hecast.symm.trans (hhom.trans hfcast))

theorem graphCover_source_lift
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root) (e : Quiver.Total V)
    (h : x.1 = e.left) :
    ∃ d : Quiver.Total (graphCoverVertex root),
      d.left = x ∧
        (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) = e := by
  let s : Quiver.Star x.1 := ⟨e.right, h.symm ▸ e.hom⟩
  let l : Quiver.Star x := (graphCoverStarEquiv root x).symm s
  let d : Quiver.Total (graphCoverVertex root) := ⟨x, l.1, l.2⟩
  refine ⟨d, rfl, ?_⟩
  have hl := (graphCoverStarEquiv root x).apply_symm_apply s
  change (⟨l.1.1, l.2.1⟩ : Quiver.Star x.1) = s at hl
  have hl' := (Sigma.ext_iff.mp hl).2
  have hright : l.1.1 = e.right := congrArg Sigma.fst hl
  have hhom : l.2.1 ≍ h.symm ▸ e.hom := hl'
  change (⟨x.1, l.1.1, l.2.1⟩ : Quiver.Total V) = e
  refine Quiver.Total.ext h hright ?_
  exact hhom.trans (by
    exact eqRec_heq (φ := fun z : V => z ⟶ e.right) h.symm e.hom)

theorem graphCover_target_lift
    {V : Type u} [Quiver.{u} V] {root : V}
    (x : graphCoverVertex root) (e : Quiver.Total V)
    (h : e.right = x.1) :
    ∃ d : Quiver.Total (graphCoverVertex root),
      d.right = x ∧
        (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) = e := by
  let s : Quiver.Costar x.1 := ⟨e.left, h ▸ e.hom⟩
  let l : Quiver.Costar x := (graphCoverCostarEquiv root x).symm s
  let d : Quiver.Total (graphCoverVertex root) := ⟨l.1, x, l.2⟩
  refine ⟨d, rfl, ?_⟩
  have hl := (graphCoverCostarEquiv root x).apply_symm_apply s
  change (⟨l.1.1, l.2.1⟩ : Quiver.Costar x.1) = s at hl
  have hl' := (Sigma.ext_iff.mp hl).2
  have hleft : l.1.1 = e.left := congrArg Sigma.fst hl
  have hhom : l.2.1 ≍ h ▸ e.hom := hl'
  change (⟨l.1.1, x.1, l.2.1⟩ : Quiver.Total V) = e
  refine Quiver.Total.ext hleft h.symm ?_
  exact hhom.trans (by
    exact eqRec_heq h e.hom)

private theorem graphCoverRealizationProjection_vertexStar_injective_vertex
    {V : Type u} [Quiver.{u} V] {root v : V}
    (x : graphCoverVertexOver root v)
    (av : WithDiscreteTopology (graphCoverVertex root))
    (ha₀ : (Sum.inl av : graphRealizationPre (graphCoverVertex root)) ∈
      graphVertexStarPre x.1)
    (b₀ : graphRealizationPre (graphCoverVertex root))
    (hb₀ : b₀ ∈ graphVertexStarPre x.1)
    (hbase :
      graphRealizationQuotient
          (graphRealizationPreMap (graphCoverProjection root) (Sum.inl av)) =
        graphRealizationQuotient
          (graphRealizationPreMap (graphCoverProjection root) b₀)) :
    graphRealizationQuotient (Sum.inl av) = graphRealizationQuotient b₀ := by
  have hav : graphVertexUnderlying av = x.1 := by
    simpa [graphVertexStarPre] using ha₀
  cases b₀ with
  | inl bv =>
      have hbv : graphVertexUnderlying bv = x.1 := by
        simpa [graphVertexStarPre] using hb₀
      exact congrArg graphVertex (hav.trans hbv.symm)
  | inr bz =>
      rcases bz with ⟨bz, t⟩
      let e : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying bz
      change ((e.left = x.1 ∧ t < graphHalf) ∨
        (e.right = x.1 ∧ graphHalf < t)) at hb₀
      have hbase' :
          graphRealizationQuotient
              (Sum.inl (graphDiscreteVertex (graphVertexUnderlying av).1)) =
            graphRealizationQuotient
              (Sum.inr ⟨graphDiscreteEdge
                ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩) := by
        simpa [graphRealizationPreMap, graphCoverProjection,
          graphVertexUnderlying, graphDiscreteVertex,
          graphEdgeUnderlying, graphDiscreteEdge, e] using hbase
      have hbz : bz = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      rw [hbz]
      rcases graphRealization_vertex_edge_endpoint hbase' with ht | ht
      · have hes : e.left = x.1 := by
          rcases hb₀ with hb₀ | hb₀
          · exact hb₀.1
          · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_pos)) (ht ▸ hb₀.2))
        calc
          graphRealizationQuotient (Sum.inl (graphDiscreteVertex
              (graphVertexUnderlying av))) =
              graphRealizationQuotient (Sum.inl (graphDiscreteVertex e.left)) := by
                exact congrArg (fun z : graphCoverVertex root =>
                  graphRealizationQuotient (Sum.inl (graphDiscreteVertex z)))
                  (hav.trans hes.symm)
          _ = graphRealizationQuotient (Sum.inr
              ⟨graphDiscreteEdge e, 0⟩) := (graphEdgePath_zero e).symm
          _ = graphRealizationQuotient (Sum.inr
              ⟨graphDiscreteEdge e, t⟩) := by rw [ht]
      · have het : e.right = x.1 := by
          rcases hb₀ with hb₀ | hb₀
          · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_lt_one)) (ht ▸ hb₀.2))
          · exact hb₀.1
        calc
          graphRealizationQuotient (Sum.inl (graphDiscreteVertex
              (graphVertexUnderlying av))) =
              graphRealizationQuotient (Sum.inl (graphDiscreteVertex e.right)) := by
                exact congrArg (fun z : graphCoverVertex root =>
                  graphRealizationQuotient (Sum.inl (graphDiscreteVertex z)))
                  (hav.trans het.symm)
          _ = graphRealizationQuotient (Sum.inr
              ⟨graphDiscreteEdge e, 1⟩) := (graphEdgePath_one e).symm
          _ = graphRealizationQuotient (Sum.inr
              ⟨graphDiscreteEdge e, t⟩) := by rw [ht]

private theorem graphCoverRealizationProjection_vertexStar_injective_edge_vertex
    {V : Type u} [Quiver.{u} V] {root v : V}
    (x : graphCoverVertexOver root v)
    (e : Quiver.Total (graphCoverVertex root)) (t : I)
    (ha₀ : (e.left = x.1 ∧ t < graphHalf) ∨
      (e.right = x.1 ∧ graphHalf < t))
    (bv : WithDiscreteTopology (graphCoverVertex root))
    (hbv : graphVertexUnderlying bv = x.1)
    (hbase :
      graphRealizationQuotient
          (Sum.inl (graphDiscreteVertex (graphVertexUnderlying bv).1)) =
        graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge
            ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩)) :
    graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
      graphRealizationQuotient (Sum.inl bv) := by
  rcases graphRealization_vertex_edge_endpoint hbase with ht | ht
  · have hes : e.left = x.1 := by
      rcases ha₀ with ha₀ | ha₀
      · exact ha₀.1
      · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_pos)) (ht ▸ ha₀.2))
    calc
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
          graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, 0⟩) := by rw [ht]
      _ = graphRealizationQuotient (Sum.inl (graphDiscreteVertex e.left)) :=
        graphEdgePath_zero e
      _ = graphRealizationQuotient (Sum.inl
          (graphDiscreteVertex (graphVertexUnderlying bv))) := by
            exact congrArg (fun z : graphCoverVertex root =>
              graphRealizationQuotient (Sum.inl (graphDiscreteVertex z)))
              (hes.trans hbv.symm)
  · have het : e.right = x.1 := by
      rcases ha₀ with ha₀ | ha₀
      · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_lt_one)) (ht ▸ ha₀.2))
      · exact ha₀.1
    calc
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
          graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, 1⟩) := by rw [ht]
      _ = graphRealizationQuotient (Sum.inl (graphDiscreteVertex e.right)) :=
        graphEdgePath_one e
      _ = graphRealizationQuotient (Sum.inl
          (graphDiscreteVertex (graphVertexUnderlying bv))) := by
            exact congrArg (fun z : graphCoverVertex root =>
              graphRealizationQuotient (Sum.inl (graphDiscreteVertex z)))
              (het.trans hbv.symm)

private theorem graphVertexStar_edge_endpoint
    {V : Type u} [Quiver.{u} V] {root v : V}
    (x : graphCoverVertexOver root v)
    (e : Quiver.Total (graphCoverVertex root)) (t : I)
    (hstar : (e.left = x.1 ∧ t < graphHalf) ∨
      (e.right = x.1 ∧ graphHalf < t))
    (hendpoint : t = 0 ∨ t = 1) :
    graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
      graphRealizationQuotient (Sum.inl (graphDiscreteVertex x.1)) := by
  rcases hendpoint with ht | ht
  · have he : e.left = x.1 := by
      rcases hstar with hstar | hstar
      · exact hstar.1
      · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_pos)) (ht ▸ hstar.2))
    rw [ht]
    exact (graphEdgePath_zero e).trans (congrArg graphVertex he)
  · have he : e.right = x.1 := by
      rcases hstar with hstar | hstar
      · exact False.elim ((not_lt_of_ge (le_of_lt graphHalf_lt_one)) (ht ▸ hstar.2))
      · exact hstar.1
    rw [ht]
    exact (graphEdgePath_one e).trans (congrArg graphVertex he)

private theorem graphCoverRealizationProjection_vertexStar_injective_edges
    {V : Type u} [Quiver.{u} V] {root v : V}
    (x : graphCoverVertexOver root v)
    (e f : Quiver.Total (graphCoverVertex root)) (t t' : I)
    (ha₀ : (e.left = x.1 ∧ t < graphHalf) ∨
      (e.right = x.1 ∧ graphHalf < t))
    (hb₀ : (f.left = x.1 ∧ t' < graphHalf) ∨
      (f.right = x.1 ∧ graphHalf < t'))
    (hbase :
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩) =
        graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge ⟨f.left.1, f.right.1, f.hom.1⟩, t'⟩)) :
    graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge e, t⟩) =
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge f, t'⟩) := by
  let eb : Quiver.Total V := ⟨e.left.1, e.right.1, e.hom.1⟩
  let fb : Quiver.Total V := ⟨f.left.1, f.right.1, f.hom.1⟩
  have hbase' :
      graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge eb, t⟩) =
        graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge fb, t'⟩) := by
    simpa [eb, fb] using hbase
  by_cases ht0 : t = 0
  · have hvertex :
        graphRealizationQuotient (Sum.inl (graphDiscreteVertex eb.left)) =
          graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge fb, t'⟩) := by
      have hbase0 :
          graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge eb, 0⟩) =
            graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge fb, t'⟩) := by
        simpa [ht0] using hbase'
      exact (graphEdgePath_zero eb).symm.trans hbase0
    rcases graphRealization_vertex_edge_endpoint hvertex with ht'0 | ht'1
    · exact (graphVertexStar_edge_endpoint x e t ha₀ (Or.inl ht0)).trans
        (graphVertexStar_edge_endpoint x f t' hb₀ (Or.inl ht'0)).symm
    · exact (graphVertexStar_edge_endpoint x e t ha₀ (Or.inl ht0)).trans
        (graphVertexStar_edge_endpoint x f t' hb₀ (Or.inr ht'1)).symm
  · by_cases ht1 : t = 1
    · have hvertex :
          graphRealizationQuotient (Sum.inl (graphDiscreteVertex eb.right)) =
            graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge fb, t'⟩) := by
        have hbase1 :
            graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge eb, 1⟩) =
              graphRealizationQuotient (Sum.inr ⟨graphDiscreteEdge fb, t'⟩) := by
          simpa [ht1] using hbase'
        exact (graphEdgePath_one eb).symm.trans hbase1
      rcases graphRealization_vertex_edge_endpoint hvertex with ht'0 | ht'1
      · exact (graphVertexStar_edge_endpoint x e t ha₀ (Or.inr ht1)).trans
          (graphVertexStar_edge_endpoint x f t' hb₀ (Or.inl ht'0)).symm
      · exact (graphVertexStar_edge_endpoint x e t ha₀ (Or.inr ht1)).trans
          (graphVertexStar_edge_endpoint x f t' hb₀ (Or.inr ht'1)).symm
    · have ht0' : 0 < t := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      have ht1' : t < 1 := lt_of_le_of_ne t.2.2 ht1
      have ht0ne : t' ≠ 0 := by
        intro ht'
        have hl := graphRealization_eqvGen_interiorLabel (Quotient.exact hbase')
        simp [graphRealizationInteriorLabel, ht0, ht1, ht'] at hl
      have ht1ne : t' ≠ 1 := by
        intro ht'
        have hl := graphRealization_eqvGen_interiorLabel (Quotient.exact hbase')
        simp [graphRealizationInteriorLabel, ht0, ht1, ht'] at hl
      have heq := graphRealization_interior_eqvGen_eq
        ht0' ht1' (lt_of_le_of_ne t'.2.1 (Ne.symm ht0ne))
        (lt_of_le_of_ne t'.2.2 ht1ne) (Quotient.exact hbase')
      have hteq : t = t' := heq.2
      rcases ha₀ with ha₀ | ha₀
      · have hf : f.left = x.1 := by
          rcases hb₀ with hb₀ | hb₀
          · exact hb₀.1
          · exact False.elim ((not_lt_of_ge (le_of_lt ha₀.2)) (hteq ▸ hb₀.2))
        let se : Quiver.Star x.1 := ⟨e.right, ha₀.1 ▸ e.hom⟩
        let sf : Quiver.Star x.1 := ⟨f.right, hf ▸ f.hom⟩
        have hstar : se = sf := by
          apply (graphCoverStarEquiv root x.1).injective
          simpa [se, sf] using
            (graphCoverStarEquiv_map_eq_of_total_eq x.1 e f ha₀.1 hf heq.1)
        have hedge : e = f := graphCover_total_eq_of_star_eq x.1 e f ha₀.1 hf (by
          simpa [se, sf, ha₀.1, hf] using hstar)
        simp [hedge, hteq]
      · have hf : f.right = x.1 := by
          rcases hb₀ with hb₀ | hb₀
          · exact False.elim ((not_lt_of_ge (le_of_lt ha₀.2)) (hteq ▸ hb₀.2))
          · exact hb₀.1
        let ce : Quiver.Costar x.1 := ⟨e.left, ha₀.1 ▸ e.hom⟩
        let cf : Quiver.Costar x.1 := ⟨f.left, hf ▸ f.hom⟩
        have hcostar : ce = cf := by
          apply (graphCoverCostarEquiv root x.1).injective
          simpa [ce, cf] using
            (graphCoverCostarEquiv_map_eq_of_total_eq x.1 e f ha₀.1 hf heq.1)
        have hedge : e = f := graphCover_total_eq_of_costar_eq x.1 e f ha₀.1 hf (by
          simpa [ce, cf, ha₀.1, hf] using hcostar)
        simp [hedge, hteq]

theorem graphCoverRealizationProjection_vertexStar_injective
    {V : Type u} [Quiver.{u} V] {root v : V}
    (x : graphCoverVertexOver root v) :
    Set.InjOn (graphCoverRealizationProjection root)
      (graphVertexStar x.1) := by
  intro a ha b hb hab
  rcases ha with ⟨a₀, ha₀, rfl⟩
  rcases hb with ⟨b₀, hb₀, rfl⟩
  have hbase :
      graphRealizationQuotient
          (graphRealizationPreMap (graphCoverProjection root) a₀) =
        graphRealizationQuotient
          (graphRealizationPreMap (graphCoverProjection root) b₀) := by
    change graphCoverRealizationProjection root (graphRealizationQuotient a₀) =
      graphCoverRealizationProjection root (graphRealizationQuotient b₀) at hab
    simpa only [graphRealizationMap_quotient,
      graphCoverRealizationProjection] using hab
  cases a₀ with
  | inl av =>
      exact graphCoverRealizationProjection_vertexStar_injective_vertex
        x av ha₀ b₀ hb₀ hbase
  | inr az =>
      rcases az with ⟨az, t⟩
      let e : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying az
      change ((e.left = x.1 ∧ t < graphHalf) ∨
        (e.right = x.1 ∧ graphHalf < t)) at ha₀
      have haz : az = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      cases b₀ with
      | inl bv =>
          have hbv : graphVertexUnderlying bv = x.1 := by
            simpa [graphVertexStarPre] using hb₀
          have hbase' :
              graphRealizationQuotient
                  (Sum.inl (graphDiscreteVertex (graphVertexUnderlying bv).1)) =
                graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge
                    ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩) := by
            simpa [graphRealizationPreMap, graphCoverProjection,
              graphVertexUnderlying, graphDiscreteVertex,
              graphEdgeUnderlying, graphDiscreteEdge, e] using hbase.symm
          rw [haz]
          exact graphCoverRealizationProjection_vertexStar_injective_edge_vertex
            x e t ha₀ bv hbv hbase'
      | inr bz =>
          rcases bz with ⟨bz, t'⟩
          let f : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying bz
          change ((f.left = x.1 ∧ t' < graphHalf) ∨
            (f.right = x.1 ∧ graphHalf < t')) at hb₀
          have hbase' :
              graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge
                    ⟨e.left.1, e.right.1, e.hom.1⟩, t⟩) =
                graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge
                    ⟨f.left.1, f.right.1, f.hom.1⟩, t'⟩) := by
            simpa [graphRealizationPreMap, graphCoverProjection,
              graphEdgeUnderlying, graphDiscreteEdge, e, f] using hbase
          have hbz : bz = graphDiscreteEdge f := by
            simp [f, graphDiscreteEdge, graphEdgeUnderlying]
          rw [haz, hbz]
          exact graphCoverRealizationProjection_vertexStar_injective_edges
            x e f t t' ha₀ hb₀ hbase'

theorem graphCoverRealizationProjection_vertexStar_surjective
    {V : Type u} [Quiver.{u} V]
    {root v : V} (x : graphCoverVertexOver root v) :
    Set.SurjOn (graphCoverRealizationProjection root)
      (graphVertexStar x.1) (graphVertexStar v) := by
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  cases z with
  | inl zv =>
      have hzv : graphVertexUnderlying zv = v := by
        simpa [graphVertexStarPre] using hz
      have hp :
          graphCoverRealizationProjection root (graphVertex (x.1)) =
            graphRealizationQuotient
              (Sum.inl (graphDiscreteVertex (graphVertexUnderlying zv))) := by
        change graphRealizationMap (graphCoverProjection root)
          (graphVertex (x.1)) = _
        rw [graphRealizationMap_vertex]
        exact congrArg graphVertex (x.2.trans hzv.symm)
      refine ⟨graphVertex (x.1), graphVertex_mem_graphVertexStar x.1, ?_⟩
      exact hp.trans hzy
  | inr z =>
      rcases z with ⟨ze, t⟩
      let e : Quiver.Total V := graphEdgeUnderlying ze
      have hze : ze = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      rw [hze] at hzy
      change ((e.left = v ∧ t < graphHalf) ∨
        (e.right = v ∧ graphHalf < t)) at hz
      rcases hz with hz | hz
      · obtain ⟨d, hdl, hde⟩ := graphCover_source_lift x.1 e
          (x.2.trans hz.1.symm)
        refine ⟨graphEdgePath d t, ?_, ?_⟩
        · refine ⟨Sum.inr ⟨graphDiscreteEdge d, t⟩, ?_, rfl⟩
          simp [graphVertexStarPre, graphEdgeUnderlying, graphDiscreteEdge,
            hdl, hz.2]
        · calc
            graphCoverRealizationProjection root (graphEdgePath d t) =
                graphEdgePath
                  (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
              exact graphRealizationMap_edgePath
                (graphCoverProjection root) d t
            _ = graphEdgePath e t := by rw [hde]
            _ = y := hzy
      · obtain ⟨d, hdr, hde⟩ := graphCover_target_lift x.1 e
          (hz.1.trans x.2.symm)
        refine ⟨graphEdgePath d t, ?_, ?_⟩
        · refine ⟨Sum.inr ⟨graphDiscreteEdge d, t⟩, ?_, rfl⟩
          simp [graphVertexStarPre, graphEdgeUnderlying, graphDiscreteEdge,
            hdr, hz.2]
        · calc
            graphCoverRealizationProjection root (graphEdgePath d t) =
                graphEdgePath
                  (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
              exact graphRealizationMap_edgePath
                (graphCoverProjection root) d t
            _ = graphEdgePath e t := by rw [hde]
            _ = y := hzy

theorem graphCoverRealizationProjection_vertexStar_open_iff
    {V : Type u} [Quiver.{u} V]
    {root v : V} (x : graphCoverVertexOver root v)
    {W : Set (graphRealization V)} (hW : W ⊆ graphVertexStar v) :
    IsOpen W ↔ IsOpen
      (graphCoverRealizationProjection root ⁻¹' W ∩ graphVertexStar x.1) := by
  constructor
  · intro hopen
    exact (hopen.preimage
      (continuous_graphCoverRealizationProjection root)).inter
      (graphVertexStar_isOpen x.1)
  · intro hopen
    have hopen_cover : IsOpen
        (graphRealizationQuotient ⁻¹'
          (graphCoverRealizationProjection root ⁻¹' W ∩
            graphVertexStar x.1)) :=
      (graphRealization_isOpen_iff.mp hopen)
    have hbase_pre : IsOpen (graphRealizationQuotient ⁻¹' W) := by
      rw [isOpen_sum_iff]
      constructor
      · exact isOpen_discrete _
      · rw [isOpen_sigma_iff]
        intro eb
        change IsOpen {t : I | graphEdgePath
          (graphEdgeUnderlying eb) t ∈ W}
        let e : Quiver.Total V := graphEdgeUnderlying eb
        have hdecomp :
            {t : I | graphEdgePath e t ∈ W} =
              {t : I | e.left = v ∧ t < graphHalf ∧
                graphEdgePath e t ∈ W} ∪
              {t : I | e.right = v ∧ graphHalf < t ∧
                graphEdgePath e t ∈ W} := by
          ext t
          constructor
          · intro ht
            have hstar :
                Sum.inr ⟨graphDiscreteEdge e, t⟩ ∈
                  graphVertexStarPre v := by
              rw [← graphVertexStar_preimage]
              exact hW ht
            change ((e.left = v ∧ t < graphHalf) ∨
              (e.right = v ∧ graphHalf < t)) at hstar
            rcases hstar with hstar | hstar
            · exact Or.inl ⟨hstar.1, hstar.2, ht⟩
            · exact Or.inr ⟨hstar.1, hstar.2, ht⟩
          · intro ht
            rcases ht with ht | ht
            · exact ht.2.2
            · exact ht.2.2
        have hsource_open :
            IsOpen {t : I | t < graphHalf ∧ graphEdgePath e t ∈ W} := by
          by_cases hev : e.left = v
          · obtain ⟨d, hdl, hde⟩ := graphCover_source_lift x.1 e
              (x.2.trans hev.symm)
            have hopen_d : IsOpen
                ((graphEdgePath d) ⁻¹'
                  (graphCoverRealizationProjection root ⁻¹' W ∩
                    graphVertexStar x.1)) :=
              hopen.preimage (graphEdgePath d).continuous
            have hset :
                {t : I | t < graphHalf ∧ graphEdgePath e t ∈ W} =
                  (graphEdgePath d) ⁻¹'
                    (graphCoverRealizationProjection root ⁻¹' W ∩
                      graphVertexStar x.1) ∩
                    {t : I | t < graphHalf} := by
              ext t
              constructor
              · rintro ⟨ht, htW⟩
                have hmap :
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                      graphEdgePath e t := by
                  calc
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                        graphEdgePath
                          (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
                      exact graphRealizationMap_edgePath
                        (graphCoverProjection root) d t
                    _ = graphEdgePath e t := by rw [hde]
                have hmem : graphEdgePath d t ∈ graphVertexStar x.1 := by
                  refine ⟨Sum.inr ⟨graphDiscreteEdge d, t⟩, ?_, rfl⟩
                  simp [graphVertexStarPre, graphEdgeUnderlying,
                    graphDiscreteEdge, hdl, ht]
                have hmapW :
                    graphCoverRealizationProjection root (graphEdgePath d t) ∈ W :=
                  hmap.symm ▸ htW
                exact ⟨⟨hmapW, hmem⟩, ht⟩
              · rintro ⟨htA, ht⟩
                have hmap :
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                      graphEdgePath e t := by
                  calc
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                        graphEdgePath
                          (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
                      exact graphRealizationMap_edgePath
                        (graphCoverProjection root) d t
                    _ = graphEdgePath e t := by rw [hde]
                exact ⟨ht, hmap ▸ htA.1⟩
            rw [hset]
            exact hopen_d.inter isOpen_Iio
          · have hempty : {t : I |
                t < graphHalf ∧ graphEdgePath e t ∈ W} = ∅ := by
              ext t
              constructor
              · rintro ⟨ht, htW⟩
                have hstar :
                    Sum.inr ⟨graphDiscreteEdge e, t⟩ ∈
                      graphVertexStarPre v := by
                  rw [← graphVertexStar_preimage]
                  exact hW htW
                change ((e.left = v ∧ t < graphHalf) ∨
                  (e.right = v ∧ graphHalf < t)) at hstar
                rcases hstar with hstar | hstar
                · exact (hev hstar.1).elim
                · exact (not_lt_of_ge (le_of_lt hstar.2)) ht
              · intro ht
                exact False.elim (by simp at ht)
            rw [hempty]
            exact isOpen_empty
        have htarget_open :
            IsOpen {t : I | graphHalf < t ∧ graphEdgePath e t ∈ W} := by
          by_cases hev : e.right = v
          · obtain ⟨d, hdr, hde⟩ := graphCover_target_lift x.1 e
              (hev.trans x.2.symm)
            have hopen_d : IsOpen
                ((graphEdgePath d) ⁻¹'
                  (graphCoverRealizationProjection root ⁻¹' W ∩
                    graphVertexStar x.1)) :=
              hopen.preimage (graphEdgePath d).continuous
            have hset :
                {t : I | graphHalf < t ∧ graphEdgePath e t ∈ W} =
                  (graphEdgePath d) ⁻¹'
                    (graphCoverRealizationProjection root ⁻¹' W ∩
                      graphVertexStar x.1) ∩
                    {t : I | graphHalf < t} := by
              ext t
              constructor
              · rintro ⟨ht, htW⟩
                have hmap :
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                      graphEdgePath e t := by
                  calc
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                        graphEdgePath
                          (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
                      exact graphRealizationMap_edgePath
                        (graphCoverProjection root) d t
                    _ = graphEdgePath e t := by rw [hde]
                have hmem : graphEdgePath d t ∈ graphVertexStar x.1 := by
                  refine ⟨Sum.inr ⟨graphDiscreteEdge d, t⟩, ?_, rfl⟩
                  simp [graphVertexStarPre, graphEdgeUnderlying,
                    graphDiscreteEdge, hdr, ht]
                have hmapW :
                    graphCoverRealizationProjection root (graphEdgePath d t) ∈ W :=
                  hmap.symm ▸ htW
                exact ⟨⟨hmapW, hmem⟩, ht⟩
              · rintro ⟨htA, ht⟩
                have hmap :
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                      graphEdgePath e t := by
                  calc
                    graphCoverRealizationProjection root (graphEdgePath d t) =
                        graphEdgePath
                          (⟨d.left.1, d.right.1, d.hom.1⟩ : Quiver.Total V) t := by
                      exact graphRealizationMap_edgePath
                        (graphCoverProjection root) d t
                    _ = graphEdgePath e t := by rw [hde]
                exact ⟨ht, hmap ▸ htA.1⟩
            rw [hset]
            exact hopen_d.inter isOpen_Ioi
          · have hempty : {t : I |
                graphHalf < t ∧ graphEdgePath e t ∈ W} = ∅ := by
              ext t
              constructor
              · rintro ⟨ht, htW⟩
                have hstar :
                    Sum.inr ⟨graphDiscreteEdge e, t⟩ ∈
                      graphVertexStarPre v := by
                  rw [← graphVertexStar_preimage]
                  exact hW htW
                change ((e.left = v ∧ t < graphHalf) ∨
                  (e.right = v ∧ graphHalf < t)) at hstar
                rcases hstar with hstar | hstar
                · exact (not_lt_of_ge (le_of_lt hstar.2)) ht
                · exact (hev hstar.1).elim
              · intro ht
                exact False.elim (by simp at ht)
            rw [hempty]
            exact isOpen_empty
        have hsource' : IsOpen {t : I |
            e.left = v ∧ t < graphHalf ∧ graphEdgePath e t ∈ W} := by
          by_cases hev : e.left = v
          · simpa [hev] using hsource_open
          · simp [hev]
        have htarget' : IsOpen {t : I |
            e.right = v ∧ graphHalf < t ∧ graphEdgePath e t ∈ W} := by
          by_cases hev : e.right = v
          · simpa [hev] using htarget_open
          · simp [hev]
        rw [hdecomp]
        exact hsource'.union htarget'
    exact graphRealization_isOpen_iff.mpr hbase_pre

/-- The forward open-set implication used by the vertex-star trivialization. -/
theorem graphCoverRealizationProjection_vertexStar_open
    {V : Type u} [Quiver.{u} V]
    {root v : V} (x : graphCoverVertexOver root v)
    {W : Set (graphRealization V)} (hW : W ⊆ graphVertexStar v)
    (hopen : IsOpen W) :
    IsOpen (graphCoverRealizationProjection root ⁻¹' W ∩ graphVertexStar x.1) :=
  (graphCoverRealizationProjection_vertexStar_open_iff x hW).mp hopen

/-- Projects a total edge of the canonical cover to its underlying base edge. -/
def graphCoverEdgeProjection {V : Type u} [Quiver.{u} V] (root : V)
    (d : Quiver.Total (graphCoverVertex root)) : Quiver.Total V :=
  ⟨d.left.1, d.right.1, d.hom.1⟩

/-- The discrete fiber of cover edges over a base edge. -/
def graphCoverEdgeOver {V : Type u} [Quiver.{u} V] (root : V)
    (e : Quiver.Total V) :=
  {d : Quiver.Total (graphCoverVertex root) //
    graphCoverEdgeProjection root d = e}

instance graphCoverEdgeOverTopology {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total V) :
    TopologicalSpace (graphCoverEdgeOver root e) := ⊥

instance graphCoverEdgeOver_discrete {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total V) :
    DiscreteTopology (graphCoverEdgeOver root e) := by
  exact discreteTopology_bot _

theorem graphEdgeInterior_disjoint {V : Type u} [Quiver.{u} V]
    {e f : Quiver.Total V} (hef : e ≠ f) :
    Disjoint (graphEdgeInterior e) (graphEdgeInterior f) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
  have hrel : Relation.EqvGen
      (graphRealizationGenerator (V := V)) b a :=
    Quotient.exact (hbz.trans haz.symm)
  have hba : b ∈ graphEdgeInteriorPre e :=
    (graphEdgeInteriorPre_saturated e hrel).mpr ha
  cases b with
  | inl bv =>
      simp [graphEdgeInteriorPre] at hba
  | inr bz =>
      rcases bz with ⟨bz, t⟩
      have hbe' : bz = graphDiscreteEdge e ∧ t ∈ Ioo (0 : I) 1 := by
        simpa [graphEdgeInteriorPre] using hba
      have hbe : bz = graphDiscreteEdge e := hbe'.1
      have hbf : bz = graphDiscreteEdge f := by
        have hbf'' : bz = graphDiscreteEdge f ∧ t ∈ Ioo (0 : I) 1 := by
          simpa [graphEdgeInteriorPre] using hb
        exact hbf''.1
      apply hef
      have h := congrArg graphEdgeUnderlying (hbe.symm.trans hbf)
      simpa [graphEdgeUnderlying, graphDiscreteEdge] using h

theorem graphCoverEdgeOver_nonempty {V : Type u} [Quiver.{u} V]
    [WeaklyConnected V] {root : V} (e : Quiver.Total V) :
    Nonempty (graphCoverEdgeOver root e) := by
  rcases graphCoverVertexOver_nonempty root e.left with ⟨x⟩
  obtain ⟨d, _, hd⟩ := graphCover_source_lift x.1 e x.2
  exact ⟨⟨d, by simpa [graphCoverEdgeProjection] using hd⟩⟩

theorem graphCoverRealizationProjection_edgeInterior_injective
    {V : Type u} [Quiver.{u} V] {root : V}
    (d : Quiver.Total (graphCoverVertex root)) :
    Set.InjOn (graphCoverRealizationProjection root)
      (graphEdgeInterior d) := by
  intro a ha b hb hab
  rcases ha with ⟨a₀, ha₀, rfl⟩
  rcases hb with ⟨b₀, hb₀, rfl⟩
  cases a₀ with
  | inl av =>
      simp [graphEdgeInteriorPre] at ha₀
  | inr az =>
      rcases az with ⟨az, t⟩
      change az = graphDiscreteEdge d ∧ t ∈ Ioo (0 : I) 1 at ha₀
      rcases ha₀ with ⟨rfl, hta⟩
      cases b₀ with
      | inl bv =>
          simp [graphEdgeInteriorPre] at hb₀
      | inr bz =>
          rcases bz with ⟨bz, t'⟩
          change bz = graphDiscreteEdge d ∧ t' ∈ Ioo (0 : I) 1 at hb₀
          rcases hb₀ with ⟨rfl, htb⟩
          have hbase :
              graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge (graphCoverEdgeProjection root d), t⟩) =
                graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge (graphCoverEdgeProjection root d), t'⟩) := by
            change graphCoverRealizationProjection root
                (graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge d, t⟩)) =
              graphCoverRealizationProjection root
                (graphRealizationQuotient
                  (Sum.inr ⟨graphDiscreteEdge d, t'⟩)) at hab
            simpa [graphRealizationMap_quotient,
              graphCoverRealizationProjection, graphCoverPreMap_edge,
              graphCoverEdgeProjection] using hab
          have hteq := graphRealization_interior_eqvGen_eq
            hta.1 hta.2 htb.1 htb.2 (Quotient.exact hbase)
          simp [hteq.2]

theorem graphCoverRealizationProjection_edgeInterior_surjective
    {V : Type u} [Quiver.{u} V]
    {root : V} {e : Quiver.Total V}
    (d : graphCoverEdgeOver root e) :
    Set.SurjOn (graphCoverRealizationProjection root)
      (graphEdgeInterior d.1) (graphEdgeInterior e) := by
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  cases z with
  | inl zv =>
      simp [graphEdgeInteriorPre] at hz
  | inr z =>
      rcases z with ⟨ze, t⟩
      change ze = graphDiscreteEdge e ∧ t ∈ Ioo (0 : I) 1 at hz
      rcases hz with ⟨rfl, ht⟩
      refine ⟨graphEdgePath d.1 t, ?_, ?_⟩
      · exact graphEdgePath_mem_graphEdgeInterior d.1 ht.1 ht.2
      · calc
          graphCoverRealizationProjection root (graphEdgePath d.1 t) =
              graphEdgePath (graphCoverEdgeProjection root d.1) t := by
            exact graphRealizationMap_edgePath
              (graphCoverProjection root) d.1 t
          _ = graphEdgePath e t := by rw [d.2]
          _ = y := hzy

theorem graphCoverRealizationProjection_edgeInterior_open_iff
    {V : Type u} [Quiver.{u} V]
    {root : V} {e : Quiver.Total V}
    (d : graphCoverEdgeOver root e)
    {W : Set (graphRealization V)} (hW : W ⊆ graphEdgeInterior e) :
    IsOpen W ↔ IsOpen
      (graphCoverRealizationProjection root ⁻¹' W ∩
        graphEdgeInterior d.1) := by
  constructor
  · intro hopen
    exact (hopen.preimage
      (continuous_graphCoverRealizationProjection root)).inter
      (graphEdgeInterior_isOpen d.1)
  · intro hopen
    have hbase_pre : IsOpen (graphRealizationQuotient ⁻¹' W) := by
      rw [isOpen_sum_iff]
      constructor
      · change IsOpen {z : WithDiscreteTopology V |
          graphVertex (graphVertexUnderlying z) ∈ W}
        have hempty : {z : WithDiscreteTopology V |
            graphVertex (graphVertexUnderlying z) ∈ W} = ∅ := by
          ext z
          constructor
          · intro hz
            have hi : graphVertex (graphVertexUnderlying z) ∈
                graphEdgeInterior e := hW hz
            have hipre :
                Sum.inl (graphDiscreteVertex (graphVertexUnderlying z)) ∈
                  graphEdgeInteriorPre e := by
              rw [← graphEdgeInterior_preimage]
              exact hi
            simp [graphEdgeInteriorPre] at hipre
          · intro hz
            exact False.elim (by simp at hz)
        rw [hempty]
        exact isOpen_empty
      · rw [isOpen_sigma_iff]
        intro eb
        let e' : Quiver.Total V := graphEdgeUnderlying eb
        change IsOpen {t : I | graphEdgePath e' t ∈ W}
        by_cases he' : e' = e
        · have hde : graphCoverEdgeProjection root d.1 = e := d.2
          have hopen_d : IsOpen
              ((graphEdgePath d.1) ⁻¹'
                (graphCoverRealizationProjection root ⁻¹' W ∩
                  graphEdgeInterior d.1)) :=
            hopen.preimage (graphEdgePath d.1).continuous
          have hset :
              {t : I | graphEdgePath e' t ∈ W} =
                (graphEdgePath d.1) ⁻¹'
                  (graphCoverRealizationProjection root ⁻¹' W ∩
                    graphEdgeInterior d.1) := by
            ext t
            constructor
            · intro htW
              have htint : t ∈ Ioo (0 : I) 1 := by
                have hi :
                    Sum.inr ⟨graphDiscreteEdge e, t⟩ ∈
                      graphEdgeInteriorPre e := by
                  rw [← graphEdgeInterior_preimage]
                  exact hW (he' ▸ htW)
                simpa [graphEdgeInteriorPre] using hi
              have hmap :
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) = graphEdgePath e t := by
                calc
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) =
                      graphEdgePath (graphCoverEdgeProjection root d.1) t := by
                    exact graphRealizationMap_edgePath
                      (graphCoverProjection root) d.1 t
                  _ = graphEdgePath e t := by rw [hde]
              have hmem : graphEdgePath d.1 t ∈ graphEdgeInterior d.1 :=
                graphEdgePath_mem_graphEdgeInterior d.1 htint.1 htint.2
              have hmapW :
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) ∈ W :=
                hmap.symm ▸ (he' ▸ htW)
              exact ⟨hmapW, hmem⟩
            · rintro ⟨htA, _⟩
              have hmap :
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) = graphEdgePath e t := by
                calc
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) =
                      graphEdgePath (graphCoverEdgeProjection root d.1) t := by
                    exact graphRealizationMap_edgePath
                      (graphCoverProjection root) d.1 t
                  _ = graphEdgePath e t := by rw [hde]
              have htAW :
                  graphCoverRealizationProjection root
                      (graphEdgePath d.1 t) ∈ W := htA
              have htW : graphEdgePath e t ∈ W := hmap ▸ htAW
              exact he'.symm ▸ htW
          rw [hset]
          exact hopen_d
        · have hempty : {t : I | graphEdgePath e' t ∈ W} = ∅ := by
            ext t
            constructor
            · intro htW
              have hi :
                  Sum.inr ⟨graphDiscreteEdge e', t⟩ ∈
                    graphEdgeInteriorPre e := by
                rw [← graphEdgeInterior_preimage]
                exact hW htW
              have hieq : e' = e := by
                have hi' : e' = e ∧ t ∈ Ioo (0 : I) 1 := by
                  simpa [graphEdgeInteriorPre] using hi
                exact hi'.1
              exact (he' hieq).elim
            · intro ht
              exact False.elim (by simp at ht)
          rw [hempty]
          exact isOpen_empty
    exact graphRealization_isOpen_iff.mpr hbase_pre

private theorem graphCoverRealizationProjection_edgeInterior_preimage_forward
    {V : Type u} [Quiver.{u} V]
    {root : V} (e : Quiver.Total V) {z : graphCoverRealization root}
    (hz : z ∈ graphCoverRealizationProjection root ⁻¹' graphEdgeInterior e) :
    z ∈ ⋃ d : graphCoverEdgeOver root e, graphEdgeInterior d.1 := by
  revert hz
  refine Quotient.inductionOn z ?_
  intro z hz
  change graphRealizationMap (graphCoverProjection root)
      (graphRealizationQuotient z) ∈ graphEdgeInterior e at hz
  rw [graphRealizationMap_quotient] at hz
  have hpre : graphRealizationPreMap (graphCoverProjection root) z ∈
      graphEdgeInteriorPre e := by
    rw [← graphEdgeInterior_preimage]
    exact hz
  cases z with
  | inl zv =>
      change False at hpre
      exact hpre.elim
  | inr z =>
      rcases z with ⟨ze, t⟩
      let d : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying ze
      have hpre' : graphCoverEdgeProjection root d = e ∧
          t ∈ Ioo (0 : I) 1 := by
        simpa only [graphRealizationPreMap, graphCoverProjection,
          graphEdgeInteriorPre, graphEdgeUnderlying, graphDiscreteEdge,
          graphCoverEdgeProjection, Sum.elim_inr, Set.mem_ofPred_eq,
          WithTopology.toTopology_inj, d] using hpre
      refine Set.mem_iUnion.mpr ⟨⟨d, hpre'.1⟩, ?_⟩
      refine ⟨Sum.inr ⟨graphDiscreteEdge d, t⟩, ?_, ?_⟩
      · change graphDiscreteEdge d = graphDiscreteEdge d ∧ t ∈ Ioo (0 : I) 1
        exact ⟨rfl, hpre'.2⟩
      · rfl

private theorem graphCoverRealizationProjection_edgeInterior_preimage_reverse
    {V : Type u} [Quiver.{u} V]
    {root : V} (e : Quiver.Total V) {z : graphCoverRealization root}
    (hz : z ∈ ⋃ d : graphCoverEdgeOver root e, graphEdgeInterior d.1) :
    z ∈ graphCoverRealizationProjection root ⁻¹' graphEdgeInterior e := by
  rcases Set.mem_iUnion.mp hz with ⟨d, hd⟩
  rcases hd with ⟨w, hw, hwz⟩
  have hpw :
      graphCoverRealizationProjection root
          (graphRealizationQuotient w) ∈ graphEdgeInterior e := by
    cases w with
    | inl wv =>
        simp [graphEdgeInteriorPre] at hw
    | inr w =>
        rcases w with ⟨we, t⟩
        change we = graphDiscreteEdge d.1 ∧ t ∈ Ioo (0 : I) 1 at hw
        rcases hw with ⟨rfl, ht⟩
        have hmap :
            graphCoverRealizationProjection root
                (graphEdgePath d.1 t) = graphEdgePath e t := by
          calc
            graphCoverRealizationProjection root (graphEdgePath d.1 t) =
                graphEdgePath (graphCoverEdgeProjection root d.1) t := by
              exact graphRealizationMap_edgePath (graphCoverProjection root) d.1 t
            _ = graphEdgePath e t := by rw [d.2]
        change graphCoverRealizationProjection root
            (graphEdgePath d.1 t) ∈ graphEdgeInterior e
        exact hmap.symm ▸ graphEdgePath_mem_graphEdgeInterior e ht.1 ht.2
  change graphCoverRealizationProjection root z ∈ graphEdgeInterior e
  exact (congrArg (graphCoverRealizationProjection root) hwz) ▸ hpw

theorem graphCoverRealizationProjection_edgeInterior_preimage
    {V : Type u} [Quiver.{u} V]
    {root : V} (e : Quiver.Total V) :
    graphCoverRealizationProjection root ⁻¹' graphEdgeInterior e =
      ⋃ d : graphCoverEdgeOver root e, graphEdgeInterior d.1 := by
  ext z
  exact ⟨graphCoverRealizationProjection_edgeInterior_preimage_forward e,
    graphCoverRealizationProjection_edgeInterior_preimage_reverse e⟩

/-! The local charts above assemble into an honest covering map.  Vertices use
the lifted stars, while the open interval cells use their lifted interiors. -/

theorem graphCoverRealizationProjection_isCovering
    {V : Type u} [Quiver.{u} V] [WeaklyConnected V]
    (root : V) :
    IsCoveringMap (graphCoverRealizationProjection root) := by
  have hvertex : ∀ v : V,
      IsEvenlyCovered (graphCoverRealizationProjection root)
        (graphVertex v) (graphCoverVertexOver root v) := by
    intro v
    have : Nonempty (graphCoverVertexOver root v) :=
      graphCoverVertexOver_nonempty root v
    have : Nonempty (graphCoverRealization root) := by
      rcases (inferInstance : Nonempty (graphCoverVertexOver root v)) with ⟨x⟩
      exact ⟨graphVertex x.1⟩
    let t := (graphVertexStar_isOpen (v := v)).trivializationDiscrete
      (fun x : graphCoverVertexOver root v => graphVertexStar x.1)
      (graphVertexStar v)
      (fun x {W} hW =>
        graphCoverRealizationProjection_vertexStar_open_iff x hW)
      (fun x => graphCoverRealizationProjection_vertexStar_injective x)
      (fun x => graphCoverRealizationProjection_vertexStar_surjective x)
      (by
        intro x y hxy
        have hxy' : x.1 ≠ y.1 := by
          intro h
          apply hxy
          exact Subtype.ext h
        exact graphVertexStar_disjoint hxy')
      (by
        rw [graphCoverRealizationProjection_vertexStar_preimage])
    exact IsEvenlyCovered.of_trivialization
      (t := t) (graphVertex_mem_graphVertexStar v)
  have hedge : ∀ (e : Quiver.Total V) {y : graphRealization V},
      y ∈ graphEdgeInterior e →
        IsEvenlyCovered (graphCoverRealizationProjection root) y
          (graphCoverEdgeOver root e) := by
    intro e y hy
    have : Nonempty (graphCoverEdgeOver root e) :=
      graphCoverEdgeOver_nonempty e
    have : Nonempty (graphCoverRealization root) := by
      rcases (inferInstance : Nonempty (graphCoverEdgeOver root e)) with ⟨d⟩
      exact ⟨graphEdgePath d.1 graphHalf⟩
    let t := (graphEdgeInterior_isOpen e).trivializationDiscrete
      (fun d : graphCoverEdgeOver root e => graphEdgeInterior d.1)
      (graphEdgeInterior e)
      (fun d {W} hW =>
        graphCoverRealizationProjection_edgeInterior_open_iff d hW)
      (fun d => graphCoverRealizationProjection_edgeInterior_injective d.1)
      (fun d => graphCoverRealizationProjection_edgeInterior_surjective d)
      (by
        intro d₁ d₂ hd
        have hval : d₁.1 ≠ d₂.1 := by
          intro h
          apply hd
          exact Subtype.ext h
        exact graphEdgeInterior_disjoint hval)
      (by
        rw [graphCoverRealizationProjection_edgeInterior_preimage])
    exact IsEvenlyCovered.of_trivialization (t := t) hy
  intro y
  refine Quotient.inductionOn y ?_
  intro z
  cases z with
  | inl v =>
      have hv : graphRealizationQuotient (Sum.inl v) =
          graphVertex (graphVertexUnderlying v) := by
        have hv' : v = graphDiscreteVertex (graphVertexUnderlying v) := by
          simp [graphDiscreteVertex, graphVertexUnderlying]
        calc
          graphRealizationQuotient (Sum.inl v) =
              graphRealizationQuotient (Sum.inl
                (graphDiscreteVertex (graphVertexUnderlying v))) := by rw [hv']
          _ = graphVertex (graphVertexUnderlying v) := rfl
      change IsEvenlyCovered (graphCoverRealizationProjection root)
        (graphRealizationQuotient (Sum.inl v))
        (graphCoverRealizationProjection root ⁻¹'
          {graphRealizationQuotient (Sum.inl v)})
      rw [hv]
      exact (hvertex (graphVertexUnderlying v)).to_isEvenlyCovered_preimage
  | inr z =>
      rcases z with ⟨ze, t⟩
      let e : Quiver.Total V := graphEdgeUnderlying ze
      have hze : ze = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      by_cases ht0 : t = 0
      · subst t
        have hp : graphRealizationQuotient (Sum.inr
            ⟨ze, (0 : I)⟩) = graphVertex e.left := by
          calc
            graphRealizationQuotient (Sum.inr ⟨ze, (0 : I)⟩) =
                graphRealizationQuotient (Sum.inr
                  ⟨graphDiscreteEdge e, (0 : I)⟩) := by rw [hze]
            _ = graphEdgePath e 0 := rfl
            _ = graphVertex e.left := graphEdgePath_zero e
        change IsEvenlyCovered (graphCoverRealizationProjection root)
          (graphRealizationQuotient (Sum.inr ⟨ze, (0 : I)⟩))
          (graphCoverRealizationProjection root ⁻¹'
            {graphRealizationQuotient (Sum.inr ⟨ze, (0 : I)⟩)})
        rw [hp]
        exact (hvertex e.left).to_isEvenlyCovered_preimage
      · by_cases ht1 : t = 1
        · subst t
          have hp : graphRealizationQuotient (Sum.inr
              ⟨ze, (1 : I)⟩) = graphVertex e.right := by
            calc
              graphRealizationQuotient (Sum.inr ⟨ze, (1 : I)⟩) =
                  graphRealizationQuotient (Sum.inr
                    ⟨graphDiscreteEdge e, (1 : I)⟩) := by rw [hze]
              _ = graphEdgePath e 1 := rfl
              _ = graphVertex e.right := graphEdgePath_one e
          change IsEvenlyCovered (graphCoverRealizationProjection root)
            (graphRealizationQuotient (Sum.inr ⟨ze, (1 : I)⟩))
            (graphCoverRealizationProjection root ⁻¹'
              {graphRealizationQuotient (Sum.inr ⟨ze, (1 : I)⟩)})
          rw [hp]
          exact (hvertex e.right).to_isEvenlyCovered_preimage
        · have ht0' : 0 < t := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
          have ht1' : t < 1 := lt_of_le_of_ne t.2.2 ht1
          have hy : graphRealizationQuotient (Sum.inr ⟨ze, t⟩) ∈
              graphEdgeInterior e := by
            rw [hze]
            exact graphEdgePath_mem_graphEdgeInterior e ht0' ht1'
          exact (hedge e hy).to_isEvenlyCovered_preimage

end FiniteGraphFreeGroup
