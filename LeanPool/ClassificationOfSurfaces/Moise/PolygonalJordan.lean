/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The Jordan curve theorem for polygons

Statements of the separation properties of polygonal simple closed curves in the plane, following
Moise, *Geometric Topology in Dimensions 2 and 3*, Ch. 2 ("Separation properties of polygons in
R²").  Only the **polygonal** case is stated: this is what the triangulation theorem consumes
(via the combinatorial Schoenflies theorem, Moise Thm. 5.3).  The full Jordan curve theorem
(Moise Ch. 4) is *not* on the triangulation route's critical path.

`PolygonalCircle` is the honest object: cyclically indexed vertices joined by genuine segments,
with adjacent segments meeting exactly at their shared vertex and non-adjacent segments disjoint.
A junk witness cannot satisfy these fields: they force the carrier to be a topological circle.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A polygonal simple closed curve in the plane: at least three vertices, cyclically indexed,
with consecutive vertices distinct, adjacent edges meeting exactly in their shared vertex, and
non-adjacent edges disjoint. -/
structure PolygonalCircle where
  /-- The number of vertices (and edges). -/
  n : ℕ
  /-- A polygon has at least three vertices. -/
  three_le : 3 ≤ n
  /-- The cyclically indexed vertices. -/
  vertex : ZMod n → Plane
  /-- Consecutive vertices are distinct, so every edge is a genuine segment. -/
  adjacent_ne : ∀ i, vertex i ≠ vertex (i + 1)
  /-- Adjacent edges meet exactly in their shared vertex. -/
  consecutive_inter : ∀ i,
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex (i + 1)) (vertex (i + 2)) =
      {vertex (i + 1)}
  /-- Non-adjacent edges are disjoint. -/
  nonadjacent_disjoint : ∀ i j, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
    segment ℝ (vertex i) (vertex (i + 1)) ∩ segment ℝ (vertex j) (vertex (j + 1)) = ∅

namespace PolygonalCircle

variable (J : PolygonalCircle)

instance : NeZero J.n :=
  ⟨by have := J.three_le; omega⟩

/-- The edge from vertex `i` to vertex `i + 1`. -/
def edgeSegment (i : ZMod J.n) : Set Plane :=
  segment ℝ (J.vertex i) (J.vertex (i + 1))

/-- Two edge indices are nonadjacent when the corresponding edges share no endpoint. -/
def NonAdjacentEdges (i j : ZMod J.n) : Prop :=
  i ≠ j ∧ i ≠ j + 1 ∧ j ≠ i + 1

/-- The carrier of the polygon: the union of its edges. -/
def carrier : Set Plane :=
  ⋃ i, J.edgeSegment i

theorem vertex_mem_carrier (i : ZMod J.n) : J.vertex i ∈ J.carrier :=
  Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

theorem carrier_nonempty : J.carrier.Nonempty :=
  ⟨J.vertex 0, J.vertex_mem_carrier 0⟩

theorem isCompact_edgeSegment (i : ZMod J.n) : IsCompact (J.edgeSegment i) := by
  rw [edgeSegment, ← convexHull_pair]
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp)

/-- The carrier of a polygon is compact. -/
theorem isCompact_carrier : IsCompact J.carrier :=
  isCompact_iUnion J.isCompact_edgeSegment

theorem isClosed_carrier : IsClosed J.carrier :=
  J.isCompact_carrier.isClosed

theorem isClosed_edgeSegment (i : ZMod J.n) : IsClosed (J.edgeSegment i) :=
  (J.isCompact_edgeSegment i).isClosed

/-- Transport a polygon through a function which is injective on its carrier and straight on
each edge.  No extension to an ambient homeomorphism is needed. -/
noncomputable def mapEmbedding (f : Plane → Plane)
    (hinj : Set.InjOn f J.carrier)
    (hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i = segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1)))) :
    PolygonalCircle where
  n := J.n
  three_le := J.three_le
  vertex i := f (J.vertex i)
  adjacent_ne i := by
    intro heq
    exact J.adjacent_ne i
      (hinj (J.vertex_mem_carrier i) (J.vertex_mem_carrier (i + 1)) heq)
  consecutive_inter i := by
    have hedgeNext : f '' J.edgeSegment (i + 1) =
        segment ℝ (f (J.vertex (i + 1))) (f (J.vertex (i + 2))) := by
      convert hedge (i + 1) using 1; ring
    have hsub (k : ZMod J.n) : J.edgeSegment k ⊆ J.carrier := fun x hx =>
      Set.mem_iUnion.mpr ⟨k, hx⟩
    rw [← hedge i, ← hedgeNext, ← hinj.image_inter (hsub i) (hsub (i + 1))]
    have hJ : J.edgeSegment i ∩ J.edgeSegment (i + 1) = {J.vertex (i + 1)} := by
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter i
    rw [hJ]
    simp
  nonadjacent_disjoint i j hij hprev hnext := by
    have hsub (k : ZMod J.n) : J.edgeSegment k ⊆ J.carrier := fun x hx =>
      Set.mem_iUnion.mpr ⟨k, hx⟩
    rw [← hedge i, ← hedge j, ← hinj.image_inter (hsub i) (hsub j)]
    have hdis : J.edgeSegment i ∩ J.edgeSegment j = ∅ :=
      J.nonadjacent_disjoint i j hij hprev hnext
    rw [hdis]
    simp

@[simp] theorem mapEmbedding_n (f : Plane → Plane) (hinj : Set.InjOn f J.carrier)
    (hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i = segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1)))) :
    (J.mapEmbedding f hinj hedge).n = J.n := rfl

@[simp] theorem mapEmbedding_vertex (f : Plane → Plane) (hinj : Set.InjOn f J.carrier)
    (hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i = segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1))))
    (i : ZMod J.n) :
    (J.mapEmbedding f hinj hedge).vertex i = f (J.vertex i) := rfl

theorem mapEmbedding_edgeSegment (f : Plane → Plane) (hinj : Set.InjOn f J.carrier)
    (hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i = segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1))))
    (i : ZMod J.n) :
    (J.mapEmbedding f hinj hedge).edgeSegment i = f '' J.edgeSegment i := by
  exact (hedge i).symm

theorem mapEmbedding_carrier (f : Plane → Plane) (hinj : Set.InjOn f J.carrier)
    (hedge : ∀ i : ZMod J.n,
      f '' J.edgeSegment i = segment ℝ (f (J.vertex i)) (f (J.vertex (i + 1)))) :
    (J.mapEmbedding f hinj hedge).carrier = f '' J.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    rw [J.mapEmbedding_edgeSegment f hinj hedge i] at hpi
    obtain ⟨q, hqi, rfl⟩ := hpi
    exact ⟨q, Set.mem_iUnion.mpr ⟨i, hqi⟩, rfl⟩
  · rintro p ⟨q, hq, rfl⟩
    obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [J.mapEmbedding_edgeSegment f hinj hedge i]
      exact ⟨q, hqi, rfl⟩⟩

/-- Transport a polygon through a homeomorphism which is straight on each polygon edge. -/
noncomputable def mapHomeomorph (h : Plane ≃ₜ Plane)
    (hedge : ∀ i : ZMod J.n,
      h '' J.edgeSegment i = segment ℝ (h (J.vertex i)) (h (J.vertex (i + 1)))) :
    PolygonalCircle where
  n := J.n
  three_le := J.three_le
  vertex i := h (J.vertex i)
  adjacent_ne i := h.injective.ne (J.adjacent_ne i)
  consecutive_inter i := by
    have hedgeNext : h '' J.edgeSegment (i + 1) =
        segment ℝ (h (J.vertex (i + 1))) (h (J.vertex (i + 2))) := by
      convert hedge (i + 1) using 1; ring
    rw [← hedge i, ← hedgeNext, ← Set.image_inter h.injective]
    have hJ : J.edgeSegment i ∩ J.edgeSegment (i + 1) = {J.vertex (i + 1)} := by
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter i
    rw [hJ]
    simp
  nonadjacent_disjoint i j hij hprev hnext := by
    rw [← hedge i, ← hedge j, ← Set.image_inter h.injective]
    have hdisjoint : J.edgeSegment i ∩ J.edgeSegment j = ∅ := by
      exact J.nonadjacent_disjoint i j hij hprev hnext
    rw [hdisjoint]
    simp

@[simp] theorem mapHomeomorph_n (h : Plane ≃ₜ Plane)
    (hedge : ∀ i : ZMod J.n,
      h '' J.edgeSegment i = segment ℝ (h (J.vertex i)) (h (J.vertex (i + 1)))) :
    (J.mapHomeomorph h hedge).n = J.n := rfl

@[simp] theorem mapHomeomorph_vertex (h : Plane ≃ₜ Plane)
    (hedge : ∀ i : ZMod J.n,
      h '' J.edgeSegment i = segment ℝ (h (J.vertex i)) (h (J.vertex (i + 1))))
    (i : ZMod J.n) :
    (J.mapHomeomorph h hedge).vertex i = h (J.vertex i) := rfl

theorem mapHomeomorph_edgeSegment (h : Plane ≃ₜ Plane)
    (hedge : ∀ i : ZMod J.n,
      h '' J.edgeSegment i = segment ℝ (h (J.vertex i)) (h (J.vertex (i + 1))))
    (i : ZMod J.n) :
    (J.mapHomeomorph h hedge).edgeSegment i = h '' J.edgeSegment i := by
  exact (hedge i).symm

theorem mapHomeomorph_carrier (h : Plane ≃ₜ Plane)
    (hedge : ∀ i : ZMod J.n,
      h '' J.edgeSegment i = segment ℝ (h (J.vertex i)) (h (J.vertex (i + 1)))) :
    (J.mapHomeomorph h hedge).carrier = h '' J.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    rw [J.mapHomeomorph_edgeSegment h hedge i] at hpi
    obtain ⟨q, hqi, rfl⟩ := hpi
    exact ⟨q, Set.mem_iUnion.mpr ⟨i, hqi⟩, rfl⟩
  · rintro p ⟨q, hq, rfl⟩
    obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨i, by
      rw [J.mapHomeomorph_edgeSegment h hedge i]
      exact ⟨q, hqi, rfl⟩⟩

theorem disjoint_edgeSegment_of_nonAdjacent {i j : ZMod J.n}
    (hij : J.NonAdjacentEdges i j) : Disjoint (J.edgeSegment i) (J.edgeSegment j) := by
  rw [Set.disjoint_iff_inter_eq_empty, edgeSegment, edgeSegment]
  exact J.nonadjacent_disjoint i j hij.1 hij.2.1 hij.2.2

private theorem exists_pos_three_mul_lt_of_finite {ι : Type*} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 3 * ε < r i := by
  classical
  let := Fintype.ofFinite ι
  set values : Finset ℝ := insert 1 (Finset.univ.image r) with hvalues
  have hvalues_ne : values.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  set rmin : ℝ := values.min' hvalues_ne with hrmin
  have hrmin_pos : 0 < rmin := by
    have hall : ∀ x ∈ values, 0 < x := by
      intro x hx
      simp only [hvalues, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
      rcases hx with rfl | ⟨i, rfl⟩
      · norm_num
      · exact hr i
    exact hall rmin (by rw [hrmin]; exact values.min'_mem hvalues_ne)
  refine ⟨rmin / 4, by positivity, fun i => ?_⟩
  have hmem : r i ∈ values := by
    rw [hvalues]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hle : rmin ≤ r i := by
    rw [hrmin]
    exact Finset.min'_le values _ hmem
  linarith

/-- There is a uniform positive lower bound on distances between nonadjacent polygon edges. -/
theorem exists_uniform_nonAdjacent_separation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j : ZMod J.n, J.NonAdjacentEdges i j →
      ∀ x ∈ J.edgeSegment i, ∀ y ∈ J.edgeSegment j, 3 * ε < dist x y := by
  classical
  let Pair := {p : ZMod J.n × ZMod J.n // J.NonAdjacentEdges p.1 p.2}
  have hsep : ∀ p : Pair, ∃ r : NNReal, 0 < r ∧
      ∀ x ∈ J.edgeSegment p.val.1, ∀ y ∈ J.edgeSegment p.val.2,
        (r : ENNReal) < edist x y := by
    intro p
    exact Metric.exists_pos_forall_lt_edist (J.isCompact_edgeSegment p.val.1)
      (J.isClosed_edgeSegment p.val.2) (J.disjoint_edgeSegment_of_nonAdjacent p.property)
  let radiusNN : Pair → NNReal := fun p =>
    (hsep p).choose
  have hradius_pos : ∀ p : Pair, 0 < radiusNN p := fun p =>
    (hsep p).choose_spec.1
  have hradius_dist : ∀ p : Pair, ∀ x ∈ J.edgeSegment p.val.1,
      ∀ y ∈ J.edgeSegment p.val.2,
      (radiusNN p : ℝ) < dist x y := by
    intro p x hx y hy
    have h := (hsep p).choose_spec.2 x hx y hy
    simpa [radiusNN, edist_dist] using h
  set radii : Finset ℝ := insert 1 (Finset.univ.image fun p : Pair => (radiusNN p : ℝ))
    with hradii
  have hradii_ne : radii.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  set rmin : ℝ := radii.min' hradii_ne with hrmin
  have hrmin_pos : 0 < rmin := by
    have hall : ∀ r ∈ radii, 0 < r := by
      intro r hr
      simp only [hradii, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hr
      rcases hr with rfl | ⟨p, rfl⟩
      · norm_num
      · exact_mod_cast hradius_pos p
    exact hall rmin (by rw [hrmin]; exact radii.min'_mem hradii_ne)
  refine ⟨rmin / 4, by positivity, ?_⟩
  intro i j hij x hx y hy
  let p : Pair := ⟨(i, j), hij⟩
  have hrmem : (radiusNN p : ℝ) ∈ radii := by
    rw [hradii]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)
  have hminle : rmin ≤ (radiusNN p : ℝ) := by
    rw [hrmin]
    exact Finset.min'_le radii _ hrmem
  exact lt_of_lt_of_le (by linarith) (hradius_dist p x hx y hy).le

/-- Nonadjacent edges have disjoint tubes of one uniform positive radius. -/
theorem exists_uniform_nonAdjacent_thickenings_disjoint :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j : ZMod J.n, J.NonAdjacentEdges i j →
      Disjoint (Metric.thickening ε (J.edgeSegment i))
        (Metric.thickening ε (J.edgeSegment j)) := by
  obtain ⟨ε, hε, hsep⟩ := J.exists_uniform_nonAdjacent_separation
  refine ⟨ε, hε, ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  obtain ⟨x, hxi, hzx⟩ := Metric.mem_thickening_iff.mp hzi
  obtain ⟨y, hyj, hzy⟩ := Metric.mem_thickening_iff.mp hzj
  have hxy := hsep i j hij x hxi y hyj
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  rw [dist_comm x z] at htri
  linarith

/-- A vertex lies on exactly its outgoing and incoming polygon edges. -/
theorem vertex_mem_edgeSegment_iff (i j : ZMod J.n) :
    J.vertex i ∈ J.edgeSegment j ↔ i = j ∨ i = j + 1 := by
  constructor
  · intro hmem
    by_cases hij : i = j
    · exact Or.inl hij
    by_cases hprev : i = j + 1
    · exact Or.inr hprev
    by_cases hnext : j = i + 1
    · have hinter : J.edgeSegment i ∩ J.edgeSegment (i + 1) = {J.vertex (i + 1)} := by
        simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter i
      have hi : J.vertex i ∈ J.edgeSegment i ∩ J.edgeSegment (i + 1) := by
        refine ⟨left_mem_segment ℝ _ _, ?_⟩
        simpa [hnext] using hmem
      rw [hinter] at hi
      exact (J.adjacent_ne i hi).elim
    · have hdisj := J.disjoint_edgeSegment_of_nonAdjacent
          (i := i) (j := j) ⟨hij, hprev, hnext⟩
      exact (Set.disjoint_left.1 hdisj (left_mem_segment ℝ _ _) hmem).elim
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

/-- The vertices of a simple polygon are pairwise distinct. -/
theorem vertex_injective : Function.Injective J.vertex := by
  intro i j hij
  have hmem : J.vertex i ∈ J.edgeSegment j := by
    rw [hij]
    exact left_mem_segment ℝ _ _
  rcases (J.vertex_mem_edgeSegment_iff i j).mp hmem with h | h
  · exact h
  · exfalso
    apply J.adjacent_ne j
    rw [← h]
    exact hij.symm

/-- There is a uniform positive lower bound between every vertex and every edge not incident to
that vertex. -/
theorem exists_uniform_nonincident_vertex_edge_separation :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, 3 * ε < dist (J.vertex i) y := by
  classical
  let Pair := {p : ZMod J.n × ZMod J.n // p.1 ≠ p.2 ∧ p.1 ≠ p.2 + 1}
  have hdisj : ∀ p : Pair,
      Disjoint ({J.vertex p.val.1} : Set Plane) (J.edgeSegment p.val.2) := by
    intro p
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Set.mem_singleton_iff] at hx
    subst x
    rcases (J.vertex_mem_edgeSegment_iff p.val.1 p.val.2).mp hy with h | h
    · exact p.property.1 h
    · exact p.property.2 h
  have hsep : ∀ p : Pair, ∃ r : NNReal, 0 < r ∧
      ∀ x ∈ ({J.vertex p.val.1} : Set Plane), ∀ y ∈ J.edgeSegment p.val.2,
        (r : ENNReal) < edist x y := fun p =>
    Metric.exists_pos_forall_lt_edist (isCompact_singleton)
      (J.isClosed_edgeSegment p.val.2) (hdisj p)
  let radiusNN : Pair → NNReal := fun p => (hsep p).choose
  have hradius_pos : ∀ p : Pair, 0 < (radiusNN p : ℝ) := by
    intro p
    exact_mod_cast (hsep p).choose_spec.1
  obtain ⟨ε, hε, hεradius⟩ :=
    exists_pos_three_mul_lt_of_finite (fun p : Pair => (radiusNN p : ℝ)) hradius_pos
  refine ⟨ε, hε, ?_⟩
  intro i j hij hprev y hy
  let p : Pair := ⟨(i, j), hij, hprev⟩
  have hdist := (hsep p).choose_spec.2 (J.vertex i) (Set.mem_singleton _) y hy
  have hdist' : (radiusNN p : ℝ) < dist (J.vertex i) y := by
    simpa [radiusNN, edist_dist] using hdist
  exact (hεradius p).trans hdist'

/-- Polygon edges have a uniform positive lower bound on their lengths. -/
theorem exists_uniform_edge_length :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : ZMod J.n, 3 * ε < dist (J.vertex i) (J.vertex (i + 1)) := by
  apply exists_pos_three_mul_lt_of_finite
  intro i
  exact dist_pos.mpr (J.adjacent_ne i)

/-- A single feature radius simultaneously controls edge lengths, nonadjacent-edge separation,
and vertex-to-nonincident-edge separation. -/
theorem exists_featureRadius :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i : ZMod J.n, 12 * ε < dist (J.vertex i) (J.vertex (i + 1))) ∧
      (∀ i j : ZMod J.n, J.NonAdjacentEdges i j →
        ∀ x ∈ J.edgeSegment i, ∀ y ∈ J.edgeSegment j, 12 * ε < dist x y) ∧
      (∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
        ∀ y ∈ J.edgeSegment j, 12 * ε < dist (J.vertex i) y) := by
  obtain ⟨a, ha, haLen⟩ := J.exists_uniform_edge_length
  obtain ⟨b, hb, hbEdge⟩ := J.exists_uniform_nonAdjacent_separation
  obtain ⟨c, hc, hcVertex⟩ := J.exists_uniform_nonincident_vertex_edge_separation
  set ε : ℝ := min a (min b c) / 4 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  refine ⟨ε, hεpos, ?_, ?_, ?_⟩
  · intro i
    have hmin : min a (min b c) ≤ a := min_le_left _ _
    have := haLen i
    rw [hε]
    linarith
  · intro i j hij x hx y hy
    have hmin : min a (min b c) ≤ b :=
      (min_le_right a (min b c)).trans (min_le_left b c)
    have := hbEdge i j hij x hx y hy
    rw [hε]
    linarith
  · intro i j hij hprev y hy
    have hmin : min a (min b c) ≤ c :=
      (min_le_right a (min b c)).trans (min_le_right b c)
    have := hcVertex i j hij hprev y hy
    rw [hε]
    linarith

/-- Inside the vertex-to-nonincident-edge separation radius, every point of the carrier lies on
one of the two edges incident to the vertex. -/
theorem mem_incident_edge_of_mem_carrier_of_dist_lt {r : ℝ}
    (hsep : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex i) y)
    {i : ZMod J.n} {x : Plane} (hx : x ∈ J.carrier)
    (hdist : dist (J.vertex i) x < r) :
    x ∈ J.edgeSegment i ∪ J.edgeSegment (i - 1) := by
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  rcases eq_or_ne i j with rfl | hij
  · exact Or.inl hxj
  rcases eq_or_ne i (j + 1) with hprev | hprev
  · right
    have hindex : i - 1 = j := by
      rw [hprev]
      abel
    simpa [hindex] using hxj
  · exact (not_lt_of_ge (hsep i j hij hprev x hxj).le hdist).elim

/-- A ball inside the feature radius sees exactly the two polygon edges incident to its center
vertex.  This is the local isolation input for the vertex sectors of Moise's strip. -/
theorem ball_inter_carrier_eq_incident_edges {r : ℝ}
    (hsep : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex i) y)
    (i : ZMod J.n) :
    Metric.ball (J.vertex i) r ∩ J.carrier =
      Metric.ball (J.vertex i) r ∩ (J.edgeSegment i ∪ J.edgeSegment (i - 1)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxball, hxcarrier⟩
    refine ⟨hxball, J.mem_incident_edge_of_mem_carrier_of_dist_lt hsep hxcarrier ?_⟩
    simpa only [Metric.mem_ball, dist_comm] using hxball
  · rintro x ⟨hxball, hxedge | hxedge⟩
    · exact ⟨hxball, Set.mem_iUnion.mpr ⟨i, hxedge⟩⟩
    · exact ⟨hxball, Set.mem_iUnion.mpr ⟨i - 1, hxedge⟩⟩

/-! #### The local angular model at a polygon vertex -/

/-- The open radial sector of radius `r` swept counterclockwise from direction `a` to direction
`b`.  It is parametrized by an open rectangle, avoiding the center and both boundary rays. -/
noncomputable def openAngularSector (a b : Circle) (r : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ =>
    (p.1 : ℂ) * (Circle.exp (a.val.arg + p.2 * a.angleDiff b) : ℂ)) ''
      (Set.Ioo 0 r ×ˢ Set.Ioo 0 1)

/-- An open angular sector of positive radius and nonzero angle is path connected. -/
theorem isPathConnected_openAngularSector (a b : Circle) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (openAngularSector a b r) := by
  have hdomain : IsPathConnected (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (0 : ℝ) 1) := by
    apply ((convex_Ioo (0 : ℝ) r).prod (convex_Ioo (0 : ℝ) 1)).isPathConnected
    exact ⟨(r / 2, 1 / 2), by constructor <;> constructor <;> linarith⟩
  apply hdomain.image
  fun_prop

/-- The radial norm in the sector is exactly its radial parameter. -/
theorem norm_openAngularSector_param (a b : Circle) {r : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Set.Ioo 0 r ×ˢ Set.Ioo 0 1) :
    ‖(p.1 : ℂ) * (Circle.exp (a.val.arg + p.2 * a.angleDiff b) : ℂ)‖ = p.1 := by
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp.1.1]

/-- Every point in an open angular sector lies in the punctured open disk of the stated radius. -/
theorem openAngularSector_subset_puncturedBall (a b : Circle) {r : ℝ} :
    openAngularSector a b r ⊆ Metric.ball (0 : ℂ) r \ {0} := by
  rintro z ⟨p, hp, rfl⟩
  have hnorm := norm_openAngularSector_param a b hp
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact hp.1.2
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    have hzero : ‖((p.1 : ℂ) *
        (Circle.exp (a.val.arg + p.2 * a.angleDiff b) : ℂ))‖ = 0 := by
      simpa only [norm_zero] using congrArg norm hz
    rw [hnorm] at hzero
    linarith [hp.1.1]

/-- The closed parameter rectangle maps into the closure of the open angular sector. -/
theorem angularSector_param_mem_closure (a b : Circle) {r : ℝ} (hr : 0 < r)
    {p : ℝ × ℝ} (hp : p ∈ Set.Icc 0 r ×ˢ Set.Icc 0 1) :
    (p.1 : ℂ) * (Circle.exp (a.val.arg + p.2 * a.angleDiff b) : ℂ) ∈
      closure (openAngularSector a b r) := by
  let f : ℝ × ℝ → ℂ := fun q =>
    (q.1 : ℂ) * (Circle.exp (a.val.arg + q.2 * a.angleDiff b) : ℂ)
  have hf : Continuous f := by unfold f; fun_prop
  have hpclosure : p ∈ closure (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (0 : ℝ) 1) := by
    rw [closure_prod_eq, closure_Ioo (a := (0 : ℝ)) (b := r) hr.ne,
      closure_Ioo (a := (0 : ℝ)) (b := 1) zero_ne_one]
    exact hp
  exact image_closure_subset_closure_image hf ⟨p, hpclosure, rfl⟩

/-- The initial radial boundary ray belongs to the closure of an angular sector. -/
theorem sourceRadialRay_mem_closure_openAngularSector (a b : Circle) {r radius : ℝ}
    (hr : 0 < r) (hradius : radius ∈ Set.Icc 0 r) :
    (radius : ℂ) * (a : ℂ) ∈ closure (openAngularSector a b r) := by
  have h := angularSector_param_mem_closure a b hr
    (p := (radius, 0)) ⟨hradius, le_rfl, zero_le_one⟩
  simpa only [Prod.fst, Prod.snd, zero_mul, add_zero, Circle.exp_arg] using h

/-- The terminal radial boundary ray belongs to the closure of an angular sector. -/
theorem targetRadialRay_mem_closure_openAngularSector (a b : Circle) {r radius : ℝ}
    (hr : 0 < r) (hradius : radius ∈ Set.Icc 0 r) :
    (radius : ℂ) * (b : ℂ) ∈ closure (openAngularSector a b r) := by
  have h := angularSector_param_mem_closure a b hr
    (p := (radius, 1)) ⟨hradius, zero_le_one, le_rfl⟩
  have hab : Circle.exp (a.val.arg + 1 * a.angleDiff b) = b := by
    rw [one_mul, Circle.exp_add, Circle.exp_arg, mul_comm, Circle.exp_angleDiff_mul]
  simpa only [Prod.fst, Prod.snd, hab] using h

/-- The unit direction of a nonzero complex vector. -/
noncomputable def complexDirection (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by
    apply mem_sphere_zero_iff_norm.2
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.mpr hz), div_self (norm_ne_zero_iff.mpr hz)]⟩

@[simp] theorem coe_complexDirection (z : ℂ) (hz : z ≠ 0) :
    (complexDirection z hz : ℂ) = z / ‖z‖ := rfl

/-- Polar reconstruction from norm and unit direction. -/
theorem norm_mul_complexDirection (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ : ℂ) * (complexDirection z hz : ℂ) = z := by
  rw [coe_complexDirection]
  field_simp [norm_ne_zero_iff.mpr hz]

/-- The open radial ray in direction `a`, truncated at radius `r`. -/
def openRadialRay (a : Circle) (r : ℝ) : Set ℂ :=
  (fun ρ : ℝ => (ρ : ℂ) * (a : ℂ)) '' Set.Ioo 0 r

theorem mem_openAngularSector_of_direction_eq_path {a b : Circle} {r : ℝ} {z : ℂ}
    (hz : z ≠ 0) (hzr : ‖z‖ < r) {t : unitInterval} (ht0 : 0 < t) (ht1 : t < 1)
    (hdir : complexDirection z hz = Circle.path a b t) :
    z ∈ openAngularSector a b r := by
  refine ⟨(‖z‖, (t : ℝ)), ?_, ?_⟩
  · refine ⟨⟨norm_pos_iff.mpr hz, hzr⟩, ?_⟩
    constructor
    · exact_mod_cast ht0
    · exact_mod_cast ht1
  have hpath : Circle.exp (a.val.arg + (t : ℝ) * a.angleDiff b) = Circle.path a b t := by
    rw [Circle.path_apply]
    congr 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul]
    ring
  change (‖z‖ : ℂ) * (Circle.exp (a.val.arg + (t : ℝ) * a.angleDiff b) : ℂ) = z
  rw [congrArg (fun q : Circle => (q : ℂ)) hpath,
    ← congrArg (fun q : Circle => (q : ℂ)) hdir]
  exact norm_mul_complexDirection z hz

theorem mem_openRadialRay_of_direction_eq {a : Circle} {r : ℝ} {z : ℂ}
    (hz : z ≠ 0) (hzr : ‖z‖ < r) (hdir : complexDirection z hz = a) :
    z ∈ openRadialRay a r := by
  refine ⟨‖z‖, ⟨norm_pos_iff.mpr hz, hzr⟩, ?_⟩
  calc
    (‖z‖ : ℂ) * (a : ℂ) =
        (‖z‖ : ℂ) * (complexDirection z hz : ℂ) := by rw [hdir]
    _ = z := norm_mul_complexDirection z hz

/-- The two angular sectors and their two boundary rays partition the punctured disk. -/
theorem puncturedBall_subset_twoSectors_union_rays {a b : Circle} (hab : a ≠ b) {r : ℝ} :
    Metric.ball (0 : ℂ) r \ {0} ⊆
      openAngularSector a b r ∪ openAngularSector b a r ∪
        openRadialRay a r ∪ openRadialRay b r := by
  rintro z ⟨hzball, hz0⟩
  rw [Set.mem_singleton_iff] at hz0
  have hzr : ‖z‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hzball
  let d : Circle := complexDirection z hz0
  have hd : d ∈ Set.range (Circle.path a b) ∪ Set.range (Circle.path b a) := by
    rw [Circle.range_path_union_range_path hab]
    trivial
  rcases hd with ⟨t, ht⟩ | ⟨t, ht⟩
  · by_cases ht0 : t = 0
    · apply Or.inl; apply Or.inr
      apply mem_openRadialRay_of_direction_eq hz0 hzr
      dsimp [d] at ht
      rw [ht0, (Circle.path a b).source] at ht
      exact ht.symm
    by_cases ht1 : t = 1
    · apply Or.inr
      apply mem_openRadialRay_of_direction_eq hz0 hzr
      dsimp [d] at ht
      rw [ht1, (Circle.path a b).target] at ht
      exact ht.symm
    · apply Or.inl; apply Or.inl; apply Or.inl
      apply mem_openAngularSector_of_direction_eq_path hz0 hzr
      · exact lt_of_le_of_ne t.property.1 (Ne.symm ht0)
      · exact lt_of_le_of_ne t.property.2 ht1
      · exact ht.symm
  · by_cases ht0 : t = 0
    · apply Or.inr
      apply mem_openRadialRay_of_direction_eq hz0 hzr
      dsimp [d] at ht
      rw [ht0, (Circle.path b a).source] at ht
      exact ht.symm
    by_cases ht1 : t = 1
    · apply Or.inl; apply Or.inr
      apply mem_openRadialRay_of_direction_eq hz0 hzr
      dsimp [d] at ht
      rw [ht1, (Circle.path b a).target] at ht
      exact ht.symm
    · apply Or.inl; apply Or.inl; apply Or.inr
      apply mem_openAngularSector_of_direction_eq_path hz0 hzr
      · exact lt_of_le_of_ne t.property.1 (Ne.symm ht0)
      · exact lt_of_le_of_ne t.property.2 ht1
      · exact ht.symm

/-- The standard linear isometry from the project's Euclidean plane to the complex plane. -/
noncomputable def planeComplexEquiv : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

theorem norm_planeComplexEquiv (x : Plane) : ‖planeComplexEquiv x‖ = ‖x‖ :=
  planeComplexEquiv.norm_map x

/-- Equality of complex unit directions reflects equality of normalized plane vectors. -/
theorem normalized_eq_of_complexDirection_eq {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdir : complexDirection (planeComplexEquiv u)
        (by simpa using planeComplexEquiv.injective.ne hu) =
      complexDirection (planeComplexEquiv v)
        (by simpa using planeComplexEquiv.injective.ne hv)) :
    ‖u‖⁻¹ • u = ‖v‖⁻¹ • v := by
  apply (planeComplexEquiv : Plane ≃ₗᵢ[ℝ] ℂ).injective
  have hcoe := congrArg (fun q : Circle => (q : ℂ)) hdir
  simpa [coe_complexDirection, map_smul, norm_planeComplexEquiv, div_eq_inv_mul,
    Complex.real_smul] using hcoe

/-- Two nonzero vectors with the same normalized direction have a common nonzero initial point
on their segments from the origin. -/
theorem exists_nonzero_mem_segments_of_normalized_eq {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0)
    (hdir : ‖u‖⁻¹ • u = ‖v‖⁻¹ • v) :
    ∃ q : Plane, q ≠ 0 ∧ q ∈ segment ℝ 0 u ∧ q ∈ segment ℝ 0 v := by
  set ρ : ℝ := min ‖u‖ ‖v‖ / 2 with hρ
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvNorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρu : ρ / ‖u‖ ≤ 1 := by
    rw [div_le_one huNorm]
    rw [hρ]
    linarith [min_le_left ‖u‖ ‖v‖]
  have hρv : ρ / ‖v‖ ≤ 1 := by
    rw [div_le_one hvNorm]
    rw [hρ]
    linarith [min_le_right ‖u‖ ‖v‖]
  set q : Plane := ρ • (‖u‖⁻¹ • u) with hq
  have hqne : q ≠ 0 := by
    rw [hq, smul_smul]
    exact smul_ne_zero (mul_ne_zero hρpos.ne' (inv_ne_zero huNorm.ne')) hu
  refine ⟨q, hqne, ?_, ?_⟩
  · rw [segment_eq_image]
    refine ⟨ρ / ‖u‖, ⟨div_nonneg hρpos.le huNorm.le, hρu⟩, ?_⟩
    simp only [smul_zero, zero_add]
    rw [hq, smul_smul]
    congr 1
  · rw [segment_eq_image]
    refine ⟨ρ / ‖v‖, ⟨div_nonneg hρpos.le hvNorm.le, hρv⟩, ?_⟩
    simp only [smul_zero, zero_add]
    rw [hq, hdir, smul_smul]
    congr 1

/-- Translating a segment based at the origin gives the corresponding segment based at `p`. -/
theorem add_mem_segment_of_mem_segment_zero {p u q : Plane} (hq : q ∈ segment ℝ 0 u) :
    p + q ∈ segment ℝ p (p + u) := by
  rcases hq with ⟨a, b, ha, hb, hab, hq⟩
  refine ⟨a, b, ha, hb, hab, ?_⟩
  have hq' : b • u = q := by simpa using hq
  rw [← hq']
  rw [smul_add, ← add_assoc, ← add_smul, hab, one_smul]

/-- The ray from vertex `i` toward the next vertex. -/
def outgoingVector (i : ZMod J.n) : Plane :=
  J.vertex (i + 1) - J.vertex i

/-- The ray from vertex `i` toward the preceding vertex. -/
def incomingRayVector (i : ZMod J.n) : Plane :=
  J.vertex (i - 1) - J.vertex i

theorem outgoingVector_ne_zero (i : ZMod J.n) : J.outgoingVector i ≠ 0 := by
  rw [outgoingVector, sub_ne_zero]
  exact (J.adjacent_ne i).symm

theorem incomingRayVector_ne_zero (i : ZMod J.n) : J.incomingRayVector i ≠ 0 := by
  rw [incomingRayVector, sub_ne_zero]
  have h := J.adjacent_ne (i - 1)
  simpa only [sub_add_cancel] using h

/-- The two unit directions cut out by the incident edges at a polygon vertex are distinct. -/
theorem incident_complexDirections_ne (i : ZMod J.n) :
    complexDirection (planeComplexEquiv (J.outgoingVector i))
        (by simpa using planeComplexEquiv.injective.ne (J.outgoingVector_ne_zero i)) ≠
      complexDirection (planeComplexEquiv (J.incomingRayVector i))
        (by simpa using planeComplexEquiv.injective.ne (J.incomingRayVector_ne_zero i)) := by
  intro hdir
  have hnormalized := normalized_eq_of_complexDirection_eq
    (J.outgoingVector_ne_zero i) (J.incomingRayVector_ne_zero i) hdir
  obtain ⟨q, hqne, hqout, hqin⟩ := exists_nonzero_mem_segments_of_normalized_eq
    (J.outgoingVector_ne_zero i) (J.incomingRayVector_ne_zero i) hnormalized
  set x : Plane := J.vertex i + q with hx
  have hxout : x ∈ J.edgeSegment i := by
    have := add_mem_segment_of_mem_segment_zero (p := J.vertex i) hqout
    rw [hx, edgeSegment]
    convert this using 1; simp only [outgoingVector]; abel
  have hxin : x ∈ J.edgeSegment (i - 1) := by
    have := add_mem_segment_of_mem_segment_zero (p := J.vertex i) hqin
    rw [edgeSegment, segment_symm]
    rw [hx]
    convert this using 1; simp only [incomingRayVector, sub_add_cancel]; abel
  have hinter : J.edgeSegment (i - 1) ∩ J.edgeSegment i = {J.vertex i} := by
    convert J.consecutive_inter (i - 1) using 1 <;>
      simp only [edgeSegment, sub_add_cancel]; ring
  have hxvertex : x = J.vertex i := by
    have hxinter : x ∈ J.edgeSegment (i - 1) ∩ J.edgeSegment i := ⟨hxin, hxout⟩
    rw [hinter] at hxinter
    exact hxinter
  apply hqne
  apply add_left_cancel (a := J.vertex i)
  simpa only [add_zero] using hx.symm.trans hxvertex

@[simp] theorem complexDirection_pos_mul_circle (ρ : ℝ) (hρ : 0 < ρ) (a : Circle) :
    complexDirection ((ρ : ℂ) * (a : ℂ))
        (mul_ne_zero (by exact_mod_cast hρ.ne') a.coe_ne_zero) = a := by
  apply Circle.ext
  rw [coe_complexDirection, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ]
  field_simp [hρ.ne']

/-- An interior point of an angular sector does not have either boundary direction. -/
theorem direction_ne_boundary_of_mem_openAngularSector {a b : Circle} (hab : a ≠ b) {r : ℝ}
    {z : ℂ} (hz : z ∈ openAngularSector a b r) :
    complexDirection z
        ((openAngularSector_subset_puncturedBall a b hz).2 ∘ Set.mem_singleton_iff.mpr) ≠ a ∧
      complexDirection z
        ((openAngularSector_subset_puncturedBall a b hz).2 ∘ Set.mem_singleton_iff.mpr) ≠ b := by
  rcases hz with ⟨p, hp, rfl⟩
  let t : unitInterval := ⟨p.2, hp.2.1.le, hp.2.2.le⟩
  have ht0 : t ≠ 0 := by
    intro ht
    have := congrArg Subtype.val ht
    change p.2 = 0 at this
    linarith [hp.2.1]
  have ht1 : t ≠ 1 := by
    intro ht
    have := congrArg Subtype.val ht
    change p.2 = 1 at this
    linarith [hp.2.2]
  have hpath : Circle.exp (a.val.arg + p.2 * a.angleDiff b) = Circle.path a b t := by
    rw [Circle.path_apply]
    congr 1
    simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, t]
    ring
  have hdir : complexDirection
      ((p.1 : ℂ) * (Circle.exp (a.val.arg + p.2 * a.angleDiff b) : ℂ))
      (mul_ne_zero (by exact_mod_cast hp.1.1.ne') (Circle.exp _).coe_ne_zero) =
      Circle.path a b t := by
    rw [complexDirection_pos_mul_circle p.1 hp.1.1, hpath]
  constructor
  · intro ha
    rw [hdir] at ha
    have := (Circle.path_injective_of_ne hab) (ha.trans (Circle.path a b).source.symm)
    exact ht0 this
  · intro hb
    rw [hdir] at hb
    have := (Circle.path_injective_of_ne hab) (hb.trans (Circle.path a b).target.symm)
    exact ht1 this

/-- A small positive rotation from the initial boundary direction lies in the angular sector. -/
theorem pos_rotation_mem_openAngularSector {a b : Circle} {radius bound θ : ℝ}
    (hθ : 0 < θ) (hδ : θ < a.angleDiff b) (hradius : 0 < radius)
    (hrbound : radius < bound) :
    (radius : ℂ) * ((Circle.exp θ : Circle) : ℂ) * (a : ℂ) ∈
      openAngularSector a b bound := by
  set t : ℝ := θ / a.angleDiff b with ht
  have hδpos : 0 < a.angleDiff b := lt_of_lt_of_le hθ hδ.le
  have ht0 : 0 < t := div_pos hθ hδpos
  have ht1 : t < 1 := (div_lt_one hδpos).mpr hδ
  refine ⟨(radius, t), ⟨⟨hradius, hrbound⟩, ⟨ht0, ht1⟩⟩, ?_⟩
  change (radius : ℂ) * (Circle.exp (a.val.arg + t * a.angleDiff b) : ℂ) =
    (radius : ℂ) * (Circle.exp θ : ℂ) * (a : ℂ)
  have hangle : a.val.arg + t * a.angleDiff b = θ + a.val.arg := by
    rw [ht]
    field_simp [hδpos.ne']
    ring
  have hcircle : Circle.exp (a.val.arg + t * a.angleDiff b) = Circle.exp θ * a := by
    rw [hangle, Circle.exp_add, Circle.exp_arg]
  rw [congrArg (fun q : Circle => (q : ℂ)) hcircle, Circle.coe_mul]
  ring

/-- A small negative rotation from the terminal boundary direction lies in the angular sector. -/
theorem neg_rotation_mem_openAngularSector {a b : Circle} {radius bound θ : ℝ}
    (hθ : 0 < θ) (hδ : θ < a.angleDiff b) (hradius : 0 < radius)
    (hrbound : radius < bound) :
    (radius : ℂ) * ((Circle.exp (-θ) : Circle) : ℂ) * (b : ℂ) ∈
      openAngularSector a b bound := by
  set t : ℝ := 1 - θ / a.angleDiff b with ht
  have hab : a ≠ b := by
    intro heq
    subst b
    have : θ < 0 := by simpa [Circle.angleDiff] using hδ
    linarith
  have hδab : 0 < a.angleDiff b := Circle.angleDiff_pos hab
  have ht0 : 0 < t := by rw [ht]; exact sub_pos.mpr ((div_lt_one hδab).mpr hδ)
  have ht1 : t < 1 := by rw [ht]; exact sub_lt_self _ (div_pos hθ hδab)
  refine ⟨(radius, t), ⟨⟨hradius, hrbound⟩, ⟨ht0, ht1⟩⟩, ?_⟩
  change (radius : ℂ) * (Circle.exp (a.val.arg + t * a.angleDiff b) : ℂ) =
    (radius : ℂ) * (Circle.exp (-θ) : ℂ) * (b : ℂ)
  have hangle : a.val.arg + t * a.angleDiff b =
      -θ + (a.angleDiff b + a.val.arg) := by
    rw [ht]
    field_simp [hδab.ne']
    ring
  have hcircle : Circle.exp (a.val.arg + t * a.angleDiff b) = Circle.exp (-θ) * b := by
    rw [hangle, Circle.exp_add, Circle.exp_add, Circle.exp_arg,
      Circle.exp_angleDiff_mul]
  rw [congrArg (fun q : Circle => (q : ℂ)) hcircle, Circle.coe_mul]
  ring

theorem ofReal_mul_circle_exp_re (radius θ : ℝ) :
    ((radius : ℂ) * (Circle.exp θ : ℂ)).re = radius * Real.cos θ := by
  simp only [Circle.coe_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

theorem ofReal_mul_circle_exp_im (radius θ : ℝ) :
    ((radius : ℂ) * (Circle.exp θ : ℂ)).im = radius * Real.sin θ := by
  simp only [Circle.coe_exp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

/-- A noninitial point of a segment has the direction of the segment. -/
theorem complexDirection_sub_eq_of_mem_segment {p q x : Plane} (hpq : p ≠ q)
    (hx : x ∈ segment ℝ p q) (hxp : x ≠ p) :
    complexDirection (planeComplexEquiv (x - p))
        (by
          intro h
          apply hxp
          rw [← sub_eq_zero]
          apply planeComplexEquiv.injective
          simpa using h) =
      complexDirection (planeComplexEquiv (q - p))
        (by
          intro h
          apply hpq.symm
          rw [← sub_eq_zero]
          apply planeComplexEquiv.injective
          simpa using h) := by
  rcases hx with ⟨a, b, ha, hb, hab, hx⟩
  have hbpos : 0 < b := by
    have hbne : b ≠ 0 := by
      intro hb0
      have ha1 : a = 1 := by linarith
      apply hxp
      rw [← hx, hb0, ha1, one_smul, zero_smul, add_zero]
    exact lt_of_le_of_ne hb hbne.symm
  have hsub : x - p = b • (q - p) := by
    rw [← hx]
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    module
  have hmap : planeComplexEquiv (x - p) =
      (b : ℂ) * planeComplexEquiv (q - p) := by
    rw [hsub, map_smul, Complex.real_smul]
  apply Circle.ext
  rw [coe_complexDirection, coe_complexDirection, hmap, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hbpos]
  field_simp [hbpos.ne', norm_ne_zero_iff.mpr (by
    intro hzero
    apply hpq.symm
    rw [← sub_eq_zero]
    exact planeComplexEquiv.injective (by simpa using hzero))]
  rw [Complex.ofReal_mul]
  ring

/-- The outgoing complex direction at a polygon vertex. -/
noncomputable def outgoingDirection (i : ZMod J.n) : Circle :=
  complexDirection (planeComplexEquiv (J.outgoingVector i))
    (by simpa using planeComplexEquiv.injective.ne (J.outgoingVector_ne_zero i))

/-- The complex direction from a polygon vertex toward its predecessor. -/
noncomputable def incomingRayDirection (i : ZMod J.n) : Circle :=
  complexDirection (planeComplexEquiv (J.incomingRayVector i))
    (by simpa using planeComplexEquiv.injective.ne (J.incomingRayVector_ne_zero i))

theorem outgoingDirection_ne_incomingRayDirection (i : ZMod J.n) :
    J.outgoingDirection i ≠ J.incomingRayDirection i :=
  J.incident_complexDirections_ne i

/-- At the terminal endpoint of an edge, its incoming ray points opposite to its oriented
outgoing direction. -/
theorem coe_incomingRayDirection_add_one (i : ZMod J.n) :
    (J.incomingRayDirection (i + 1) : ℂ) = -(J.outgoingDirection i : ℂ) := by
  rw [incomingRayDirection, outgoingDirection, coe_complexDirection,
    coe_complexDirection]
  have hv : J.incomingRayVector (i + 1) = -J.outgoingVector i := by
    simp only [incomingRayVector, outgoingVector, add_sub_cancel_right]
    abel
  rw [hv, map_neg, norm_neg]
  ring

/-- One of the two open sectors in the vertex ball, transported back from the complex plane. -/
noncomputable def vertexForwardSector (i : ZMod J.n) (r : ℝ) : Set Plane :=
  (fun z : ℂ => J.vertex i + planeComplexEquiv.symm z) ''
    openAngularSector (J.outgoingDirection i) (J.incomingRayDirection i) r

/-- The other open sector in the vertex ball. -/
noncomputable def vertexBackwardSector (i : ZMod J.n) (r : ℝ) : Set Plane :=
  (fun z : ℂ => J.vertex i + planeComplexEquiv.symm z) ''
    openAngularSector (J.incomingRayDirection i) (J.outgoingDirection i) r

theorem isPathConnected_vertexForwardSector (i : ZMod J.n) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (J.vertexForwardSector i r) := by
  apply (isPathConnected_openAngularSector _ _ hr).image
  fun_prop

theorem isPathConnected_vertexBackwardSector (i : ZMod J.n) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (J.vertexBackwardSector i r) := by
  apply (isPathConnected_openAngularSector _ _ hr).image
  fun_prop

/-- The outgoing edge ray is in the closure of each local side sector. -/
theorem outgoingRay_mem_closure_vertexSectors (i : ZMod J.n) {r radius : ℝ}
    (hr : 0 < r) (hradius : radius ∈ Set.Icc 0 r) :
    J.vertex i + planeComplexEquiv.symm
        ((radius : ℂ) * (J.outgoingDirection i : ℂ)) ∈
          closure (J.vertexForwardSector i r) ∩ closure (J.vertexBackwardSector i r) := by
  constructor
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, sourceRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, targetRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩

/-- The incoming edge ray is in the closure of each local side sector. -/
theorem incomingRay_mem_closure_vertexSectors (i : ZMod J.n) {r radius : ℝ}
    (hr : 0 < r) (hradius : radius ∈ Set.Icc 0 r) :
    J.vertex i + planeComplexEquiv.symm
        ((radius : ℂ) * (J.incomingRayDirection i : ℂ)) ∈
          closure (J.vertexForwardSector i r) ∩ closure (J.vertexBackwardSector i r) := by
  constructor
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, targetRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩
  · apply image_closure_subset_closure_image (by fun_prop)
    exact ⟨_, sourceRadialRay_mem_closure_openAngularSector _ _ hr hradius, rfl⟩

/-- Either transported angular sector lies in its vertex ball and avoids the polygon, provided
the ball sees only the two incident edges. -/
theorem vertexForwardSector_subset_ball_diff_carrier {r : ℝ}
    (hsep : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex i) y)
    (i : ZMod J.n) :
    J.vertexForwardSector i r ⊆ Metric.ball (J.vertex i) r \ J.carrier := by
  rintro x ⟨z, hzsector, rfl⟩
  have hzpunctured := openAngularSector_subset_puncturedBall
    (J.outgoingDirection i) (J.incomingRayDirection i) hzsector
  have hz0 : z ≠ 0 := by
    intro hz
    apply hzpunctured.2
    simp [hz]
  have hball : J.vertex i + planeComplexEquiv.symm z ∈ Metric.ball (J.vertex i) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hzpunctured.1
  refine ⟨hball, ?_⟩
  intro hcarrier
  have hincident := J.mem_incident_edge_of_mem_carrier_of_dist_lt hsep hcarrier
    (by simpa only [Metric.mem_ball, dist_comm] using hball)
  have hneVertex : J.vertex i + planeComplexEquiv.symm z ≠ J.vertex i := by
    intro heq
    apply hz0
    have hzero : planeComplexEquiv.symm z = 0 := by
      apply add_left_cancel (a := J.vertex i)
      simpa using heq
    apply planeComplexEquiv.symm.injective
    simpa using hzero
  have hboundary := direction_ne_boundary_of_mem_openAngularSector
    (J.outgoingDirection_ne_incomingRayDirection i) hzsector
  rcases hincident with hout | hin
  · apply hboundary.1
    have hdir := complexDirection_sub_eq_of_mem_segment (J.adjacent_ne i) hout hneVertex
    simpa only [outgoingDirection, outgoingVector, add_sub_cancel_left,
      planeComplexEquiv.apply_symm_apply] using hdir
  · apply hboundary.2
    rw [edgeSegment, segment_symm] at hin
    have hin' : J.vertex i + planeComplexEquiv.symm z ∈
        segment ℝ (J.vertex i) (J.vertex (i - 1)) := by
      simpa only [sub_add_cancel] using hin
    have hpq : J.vertex i ≠ J.vertex (i - 1) := by
      have h := J.adjacent_ne (i - 1)
      simpa only [sub_add_cancel] using h.symm
    have hdir := complexDirection_sub_eq_of_mem_segment hpq hin' hneVertex
    simpa only [incomingRayDirection, incomingRayVector, add_sub_cancel_left,
      planeComplexEquiv.apply_symm_apply] using hdir

theorem vertexBackwardSector_subset_ball_diff_carrier {r : ℝ}
    (hsep : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex i) y)
    (i : ZMod J.n) :
    J.vertexBackwardSector i r ⊆ Metric.ball (J.vertex i) r \ J.carrier := by
  rintro x ⟨z, hzsector, rfl⟩
  have hzpunctured := openAngularSector_subset_puncturedBall
    (J.incomingRayDirection i) (J.outgoingDirection i) hzsector
  have hz0 : z ≠ 0 := by
    intro hz
    apply hzpunctured.2
    simp [hz]
  have hball : J.vertex i + planeComplexEquiv.symm z ∈ Metric.ball (J.vertex i) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hzpunctured.1
  refine ⟨hball, ?_⟩
  intro hcarrier
  have hincident := J.mem_incident_edge_of_mem_carrier_of_dist_lt hsep hcarrier
    (by simpa only [Metric.mem_ball, dist_comm] using hball)
  have hneVertex : J.vertex i + planeComplexEquiv.symm z ≠ J.vertex i := by
    intro heq
    apply hz0
    have hzero : planeComplexEquiv.symm z = 0 := by
      apply add_left_cancel (a := J.vertex i)
      simpa using heq
    apply planeComplexEquiv.symm.injective
    simpa using hzero
  have hboundary := direction_ne_boundary_of_mem_openAngularSector
    (J.outgoingDirection_ne_incomingRayDirection i).symm hzsector
  rcases hincident with hout | hin
  · apply hboundary.2
    have hdir := complexDirection_sub_eq_of_mem_segment (J.adjacent_ne i) hout hneVertex
    simpa only [outgoingDirection, outgoingVector, add_sub_cancel_left,
      planeComplexEquiv.apply_symm_apply] using hdir
  · apply hboundary.1
    rw [edgeSegment, segment_symm] at hin
    have hin' : J.vertex i + planeComplexEquiv.symm z ∈
        segment ℝ (J.vertex i) (J.vertex (i - 1)) := by
      simpa only [sub_add_cancel] using hin
    have hpq : J.vertex i ≠ J.vertex (i - 1) := by
      have h := J.adjacent_ne (i - 1)
      simpa only [sub_add_cancel] using h.symm
    have hdir := complexDirection_sub_eq_of_mem_segment hpq hin' hneVertex
    simpa only [incomingRayDirection, incomingRayVector, add_sub_cancel_left,
      planeComplexEquiv.apply_symm_apply] using hdir

/-- A short radial ray in the direction of `u` transports into the segment from `p` to
`p + u`. -/
theorem vertex_add_symm_mem_segment_of_mem_openRadialRay {p u : Plane} (hu : u ≠ 0)
    {r : ℝ} (hr : r ≤ ‖u‖) {z : ℂ}
    (hz : z ∈ openRadialRay
      (complexDirection (planeComplexEquiv u)
        (by simpa using planeComplexEquiv.injective.ne hu)) r) :
    p + planeComplexEquiv.symm z ∈ segment ℝ p (p + u) := by
  rcases hz with ⟨ρ, hρ, rfl⟩
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hcoef : ρ / ‖u‖ ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg hρ.1.le huNorm.le, (div_le_one huNorm).mpr ?_⟩
    exact hρ.2.le.trans hr
  have hsymm : planeComplexEquiv.symm
      ((ρ : ℂ) * (complexDirection (planeComplexEquiv u)
        (by simpa using planeComplexEquiv.injective.ne hu) : ℂ)) = (ρ / ‖u‖) • u := by
    apply planeComplexEquiv.injective
    rw [planeComplexEquiv.apply_symm_apply, map_smul, Complex.real_smul,
      coe_complexDirection, norm_planeComplexEquiv, Complex.ofReal_div]
    field_simp [huNorm.ne']
  apply add_mem_segment_of_mem_segment_zero
  rw [segment_eq_image]
  refine ⟨ρ / ‖u‖, hcoef, ?_⟩
  simp only [smul_zero, zero_add, hsymm]

/-- The punctured vertex ball is exactly the union of its two angular sectors. -/
theorem ball_diff_carrier_eq_vertexSectors {r : ℝ}
    (hsep : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, r < dist (J.vertex i) y)
    (hlen : ∀ i : ZMod J.n, r < dist (J.vertex i) (J.vertex (i + 1)))
    (i : ZMod J.n) :
    Metric.ball (J.vertex i) r \ J.carrier =
      J.vertexForwardSector i r ∪ J.vertexBackwardSector i r := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxball, hxcarrier⟩
    have hxne : x ≠ J.vertex i := fun h => hxcarrier (h ▸ J.vertex_mem_carrier i)
    set z : ℂ := planeComplexEquiv (x - J.vertex i) with hz
    have hz0 : z ≠ 0 := by
      intro hzero
      apply hxne
      rw [← sub_eq_zero]
      apply planeComplexEquiv.injective
      simpa [hz] using hzero
    have hzr : ‖z‖ < r := by
      rw [hz, norm_planeComplexEquiv]
      simpa only [Metric.mem_ball, dist_eq_norm] using hxball
    have hzpunctured : z ∈ Metric.ball (0 : ℂ) r \ {0} := by
      refine ⟨?_, ?_⟩
      · simpa [Metric.mem_ball, dist_zero_right] using hzr
      · simpa [Set.mem_singleton_iff] using hz0
    have hcover := puncturedBall_subset_twoSectors_union_rays
      (J.outgoingDirection_ne_incomingRayDirection i) hzpunctured
    rcases hcover with ((hforward | hbackward) | hout) | hin
    · left
      refine ⟨z, hforward, ?_⟩
      change J.vertex i + planeComplexEquiv.symm z = x
      rw [hz, planeComplexEquiv.symm_apply_apply]
      abel
    · right
      refine ⟨z, hbackward, ?_⟩
      change J.vertex i + planeComplexEquiv.symm z = x
      rw [hz, planeComplexEquiv.symm_apply_apply]
      abel
    · exfalso
      apply hxcarrier
      have hrout : r ≤ ‖J.outgoingVector i‖ := by
        have : r < ‖J.outgoingVector i‖ := by
          simpa [outgoingVector, dist_eq_norm, norm_sub_rev] using hlen i
        exact this.le
      have hseg := vertex_add_symm_mem_segment_of_mem_openRadialRay
        (p := J.vertex i) (J.outgoingVector_ne_zero i) hrout hout
      have hxrepr : J.vertex i + planeComplexEquiv.symm z = x := by
        rw [hz, planeComplexEquiv.symm_apply_apply]
        abel
      rw [hxrepr] at hseg
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [edgeSegment]
      convert hseg using 1; simp only [outgoingVector]; abel
    · exfalso
      apply hxcarrier
      have hlenPrev := hlen (i - 1)
      have hrin : r < ‖J.incomingRayVector i‖ := by
        rw [incomingRayVector]
        simpa only [sub_add_cancel, dist_eq_norm] using hlenPrev
      have hseg := vertex_add_symm_mem_segment_of_mem_openRadialRay
        (p := J.vertex i) (J.incomingRayVector_ne_zero i) hrin.le hin
      have hxrepr : J.vertex i + planeComplexEquiv.symm z = x := by
        rw [hz, planeComplexEquiv.symm_apply_apply]
        abel
      rw [hxrepr] at hseg
      apply Set.mem_iUnion.mpr
      refine ⟨i - 1, ?_⟩
      rw [edgeSegment, segment_symm]
      convert hseg using 1; simp only [incomingRayVector, sub_add_cancel]; abel
  · intro x hx
    rcases hx with hx | hx
    · exact J.vertexForwardSector_subset_ball_diff_carrier hsep i hx
    · exact J.vertexBackwardSector_subset_ball_diff_carrier hsep i hx

/-! #### Rectangular coordinates along an edge -/

/-- Length of edge `i`. -/
noncomputable def edgeLength (i : ZMod J.n) : ℝ :=
  ‖J.outgoingVector i‖

theorem edgeLength_pos (i : ZMod J.n) : 0 < J.edgeLength i :=
  norm_pos_iff.mpr (J.outgoingVector_ne_zero i)

/-- Complex coordinates centered at the initial vertex and divided by the oriented unit edge
direction.  The edge itself is the real interval from `0` to `edgeLength`. -/
noncomputable def edgeCoordinate (i : ZMod J.n) (x : Plane) : ℂ :=
  planeComplexEquiv (x - J.vertex i) / (J.outgoingDirection i : ℂ)

/-- Inverse edge coordinates. -/
noncomputable def edgeCoordinateInv (i : ZMod J.n) (z : ℂ) : Plane :=
  J.vertex i + planeComplexEquiv.symm (z * (J.outgoingDirection i : ℂ))

@[simp] theorem edgeCoordinate_edgeCoordinateInv (i : ZMod J.n) (z : ℂ) :
    J.edgeCoordinate i (J.edgeCoordinateInv i z) = z := by
  rw [edgeCoordinate, edgeCoordinateInv]
  have hsub : J.vertex i + planeComplexEquiv.symm
      (z * (J.outgoingDirection i : ℂ)) - J.vertex i =
      planeComplexEquiv.symm (z * (J.outgoingDirection i : ℂ)) := by abel
  rw [hsub, planeComplexEquiv.apply_symm_apply, mul_div_cancel_right₀]
  exact (J.outgoingDirection i).coe_ne_zero

@[simp] theorem edgeCoordinateInv_edgeCoordinate (i : ZMod J.n) (x : Plane) :
    J.edgeCoordinateInv i (J.edgeCoordinate i x) = x := by
  rw [edgeCoordinateInv, edgeCoordinate, div_mul_cancel₀]
  · rw [planeComplexEquiv.symm_apply_apply]
    abel
  · exact (J.outgoingDirection i).coe_ne_zero

@[simp] theorem edgeCoordinate_initial (i : ZMod J.n) :
    J.edgeCoordinate i (J.vertex i) = 0 := by
  simp [edgeCoordinate]

@[simp] theorem edgeCoordinate_terminal (i : ZMod J.n) :
    J.edgeCoordinate i (J.vertex (i + 1)) = J.edgeLength i := by
  rw [edgeCoordinate]
  apply (div_eq_iff (J.outgoingDirection i).coe_ne_zero).2
  change planeComplexEquiv (J.outgoingVector i) =
    (J.edgeLength i : ℂ) * (J.outgoingDirection i : ℂ)
  rw [edgeLength, outgoingDirection, ← norm_planeComplexEquiv]
  exact (norm_mul_complexDirection _ _).symm

/-- An open rectangular tube around the central part of edge `i`. -/
noncomputable def edgeTube (i : ZMod J.n) (trim width : ℝ) : Set Plane :=
  {x | 2 * trim < (J.edgeCoordinate i x).re ∧
    (J.edgeCoordinate i x).re < J.edgeLength i - 2 * trim ∧
    -width < (J.edgeCoordinate i x).im ∧ (J.edgeCoordinate i x).im < width}

/-- The positive-imaginary half of the edge tube. -/
noncomputable def edgePositiveSide (i : ZMod J.n) (trim width : ℝ) : Set Plane :=
  {x | 2 * trim < (J.edgeCoordinate i x).re ∧
    (J.edgeCoordinate i x).re < J.edgeLength i - 2 * trim ∧
    0 < (J.edgeCoordinate i x).im ∧ (J.edgeCoordinate i x).im < width}

/-- The negative-imaginary half of the edge tube. -/
noncomputable def edgeNegativeSide (i : ZMod J.n) (trim width : ℝ) : Set Plane :=
  {x | 2 * trim < (J.edgeCoordinate i x).re ∧
    (J.edgeCoordinate i x).re < J.edgeLength i - 2 * trim ∧
    -width < (J.edgeCoordinate i x).im ∧ (J.edgeCoordinate i x).im < 0}

theorem continuous_edgeCoordinate (i : ZMod J.n) : Continuous (J.edgeCoordinate i) := by
  unfold edgeCoordinate
  fun_prop

theorem isOpen_edgeTube (i : ZMod J.n) (trim width : ℝ) :
    IsOpen (J.edgeTube i trim width) := by
  have hre : Continuous fun x => (J.edgeCoordinate i x).re :=
    Complex.continuous_re.comp (J.continuous_edgeCoordinate i)
  have him : Continuous fun x => (J.edgeCoordinate i x).im :=
    Complex.continuous_im.comp (J.continuous_edgeCoordinate i)
  rw [edgeTube]
  exact (isOpen_lt continuous_const hre).inter ((isOpen_lt hre continuous_const).inter
    ((isOpen_lt continuous_const him).inter (isOpen_lt him continuous_const)))

theorem edgePositiveSide_subset_edgeTube (i : ZMod J.n) {trim width : ℝ}
    (hwidth : 0 < width) :
    J.edgePositiveSide i trim width ⊆ J.edgeTube i trim width := by
  rintro x ⟨hx0, hx1, hy0, hy1⟩
  exact ⟨hx0, hx1, hy0.trans' (neg_neg_of_pos hwidth), hy1⟩

theorem edgeNegativeSide_subset_edgeTube (i : ZMod J.n) {trim width : ℝ}
    (hwidth : 0 < width) :
    J.edgeNegativeSide i trim width ⊆ J.edgeTube i trim width := by
  rintro x ⟨hx0, hx1, hy0, hy1⟩
  exact ⟨hx0, hx1, hy0, hy1.trans hwidth⟩

private theorem edgePositiveSide_eq_image_rectangle (i : ZMod J.n) (trim width : ℝ) :
    J.edgePositiveSide i trim width =
      (fun p : ℝ × ℝ => J.edgeCoordinateInv i ((p.1 : ℂ) + p.2 * Complex.I)) ''
        (Set.Ioo (2 * trim) (J.edgeLength i - 2 * trim) ×ˢ Set.Ioo 0 width) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨((J.edgeCoordinate i x).re, (J.edgeCoordinate i x).im),
      ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, ?_⟩
    change J.edgeCoordinateInv i
      (((J.edgeCoordinate i x).re : ℂ) + (J.edgeCoordinate i x).im * Complex.I) = x
    rw [Complex.re_add_im, J.edgeCoordinateInv_edgeCoordinate]
  · rintro ⟨p, hp, rfl⟩
    change 2 * trim < (J.edgeCoordinate i (J.edgeCoordinateInv i _)).re ∧
      (J.edgeCoordinate i (J.edgeCoordinateInv i _)).re < J.edgeLength i - 2 * trim ∧
      0 < (J.edgeCoordinate i (J.edgeCoordinateInv i _)).im ∧
      (J.edgeCoordinate i (J.edgeCoordinateInv i _)).im < width
    rcases hp with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    simpa using ⟨hx0, hx1, hy0, hy1⟩

private theorem edgeNegativeSide_eq_image_rectangle (i : ZMod J.n) (trim width : ℝ) :
    J.edgeNegativeSide i trim width =
      (fun p : ℝ × ℝ => J.edgeCoordinateInv i ((p.1 : ℂ) + p.2 * Complex.I)) ''
        (Set.Ioo (2 * trim) (J.edgeLength i - 2 * trim) ×ˢ Set.Ioo (-width) 0) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx0, hx1, hy0, hy1⟩
    refine ⟨((J.edgeCoordinate i x).re, (J.edgeCoordinate i x).im),
      ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩, ?_⟩
    change J.edgeCoordinateInv i
      (((J.edgeCoordinate i x).re : ℂ) + (J.edgeCoordinate i x).im * Complex.I) = x
    rw [Complex.re_add_im, J.edgeCoordinateInv_edgeCoordinate]
  · rintro ⟨p, hp, rfl⟩
    change 2 * trim < (J.edgeCoordinate i (J.edgeCoordinateInv i _)).re ∧
      (J.edgeCoordinate i (J.edgeCoordinateInv i _)).re < J.edgeLength i - 2 * trim ∧
      -width < (J.edgeCoordinate i (J.edgeCoordinateInv i _)).im ∧
      (J.edgeCoordinate i (J.edgeCoordinateInv i _)).im < 0
    rcases hp with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    simpa using ⟨hx0, hx1, hy0, hy1⟩

theorem isPathConnected_edgePositiveSide (i : ZMod J.n) {trim width : ℝ}
    (hwidth : 0 < width) (hlen : 4 * trim < J.edgeLength i) :
    IsPathConnected (J.edgePositiveSide i trim width) := by
  rw [edgePositiveSide_eq_image_rectangle]
  have hdom := ((convex_Ioo (2 * trim) (J.edgeLength i - 2 * trim)).prod
    (convex_Ioo (0 : ℝ) width)).isPathConnected (by
    refine ⟨((J.edgeLength i) / 2, width / 2), ?_, ?_⟩
    · constructor <;> linarith
    · constructor <;> linarith)
  exact hdom.image (by unfold edgeCoordinateInv; fun_prop)

theorem isPathConnected_edgeNegativeSide (i : ZMod J.n) {trim width : ℝ}
    (hwidth : 0 < width) (hlen : 4 * trim < J.edgeLength i) :
    IsPathConnected (J.edgeNegativeSide i trim width) := by
  rw [edgeNegativeSide_eq_image_rectangle]
  have hdom := ((convex_Ioo (2 * trim) (J.edgeLength i - 2 * trim)).prod
    (convex_Ioo (-width) (0 : ℝ))).isPathConnected (by
    refine ⟨((J.edgeLength i) / 2, -width / 2), ?_, ?_⟩
    · constructor <;> linarith
    · constructor <;> linarith)
  exact hdom.image (by unfold edgeCoordinateInv; fun_prop)

/-- The central edge axis is approached from the positive side rectangle. -/
theorem edgeAxis_mem_closure_positiveSide (i : ZMod J.n) {trim width s : ℝ}
    (hwidth : 0 < width) (hlen : 4 * trim < J.edgeLength i)
    (hs : s ∈ Set.Icc (2 * trim) (J.edgeLength i - 2 * trim)) :
    J.edgeCoordinateInv i (s : ℂ) ∈ closure (J.edgePositiveSide i trim width) := by
  rw [edgePositiveSide_eq_image_rectangle]
  let f : ℝ × ℝ → Plane := fun p =>
    J.edgeCoordinateInv i ((p.1 : ℂ) + p.2 * Complex.I)
  have hf : Continuous f := by unfold f edgeCoordinateInv; fun_prop
  apply image_closure_subset_closure_image hf
  refine ⟨(s, 0), ?_, ?_⟩
  · rw [closure_prod_eq,
      closure_Ioo (a := 2 * trim) (b := J.edgeLength i - 2 * trim) (by linarith),
      closure_Ioo (a := (0 : ℝ)) (b := width) hwidth.ne]
    exact ⟨hs, le_rfl, hwidth.le⟩
  · simp only [f, Complex.ofReal_zero, zero_mul, add_zero]

/-- The central edge axis is approached from the negative side rectangle. -/
theorem edgeAxis_mem_closure_negativeSide (i : ZMod J.n) {trim width s : ℝ}
    (hwidth : 0 < width) (hlen : 4 * trim < J.edgeLength i)
    (hs : s ∈ Set.Icc (2 * trim) (J.edgeLength i - 2 * trim)) :
    J.edgeCoordinateInv i (s : ℂ) ∈ closure (J.edgeNegativeSide i trim width) := by
  rw [edgeNegativeSide_eq_image_rectangle]
  let f : ℝ × ℝ → Plane := fun p =>
    J.edgeCoordinateInv i ((p.1 : ℂ) + p.2 * Complex.I)
  have hf : Continuous f := by unfold f edgeCoordinateInv; fun_prop
  apply image_closure_subset_closure_image hf
  refine ⟨(s, 0), ?_, ?_⟩
  · rw [closure_prod_eq,
      closure_Ioo (a := 2 * trim) (b := J.edgeLength i - 2 * trim) (by linarith),
      closure_Ioo (a := -width) (b := (0 : ℝ)) (by linarith)]
    exact ⟨hs, neg_nonpos.mpr hwidth.le, le_rfl⟩
  · simp only [f, Complex.ofReal_zero, zero_mul, add_zero]

theorem edgeCoordinate_im_eq_zero_of_mem_edgeSegment (i : ZMod J.n) {x : Plane}
    (hx : x ∈ J.edgeSegment i) : (J.edgeCoordinate i x).im = 0 := by
  rw [edgeSegment, segment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  change (J.edgeCoordinate i ((1 - t) • J.vertex i + t • J.vertex (i + 1))).im = 0
  have hpoint : (1 - t) • J.vertex i + t • J.vertex (i + 1) =
      J.vertex i + t • J.outgoingVector i := by
    rw [outgoingVector]
    module
  rw [hpoint, edgeCoordinate]
  have hsub : J.vertex i + t • J.outgoingVector i - J.vertex i =
      t • J.outgoingVector i := by abel
  rw [hsub, map_smul, Complex.real_smul, mul_div_assoc,
    show planeComplexEquiv (J.outgoingVector i) / (J.outgoingDirection i : ℂ) =
      J.edgeLength i by
        have ht := J.edgeCoordinate_terminal i
        rw [edgeCoordinate] at ht
        exact ht]
  simp

/-- Removing the polygon from a central edge tube leaves exactly its positive and negative
rectangular halves. -/
theorem edgeTube_diff_carrier_eq_sides (i : ZMod J.n) {trim width : ℝ}
    (htrim : 0 < trim) (hwidth : 0 < width)
    (honly : J.edgeTube i trim width ∩ J.carrier ⊆ J.edgeSegment i) :
    J.edgeTube i trim width \ J.carrier =
      J.edgePositiveSide i trim width ∪ J.edgeNegativeSide i trim width := by
  apply Set.Subset.antisymm
  · rintro x ⟨htube, hxcarrier⟩
    rcases lt_trichotomy 0 (J.edgeCoordinate i x).im with him | him | him
    · exact Or.inl ⟨htube.1, htube.2.1, him, htube.2.2.2⟩
    · exfalso
      apply hxcarrier
      have hre0 : 0 < (J.edgeCoordinate i x).re := by linarith [htube.1]
      have hreL : (J.edgeCoordinate i x).re < J.edgeLength i := by
        linarith [htube.2.1]
      have hzray : (J.edgeCoordinate i x) * (J.outgoingDirection i : ℂ) ∈
          openRadialRay (J.outgoingDirection i) (J.edgeLength i) := by
        refine ⟨(J.edgeCoordinate i x).re, ⟨hre0, hreL⟩, ?_⟩
        change ((J.edgeCoordinate i x).re : ℂ) * (J.outgoingDirection i : ℂ) =
          J.edgeCoordinate i x * (J.outgoingDirection i : ℂ)
        congr 1
        rw [← Complex.re_add_im (J.edgeCoordinate i x), ← him]
        simp
      have hseg := vertex_add_symm_mem_segment_of_mem_openRadialRay
        (p := J.vertex i) (J.outgoingVector_ne_zero i) le_rfl hzray
      rw [← edgeCoordinateInv, J.edgeCoordinateInv_edgeCoordinate] at hseg
      exact Set.mem_iUnion.mpr ⟨i, by
        rw [edgeSegment]
        convert hseg using 1; simp only [outgoingVector]; abel⟩
    · exact Or.inr ⟨htube.1, htube.2.1, htube.2.2.1, him⟩
  · rintro x (hx | hx)
    · refine ⟨J.edgePositiveSide_subset_edgeTube i hwidth hx, ?_⟩
      intro hxcarrier
      have hxedge := honly ⟨J.edgePositiveSide_subset_edgeTube i hwidth hx, hxcarrier⟩
      linarith [hx.2.2.1, J.edgeCoordinate_im_eq_zero_of_mem_edgeSegment i hxedge]
    · refine ⟨J.edgeNegativeSide_subset_edgeTube i hwidth hx, ?_⟩
      intro hxcarrier
      have hxedge := honly ⟨J.edgeNegativeSide_subset_edgeTube i hwidth hx, hxcarrier⟩
      linarith [hx.2.2.2, J.edgeCoordinate_im_eq_zero_of_mem_edgeSegment i hxedge]

/-- Distinct polygon edges can meet only at an endpoint of the first edge. -/
theorem edgeSegment_inter_subset_endpoints {i j : ZMod J.n} (hij : i ≠ j) :
    J.edgeSegment i ∩ J.edgeSegment j ⊆ {J.vertex i, J.vertex (i + 1)} := by
  intro x hx
  by_cases hprev : i = j + 1
  · have hinter : J.edgeSegment j ∩ J.edgeSegment i = {J.vertex i} := by
      rw [hprev]
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter j
    have : x = J.vertex i := by
      have hx' : x ∈ J.edgeSegment j ∩ J.edgeSegment i := ⟨hx.2, hx.1⟩
      rw [hinter] at hx'
      exact hx'
    simp [this]
  by_cases hnext : j = i + 1
  · have hinter : J.edgeSegment i ∩ J.edgeSegment j = {J.vertex (i + 1)} := by
      rw [hnext]
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter i
    rw [hinter] at hx
    simp [hx]
  · have hdisj := J.disjoint_edgeSegment_of_nonAdjacent
        (i := i) (j := j) ⟨hij, hprev, hnext⟩
    exact (Set.disjoint_left.1 hdisj hx.1 hx.2).elim

/-- The union of all polygon edges other than edge `i`. -/
def otherEdges (i : ZMod J.n) : Set Plane :=
  ⋃ (j : ZMod J.n) (_ : j ≠ i), J.edgeSegment j

theorem isCompact_otherEdges (i : ZMod J.n) : IsCompact (J.otherEdges i) := by
  exact isCompact_iUnion fun _ => isCompact_iUnion fun _ => J.isCompact_edgeSegment _

theorem isClosed_otherEdges (i : ZMod J.n) : IsClosed (J.otherEdges i) :=
  (J.isCompact_otherEdges i).isClosed

/-- Near a relative-interior point of a polygon edge, the carrier consists only of that edge. -/
theorem exists_ball_inter_carrier_subset_edgeSegment {i : ZMod J.n} {x : Plane}
    (hx : x ∈ openSegment ℝ (J.vertex i) (J.vertex (i + 1))) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ∩ J.carrier ⊆ J.edgeSegment i := by
  have hxEdge : x ∈ J.edgeSegment i := by
    exact openSegment_subset_segment ℝ _ _ hx
  have hxNotOther : x ∉ J.otherEdges i := by
    intro hxOther
    simp only [otherEdges, Set.mem_iUnion] at hxOther
    obtain ⟨j, hji, hxj⟩ := hxOther
    have hxEnds := J.edgeSegment_inter_subset_endpoints (Ne.symm hji) ⟨hxEdge, hxj⟩
    rcases hxEnds with hx0 | hx1
    · subst x
      simp [J.adjacent_ne i] at hx
    · subst x
      simp [J.adjacent_ne i] at hx
  have hnhds : (J.otherEdges i)ᶜ ∈ nhds x :=
    J.isClosed_otherEdges i |>.isOpen_compl.mem_nhds hxNotOther
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r, hr, ?_⟩
  rintro y ⟨hyBall, hyCarrier⟩
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyCarrier
  by_cases hji : j = i
  · simpa [hji] using hyj
  · exact False.elim (hball hyBall <|
      Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hyj⟩⟩)

/-- If a straight subsegment of the polygon carrier passes through a polygon vertex, its two
local sides occupy the two incident polygon edges. -/
theorem exists_basePoints_on_incident_edges {P Q : Plane} (hPQ : P ≠ Q)
    (hbase : segment ℝ P Q ⊆ J.carrier) {i : ZMod J.n}
    (hi : J.vertex i ∈ openSegment ℝ P Q) :
    (∃ y ≠ J.vertex i, y ∈ segment ℝ P Q ∧ y ∈ J.edgeSegment i) ∧
      ∃ y ≠ J.vertex i, y ∈ segment ℝ P Q ∧ y ∈ J.edgeSegment (i - 1) := by
  obtain ⟨ε, hε, -, -, hvertex⟩ := J.exists_featureRadius
  have hvertex3 : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
      ∀ y ∈ J.edgeSegment j, 3 * ε < dist (J.vertex i) y := by
    intro i j hij hprev y hy
    exact (by linarith [hε] : 3 * ε < 12 * ε).trans (hvertex i j hij hprev y hy)
  have hiP : J.vertex i ≠ P := by
    intro h
    rw [h] at hi
    have := (left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hi
    exact hPQ this
  have hiQ : J.vertex i ≠ Q := by
    intro h
    rw [h] at hi
    have := (right_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hi
    exact hPQ this
  obtain ⟨yP, hyPopen, hyPball⟩ :=
    exists_mem_openSegment_inter_ball hiP (r := 3 * ε) (by positivity)
  obtain ⟨yQ, hyQopen, hyQball⟩ :=
    exists_mem_openSegment_inter_ball hiQ (r := 3 * ε) (by positivity)
  have hiSegment : J.vertex i ∈ segment ℝ P Q :=
    openSegment_subset_segment ℝ _ _ hi
  have hyPBase : yP ∈ segment ℝ P Q :=
    (convex_segment (𝕜 := ℝ) P Q).segment_subset hiSegment
      (left_mem_segment ℝ P Q) (openSegment_subset_segment ℝ _ _ hyPopen)
  have hyQBase : yQ ∈ segment ℝ P Q :=
    (convex_segment (𝕜 := ℝ) P Q).segment_subset hiSegment
      (right_mem_segment ℝ P Q) (openSegment_subset_segment ℝ _ _ hyQopen)
  have hyPne : yP ≠ J.vertex i := by
    intro h
    rw [h] at hyPopen
    simp [hiP] at hyPopen
  have hyQne : yQ ≠ J.vertex i := by
    intro h
    rw [h] at hyQopen
    simp [hiQ] at hyQopen
  have hyPInc : yP ∈ J.edgeSegment i ∪ J.edgeSegment (i - 1) := by
    have hmem : yP ∈ Metric.ball (J.vertex i) (3 * ε) ∩ J.carrier :=
      ⟨hyPball, hbase hyPBase⟩
    rw [J.ball_inter_carrier_eq_incident_edges hvertex3 i] at hmem
    exact hmem.2
  have hyQInc : yQ ∈ J.edgeSegment i ∪ J.edgeSegment (i - 1) := by
    have hmem : yQ ∈ Metric.ball (J.vertex i) (3 * ε) ∩ J.carrier :=
      ⟨hyQball, hbase hyQBase⟩
    rw [J.ball_inter_carrier_eq_incident_edges hvertex3 i] at hmem
    exact hmem.2
  have hsbtw {a b x : Plane} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
      Sbtw ℝ a x b := by
    apply sbtw_iff_mem_image_Ioo_and_ne.mpr
    rw [← openSegment_eq_image_lineMap]
    exact ⟨hx, hab⟩
  have hPiQ := hsbtw hPQ hi
  have hiPyP := hsbtw hiP hyPopen
  have hiQyQ := hsbtw hiQ hyQopen
  have hstrict : Sbtw ℝ yP (J.vertex i) yQ :=
    (hPiQ.trans_left_right hiPyP.symm).trans_right_left hiQyQ
  have hbetween : J.vertex i ∈ openSegment ℝ yP yQ := by
    rw [openSegment_eq_image_lineMap]
    exact hstrict.mem_image_Ioo
  have hnotBothOutgoing : ¬(yP ∈ J.edgeSegment i ∧ yQ ∈ J.edgeSegment i) := by
    rintro ⟨hyP, hyQ⟩
    exact endpoint_not_mem_openSegment_of_mem_segment (J.adjacent_ne i)
      hstrict.left_ne_right hyP hyQ hbetween
  have hnotBothIncoming :
      ¬(yP ∈ J.edgeSegment (i - 1) ∧ yQ ∈ J.edgeSegment (i - 1)) := by
    rintro ⟨hyP, hyQ⟩
    have hne : J.vertex i ≠ J.vertex (i - 1) := by
      have := J.adjacent_ne (i - 1)
      simpa using this.symm
    apply endpoint_not_mem_openSegment_of_mem_segment hne
      hstrict.left_ne_right _ _ hbetween
    · simpa only [edgeSegment, sub_add_cancel, segment_symm] using hyP
    · simpa only [edgeSegment, sub_add_cancel, segment_symm] using hyQ
  rcases hyPInc with hyPout | hyPin <;> rcases hyQInc with hyQout | hyQin
  · exact False.elim (hnotBothOutgoing ⟨hyPout, hyQout⟩)
  · exact ⟨⟨yP, hyPne, hyPBase, hyPout⟩, yQ, hyQne, hyQBase, hyQin⟩
  · exact ⟨⟨yQ, hyQne, hyQBase, hyQout⟩, yP, hyPne, hyPBase, hyPin⟩
  · exact False.elim (hnotBothIncoming ⟨hyPin, hyQin⟩)

/-- An edge meeting the relative interior of a straight subsegment of the carrier overlaps that
subsegment in at least two points. -/
theorem exists_second_basePoint_of_edge_inter_openSegment {P Q x : Plane}
    (hPQ : P ≠ Q) (hbase : segment ℝ P Q ⊆ J.carrier) {i : ZMod J.n}
    (hxEdge : x ∈ J.edgeSegment i) (hxBase : x ∈ openSegment ℝ P Q) :
    ∃ y ≠ x, y ∈ J.edgeSegment i ∧ y ∈ segment ℝ P Q := by
  have hxCases : x = J.vertex i ∨ x = J.vertex (i + 1) ∨
      x ∈ openSegment ℝ (J.vertex i) (J.vertex (i + 1)) := by
    change x ∈ segment ℝ (J.vertex i) (J.vertex (i + 1)) at hxEdge
    rw [← insert_endpoints_openSegment] at hxEdge
    simpa only [Set.mem_insert_iff] using hxEdge
  rcases hxCases with rfl | rfl | hxInterior
  · obtain ⟨hout, -⟩ := J.exists_basePoints_on_incident_edges hPQ hbase hxBase
    obtain ⟨y, hyne, hyBase, hyEdge⟩ := hout
    exact ⟨y, hyne, hyEdge, hyBase⟩
  · obtain ⟨-, hin⟩ := J.exists_basePoints_on_incident_edges hPQ hbase hxBase
    obtain ⟨y, hyne, hyBase, hyEdge⟩ := hin
    refine ⟨y, hyne, ?_, hyBase⟩
    simpa only [add_sub_cancel_right] using hyEdge
  · obtain ⟨r, hr, hlocal⟩ :=
      J.exists_ball_inter_carrier_subset_edgeSegment hxInterior
    have hxP : x ≠ P := by
      intro h
      rw [h] at hxBase
      exact hPQ ((left_mem_openSegment_iff (𝕜 := ℝ) (x := P) (y := Q)).mp hxBase)
    obtain ⟨y, hyOpen, hyBall⟩ := exists_mem_openSegment_inter_ball hxP hr
    have hxSegment : x ∈ segment ℝ P Q :=
      openSegment_subset_segment ℝ _ _ hxBase
    have hyBase : y ∈ segment ℝ P Q :=
      (convex_segment (𝕜 := ℝ) P Q).segment_subset hxSegment
        (left_mem_segment ℝ P Q) (openSegment_subset_segment ℝ _ _ hyOpen)
    have hyne : y ≠ x := by
      intro h
      rw [h] at hyOpen
      simp [hxP] at hyOpen
    exact ⟨y, hyne, hlocal ⟨hyBall, hbase hyBase⟩, hyBase⟩

/-- In normalized ear coordinates, every polygon edge meeting the open base lies on the
horizontal base line. -/
theorem edge_endpoints_on_axis_of_inter_openBase
    {P Q : Plane} (hPQ : P ≠ Q) (hP0 : P 1 = 0) (hQ0 : Q 1 = 0)
    (hbase : segment ℝ P Q ⊆ J.carrier)
    {i : ZMod J.n} {x : Plane} (hxEdge : x ∈ J.edgeSegment i)
    (hxBase : x ∈ openSegment ℝ P Q) :
    (J.vertex i) 1 = 0 ∧ (J.vertex (i + 1)) 1 = 0 := by
  obtain ⟨y, hyne, hyEdge, hyBase⟩ :=
    J.exists_second_basePoint_of_edge_inter_openSegment hPQ hbase hxEdge hxBase
  have haxis {p : Plane}
      (hp : p ∈ segment ℝ P Q) : p 1 = 0 := by
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨t, -, rfl⟩ := hp
    simp [AffineMap.lineMap_apply_module, hP0, hQ0]
  apply endpoint_secondCoords_eq_zero_of_two_axis_points
    (a := J.vertex i) (b := J.vertex (i + 1)) (x := x) (y := y)
    (J.adjacent_ne i) hyne.symm
  · exact hxEdge
  · exact hyEdge
  · exact haxis (openSegment_subset_segment ℝ _ _ hxBase)
  · exact haxis hyBase

theorem mem_edgeSegment_or_otherEdges {x : Plane} (hx : x ∈ J.carrier) (i : ZMod J.n) :
    x ∈ J.edgeSegment i ∨ x ∈ J.otherEdges i := by
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  rcases eq_or_ne j i with rfl | hji
  · exact Or.inl hxj
  · exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hxj⟩⟩)

/-- The closed central subsegment obtained by trimming `2 * trim` from both endpoint coordinates. -/
noncomputable def edgeCore (i : ZMod J.n) (trim : ℝ) : Set Plane :=
  (fun s : ℝ => J.edgeCoordinateInv i s) ''
    Set.Icc (2 * trim) (J.edgeLength i - 2 * trim)

theorem isCompact_edgeCore (i : ZMod J.n) (trim : ℝ) :
    IsCompact (J.edgeCore i trim) := by
  apply (isCompact_Icc.image_of_continuousOn)
  unfold edgeCoordinateInv
  fun_prop

theorem edgeCore_subset_edgeSegment (i : ZMod J.n) {trim : ℝ} (htrim : 0 < trim)
    (_ : 4 * trim < J.edgeLength i) : J.edgeCore i trim ⊆ J.edgeSegment i := by
  rintro x ⟨s, hs, rfl⟩
  have hs0 : 0 < s := by linarith [hs.1]
  have hsL : s < J.edgeLength i := by linarith [hs.2]
  have hzray : (s : ℂ) * (J.outgoingDirection i : ℂ) ∈
      openRadialRay (J.outgoingDirection i) (J.edgeLength i) := ⟨s, ⟨hs0, hsL⟩, rfl⟩
  have hseg := vertex_add_symm_mem_segment_of_mem_openRadialRay
    (p := J.vertex i) (J.outgoingVector_ne_zero i) le_rfl hzray
  rw [edgeSegment]
  change J.vertex i + planeComplexEquiv.symm
    ((s : ℂ) * (J.outgoingDirection i : ℂ)) ∈
      segment ℝ (J.vertex i) (J.vertex (i + 1))
  convert hseg using 1
  simp only [outgoingVector]
  abel

theorem disjoint_edgeCore_otherEdges (i : ZMod J.n) {trim : ℝ} (htrim : 0 < trim)
    (hlen : 4 * trim < J.edgeLength i) :
    Disjoint (J.edgeCore i trim) (J.otherEdges i) := by
  rw [Set.disjoint_left]
  intro x hxcore hxother
  rcases Set.mem_iUnion.mp hxother with ⟨j, hxother⟩
  rcases Set.mem_iUnion.mp hxother with ⟨hji, hxj⟩
  have hxi := J.edgeCore_subset_edgeSegment i htrim hlen hxcore
  rcases J.edgeSegment_inter_subset_endpoints hji.symm ⟨hxi, hxj⟩ with hstart | hend
  · rcases hxcore with ⟨s, hs, hsx⟩
    have hcoord := congrArg (J.edgeCoordinate i) hsx
    rw [J.edgeCoordinate_edgeCoordinateInv, hstart, J.edgeCoordinate_initial] at hcoord
    have : 0 < s := by linarith [hs.1]
    exact this.ne' (Complex.ofReal_injective hcoord)
  · rcases hxcore with ⟨s, hs, hsx⟩
    have hcoord := congrArg (J.edgeCoordinate i) hsx
    rw [J.edgeCoordinate_edgeCoordinateInv, hend, J.edgeCoordinate_terminal] at hcoord
    have : s < J.edgeLength i := by linarith [hs.2]
    exact this.ne (Complex.ofReal_injective hcoord)

/-- Inverse edge coordinates preserve distances. -/
theorem dist_edgeCoordinateInv (i : ZMod J.n) (z w : ℂ) :
    dist (J.edgeCoordinateInv i z) (J.edgeCoordinateInv i w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖J.edgeCoordinateInv i z - J.edgeCoordinateInv i w‖ =
        ‖planeComplexEquiv (J.edgeCoordinateInv i z - J.edgeCoordinateInv i w)‖ :=
      (norm_planeComplexEquiv _).symm
    _ = ‖(z - w) * (J.outgoingDirection i : ℂ)‖ := by
      congr 1
      simp only [edgeCoordinateInv, map_sub, map_add, planeComplexEquiv.apply_symm_apply]
      ring
    _ = ‖z - w‖ := by rw [norm_mul, Circle.norm_coe, mul_one]

/-- After fixing a longitudinal trim, one can choose a uniform thinner transverse width so that
every central edge tube meets the polygon only in its own edge. -/
theorem exists_edgeTube_width {trim : ℝ} (htrim : 0 < trim)
    (hlen : ∀ i : ZMod J.n, 4 * trim < J.edgeLength i) :
    ∃ width : ℝ, 0 < width ∧ width < trim ∧
      ∀ i : ZMod J.n, J.edgeTube i trim width ∩ J.carrier ⊆ J.edgeSegment i := by
  classical
  have hsep : ∀ i : ZMod J.n, ∃ d : NNReal, 0 < d ∧
      ∀ q ∈ J.edgeCore i trim, ∀ x ∈ J.otherEdges i, (d : ℝ) < dist q x := by
    intro i
    obtain ⟨d, hd, hdist⟩ := Metric.exists_pos_forall_lt_edist (J.isCompact_edgeCore i trim)
      (J.isClosed_otherEdges i) (J.disjoint_edgeCore_otherEdges i htrim (hlen i))
    refine ⟨d, hd, ?_⟩
    intro q hq x hx
    have := hdist q hq x hx
    simpa [edist_dist] using this
  let d : ZMod J.n → ℝ := fun i => ((hsep i).choose : NNReal)
  have hdpos : ∀ i, 0 < d i := by
    intro i
    exact_mod_cast (hsep i).choose_spec.1
  obtain ⟨w, hw, hwd⟩ := exists_pos_three_mul_lt_of_finite d hdpos
  set width : ℝ := min w (trim / 2) with hwidth
  have hwidthpos : 0 < width := by rw [hwidth]; positivity
  have hwidthtrim : width < trim := by
    rw [hwidth]
    exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨width, hwidthpos, hwidthtrim, ?_⟩
  intro i x hx
  rcases J.mem_edgeSegment_or_otherEdges hx.2 i with hxi | hxother
  · exact hxi
  · exfalso
    set q : Plane := J.edgeCoordinateInv i ((J.edgeCoordinate i x).re : ℂ) with hq
    have hqcore : q ∈ J.edgeCore i trim := by
      refine ⟨(J.edgeCoordinate i x).re, ⟨hx.1.1.le, hx.1.2.1.le⟩, hq.symm⟩
    have hdistLower : 3 * width < dist q x := by
      have hdi := (hsep i).choose_spec.2 q hqcore x hxother
      have hwle : width ≤ w := by rw [hwidth]; exact min_le_left _ _
      have h3 : 3 * width ≤ 3 * w := mul_le_mul_of_nonneg_left hwle (by norm_num)
      exact (h3.trans_lt (hwd i)).trans hdi
    have hdistUpper : dist q x < width := by
      have hxinv : J.edgeCoordinateInv i (J.edgeCoordinate i x) = x :=
        J.edgeCoordinateInv_edgeCoordinate i x
      calc
        dist q x = dist ((J.edgeCoordinate i x).re : ℂ) (J.edgeCoordinate i x) := by
          calc
            dist q x = dist (J.edgeCoordinateInv i ((J.edgeCoordinate i x).re : ℂ))
                (J.edgeCoordinateInv i (J.edgeCoordinate i x)) := by rw [hq, hxinv]
            _ = _ := J.dist_edgeCoordinateInv i _ _
        _ = |(J.edgeCoordinate i x).im| := by
          rw [dist_eq_norm]
          have hsub : ((J.edgeCoordinate i x).re : ℂ) - J.edgeCoordinate i x =
              -((J.edgeCoordinate i x).im : ℂ) * Complex.I := by
            apply Complex.ext <;> simp
          rw [hsub, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_I, mul_one]
        _ < width := abs_lt.mpr ⟨hx.1.2.2.1, hx.1.2.2.2⟩
    linarith

/-- Points on an edge have a real edge coordinate between zero and the edge length. -/
theorem edgeCoordinate_mem_real_Icc (i : ZMod J.n) {x : Plane} (hx : x ∈ J.edgeSegment i) :
    ∃ s ∈ Set.Icc (0 : ℝ) (J.edgeLength i), J.edgeCoordinate i x = s := by
  rw [edgeSegment, segment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  refine ⟨t * J.edgeLength i, ⟨mul_nonneg ht.1 (J.edgeLength_pos i).le, ?_⟩, ?_⟩
  · exact (mul_le_iff_le_one_left (J.edgeLength_pos i)).mpr ht.2
  · have hpoint : (1 - t) • J.vertex i + t • J.vertex (i + 1) =
        J.vertex i + t • J.outgoingVector i := by
      rw [outgoingVector]
      module
    change J.edgeCoordinate i ((1 - t) • J.vertex i + t • J.vertex (i + 1)) =
      (t * J.edgeLength i : ℝ)
    rw [hpoint, edgeCoordinate]
    have hsub : J.vertex i + t • J.outgoingVector i - J.vertex i =
        t • J.outgoingVector i := by abel
    rw [hsub, map_smul, Complex.real_smul, mul_div_assoc]
    have htcoord : planeComplexEquiv (J.outgoingVector i) /
        (J.outgoingDirection i : ℂ) = J.edgeLength i := by
      have ht := J.edgeCoordinate_terminal i
      rw [edgeCoordinate] at ht
      change planeComplexEquiv (J.outgoingVector i) /
        (J.outgoingDirection i : ℂ) = J.edgeLength i at ht
      exact ht
    rw [htcoord, Complex.ofReal_mul]

/-- The explicit open strip made from vertex balls and the isolated central edge tubes. -/
noncomputable def polygonStrip (trim width : ℝ) : Set Plane :=
  (⋃ i : ZMod J.n, Metric.ball (J.vertex i) (3 * trim)) ∪
    ⋃ i : ZMod J.n, J.edgeTube i trim width

theorem isOpen_polygonStrip (trim width : ℝ) : IsOpen (J.polygonStrip trim width) := by
  apply IsOpen.union
  · exact isOpen_iUnion fun i => Metric.isOpen_ball
  · exact isOpen_iUnion fun i => J.isOpen_edgeTube i trim width

/-- Vertex balls cover the endpoint portions of every edge and the central tube covers the
remainder. -/
theorem carrier_subset_polygonStrip {trim width : ℝ} (htrim : 0 < trim)
    (hwidth : 0 < width) : J.carrier ⊆ J.polygonStrip trim width := by
  intro x hxcarrier
  rcases Set.mem_iUnion.mp hxcarrier with ⟨i, hxi⟩
  obtain ⟨s, hs, hcoord⟩ := J.edgeCoordinate_mem_real_Icc i hxi
  by_cases hstart : s < 3 * trim
  · left
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hdist : dist (J.vertex i) x = s := by
      calc
        dist (J.vertex i) x =
            dist (J.edgeCoordinateInv i 0) (J.edgeCoordinateInv i (J.edgeCoordinate i x)) := by
          rw [J.edgeCoordinateInv_edgeCoordinate]
          have hv0 := J.edgeCoordinateInv_edgeCoordinate i (J.vertex i)
          rw [J.edgeCoordinate_initial] at hv0
          rw [hv0]
        _ = dist (0 : ℂ) (J.edgeCoordinate i x) := J.dist_edgeCoordinateInv i _ _
        _ = s := by rw [hcoord, dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hs.1]
    rw [Metric.mem_ball, dist_comm, hdist]
    exact hstart
  by_cases hend : J.edgeLength i - 3 * trim < s
  · left
    apply Set.mem_iUnion.mpr
    refine ⟨i + 1, ?_⟩
    have hdist : dist (J.vertex (i + 1)) x = J.edgeLength i - s := by
      calc
        dist (J.vertex (i + 1)) x =
            dist (J.edgeCoordinateInv i (J.edgeLength i))
              (J.edgeCoordinateInv i (J.edgeCoordinate i x)) := by
          rw [J.edgeCoordinateInv_edgeCoordinate]
          have hvL := J.edgeCoordinateInv_edgeCoordinate i (J.vertex (i + 1))
          rw [J.edgeCoordinate_terminal] at hvL
          rw [hvL]
        _ = dist (J.edgeLength i : ℂ) (J.edgeCoordinate i x) :=
          J.dist_edgeCoordinateInv i _ _
        _ = J.edgeLength i - s := by
          rw [hcoord, dist_eq_norm]
          rw [show (J.edgeLength i : ℂ) - (s : ℂ) =
              (J.edgeLength i - s : ℝ) by norm_num,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    rw [Metric.mem_ball, dist_comm, hdist]
    linarith
  · right
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have him : (J.edgeCoordinate i x).im = 0 :=
      J.edgeCoordinate_im_eq_zero_of_mem_edgeSegment i hxi
    have hre : (J.edgeCoordinate i x).re = s := by
      rw [hcoord]
      simp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hre] at * <;> rw [him] at *
    · linarith
    · linarith
    · linarith
    · exact hwidth

/-- Quantitative scales for the explicit polygon strip. -/
structure StripScales where
  /-- The `trim` declaration. -/
  trim : ℝ
  /-- The `width` declaration. -/
  width : ℝ
  trim_pos : 0 < trim
  width_pos : 0 < width
  width_lt_trim : width < trim
  edge_long : ∀ i : ZMod J.n, 12 * trim < J.edgeLength i
  vertex_isolation : ∀ i j : ZMod J.n, i ≠ j → i ≠ j + 1 →
    ∀ y ∈ J.edgeSegment j, 3 * trim < dist (J.vertex i) y
  tube_isolation : ∀ i : ZMod J.n,
    J.edgeTube i trim width ∩ J.carrier ⊆ J.edgeSegment i

theorem exists_stripScales : Nonempty J.StripScales := by
  obtain ⟨trim, htrim, hedge, -, hvertex⟩ := J.exists_featureRadius
  have hlen4 : ∀ i : ZMod J.n, 4 * trim < J.edgeLength i := by
    intro i
    simpa only [edgeLength, outgoingVector, dist_eq_norm, norm_sub_rev] using
      lt_trans (by linarith : 4 * trim < 12 * trim) (hedge i)
  obtain ⟨width, hwidth, hwidthtrim, htube⟩ := J.exists_edgeTube_width htrim hlen4
  refine ⟨⟨trim, width, htrim, hwidth, hwidthtrim, ?_, ?_, htube⟩⟩
  · intro i
    simpa only [edgeLength, outgoingVector, dist_eq_norm, norm_sub_rev] using hedge i
  · intro i j hij hprev y hy
    exact (by linarith : 3 * trim < 12 * trim).trans (hvertex i j hij hprev y hy)

/-- The forward vertex sectors and positive edge rectangles. -/
noncomputable def stripForwardPieces (S : J.StripScales) : Set Plane :=
  (⋃ i : ZMod J.n, J.vertexForwardSector i (3 * S.trim)) ∪
    ⋃ i : ZMod J.n, J.edgePositiveSide i S.trim S.width

/-- The backward vertex sectors and negative edge rectangles. -/
noncomputable def stripBackwardPieces (S : J.StripScales) : Set Plane :=
  (⋃ i : ZMod J.n, J.vertexBackwardSector i (3 * S.trim)) ∪
    ⋃ i : ZMod J.n, J.edgeNegativeSide i S.trim S.width

/-- The punctured explicit strip is exactly the union of all its local forward and backward
pieces. -/
theorem polygonStrip_diff_carrier_eq_pieces (S : J.StripScales) :
    J.polygonStrip S.trim S.width \ J.carrier =
      J.stripForwardPieces S ∪ J.stripBackwardPieces S := by
  ext x
  constructor
  · rintro ⟨hxstrip, hxcarrier⟩
    rcases hxstrip with hvertex | hedge
    · rcases Set.mem_iUnion.mp hvertex with ⟨i, hball⟩
      have hsep : ∀ a b : ZMod J.n, a ≠ b → a ≠ b + 1 →
          ∀ y ∈ J.edgeSegment b, 3 * S.trim < dist (J.vertex a) y :=
        S.vertex_isolation
      have hlen : ∀ a : ZMod J.n,
          3 * S.trim < dist (J.vertex a) (J.vertex (a + 1)) := by
        intro a
        rw [dist_eq_norm, norm_sub_rev]
        have hlong := S.edge_long a
        simpa only [edgeLength, outgoingVector] using
          lt_trans (by linarith [S.trim_pos] : 3 * S.trim < 12 * S.trim) hlong
      have hxlocal : x ∈ J.vertexForwardSector i (3 * S.trim) ∪
          J.vertexBackwardSector i (3 * S.trim) := by
        rw [← J.ball_diff_carrier_eq_vertexSectors hsep hlen i]
        exact ⟨hball, hxcarrier⟩
      rcases hxlocal with hx | hx
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, hx⟩))
      · exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, hx⟩))
    · rcases Set.mem_iUnion.mp hedge with ⟨i, htube⟩
      have hxlocal : x ∈ J.edgePositiveSide i S.trim S.width ∪
          J.edgeNegativeSide i S.trim S.width := by
        rw [← J.edgeTube_diff_carrier_eq_sides i S.trim_pos S.width_pos
          (S.tube_isolation i)]
        exact ⟨htube, hxcarrier⟩
      rcases hxlocal with hx | hx
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
      · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  · rintro (hx | hx)
    · rcases hx with hx | hx
      · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        have hsub := J.vertexForwardSector_subset_ball_diff_carrier
          S.vertex_isolation i hx
        exact ⟨Or.inl (Set.mem_iUnion.mpr ⟨i, hsub.1⟩), hsub.2⟩
      · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        have hsub := J.edgePositiveSide_subset_edgeTube i S.width_pos hx
        have hoff : x ∉ J.carrier := by
          intro hcarrier
          have hedge := S.tube_isolation i ⟨hsub, hcarrier⟩
          linarith [hx.2.2.1, J.edgeCoordinate_im_eq_zero_of_mem_edgeSegment i hedge]
        exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, hsub⟩), hoff⟩
    · rcases hx with hx | hx
      · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        have hsub := J.vertexBackwardSector_subset_ball_diff_carrier
          S.vertex_isolation i hx
        exact ⟨Or.inl (Set.mem_iUnion.mpr ⟨i, hsub.1⟩), hsub.2⟩
      · rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
        have hsub := J.edgeNegativeSide_subset_edgeTube i S.width_pos hx
        have hoff : x ∉ J.carrier := by
          intro hcarrier
          have hedge := S.tube_isolation i ⟨hsub, hcarrier⟩
          linarith [hx.2.2.2, J.edgeCoordinate_im_eq_zero_of_mem_edgeSegment i hedge]
        exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, hsub⟩), hoff⟩

/-- A single sufficiently small positive angle gives overlap points for both sides of an edge at
both endpoint vertex sectors. -/
theorem StripScales.exists_edgeOverlapAngle (S : J.StripScales) (i : ZMod J.n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
      θ < (J.outgoingDirection i).angleDiff (J.incomingRayDirection i) ∧
      θ < (J.incomingRayDirection i).angleDiff (J.outgoingDirection i) ∧
      θ < (J.outgoingDirection (i + 1)).angleDiff (J.incomingRayDirection (i + 1)) ∧
      θ < (J.incomingRayDirection (i + 1)).angleDiff (J.outgoingDirection (i + 1)) ∧
      2 * S.trim < ((5 * S.trim / 2 : ℝ) * (Circle.exp θ : ℂ)).re ∧
      ((5 * S.trim / 2 : ℝ) * (Circle.exp θ : ℂ)).re <
        J.edgeLength i - 2 * S.trim ∧
      |((5 * S.trim / 2 : ℝ) * (Circle.exp θ : ℂ)).im| < S.width := by
  let ρ : ℝ := 5 * S.trim / 2
  let g : ℝ → ℂ := fun θ => (ρ : ℂ) * (Circle.exp θ : ℂ)
  let U : Set ℝ := {θ | 2 * S.trim < (g θ).re ∧
    (g θ).re < J.edgeLength i - 2 * S.trim ∧ |(g θ).im| < S.width}
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hgre : Continuous fun θ => (g θ).re := Complex.continuous_re.comp hg
  have hgimabs : Continuous fun θ => |(g θ).im| :=
    (Complex.continuous_im.comp hg).abs
  have hUopen : IsOpen U := by
    exact (isOpen_lt continuous_const hgre).inter
      ((isOpen_lt hgre continuous_const).inter (isOpen_lt hgimabs continuous_const))
  have hUzero : 0 ∈ U := by
    have hlong := S.edge_long i
    dsimp [U, g]
    simp only [zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_re,
      Complex.ofReal_im, abs_zero]
    constructor
    · dsimp [ρ]
      linarith [S.trim_pos]
    constructor
    · dsimp [ρ]
      linarith [S.trim_pos]
    · exact S.width_pos
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hUzero)
  let d₁ := (J.outgoingDirection i).angleDiff (J.incomingRayDirection i)
  let d₂ := (J.incomingRayDirection i).angleDiff (J.outgoingDirection i)
  let d₃ := (J.outgoingDirection (i + 1)).angleDiff (J.incomingRayDirection (i + 1))
  let d₄ := (J.incomingRayDirection (i + 1)).angleDiff (J.outgoingDirection (i + 1))
  have hd₁ : 0 < d₁ := Circle.angleDiff_pos (J.outgoingDirection_ne_incomingRayDirection i)
  have hd₂ : 0 < d₂ := Circle.angleDiff_pos (J.outgoingDirection_ne_incomingRayDirection i).symm
  have hd₃ : 0 < d₃ :=
    Circle.angleDiff_pos (J.outgoingDirection_ne_incomingRayDirection (i + 1))
  have hd₄ : 0 < d₄ :=
    Circle.angleDiff_pos (J.outgoingDirection_ne_incomingRayDirection (i + 1)).symm
  let m := min ε (min Real.pi (min d₁ (min d₂ (min d₃ d₄))))
  have hm : 0 < m := by unfold m; positivity
  let θ := m / 2
  have hθ : 0 < θ := by unfold θ; positivity
  have hθε : θ < ε := by
    have hmle : m ≤ ε := by unfold m; exact min_le_left _ _
    unfold θ
    linarith
  have hθU : θ ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hθ]
    exact hθε)
  refine ⟨θ, hθ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : m ≤ Real.pi := by
      exact (min_le_right ε _).trans (min_le_left _ _)
    unfold θ
    linarith [Real.pi_pos]
  · have : m ≤ d₁ := by
      exact (min_le_right ε _).trans ((min_le_right Real.pi _).trans (min_le_left _ _))
    have h : θ < d₁ := by unfold θ; linarith
    simpa only [d₁] using h
  · have : m ≤ d₂ := by
      exact (min_le_right ε _).trans ((min_le_right Real.pi _).trans
        ((min_le_right d₁ _).trans (min_le_left _ _)))
    have h : θ < d₂ := by unfold θ; linarith
    simpa only [d₂] using h
  · have : m ≤ d₃ := by
      exact (min_le_right ε _).trans ((min_le_right Real.pi _).trans
        ((min_le_right d₁ _).trans ((min_le_right d₂ _).trans (min_le_left _ _))))
    have h : θ < d₃ := by unfold θ; linarith
    simpa only [d₃] using h
  · have : m ≤ d₄ := by
      exact (min_le_right ε _).trans ((min_le_right Real.pi _).trans
        ((min_le_right d₁ _).trans ((min_le_right d₂ _).trans
          (min_le_right d₃ d₄))))
    have h : θ < d₄ := by unfold θ; linarith
    simpa only [d₄] using h
  · simpa only [U, g, ρ, Set.mem_ofPred_eq] using hθU

/-- The two side rectangles at the initial endpoint of an edge overlap the corresponding
vertex sectors. -/
theorem StripScales.initial_edge_side_intersections (S : J.StripScales) (i : ZMod J.n) :
    (J.vertexForwardSector i (3 * S.trim) ∩
        J.edgePositiveSide i S.trim S.width).Nonempty ∧
      (J.vertexBackwardSector i (3 * S.trim) ∩
        J.edgeNegativeSide i S.trim S.width).Nonempty := by
  obtain ⟨θ, hθ, hθpi, hδforward, hδbackward, -, -, hre0, hre1, himabs⟩ :=
    S.exists_edgeOverlapAngle J i
  let ρ : ℝ := 5 * S.trim / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [S.trim_pos]
  have hρbound : ρ < 3 * S.trim := by dsimp [ρ]; linarith [S.trim_pos]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθpi
  let zpos : ℂ := (ρ : ℂ) * (Circle.exp θ : ℂ)
  let zneg : ℂ := (ρ : ℂ) * (Circle.exp (-θ) : ℂ)
  have hzposim : 0 < zpos.im := by
    rw [show zpos.im = ρ * Real.sin θ by simp only [zpos, ofReal_mul_circle_exp_im]]
    positivity
  have hznegim : zneg.im < 0 := by
    rw [show zneg.im = ρ * Real.sin (-θ) by
      simp only [zneg, ofReal_mul_circle_exp_im], Real.sin_neg]
    nlinarith [mul_pos hρ hsin]
  have hznegre : zneg.re = zpos.re := by
    simp only [zneg, zpos, ofReal_mul_circle_exp_re, Real.cos_neg]
  have hznegabsim : |zneg.im| = |zpos.im| := by
    simp only [zneg, zpos, ofReal_mul_circle_exp_im, Real.sin_neg, mul_neg, abs_neg]
  have hzposre0 : 2 * S.trim < zpos.re := by simpa only [zpos, ρ] using hre0
  have hzposre1 : zpos.re < J.edgeLength i - 2 * S.trim := by
    simpa only [zpos, ρ] using hre1
  have hzposabsim : |zpos.im| < S.width := by simpa only [zpos, ρ] using himabs
  have hznegabsimlt : |zneg.im| < S.width := by rw [hznegabsim]; exact hzposabsim
  constructor
  · refine ⟨J.edgeCoordinateInv i zpos, ?_, ?_⟩
    · refine ⟨zpos * (J.outgoingDirection i : ℂ), ?_, rfl⟩
      change ((ρ : ℂ) * (Circle.exp θ : ℂ)) * (J.outgoingDirection i : ℂ) ∈ _
      exact pos_rotation_mem_openAngularSector hθ hδforward hρ hρbound
    · change 2 * S.trim < (J.edgeCoordinate i (J.edgeCoordinateInv i zpos)).re ∧
        (J.edgeCoordinate i (J.edgeCoordinateInv i zpos)).re <
          J.edgeLength i - 2 * S.trim ∧
        0 < (J.edgeCoordinate i (J.edgeCoordinateInv i zpos)).im ∧
        (J.edgeCoordinate i (J.edgeCoordinateInv i zpos)).im < S.width
      simp only [J.edgeCoordinate_edgeCoordinateInv]
      refine ⟨hzposre0, hzposre1, hzposim, (abs_lt.mp hzposabsim).2⟩
  · refine ⟨J.edgeCoordinateInv i zneg, ?_, ?_⟩
    · refine ⟨zneg * (J.outgoingDirection i : ℂ), ?_, rfl⟩
      change ((ρ : ℂ) * (Circle.exp (-θ) : ℂ)) * (J.outgoingDirection i : ℂ) ∈ _
      exact neg_rotation_mem_openAngularSector hθ hδbackward hρ hρbound
    · change 2 * S.trim < (J.edgeCoordinate i (J.edgeCoordinateInv i zneg)).re ∧
        (J.edgeCoordinate i (J.edgeCoordinateInv i zneg)).re <
          J.edgeLength i - 2 * S.trim ∧
        -S.width < (J.edgeCoordinate i (J.edgeCoordinateInv i zneg)).im ∧
        (J.edgeCoordinate i (J.edgeCoordinateInv i zneg)).im < 0
      simp only [J.edgeCoordinate_edgeCoordinateInv]
      rw [hznegre]
      exact ⟨hzposre0, hzposre1, (abs_lt.mp hznegabsimlt).1, hznegim⟩

/-- Coordinates measured from an edge's terminal endpoint run in the opposite direction. -/
@[simp] theorem edgeCoordinate_terminal_ray (i : ZMod J.n) (z : ℂ) :
    J.edgeCoordinate i (J.vertex (i + 1) + planeComplexEquiv.symm
      (z * (J.incomingRayDirection (i + 1) : ℂ))) = (J.edgeLength i : ℂ) - z := by
  rw [edgeCoordinate]
  have hsub : J.vertex (i + 1) + planeComplexEquiv.symm
      (z * (J.incomingRayDirection (i + 1) : ℂ)) - J.vertex i =
      J.outgoingVector i + planeComplexEquiv.symm
        (z * (J.incomingRayDirection (i + 1) : ℂ)) := by
    rw [outgoingVector]
    abel
  rw [hsub, map_add, planeComplexEquiv.apply_symm_apply,
    J.coe_incomingRayDirection_add_one]
  have hout : planeComplexEquiv (J.outgoingVector i) =
      (J.edgeLength i : ℂ) * (J.outgoingDirection i : ℂ) := by
    rw [edgeLength, outgoingDirection, ← norm_planeComplexEquiv]
    exact (norm_mul_complexDirection _ _).symm
  rw [hout]
  field_simp [(J.outgoingDirection i).coe_ne_zero]
  ring

/-- The two side rectangles at the terminal endpoint of an edge overlap the corresponding
vertex sectors. -/
theorem StripScales.terminal_edge_side_intersections (S : J.StripScales) (i : ZMod J.n) :
    (J.vertexForwardSector (i + 1) (3 * S.trim) ∩
        J.edgePositiveSide i S.trim S.width).Nonempty ∧
      (J.vertexBackwardSector (i + 1) (3 * S.trim) ∩
        J.edgeNegativeSide i S.trim S.width).Nonempty := by
  obtain ⟨θ, hθ, hθpi, -, -, hδforward, hδbackward, hre0, hre1, himabs⟩ :=
    S.exists_edgeOverlapAngle J i
  let ρ : ℝ := 5 * S.trim / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [S.trim_pos]
  have hρbound : ρ < 3 * S.trim := by dsimp [ρ]; linarith [S.trim_pos]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθpi
  let zpos : ℂ := (ρ : ℂ) * (Circle.exp θ : ℂ)
  let zneg : ℂ := (ρ : ℂ) * (Circle.exp (-θ) : ℂ)
  have hzposim : 0 < zpos.im := by
    rw [show zpos.im = ρ * Real.sin θ by simp only [zpos, ofReal_mul_circle_exp_im]]
    positivity
  have hznegim : zneg.im < 0 := by
    rw [show zneg.im = ρ * Real.sin (-θ) by
      simp only [zneg, ofReal_mul_circle_exp_im], Real.sin_neg]
    nlinarith [mul_pos hρ hsin]
  have hznegre : zneg.re = zpos.re := by
    simp only [zneg, zpos, ofReal_mul_circle_exp_re, Real.cos_neg]
  have hznegabsim : |zneg.im| = |zpos.im| := by
    simp only [zneg, zpos, ofReal_mul_circle_exp_im, Real.sin_neg, mul_neg, abs_neg]
  have hzposre0 : 2 * S.trim < zpos.re := by simpa only [zpos, ρ] using hre0
  have hzposre1 : zpos.re < J.edgeLength i - 2 * S.trim := by
    simpa only [zpos, ρ] using hre1
  have hzposabsim : |zpos.im| < S.width := by simpa only [zpos, ρ] using himabs
  have hznegabsimlt : |zneg.im| < S.width := by rw [hznegabsim]; exact hzposabsim
  constructor
  · refine ⟨J.vertex (i + 1) + planeComplexEquiv.symm
        (zneg * (J.incomingRayDirection (i + 1) : ℂ)), ?_, ?_⟩
    · refine ⟨zneg * (J.incomingRayDirection (i + 1) : ℂ), ?_, rfl⟩
      change ((ρ : ℂ) * (Circle.exp (-θ) : ℂ)) *
        (J.incomingRayDirection (i + 1) : ℂ) ∈ _
      exact neg_rotation_mem_openAngularSector hθ hδforward hρ hρbound
    · change 2 * S.trim < (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zneg * (J.incomingRayDirection (i + 1) : ℂ)))).re ∧
        (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zneg * (J.incomingRayDirection (i + 1) : ℂ)))).re <
            J.edgeLength i - 2 * S.trim ∧
        0 < (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zneg * (J.incomingRayDirection (i + 1) : ℂ)))).im ∧
        (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zneg * (J.incomingRayDirection (i + 1) : ℂ)))).im < S.width
      rw [J.edgeCoordinate_terminal_ray]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        zero_sub]
      rw [hznegre]
      refine ⟨by linarith, by linarith, neg_pos.mpr hznegim, ?_⟩
      rw [← abs_of_neg hznegim]
      exact hznegabsimlt
  · refine ⟨J.vertex (i + 1) + planeComplexEquiv.symm
        (zpos * (J.incomingRayDirection (i + 1) : ℂ)), ?_, ?_⟩
    · refine ⟨zpos * (J.incomingRayDirection (i + 1) : ℂ), ?_, rfl⟩
      change ((ρ : ℂ) * (Circle.exp θ : ℂ)) *
        (J.incomingRayDirection (i + 1) : ℂ) ∈ _
      exact pos_rotation_mem_openAngularSector hθ hδbackward hρ hρbound
    · change 2 * S.trim < (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zpos * (J.incomingRayDirection (i + 1) : ℂ)))).re ∧
        (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zpos * (J.incomingRayDirection (i + 1) : ℂ)))).re <
            J.edgeLength i - 2 * S.trim ∧
        -S.width < (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zpos * (J.incomingRayDirection (i + 1) : ℂ)))).im ∧
        (J.edgeCoordinate i (J.vertex (i + 1) +
          planeComplexEquiv.symm (zpos * (J.incomingRayDirection (i + 1) : ℂ)))).im < 0
      rw [J.edgeCoordinate_terminal_ray]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
        zero_sub]
      refine ⟨by linarith, by linarith, ?_, neg_neg_of_pos hzposim⟩
      have := (abs_lt.mp hzposabsim).2
      linarith

/-- A graph-connected union of path-connected sets is path-connected.  This is the path analogue
of `IsConnected.iUnion_of_reflTransGen`. -/
theorem isPathConnected_iUnion_of_reflTransGen {X ι : Type*} [TopologicalSpace X] [Nonempty ι]
    {s : ι → Set X} (hs : ∀ i, IsPathConnected (s i))
    (hgraph : ∀ i j, Relation.ReflTransGen
      (fun a b : ι => (s a ∩ s b).Nonempty) i j) :
    IsPathConnected (⋃ i, s i) := by
  have hchain : ∀ i j, Relation.ReflTransGen
      (fun a b : ι => (s a ∩ s b).Nonempty) i j →
      ∃ p : Set ι, i ∈ p ∧ j ∈ p ∧ IsPathConnected (⋃ k ∈ p, s k) := by
    intro i j hij
    induction hij with
    | refl =>
        refine ⟨{i}, Set.mem_singleton i, Set.mem_singleton i, ?_⟩
        simpa using hs i
    | @tail j k _ hjk ih =>
        obtain ⟨p, hip, hjp, hp⟩ := ih
        refine ⟨insert k p, Set.mem_insert_of_mem k hip, Set.mem_insert k p, ?_⟩
        rw [Set.biUnion_insert]
        refine (hs k).union hp ?_
        exact hjk.mono fun x hx =>
          ⟨hx.2, Set.mem_iUnion₂.mpr ⟨j, hjp, hx.1⟩⟩
  rw [isPathConnected_iff]
  constructor
  · exact Nonempty.elim ‹Nonempty ι› fun i =>
      ⟨(hs i).nonempty.some, Set.mem_iUnion.mpr ⟨i, (hs i).nonempty.some_mem⟩⟩
  · intro x hx y hy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    obtain ⟨p, hip, hjp, hp⟩ := hchain i j (hgraph i j)
    exact (hp.joinedIn x (Set.mem_iUnion₂.mpr ⟨i, hip, hxi⟩)
      y (Set.mem_iUnion₂.mpr ⟨j, hjp, hyj⟩)).mono
        (Set.iUnion₂_subset fun k _ => Set.subset_iUnion s k)

private noncomputable def forwardEdgePatch (S : J.StripScales) (i : ZMod J.n) : Set Plane :=
  J.vertexForwardSector i (3 * S.trim) ∪ J.edgePositiveSide i S.trim S.width

private noncomputable def backwardEdgePatch (S : J.StripScales) (i : ZMod J.n) : Set Plane :=
  J.vertexBackwardSector i (3 * S.trim) ∪ J.edgeNegativeSide i S.trim S.width

theorem StripScales.isPathConnected_stripForwardPieces (S : J.StripScales) :
    IsPathConnected (J.stripForwardPieces S) := by
  have hpatch : ∀ i : ZMod J.n, IsPathConnected (J.forwardEdgePatch S i) := by
    intro i
    exact (J.isPathConnected_vertexForwardSector i (by linarith [S.trim_pos])).union
      (J.isPathConnected_edgePositiveSide i S.width_pos (by
        linarith [S.edge_long i, S.trim_pos]))
      (S.initial_edge_side_intersections J i).1
  have hstep : ∀ i : ZMod J.n,
      (J.forwardEdgePatch S i ∩ J.forwardEdgePatch S (i + 1)).Nonempty := by
    intro i
    obtain ⟨x, hxvertex, hxedge⟩ := (S.terminal_edge_side_intersections J i).1
    exact ⟨x, Or.inr hxedge, Or.inl hxvertex⟩
  have hconnected : IsPathConnected (⋃ i : ZMod J.n, J.forwardEdgePatch S i) := by
    apply isPathConnected_iUnion_of_reflTransGen hpatch
    intro i j
    have hwalk : ∀ m : ℕ, Relation.ReflTransGen
        (fun a b : ZMod J.n => (J.forwardEdgePatch S a ∩ J.forwardEdgePatch S b).Nonempty)
        i (i + (m : ZMod J.n)) := by
      intro m
      induction m with
      | zero => simpa using Relation.ReflTransGen.refl
      | succ m ih =>
          apply Relation.ReflTransGen.tail ih
          rw [Nat.cast_succ]
          convert hstep (i + (m : ZMod J.n)) using 1; ring_nf
    convert hwalk (j - i).val using 1
    rw [ZMod.natCast_zmod_val]
    ring
  have heq : (⋃ i : ZMod J.n, J.forwardEdgePatch S i) = J.stripForwardPieces S := by
    ext x
    simp only [forwardEdgePatch, stripForwardPieces, Set.mem_iUnion, Set.mem_union]
    aesop
  rwa [heq] at hconnected

theorem StripScales.isPathConnected_stripBackwardPieces (S : J.StripScales) :
    IsPathConnected (J.stripBackwardPieces S) := by
  have hpatch : ∀ i : ZMod J.n, IsPathConnected (J.backwardEdgePatch S i) := by
    intro i
    exact (J.isPathConnected_vertexBackwardSector i (by linarith [S.trim_pos])).union
      (J.isPathConnected_edgeNegativeSide i S.width_pos (by
        linarith [S.edge_long i, S.trim_pos]))
      (S.initial_edge_side_intersections J i).2
  have hstep : ∀ i : ZMod J.n,
      (J.backwardEdgePatch S i ∩ J.backwardEdgePatch S (i + 1)).Nonempty := by
    intro i
    obtain ⟨x, hxvertex, hxedge⟩ := (S.terminal_edge_side_intersections J i).2
    exact ⟨x, Or.inr hxedge, Or.inl hxvertex⟩
  have hconnected : IsPathConnected (⋃ i : ZMod J.n, J.backwardEdgePatch S i) := by
    apply isPathConnected_iUnion_of_reflTransGen hpatch
    intro i j
    have hwalk : ∀ m : ℕ, Relation.ReflTransGen
        (fun a b : ZMod J.n =>
          (J.backwardEdgePatch S a ∩ J.backwardEdgePatch S b).Nonempty)
        i (i + (m : ZMod J.n)) := by
      intro m
      induction m with
      | zero => simpa using Relation.ReflTransGen.refl
      | succ m ih =>
          apply Relation.ReflTransGen.tail ih
          rw [Nat.cast_succ]
          convert hstep (i + (m : ZMod J.n)) using 1; ring_nf
    convert hwalk (j - i).val using 1
    rw [ZMod.natCast_zmod_val]
    ring
  have heq : (⋃ i : ZMod J.n, J.backwardEdgePatch S i) = J.stripBackwardPieces S := by
    ext x
    simp only [backwardEdgePatch, stripBackwardPieces, Set.mem_iUnion, Set.mem_union]
    aesop
  rwa [heq] at hconnected

/-- Every point of the polygon is approached from both of the explicit strip bands. -/
theorem StripScales.carrier_subset_closure_stripPieces (S : J.StripScales) :
    J.carrier ⊆ closure (J.stripForwardPieces S) ∩ closure (J.stripBackwardPieces S) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hcoord⟩ := J.edgeCoordinate_mem_real_Icc i hxi
  have hxinv : J.edgeCoordinateInv i (s : ℂ) = x := by
    rw [← hcoord, J.edgeCoordinateInv_edgeCoordinate]
  have hforwardVertex : ∀ k : ZMod J.n,
      J.vertexForwardSector k (3 * S.trim) ⊆ J.stripForwardPieces S := by
    intro k y hy
    exact Or.inl (Set.mem_iUnion.mpr ⟨k, hy⟩)
  have hbackwardVertex : ∀ k : ZMod J.n,
      J.vertexBackwardSector k (3 * S.trim) ⊆ J.stripBackwardPieces S := by
    intro k y hy
    exact Or.inl (Set.mem_iUnion.mpr ⟨k, hy⟩)
  have hforwardEdge : J.edgePositiveSide i S.trim S.width ⊆ J.stripForwardPieces S := by
    intro y hy
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hy⟩)
  have hbackwardEdge : J.edgeNegativeSide i S.trim S.width ⊆ J.stripBackwardPieces S := by
    intro y hy
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hy⟩)
  by_cases hsource : s ≤ 3 * S.trim
  · have hlocal := J.outgoingRay_mem_closure_vertexSectors i
      (by linarith [S.trim_pos] : 0 < 3 * S.trim) ⟨hs.1, hsource⟩
    have hlocal' : x ∈ closure (J.vertexForwardSector i (3 * S.trim)) ∩
        closure (J.vertexBackwardSector i (3 * S.trim)) := by
      rw [← hxinv]
      simpa only [edgeCoordinateInv] using hlocal
    exact ⟨closure_mono (hforwardVertex i) hlocal'.1,
      closure_mono (hbackwardVertex i) hlocal'.2⟩
  by_cases hterminal : J.edgeLength i - s ≤ 3 * S.trim
  · let y : Plane := J.vertex (i + 1) + planeComplexEquiv.symm
        (((J.edgeLength i - s : ℝ) : ℂ) * (J.incomingRayDirection (i + 1) : ℂ))
    have hycoord : J.edgeCoordinate i y = (s : ℂ) := by
      dsimp [y]
      rw [J.edgeCoordinate_terminal_ray]
      norm_num
    have hy : y = x := by
      calc
        y = J.edgeCoordinateInv i (J.edgeCoordinate i y) :=
          (J.edgeCoordinateInv_edgeCoordinate i y).symm
        _ = J.edgeCoordinateInv i (s : ℂ) := by rw [hycoord]
        _ = x := hxinv
    have hradius : J.edgeLength i - s ∈ Set.Icc (0 : ℝ) (3 * S.trim) :=
      ⟨sub_nonneg.mpr hs.2, hterminal⟩
    have hlocal := J.incomingRay_mem_closure_vertexSectors (i + 1)
      (by linarith [S.trim_pos] : 0 < 3 * S.trim) hradius
    have hlocal' : x ∈ closure (J.vertexForwardSector (i + 1) (3 * S.trim)) ∩
        closure (J.vertexBackwardSector (i + 1) (3 * S.trim)) := by
      rw [← hy]
      exact hlocal
    exact ⟨closure_mono (hforwardVertex (i + 1)) hlocal'.1,
      closure_mono (hbackwardVertex (i + 1)) hlocal'.2⟩
  · have hscentral : s ∈ Set.Icc (2 * S.trim) (J.edgeLength i - 2 * S.trim) := by
      constructor <;> linarith [S.trim_pos]
    have hlen : 4 * S.trim < J.edgeLength i := by
      linarith [S.edge_long i, S.trim_pos]
    have hpos := J.edgeAxis_mem_closure_positiveSide i S.width_pos hlen hscentral
    have hneg := J.edgeAxis_mem_closure_negativeSide i S.width_pos hlen hscentral
    rw [hxinv] at hpos hneg
    exact ⟨closure_mono hforwardEdge hpos, closure_mono hbackwardEdge hneg⟩

theorem StripScales.carrier_subset_closure_stripForwardPieces (S : J.StripScales) :
    J.carrier ⊆ closure (J.stripForwardPieces S) := fun _ hx =>
  (S.carrier_subset_closure_stripPieces J hx).1

theorem StripScales.carrier_subset_closure_stripBackwardPieces (S : J.StripScales) :
    J.carrier ⊆ closure (J.stripBackwardPieces S) := fun _ hx =>
  (S.carrier_subset_closure_stripPieces J hx).2

/-- A genuine segment in the plane has empty planar interior. -/
theorem interior_edgeSegment (i : ZMod J.n) : interior (J.edgeSegment i) = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hinterior
  have hspan : affineSpan ℝ (J.edgeSegment i) = ⊤ :=
    ((convex_segment (J.vertex i) (J.vertex (i + 1))).interior_nonempty_iff_affineSpan_eq_top).mp
      hinterior
  have hpair : affineSpan ℝ ({J.vertex i, J.vertex (i + 1)} : Set Plane) = ⊤ := by
    rw [← affineSpan_convexHull, convexHull_pair]
    exact hspan
  set dx : ℝ := (J.vertex (i + 1)) 0 - (J.vertex i) 0 with hdx
  set dy : ℝ := (J.vertex (i + 1)) 1 - (J.vertex i) 1 with hdy
  set q : Plane :=
    (WithLp.toLp 2 ![(J.vertex i) 0 - dy, (J.vertex i) 1 + dx] : Plane) with hq
  have hqline : q ∈ affineSpan ℝ ({J.vertex i, J.vertex (i + 1)} : Set Plane) := by
    rw [hpair]
    trivial
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hqline
  obtain ⟨t, ht⟩ := hqline
  have ht0 := congrArg (fun p : Plane => p 0) ht
  have ht1 := congrArg (fun p : Plane => p 1) ht
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at ht0 ht1
  change t * ((J.vertex (i + 1)) 0 - (J.vertex i) 0) + (J.vertex i) 0 =
      (J.vertex i) 0 - dy at ht0
  change t * ((J.vertex (i + 1)) 1 - (J.vertex i) 1) + (J.vertex i) 1 =
      (J.vertex i) 1 + dx at ht1
  have ht0' := congrArg (fun x : ℝ => x * dy) ht0
  have ht1' := congrArg (fun x : ℝ => x * dx) ht1
  rw [hdy] at ht0 ht0'
  rw [hdx] at ht1 ht1'
  have hdx0 : dx = 0 := by
    rw [hdx]
    nlinarith [sq_nonneg ((J.vertex (i + 1)) 0 - (J.vertex i) 0),
      sq_nonneg ((J.vertex (i + 1)) 1 - (J.vertex i) 1)]
  have hdy0 : dy = 0 := by
    rw [hdy]
    nlinarith [sq_nonneg ((J.vertex (i + 1)) 0 - (J.vertex i) 0),
      sq_nonneg ((J.vertex (i + 1)) 1 - (J.vertex i) 1)]
  apply J.adjacent_ne i
  ext j
  fin_cases j
  · change (J.vertex i) 0 = (J.vertex (i + 1)) 0
    rw [hdx] at hdx0
    linarith
  · change (J.vertex i) 1 = (J.vertex (i + 1)) 1
    rw [hdy] at hdy0
    linarith

/-- A finite polygonal carrier has empty interior in the plane. -/
theorem interior_carrier : interior J.carrier = ∅ := by
  classical
  have hfinite : ∀ s : Finset (ZMod J.n),
      interior (⋃ i ∈ s, J.edgeSegment i) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.set_biUnion_insert]
        rw [interior_union_isClosed_of_interior_empty (J.isClosed_edgeSegment i) ih,
          J.interior_edgeSegment i]
  rw [carrier]
  simpa using hfinite Finset.univ

/-- The carrier of a polygon is connected: it is a cyclic union of connected segments, with each
segment meeting the next one at their common vertex. -/
theorem isConnected_carrier : IsConnected J.carrier := by
  have hedge : ∀ i : ZMod J.n, IsConnected (J.edgeSegment i) := by
    intro i
    exact (convex_segment (J.vertex i) (J.vertex (i + 1))).isConnected
      ⟨J.vertex i, left_mem_segment ℝ _ _⟩
  have hstep : ∀ i : ZMod J.n,
      (J.edgeSegment i ∩ J.edgeSegment (i + 1)).Nonempty := by
    intro i
    refine ⟨J.vertex (i + 1), right_mem_segment ℝ _ _, ?_⟩
    exact left_mem_segment ℝ _ _
  rw [carrier]
  apply IsConnected.iUnion_of_reflTransGen hedge
  intro i j
  have hwalk : ∀ m : ℕ,
      Relation.ReflTransGen
        (fun a b : ZMod J.n => (J.edgeSegment a ∩ J.edgeSegment b).Nonempty)
        i (i + (m : ZMod J.n)) := by
    intro m
    induction m with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ m ih =>
        apply Relation.ReflTransGen.tail ih
        rw [Nat.cast_succ]
        convert hstep (i + (m : ZMod J.n)) using 1
        all_goals ring_nf
  convert hwalk (j - i).val using 1
  rw [ZMod.natCast_zmod_val]
  ring

/-- Every point off the polygon can be joined by a single polygon-avoiding segment to any open
neighborhood of the polygon.  This is the "reach the strip" part of Moise Ch. 2, Thm. 1,
Lemma 1. -/
theorem exists_segment_to_open_neighborhood {N : Set Plane} (hN : IsOpen N)
    (hcarrierN : J.carrier ⊆ N) {P : Plane} (hP : P ∉ J.carrier) :
    ∃ Q ∈ N \ J.carrier, segment ℝ P Q ⊆ J.carrierᶜ := by
  obtain ⟨z, hzcarrier, -, hvis⟩ :=
    J.isClosed_carrier.exists_wbtw_isVisible (J.vertex_mem_carrier 0) P
  have hPz : P ≠ z := fun h => hP (h ▸ hzcarrier)
  have hzclosure : z ∈ closure (openSegment ℝ P z) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ P z)
  obtain ⟨Q, hQN, hQopen⟩ := (mem_closure_iff.mp hzclosure) N hN (hcarrierN hzcarrier)
  have hQstrict : Sbtw ℝ P Q z := by
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    constructor
    · rwa [← openSegment_eq_image_lineMap]
    · exact hPz
  have hQcarrier : Q ∉ J.carrier := fun hQ => hvis hQ hQstrict
  refine ⟨Q, ⟨hQN, hQcarrier⟩, ?_⟩
  intro X hX hXcarrier
  rcases eq_or_ne X P with rfl | hXP
  · exact hP hXcarrier
  rcases eq_or_ne X Q with rfl | hXQ
  · exact hQcarrier hXcarrier
  have hXstrict : Sbtw ℝ P X Q :=
    ⟨mem_segment_iff_wbtw.mp hX, hXP, hXQ⟩
  exact hvis hXcarrier (hQstrict.trans_left hXstrict)

/-! ### The crossing index (Moise Ch. 2, proof of Thm. 1, Lemma 2)

The parity of the number of polygon edges crossed by the leftward horizontal ray from a point.
We use the half-open edge convention (an edge is crossed when the point's height lies in the
half-open interval between the endpoint heights): this replaces Moise's "slightly perturbed
line" device, needs no general-position choice of axes, and makes the index everywhere defined.
Horizontal edges are never crossed. -/

/-- The x-coordinate at height `y` of the line through `v` and `w` (meaningful when the heights
of `v` and `w` differ, which the crossing condition guarantees at use sites). -/
noncomputable def crossingX (v w : Plane) (y : ℝ) : ℝ :=
  v 0 + (y - v 1) / (w 1 - v 1) * (w 0 - v 0)

/-- The leftward horizontal ray from `P` crosses edge `i`, with the half-open height
convention. -/
def EdgeCrossed (i : ZMod J.n) (P : Plane) : Prop :=
  ((J.vertex i) 1 ≤ P 1 ∧ P 1 < (J.vertex (i + 1)) 1 ∨
    (J.vertex (i + 1)) 1 ≤ P 1 ∧ P 1 < (J.vertex i) 1) ∧
  crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0

open scoped Classical in
/-- The Moise index of a point: the parity of the number of edges crossed by its leftward
horizontal ray. -/
noncomputable def index (P : Plane) : ℕ :=
  (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P).card % 2

theorem index_lt_two (P : Plane) : J.index P < 2 :=
  Nat.mod_lt _ (by norm_num)

/-- Points of a segment have heights between the endpoint heights. -/
theorem height_le_max_of_mem_segment {v w q : Plane} (hq : q ∈ segment ℝ v w) :
    q 1 ≤ max (v 1) (w 1) := by
  rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
  have h1 : (a • v + b • w) 1 = a * v 1 + b * w 1 := by
    simp
  rw [h1]
  calc a * v 1 + b * w 1 ≤ a * max (v 1) (w 1) + b * max (v 1) (w 1) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max (v 1) (w 1) := by rw [← add_mul, hab, one_mul]

/-- Points of a segment have heights at least the smaller endpoint height. -/
theorem min_le_height_of_mem_segment {v w q : Plane} (hq : q ∈ segment ℝ v w) :
    min (v 1) (w 1) ≤ q 1 := by
  rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
  have h1 : (a • v + b • w) 1 = a * v 1 + b * w 1 := by
    simp
  rw [h1]
  calc min (v 1) (w 1) = a * min (v 1) (w 1) + b * min (v 1) (w 1) := by
        rw [← add_mul, hab, one_mul]
    _ ≤ a * v 1 + b * w 1 := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _

/-- Points of the polygon have heights at most the maximal vertex height. -/
theorem height_le_of_mem_carrier {q : Plane} (hq : q ∈ J.carrier) :
    ∃ i : ZMod J.n, q 1 ≤ (J.vertex i) 1 := by
  rcases Set.mem_iUnion.mp hq with ⟨i, hqi⟩
  rcases le_total ((J.vertex i) 1) ((J.vertex (i + 1)) 1) with h | h
  · exact ⟨i + 1, by simpa [max_eq_right h] using height_le_max_of_mem_segment hqi⟩
  · exact ⟨i, by simpa [max_eq_left h] using height_le_max_of_mem_segment hqi⟩

/-- A point strictly above every vertex has index zero: its leftward ray crosses nothing. -/
theorem index_eq_zero_of_high {P : Plane} (hP : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1) :
    J.index P = 0 := by
  classical
  have hempty : (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i _
    rintro ⟨hy | hy, -⟩
    · exact absurd hy.2 (not_lt.mpr (hP (i + 1)).le)
    · exact absurd hy.2 (not_lt.mpr (hP i).le)
  simp [index, hempty]

/-- A point strictly above every vertex is off the polygon. -/
theorem notMem_carrier_of_high {P : Plane} (hP : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1) :
    P ∉ J.carrier := by
  intro hmem
  rcases J.height_le_of_mem_carrier hmem with ⟨i, hi⟩
  exact absurd hi (not_le.mpr (hP i))

/-- There are points off the polygon with index zero. -/
theorem exists_index_eq_zero : ∃ P : Plane, P ∉ J.carrier ∧ J.index P = 0 := by
  classical
  obtain ⟨ymax, hymax⟩ : ∃ y, ∀ i : ZMod J.n, (J.vertex i) 1 ≤ y := by
    set g : ZMod J.n → ℝ := fun i => (J.vertex i) 1 with hg
    exact ⟨(Finset.univ.image g).max' (by simp),
      fun i => Finset.le_max' _ (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))⟩
  set P : Plane := (WithLp.toLp 2 ![0, ymax + 1] : Plane) with hPdef
  have hP1 : P 1 = ymax + 1 := rfl
  have hhigh : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1 := by
    intro i
    rw [hP1]
    exact lt_of_le_of_lt (hymax i) (by linarith)
  exact ⟨P, J.notMem_carrier_of_high hhigh, J.index_eq_zero_of_high hhigh⟩

/-! #### The handshake lemma for the local-constancy casework

Near a point `P` off the polygon, the only edges whose crossing status is not locally constant
are those with exactly one endpoint at the height of `P`, that endpoint lying strictly to the
left of `P`: rising edges switch on and falling edges switch off as the query point's height
crosses `P`'s.  The index is therefore locally constant provided the number of such edges is
even, which is a double-counting argument: every vertex has two incident edges, a horizontal
partner of a left vertex is itself a left vertex (otherwise the horizontal edge would contain
`P`), and so the non-horizontal incident edges of the left vertices pair up. -/

/-- A point at the height of a horizontal segment, with abscissa between the endpoints, lies on
the segment. -/
theorem mem_segment_of_horizontal {a b P : Plane} (ha : a 1 = P 1) (hb : b 1 = P 1)
    (hax : a 0 ≤ P 0) (hxb : P 0 ≤ b 0) : P ∈ segment ℝ a b := by
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · have hPa : P = a := by
      apply plane_ext
      · exact le_antisymm (by rw [hab]; exact hxb) hax
      · exact ha.symm
    rw [hPa]
    exact left_mem_segment ℝ a b
  · set t : ℝ := (P 0 - a 0) / (b 0 - a 0) with ht
    have hden : (0 : ℝ) < b 0 - a 0 := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hden]
      linarith
    have hpt : (1 - t) • a + t • b = P := by
      apply plane_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [ht]
        field_simp
        ring
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        rw [ha, hb]
        ring
    exact ⟨1 - t, t, by linarith, ht0, by ring, hpt⟩

variable (J : PolygonalCircle)

open Classical in
/-- The vertices at the height of `P`, strictly to its left. -/
noncomputable def leftVertices (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun k => (J.vertex k) 1 = P 1 ∧ (J.vertex k) 0 < P 0

open Classical in
/-- Edges with one endpoint at the height of `P` and left of `P`, the other endpoint strictly
above. -/
noncomputable def upLeftEdges (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun i =>
    ((J.vertex i) 1 = P 1 ∧ (J.vertex i) 0 < P 0 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
    ((J.vertex (i + 1)) 1 = P 1 ∧ (J.vertex (i + 1)) 0 < P 0 ∧ P 1 < (J.vertex i) 1)

open Classical in
/-- Edges with one endpoint at the height of `P` and left of `P`, the other endpoint strictly
below. -/
noncomputable def downLeftEdges (P : Plane) : Finset (ZMod J.n) :=
  Finset.univ.filter fun i =>
    ((J.vertex i) 1 = P 1 ∧ (J.vertex i) 0 < P 0 ∧ (J.vertex (i + 1)) 1 < P 1) ∨
    ((J.vertex (i + 1)) 1 = P 1 ∧ (J.vertex (i + 1)) 0 < P 0 ∧ (J.vertex i) 1 < P 1)

/-- The horizontal partner of a left vertex is a left vertex: otherwise the horizontal edge
between them would contain `P`. -/
theorem left_of_horizontal_partner {P : Plane} (hP : P ∉ J.carrier) {k : ZMod J.n}
    (hk1 : (J.vertex k) 1 = P 1) (hk0 : (J.vertex k) 0 < P 0)
    {l : ZMod J.n} (hl1 : (J.vertex l) 1 = P 1)
    (hedge : segment ℝ (J.vertex k) (J.vertex l) ⊆ J.carrier ∨
      segment ℝ (J.vertex l) (J.vertex k) ⊆ J.carrier) :
    (J.vertex l) 0 < P 0 := by
  by_contra hge
  rw [not_lt] at hge
  have hmem : P ∈ segment ℝ (J.vertex k) (J.vertex l) :=
    mem_segment_of_horizontal hk1 hl1 hk0.le hge
  rcases hedge with h | h
  · exact hP (h hmem)
  · refine hP (h ?_)
    rw [segment_symm]
    exact hmem

/-- Edge `i` (from vertex `i` to vertex `i + 1`) lies on the carrier. -/
theorem edgeSegment_subset_carrier (i : ZMod J.n) :
    segment ℝ (J.vertex i) (J.vertex (i + 1)) ⊆ J.carrier :=
  fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩

open Classical in
/-- **The handshake lemma**: the flipping edges (up-left plus down-left) are even in number. -/
theorem upLeft_card_add_downLeft_card_even {P : Plane} (hP : P ∉ J.carrier) :
    Even ((J.upLeftEdges P).card + (J.downLeftEdges P).card) := by
  classical
  set h : ℝ := P 1 with hh
  -- edges based at their first endpoint / second endpoint
  set A : Finset (ZMod J.n) := Finset.univ.filter fun i =>
    ((J.vertex i) 1 = h ∧ (J.vertex i) 0 < P 0) ∧ (J.vertex (i + 1)) 1 ≠ h with hA
  set B : Finset (ZMod J.n) := Finset.univ.filter fun i =>
    ((J.vertex (i + 1)) 1 = h ∧ (J.vertex (i + 1)) 0 < P 0) ∧ (J.vertex i) 1 ≠ h with hB
  -- the flipping edges split as A ⊔ B
  have hsplit : (J.upLeftEdges P).card + (J.downLeftEdges P).card = A.card + B.card := by
    have hUD : J.upLeftEdges P ∪ J.downLeftEdges P = A ∪ B := by
      ext i
      simp only [upLeftEdges, downLeftEdges, hA, hB, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨h1, h0, hup⟩ | ⟨h1, h0, hup⟩) | (⟨h1, h0, hdn⟩ | ⟨h1, h0, hdn⟩))
        · exact Or.inl ⟨⟨h1, h0⟩, (ne_of_lt hup).symm⟩
        · exact Or.inr ⟨⟨h1, h0⟩, (ne_of_lt hup).symm⟩
        · exact Or.inl ⟨⟨h1, h0⟩, ne_of_lt hdn⟩
        · exact Or.inr ⟨⟨h1, h0⟩, ne_of_lt hdn⟩
      · rintro (⟨⟨h1, h0⟩, hne⟩ | ⟨⟨h1, h0⟩, hne⟩)
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr (Or.inl ⟨h1, h0, hlt⟩)
          · exact Or.inl (Or.inl ⟨h1, h0, hgt⟩)
        · rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inr (Or.inr ⟨h1, h0, hlt⟩)
          · exact Or.inl (Or.inr ⟨h1, h0, hgt⟩)
    have hUDdisj : Disjoint (J.upLeftEdges P) (J.downLeftEdges P) := by
      rw [Finset.disjoint_left]
      intro i hiU hiD
      simp only [upLeftEdges, downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        at hiU hiD
      rcases hiU with ⟨h1, -, hup⟩ | ⟨h1, -, hup⟩ <;>
        rcases hiD with ⟨h1', -, hdn⟩ | ⟨h1', -, hdn⟩ <;> linarith
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro i hiA hiB
      simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiB
      exact hiB.2 hiA.1.1
    rw [← Finset.card_union_of_disjoint hUDdisj, ← Finset.card_union_of_disjoint hABdisj, hUD]
  -- count A against the left vertices whose outgoing edge is horizontal
  have hAcount : A.card +
      ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h).card =
        (J.leftVertices P).card := by
    have hdisj : Disjoint A ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h) := by
      rw [Finset.disjoint_left]
      intro i hiA hiL
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hiL
      exact hiA.2 hiL.2
    have hunion : A ∪ ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h) =
        J.leftVertices P := by
      ext i
      simp only [hA, leftVertices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, hh]
      tauto
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- count B against the left vertices whose incoming edge is horizontal, via the shift bijection
  have hBcount : B.card +
      ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h).card =
        (J.leftVertices P).card := by
    have hBimg : B = ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h).image
        (fun k => k - 1) := by
      ext i
      simp only [hB, leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h0⟩, hne⟩
        exact ⟨i + 1, ⟨⟨h1, h0⟩, by simpa using hne⟩, by ring⟩
      · rintro ⟨k, ⟨⟨h1, h0⟩, hne⟩, rfl⟩
        refine ⟨⟨by simpa using h1, by simpa using h0⟩, by simpa using hne⟩
    have himgcard : B.card =
        ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h).card := by
      rw [hBimg]
      exact Finset.card_image_of_injective _ sub_left_injective
    have hdisj : Disjoint ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h)
        ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h) := by
      rw [Finset.disjoint_left]
      intro i hiA hiL
      simp only [Finset.mem_filter] at hiA hiL
      exact hiA.2 hiL.2
    have hunion : ((J.leftVertices P).filter fun k => ¬ (J.vertex (k - 1)) 1 = h) ∪
        ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h) = J.leftVertices P := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    rw [himgcard, ← Finset.card_union_of_disjoint hdisj, hunion]
  -- horizontal partners stay left, so the two horizontal counts agree via the shift bijection
  have hhoriz : ((J.leftVertices P).filter fun k => (J.vertex (k + 1)) 1 = h).card =
      ((J.leftVertices P).filter fun k => (J.vertex (k - 1)) 1 = h).card := by
    apply Finset.card_bij (fun k _ => k + 1)
    · intro k hk
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh] at hk ⊢
      obtain ⟨⟨h1, h0⟩, hpart⟩ := hk
      have hleft : (J.vertex (k + 1)) 0 < P 0 :=
        J.left_of_horizontal_partner hP h1 h0 hpart
          (Or.inl (J.edgeSegment_subset_carrier k))
      exact ⟨⟨hpart, hleft⟩, by simpa using h1⟩
    · intro a _ b _ hab
      exact add_left_injective 1 hab
    · intro k hk
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh] at hk
      obtain ⟨⟨h1, h0⟩, hpart⟩ := hk
      refine ⟨k - 1, ?_, by ring⟩
      simp only [leftVertices, Finset.mem_filter, Finset.mem_univ, true_and, hh]
      have hseg : segment ℝ (J.vertex (k - 1)) (J.vertex k) ⊆ J.carrier := by
        have hsub := J.edgeSegment_subset_carrier (k - 1)
        rwa [show k - 1 + 1 = k by ring] at hsub
      have hleft : (J.vertex (k - 1)) 0 < P 0 :=
        J.left_of_horizontal_partner hP h1 h0 (l := k - 1) hpart (Or.inr hseg)
      exact ⟨⟨hpart, hleft⟩, by rwa [show k - 1 + 1 = k by ring]⟩
  rw [hsplit, Nat.even_iff]
  omega

/-! #### Per-edge behavior of the crossing status near a point off the polygon -/

theorem continuous_coord (j : Fin 2) : Continuous fun v : Plane => v j :=
  PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) j

/-- The crossing abscissa depends continuously on the query point. -/
theorem continuous_crossingX (v w : Plane) :
    Continuous fun Q : Plane => crossingX v w (Q 1) := by
  unfold crossingX
  fun_prop

@[simp] theorem crossingX_left (v w : Plane) : crossingX v w (v 1) = v 0 := by
  unfold crossingX
  simp

theorem crossingX_right (v w : Plane) (hne : v 1 ≠ w 1) : crossingX v w (w 1) = w 0 := by
  unfold crossingX
  field_simp
  ring

end PolygonalCircle

namespace PolygonalCircle

variable (J : PolygonalCircle)

/-- A point whose height lies in an edge's band and whose abscissa is the crossing abscissa lies
on that edge. -/
theorem mem_edgeSegment_of_crossing {P : Plane} (i : ZMod J.n)
    (hy : ((J.vertex i) 1 ≤ P 1 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
      ((J.vertex (i + 1)) 1 ≤ P 1 ∧ P 1 < (J.vertex i) 1))
    (hx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) = P 0) :
    P ∈ J.edgeSegment i := by
  have hab : (J.vertex (i + 1)) 1 - (J.vertex i) 1 ≠ 0 := by
    intro hz
    rw [sub_eq_zero] at hz
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  set t : ℝ := (P 1 - (J.vertex i) 1) / ((J.vertex (i + 1)) 1 - (J.vertex i) 1) with htdef
  have ht0 : 0 ≤ t := by
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_nonneg (by linarith) (by linarith)
    · exact le_of_lt (div_pos_of_neg_of_neg (by linarith) (by linarith))
  have ht1 : t ≤ 1 := by
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [htdef, div_le_one (by linarith)]
      linarith
    · rw [htdef, div_le_one_of_neg (by linarith)]
      linarith
  have hpt : (1 - t) • J.vertex i + t • J.vertex (i + 1) = P := by
    have hcx := hx
    unfold crossingX at hcx
    apply plane_ext
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [← hcx, htdef]
      field_simp
      ring
    · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [htdef]
      field_simp
      ring
  exact ⟨1 - t, t, by linarith, ht0, by ring, hpt⟩

/-- Carrier-level form of `mem_edgeSegment_of_crossing`. -/
theorem mem_carrier_of_crossing {P : Plane} (i : ZMod J.n)
    (hy : ((J.vertex i) 1 ≤ P 1 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
      ((J.vertex (i + 1)) 1 ≤ P 1 ∧ P 1 < (J.vertex i) 1))
    (hx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) = P 0) :
    P ∈ J.carrier :=
  J.edgeSegment_subset_carrier i (J.mem_edgeSegment_of_crossing i hy hx)

/-- On a nonhorizontal edge, the crossing formula recovers the abscissa of every point of the
edge. -/
theorem crossingX_eq_of_mem_edgeSegment {P : Plane} {i : ZMod J.n}
    (horiz : (J.vertex i) 1 ≠ (J.vertex (i + 1)) 1) (hP : P ∈ J.edgeSegment i) :
    crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) = P 0 := by
  rcases hP with ⟨a, b, ha, hb, hab, rfl⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  unfold crossingX
  have hden : (J.vertex (i + 1)) 1 - (J.vertex i) 1 ≠ 0 :=
    sub_ne_zero.mpr horiz.symm
  have haeq : a = 1 - b := by linarith
  have hquot :
      (a * (J.vertex i) 1 + b * (J.vertex (i + 1)) 1 - (J.vertex i) 1) /
          ((J.vertex (i + 1)) 1 - (J.vertex i) 1) = b := by
    rw [haeq]
    field_simp [hden]
    ring
  rw [hquot]
  rw [haeq]
  ring

/-- At a height different from both endpoint heights, a point of an edge lies strictly between
those heights. -/
theorem strict_height_band_of_mem_edgeSegment {P : Plane} {i : ZMod J.n}
    (hP : P ∈ J.edgeSegment i)
    (hheight : ∀ k : ZMod J.n, P 1 ≠ (J.vertex k) 1) :
    ((J.vertex i) 1 < P 1 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
      ((J.vertex (i + 1)) 1 < P 1 ∧ P 1 < (J.vertex i) 1) := by
  have hlo := min_le_height_of_mem_segment hP
  have hhi := height_le_max_of_mem_segment hP
  rcases lt_trichotomy ((J.vertex i) 1) ((J.vertex (i + 1)) 1) with hlt | heq | hgt
  · left
    rw [min_eq_left hlt.le] at hlo
    rw [max_eq_right hlt.le] at hhi
    exact ⟨lt_of_le_of_ne hlo (hheight i).symm,
      lt_of_le_of_ne hhi (hheight (i + 1))⟩
  · have hlo' := hlo
    have hhi' := hhi
    simp only [heq, min_self] at hlo'
    simp only [heq, max_self] at hhi'
    have hPeq : P 1 = (J.vertex (i + 1)) 1 := le_antisymm hhi' hlo'
    exact (hheight (i + 1) hPeq).elim
  · right
    rw [min_eq_right hgt.le] at hlo
    rw [max_eq_left hgt.le] at hhi
    exact ⟨lt_of_le_of_ne hlo (hheight (i + 1)).symm,
      lt_of_le_of_ne hhi (hheight i)⟩

/-- Two edges containing the same point away from all vertices are the same edge. -/
theorem edge_eq_of_mem_edgeSegments_of_height_ne_vertices {P : Plane} {i j : ZMod J.n}
    (hi : P ∈ J.edgeSegment i) (hj : P ∈ J.edgeSegment j)
    (hheight : ∀ k : ZMod J.n, P 1 ≠ (J.vertex k) 1) : i = j := by
  by_contra hij
  by_cases hij' : i = j + 1
  · have hmem : P ∈ J.edgeSegment j ∩ J.edgeSegment (j + 1) := by
      simpa [hij'] using And.intro hj hi
    have hinter : J.edgeSegment j ∩ J.edgeSegment (j + 1) = {J.vertex (j + 1)} := by
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter j
    have hvertex : P = J.vertex (j + 1) := by
      rw [hinter] at hmem
      exact hmem
    exact hheight (j + 1) (congrArg (fun q : Plane => q 1) hvertex)
  by_cases hji' : j = i + 1
  · have hmem : P ∈ J.edgeSegment i ∩ J.edgeSegment (i + 1) := by
      simpa [hji'] using And.intro hi hj
    have hinter : J.edgeSegment i ∩ J.edgeSegment (i + 1) = {J.vertex (i + 1)} := by
      simpa only [edgeSegment, add_assoc, one_add_one_eq_two] using J.consecutive_inter i
    have hvertex : P = J.vertex (i + 1) := by
      rw [hinter] at hmem
      exact hmem
    exact hheight (i + 1) (congrArg (fun q : Plane => q 1) hvertex)
  · have hdisj := J.nonadjacent_disjoint i j hij hij' hji'
    have hmem : P ∈ J.edgeSegment i ∩ J.edgeSegment j := ⟨hi, hj⟩
    rw [edgeSegment, edgeSegment, hdisj] at hmem
    exact hmem

/-- A polygon has a nonhorizontal edge.  Otherwise, at a leftmost vertex the two incident
horizontal edges overlap in more than their common endpoint. -/
theorem exists_nonhorizontal_edge :
    ∃ i : ZMod J.n, (J.vertex i) 1 ≠ (J.vertex (i + 1)) 1 := by
  classical
  by_contra hnone
  push Not at hnone
  set xs : Finset ℝ := Finset.univ.image fun i : ZMod J.n => (J.vertex i) 0 with hxs
  have hxsne : xs.Nonempty := by simp [hxs]
  set xmin : ℝ := xs.min' hxsne with hxmin
  obtain ⟨k, -, hkx⟩ := Finset.mem_image.mp (xs.min'_mem hxsne)
  have hkmin : ∀ i : ZMod J.n, (J.vertex k) 0 ≤ (J.vertex i) 0 := by
    intro i
    rw [hkx]
    exact Finset.min'_le xs _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hprevY : (J.vertex (k - 1)) 1 = (J.vertex k) 1 := by
    simpa using hnone (k - 1)
  have hnextY : (J.vertex k) 1 = (J.vertex (k + 1)) 1 := hnone k
  have hprevNe : J.vertex (k - 1) ≠ J.vertex k := by
    simpa using J.adjacent_ne (k - 1)
  have hnextNe : J.vertex k ≠ J.vertex (k + 1) := J.adjacent_ne k
  have hprevXne : (J.vertex (k - 1)) 0 ≠ (J.vertex k) 0 := by
    intro hx
    exact hprevNe (plane_ext hx hprevY)
  have hnextXne : (J.vertex k) 0 ≠ (J.vertex (k + 1)) 0 := by
    intro hx
    exact hnextNe (plane_ext hx hnextY)
  have hprevX : (J.vertex k) 0 < (J.vertex (k - 1)) 0 :=
    lt_of_le_of_ne (hkmin (k - 1)) hprevXne.symm
  have hnextX : (J.vertex k) 0 < (J.vertex (k + 1)) 0 :=
    lt_of_le_of_ne (hkmin (k + 1)) hnextXne
  set xmid : ℝ :=
    ((J.vertex k) 0 + min ((J.vertex (k - 1)) 0) ((J.vertex (k + 1)) 0)) / 2
      with hxmid
  set q : Plane := (WithLp.toLp 2 ![xmid, (J.vertex k) 1] : Plane) with hq
  have hkxmid : (J.vertex k) 0 < xmid := by
    rw [hxmid]
    have := lt_min hprevX hnextX
    linarith
  have hxmidprev : xmid ≤ (J.vertex (k - 1)) 0 := by
    rw [hxmid]
    have hle := min_le_left ((J.vertex (k - 1)) 0) ((J.vertex (k + 1)) 0)
    have hlt := lt_min hprevX hnextX
    linarith
  have hxmidnext : xmid ≤ (J.vertex (k + 1)) 0 := by
    rw [hxmid]
    have hle := min_le_right ((J.vertex (k - 1)) 0) ((J.vertex (k + 1)) 0)
    have hlt := lt_min hprevX hnextX
    linarith
  have hqprev' : q ∈ segment ℝ (J.vertex k) (J.vertex (k - 1)) := by
    apply mem_segment_of_horizontal
    · rfl
    · exact hprevY
    · exact hkxmid.le
    · exact hxmidprev
  have hqprev : q ∈ J.edgeSegment (k - 1) := by
    rw [edgeSegment, show k - 1 + 1 = k by ring, segment_symm]
    exact hqprev'
  have hqnext : q ∈ J.edgeSegment k := by
    apply mem_segment_of_horizontal
    · rfl
    · exact hnextY.symm
    · exact hkxmid.le
    · exact hxmidnext
  have hinter : J.edgeSegment (k - 1) ∩ J.edgeSegment k = {J.vertex k} := by
    simp only [edgeSegment]
    convert J.consecutive_inter (k - 1) using 1
    all_goals ring_nf
  have hqeq : q = J.vertex k := by
    have hmem : q ∈ J.edgeSegment (k - 1) ∩ J.edgeSegment k := ⟨hqprev, hqnext⟩
    rw [hinter] at hmem
    exact hmem
  have hx := congrArg (fun p : Plane => p 0) hqeq
  change xmid = (J.vertex k) 0 at hx
  linarith

/-- Horizontal edges are never crossed. -/
theorem not_edgeCrossed_of_horizontal {i : ZMod J.n}
    (hAB : (J.vertex i) 1 = (J.vertex (i + 1)) 1) (R : Plane) : ¬ J.EdgeCrossed i R := by
  rintro ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, -⟩ <;> linarith

/-- Near a point off the polygon, each edge's crossing status is: switched by the query height
for the flipping edges, constant otherwise. -/
theorem eventually_edgeCrossed_iff {P : Plane} (hP : P ∉ J.carrier) (i : ZMod J.n) :
    ∀ᶠ Q in nhds P,
      (J.EdgeCrossed i Q ↔
        if i ∈ J.upLeftEdges P then P 1 ≤ Q 1
        else if i ∈ J.downLeftEdges P then Q 1 < P 1
        else J.EdgeCrossed i P) := by
  classical
  have hev_lt : ∀ c : ℝ, P 1 < c → ∀ᶠ Q : Plane in nhds P, Q 1 < c := fun c hc =>
    (isOpen_lt (continuous_coord 1) continuous_const).eventually_mem hc
  have hev_gt : ∀ c : ℝ, c < P 1 → ∀ᶠ Q : Plane in nhds P, c < Q 1 := fun c hc =>
    (isOpen_lt continuous_const (continuous_coord 1)).eventually_mem hc
  have hev_x_lt : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0 →
      ∀ᶠ Q : Plane in nhds P, crossingX (J.vertex i) (J.vertex (i + 1)) (Q 1) < Q 0 :=
    fun hc => (isOpen_lt (continuous_crossingX _ _) (continuous_coord 0)).eventually_mem hc
  have hev_x_gt : P 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) →
      ∀ᶠ Q : Plane in nhds P, Q 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (Q 1) :=
    fun hc => (isOpen_lt (continuous_coord 0) (continuous_crossingX _ _)).eventually_mem hc
  by_cases hU : i ∈ J.upLeftEdges P
  · -- rising flipping edge: status iff (P 1 ≤ Q 1) eventually
    simp only [hU, ite_eq_left]
    have hU' := hU
    simp only [upLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hU'
    obtain ⟨hbase1, hbase0, htop⟩ | ⟨hbase1, hbase0, htop⟩ := hU'
    · -- base is vertex i
      have hcx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0 := by
        rw [← hbase1, crossingX_left]
        exact hbase0
      filter_upwards [hev_lt _ htop, hev_x_lt hcx] with Q hQtop hQx
      constructor
      · rintro ⟨⟨h1, -⟩ | ⟨h1, -⟩, -⟩
        · rw [← hbase1]; exact h1
        · linarith
      · intro hQ1
        exact ⟨Or.inl ⟨by rw [hbase1]; exact hQ1, hQtop⟩, hQx⟩
    · -- base is vertex i + 1
      have hcx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0 := by
        rw [← hbase1, crossingX_right _ _ (by rw [hbase1]; exact ne_of_gt htop)]
        exact hbase0
      filter_upwards [hev_lt _ htop, hev_x_lt hcx] with Q hQtop hQx
      constructor
      · rintro ⟨⟨h1', -⟩ | ⟨h1, -⟩, -⟩
        · linarith
        · rw [← hbase1]; exact h1
      · intro hQ1
        exact ⟨Or.inr ⟨by rw [hbase1]; exact hQ1, hQtop⟩, hQx⟩
  by_cases hD : i ∈ J.downLeftEdges P
  · -- falling flipping edge: status iff (Q 1 < P 1) eventually
    simp only [hU, hD, ite_eq_right, ite_eq_left, not_false_iff]
    have hD' := hD
    simp only [downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hD'
    obtain ⟨hbase1, hbase0, hbot⟩ | ⟨hbase1, hbase0, hbot⟩ := hD'
    · -- base is vertex i, other endpoint below
      have hcx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0 := by
        rw [← hbase1, crossingX_left]
        exact hbase0
      filter_upwards [hev_gt _ hbot, hev_x_lt hcx] with Q hQbot hQx
      constructor
      · rintro ⟨⟨h1, h2⟩ | ⟨-, h2⟩, -⟩
        · linarith
        · rw [← hbase1]; exact h2
      · intro hQ1
        exact ⟨Or.inr ⟨hQbot.le, by rw [hbase1]; exact hQ1⟩, hQx⟩
    · -- base is vertex i + 1, other endpoint below
      have hcx : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) < P 0 := by
        rw [← hbase1, crossingX_right _ _ (by rw [hbase1]; exact ne_of_lt hbot)]
        exact hbase0
      filter_upwards [hev_gt _ hbot, hev_x_lt hcx] with Q hQbot hQx
      constructor
      · rintro ⟨⟨-, h2⟩ | ⟨h1, h2⟩, -⟩
        · rw [← hbase1]; exact h2
        · linarith
      · intro hQ1
        exact ⟨Or.inl ⟨hQbot.le, by rw [hbase1]; exact hQ1⟩, hQx⟩
  · -- non-flipping edge: status eventually constant
    simp only [hU, hD, ite_eq_right, not_false_iff]
    by_cases hAB : (J.vertex i) 1 = (J.vertex (i + 1)) 1
    · -- horizontal: never crossed on either side
      filter_upwards [] with Q
      exact iff_of_false (J.not_edgeCrossed_of_horizontal hAB Q)
        (J.not_edgeCrossed_of_horizontal hAB P)
    -- non-horizontal, non-flipping
    by_cases hyP : ((J.vertex i) 1 ≤ P 1 ∧ P 1 < (J.vertex (i + 1)) 1) ∨
        ((J.vertex (i + 1)) 1 ≤ P 1 ∧ P 1 < (J.vertex i) 1)
    · -- the height condition holds at P
      have hxne : crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) ≠ P 0 := fun hx =>
        hP (J.mem_carrier_of_crossing i hyP hx)
      -- P is not at either endpoint height, or the edge would be flipping or right-critical;
      -- first show the endpoint heights straddle P strictly or the x-condition settles it
      rcases lt_or_gt_of_ne hxne with hxlt | hxgt
      · -- the crossing is strictly left of P: the edge is genuinely crossed at P unless the
        -- height condition degenerates at an endpoint, which the flipping/critical analysis
        -- below rules out
        rcases hyP with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases eq_or_lt_of_le h1 with heq | hlt
          · -- P at the lower endpoint height: vertex i is the base; it must be right of P or
            -- equal to P, but the crossing abscissa at P 1 is vertex i's abscissa < P 0,
            -- contradicting non-membership in the flipping sets
            exfalso
            have hbx : (J.vertex i) 0 < P 0 := by
              rw [← heq] at hxlt
              rwa [crossingX_left] at hxlt
            exact hU (by
              simp only [upLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Or.inl ⟨heq, hbx, h2⟩)
          · -- strictly inside the band: the status is eventually true, as at P
            filter_upwards [hev_gt _ hlt, hev_lt _ h2, hev_x_lt hxlt] with Q hQ1 hQ2 hQx
            exact iff_of_true ⟨Or.inl ⟨hQ1.le, hQ2⟩, hQx⟩ ⟨Or.inl ⟨h1, h2⟩, hxlt⟩
        · rcases eq_or_lt_of_le h1 with heq | hlt
          · exfalso
            have hbx : (J.vertex (i + 1)) 0 < P 0 := by
              rw [← heq] at hxlt
              rwa [crossingX_right _ _ (by rw [heq]; exact ne_of_gt h2)] at hxlt
            exact hU (by
              simp only [upLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Or.inr ⟨heq, hbx, h2⟩)
          · filter_upwards [hev_gt _ hlt, hev_lt _ h2, hev_x_lt hxlt] with Q hQ1 hQ2 hQx
            exact iff_of_true ⟨Or.inr ⟨hQ1.le, hQ2⟩, hQx⟩ ⟨Or.inr ⟨h1, h2⟩, hxlt⟩
      · -- the crossing is strictly right of P: eventually never crossed, and not crossed at P
        filter_upwards [hev_x_gt hxgt] with Q hQx
        exact iff_of_false (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hQx.le))
          (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hxgt.le))
    · -- the height condition fails at P and P is at neither endpoint height strictly inside:
      -- P's height avoids the closed band, so nearby heights do too
      have hAne : (J.vertex i) 1 ≠ P 1 ∨ ¬ (P 1 < (J.vertex (i + 1)) 1) := by
        by_cases hA : (J.vertex i) 1 = P 1
        · right
          intro hB
          exact hyP (Or.inl ⟨hA.le, hB⟩)
        · exact Or.inl hA
      -- case on the position of P 1 relative to both endpoint heights
      rcases lt_trichotomy (P 1) ((J.vertex i) 1) with hA | hA | hA
      · rcases lt_trichotomy (P 1) ((J.vertex (i + 1)) 1) with hB | hB | hB
        · -- P 1 below both: nearby heights below both
          filter_upwards [hev_lt _ hA, hev_lt _ hB] with Q hQ1 hQ2
          refine iff_of_false ?_ ?_
          · rintro ⟨⟨h1, -⟩ | ⟨h1, -⟩, -⟩ <;> linarith
          · rintro ⟨⟨h1, -⟩ | ⟨h1, -⟩, -⟩ <;> linarith
        · -- P 1 equals the height of vertex i+1, which is below vertex i: the edge falls to a
          -- base at P's height; it is not flipping, so the base is right of P (or equals P)
          have hbase : P 0 < (J.vertex (i + 1)) 0 := by
            rcases lt_trichotomy ((J.vertex (i + 1)) 0) (P 0) with hlt | heq | hgt
            · exact absurd (by
                simp only [upLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
                exact Or.inr ⟨hB.symm, hlt, hA⟩) hU
            · exact absurd (J.vertex_mem_carrier (i + 1))
                (by rw [plane_ext heq (by rw [hB])]; exact hP)
            · exact hgt
          have hxgt : P 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) := by
            rw [hB, crossingX_right _ _ (by rw [← hB]; exact ne_of_gt hA)]
            exact hbase
          filter_upwards [hev_x_gt hxgt] with Q hQx
          exact iff_of_false (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hQx.le))
            (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hxgt.le))
        · -- between the heights with the band living on the other side: the height condition
          -- holds at P after all, contradiction
          exact absurd (Or.inr ⟨hB.le, hA⟩) hyP
      · -- P 1 equals the height of vertex i
        have hBne : (J.vertex (i + 1)) 1 ≠ P 1 := by
          intro hB
          exact hAB (hA.symm.trans hB.symm)
        rcases lt_or_gt_of_ne hBne with hB | hB
        · -- the edge falls from a base at P's height
          have hbase : P 0 < (J.vertex i) 0 := by
            rcases lt_trichotomy ((J.vertex i) 0) (P 0) with hlt | heq | hgt
            · exact absurd (by
                simp only [downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
                exact Or.inl ⟨hA.symm, hlt, hB⟩) hD
            · exact absurd (J.vertex_mem_carrier i)
                (by rw [plane_ext heq hA.symm]; exact hP)
            · exact hgt
          have hxgt : P 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) := by
            rw [hA, crossingX_left]
            exact hbase
          filter_upwards [hev_x_gt hxgt] with Q hQx
          exact iff_of_false (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hQx.le))
            (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hxgt.le))
        · -- the edge rises from a base at P's height
          have hbase : P 0 < (J.vertex i) 0 := by
            rcases lt_trichotomy ((J.vertex i) 0) (P 0) with hlt | heq | hgt
            · exact absurd (by
                simp only [upLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
                exact Or.inl ⟨hA.symm, hlt, hB⟩) hU
            · exact absurd (J.vertex_mem_carrier i)
                (by rw [plane_ext heq hA.symm]; exact hP)
            · exact hgt
          have hxgt : P 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) := by
            rw [hA, crossingX_left]
            exact hbase
          filter_upwards [hev_x_gt hxgt] with Q hQx
          exact iff_of_false (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hQx.le))
            (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hxgt.le))
      · rcases lt_trichotomy (P 1) ((J.vertex (i + 1)) 1) with hB | hB | hB
        · -- band straddles P from the other orientation: height condition holds, contradiction
          exact absurd (Or.inl ⟨hA.le, hB⟩) hyP
        · -- P 1 equals the height of vertex i+1, which is above... the edge rises to a base at
          -- P's height from vertex i below? No: vertex i is below P, base is vertex i+1 at P
          have hbase : P 0 < (J.vertex (i + 1)) 0 := by
            rcases lt_trichotomy ((J.vertex (i + 1)) 0) (P 0) with hlt | heq | hgt
            · exact absurd (by
                simp only [downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
                exact Or.inr ⟨hB.symm, hlt, hA⟩) hD
            · exact absurd (J.vertex_mem_carrier (i + 1))
                (by rw [plane_ext heq (by rw [hB])]; exact hP)
            · exact hgt
          have hxgt : P 0 < crossingX (J.vertex i) (J.vertex (i + 1)) (P 1) := by
            rw [hB, crossingX_right _ _ (by rw [← hB]; exact ne_of_lt hA)]
            exact hbase
          filter_upwards [hev_x_gt hxgt] with Q hQx
          exact iff_of_false (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hQx.le))
            (fun ⟨_, hx⟩ => absurd hx (not_lt.mpr hxgt.le))
        · -- P 1 above both: nearby heights above both
          filter_upwards [hev_gt _ hA, hev_gt _ hB] with Q hQ1 hQ2
          refine iff_of_false ?_ ?_
          · rintro ⟨⟨-, h2⟩ | ⟨-, h2⟩, -⟩ <;> linarith
          · rintro ⟨⟨-, h2⟩ | ⟨-, h2⟩, -⟩ <;> linarith

/-- **Sub-boundary** (Moise Ch. 2, Thm. 1, Lemma 2, local constancy of the index).

Off the polygon the crossing index is locally constant.  The proof is elementary casework: for
`Q` near `P`, the crossing status of each edge is unchanged unless the ray endpoint passes a
vertex height, and at a vertex height the half-open convention makes the count change by `0` or
`2` (the two edges at that vertex are both gained or both lost when they point to the same side,
and exchanged when they point to opposite sides). -/
theorem index_locallyConstant {P : Plane} (hP : P ∉ J.carrier) :
    ∀ᶠ Q in nhds P, J.index Q = J.index P := by
  classical
  have hnearFin : ∀ s : Finset (ZMod J.n), ∀ᶠ Q in nhds P, ∀ i ∈ s,
      (J.EdgeCrossed i Q ↔
        if i ∈ J.upLeftEdges P then P 1 ≤ Q 1
        else if i ∈ J.downLeftEdges P then Q 1 < P 1
        else J.EdgeCrossed i P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        filter_upwards [J.eventually_edgeCrossed_iff hP i, ih] with Q hQi hQs
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hQi
        · exact hQs j hj
  have hnear : ∀ᶠ Q in nhds P, ∀ i : ZMod J.n,
      (J.EdgeCrossed i Q ↔
        if i ∈ J.upLeftEdges P then P 1 ≤ Q 1
        else if i ∈ J.downLeftEdges P then Q 1 < P 1
        else J.EdgeCrossed i P) :=
    (hnearFin Finset.univ).mono fun _ h i => h i (Finset.mem_univ i)
  have hatP : ∀ i : ZMod J.n,
      (J.EdgeCrossed i P ↔
        if i ∈ J.upLeftEdges P then P 1 ≤ P 1
        else if i ∈ J.downLeftEdges P then P 1 < P 1
        else J.EdgeCrossed i P) := by
    intro i
    have hmem : {Q : Plane |
        J.EdgeCrossed i Q ↔
          if i ∈ J.upLeftEdges P then P 1 ≤ Q 1
          else if i ∈ J.downLeftEdges P then Q 1 < P 1
          else J.EdgeCrossed i P} ∈ nhds P :=
      J.eventually_edgeCrossed_iff hP i
    exact @Filter.Eventually.self_of_nhds Plane _ P (fun Q =>
      J.EdgeCrossed i Q ↔
        if i ∈ J.upLeftEdges P then P 1 ≤ Q 1
        else if i ∈ J.downLeftEdges P then Q 1 < P 1
        else J.EdgeCrossed i P) hmem
  filter_upwards [hnear] with Q hQ
  by_cases habove : P 1 ≤ Q 1
  · unfold index
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hQ i, hatP i]
    by_cases hU : i ∈ J.upLeftEdges P
    · simp [hU, habove]
    by_cases hD : i ∈ J.downLeftEdges P
    · simp [hU, hD, habove]
    · simp [hU, hD]
  · have hbelow : Q 1 < P 1 := lt_of_not_ge habove
    have hUD : Disjoint (J.upLeftEdges P) (J.downLeftEdges P) := by
      rw [Finset.disjoint_left]
      intro i hiU hiD
      simp only [upLeftEdges, downLeftEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        at hiU hiD
      rcases hiU with ⟨h1, -, hup⟩ | ⟨h1, -, hup⟩ <;>
        rcases hiD with ⟨h1', -, hdn⟩ | ⟨h1', -, hdn⟩ <;> linarith
    set R : Finset (ZMod J.n) := Finset.univ.filter fun i =>
      i ∉ J.upLeftEdges P ∧ i ∉ J.downLeftEdges P ∧ J.EdgeCrossed i P with hR
    have hcrossP :
        (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P) =
          J.upLeftEdges P ∪ R := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hR]
      rw [hatP i]
      by_cases hU : i ∈ J.upLeftEdges P
      · simp [hU]
      by_cases hD : i ∈ J.downLeftEdges P
      · simp [hU, hD]
      · simp [hU, hD]
    have hcrossQ :
        (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i Q) =
          J.downLeftEdges P ∪ R := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hR]
      rw [hQ i]
      by_cases hU : i ∈ J.upLeftEdges P
      · have hD : i ∉ J.downLeftEdges P := Finset.disjoint_left.mp hUD hU
        simp [hU, hD, habove]
      by_cases hD : i ∈ J.downLeftEdges P
      · simp [hU, hD, hbelow]
      · simp [hU, hD]
    have hUR : Disjoint (J.upLeftEdges P) R := by
      rw [Finset.disjoint_left]
      intro i hiU hiR
      exact (Finset.mem_filter.mp hiR).2.1 hiU
    have hDR : Disjoint (J.downLeftEdges P) R := by
      rw [Finset.disjoint_left]
      intro i hiD hiR
      exact (Finset.mem_filter.mp hiR).2.2.1 hiD
    have heven := J.upLeft_card_add_downLeft_card_even hP
    rw [Nat.even_iff] at heven
    unfold index
    rw [hcrossQ, Finset.card_union_of_disjoint hDR, hcrossP,
      Finset.card_union_of_disjoint hUR]
    omega

/-- **Sub-boundary** (Moise Ch. 2, Thm. 1, Lemma 2, existence of an inside point).

Some point off the polygon has index one: take a height that is no vertex height but is attained
by the polygon, let `P₁` be the leftmost polygon point at that height, and move slightly right of
`P₁`.  (Moise's construction; requires knowing the polygon is not contained in a single
horizontal line, which follows from the embedding fields.) -/
theorem exists_index_eq_one : ∃ P : Plane, P ∉ J.carrier ∧ J.index P = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := J.exists_nonhorizontal_edge
  set vertexHeights : Finset ℝ :=
    Finset.univ.image fun i : ZMod J.n => (J.vertex i) 1 with hvertexHeights
  have hinterval :
      min ((J.vertex i₀) 1) ((J.vertex (i₀ + 1)) 1) <
        max ((J.vertex i₀) 1) ((J.vertex (i₀ + 1)) 1) :=
    min_lt_max.mpr hi₀
  obtain ⟨y, hy, hynot⟩ :=
    (Set.Ioo_infinite hinterval).exists_notMem_finset vertexHeights
  have hyne : ∀ i : ZMod J.n, y ≠ (J.vertex i) 1 := by
    intro i heq
    apply hynot
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩
  set active : Finset (ZMod J.n) := Finset.univ.filter fun i =>
    ((J.vertex i) 1 < y ∧ y < (J.vertex (i + 1)) 1) ∨
      ((J.vertex (i + 1)) 1 < y ∧ y < (J.vertex i) 1) with hactive
  have hi₀active : i₀ ∈ active := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i₀, ?_⟩
    rcases lt_or_gt_of_ne hi₀ with hlt | hgt
    · left
      simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hy
    · right
      simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hy
  set xCross : ZMod J.n → ℝ := fun i =>
    crossingX (J.vertex i) (J.vertex (i + 1)) y with hxCross
  have hxCross_inj : Set.InjOn xCross (active : Set (ZMod J.n)) := by
    intro i hi j hj hij
    change i ∈ active at hi
    change j ∈ active at hj
    have hiband := (Finset.mem_filter.mp hi).2
    have hjband := (Finset.mem_filter.mp hj).2
    set q : Plane := (WithLp.toLp 2 ![xCross i, y] : Plane) with hq
    have hqi : q ∈ J.edgeSegment i := by
      apply J.mem_edgeSegment_of_crossing i
      · rcases hiband with h | h
        · exact Or.inl ⟨h.1.le, h.2⟩
        · exact Or.inr ⟨h.1.le, h.2⟩
      · rfl
    have hqj : q ∈ J.edgeSegment j := by
      apply J.mem_edgeSegment_of_crossing j
      · rcases hjband with h | h
        · exact Or.inl ⟨h.1.le, h.2⟩
        · exact Or.inr ⟨h.1.le, h.2⟩
      · change xCross j = xCross i
        exact hij.symm
    apply J.edge_eq_of_mem_edgeSegments_of_height_ne_vertices hqi hqj
    intro k
    change y ≠ (J.vertex k) 1
    exact hyne k
  set crossingXs : Finset ℝ := active.image xCross with hcrossingXs
  have hcrossingXs_ne : crossingXs.Nonempty :=
    ⟨xCross i₀, Finset.mem_image.mpr ⟨i₀, hi₀active, rfl⟩⟩
  set xmin : ℝ := crossingXs.min' hcrossingXs_ne with hxmin
  have hxmin_mem : xmin ∈ crossingXs := by
    rw [hxmin]
    exact crossingXs.min'_mem hcrossingXs_ne
  obtain ⟨imin, himin, himinx⟩ := Finset.mem_image.mp hxmin_mem
  have hxmin_le : ∀ x ∈ crossingXs, xmin ≤ x := by
    intro x hx
    rw [hxmin]
    exact Finset.min'_le crossingXs x hx
  have hgap : ∃ xp : ℝ, xmin < xp ∧
      ∀ x ∈ crossingXs, x = xmin ∨ xp < x := by
    set above : Finset ℝ := crossingXs.filter fun x => xmin < x with habove
    by_cases hne : above.Nonempty
    · set xnext : ℝ := above.min' hne with hxnext
      have hxnext_mem : xnext ∈ above := by
        rw [hxnext]
        exact above.min'_mem hne
      have hxminnext : xmin < xnext := (Finset.mem_filter.mp hxnext_mem).2
      refine ⟨(xmin + xnext) / 2, by linarith, ?_⟩
      intro x hx
      by_cases hxeq : x = xmin
      · exact Or.inl hxeq
      · right
        have hxminx : xmin < x :=
          lt_of_le_of_ne (hxmin_le x hx) (Ne.symm hxeq)
        have hxabove : x ∈ above := Finset.mem_filter.mpr ⟨hx, hxminx⟩
        have hnextle : xnext ≤ x := by
          rw [hxnext]
          exact Finset.min'_le above x hxabove
        linarith
    · refine ⟨xmin + 1, by linarith, ?_⟩
      intro x hx
      by_cases hxeq : x = xmin
      · exact Or.inl hxeq
      · have hxminx : xmin < x :=
          lt_of_le_of_ne (hxmin_le x hx) (Ne.symm hxeq)
        exact (hne ⟨x, Finset.mem_filter.mpr ⟨hx, hxminx⟩⟩).elim
  obtain ⟨xp, hxminxp, hgap⟩ := hgap
  set P : Plane := (WithLp.toLp 2 ![xp, y] : Plane) with hPdef
  have hcrossed_iff (i : ZMod J.n) : J.EdgeCrossed i P ↔ i = imin := by
    constructor
    · rintro ⟨hiband, hix⟩
      have hiactive : i ∈ active := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_⟩
        rcases hiband with h | h
        · exact Or.inl ⟨lt_of_le_of_ne h.1 (hyne i).symm, h.2⟩
        · exact Or.inr ⟨lt_of_le_of_ne h.1 (hyne (i + 1)).symm, h.2⟩
      have hxmem : xCross i ∈ crossingXs :=
        Finset.mem_image.mpr ⟨i, hiactive, rfl⟩
      have hxlt : xCross i < xp := hix
      rcases hgap (xCross i) hxmem with hxmin' | hxp
      · apply hxCross_inj hiactive himin
        exact hxmin'.trans himinx.symm
      · linarith
    · intro hieq
      rw [hieq]
      have hband := (Finset.mem_filter.mp himin).2
      constructor
      · rcases hband with h | h
        · exact Or.inl ⟨h.1.le, h.2⟩
        · exact Or.inr ⟨h.1.le, h.2⟩
      · change xCross imin < xp
        rw [himinx]
        exact hxminxp
  have hPnot : P ∉ J.carrier := by
    intro hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    have hheight : ∀ k : ZMod J.n, P 1 ≠ (J.vertex k) 1 := by
      intro k
      change y ≠ (J.vertex k) 1
      exact hyne k
    have hiband := J.strict_height_band_of_mem_edgeSegment hi hheight
    have hiactive : i ∈ active :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiband⟩
    have horiz : (J.vertex i) 1 ≠ (J.vertex (i + 1)) 1 := by
      rcases hiband with h | h
      · exact ne_of_lt (h.1.trans h.2)
      · exact (ne_of_lt (h.1.trans h.2)).symm
    have hxeq := J.crossingX_eq_of_mem_edgeSegment horiz hi
    change xCross i = xp at hxeq
    have hxmem : xCross i ∈ crossingXs :=
      Finset.mem_image.mpr ⟨i, hiactive, rfl⟩
    rcases hgap (xCross i) hxmem with hxmin' | hxp
    · linarith
    · linarith
  refine ⟨P, hPnot, ?_⟩
  unfold index
  have hfilter :
      (Finset.univ.filter fun i : ZMod J.n => J.EdgeCrossed i P) = {imin} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact hcrossed_iff i
  rw [hfilter]
  simp

/-- The part of the polygon complement having crossing index `k`.  Only `k = 0, 1` are
nonempty. -/
def indexRegion (k : ℕ) : Set Plane :=
  {P | P ∉ J.carrier ∧ J.index P = k}

/-- Every index region is open, since the carrier is closed and the index is locally constant on
its complement. -/
theorem isOpen_indexRegion (k : ℕ) : IsOpen (J.indexRegion k) := by
  rw [isOpen_iff_mem_nhds]
  rintro P ⟨hPmem, hPk⟩
  have hcompl : J.carrierᶜ ∈ nhds P :=
    J.isClosed_carrier.isOpen_compl.mem_nhds hPmem
  filter_upwards [J.index_locallyConstant hPmem, hcompl] with Q hQ hQmem
  exact ⟨hQmem, by rw [hQ, hPk]⟩

theorem indexRegion_zero_nonempty : (J.indexRegion 0).Nonempty := by
  obtain ⟨P, hPmem, hPindex⟩ := J.exists_index_eq_zero
  exact ⟨P, hPmem, hPindex⟩

theorem indexRegion_one_nonempty : (J.indexRegion 1).Nonempty := by
  obtain ⟨P, hPmem, hPindex⟩ := J.exists_index_eq_one
  exact ⟨P, hPmem, hPindex⟩

/-- The index-zero region is unbounded: it contains points arbitrarily high above the polygon. -/
theorem not_isBounded_indexRegion_zero : ¬ Bornology.IsBounded (J.indexRegion 0) := by
  intro hbounded
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  obtain ⟨ymax, hymax⟩ : ∃ y, ∀ i : ZMod J.n, (J.vertex i) 1 ≤ y := by
    set heights : Finset ℝ := Finset.univ.image fun i : ZMod J.n => (J.vertex i) 1 with hheights
    have hne : heights.Nonempty := by simp [hheights]
    exact ⟨heights.max' hne,
      fun i => Finset.le_max' heights _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
  set y : ℝ := max (ymax + 1) (|C| + 1) with hy
  set P : Plane := (WithLp.toLp 2 ![0, y] : Plane) with hP
  have hhigh : ∀ i : ZMod J.n, (J.vertex i) 1 < P 1 := by
    intro i
    change (J.vertex i) 1 < y
    have := hymax i
    have : ymax + 1 ≤ y := by rw [hy]; exact le_max_left _ _
    linarith
  have hPreg : P ∈ J.indexRegion 0 :=
    ⟨J.notMem_carrier_of_high hhigh, J.index_eq_zero_of_high hhigh⟩
  have hnorm := hC P hPreg
  have hcoord := PiLp.norm_apply_le (p := 2) P (1 : Fin 2)
  have hyC : |C| + 1 ≤ y := by rw [hy]; exact le_max_right _ _
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hyC
  change |y| ≤ ‖P‖ at hcoord
  rw [abs_of_pos hypos] at hcoord
  have hCle : C ≤ |C| := le_abs_self C
  linarith

theorem disjoint_indexRegion_zero_one : Disjoint (J.indexRegion 0) (J.indexRegion 1) := by
  rw [Set.disjoint_left]
  intro P hP0 hP1
  change P ∉ J.carrier ∧ J.index P = 0 at hP0
  change P ∉ J.carrier ∧ J.index P = 1 at hP1
  rw [hP0.2] at hP1
  norm_num at hP1

theorem indexRegion_zero_union_one :
    J.indexRegion 0 ∪ J.indexRegion 1 = J.carrierᶜ := by
  ext P
  constructor
  · rintro (hP | hP)
    · exact hP.1
    · exact hP.1
  · intro hP
    have hlt := J.index_lt_two P
    interval_cases hindex : J.index P
    · exact Or.inl ⟨hP, hindex⟩
    · exact Or.inr ⟨hP, hindex⟩

/-- The polygon is the frontier of its full complement. -/
theorem frontier_compl_carrier : frontier J.carrierᶜ = J.carrier := by
  rw [frontier_compl, J.isClosed_carrier.frontier_eq, J.interior_carrier]
  simp

theorem frontier_indexRegion_zero_subset_carrier :
    frontier (J.indexRegion 0) ⊆ J.carrier := by
  intro P hP
  by_contra hPcarrier
  have hPcompl : P ∈ J.carrierᶜ := hPcarrier
  rw [← J.indexRegion_zero_union_one] at hPcompl
  rcases hPcompl with hP0 | hP1
  · exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (J.isOpen_indexRegion 0)) hP hP0
  · exact Set.disjoint_left.1
      (J.disjoint_indexRegion_zero_one.frontier_left (J.isOpen_indexRegion 1)) hP hP1

theorem frontier_indexRegion_one_subset_carrier :
    frontier (J.indexRegion 1) ⊆ J.carrier := by
  intro P hP
  by_contra hPcarrier
  have hPcompl : P ∈ J.carrierᶜ := hPcarrier
  rw [← J.indexRegion_zero_union_one] at hPcompl
  rcases hPcompl with hP0 | hP1
  · exact Set.disjoint_left.1
      (J.disjoint_indexRegion_zero_one.frontier_right (J.isOpen_indexRegion 0)) hP0 hP
  · exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (J.isOpen_indexRegion 1)) hP hP1

/-- Every polygon point is approached by at least one of the two index sides.  The remaining
two-sided frontier step is to show that it is approached by both. -/
theorem carrier_subset_frontier_indexRegion_union :
    J.carrier ⊆ frontier (J.indexRegion 0) ∪ frontier (J.indexRegion 1) := by
  rw [← J.frontier_compl_carrier, ← J.indexRegion_zero_union_one]
  exact (frontier_union_subset (J.indexRegion 0) (J.indexRegion 1)).trans fun P hP => by
    rcases hP with hP | hP
    · exact Or.inl hP.1
    · exact Or.inr hP.2

/-- The crossing index is constant on every preconnected subset of the polygon complement. -/
theorem index_eq_of_isPreconnected {s : Set Plane} (hs : IsPreconnected s)
    (hsub : s ⊆ J.carrierᶜ) {P Q : Plane} (hP : P ∈ s) (hQ : Q ∈ s) :
    J.index P = J.index Q := by
  by_contra hne
  have hPlt := J.index_lt_two P
  have hQlt := J.index_lt_two Q
  interval_cases hPi : J.index P <;> interval_cases hQi : J.index Q
  · exact hne rfl
  · obtain ⟨R, -, hR0, hR1⟩ := hs (J.indexRegion 0) (J.indexRegion 1)
      (J.isOpen_indexRegion 0) (J.isOpen_indexRegion 1)
      (by rw [J.indexRegion_zero_union_one]; exact hsub)
      ⟨P, hP, hsub hP, hPi⟩ ⟨Q, hQ, hsub hQ, hQi⟩
    exact Set.disjoint_left.1 J.disjoint_indexRegion_zero_one hR0 hR1
  · obtain ⟨R, -, hR1, hR0⟩ := hs (J.indexRegion 1) (J.indexRegion 0)
      (J.isOpen_indexRegion 1) (J.isOpen_indexRegion 0)
      (by rw [Set.union_comm, J.indexRegion_zero_union_one]; exact hsub)
      ⟨P, hP, hsub hP, hPi⟩ ⟨Q, hQ, hsub hQ, hQi⟩
    exact Set.disjoint_left.1 J.disjoint_indexRegion_zero_one hR0 hR1
  · exact hne rfl

/-- A path in the polygon complement has constant crossing index. -/
theorem index_eq_of_joinedIn_compl {P Q : Plane} (h : JoinedIn J.carrierᶜ P Q) :
    J.index P = J.index Q := by
  let γ := h.somePath
  have hconn : IsPreconnected (Set.range γ) :=
    (isConnected_range γ.continuous).isPreconnected
  have hsub : Set.range γ ⊆ J.carrierᶜ := by
    rintro x ⟨t, ht⟩
    rw [← ht]
    exact h.somePath_mem t
  apply J.index_eq_of_isPreconnected hconn hsub
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

/-- A path in a neighborhood of the polygon complement whose initial point has index `k` stays
in the index-`k` part of that neighborhood. -/
theorem JoinedIn.mono_indexRegion {N : Set Plane} {P Q : Plane} {k : ℕ}
    (h : JoinedIn (N \ J.carrier) P Q) (hindex : J.index P = k) :
    JoinedIn (N ∩ J.indexRegion k) P Q := by
  let γ := h.somePath
  refine ⟨γ, fun t => ?_⟩
  have ht := h.somePath_mem t
  refine ⟨ht.1, ht.2, ?_⟩
  have hconn : IsPreconnected (Set.range γ) :=
    (isConnected_range γ.continuous).isPreconnected
  have hsub : Set.range γ ⊆ J.carrierᶜ := by
    rintro x ⟨u, hu⟩
    rw [← hu]
    exact (h.somePath_mem u).2
  have heq := J.index_eq_of_isPreconnected hconn hsub
    (P := P) (Q := γ t) ⟨0, γ.source⟩ ⟨t, rfl⟩
  exact heq.symm.trans hindex

/-- The precise output needed from Moise's informal strip construction.  The two gates are not
labelled as inside and outside: every strip-complement point merely has to be path-joinable to
one of them.  The crossing index subsequently proves that the gates lie on different sides, so
this interface also covers Moise's a priori "Möbius strip" possibility. -/
structure TwoGateStrip where
  /-- The open strip neighborhood. -/
  strip : Set Plane
  isOpen_strip : IsOpen strip
  carrier_subset : J.carrier ⊆ strip
  /-- Two candidate path-component representatives. -/
  gateA : Plane
  /-- The `gateB` declaration. -/
  gateB : Plane
  gateA_mem : gateA ∈ (strip \ J.carrier)
  gateB_mem : gateB ∈ (strip \ J.carrier)
  /-- Every point of the punctured strip reaches one of the two gates. -/
  reaches : ∀ {P : Plane}, P ∈ (strip \ J.carrier) →
    JoinedIn (strip \ J.carrier) gateA P ∨
      JoinedIn (strip \ J.carrier) gateB P
  /-- Both gate components accumulate on every point of the core polygon. -/
  gateA_approaches : J.carrier ⊆ closure
    {P | P ∈ (strip \ J.carrier) ∧ JoinedIn (strip \ J.carrier) gateA P}
  gateB_approaches : J.carrier ⊆ closure
    {P | P ∈ (strip \ J.carrier) ∧ JoinedIn (strip \ J.carrier) gateB P}

/-- The explicit polygon strip provides the two-gate local separation data used by the crossing
index argument. -/
noncomputable def StripScales.toTwoGateStrip (S : J.StripScales) : J.TwoGateStrip := by
  let F := J.stripForwardPieces S
  let B := J.stripBackwardPieces S
  have hF : IsPathConnected F := S.isPathConnected_stripForwardPieces J
  have hB : IsPathConnected B := S.isPathConnected_stripBackwardPieces J
  let gateA : Plane := hF.nonempty.some
  let gateB : Plane := hB.nonempty.some
  have hgateA : gateA ∈ F := hF.nonempty.some_mem
  have hgateB : gateB ∈ B := hB.nonempty.some_mem
  have hFsub : F ⊆ J.polygonStrip S.trim S.width \ J.carrier := by
    rw [J.polygonStrip_diff_carrier_eq_pieces S]
    exact Set.subset_union_left
  have hBsub : B ⊆ J.polygonStrip S.trim S.width \ J.carrier := by
    rw [J.polygonStrip_diff_carrier_eq_pieces S]
    exact Set.subset_union_right
  refine
    { strip := J.polygonStrip S.trim S.width
      isOpen_strip := J.isOpen_polygonStrip S.trim S.width
      carrier_subset := J.carrier_subset_polygonStrip S.trim_pos S.width_pos
      gateA := gateA
      gateB := gateB
      gateA_mem := hFsub hgateA
      gateB_mem := hBsub hgateB
      reaches := ?_
      gateA_approaches := ?_
      gateB_approaches := ?_ }
  · intro P hP
    rw [J.polygonStrip_diff_carrier_eq_pieces S] at hP
    rcases hP with hPF | hPB
    · exact Or.inl ((hF.joinedIn gateA hgateA P hPF).mono hFsub)
    · exact Or.inr ((hB.joinedIn gateB hgateB P hPB).mono hBsub)
  · intro x hx
    apply closure_mono _ (S.carrier_subset_closure_stripForwardPieces J hx)
    intro P hPF
    exact ⟨hFsub hPF, (hF.joinedIn gateA hgateA P hPF).mono hFsub⟩
  · intro x hx
    apply closure_mono _ (S.carrier_subset_closure_stripBackwardPieces J hx)
    intro P hPB
    exact ⟨hBsub hPB, (hB.joinedIn gateB hgateB P hPB).mono hBsub⟩

theorem exists_twoGateStrip : Nonempty J.TwoGateStrip := by
  let S := J.exists_stripScales.some
  exact ⟨S.toTwoGateStrip J⟩

/-- The path component represented by the first gate, written as an ambient set. -/
def TwoGateStrip.gateAComponent (S : J.TwoGateStrip) : Set Plane :=
  {P | P ∈ (S.strip \ J.carrier) ∧ JoinedIn (S.strip \ J.carrier) S.gateA P}

/-- The path component represented by the second gate, written as an ambient set. -/
def TwoGateStrip.gateBComponent (S : J.TwoGateStrip) : Set Plane :=
  {P | P ∈ (S.strip \ J.carrier) ∧ JoinedIn (S.strip \ J.carrier) S.gateB P}

theorem TwoGateStrip.gateAComponent_subset_indexRegion (S : J.TwoGateStrip) {k : ℕ}
    (hk : J.index S.gateA = k) : S.gateAComponent ⊆ J.indexRegion k := by
  rintro P ⟨hP, hjoin⟩
  have heq := J.index_eq_of_joinedIn_compl (hjoin.mono fun _ hx => hx.2)
  exact ⟨hP.2, heq.symm.trans hk⟩

theorem TwoGateStrip.gateBComponent_subset_indexRegion (S : J.TwoGateStrip) {k : ℕ}
    (hk : J.index S.gateB = k) : S.gateBComponent ⊆ J.indexRegion k := by
  rintro P ⟨hP, hjoin⟩
  have heq := J.index_eq_of_joinedIn_compl (hjoin.mono fun _ hx => hx.2)
  exact ⟨hP.2, heq.symm.trans hk⟩

/-- If gate A has index `k`, every carrier point belongs to the frontier of the index-`k`
region. -/
theorem TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateA
    (S : J.TwoGateStrip) {k : ℕ} (hk : J.index S.gateA = k) :
    J.carrier ⊆ frontier (J.indexRegion k) := by
  intro P hP
  rw [(J.isOpen_indexRegion k).frontier_eq]
  refine ⟨closure_mono (TwoGateStrip.gateAComponent_subset_indexRegion J S hk) ?_, ?_⟩
  · simpa only [TwoGateStrip.gateAComponent] using S.gateA_approaches hP
  · exact fun hPregion => hPregion.1 hP

/-- If gate B has index `k`, every carrier point belongs to the frontier of the index-`k`
region. -/
theorem TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateB
    (S : J.TwoGateStrip) {k : ℕ} (hk : J.index S.gateB = k) :
    J.carrier ⊆ frontier (J.indexRegion k) := by
  intro P hP
  rw [(J.isOpen_indexRegion k).frontier_eq]
  refine ⟨closure_mono (TwoGateStrip.gateBComponent_subset_indexRegion J S hk) ?_, ?_⟩
  · simpa only [TwoGateStrip.gateBComponent] using S.gateB_approaches hP
  · exact fun hPregion => hPregion.1 hP

/-- Every nonempty index region meets every open neighborhood of the polygon.  A point is joined
to the neighborhood by the visibility segment from `exists_segment_to_open_neighborhood`, and
the index is constant on that segment. -/
theorem indexRegion_inter_neighborhood_nonempty {N : Set Plane} (hN : IsOpen N)
    (hcarrierN : J.carrier ⊆ N) {k : ℕ} (hk : (J.indexRegion k).Nonempty) :
    (N ∩ J.indexRegion k).Nonempty := by
  obtain ⟨P, hPk⟩ := hk
  obtain ⟨Q, ⟨hQN, hQcarrier⟩, hsegment⟩ :=
    J.exists_segment_to_open_neighborhood hN hcarrierN hPk.1
  have hconn : IsPreconnected (segment ℝ P Q) := (convex_segment P Q).isPreconnected
  have hindex := J.index_eq_of_isPreconnected hconn hsegment
    (left_mem_segment ℝ P Q) (right_mem_segment ℝ P Q)
  exact ⟨Q, hQN, hQcarrier, hindex.symm.trans hPk.2⟩

/-- The crossing index rules out the a priori possibility that the punctured strip has only one
path component. -/
theorem TwoGateStrip.index_gateA_ne_index_gateB (S : J.TwoGateStrip) :
    J.index S.gateA ≠ J.index S.gateB := by
  obtain ⟨P₀, hP₀N, hP₀carrier, hP₀index⟩ :=
    J.indexRegion_inter_neighborhood_nonempty S.isOpen_strip S.carrier_subset
      J.indexRegion_zero_nonempty
  obtain ⟨P₁, hP₁N, hP₁carrier, hP₁index⟩ :=
    J.indexRegion_inter_neighborhood_nonempty S.isOpen_strip S.carrier_subset
      J.indexRegion_one_nonempty
  rcases S.reaches ⟨hP₀N, hP₀carrier⟩ with hA₀ | hB₀ <;>
    rcases S.reaches ⟨hP₁N, hP₁carrier⟩ with hA₁ | hB₁
  · have h01 := (J.index_eq_of_joinedIn_compl
        (hA₀.mono fun _ hx => hx.2)).symm.trans
        (J.index_eq_of_joinedIn_compl (hA₁.mono fun _ hx => hx.2))
    rw [hP₀index, hP₁index] at h01
    norm_num at h01
  · intro h
    have h0 := J.index_eq_of_joinedIn_compl (hA₀.mono fun _ hx => hx.2)
    have h1 := J.index_eq_of_joinedIn_compl (hB₁.mono fun _ hx => hx.2)
    have h01 : (0 : ℕ) = 1 :=
      hP₀index.symm.trans (h0.symm.trans (h.trans (h1.trans hP₁index)))
    omega
  · intro h
    have h0 := J.index_eq_of_joinedIn_compl (hB₀.mono fun _ hx => hx.2)
    have h1 := J.index_eq_of_joinedIn_compl (hA₁.mono fun _ hx => hx.2)
    have h01 : (0 : ℕ) = 1 :=
      hP₀index.symm.trans (h0.symm.trans (h.symm.trans (h1.trans hP₁index)))
    omega
  · have h01 := (J.index_eq_of_joinedIn_compl
        (hB₀.mono fun _ hx => hx.2)).symm.trans
        (J.index_eq_of_joinedIn_compl (hB₁.mono fun _ hx => hx.2))
    rw [hP₀index, hP₁index] at h01
    norm_num at h01

/-- Every point of the polygon is approached from the index-zero gate component. -/
theorem TwoGateStrip.frontier_indexRegion_zero (S : J.TwoGateStrip) :
    frontier (J.indexRegion 0) = J.carrier := by
  apply Set.Subset.antisymm J.frontier_indexRegion_zero_subset_carrier
  have hA := J.index_lt_two S.gateA
  have hB := J.index_lt_two S.gateB
  interval_cases hAi : J.index S.gateA <;> interval_cases hBi : J.index S.gateB
  · exact (TwoGateStrip.index_gateA_ne_index_gateB J S (hAi.trans hBi.symm)).elim
  · exact TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateA J S hAi
  · exact TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateB J S hBi
  · exact (TwoGateStrip.index_gateA_ne_index_gateB J S (hAi.trans hBi.symm)).elim

/-- Every point of the polygon is approached from the index-one gate component. -/
theorem TwoGateStrip.frontier_indexRegion_one (S : J.TwoGateStrip) :
    frontier (J.indexRegion 1) = J.carrier := by
  apply Set.Subset.antisymm J.frontier_indexRegion_one_subset_carrier
  have hA := J.index_lt_two S.gateA
  have hB := J.index_lt_two S.gateB
  interval_cases hAi : J.index S.gateA <;> interval_cases hBi : J.index S.gateB
  · exact (TwoGateStrip.index_gateA_ne_index_gateB J S (hAi.trans hBi.symm)).elim
  · exact TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateB J S hBi
  · exact TwoGateStrip.carrier_subset_frontier_indexRegion_of_gateA J S hAi
  · exact (TwoGateStrip.index_gateA_ne_index_gateB J S (hAi.trans hBi.symm)).elim

/-- The two index sides of a two-gate strip are path connected.  This is the formal form of the
last sentence in Moise Ch. 2, Thm. 1, Lemma 1: the index forces the two gates to represent the two
different strip components. -/
theorem TwoGateStrip.isPathConnected_indexRegion (S : J.TwoGateStrip) (k : ℕ)
    (hk : k = 0 ∨ k = 1) :
    IsPathConnected (S.strip ∩ J.indexRegion k) := by
  have hzero := J.indexRegion_inter_neighborhood_nonempty S.isOpen_strip
    S.carrier_subset J.indexRegion_zero_nonempty
  have hone := J.indexRegion_inter_neighborhood_nonempty S.isOpen_strip
    S.carrier_subset J.indexRegion_one_nonempty
  obtain ⟨P₀, hP₀N, hP₀carrier, hP₀index⟩ := hzero
  obtain ⟨P₁, hP₁N, hP₁carrier, hP₁index⟩ := hone
  have hgate_ne := S.index_gateA_ne_index_gateB
  rcases hk with rfl | rfl
  · rcases S.reaches ⟨hP₀N, hP₀carrier⟩ with hA₀ | hB₀
    · have hAindex : J.index S.gateA = 0 :=
        (J.index_eq_of_joinedIn_compl (hA₀.mono fun _ hx => hx.2)).trans hP₀index
      refine ⟨S.gateA, ⟨S.gateA_mem.1, S.gateA_mem.2, hAindex⟩, ?_⟩
      intro Q hQ
      rcases S.reaches ⟨hQ.1, hQ.2.1⟩ with hAQ | hBQ
      · exact PolygonalCircle.JoinedIn.mono_indexRegion J hAQ hAindex
      · have hBindex : J.index S.gateB = 0 :=
          (J.index_eq_of_joinedIn_compl (hBQ.mono fun _ hx => hx.2)).trans hQ.2.2
        exact (hgate_ne (hAindex.trans hBindex.symm)).elim
    · have hBindex : J.index S.gateB = 0 :=
        (J.index_eq_of_joinedIn_compl (hB₀.mono fun _ hx => hx.2)).trans hP₀index
      refine ⟨S.gateB, ⟨S.gateB_mem.1, S.gateB_mem.2, hBindex⟩, ?_⟩
      intro Q hQ
      rcases S.reaches ⟨hQ.1, hQ.2.1⟩ with hAQ | hBQ
      · have hAindex : J.index S.gateA = 0 :=
          (J.index_eq_of_joinedIn_compl (hAQ.mono fun _ hx => hx.2)).trans hQ.2.2
        exact (hgate_ne (hAindex.trans hBindex.symm)).elim
      · exact PolygonalCircle.JoinedIn.mono_indexRegion J hBQ hBindex
  · rcases S.reaches ⟨hP₁N, hP₁carrier⟩ with hA₁ | hB₁
    · have hAindex : J.index S.gateA = 1 :=
        (J.index_eq_of_joinedIn_compl (hA₁.mono fun _ hx => hx.2)).trans hP₁index
      refine ⟨S.gateA, ⟨S.gateA_mem.1, S.gateA_mem.2, hAindex⟩, ?_⟩
      intro Q hQ
      rcases S.reaches ⟨hQ.1, hQ.2.1⟩ with hAQ | hBQ
      · exact PolygonalCircle.JoinedIn.mono_indexRegion J hAQ hAindex
      · have hBindex : J.index S.gateB = 1 :=
          (J.index_eq_of_joinedIn_compl (hBQ.mono fun _ hx => hx.2)).trans hQ.2.2
        exact (hgate_ne (hAindex.trans hBindex.symm)).elim
    · have hBindex : J.index S.gateB = 1 :=
        (J.index_eq_of_joinedIn_compl (hB₁.mono fun _ hx => hx.2)).trans hP₁index
      refine ⟨S.gateB, ⟨S.gateB_mem.1, S.gateB_mem.2, hBindex⟩, ?_⟩
      intro Q hQ
      rcases S.reaches ⟨hQ.1, hQ.2.1⟩ with hAQ | hBQ
      · have hAindex : J.index S.gateA = 1 :=
          (J.index_eq_of_joinedIn_compl (hAQ.mono fun _ hx => hx.2)).trans hQ.2.2
        exact (hgate_ne (hAindex.trans hBindex.symm)).elim
      · exact PolygonalCircle.JoinedIn.mono_indexRegion J hBQ hBindex

/-- If one index side is preconnected inside an open strip neighborhood of the polygon, then the
whole index side is preconnected.  The proof joins arbitrary points to the strip using
`exists_segment_to_open_neighborhood`. -/
theorem isPreconnected_indexRegion_of_strip (k : ℕ) {N : Set Plane} (hN : IsOpen N)
    (hcarrierN : J.carrier ⊆ N) (hstrip : IsPreconnected (N ∩ J.indexRegion k)) :
    IsPreconnected (J.indexRegion k) := by
  apply isPreconnected_of_forall_pair
  intro P hPk Q hQk
  have hPk' := hPk
  have hQk' := hQk
  change P ∉ J.carrier ∧ J.index P = k at hPk'
  change Q ∉ J.carrier ∧ J.index Q = k at hQk'
  obtain ⟨P', ⟨hP'N, hP'carrier⟩, hsegP⟩ :=
    J.exists_segment_to_open_neighborhood hN hcarrierN hPk'.1
  obtain ⟨Q', ⟨hQ'N, hQ'carrier⟩, hsegQ⟩ :=
    J.exists_segment_to_open_neighborhood hN hcarrierN hQk'.1
  have hsegPconn : IsPreconnected (segment ℝ P P') :=
    (convex_segment P P').isPreconnected
  have hsegQconn : IsPreconnected (segment ℝ Q Q') :=
    (convex_segment Q Q').isPreconnected
  have hsegPregion : segment ℝ P P' ⊆ J.indexRegion k := by
    intro X hX
    have hindex := J.index_eq_of_isPreconnected hsegPconn hsegP
      (left_mem_segment ℝ P P') hX
    exact ⟨hsegP hX, hindex.symm.trans hPk'.2⟩
  have hsegQregion : segment ℝ Q Q' ⊆ J.indexRegion k := by
    intro X hX
    have hindex := J.index_eq_of_isPreconnected hsegQconn hsegQ
      (left_mem_segment ℝ Q Q') hX
    exact ⟨hsegQ hX, hindex.symm.trans hQk'.2⟩
  have hP'strip : P' ∈ N ∩ J.indexRegion k :=
    ⟨hP'N, hsegPregion (right_mem_segment ℝ P P')⟩
  have hQ'strip : Q' ∈ N ∩ J.indexRegion k :=
    ⟨hQ'N, hsegQregion (right_mem_segment ℝ Q Q')⟩
  let T := segment ℝ P P' ∪ (N ∩ J.indexRegion k) ∪ segment ℝ Q Q'
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · rintro X ((hX | hX) | hX)
    · exact hsegPregion hX
    · exact hX.2
    · exact hsegQregion hX
  · exact Or.inl (Or.inl (left_mem_segment ℝ P P'))
  · exact Or.inr (left_mem_segment ℝ Q Q')
  · apply IsPreconnected.union'
      ⟨Q', Or.inr hQ'strip, right_mem_segment ℝ Q Q'⟩
    · exact IsPreconnected.union'
        ⟨P', right_mem_segment ℝ P P', hP'strip⟩ hsegPconn hstrip
    · exact hsegQconn

/-- The index-one region is bounded.  Outside a ball containing the polygon, every point lies on
a large connected circle with a point above the polygon, where the index is zero. -/
theorem isBounded_indexRegion_one : Bornology.IsBounded (J.indexRegion 1) := by
  obtain ⟨R, hR⟩ := J.isCompact_carrier.isBounded.subset_closedBall (0 : Plane)
  set R₀ : ℝ := max R 0 with hR₀
  have hcarrier : J.carrier ⊆ Metric.closedBall (0 : Plane) R₀ := by
    intro P hP
    exact (hR hP).trans (le_max_left R 0)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R₀, ?_⟩
  intro P hP
  change P ∉ J.carrier ∧ J.index P = 1 at hP
  by_contra hPR
  have hRlt : R₀ < ‖P‖ := lt_of_not_ge hPR
  set r : ℝ := ‖P‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg P
  set Q : Plane := (WithLp.toLp 2 ![0, r] : Plane) with hQ
  have hQnorm : ‖Q‖ = r := by
    have hsquare : ‖Q‖ ^ 2 = r ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [Q, Fin.sum_univ_two]
    nlinarith [norm_nonneg Q]
  set S : Set Plane := Metric.sphere (0 : Plane) r with hS
  have hSconn : IsPreconnected S := by
    rw [hS]
    apply isPreconnected_sphere (E := Plane)
    rw [← Module.finrank_eq_rank]
    simp [Plane]
  have hPS : P ∈ S := by
    rw [hS, Metric.mem_sphere, dist_zero_right, hr]
  have hQS : Q ∈ S := by
    rw [hS, Metric.mem_sphere, dist_zero_right, hQnorm]
  have hSsub : S ⊆ J.carrierᶜ := by
    intro X hXS hXcarrier
    have hXle := hcarrier hXcarrier
    rw [Metric.mem_closedBall, dist_zero_right] at hXle
    have hXnorm : ‖X‖ = r := by
      simpa [hS, Metric.mem_sphere, dist_zero_right] using hXS
    rw [hXnorm] at hXle
    linarith
  have hQhigh : ∀ i : ZMod J.n, (J.vertex i) 1 < Q 1 := by
    intro i
    have hvle := hcarrier (J.vertex_mem_carrier i)
    rw [Metric.mem_closedBall, dist_zero_right] at hvle
    have hcoord := PiLp.norm_apply_le (p := 2) (J.vertex i) (1 : Fin 2)
    have hyle : (J.vertex i) 1 ≤ |(J.vertex i) 1| := le_abs_self _
    change |(J.vertex i) 1| ≤ ‖J.vertex i‖ at hcoord
    change (J.vertex i) 1 < r
    linarith
  have hQindex : J.index Q = 0 := J.index_eq_zero_of_high hQhigh
  have heq := J.index_eq_of_isPreconnected hSconn hSsub hPS hQS
  rw [hP.2, hQindex] at heq
  norm_num at heq

/-- **Moise Ch. 2, Thm. 1, Lemma 2**: the complement of a polygon is disconnected.  Proved from
the index machinery: the index-0 and index-1 loci are relatively open (local constancy), cover
the complement (the index is a parity), and are both nonempty. -/
theorem compl_carrier_not_isPreconnected : ¬ IsPreconnected (J.carrierᶜ : Set Plane) := by
  intro hconn
  obtain ⟨P₀, hP₀⟩ := J.indexRegion_zero_nonempty
  obtain ⟨P₁, hP₁⟩ := J.indexRegion_one_nonempty
  have hP₀' := hP₀
  have hP₁' := hP₁
  change P₀ ∉ J.carrier ∧ J.index P₀ = 0 at hP₀'
  change P₁ ∉ J.carrier ∧ J.index P₁ = 1 at hP₁'
  obtain ⟨Q, -, hQ0, hQ1⟩ := hconn (J.indexRegion 0) (J.indexRegion 1)
    (J.isOpen_indexRegion 0) (J.isOpen_indexRegion 1)
    (by rw [J.indexRegion_zero_union_one])
    ⟨P₀, hP₀'.1, hP₀⟩
    ⟨P₁, hP₁'.1, hP₁⟩
  exact Set.disjoint_left.1 J.disjoint_indexRegion_zero_one hQ0 hQ1

/-- Once the explicit two-gate strip has been constructed, all global parts of polygonal Jordan
follow from the crossing index and the visibility-to-strip lemma. -/
theorem polygonal_jordan_of_twoGateStrip (S : J.TwoGateStrip) :
    ∃ inside outside : Set Plane,
      IsOpen inside ∧ IsOpen outside ∧ Disjoint inside outside ∧
      inside ∪ outside = J.carrierᶜ ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      frontier inside = J.carrier ∧ frontier outside = J.carrier := by
  have hlocal₀ := TwoGateStrip.isPathConnected_indexRegion J S 0 (Or.inl rfl)
  have hlocal₁ := TwoGateStrip.isPathConnected_indexRegion J S 1 (Or.inr rfl)
  have hconn₀ : IsConnected (J.indexRegion 0) := ⟨J.indexRegion_zero_nonempty,
    J.isPreconnected_indexRegion_of_strip 0 S.isOpen_strip S.carrier_subset
      hlocal₀.isConnected.isPreconnected⟩
  have hconn₁ : IsConnected (J.indexRegion 1) := ⟨J.indexRegion_one_nonempty,
    J.isPreconnected_indexRegion_of_strip 1 S.isOpen_strip S.carrier_subset
      hlocal₁.isConnected.isPreconnected⟩
  refine ⟨J.indexRegion 1, J.indexRegion 0,
    J.isOpen_indexRegion 1, J.isOpen_indexRegion 0,
    J.disjoint_indexRegion_zero_one.symm, ?_, hconn₁, hconn₀,
    J.isBounded_indexRegion_one, J.not_isBounded_indexRegion_zero, ?_, ?_⟩
  · simpa [Set.union_comm] using J.indexRegion_zero_union_one
  · exact TwoGateStrip.frontier_indexRegion_one J S
  · exact TwoGateStrip.frontier_indexRegion_zero J S

/-- **Jordan curve theorem for polygons** (Moise Ch. 2, Thms. 1, 5, 6).

The complement of a polygon has exactly two connected components: a bounded interior and an
unbounded exterior, both open, and the polygon is the frontier of each.

Must-fail check: the statement forces `interior ∪ exterior = carrierᶜ` with both sides connected
and the frontiers equal to the carrier, so it cannot be satisfied by choosing junk open sets. -/
theorem polygonal_jordan :
    ∃ inside outside : Set Plane,
      IsOpen inside ∧ IsOpen outside ∧ Disjoint inside outside ∧
      inside ∪ outside = J.carrierᶜ ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      frontier inside = J.carrier ∧ frontier outside = J.carrier := by
  exact J.polygonal_jordan_of_twoGateStrip J.exists_twoGateStrip.some

/-- The interior region of a polygon (the bounded complementary component). -/
noncomputable def interiorRegion : Set Plane :=
  J.polygonal_jordan.choose

/-- The exterior region of a polygon (the unbounded complementary component). -/
noncomputable def exteriorRegion : Set Plane :=
  J.polygonal_jordan.choose_spec.choose

theorem isOpen_interiorRegion : IsOpen J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.1

theorem isOpen_exteriorRegion : IsOpen J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.1

theorem disjoint_interior_exterior : Disjoint J.interiorRegion J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.1

theorem interior_union_exterior : J.interiorRegion ∪ J.exteriorRegion = J.carrierᶜ :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.1

theorem isConnected_interiorRegion : IsConnected J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.1

theorem isConnected_exteriorRegion : IsConnected J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.1

theorem isBounded_interiorRegion : Bornology.IsBounded J.interiorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.1

theorem not_isBounded_exteriorRegion : ¬ Bornology.IsBounded J.exteriorRegion :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.1

theorem frontier_interiorRegion : frontier J.interiorRegion = J.carrier :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.2.1

theorem frontier_exteriorRegion : frontier J.exteriorRegion = J.carrier :=
  J.polygonal_jordan.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2

theorem exteriorRegion_eq_indexRegion_zero : J.exteriorRegion = J.indexRegion 0 := by
  have hExteriorSubset : J.exteriorRegion ⊆ J.indexRegion 0 := by
    have hsubset : J.exteriorRegion ⊆ J.indexRegion 0 ∪ J.indexRegion 1 := by
      rw [J.indexRegion_zero_union_one]
      intro x hx
      rw [← J.interior_union_exterior]
      exact Or.inr hx
    by_contra hnot
    obtain ⟨x, hxExterior, hxNotZero⟩ := Set.not_subset.mp hnot
    have hxOne := (hsubset hxExterior).resolve_left hxNotZero
    have hallOne : J.exteriorRegion ⊆ J.indexRegion 1 :=
      J.isConnected_exteriorRegion.isPreconnected.subset_right_of_subset_union
        (J.isOpen_indexRegion 0) (J.isOpen_indexRegion 1)
        J.disjoint_indexRegion_zero_one hsubset ⟨x, hxExterior, hxOne⟩
    exact J.not_isBounded_exteriorRegion (J.isBounded_indexRegion_one.subset hallOne)
  apply Set.Subset.antisymm hExteriorSubset
  have hsubset : J.indexRegion 0 ⊆ J.interiorRegion ∪ J.exteriorRegion := by
    rw [J.interior_union_exterior]
    intro x hx
    exact hx.1
  obtain ⟨x, hxExterior⟩ := J.isConnected_exteriorRegion.nonempty
  have hxZero := hExteriorSubset hxExterior
  let S := J.exists_twoGateStrip.some
  have hpre : IsPreconnected (J.indexRegion 0) :=
    J.isPreconnected_indexRegion_of_strip 0 S.isOpen_strip S.carrier_subset
    (TwoGateStrip.isPathConnected_indexRegion J S 0
      (Or.inl rfl)).isConnected.isPreconnected
  exact hpre.subset_right_of_subset_union J.isOpen_interiorRegion J.isOpen_exteriorRegion
    J.disjoint_interior_exterior hsubset ⟨x, hxZero, hxExterior⟩

theorem interiorRegion_eq_indexRegion_one : J.interiorRegion = J.indexRegion 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxCompl : x ∈ J.carrierᶜ := by
      rw [← J.interior_union_exterior]
      exact Or.inl hx
    rw [← J.indexRegion_zero_union_one] at hxCompl
    rcases hxCompl with hxZero | hxOne
    · rw [← J.exteriorRegion_eq_indexRegion_zero] at hxZero
      exact (Set.disjoint_left.mp J.disjoint_interior_exterior hx hxZero).elim
    · exact hxOne
  · intro x hx
    have hxCompl : x ∈ J.carrierᶜ := by
      rw [← J.indexRegion_zero_union_one]
      exact Or.inr hx
    rw [← J.interior_union_exterior] at hxCompl
    rcases hxCompl with hxInside | hxExterior
    · exact hxInside
    · rw [J.exteriorRegion_eq_indexRegion_zero] at hxExterior
      exact (Set.disjoint_left.mp J.disjoint_indexRegion_zero_one hxExterior hx).elim

/-- The closed region bounded by a polygon: the closure of its interior region. -/
noncomputable def closedRegion : Set Plane :=
  closure J.interiorRegion

theorem closedRegion_eq_union : J.closedRegion = J.interiorRegion ∪ J.carrier := by
  rw [closedRegion, closure_eq_self_union_frontier, J.frontier_interiorRegion]

theorem isCompact_closedRegion : IsCompact J.closedRegion :=
  J.isBounded_interiorRegion.isCompact_closure

end PolygonalCircle

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
