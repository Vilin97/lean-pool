/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex

/-!
# Intrinsic finite PL complexes

The complexes used during the Rado induction are not generally realized by straight triangles
in one global copy of the plane.  Their honest carrier is instead the canonical barycentric
realization `GeometricRealization`.  This file supplies the small intrinsic PL layer needed to
state chart-transition approximation and refinement without pretending that source is planar.

A subdivision contains a homeomorphism between the two canonical realizations, together with
facewise affine formulas and subordination to old faces.  Thus an arbitrary homeomorphism cannot
be installed as a subdivision by bookkeeping alone.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- A finite pure two-dimensional abstract simplicial complex.  Lower-dimensional faces are
implicit in the supports of the listed triangles, exactly as in `GeometricRealization`. -/
structure IntrinsicTwoComplex where
  /-- The `Vertex` declaration. -/
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The `faces` declaration. -/
  faces : Finset (Finset Vertex)
  faces_card : ∀ t ∈ faces, t.card = 3

attribute [instance] IntrinsicTwoComplex.vertexFintype
attribute [instance] IntrinsicTwoComplex.vertexDecidableEq

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- The canonical barycentric realization of an intrinsic complex. -/
abbrev realization : Type :=
  GeometricRealization K.Vertex K.faces

/-- The closed barycentric carrier of a vertex set. -/
def ambientFaceCarrier (t : Finset K.Vertex) : Set (K.Vertex → ℝ) :=
  {x | x ∈ stdSimplex ℝ K.Vertex ∧ ∀ v ∉ t, x v = 0}

/-- The carrier of a listed triangle as a subset of the realization. -/
def faceCarrier (t : Finset K.Vertex) : Set K.realization :=
  {x | ∀ v ∉ t, x.1 v = 0}

theorem mem_realization_iff (x : K.Vertex → ℝ) :
    x ∈ GeometricRealization K.Vertex K.faces ↔
      ∃ t ∈ K.faces, x ∈ K.ambientFaceCarrier t := by
  simp only [GeometricRealization, ambientFaceCarrier, Set.mem_ofPred_eq]
  tauto

theorem mem_faceCarrier_iff (t : Finset K.Vertex) (x : K.realization) :
    x ∈ K.faceCarrier t ↔ ∀ v ∉ t, x.1 v = 0 :=
  Iff.rfl

theorem faceCarrier_eq_preimage (t : Finset K.Vertex) :
    K.faceCarrier t = Subtype.val ⁻¹' K.ambientFaceCarrier t := by
  ext x
  simp only [faceCarrier, ambientFaceCarrier, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · exact fun hx => ⟨x.2.1, hx⟩
  · exact fun hx => hx.2

theorem faceCarrier_closed (t : Finset K.Vertex) : IsClosed (K.faceCarrier t) := by
  rw [K.faceCarrier_eq_preimage t]
  have hclosed : IsClosed (K.ambientFaceCarrier t) := by
    have hrepr : K.ambientFaceCarrier t =
        stdSimplex ℝ K.Vertex ∩ ⋂ v ∈ {v : K.Vertex | v ∉ t},
          {x : K.Vertex → ℝ | x v = 0} := by
      ext x
      simp [ambientFaceCarrier]
    rw [hrepr]
    exact (isClosed_stdSimplex ℝ K.Vertex).inter
      (isClosed_biInter fun v _ => isClosed_eq (continuous_apply v) continuous_const)
  exact hclosed.preimage continuous_subtype_val

theorem realization_eq_iUnion_faceCarrier :
    (Set.univ : Set K.realization) = ⋃ t : {t // t ∈ K.faces}, K.faceCarrier t.1 := by
  apply Set.Subset.antisymm
  · intro x _
    rcases x.2.2 with ⟨t, ht, hxt⟩
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩
  · exact Set.subset_univ _

/-- The intrinsic subcomplex obtained by retaining a selected family of maximal faces. -/
def restrictFaces (p : Finset K.Vertex → Prop) [DecidablePred p] : IntrinsicTwoComplex where
  Vertex := K.Vertex
  faces := K.faces.filter p
  faces_card := by
    intro t ht
    exact K.faces_card t (Finset.mem_filter.mp ht).1

@[simp] theorem restrictFaces_faces (p : Finset K.Vertex → Prop) [DecidablePred p] :
    (K.restrictFaces p).faces = K.faces.filter p := rfl

/-- The canonical inclusion of a face restriction into the old realization. -/
def restrictFacesInclusion (p : Finset K.Vertex → Prop)
    [decidablePred : DecidablePred p] :
    (K.restrictFaces p).realization → K.realization :=
  fun x => ⟨x.1, x.2.1, by
    rcases x.2.2 with ⟨t, ht, hxt⟩
    exact ⟨t, (@Finset.mem_filter _ p decidablePred _ _).mp ht |>.1, hxt⟩⟩

@[simp] theorem restrictFacesInclusion_val (p : Finset K.Vertex → Prop) [DecidablePred p]
    (x : (K.restrictFaces p).realization) :
    (K.restrictFacesInclusion p x).1 = x.1 := rfl

theorem isEmbedding_restrictFacesInclusion (p : Finset K.Vertex → Prop)
    [decidablePred : DecidablePred p] :
    _root_.Topology.IsEmbedding (K.restrictFacesInclusion p) := by
  have hsubset : GeometricRealization (K.restrictFaces p).Vertex
      (K.restrictFaces p).faces ⊆ GeometricRealization K.Vertex K.faces := by
    rintro x ⟨hxstd, t, ht, hxt⟩
    exact ⟨hxstd, t, (@Finset.mem_filter _ p decidablePred _ _).mp ht |>.1, hxt⟩
  convert _root_.Topology.IsEmbedding.inclusion hsubset using 1
  all_goals rfl

theorem restrictFacesInclusion_mem_faceCarrier_iff
    (p : Finset K.Vertex → Prop) [DecidablePred p]
    (t : Finset K.Vertex) (x : (K.restrictFaces p).realization) :
    K.restrictFacesInclusion p x ∈ K.faceCarrier t ↔
      x ∈ (K.restrictFaces p).faceCarrier t :=
  Iff.rfl

theorem restrictFacesInclusion_range (p : Finset K.Vertex → Prop)
    [decidablePred : DecidablePred p] :
    Set.range (K.restrictFacesInclusion p) =
      {x : K.realization | ∃ t ∈ K.faces, p t ∧ x ∈ K.faceCarrier t} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rcases y.2.2 with ⟨t, ht, hyt⟩
    have ht' := (@Finset.mem_filter _ p decidablePred _ _).mp ht
    exact ⟨t, ht'.1, ht'.2, hyt⟩
  · rintro ⟨t, ht, hpt, hxt⟩
    let y : (K.restrictFaces p).realization :=
      ⟨x.1, x.2.1,
        ⟨t, (@Finset.mem_filter _ p decidablePred _ _).mpr ⟨ht, hpt⟩, hxt⟩⟩
    exact ⟨y, Subtype.ext rfl⟩

/-! ## Intrinsic vertices and edges -/

/-- The edges of an intrinsic two-complex. -/
def edges : Finset (Finset K.Vertex) :=
  K.faces.biUnion fun t => t.powersetCard 2

/-- The abstract two-complex has surface edge valence when every edge is contained in at most
two maximal triangles. -/
def HasSurfaceEdgeValence : Prop :=
  ∀ e ∈ K.edges, (K.faces.filter fun t => e ⊆ t).card ≤ 2

theorem card_of_mem_edges {e : Finset K.Vertex} (he : e ∈ K.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

theorem exists_face_of_mem_edges {e : Finset K.Vertex} (he : e ∈ K.edges) :
    ∃ t ∈ K.faces, e ⊆ t := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact ⟨t, ht, (Finset.mem_powersetCard.mp het).1⟩

/-- The finite edge type. -/
abbrev Edge : Type := {e : Finset K.Vertex // e ∈ K.edges}

/-- The intrinsic one-skeleton, as the finite union of all barycentric edge carriers. -/
def oneSkeleton : Set K.realization :=
  {x | ∃ e : K.Edge, x ∈ K.faceCarrier e.1}

theorem mem_oneSkeleton_iff (x : K.realization) :
    x ∈ K.oneSkeleton ↔ ∃ e : K.Edge, x ∈ K.faceCarrier e.1 :=
  Iff.rfl

theorem faceCarrier_edge_subset_oneSkeleton (e : K.Edge) :
    K.faceCarrier e.1 ⊆ K.oneSkeleton :=
  fun _ hx => ⟨e, hx⟩

theorem oneSkeleton_eq_iUnion_faceCarrier :
    K.oneSkeleton = ⋃ e : K.Edge, K.faceCarrier e.1 := by
  ext x
  simp [oneSkeleton]

theorem oneSkeleton_closed : IsClosed K.oneSkeleton := by
  rw [K.oneSkeleton_eq_iUnion_faceCarrier]
  exact isClosed_iUnion_of_finite fun e => K.faceCarrier_closed e.1

/-! ### Cyclic data on a maximal face -/

/-- A maximal two-face of the intrinsic complex. -/
abbrev Face : Type := {t : Finset K.Vertex // t ∈ K.faces}

/-- A chosen cyclic enumeration of the three vertices of a maximal face. -/
noncomputable def faceVertexEquiv (t : K.Face) : Fin 3 ≃ t.1 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, K.faces_card t.1 t.2])

/-- Cyclically indexed vertices of a maximal face. -/
noncomputable def faceVertex (t : K.Face) (i : ZMod 3) : K.Vertex :=
  (K.faceVertexEquiv t ((ZMod.finEquiv 3).symm i)).1

theorem faceVertex_mem (t : K.Face) (i : ZMod 3) : K.faceVertex t i ∈ t.1 :=
  (K.faceVertexEquiv t ((ZMod.finEquiv 3).symm i)).2

theorem faceVertex_injective (t : K.Face) : Function.Injective (K.faceVertex t) := by
  intro i j hij
  apply (ZMod.finEquiv 3).symm.injective
  apply (K.faceVertexEquiv t).injective
  exact Subtype.ext hij

theorem faceVertex_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceVertex t i ≠ K.faceVertex t (i + 1) := by
  intro h
  have hi : i = i + 1 := K.faceVertex_injective t h
  have hone : (0 : ZMod 3) = 1 := by
    calc
      0 = i - i := by abel
      _ = (i + 1) - i := congrArg (fun z => z - i) hi
      _ = 1 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 1) hone

theorem faceVertex_ne_add_two (t : K.Face) (i : ZMod 3) :
    K.faceVertex t i ≠ K.faceVertex t (i + 2) := by
  intro h
  have hi : i = i + 2 := K.faceVertex_injective t h
  have htwo : (0 : ZMod 3) = 2 := by
    calc
      0 = i - i := by abel
      _ = (i + 2) - i := congrArg (fun z => z - i) hi
      _ = 2 := by abel
  exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- The intrinsic edge joining two consecutive cyclic vertices of a maximal face. -/
noncomputable def faceEdge (t : K.Face) (i : ZMod 3) : K.Edge := by
  refine ⟨{K.faceVertex t i, K.faceVertex t (i + 1)}, ?_⟩
  rw [edges]
  apply Finset.mem_biUnion.mpr
  refine ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact K.faceVertex_mem t i
    · exact K.faceVertex_mem t (i + 1)
  · simp [K.faceVertex_ne_next t i]

@[simp] theorem faceEdge_val (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 = {K.faceVertex t i, K.faceVertex t (i + 1)} := rfl

/-- The consecutive face edges share exactly their common cyclic vertex. -/
theorem faceEdge_inter_next (t : K.Face) (i : ZMod 3) :
    (K.faceEdge t i).1 ∩ (K.faceEdge t (i + 1)).1 =
      {K.faceVertex t (i + 1)} := by
  ext v
  simp only [faceEdge_val, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton, add_assoc, one_add_one_eq_two]
  constructor
  · rintro ⟨hvi | hvi, hvnext | hvtwo⟩
    · exact (K.faceVertex_ne_next t i (hvi.symm.trans hvnext)).elim
    · exact (K.faceVertex_ne_add_two t i (hvi.symm.trans hvtwo)).elim
    · exact hvi
    · exact hvi
  · intro hv
    exact ⟨Or.inr hv, Or.inl hv⟩

theorem faceEdge_ne_next (t : K.Face) (i : ZMod 3) :
    K.faceEdge t i ≠ K.faceEdge t (i + 1) := by
  intro h
  have hval := congrArg (fun e : K.Edge => e.1) h
  have hmem : K.faceVertex t i ∈ (K.faceEdge t (i + 1)).1 := by
    rw [← hval]
    simp
  simp only [faceEdge_val, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hi | hi
  · exact K.faceVertex_ne_next t i hi
  · have hz : i = i + 2 := K.faceVertex_injective t (by
        simpa only [one_add_one_eq_two, add_assoc] using hi)
    have htwo : (0 : ZMod 3) = 2 := by
      calc
        0 = i - i := by abel
        _ = (i + 2) - i := congrArg (fun z => z - i) hz
        _ = 2 := by abel
    exact (by decide : (0 : ZMod 3) ≠ 2) htwo

/-- Vertices which actually occur in a maximal face. -/
abbrev UsedVertex : Type := {v : K.Vertex // ∃ t ∈ K.faces, v ∈ t}

/-- A cyclic face vertex with explicit evidence that it occurs in the complex. -/
noncomputable def faceUsedVertex (t : K.Face) (i : ZMod 3) : K.UsedVertex :=
  ⟨K.faceVertex t i, t.1, t.2, K.faceVertex_mem t i⟩

/-- A chosen maximal face containing a used vertex. -/
noncomputable def usedVertexParent (v : K.UsedVertex) : Finset K.Vertex :=
  Classical.choose v.2

theorem usedVertexParent_mem (v : K.UsedVertex) : K.usedVertexParent v ∈ K.faces :=
  (Classical.choose_spec v.2).1

theorem usedVertex_mem_parent (v : K.UsedVertex) : v.1 ∈ K.usedVertexParent v :=
  (Classical.choose_spec v.2).2

/-- The canonical barycentric point of a used vertex. -/
noncomputable def vertexPoint (v : K.UsedVertex) : K.realization :=
  ⟨Pi.single v.1 1, single_mem_stdSimplex ℝ v.1, by
    refine ⟨K.usedVertexParent v, K.usedVertexParent_mem v, ?_⟩
    intro w hw
    have hwv : w ≠ v.1 := by
      intro h
      subst w
      exact hw (K.usedVertex_mem_parent v)
    simp [hwv]⟩

theorem injective_vertexPoint : Function.Injective K.vertexPoint := by
  intro v w hvw
  apply Subtype.ext
  by_contra hvw'
  have hcoord := congrArg (fun x : K.realization => x.1 v.1) hvw
  simp [vertexPoint, hvw'] at hcoord

theorem vertexPoint_mem_faceCarrier_iff (v : K.UsedVertex) (s : Finset K.Vertex) :
    K.vertexPoint v ∈ K.faceCarrier s ↔ v.1 ∈ s := by
  constructor
  · intro hv
    by_contra hvs
    have := hv v.1 hvs
    simp [vertexPoint] at this
  · intro hvs w hw
    have hwv : w ≠ v.1 := by
      intro h
      subst w
      exact hw hvs
    simp [vertexPoint, hwv]

/-- A chosen old face containing an edge. -/
noncomputable def edgeParent (e : K.Edge) : Finset K.Vertex :=
  Classical.choose (K.exists_face_of_mem_edges e.2)

theorem edgeParent_mem (e : K.Edge) : K.edgeParent e ∈ K.faces :=
  (Classical.choose_spec (K.exists_face_of_mem_edges e.2)).1

theorem edge_subset_parent (e : K.Edge) : e.1 ⊆ K.edgeParent e :=
  (Classical.choose_spec (K.exists_face_of_mem_edges e.2)).2

/-- The chosen first endpoint of an intrinsic edge. -/
noncomputable def edgeFirst (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose

/-- The chosen second endpoint of an intrinsic edge. -/
noncomputable def edgeSecond (e : K.Edge) : K.Vertex :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose

theorem edgeFirst_ne_edgeSecond (e : K.Edge) : K.edgeFirst e ≠ K.edgeSecond e :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose_spec.1

theorem edge_eq_pair (e : K.Edge) : e.1 = {K.edgeFirst e, K.edgeSecond e} :=
  (Finset.card_eq_two.mp (K.card_of_mem_edges e.2)).choose_spec.choose_spec.2

theorem edgeFirst_mem (e : K.Edge) : K.edgeFirst e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

theorem edgeSecond_mem (e : K.Edge) : K.edgeSecond e ∈ e.1 := by
  rw [K.edge_eq_pair e]
  simp

/-- The canonical barycentric realization point associated to a vertex of an edge. -/
noncomputable def edgeVertexPoint (e : K.Edge) (v : K.Vertex) (hv : v ∈ e.1) :
    K.realization :=
  ⟨Pi.single v 1, single_mem_stdSimplex ℝ v, by
    refine ⟨K.edgeParent e, K.edgeParent_mem e, ?_⟩
    intro w hw
    have hwv : w ≠ v := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e hv)
    simp [hwv]⟩

theorem edgeVertexPoint_eq_vertexPoint (e : K.Edge) (v : K.Vertex) (hv : v ∈ e.1) :
    K.edgeVertexPoint e v hv = K.vertexPoint
      ⟨v, K.edgeParent e, K.edgeParent_mem e, K.edge_subset_parent e hv⟩ := by
  apply Subtype.ext
  rfl

/-- Canonical first endpoint in the barycentric realization. -/
noncomputable def edgeFirstPoint (e : K.Edge) : K.realization :=
  K.edgeVertexPoint e (K.edgeFirst e) (K.edgeFirst_mem e)

/-- Canonical second endpoint in the barycentric realization. -/
noncomputable def edgeSecondPoint (e : K.Edge) : K.realization :=
  K.edgeVertexPoint e (K.edgeSecond e) (K.edgeSecond_mem e)

/-- The first endpoint as a used vertex. -/
noncomputable def edgeFirstUsed (e : K.Edge) : K.UsedVertex :=
  ⟨K.edgeFirst e, K.edgeParent e, K.edgeParent_mem e,
    K.edge_subset_parent e (K.edgeFirst_mem e)⟩

/-- The second endpoint as a used vertex. -/
noncomputable def edgeSecondUsed (e : K.Edge) : K.UsedVertex :=
  ⟨K.edgeSecond e, K.edgeParent e, K.edgeParent_mem e,
    K.edge_subset_parent e (K.edgeSecond_mem e)⟩

theorem edgeFirstUsed_ne_edgeSecondUsed (e : K.Edge) :
    K.edgeFirstUsed e ≠ K.edgeSecondUsed e := by
  intro h
  exact K.edgeFirst_ne_edgeSecond e (congrArg Subtype.val h)

theorem vertexPoint_edgeFirstUsed (e : K.Edge) :
    K.vertexPoint (K.edgeFirstUsed e) = K.edgeFirstPoint e := by
  apply Subtype.ext
  rfl

theorem vertexPoint_edgeSecondUsed (e : K.Edge) :
    K.vertexPoint (K.edgeSecondUsed e) = K.edgeSecondPoint e := by
  apply Subtype.ext
  rfl

/-- The canonical first endpoint depends only on its underlying used vertex, not on the chosen
maximal face witnessing that the vertex is used. -/
theorem edgeFirstPoint_eq_vertexPoint_of_eq (e : K.Edge) (v : K.UsedVertex)
    (h : K.edgeFirst e = v.1) :
    K.edgeFirstPoint e = K.vertexPoint v := by
  apply Subtype.ext
  simp [edgeFirstPoint, edgeVertexPoint, vertexPoint, h]

/-- The analogous proof-independence statement for the second endpoint. -/
theorem edgeSecondPoint_eq_vertexPoint_of_eq (e : K.Edge) (v : K.UsedVertex)
    (h : K.edgeSecond e = v.1) :
    K.edgeSecondPoint e = K.vertexPoint v := by
  apply Subtype.ext
  simp [edgeSecondPoint, edgeVertexPoint, vertexPoint, h]

/-- The arbitrary endpoint ordering of a cyclic face edge is one of its two cyclic
orientations. -/
theorem faceEdge_endpoint_order (t : K.Face) (i : ZMod 3) :
    (K.edgeFirst (K.faceEdge t i) = K.faceVertex t i ∧
        K.edgeSecond (K.faceEdge t i) = K.faceVertex t (i + 1)) ∨
      (K.edgeFirst (K.faceEdge t i) = K.faceVertex t (i + 1) ∧
        K.edgeSecond (K.faceEdge t i) = K.faceVertex t i) := by
  have hfirst := K.edgeFirst_mem (K.faceEdge t i)
  have hsecond := K.edgeSecond_mem (K.faceEdge t i)
  rw [K.faceEdge_val t i] at hfirst hsecond
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;> rcases hsecond with hsecond | hsecond
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge t i) (hfirst.trans hsecond.symm)).elim
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst, hsecond⟩
  · exact (K.edgeFirst_ne_edgeSecond (K.faceEdge t i) (hfirst.trans hsecond.symm)).elim

/-- The canonical interval parametrization of an intrinsic edge. -/
noncomputable def edgePath (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) : K.realization := by
  let x := AffineMap.lineMap (K.edgeFirstPoint e).1 (K.edgeSecondPoint e).1 r.1
  refine ⟨x, ?_, ?_⟩
  · exact convex_stdSimplex ℝ K.Vertex |>.lineMap_mem
      (K.edgeFirstPoint e).2.1 (K.edgeSecondPoint e).2.1 r.2
  · refine ⟨K.edgeParent e, K.edgeParent_mem e, ?_⟩
    intro w hw
    have hwFirst : w ≠ K.edgeFirst e := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e (K.edgeFirst_mem e))
    have hwSecond : w ≠ K.edgeSecond e := by
      intro h
      subst w
      exact hw (K.edge_subset_parent e (K.edgeSecond_mem e))
    simp [x, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
      AffineMap.lineMap_apply_module, hwFirst, hwSecond]

theorem continuous_edgePath (e : K.Edge) : Continuous (K.edgePath e) := by
  apply Continuous.subtype_mk
  exact (AffineMap.lineMap (k := ℝ) (K.edgeFirstPoint e).1
    (K.edgeSecondPoint e).1).continuous_of_finiteDimensional.comp continuous_subtype_val

theorem edgePath_zero (e : K.Edge) :
    K.edgePath e ⟨0, by simp⟩ = K.edgeFirstPoint e := by
  apply Subtype.ext
  simp [edgePath, AffineMap.lineMap_apply_module]

theorem edgePath_one (e : K.Edge) :
    K.edgePath e ⟨1, by simp⟩ = K.edgeSecondPoint e := by
  apply Subtype.ext
  simp [edgePath, AffineMap.lineMap_apply_module]

@[simp] theorem edgePath_apply_first (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePath e r).1 (K.edgeFirst e) = 1 - r.1 := by
  simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
    AffineMap.lineMap_apply_module, K.edgeFirst_ne_edgeSecond e]

@[simp] theorem edgePath_apply_second (e : K.Edge) (r : Set.Icc (0 : ℝ) 1) :
    (K.edgePath e r).1 (K.edgeSecond e) = r.1 := by
  simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
    AffineMap.lineMap_apply_module, K.edgeFirst_ne_edgeSecond e]

theorem injective_edgePath (e : K.Edge) : Function.Injective (K.edgePath e) := by
  intro r s hrs
  apply Subtype.ext
  have hcoord := congrArg (fun x : K.realization => x.1 (K.edgeSecond e)) hrs
  simpa using hcoord

/-- An ambient map restricted to the canonical interval of one intrinsic edge. -/
noncomputable def mappedEdgePath (h : K.realization → Plane) (e : K.Edge) :
    Set.Icc (0 : ℝ) 1 → Plane :=
  h ∘ K.edgePath e

theorem continuous_mappedEdgePath {h : K.realization → Plane} (hh : Continuous h)
    (e : K.Edge) : Continuous (K.mappedEdgePath h e) :=
  hh.comp (K.continuous_edgePath e)

theorem injective_mappedEdgePath {h : K.realization → Plane} (hh : Function.Injective h)
    (e : K.Edge) : Function.Injective (K.mappedEdgePath h e) :=
  hh.comp (K.injective_edgePath e)

theorem mappedEdgePath_zero (h : K.realization → Plane) (e : K.Edge) :
    K.mappedEdgePath h e ⟨0, by simp⟩ = h (K.edgeFirstPoint e) := by
  change h (K.edgePath e ⟨0, by simp⟩) = _
  rw [K.edgePath_zero e]

theorem mappedEdgePath_one (h : K.realization → Plane) (e : K.Edge) :
    K.mappedEdgePath h e ⟨1, by simp⟩ = h (K.edgeSecondPoint e) := by
  change h (K.edgePath e ⟨1, by simp⟩) = _
  rw [K.edgePath_one e]

/-- Intrinsic face carriers meet exactly in the carrier of the common vertex set. -/
theorem faceCarrier_inter (s t : Finset K.Vertex) :
    K.faceCarrier s ∩ K.faceCarrier t = K.faceCarrier (s ∩ t) := by
  ext x
  constructor
  · rintro ⟨hs, ht⟩ v hv
    simp only [Finset.mem_inter, not_and_or] at hv
    exact hv.elim (hs v) (ht v)
  · intro hst
    constructor
    · intro v hv
      exact hst v (by simp [hv])
    · intro v hv
      exact hst v (by simp [hv])

/-- The canonical interval path covers exactly the barycentric carrier of its edge. -/
theorem range_edgePath (e : K.Edge) :
    Set.range (K.edgePath e) = K.faceCarrier e.1 := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩ v hv
    have hvFirst : v ≠ K.edgeFirst e := by
      intro h
      subst v
      exact hv (K.edgeFirst_mem e)
    have hvSecond : v ≠ K.edgeSecond e := by
      intro h
      subst v
      exact hv (K.edgeSecond_mem e)
    simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
      AffineMap.lineMap_apply_module, hvFirst, hvSecond]
  · intro hx
    let r : Set.Icc (0 : ℝ) 1 :=
      ⟨x.1 (K.edgeSecond e), mem_Icc_of_mem_stdSimplex x.2.1 (K.edgeSecond e)⟩
    refine ⟨r, Subtype.ext ?_⟩
    funext v
    by_cases hvFirst : v = K.edgeFirst e
    · subst v
      rw [K.edgePath_apply_first]
      have hsumPair : x.1 (K.edgeFirst e) + x.1 (K.edgeSecond e) = 1 := by
        calc
          x.1 (K.edgeFirst e) + x.1 (K.edgeSecond e) = ∑ w ∈ e.1, x.1 w := by
            rw [K.edge_eq_pair e]
            simp [K.edgeFirst_ne_edgeSecond e]
          _ = ∑ w, x.1 w := Finset.sum_subset (Finset.subset_univ e.1)
            (fun w _ hw => hx w hw)
          _ = 1 := x.2.1.2
      dsimp [r]
      linarith
    · by_cases hvSecond : v = K.edgeSecond e
      · subst v
        rw [K.edgePath_apply_second]
      · have hv : v ∉ e.1 := by
          rw [K.edge_eq_pair e]
          simp [hvFirst, hvSecond]
        rw [hx v hv]
        simp [edgePath, edgeFirstPoint, edgeSecondPoint, edgeVertexPoint,
          AffineMap.lineMap_apply_module, hvFirst, hvSecond]

/-- The open barycentric carriers of distinct intrinsic edges are disjoint. -/
theorem disjoint_edgePath_image_Ioo {e d : K.Edge} (hed : e ≠ d) :
    Disjoint (K.edgePath e '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1})
      (K.edgePath d '' {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1}) := by
  rw [Set.disjoint_left]
  rintro x ⟨r, hr, rfl⟩ ⟨s, hs, hpaths⟩
  change 0 < r.1 ∧ r.1 < 1 at hr
  change 0 < s.1 ∧ s.1 < 1 at hs
  have hsCarrier : K.edgePath d s ∈ K.faceCarrier d.1 := by
    rw [← K.range_edgePath d]
    exact ⟨s, rfl⟩
  have hedSubset : e.1 ⊆ d.1 := by
    intro v hv
    by_contra hvd
    have hzero : (K.edgePath d s).1 v = 0 := hsCarrier v hvd
    have hcoord := congrArg (fun y : K.realization => y.1 v) hpaths
    have hpositive : 0 < (K.edgePath e r).1 v := by
      rw [K.edge_eq_pair e] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · rw [K.edgePath_apply_first]
        exact sub_pos.mpr hr.2
      · rw [K.edgePath_apply_second]
        exact hr.1
    linarith
  have hedge : e.1 = d.1 := Finset.eq_of_subset_of_card_le hedSubset (by
    rw [K.card_of_mem_edges e.2, K.card_of_mem_edges d.2])
  exact hed (Subtype.ext hedge)

theorem faceCarrier_empty : K.faceCarrier ∅ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hsum := x.2.1.2
  have hzero : ∀ v, x.1 v = 0 := by
    intro v
    exact hx v (Finset.notMem_empty v)
  simp_rw [hzero] at hsum
  norm_num at hsum

/-- A realization point supported on one used vertex is its canonical vertex point. -/
theorem eq_vertexPoint_of_mem_faceCarrier_singleton
    (v : K.UsedVertex) (x : K.realization)
    (hx : x ∈ K.faceCarrier ({v.1} : Finset K.Vertex)) :
    x = K.vertexPoint v := by
  have hxv : x.1 v.1 = 1 := by
    have hsum := x.2.1.2
    rw [Finset.sum_eq_single v.1] at hsum
    · exact hsum
    · intro w _ hwv
      exact hx w (by simp [hwv])
    · intro hv
      exact False.elim (hv (Finset.mem_univ v.1))
  apply Subtype.ext
  funext w
  by_cases hwv : w = v.1
  · subst w
    simp [vertexPoint, hxv]
  · simp [vertexPoint, hwv, hx w (by simp [hwv])]

/-- A nonempty barycentric carrier with at most one vertex, contained in a listed face,
consists of one canonical vertex point. -/
theorem exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
    (t : K.Face) {s : Finset K.Vertex} (hst : s ⊆ t.1)
    (hcard : s.card ≤ 1) {x : K.realization}
    (hx : x ∈ K.faceCarrier s) :
    ∃ v : K.UsedVertex, x = K.vertexPoint v := by
  have hsNonempty : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    subst s
    rw [K.faceCarrier_empty] at hx
    exact hx
  have hsCard : s.card = 1 := by
    have := Finset.card_pos.mpr hsNonempty
    omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsCard
  have hvt : v ∈ t.1 := hst (by simp)
  let vUsed : K.UsedVertex := ⟨v, t.1, t.2, hvt⟩
  exact ⟨vUsed, K.eq_vertexPoint_of_mem_faceCarrier_singleton vUsed x (by
    simpa [vUsed] using hx)⟩

/-- Exact range of an intrinsic edge after applying an ambient map. -/
theorem range_mappedEdgePath (h : K.realization → Plane) (e : K.Edge) :
    Set.range (K.mappedEdgePath h e) = h '' K.faceCarrier e.1 := by
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    have hr : K.edgePath e r ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨r, rfl⟩
    exact ⟨K.edgePath e r, hr, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← K.range_edgePath e] at hx
    rcases hx with ⟨r, rfl⟩
    exact ⟨r, rfl⟩

theorem isCompact_range_mappedEdgePath {h : K.realization → Plane} (hh : Continuous h)
    (e : K.Edge) : IsCompact (Set.range (K.mappedEdgePath h e)) := by
  exact isCompact_range (K.continuous_mappedEdgePath hh e)

/-- Nonincident intrinsic edges have disjoint ranges under an injective map. -/
theorem disjoint_range_mappedEdgePath {h : K.realization → Plane}
    (hh : Function.Injective h) {e d : K.Edge} (hed : Disjoint e.1 d.1) :
    Disjoint (Set.range (K.mappedEdgePath h e))
      (Set.range (K.mappedEdgePath h d)) := by
  rw [K.range_mappedEdgePath h e, K.range_mappedEdgePath h d,
    Set.disjoint_iff_inter_eq_empty, ← Set.image_inter hh,
    K.faceCarrier_inter e.1 d.1]
  have hinter : e.1 ∩ d.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hed
  rw [hinter, K.faceCarrier_empty, Set.image_empty]

/-- `f` is affine on an intrinsic set when it is the restriction of an ambient affine map in
barycentric coordinates. -/
def IsAffineOnSetTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) (A : Set K.realization) : Prop :=
  ∃ a : (K.Vertex → ℝ) →ᵃ[ℝ] E,
    ∀ x : K.realization, x ∈ A → f x = a x.1

/-- Restrict an intrinsic affine-on-set certificate to a smaller source set. -/
theorem IsAffineOnSetTo.mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : K.realization → E} {A B : Set K.realization}
    (hf : K.IsAffineOnSetTo f A) (hBA : B ⊆ A) :
    K.IsAffineOnSetTo f B := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun x hx => ha x (hBA hx)⟩

/-- The plane-target specialization of intrinsic affinity on an arbitrary set. -/
abbrev IsAffineOnSet (f : K.realization → Plane) (A : Set K.realization) : Prop :=
  K.IsAffineOnSetTo f A

/-- Intrinsic affine-on-set maps to the plane are continuous on that set. -/
theorem IsAffineOnSet.continuousOn {f : K.realization → Plane}
    {A : Set K.realization} (hf : K.IsAffineOnSet f A) :
    ContinuousOn f A := by
  obtain ⟨a, ha⟩ := hf
  exact (a.continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
    fun x hx => ha x hx

/-- `f` is affine on one intrinsic face when it is the restriction of an ambient affine map in
barycentric coordinates. -/
def IsAffineOnFaceTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) (t : Finset K.Vertex) : Prop :=
  ∃ a : (K.Vertex → ℝ) →ᵃ[ℝ] E,
    ∀ x : K.realization, x ∈ K.faceCarrier t → f x = a x.1

/-- The plane-target specialization used by PL approximation. -/
abbrev IsAffineOnFace (f : K.realization → Plane) (t : Finset K.Vertex) : Prop :=
  K.IsAffineOnFaceTo f t

theorem IsAffineOnFace.continuousOn {f : K.realization → Plane}
    {t : Finset K.Vertex} (hf : K.IsAffineOnFace f t) :
    ContinuousOn f (K.faceCarrier t) := by
  obtain ⟨a, ha⟩ := hf
  exact (a.continuous_of_finiteDimensional.comp continuous_subtype_val).continuousOn.congr
    fun x hx => ha x hx

/-- A faithful intrinsic subdivision.  The refined realization is homeomorphic to the original;
the homeomorphism is affine on each refined face and carries that face into an old face. -/
structure Subdivision where
  /-- The `refined` declaration. -/
  refined : IntrinsicTwoComplex
  /-- The `homeo` declaration. -/
  homeo : refined.realization ≃ₜ K.realization
  affineOnFace : ∀ t ∈ refined.faces,
    ∃ a : (refined.Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : refined.realization, x ∈ refined.faceCarrier t → (homeo x).1 = a x.1
  subordinate : ∀ t ∈ refined.faces,
    ∃ u ∈ K.faces, ∀ x : refined.realization,
      x ∈ refined.faceCarrier t → homeo x ∈ K.faceCarrier u

namespace Subdivision

/-- Every intrinsic complex is a subdivision of itself. -/
noncomputable def refl : K.Subdivision where
  refined := K
  homeo := Homeomorph.refl K.realization
  affineOnFace := by
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl
  subordinate := by
    intro t ht
    exact ⟨t, ht, fun x hx => hx⟩

@[simp] theorem refl_refined : (refl K).refined = K := rfl


/-- Faithful intrinsic subdivisions compose. -/
noncomputable def trans {K : IntrinsicTwoComplex}
    (R : K.Subdivision) (Q : R.refined.Subdivision) : K.Subdivision where
  refined := Q.refined
  homeo := Q.homeo.trans R.homeo
  affineOnFace := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := Q.subordinate t ht
    obtain ⟨a, ha⟩ := Q.affineOnFace t ht
    obtain ⟨b, hb⟩ := R.affineOnFace u hu
    refine ⟨b.comp a, ?_⟩
    intro x hx
    rw [AffineMap.comp_apply]
    change (R.homeo (Q.homeo x)).1 = b (a x.1)
    rw [hb (Q.homeo x) (htu x hx), ha x hx]
  subordinate := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := Q.subordinate t ht
    obtain ⟨s, hs, hus⟩ := R.subordinate u hu
    exact ⟨s, hs, fun x hx => hus (Q.homeo x) (htu x hx)⟩

@[simp] theorem trans_refined (R : K.Subdivision) (Q : R.refined.Subdivision) :
    (R.trans Q).refined = Q.refined := rfl

theorem trans_homeo_apply (R : K.Subdivision) (Q : R.refined.Subdivision)
    (x : Q.refined.realization) :
    (R.trans Q).homeo x = R.homeo (Q.homeo x) := rfl

end Subdivision

/-- A map from an intrinsic complex to the plane is PL when it becomes affine on every face of
a faithful finite subdivision. -/
def IsPLMap (f : K.realization → Plane) : Prop :=
  ∃ R : K.Subdivision,
    ∀ t ∈ R.refined.faces, R.refined.IsAffineOnFace (f ∘ R.homeo) t

/-- The target-vector-space form of intrinsic piecewise linearity. -/
def IsPLMapTo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : K.realization → E) : Prop :=
  ∃ R : K.Subdivision,
    ∀ t ∈ R.refined.faces, R.refined.IsAffineOnFaceTo (f ∘ R.homeo) t

theorem isPLMap_iff_isPLMapTo (f : K.realization → Plane) :
    K.IsPLMap f ↔ K.IsPLMapTo f :=
  Iff.rfl

namespace IsPLMap

/-- Intrinsic PL maps into the plane are continuous.  Continuity is glued over the finite family
of closed refined faces and transported back through the subdivision homeomorphism. -/
theorem continuous {f : K.realization → Plane} (hf : K.IsPLMap f) : Continuous f := by
  obtain ⟨R, hR⟩ := hf
  have hclosed : ∀ t : {t // t ∈ R.refined.faces},
      IsClosed (R.refined.faceCarrier t.1) :=
    fun t => R.refined.faceCarrier_closed t.1
  have hlocal : ∀ t : {t // t ∈ R.refined.faces},
      ContinuousOn (f ∘ R.homeo) (R.refined.faceCarrier t.1) :=
    fun t => (hR t.1 t.2).continuousOn
  let carriers : {t // t ∈ R.refined.faces} → Set R.refined.realization :=
    fun t => R.refined.faceCarrier t.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hcomp : Continuous (f ∘ R.homeo) :=
    hfinite.continuous R.refined.realization_eq_iUnion_faceCarrier.symm hclosed hlocal
  simpa only [Function.comp_def, R.homeo.apply_symm_apply] using
    hcomp.comp R.homeo.symm.continuous

end IsPLMap

/-- A globally affine map in barycentric coordinates is intrinsically PL. -/
theorem isPLMap_of_affine (f : K.realization → Plane)
    (a : (K.Vertex → ℝ) →ᵃ[ℝ] Plane)
    (ha : ∀ x : K.realization, f x = a x.1) : K.IsPLMap f := by
  refine ⟨Subdivision.refl K, ?_⟩
  intro t ht
  exact ⟨a, fun x hx => ha x⟩

/-- The affine barycentric map determined by positions assigned to the vertices. -/
noncomputable def barycentricMap (p : K.Vertex → Plane) (x : K.realization) : Plane :=
  ∑ v, x.1 v • p v

theorem barycentricMap_isPL (p : K.Vertex → Plane) :
    K.IsPLMap (K.barycentricMap p) := by
  let a : (K.Vertex → ℝ) →ₗ[ℝ] Plane :=
    ∑ v, (LinearMap.proj v).smulRight (p v)
  refine K.isPLMap_of_affine (K.barycentricMap p) a.toAffineMap ?_
  intro x
  simp [barycentricMap, a]

/-- A homeomorphism of canonical realizations that is intrinsically PL in both directions. -/
structure PLHomeomorph (L : IntrinsicTwoComplex) where
  /-- The `toHomeomorph` declaration. -/
  toHomeomorph : K.realization ≃ₜ L.realization
  isPL_to : K.IsPLMapTo (fun x => (toHomeomorph x).1)
  isPL_inv : L.IsPLMapTo (fun x => (toHomeomorph.symm x).1)

namespace PLHomeomorph

/-- The identity intrinsic PL homeomorphism. -/
noncomputable def refl : K.PLHomeomorph K where
  toHomeomorph := Homeomorph.refl K.realization
  isPL_to := by
    refine ⟨Subdivision.refl K, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl
  isPL_inv := by
    refine ⟨Subdivision.refl K, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (K.Vertex → ℝ), ?_⟩
    intro x hx
    rfl

@[simp] theorem refl_apply (x : K.realization) : (refl K).toHomeomorph x = x := rfl

end PLHomeomorph

/-- A faithful subdivision is itself a PL homeomorphism between the refined and original
realizations.  For the inverse direction, use the same subdivision as the witness: after
precomposition with its homeomorphism the inverse is the identity. -/
noncomputable def Subdivision.toPLHomeomorph (R : K.Subdivision) :
    R.refined.PLHomeomorph K where
  toHomeomorph := R.homeo
  isPL_to := by
    refine ⟨Subdivision.refl R.refined, ?_⟩
    intro t ht
    obtain ⟨a, ha⟩ := R.affineOnFace t ht
    exact ⟨a, fun x hx => ha x hx⟩
  isPL_inv := by
    refine ⟨R, ?_⟩
    intro t ht
    refine ⟨AffineMap.id ℝ (R.refined.Vertex → ℝ), ?_⟩
    intro x hx
    exact congrArg Subtype.val (R.homeo.symm_apply_apply x)

/-- A PL map on a refinement is PL on the original intrinsic complex. -/
theorem IsPLMap.of_subdivision (R : K.Subdivision) {f : K.realization → Plane}
    (hf : R.refined.IsPLMap (f ∘ R.homeo)) : K.IsPLMap f := by
  obtain ⟨Q, hQ⟩ := hf
  refine ⟨R.trans Q, ?_⟩
  intro t ht
  change Q.refined.IsAffineOnFace (fun x => f (R.homeo (Q.homeo x))) t
  exact hQ t ht

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
