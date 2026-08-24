/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import Mathlib.Topology.Metrizable.Urysohn
import LeanPool.ClassificationOfSurfaces.Moise.ChartPatch
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicCellwiseExtension
import LeanPool.ClassificationOfSurfaces.Moise.FineSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveTriangulation
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveFanAffine
import LeanPool.ClassificationOfSurfaces.Moise.EmbeddedComplexValence
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicMarkedFan
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveControlledApproximation
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation
import LeanPool.ClassificationOfSurfaces.Moise.FrontierGlue
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalFamilyPolyhedron
import LeanPool.ClassificationOfSurfaces.Moise.RelativeSynchronizedArrangement

/-!
# The Radó chart induction

The skeleton of Moise Ch. 8 (the triangulation theorem for 2-manifolds), extended to bordered
surfaces as required by the Eval statement.

Moise's proof of Thm. 8.3 (Radó): cover the surface by chart pairs (Thm. 8.1; finitely many, by
compactness), and build an increasing sequence of embedded complexes, absorbing one chart core at
each step.  The step adjusts the new chart's polyhedral disk by a PL approximation (Thm. 6.3,
`pl_approximation_two_manifold`) so that it meets the already-built complex simplicially
(conditions (a)-(h) in Moise's proof), and glues (Thm. 7.6).

This file provides the honest objects for that induction:

* `PartialTriangulation S` — an embedded finite complex that need not cover `S`; its realization
  is computed from the combinatorial data exactly as in `GeometricTriangulation`, so junk
  witnesses cannot inhabit it;
* `MoiseChart S` — a disk or half-disk chart with an explicit compact core;
* `moise_finite_chart_cover` — the finite chart-core cover (Moise Thm. 8.1 plus compactness);
* `RadoInvariant` and `moise_induction_step` — the boundary-aware absorption invariant and the
  complete one-chart step;
* `moise_triangulation_of_boundaries` — the finite induction and final geometric realization.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open InvarianceOfDomain

/-- A finite two-dimensional complex embedded in `S`, not necessarily covering it.  The
realization is computed from the combinatorial data (as in `GeometricTriangulation`), so the
support of a partial triangulation is a genuine finite polyhedron sitting inside `S`. -/
structure PartialTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: three-element vertex sets. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The embedding of the realization into `S`. -/
  embed : GeometricRealization Vertex faces → S
  /-- `embed` is a topological embedding. -/
  isEmbedding : _root_.Topology.IsEmbedding embed

attribute [instance] PartialTriangulation.vertexFintype
attribute [instance] PartialTriangulation.vertexDecidableEq

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S] (T : PartialTriangulation S)

/-- Forget the ambient embedding and retain the intrinsic finite complex. -/
@[reducible] def toIntrinsic : IntrinsicTwoComplex where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card

@[simp] theorem toIntrinsic_faces : T.toIntrinsic.faces = T.faces := rfl

/-- The part of `S` covered by the partial triangulation. -/
def support : Set S :=
  Set.range T.embed

/-- Restrict the ambient embedding to a set known to contain the support. -/
def embedIntoDomain {U : Set S} (hU : T.support ⊆ U) :
    T.toIntrinsic.realization → U :=
  fun x => ⟨T.embed x, hU ⟨x, rfl⟩⟩

theorem isEmbedding_embedIntoDomain {U : Set S} (hU : T.support ⊆ U) :
    _root_.Topology.IsEmbedding (T.embedIntoDomain hU) :=
  T.isEmbedding.codRestrict U (fun x => hU ⟨x, rfl⟩)

/-- The support of a partial triangulation is compact. -/
theorem isCompact_support : IsCompact T.support :=
  isCompact_range T.isEmbedding.continuous

/-- Re-embed the same finite intrinsic complex in the ambient space.  This is the bookkeeping
operation used after Moise's vanishing chart replacement: only the coordinate embedding changes;
the abstract vertices and maximal faces do not. -/
abbrev reembed (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) : PartialTriangulation S where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card
  embed := f
  isEmbedding := hf

@[simp] theorem reembed_toIntrinsic (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) :
    (T.reembed f hf).toIntrinsic = T.toIntrinsic := rfl

theorem reembed_support (f : T.toIntrinsic.realization → S)
    (hf : _root_.Topology.IsEmbedding f) :
    (T.reembed f hf).support = Set.range f := rfl

/-- Replace the ambient embedding on a selected part of the intrinsic realization and retain
the old embedding outside.  The analytic frontier argument is deliberately supplied as an
embedding certificate, so this constructor works in the nonmetrized ambient surface. -/
noncomputable abbrev replaceOnOpen (U : Set T.toIntrinsic.realization)
    (g : T.toIntrinsic.realization → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)) :
    PartialTriangulation S :=
  T.reembed (frontierGlue U g T.embed)
    he

theorem replaceOnOpen_support (U : Set T.toIntrinsic.realization)
    (g : T.toIntrinsic.realization → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed)) :
    (T.replaceOnOpen U g he).support =
      g '' U ∪ T.embed '' Uᶜ := by
  change Set.range (frontierGlue U g T.embed) = g '' U ∪ T.embed '' Uᶜ
  exact range_frontierGlue

/-- A replacement which fixes every old preimage of a closed buffer retains the interior of
that buffer in its range.  This is the small topological observation that lets the relative
straightening preserve all previously absorbed Radó cores without any ambient isotopy. -/
theorem subset_interior_range_frontierGlue_of_fixedOn
    (U : Set (GeometricRealization T.Vertex T.faces))
    (g : GeometricRealization T.Vertex T.faces → S)
    {A C : Set S} (hA : A ⊆ interior C) (hC : C ⊆ T.support)
    (hfix : ∀ x, T.embed x ∈ C → g x = T.embed x) :
    A ⊆ interior (Set.range (frontierGlue U g T.embed)) := by
  apply hA.trans
  apply interior_mono
  intro z hz
  obtain ⟨x, hx⟩ := hC hz
  by_cases hxU : x ∈ U
  · refine ⟨x, ?_⟩
    rw [frontierGlue_of_mem hxU, hfix x]
    · exact hx
    · simpa only [hx] using hz
  · refine ⟨x, ?_⟩
    rw [frontierGlue_of_notMem hxU]
    exact hx

/-- At ambient-interior points one does not need a neighborhood contained in the fixed set.
Pointwise agreement suffices, because invariance of domain makes the corresponding local sheet
of the new embedding open.  The separate closed-buffer lemma above remains necessary on the
manifold boundary. -/
theorem subset_interior_range_frontierGlue_of_fixedOn_of_isInteriorPoint
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (U : Set (GeometricRealization T.Vertex T.faces))
    (g : GeometricRealization T.Vertex T.faces → S)
    (he : _root_.Topology.IsEmbedding (frontierGlue U g T.embed))
    {A : Set S} (hA : A ⊆ interior T.support)
    (hAi : ∀ z ∈ A,
      (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint z)
    (hfix : ∀ x, T.embed x ∈ A → g x = T.embed x) :
    A ⊆ interior (Set.range (frontierGlue U g T.embed)) := by
  intro z hzA
  obtain ⟨x, hx⟩ := interior_subset (hA hzA)
  have hxA : T.embed x ∈ A := by
    rw [hx]
    exact hzA
  have hvalue : frontierGlue U g T.embed x = T.embed x := by
    by_cases hxU : x ∈ U
    · rw [frontierGlue_of_mem hxU, hfix x]
      exact hxA
    · rw [frontierGlue_of_notMem hxU]
  have hopen :=
    mem_interior_range_of_eq_of_mem_interior_range_of_isInteriorPoint
      (modelWithCornersEuclideanHalfSpace 2)
      T.isEmbedding he (x := x) (by
        rw [hx]
        exact hA hzA) (by
        simpa only [hx] using hAi z hzA)
  rw [hvalue, hx] at hopen
  exact hopen

/-- Restrict a partial triangulation to a selected finite family of maximal faces. -/
def restrictFaces (p : Finset T.Vertex → Prop) [DecidablePred p] : PartialTriangulation S where
  Vertex := T.Vertex
  faces := T.faces.filter p
  faces_card := by
    intro t ht
    exact T.faces_card t (Finset.mem_filter.mp ht).1
  embed := T.embed ∘ T.toIntrinsic.restrictFacesInclusion p
  isEmbedding := T.isEmbedding.comp (T.toIntrinsic.isEmbedding_restrictFacesInclusion p)

theorem restrictFaces_support_subset (p : Finset T.Vertex → Prop) [DecidablePred p] :
    (T.restrictFaces p).support ⊆ T.support := by
  rintro x ⟨y, rfl⟩
  exact ⟨T.toIntrinsic.restrictFacesInclusion p y, rfl⟩

/-- Exact support formula for a finite face restriction. -/
theorem restrictFaces_support (p : Finset T.Vertex → Prop)
    [decidableP : DecidablePred p] :
    (T.restrictFaces p).support =
      T.embed '' {x : T.toIntrinsic.realization |
        ∃ t ∈ T.faces, p t ∧ x ∈ T.toIntrinsic.faceCarrier t} := by
  classical
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    let x : T.toIntrinsic.realization := T.toIntrinsic.restrictFacesInclusion p z
    refine ⟨x, ?_, rfl⟩
    rcases z.2.2 with ⟨t, ht, hzt⟩
    have ht' := (@Finset.mem_filter _ p decidableP _ _).mp ht
    exact ⟨t, ht'.1, ht'.2, hzt⟩
  · rintro ⟨x, ⟨t, ht, hpt, hxt⟩, rfl⟩
    let z : (T.toIntrinsic.restrictFaces p).realization :=
      ⟨x.1, x.2.1,
        ⟨t, (@Finset.mem_filter _ p decidableP _ _).mpr ⟨ht, hpt⟩, hxt⟩⟩
    exact ⟨z, rfl⟩

/-- Replace a partial triangulation by a faithful finite intrinsic subdivision. -/
noncomputable def refine (R : T.toIntrinsic.Subdivision) : PartialTriangulation S where
  Vertex := R.refined.Vertex
  faces := R.refined.faces
  faces_card := R.refined.faces_card
  embed := T.embed ∘ R.homeo
  isEmbedding := T.isEmbedding.comp R.homeo.isEmbedding

@[simp] theorem refine_toIntrinsic (R : T.toIntrinsic.Subdivision) :
    (T.refine R).toIntrinsic = R.refined := rfl

/-- Faithful subdivision changes the finite triangulation data but not its ambient support. -/
theorem refine_support (R : T.toIntrinsic.Subdivision) :
    (T.refine R).support = T.support := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨R.homeo x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨R.homeo.symm x, ?_⟩
    exact congrArg T.embed (R.homeo.apply_symm_apply x)

/-- A compact part of a partial triangulation lying in an ambient open set is carried by a
finite face restriction of a faithful refinement which still lies in that open set.

This is the finite collar extracted from Moise Ch. 8, Thm. 2.  It is the compact ingredient of
the Radó step; the full proof additionally needs the noncompact, locally finite collar whose
mesh tends to zero at its frontier. -/
theorem exists_refinedSubcomplex_between {C U : Set S}
    (hC : IsCompact C) (hCT : C ⊆ T.support) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (R : T.toIntrinsic.Subdivision)
      (keep : Finset (Finset R.refined.Vertex)),
      C ⊆ (@PartialTriangulation.restrictFaces _ _ (T.refine R)
        (fun t => t ∈ keep) (fun t => Finset.decidableMem t keep)).support ∧
      (@PartialTriangulation.restrictFaces _ _ (T.refine R)
        (fun t => t ∈ keep) (fun t => Finset.decidableMem t keep)).support ⊆ U := by
  classical
  let C₀ : Set T.toIntrinsic.realization := T.embed ⁻¹' C
  let U₀ : Set T.toIntrinsic.realization := T.embed ⁻¹' U
  have hC₀ : IsCompact C₀ := by
    exact T.isEmbedding.isInducing.isCompact_preimage' hC hCT
  have hU₀ : IsOpen U₀ := hU.preimage T.isEmbedding.continuous
  have hC₀U₀ : C₀ ⊆ U₀ := fun x hx => hCU hx
  obtain ⟨L⟩ := T.toIntrinsic.exists_openSubcomplex hC₀ hU₀ hC₀U₀
  refine ⟨L.subdivision, L.keptFaces, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx⟩ := hCT hz
    have hxC₀ : x ∈ C₀ := by
      change T.embed x ∈ C
      simpa [hx] using hz
    obtain ⟨y, hy⟩ := L.covers hxC₀
    exact ⟨y, (congrArg T.embed hy).trans hx⟩
  · rintro z ⟨y, rfl⟩
    apply L.contained
    exact ⟨y, rfl⟩

/-- A partial triangulation covering all of `S` is a geometric triangulation.  This is the final
conversion at the top of the Radó induction. -/
noncomputable def toGeometricTriangulation (hcovers : T.support = Set.univ) :
    GeometricTriangulation S where
  Vertex := T.Vertex
  faces := T.faces
  faces_card := T.faces_card
  homeo :=
    T.isEmbedding.toHomeomorphOfSurjective (Set.range_eq_univ.mp hcovers)

/-- The edges of a partial triangulation: the two-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

/-- The dual graph of the maximal faces of a partial triangulation is connected. -/
abbrev IsDualConnected : Prop :=
  TriangleFamily.IsDualConnected T.faces

theorem card_of_mem_edges {e : Finset T.Vertex} (he : e ∈ T.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

/-- On each maximal triangle, the ambient manifold boundary is one exposed simplicial face of
dimension at most one.

This is the missing regularity behind the bordered Moise argument.  Merely asking for the
boundary to be an edge subcomplex permits an interior chord joining two boundary vertices.  An
arbitrary convex-hull polygonalization can flatten such a chord onto the model boundary.  The
facewise condition rules that out and is stable under affine subdivision: the pullback of its
supporting face to every new triangle is again empty, a vertex, or an edge. -/
def BoundaryFacewiseRegular [ChartedSpace (EuclideanHalfSpace 2) S] : Prop :=
  ∀ t ∈ T.faces, ∃ b : Finset T.Vertex,
    b ⊆ t ∧ b.card ≤ 2 ∧
      ∀ x : T.toIntrinsic.realization, x ∈ T.toIntrinsic.faceCarrier t →
        (T.embed x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          x ∈ T.toIntrinsic.faceCarrier b)

/-- Facewise boundary regularity for an embedding of a raw finite geometric realization.

This is the side-local form used by the gluing theorem.  It deliberately mentions only
barycentric coordinates, so it transports transparently across vertex relabelings. -/
def BoundaryFacewiseRegularEmbedding
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {V : Type*} [Fintype V] (F : Finset (Finset V))
    (e : GeometricRealization V F → S) : Prop :=
  ∀ t ∈ F, ∃ b : Finset V,
    b ⊆ t ∧ b.card ≤ 2 ∧
      ∀ x : GeometricRealization V F, (∀ v ∉ t, x.1 v = 0) →
        (e x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          ∀ v ∉ b, x.1 v = 0)

/-- In a nondegenerate affine triangle lying in the closed half-plane, the zero-normal locus is
the convex hull of exactly those vertices on the boundary line.  Affine independence rules out
all three vertices lying on that line, so this is an exposed face of cardinality at most two. -/
theorem planeComplex_baryEval_coordZero_exposed
    (K : PlaneComplex) {t : Finset K.Vertex} (ht : t ∈ K.cells)
    (hnonneg : ∀ v ∈ t, 0 ≤ K.position v 0) :
    ∃ b : Finset K.Vertex,
      b ⊆ t ∧ b.card ≤ 2 ∧
        ∀ x : GeometricRealization K.Vertex K.cells,
          (∀ v ∉ t, x.1 v = 0) →
            (K.baryEval x.1 0 = 0 ↔ ∀ v ∉ b, x.1 v = 0) := by
  classical
  let b := t.filter fun v ↦ K.position v 0 = 0
  have hbt : b ⊆ t := Finset.filter_subset _ _
  have hbcard : b.card ≤ 2 := by
    by_contra hcard
    have htcard : t.card = 3 := K.card_of_mem_cells ht
    have hble : b.card ≤ t.card := Finset.card_le_card hbt
    have hbcard3 : b.card = 3 := by omega
    have hbeq : b = t :=
      Finset.eq_of_subset_of_card_le hbt (by omega)
    let H : AffineSubspace ℝ Plane :=
      (LinearMap.ker
        (PiLp.projₗ 2 (fun _ : Fin 2 ↦ ℝ) 0)).toAffineSubspace
    have hspanTop :
        affineSpan ℝ (Set.range fun v : t ↦ K.position v) = ⊤ :=
      ((K.affineIndependent t (K.mem_simplexes_of_mem_cells ht))
        |>.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
          simpa [Plane] using htcard)
    have hspanH :
        affineSpan ℝ (Set.range fun v : t ↦ K.position v) ≤ H := by
      apply affineSpan_le.mpr
      rintro p ⟨v, rfl⟩
      change K.position v.1 0 = 0
      have hvb : v.1 ∈ b := by rw [hbeq]; exact v.2
      exact (Finset.mem_filter.mp hvb).2
    have htopH : (⊤ : AffineSubspace ℝ Plane) ≤ H := by
      rw [← hspanTop]
      exact hspanH
    let p : Plane := EuclideanSpace.single 0 1
    have hpTop : p ∈ (⊤ : AffineSubspace ℝ Plane) := by simp
    have hpH := htopH hpTop
    change p 0 = 0 at hpH
    simp [p] at hpH
  refine ⟨b, hbt, hbcard, ?_⟩
  intro x hxt
  rw [K.baryEval_eq_sum_of_support hxt]
  have hcoord :
      (∑ v ∈ t, x.1 v • K.position v : Plane) 0 =
        ∑ v ∈ t, x.1 v * K.position v 0 := by
    change
      ((PiLp.projₗ 2 (fun _ : Fin 2 ↦ ℝ) 0) : Plane →ₗ[ℝ] ℝ)
          (∑ v ∈ t, x.1 v • K.position v) =
        ∑ v ∈ t, x.1 v * K.position v 0
    simp
  rw [hcoord]
  constructor
  · intro hsum
    have hterms : ∀ v ∈ t, x.1 v * K.position v 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun v hv ↦ mul_nonneg (x.2.1.1 v) (hnonneg v hv))).mp hsum
    intro v hvb
    by_cases hvt : v ∈ t
    · have hvpos : K.position v 0 ≠ 0 := by
        intro hvzero
        exact hvb (Finset.mem_filter.mpr ⟨hvt, hvzero⟩)
      exact (mul_eq_zero.mp (hterms v hvt)).resolve_right hvpos
    · exact hxt v hvt
  · intro hx
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hvb : v ∈ b
    · rw [(Finset.mem_filter.mp hvb).2, mul_zero]
    · rw [hx v hvb, zero_mul]

/-- The barycentric realization of a plane triangle mesh lying in a boundary-faithful chart is
facewise boundary regular. -/
theorem TriangleMesh.boundaryFacewiseRegularEmbedding_chart
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (M : TriangleMesh) (c : MoiseChart S) (hc : c.BoundaryFaithful)
    (hmodel : M.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    BoundaryFacewiseRegularEmbedding M.triangles
      (fun x ↦
        (c.chart.symm
          (M.coordinateEmbedInto c.kind.modelRegion hmodel x)).1) := by
  classical
  intro t ht
  by_cases hk : c.kind = ChartKind.disk
  · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro x hxt
    constructor
    · intro hx
      exact False.elim <|
        (hc.1 hk
          (c.chart.symm
            (M.coordinateEmbedInto c.kind.modelRegion hmodel x)).1
          (c.chart.symm
            (M.coordinateEmbedInto c.kind.modelRegion hmodel x)).2) hx
    · intro hx
      have hzero : ∀ v, x.1 v = 0 :=
        fun v ↦ hx v (Finset.notMem_empty v)
      have hsum := x.2.1.2
      simp only [hzero, Finset.sum_const_zero] at hsum
      norm_num at hsum
  · have hkHalf : c.kind = ChartKind.halfDisk := by
      cases hkind : c.kind
      · exact (hk hkind).elim
      · rfl
    have htCells : t ∈ M.toPlaneComplex.cells := by
      rwa [M.toPlaneComplex_cells]
    have hnonneg : ∀ v ∈ t, 0 ≤ M.position v 0 := by
      intro v hv
      have hvCarrier :
          M.position v ∈ M.toPlaneComplex.cellCarrier t := by
        rw [PlaneComplex.cellCarrier]
        apply subset_convexHull ℝ
        exact ⟨v, hv, rfl⟩
      have hvSupport : M.position v ∈ M.toPlaneComplex.support := by
        exact
          M.toPlaneComplex.cellCarrier_subset_support
            (M.toPlaneComplex.mem_simplexes_of_mem_cells htCells) hvCarrier
      have hvModel := hmodel hvSupport
      rw [hkHalf] at hvModel
      exact hvModel.2
    obtain ⟨b, hbt, hbcard, hb⟩ :=
      planeComplex_baryEval_coordZero_exposed M.toPlaneComplex htCells hnonneg
    refine ⟨b, hbt, hbcard, ?_⟩
    intro x hxt
    have hchart :=
      hc.2 hkHalf
        (c.chart.symm
          (M.coordinateEmbedInto c.kind.modelRegion hmodel x)).1
        (c.chart.symm
          (M.coordinateEmbedInto c.kind.modelRegion hmodel x)).2
    have happly :=
      c.chart.apply_symm_apply
        (M.coordinateEmbedInto c.kind.modelRegion hmodel x)
    have hplane :=
      congrArg (fun z : c.kind.modelRegion ↦ (z : Plane)) happly
    rw [hplane] at hchart
    let x' :
        GeometricRealization M.toPlaneComplex.Vertex
          M.toPlaneComplex.cells :=
      ⟨x.1, x.2.1, by
        rw [M.toPlaneComplex_cells]
        exact x.2.2⟩
    have hb' := hb x' hxt
    change
      M.toPlaneComplex.baryEval x.1 0 = 0 ↔
        ∀ v ∉ b, x.1 v = 0 at hb'
    exact hchart.trans hb'

/-- Boundary-face regularity depends only on which source points map to the ambient boundary. -/
theorem boundaryFacewiseRegularEmbedding_congr
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {V : Type*} [Fintype V]
    {F : Finset (Finset V)}
    {e e' : GeometricRealization V F → S}
    (h : BoundaryFacewiseRegularEmbedding F e)
    (hee : ∀ x,
      (e' x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        e x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S)) :
    BoundaryFacewiseRegularEmbedding F e' := by
  classical
  intro t ht
  obtain ⟨b, hbt, hbcard, hb⟩ := h t ht
  refine ⟨b, hbt, hbcard, ?_⟩
  intro x hxt
  exact (hee x).trans (hb x hxt)

/-- Facewise boundary regularity is invariant under an injective relabeling of the vertex type. -/
theorem boundaryFacewiseRegularEmbedding_relabel
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (ι : A ↪ B) (F : Finset (Finset A))
    (e : GeometricRealization A F → S)
    (h : BoundaryFacewiseRegularEmbedding F e) :
    BoundaryFacewiseRegularEmbedding (relabelFaceFamily ι F)
      (e ∘ (relabelGeometricRealizationHomeomorph ι F).symm) := by
  classical
  intro t ht
  obtain ⟨s, hsF, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨b, hbs, hbcard, hb⟩ := h s hsF
  let b' : Finset B := b.map ι
  have hbsub : b' ⊆ s.map ι := by
    intro w hw
    obtain ⟨v, hvb, rfl⟩ := Finset.mem_map.mp hw
    exact Finset.mem_map.mpr ⟨v, hbs hvb, rfl⟩
  have hbcard' : b'.card ≤ 2 := by
    simpa [b'] using hbcard
  refine ⟨b', hbsub, hbcard', ?_⟩
  intro x hxs
  let xA : GeometricRealization A F :=
    (relabelGeometricRealizationHomeomorph ι F).symm x
  have hxAs : ∀ v ∉ s, xA.1 v = 0 := by
    intro v hv
    rw [show xA.1 v = x.1 (ι v) by
      exact pullGeometricRealization_apply ι F x v]
    apply hxs
    intro hvmap
    obtain ⟨w, hws, hwv⟩ := Finset.mem_map.mp hvmap
    exact hv (ι.injective hwv ▸ hws)
  have hboundary := hb xA hxAs
  change e xA ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
    ∀ w ∉ b', x.1 w = 0
  refine hboundary.trans ?_
  constructor
  · intro hx w hwb
    by_cases hwRange : w ∈ Set.range ι
    · obtain ⟨v, rfl⟩ := hwRange
      rw [← pullGeometricRealization_apply ι F x v]
      apply hx v
      intro hvb
      exact hwb (Finset.mem_map.mpr ⟨v, hvb, rfl⟩)
    · have hpush :=
        congrArg Subtype.val (push_pullGeometricRealization ι F x)
      rw [← congrFun hpush w]
      exact pushGeometricRealization_apply_of_notMem_range ι F xA hwRange
  · intro hx v hvb
    change (pullGeometricRealization ι F x).1 v = 0
    rw [pullGeometricRealization_apply ι F x v]
    apply hx (ι v)
    intro hmem
    obtain ⟨w, hwb, hwv⟩ := Finset.mem_map.mp hmem
    exact hvb (ι.injective hwv ▸ hwb)

/-- The images of the three vertices of a refined face under a faithful affine subdivision are
affinely independent in the old barycentric coordinate space. -/
theorem IntrinsicTwoComplex.Subdivision.affineIndependent_vertexImages
    {K : IntrinsicTwoComplex} (R : K.Subdivision)
    (t : R.refined.Face) :
    AffineIndependent ℝ
      (fun v : t.1 ↦ (R.homeo (R.refined.facePoint t v)).1) := by
  classical
  obtain ⟨a, ha⟩ := R.affineOnFace t.1 t.2
  let f : Plane →ᵃ[ℝ] (K.Vertex → ℝ) :=
    a.comp (R.refined.facePlaneInverseAffine t)
  have hfInj :
      Set.InjOn f (convexHull ℝ (Set.range standardTriangleVertex)) := by
    intro x hx y hy hxy
    have hxSupport : x ∈ standardTrianglePlaneComplex.support := by
      rw [standardTrianglePlaneComplex_support]
      exact hx
    have hySupport : y ∈ standardTrianglePlaneComplex.support := by
      rw [standardTrianglePlaneComplex_support]
      exact hy
    let xp : standardTrianglePlaneComplex.support := ⟨x, hxSupport⟩
    let yp : standardTrianglePlaneComplex.support := ⟨y, hySupport⟩
    let X : R.refined.ClosedFace t :=
      (R.refined.facePlaneHomeomorph t).symm xp
    let Y : R.refined.ClosedFace t :=
      (R.refined.facePlaneHomeomorph t).symm yp
    have hXval :
        X.1.1 = R.refined.facePlaneInverseAffine t x := by
      simpa only [X, xp] using
        R.refined.facePlaneHomeomorph_symm_val t xp
    have hYval :
        Y.1.1 = R.refined.facePlaneInverseAffine t y := by
      simpa only [Y, yp] using
        R.refined.facePlaneHomeomorph_symm_val t yp
    have hRX : (R.homeo X.1).1 = f x := by
      rw [ha X.1 X.2]
      change a X.1.1 = a (R.refined.facePlaneInverseAffine t x)
      rw [hXval]
    have hRY : (R.homeo Y.1).1 = f y := by
      rw [ha Y.1 Y.2]
      change a Y.1.1 = a (R.refined.facePlaneInverseAffine t y)
      rw [hYval]
    have hRXY : R.homeo X.1 = R.homeo Y.1 := by
      apply Subtype.ext
      rw [hRX, hRY]
      exact hxy
    have hXY : X = Y := by
      apply Subtype.ext
      exact R.homeo.injective hRXY
    have hplane :=
      congrArg (R.refined.facePlaneHomeomorph t) hXY
    have hxySub : xp = yp := by
      simpa only [X, Y,
        (R.refined.facePlaneHomeomorph t).apply_symm_apply] using hplane
    exact congrArg Subtype.val hxySub
  have hfin :
      AffineIndependent ℝ (f ∘ standardTriangleVertex) :=
    affineIndependent_comp_of_injOn_convexHull standardTriangleVertex
      standardTriangleVertex_affineIndependent f hfInj
  apply (affineIndependent_equiv (R.refined.faceVertexEquiv t)).mp
  convert hfin using 1
  funext i
  change
    (R.homeo
        (R.refined.facePoint t (R.refined.faceVertexEquiv t i))).1 =
      f (standardTriangleVertex i)
  rw [ha _ (R.refined.facePoint_mem_faceCarrier t _)]
  change
    a (R.refined.facePoint t (R.refined.faceVertexEquiv t i)).1 =
      a (R.refined.facePlaneInverseAffine t (standardTriangleVertex i))
  rw [R.refined.facePlaneInverseAffine_standardVertex,
    R.refined.facePoint_val]
  rfl

/-- A barycentric point supported on `b` lies in the convex hull of the corresponding unit
coordinate vectors. -/
theorem IntrinsicTwoComplex.mem_convexHull_unitVectors_of_mem_faceCarrier
    (K : IntrinsicTwoComplex) (b : Finset K.Vertex)
    (x : K.realization) (hx : x ∈ K.faceCarrier b) :
    x.1 ∈ convexHull ℝ
      (((b.image fun v ↦ Pi.single v 1 : Finset (K.Vertex → ℝ))) :
        Set (K.Vertex → ℝ)) := by
  classical
  have hsum : ∑ v ∈ b, x.1 v = 1 := by
    calc
      ∑ v ∈ b, x.1 v = ∑ v, x.1 v :=
        Finset.sum_subset (Finset.subset_univ b)
          (fun v _ hv ↦ hx v hv)
      _ = 1 := x.2.1.2
  have hcenter :
      b.centerMass x.1 (fun v ↦ Pi.single v 1) = x.1 := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hw : w ∈ b
    · rw [Finset.sum_eq_single w]
      · simp
      · intro v hv hvw
        simp [hvw]
      · simp [hw]
    · rw [hx w hw]
      apply Finset.sum_eq_zero
      intro v hv
      have hvw : v ≠ w := fun h ↦ hw (h ▸ hv)
      simp [hvw]
  rw [← hcenter]
  apply Finset.centerMass_mem_convexHull b
  · exact fun v _ ↦ x.2.1.1 v
  · rw [hsum]
    norm_num
  · intro v hv
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

/-- Facewise boundary regularity survives every faithful affine intrinsic subdivision. -/
theorem boundaryFacewiseRegular_refine
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (T : PartialTriangulation S) (hboundary : T.BoundaryFacewiseRegular)
    (R : T.toIntrinsic.Subdivision) :
    (T.refine R).BoundaryFacewiseRegular := by
  classical
  intro t ht
  change Finset R.refined.Vertex at t
  change t ∈ R.refined.faces at ht
  obtain ⟨u, hu, htu⟩ := R.subordinate t ht
  obtain ⟨b, hbu, hbcard, hb⟩ := hboundary u hu
  let q : t → T.toIntrinsic.realization :=
    fun v ↦ R.homeo
      (R.refined.facePoint (⟨t, ht⟩ : R.refined.Face) v)
  let d : Finset t :=
    Finset.univ.filter fun v ↦ q v ∈ T.toIntrinsic.faceCarrier b
  let vertexEmbedding : t ↪ R.refined.Vertex :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let b' : Finset R.refined.Vertex := d.map vertexEmbedding
  have hb't : b' ⊆ t := by
    intro v hv
    obtain ⟨w, hwd, rfl⟩ := Finset.mem_map.mp hv
    exact w.2
  have hdcard : d.card ≤ 2 := by
    by_contra hd
    have htcard : Fintype.card t = 3 := by
      rw [Fintype.card_coe, R.refined.faces_card t ht]
    have hdle : d.card ≤ Fintype.card t := by
      calc
        d.card ≤ (Finset.univ : Finset t).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card t := Finset.card_univ
    have hdcard3 : d.card = 3 := by omega
    have hdeq : d = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by simpa only [Finset.card_univ] using (show Fintype.card t ≤ d.card by omega))
    have hall (v : t) : q v ∈ T.toIntrinsic.faceCarrier b := by
      have hvd : v ∈ d := by rw [hdeq]; simp
      exact (Finset.mem_filter.mp hvd).2
    let B : Finset (T.toIntrinsic.Vertex → ℝ) :=
      b.image fun v ↦ Pi.single v 1
    have hspan :
        Set.range (fun v : t ↦ (q v).1) ⊆
          affineSpan ℝ (B : Set (T.toIntrinsic.Vertex → ℝ)) := by
      rintro z ⟨v, rfl⟩
      apply convexHull_subset_affineSpan
        (B : Set (T.toIntrinsic.Vertex → ℝ))
      exact
        IntrinsicTwoComplex.mem_convexHull_unitVectors_of_mem_faceCarrier
          T.toIntrinsic b (q v) (hall v)
    have hAI :
        AffineIndependent ℝ
          (fun v : t ↦
            (R.homeo
              (R.refined.facePoint
                (⟨t, ht⟩ : R.refined.Face) v)).1) :=
      IntrinsicTwoComplex.Subdivision.affineIndependent_vertexImages R
        (⟨t, ht⟩ : R.refined.Face)
    let A : Finset (T.toIntrinsic.Vertex → ℝ) :=
      Finset.univ.image fun v : t ↦ (q v).1
    have hqInjective : Function.Injective (fun v : t ↦ (q v).1) :=
      hAI.injective
    let toA : t → A := fun v ↦
      ⟨(q v).1, Finset.mem_image.mpr
        ⟨v, Finset.mem_univ _, rfl⟩⟩
    have htoAInjective : Function.Injective toA := by
      intro v w hvw
      apply hqInjective
      exact congrArg
        (fun z : A ↦ (z : T.toIntrinsic.Vertex → ℝ)) hvw
    have htoASurjective : Function.Surjective toA := by
      rintro ⟨z, hz⟩
      obtain ⟨v, _, hvz⟩ := Finset.mem_image.mp hz
      refine ⟨v, Subtype.ext ?_⟩
      exact hvz
    let e : t ≃ A :=
      Equiv.ofBijective toA ⟨htoAInjective, htoASurjective⟩
    have hAI' : AffineIndependent ℝ
        ((↑) : A → (T.toIntrinsic.Vertex → ℝ)) := by
      apply (affineIndependent_equiv e).mp
      convert hAI using 1
      funext v
      rfl
    have hAspan :
        (A : Set (T.toIntrinsic.Vertex → ℝ)) ⊆
          affineSpan ℝ (B : Set (T.toIntrinsic.Vertex → ℝ)) := by
      intro z hz
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
      exact hspan ⟨v, rfl⟩
    have hcardAB : A.card ≤ B.card :=
      hAI'.card_le_card_of_subset_affineSpan hAspan
    have hAcard : A.card = Fintype.card t := by
      change
        (Finset.univ.image fun v : t ↦ (q v).1).card =
          Fintype.card t
      rw [Finset.card_image_iff.mpr hqInjective.injOn,
        Finset.card_univ]
    have hcardle : Fintype.card t ≤ B.card := hAcard ▸ hcardAB
    have hBcard : B.card ≤ b.card := Finset.card_image_le
    omega
  have hb'card : b'.card ≤ 2 := by
    simpa only [b', Finset.card_map] using hdcard
  refine ⟨b', hb't, hb'card, ?_⟩
  intro x hxt
  change R.refined.realization at x
  change x ∈ R.refined.faceCarrier t at hxt
  obtain ⟨a, ha⟩ := R.affineOnFace t ht
  have hsum : ∑ v : t, x.1 v.1 = 1 :=
    R.refined.sum_face_coords (⟨t, ht⟩ : R.refined.Face) x hxt
  have hsource :
      (R.homeo x).1 =
        ∑ v : t, x.1 v.1 • (q v).1 := by
    calc
      (R.homeo x).1 = a x.1 := ha x hxt
      _ = a (Finset.univ.affineCombination ℝ
          (fun v : t ↦
            (R.refined.facePoint
              (⟨t, ht⟩ : R.refined.Face) v).1)
          (fun v : t ↦ x.1 v.1)) := by
        rw [R.refined.face_affineCombination_eq
          (⟨t, ht⟩ : R.refined.Face) x hxt]
      _ = Finset.univ.affineCombination ℝ
          (a ∘ fun v : t ↦
            (R.refined.facePoint
              (⟨t, ht⟩ : R.refined.Face) v).1)
          (fun v : t ↦ x.1 v.1) :=
        Finset.map_affineCombination _ _ _ hsum a
      _ = ∑ v : t, x.1 v.1 • (q v).1 := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
        apply Finset.sum_congr rfl
        intro v hv
        change
          x.1 v.1 •
              a (R.refined.facePoint
                (⟨t, ht⟩ : R.refined.Face) v).1 =
            x.1 v.1 • (q v).1
        congr 1
        exact (ha _
          (R.refined.facePoint_mem_faceCarrier
            (⟨t, ht⟩ : R.refined.Face) v)).symm
  have hboundaryOld :=
    hb (R.homeo x) (htu x hxt)
  change
    T.embed (R.homeo x) ∈
        (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
      ∀ v ∉ b', x.1 v = 0
  refine hboundaryOld.trans ?_
  change
    (∀ k ∉ b, (R.homeo x).1 k = 0) ↔
      ∀ v ∉ b', x.1 v = 0
  constructor
  · intro hx v hvb'
    by_cases hvt : v ∈ t
    · let vt : t := ⟨v, hvt⟩
      have hvd : vt ∉ d := by
        intro hvd
        apply hvb'
        exact Finset.mem_map.mpr ⟨vt, hvd, rfl⟩
      have hqNot : q vt ∉ T.toIntrinsic.faceCarrier b := by
        intro hq
        exact hvd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)
      rw [T.toIntrinsic.mem_faceCarrier_iff] at hqNot
      simp only [not_forall] at hqNot
      obtain ⟨k, hkb, hqk⟩ := hqNot
      have hsumk :
          ∑ w : t, x.1 w.1 * (q w).1 k = 0 := by
        rw [← hx k hkb, hsource]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hterm :
          x.1 vt.1 * (q vt).1 k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun w hw ↦ mul_nonneg (x.2.1.1 w.1)
            ((q w).2.1.1 k))).mp hsumk vt (Finset.mem_univ _)
      exact (mul_eq_zero.mp hterm).resolve_right hqk
    · exact hxt v hvt
  · intro hx k hkb
    rw [hsource]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hvd : v ∈ d
    · have hqCarrier := (Finset.mem_filter.mp hvd).2
      rw [hqCarrier k hkb, mul_zero]
    · have hvb' : v.1 ∉ b' := by
        intro hvmap
        obtain ⟨w, hwd, hwv⟩ := Finset.mem_map.mp hvmap
        have hwEq : w = v := Subtype.ext hwv
        exact hvd (hwEq ▸ hwd)
      rw [hx v.1 hvb', zero_mul]

/-- Transport a pure finite plane complex into an ambient space.  The abstract realization is
identified with the geometric support by barycentric coordinates, then followed by the supplied
ambient embedding. -/
noncomputable abbrev ofPlaneComplex {S : Type*} [TopologicalSpace S]
    (K : PlaneComplex) (hpure : K.IsPure2)
    (e : K.support → S) (he : _root_.Topology.IsEmbedding e) :
    PartialTriangulation S where
  Vertex := K.Vertex
  faces := K.cells
  faces_card := fun _ ht => K.card_of_mem_cells ht
  embed := e ∘ K.realizationHomeomorph hpure
  isEmbedding := he.comp (K.realizationHomeomorph hpure).isEmbedding

/-- The transported plane patch covers exactly the ambient range of its support embedding. -/
theorem ofPlaneComplex_support {S : Type*} [TopologicalSpace S]
    (K : PlaneComplex) (hpure : K.IsPure2)
    (e : K.support → S) (he : _root_.Topology.IsEmbedding e) :
    (ofPlaneComplex K hpure e he).support = Set.range e := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    exact ⟨K.realizationHomeomorph hpure z, rfl⟩
  · rintro x ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := (K.realizationHomeomorph hpure).surjective z
    exact ⟨w, rfl⟩

/-- The empty partial triangulation. -/
def empty (S : Type*) [TopologicalSpace S] : PartialTriangulation S where
  Vertex := Empty
  faces := ∅
  faces_card := by simp
  embed := fun x => isEmptyElim x
  isEmbedding := Topology.IsEmbedding.of_subsingleton _

/-- The empty partial triangulation is vacuously dual-connected. -/
theorem empty_isDualConnected (S : Type*) [TopologicalSpace S] :
    (empty S).IsDualConnected := by
  rintro ⟨f, hf⟩
  change f ∈ (∅ : Finset (Finset Empty)) at hf
  exact (Finset.notMem_empty f hf).elim

/-- A partial triangulation with no faces covers nothing: its realization is empty. -/
theorem support_eq_empty_of_faces_eq_empty {S : Type*} [TopologicalSpace S]
    (T : PartialTriangulation S) (h : T.faces = ∅) : T.support = ∅ := by
  ext x
  simp only [support, Set.mem_range, Set.mem_empty_iff_false, iff_false]
  rintro ⟨p, rfl⟩
  rcases p.2.2 with ⟨t, ht, -⟩
  rw [h] at ht
  exact absurd ht (Finset.notMem_empty t)

@[simp] theorem empty_support (S : Type*) [TopologicalSpace S] :
    (empty S).support = ∅ :=
  support_eq_empty_of_faces_eq_empty _ rfl

end PartialTriangulation

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] (K : LocallyFiniteTriangleComplex S)

/-- A finite compatible ambient triangle family is a partial triangulation of the ambient
space.  Its support is exactly the union of the face carriers. -/
noncomputable def toPartialTriangulation [Finite K.Face] [T2Space S] :
    PartialTriangulation S := by
  let G := K.finiteSupportGeometricTriangulation
  exact
    { Vertex := G.Vertex
      faces := G.faces
      faces_card := G.faces_card
      embed := Subtype.val ∘ G.homeo
      isEmbedding := _root_.Topology.IsEmbedding.subtypeVal.comp G.homeo.isEmbedding }

theorem toPartialTriangulation_support [Finite K.Face] [T2Space S] :
    K.toPartialTriangulation.support = K.support := by
  let G := K.finiteSupportGeometricTriangulation
  change Set.range (Subtype.val ∘ G.homeo) = K.support
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    exact (G.homeo x).2
  · intro y hy
    let z : K.support := ⟨y, hy⟩
    refine ⟨G.homeo.symm z, ?_⟩
    exact congrArg Subtype.val (G.homeo.apply_symm_apply z)

end LocallyFiniteTriangleComplex

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- The plane embedding of an intrinsic partial triangulation whose support lies in this chart.
This is the source embedding consumed by intrinsic PL approximation in the Rado step. -/
def partialChartMap (T : PartialTriangulation S) (hdom : T.support ⊆ c.domain) :
    T.toIntrinsic.realization → Plane :=
  fun x => (c.chart (T.embedIntoDomain hdom x) : Plane)

theorem isEmbedding_partialChartMap (T : PartialTriangulation S)
    (hdom : T.support ⊆ c.domain) :
    _root_.Topology.IsEmbedding (c.partialChartMap T hdom) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.isEmbedding.comp (T.isEmbedding_embedIntoDomain hdom))

/-- Include the fixed polygonal model patch into this chart's model region. -/
def patchToModelRegion : c.kind.patchComplex.support → c.kind.modelRegion :=
  fun x => ⟨x.1, c.kind.patchComplex_support_subset_modelRegion x.2⟩

theorem isEmbedding_patchToModelRegion :
    _root_.Topology.IsEmbedding c.patchToModelRegion :=
  _root_.Topology.IsEmbedding.subtypeVal.codRestrict _ _

/-- Embed the fixed polygonal patch into the ambient surface through the inverse chart. -/
def patchEmbed : c.kind.patchComplex.support → S :=
  fun x => (c.chart.symm (c.patchToModelRegion x)).1

theorem isEmbedding_patchEmbed : _root_.Topology.IsEmbedding c.patchEmbed :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp c.isEmbedding_patchToModelRegion)

/-- The concrete finite partial triangulation supplied by one Moise chart. -/
noncomputable abbrev patchPartialTriangulation : PartialTriangulation S :=
  PartialTriangulation.ofPlaneComplex c.kind.patchComplex c.kind.patchComplex_pure
    c.patchEmbed c.isEmbedding_patchEmbed

/-- The concrete partial triangulation supplied by one chart has a connected dual graph. -/
theorem patchPartialTriangulation_isDualConnected :
    c.patchPartialTriangulation.IsDualConnected := by
  change TriangleFamily.IsDualConnected c.kind.patchComplex.cells
  exact c.kind.patchComplex_isDualConnected

theorem patchPartialTriangulation_support :
    c.patchPartialTriangulation.support = Set.range c.patchEmbed :=
  PartialTriangulation.ofPlaneComplex_support c.kind.patchComplex
    c.kind.patchComplex_pure c.patchEmbed c.isEmbedding_patchEmbed

theorem patchPartialTriangulation_embed_mem_domain
    (x : c.patchPartialTriangulation.toIntrinsic.realization) :
    c.patchPartialTriangulation.embed x ∈ c.domain := by
  change
    (c.chart.symm
      (c.patchToModelRegion
        (c.kind.patchComplex.realizationHomeomorph c.kind.patchComplex_pure x))).1 ∈ c.domain
  exact
    (c.chart.symm
      (c.patchToModelRegion
        (c.kind.patchComplex.realizationHomeomorph c.kind.patchComplex_pure x))).2

theorem patchPartialTriangulation_chart_coord
    (x : c.patchPartialTriangulation.toIntrinsic.realization) :
    (c.chart
      ⟨c.patchPartialTriangulation.embed x,
        c.patchPartialTriangulation_embed_mem_domain x⟩ : Plane) =
      c.kind.patchComplex.baryEval x.1 := by
  change
    (c.chart
      ⟨(c.chart.symm
          (c.patchToModelRegion
            (c.kind.patchComplex.realizationHomeomorph c.kind.patchComplex_pure x))).1, _⟩ :
        Plane) =
      c.kind.patchComplex.baryEval x.1
  have h :=
    c.chart.apply_symm_apply
      (c.patchToModelRegion
        (c.kind.patchComplex.realizationHomeomorph c.kind.patchComplex_pure x))
  exact (congrArg (fun z : c.kind.modelRegion => (z : Plane)) h).trans
    (c.kind.patchComplex.realizationHomeomorph_apply c.kind.patchComplex_pure x)

theorem BoundaryFaithful.mem_boundary_iff_isModelBoundary
    [ChartedSpace (EuclideanHalfSpace 2) S] (hc : c.BoundaryFaithful)
    (y : S) (hy : y ∈ c.domain) :
    y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
      c.kind.IsModelBoundary (c.chart ⟨y, hy⟩ : Plane) := by
  let p : Plane := (c.chart ⟨y, hy⟩ : Plane)
  change y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
    c.kind.IsModelBoundary p
  by_cases hk : c.kind = ChartKind.disk
  · have hmodel :
        c.kind.IsModelBoundary p = False := by
      rw [hk]
      rfl
    rw [hmodel]
    exact iff_false_intro (hc.1 hk y hy)
  · have hkHalf : c.kind = ChartKind.halfDisk := by
      cases hkind : c.kind
      · exact (hk hkind).elim
      · rfl
    have hmodel :
        c.kind.IsModelBoundary p = (p 0 = 0) := by
      rw [hkHalf]
      rfl
    rw [hmodel]
    simpa only [p] using hc.2 hkHalf y hy

/-- The concrete chart patch covers the marked chart core. -/
theorem core_subset_patchPartialTriangulation_support :
    c.core ⊆ c.patchPartialTriangulation.support := by
  rw [c.patchPartialTriangulation_support]
  intro y hy
  rcases c.mem_core_iff.mp hy with ⟨hyDomain, hyCore⟩
  let p : c.kind.modelRegion := c.chart ⟨y, hyDomain⟩
  let q : c.kind.patchComplex.support :=
    ⟨p.1, c.kind.modelCore_subset_patchComplex_support hyCore⟩
  refine ⟨q, ?_⟩
  change (c.chart.symm ⟨q.1, c.kind.patchComplex_support_subset_modelRegion q.2⟩).1 = y
  exact congrArg Subtype.val (c.chart.symm_apply_apply ⟨y, hyDomain⟩)

/-- The model-region subset occupied by the fixed polygonal patch. -/
def patchInModelRegion : Set c.kind.modelRegion :=
  {p | (p : Plane) ∈ c.kind.patchComplex.support}

theorem range_patchToModelRegion :
    Set.range c.patchToModelRegion = c.patchInModelRegion := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hp
    let q : c.kind.patchComplex.support := ⟨p.1, hp⟩
    exact ⟨q, Subtype.ext rfl⟩

/-- Exact chart-domain description of the transported patch support. -/
theorem patchPartialTriangulation_support_eq_chartImage :
    c.patchPartialTriangulation.support =
      Subtype.val '' (c.chart.symm '' c.patchInModelRegion) := by
  rw [c.patchPartialTriangulation_support]
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨c.chart.symm (c.patchToModelRegion q), ?_, rfl⟩
    exact ⟨c.patchToModelRegion q, q.2, rfl⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    let q : c.kind.patchComplex.support := ⟨p.1, hp⟩
    exact ⟨q, congrArg Subtype.val (congrArg c.chart.symm (Subtype.ext rfl))⟩

/-- The marked core lies in the ambient topological interior of the concrete chart patch. -/
theorem core_subset_interior_patchPartialTriangulation_support :
    c.core ⊆ interior c.patchPartialTriangulation.support := by
  intro y hy
  rcases c.mem_core_iff.mp hy with ⟨hyDomain, hyCore⟩
  let p : c.kind.modelRegion := c.chart ⟨y, hyDomain⟩
  have hpInterior : p ∈ interior c.patchInModelRegion :=
    c.kind.modelCore_subset_interior_patchInRegion hyCore
  have hzInterior : c.chart.symm p ∈ interior (c.chart.symm '' c.patchInModelRegion) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hpInterior, rfl⟩
  let O : Set S := Subtype.val '' interior (c.chart.symm '' c.patchInModelRegion)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆ c.patchPartialTriangulation.support := by
    rw [c.patchPartialTriangulation_support_eq_chartImage]
    exact Set.image_mono interior_subset
  apply interior_maximal hOsub hOopen
  refine ⟨c.chart.symm p, hzInterior, ?_⟩
  exact congrArg Subtype.val (c.chart.symm_apply_apply ⟨y, hyDomain⟩)

/-- The fixed disk/half-disk patch has no boundary chords.  In a half-disk face its boundary
face is obtained by deleting the unique positive-normal vertex `1`; in a disk face it is empty. -/
theorem patchPartialTriangulation_boundaryFacewiseRegular
    [ChartedSpace (EuclideanHalfSpace 2) S] (hc : c.BoundaryFaithful) :
    c.patchPartialTriangulation.BoundaryFacewiseRegular := by
  classical
  intro t ht
  obtain ⟨b, hbt, hbcard, hb⟩ :=
    c.kind.patchComplex_isModelBoundary_facewise t ht
  refine ⟨b, hbt, hbcard, ?_⟩
  intro x hxt
  have hxt' : ∀ v ∉ t, x.1 v = 0 :=
    (c.patchPartialTriangulation.toIntrinsic.mem_faceCarrier_iff t x).mp hxt
  have hb' := hb x hxt'
  rw [c.patchPartialTriangulation.toIntrinsic.mem_faceCarrier_iff]
  have hsurfaceModel :
      c.patchPartialTriangulation.embed x ∈
          (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        c.kind.IsModelBoundary (c.kind.patchComplex.baryEval x.1) := by
    calc
      _ ↔ c.kind.IsModelBoundary
          (c.chart
            ⟨c.patchPartialTriangulation.embed x,
              c.patchPartialTriangulation_embed_mem_domain x⟩ : Plane) :=
        MoiseChart.BoundaryFaithful.mem_boundary_iff_isModelBoundary c hc
          (c.patchPartialTriangulation.embed x)
          (c.patchPartialTriangulation_embed_mem_domain x)
      _ ↔ _ := by rw [c.patchPartialTriangulation_chart_coord x]
  exact hsurfaceModel.trans hb'

end MoiseChart

/-! ## The locally finite old-complex overlap in one chart -/

namespace ChartKind

/-- The open disk in which chart-coordinate perturbations are performed.  For a half-disk chart
the model region is a closed subset of this disk; the later bordered approximation must preserve
that half-disk rather than use the extra side. -/
def perturbationRegion (_k : ChartKind) : Set Plane := Metric.ball 0 1

/-- A disk or half-disk model is locally compact in its subtype topology. -/
theorem modelRegionLocallyCompactSpace (k : ChartKind) :
    LocallyCompactSpace k.modelRegion := by
  cases k with
  | disk =>
      exact Metric.isOpen_ball.locallyCompactSpace
  | halfDisk =>
      apply IsLocallyClosed.locallyCompactSpace
      refine ⟨Metric.ball (0 : Plane) 1, {x : Plane | 0 ≤ x 0},
        Metric.isOpen_ball, isClosed_le continuous_const continuous_coordZero, ?_⟩
      rfl

theorem isOpen_perturbationRegion (k : ChartKind) : IsOpen k.perturbationRegion :=
  Metric.isOpen_ball

theorem modelRegion_subset_perturbationRegion (k : ChartKind) :
    k.modelRegion ⊆ k.perturbationRegion := by
  cases k <;> intro p hp
  · exact hp
  · exact hp.1

/-- Inside the open perturbation disk, the closure of the model region adds nothing: closure
only touches the unit sphere and, for a half-disk, the model already contains its edge line. -/
theorem ball_inter_closure_modelRegion_subset (k : ChartKind) :
    Metric.ball (0 : Plane) 1 ∩ closure k.modelRegion ⊆ k.modelRegion := by
  cases k with
  | disk =>
      intro z hz
      exact hz.1
  | halfDisk =>
      rintro z ⟨hzball, hzcl⟩
      refine ⟨hzball, ?_⟩
      have hsub : closure ChartKind.halfDisk.modelRegion ⊆ {x : Plane | 0 ≤ x 0} :=
        closure_minimal (fun x hx ↦ hx.2)
          (isClosed_le continuous_const continuous_coordZero)
      exact hsub hzcl

/-- The chart model, regarded as a subset of its open perturbation disk. -/
def modelInPerturbation (k : ChartKind) : Set k.perturbationRegion :=
  {p | p.1 ∈ k.modelRegion}

theorem isClosed_modelInPerturbation (k : ChartKind) :
    IsClosed k.modelInPerturbation := by
  cases k with
  | disk =>
      have hAll : ChartKind.disk.modelInPerturbation = Set.univ := by
        ext p
        simp [modelInPerturbation, modelRegion, perturbationRegion]
      rw [hAll]
      exact isClosed_univ
  | halfDisk =>
      have hset : ChartKind.halfDisk.modelInPerturbation =
          {p : Metric.ball (0 : Plane) 1 | 0 ≤ p.1 0} := by
        ext p
        constructor
        · intro hp
          exact hp.2
        · intro hp
          exact ⟨p.2, hp⟩
      rw [hset]
      exact (isClosed_le continuous_const
        (continuous_coordZero.comp continuous_subtype_val))

/-- Identify the model-region subtype with its nested closed subtype in the perturbation disk. -/
def modelToPerturbationRange (k : ChartKind) :
    k.modelRegion ≃ₜ k.modelInPerturbation where
  toFun p := ⟨⟨p.1, k.modelRegion_subset_perturbationRegion p.2⟩, p.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Include a disk or half-disk model into the open disk used for perturbations. -/
def modelToPerturbation (k : ChartKind) :
    k.modelRegion → k.perturbationRegion :=
  fun p ↦ ⟨p.1, k.modelRegion_subset_perturbationRegion p.2⟩

theorem isClosedEmbedding_modelToPerturbation (k : ChartKind) :
    _root_.Topology.IsClosedEmbedding k.modelToPerturbation := by
  have h := (k.isClosed_modelInPerturbation.isClosedEmbedding_subtypeVal).comp
    k.modelToPerturbationRange.isClosedEmbedding
  have heq : k.modelToPerturbation =
      (Subtype.val : k.modelInPerturbation → k.perturbationRegion) ∘
        k.modelToPerturbationRange := by
    funext p
    rfl
  rw [heq]
  exact h

/-- The fixed finite chart patch, regarded inside the open perturbation disk. -/
def patchInPerturbation (k : ChartKind) : Set k.perturbationRegion :=
  {p | p.1 ∈ k.patchComplex.support}

/-- The chart patch remains compact after lifting it to the perturbation-region subtype. -/
theorem isCompact_patchInPerturbation (k : ChartKind) :
    IsCompact k.patchInPerturbation := by
  apply _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    k.patchComplex.isCompact_support
  intro p hp
  exact ⟨⟨p, k.modelRegion_subset_perturbationRegion
    (k.patchComplex_support_subset_modelRegion hp)⟩, rfl⟩

end ChartKind

namespace PartialTriangulation

variable {S : Type*} [TopologicalSpace S]

/-- The part of the intrinsic realization whose ambient image lies in a Rado chart domain. -/
def chartOverlap (T : PartialTriangulation S) (c : MoiseChart S) :
    Set T.toIntrinsic.realization :=
  T.embed ⁻¹' c.domain

theorem isOpen_chartOverlap (T : PartialTriangulation S) (c : MoiseChart S) :
    IsOpen (T.chartOverlap c) :=
  c.isOpen_domain.preimage T.isEmbedding.continuous

/-- Include an overlap point into the chart domain through the old partial triangulation. -/
def chartOverlapToDomain (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.domain :=
  fun x ↦ ⟨T.embed x.1, x.2⟩

theorem isEmbedding_chartOverlapToDomain (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapToDomain c) :=
  (T.isEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal).codRestrict
    c.domain fun x ↦ x.2

/-- Chart coordinates of the old partial triangulation on the overlap. -/
def chartOverlapMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → Plane :=
  fun x ↦ (c.chart (T.chartOverlapToDomain c x) : Plane)

theorem isEmbedding_chartOverlapMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapMap c) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.isEmbedding.comp (T.isEmbedding_chartOverlapToDomain c))

/-- The adaptive conforming triangulation of the whole old-complex/chart overlap. -/
noncomputable abbrev adaptiveOverlapComplex (T : PartialTriangulation S)
    (c : MoiseChart S) :=
  T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex (T.chartOverlap c)
    (T.isOpen_chartOverlap c)

/-- Chart coordinates on the support of the adaptive overlap triangulation. -/
noncomputable def adaptiveOverlapChartMap (T : PartialTriangulation S)
    (c : MoiseChart S) : (T.adaptiveOverlapComplex c).support → Plane :=
  fun p ↦ T.chartOverlapMap c p.1

theorem isEmbedding_adaptiveOverlapChartMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.adaptiveOverlapChartMap c) :=
  (T.isEmbedding_chartOverlapMap c).comp
    _root_.Topology.IsEmbedding.subtypeVal

/-- The overlap map with the chart model retained as codomain. -/
def chartOverlapModelMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.kind.modelRegion :=
  fun x ↦ c.chart (T.chartOverlapToDomain c x)

theorem isEmbedding_chartOverlapModelMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapModelMap c) :=
  c.chart.isEmbedding.comp (T.isEmbedding_chartOverlapToDomain c)

/-- The overlap map into the open perturbation disk. -/
def chartOverlapPerturbationMap (T : PartialTriangulation S) (c : MoiseChart S) :
    T.chartOverlap c → c.kind.perturbationRegion :=
  c.kind.modelToPerturbation ∘ T.chartOverlapModelMap c

theorem isEmbedding_chartOverlapPerturbationMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsEmbedding (T.chartOverlapPerturbationMap c) :=
  c.kind.isClosedEmbedding_modelToPerturbation.isEmbedding.comp
    (T.isEmbedding_chartOverlapModelMap c)

/-- The old polyhedral overlap is closed in the chart model. -/
theorem isClosedEmbedding_chartOverlapModelMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.chartOverlapModelMap c) := by
  let A : Set c.domain := {y | y.1 ∈ T.support}
  have hAclosed : IsClosed A :=
    T.isCompact_support.isClosed.preimage continuous_subtype_val
  have hrange : Set.range (T.chartOverlapModelMap c) = c.chart '' A := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, rfl⟩
      refine ⟨T.chartOverlapToDomain c x, ?_, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro z ⟨y, hyA, rfl⟩
      obtain ⟨x, hx⟩ := hyA
      let xU : T.chartOverlap c := ⟨x, by
        change T.embed x ∈ c.domain
        rw [hx]
        exact y.2⟩
      refine ⟨xU, ?_⟩
      change c.chart (T.chartOverlapToDomain c xU) = c.chart y
      apply congrArg c.chart
      apply Subtype.ext
      exact hx
  refine ⟨T.isEmbedding_chartOverlapModelMap c, ?_⟩
  rw [hrange]
  exact c.chart.isClosedMap A hAclosed

theorem isClosedEmbedding_chartOverlapPerturbationMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.chartOverlapPerturbationMap c) :=
  c.kind.isClosedEmbedding_modelToPerturbation.comp
    (T.isClosedEmbedding_chartOverlapModelMap c)

/-- Forget the support proof of the adaptive overlap complex.  Coverage makes this a
homeomorphism onto the whole overlap, hence a closed embedding. -/
noncomputable def adaptiveOverlapToOverlap (T : PartialTriangulation S)
    (c : MoiseChart S) : (T.adaptiveOverlapComplex c).support → T.chartOverlap c :=
  Subtype.val

theorem isClosedEmbedding_adaptiveOverlapToOverlap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.adaptiveOverlapToOverlap c) := by
  refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [show Set.range (T.adaptiveOverlapToOverlap c) =
      (T.adaptiveOverlapComplex c).support by
    exact Subtype.range_val]
  rw [T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex_support
    (T.chartOverlap c) (T.isOpen_chartOverlap c)]
  exact isClosed_univ

/-- Chart coordinates of the adaptive overlap, with the open perturbation disk retained as
codomain. -/
noncomputable def adaptiveOverlapPerturbationMap (T : PartialTriangulation S)
    (c : MoiseChart S) :
    (T.adaptiveOverlapComplex c).support → c.kind.perturbationRegion :=
  T.chartOverlapPerturbationMap c ∘ T.adaptiveOverlapToOverlap c

theorem isClosedEmbedding_adaptiveOverlapPerturbationMap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    _root_.Topology.IsClosedEmbedding (T.adaptiveOverlapPerturbationMap c) :=
  (T.isClosedEmbedding_chartOverlapPerturbationMap c).comp
    (T.isClosedEmbedding_adaptiveOverlapToOverlap c)

/-- The adaptive overlap as the relative plane graph realization used by the locally finite
Chapter 6 approximation. -/
noncomputable def adaptiveOverlapGraphRealization [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    (T.adaptiveOverlapComplex c).PlaneGraphRealization :=
  LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
    c.kind.perturbationRegion
    c.kind.isOpen_perturbationRegion (T.adaptiveOverlapChartMap c)
    (T.isEmbedding_adaptiveOverlapChartMap c)
    (fun p ↦ (T.adaptiveOverlapPerturbationMap c p).2)
    (by
      have heq : (fun p ↦
          (⟨T.adaptiveOverlapChartMap c p,
            (T.adaptiveOverlapPerturbationMap c p).2⟩ :
            c.kind.perturbationRegion)) = T.adaptiveOverlapPerturbationMap c := by
        funext p
        apply Subtype.ext
        rfl
      rw [heq]
      exact (T.isClosedEmbedding_adaptiveOverlapPerturbationMap c).isClosed_range)

/-- Crossing-weld plan, item 1, first entry condition: distinct faces of the adaptive overlap
complex carry distinct vertex triples. -/
theorem injective_faceVertices_adaptiveOverlapComplex (T : PartialTriangulation S)
    (c : MoiseChart S) :
    Function.Injective (T.adaptiveOverlapComplex c).faceVertices :=
  T.toIntrinsic.adaptiveGlobalFanFaceVertices_injective (T.chartOverlap c)
    (T.isOpen_chartOverlap c)

/-- Crossing-weld plan, item 1, second entry condition, in honest existential form: a strongly
positive tolerance on the chart overlap whose region-safe reduction separates every vertex of
the adaptive overlap complex from every face not containing it, in chart coordinates.  This is
the locally finite analogue of the finite `exists_uniform_vertex_face_separation`. -/
theorem exists_separating_control_adaptiveOverlap [T2Space S]
    (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ phi : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ phi ∧
      LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces
        (T.adaptiveOverlapGraphRealization c)
        (fun p ↦ regionSafeControl c.kind.perturbationRegion
          (T.chartOverlapMap c) phi p.1) := by
  classical
  have hmem : ∀ x : T.chartOverlap c,
      x ∈ (T.adaptiveOverlapComplex c).support := by
    intro x
    rw [T.toIntrinsic.adaptiveLocallyFiniteTriangleComplex_support
      (T.chartOverlap c) (T.isOpen_chartOverlap c)]
    trivial
  refine ⟨fun x ↦ LocallyFiniteTriangleComplex.vertexSeparationControl
    (T.adaptiveOverlapGraphRealization c) ⟨x, hmem x⟩, ?_, ?_⟩
  · intro C hC _
    have himage : IsCompact ((fun x : T.chartOverlap c ↦
        (⟨x, hmem x⟩ : (T.adaptiveOverlapComplex c).support)) '' C) :=
      hC.image (continuous_id.subtype_mk _)
    obtain ⟨eps, heps, hepsLe⟩ :=
      LocallyFiniteTriangleComplex.stronglyPositiveOn_vertexSeparationControl
        (G := T.adaptiveOverlapGraphRealization c) _ himage (Set.subset_univ _)
    exact ⟨eps, heps, fun x hx ↦ hepsLe _ ⟨x, hx, rfl⟩⟩
  · apply LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces.mono
      (LocallyFiniteTriangleComplex.separatesVerticesFromFaces_vertexSeparationControl
        (G := T.adaptiveOverlapGraphRealization c))
    intro p
    exact regionSafeControl_le_left _ _ _ _

/-- Crossing-weld plan, item 2, disjointness half: a replacement taking its overlap values in
the chart domain never collides with the old embedding outside the overlap.  Together with
`range_frontierGlue`, this is the crossing-disjointness input of
`isEmbedding_frontierGlue_of_matches`. -/
theorem disjoint_image_chartOverlap_embed_compl (T : PartialTriangulation S)
    (c : MoiseChart S) {g : T.toIntrinsic.realization → S}
    (hg : ∀ x ∈ T.chartOverlap c, g x ∈ c.domain) :
    Disjoint (g '' T.chartOverlap c) (T.embed '' (T.chartOverlap c)ᶜ) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyz⟩
  apply hy
  change T.embed y ∈ c.domain
  rw [hyz]
  exact hg x hx

/-- Crossing-weld plan, item 2, matching half (Moise's vanishing tolerance).  One strongly
positive control on the chart overlap such that EVERY chart-coordinate replacement of the old
embedding within that control matches the old embedding at the overlap frontier.

The plane-metric reduction `regionSafeControl` is deliberately not enough here: a C0 chart may
shear plane-close points apart near its frontier (compose a chart with the twist
`(r, θ) ↦ (r, θ + 1/(1-r))` of the disk: a radial displacement of a quarter of the distance to
the sphere is torn to unbounded angular displacement).  The modulus must therefore be extracted
from the chart homeomorphism itself.  This is the metric-target version; the surface version
`exists_chartMatchingControl` metrizes the compact second-countable surface and applies it. -/
theorem exists_chartMatchingControl_of_metricSpace {S' : Type*} [MetricSpace S']
    (T : PartialTriangulation S') (c : MoiseChart S') :
    ∃ mu : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : T.chartOverlap c → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S'),
        (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : T.chartOverlap c,
          dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y) →
        MatchesAtFrontier (T.chartOverlap c) g T.embed := by
  classical
  by_cases hFr : (frontier (T.chartOverlap c)).Nonempty
  swap
  · refine ⟨fun _ ↦ 1, fun C _ _ ↦ ⟨1, one_pos, fun _ _ ↦ le_rfl⟩, ?_⟩
    intro g' g hgval hclose x hx
    exact absurd ⟨x, hx⟩ hFr
  -- the compact frontier trace on the old complex
  have hFrCompact : IsCompact (T.embed '' frontier (T.chartOverlap c)) :=
    isClosed_frontier.isCompact.image T.isEmbedding.continuous
  have hFrNe : (T.embed '' frontier (T.chartOverlap c)).Nonempty := hFr.image _
  -- the surface scale, vanishing at the frontier
  set sS : T.chartOverlap c → ℝ := fun y ↦
    Metric.infDist (T.embed y.1) (T.embed '' frontier (T.chartOverlap c)) with hsS
  have hsSpos : ∀ y : T.chartOverlap c, 0 < sS y := by
    intro y
    apply (hFrCompact.isClosed.notMem_iff_infDist_pos hFrNe).mp
    rintro ⟨x, hxFr, hxy⟩
    have hxval : x = y.1 := T.isEmbedding.injective hxy
    rw [hxval] at hxFr
    exact hxFr.2 (mem_interior_iff_mem_nhds.mpr
      ((T.isOpen_chartOverlap c).mem_nhds y.2))
  have hsScont : Continuous sS :=
    (Metric.continuous_infDist_pt _).comp
      (T.isEmbedding.continuous.comp continuous_subtype_val)
  -- the inverse chart on the model region
  set psi : c.kind.modelRegion → S' := fun z ↦ (c.chart.symm z).1 with hpsi
  have hpsiCont : Continuous psi :=
    continuous_subtype_val.comp c.chart.symm.continuous
  have hpsiModel : ∀ y : T.chartOverlap c,
      psi (T.chartOverlapModelMap c y) = T.embed y.1 := by
    intro y
    change (c.chart.symm (c.chart (T.chartOverlapToDomain c y))).1 = T.embed y.1
    rw [c.chart.symm_apply_apply]
    rfl
  -- the admissible chart moduli at one overlap point
  set A : T.chartOverlap c → Set ℝ := fun y ↦
    {r | 0 ≤ r ∧ r ≤ 1 ∧ ∀ z : c.kind.modelRegion,
      dist (z : Plane) (T.chartOverlapMap c y) < r →
        dist (psi z) (T.embed y.1) ≤ sS y} with hA
  have hANe : ∀ y, (A y).Nonempty := by
    intro y
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    intro z hz
    exact absurd hz (not_lt.mpr dist_nonneg)
  have hAbdd : ∀ y, BddAbove (A y) := fun y ↦ ⟨1, fun r hr ↦ hr.2.1⟩
  -- one admissible modulus works uniformly on every compact set of the overlap
  have hUniform : ∀ C : Set (T.chartOverlap c), IsCompact C → C.Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C, min δ 1 ∈ A y := by
    intro C hC hCne
    obtain ⟨y₀, hy₀C, hy₀min⟩ := hC.exists_isMinOn hCne hsScont.continuousOn
    have hmpos : 0 < sS y₀ := hsSpos y₀
    -- the compact model trace of C and a compact plane neighborhood inside the model
    have hmodelCont : Continuous fun y : T.chartOverlap c ↦
        (T.chartOverlapModelMap c y : Plane) :=
      continuous_subtype_val.comp (T.isEmbedding_chartOverlapModelMap c).continuous
    set Z : Set Plane := (fun y : T.chartOverlap c ↦
      (T.chartOverlapModelMap c y : Plane)) '' C with hZ
    have hZcompact : IsCompact Z := hC.image hmodelCont
    have hZball : Z ⊆ Metric.ball (0 : Plane) 1 := by
      rintro z ⟨y, -, rfl⟩
      exact c.kind.modelRegion_subset_perturbationRegion
        (T.chartOverlapModelMap c y).2
    obtain ⟨δ₀, hδ₀, hthick⟩ :=
      hZcompact.exists_cthickening_subset_open Metric.isOpen_ball hZball
    set Kpl : Set Plane :=
      Metric.cthickening δ₀ Z ∩ closure c.kind.modelRegion with hKpl
    have hKplCompact : IsCompact Kpl :=
      hZcompact.cthickening.inter_right isClosed_closure
    have hKplModel : Kpl ⊆ c.kind.modelRegion := by
      rintro z ⟨hzthick, hzcl⟩
      exact c.kind.ball_inter_closure_modelRegion_subset ⟨hthick hzthick, hzcl⟩
    set KM : Set c.kind.modelRegion := Subtype.val ⁻¹' Kpl with hKM
    have hKMcompact : IsCompact KM :=
      LocallyFiniteTriangleComplex.PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        hKplCompact hKplModel
    -- uniform continuity of the compared distance on the compact product
    set Phi : T.chartOverlap c × c.kind.modelRegion → ℝ := fun p ↦
      dist (psi p.2) (T.embed p.1.1) with hPhi
    have hPhiCont : Continuous Phi := by
      apply Continuous.dist
      · exact hpsiCont.comp continuous_snd
      · exact T.isEmbedding.continuous.comp
          (continuous_subtype_val.comp continuous_fst)
    obtain ⟨δ₁, hδ₁, hδ₁close⟩ :=
      (Metric.uniformContinuousOn_iff.mp
        ((hC.prod hKMcompact).uniformContinuousOn_of_continuous
          hPhiCont.continuousOn)) (sS y₀) hmpos
    refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, ?_⟩
    intro y hyC
    refine ⟨le_min (lt_min hδ₁ hδ₀).le zero_le_one, min_le_right _ _, ?_⟩
    intro z hz
    have hzδ : dist (z : Plane) (T.chartOverlapModelMap c y : Plane) <
        min δ₁ δ₀ := by
      have hval : T.chartOverlapMap c y = (T.chartOverlapModelMap c y : Plane) := rfl
      rw [← hval]
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hcenter : (T.chartOverlapModelMap c y : Plane) ∈ Z :=
      Set.mem_image_of_mem _ hyC
    -- the perturbed point stays in the compact model neighborhood
    have hzK : z ∈ KM := by
      have hzball : (z : Plane) ∈ Metric.closedBall
          (T.chartOverlapModelMap c y : Plane) δ₀ :=
        Metric.mem_closedBall.mpr ((hzδ.trans_le (min_le_right _ _)).le)
      have hz1 : (z : Plane) ∈ Metric.cthickening δ₀ Z :=
        Metric.closedBall_subset_cthickening hcenter δ₀ hzball
      exact ⟨hz1, subset_closure z.2⟩
    -- compare with the unperturbed model point through uniform continuity
    have hpair : ((y, z) : T.chartOverlap c × c.kind.modelRegion) ∈ C ×ˢ KM :=
      ⟨hyC, hzK⟩
    have hbase : ((y, T.chartOverlapModelMap c y) :
        T.chartOverlap c × c.kind.modelRegion) ∈ C ×ˢ KM := by
      refine ⟨hyC, Metric.self_subset_cthickening _ hcenter, ?_⟩
      exact subset_closure (T.chartOverlapModelMap c y).2
    have hdistPair : dist ((y, z) : T.chartOverlap c × c.kind.modelRegion)
        (y, T.chartOverlapModelMap c y) < δ₁ := by
      rw [Prod.dist_eq]
      apply max_lt (by simpa using hδ₁)
      rw [Subtype.dist_eq]
      exact hzδ.trans_le (min_le_left _ _)
    have hPhiZero : Phi (y, T.chartOverlapModelMap c y) = 0 := by
      simp only [hPhi]
      rw [hpsiModel y, dist_self]
    have hlt := hδ₁close _ hpair _ hbase hdistPair
    rw [hPhiZero, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hlt
    exact hlt.le.trans (hy₀min hyC)
  -- the chart matching control: half the supremum of the admissible moduli
  have hsSupPos : ∀ y : T.chartOverlap c, 0 < sSup (A y) := by
    intro y
    obtain ⟨δ, hδ, hmem⟩ := hUniform {y} isCompact_singleton ⟨y, rfl⟩
    exact lt_of_lt_of_le (lt_min hδ one_pos) (le_csSup (hAbdd y) (hmem y rfl))
  refine ⟨fun y ↦ sSup (A y) / 2, ?_, ?_⟩
  · intro C hC _
    rcases C.eq_empty_or_nonempty with rfl | hCne
    · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
    obtain ⟨δ, hδ, hmem⟩ := hUniform C hC hCne
    refine ⟨min δ 1 / 2, by positivity, ?_⟩
    intro y hy
    have := le_csSup (hAbdd y) (hmem y hy)
    linarith
  · intro g' g hgval hclose x hx
    rw [tendsto_iff_dist_tendsto_zero]
    have hbase : Filter.Tendsto (fun y' : T.toIntrinsic.realization ↦
        2 * dist (T.embed y') (T.embed x))
        (nhdsWithin x (T.chartOverlap c)) (nhds 0) := by
      have hcont : Filter.Tendsto (fun y' : T.toIntrinsic.realization ↦
          dist (T.embed y') (T.embed x))
          (nhdsWithin x (T.chartOverlap c)) (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.mp
          ((T.isEmbedding.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
      have h2 := hcont.const_mul (2 : ℝ)
      rw [mul_zero] at h2
      exact h2
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hbase
    filter_upwards [self_mem_nhdsWithin] with y' hy'
    have hkey : dist (g y') (T.embed y') ≤ sS ⟨y', hy'⟩ := by
      obtain ⟨r, hrA, hr⟩ := exists_lt_of_lt_csSup (hANe ⟨y', hy'⟩)
        (half_lt_self (hsSupPos ⟨y', hy'⟩))
      have hdist : dist ((g' ⟨y', hy'⟩ : Plane)) (T.chartOverlapMap c ⟨y', hy'⟩) < r :=
        lt_of_le_of_lt (hclose ⟨y', hy'⟩) hr
      have hval := hrA.2.2 (g' ⟨y', hy'⟩) hdist
      rw [show g y' = psi (g' ⟨y', hy'⟩) from hgval ⟨y', hy'⟩]
      exact hval
    have hSle : sS ⟨y', hy'⟩ ≤ dist (T.embed y') (T.embed x) :=
      Metric.infDist_le_dist_of_mem ⟨x, hx, rfl⟩
    calc
      dist (g y') (T.embed x) ≤
          dist (g y') (T.embed y') + dist (T.embed y') (T.embed x) :=
        dist_triangle _ _ _
      _ ≤ dist (T.embed y') (T.embed x) + dist (T.embed y') (T.embed x) :=
        add_le_add (hkey.trans hSle) le_rfl
      _ = 2 * dist (T.embed y') (T.embed x) := by ring

private theorem matchesAtFrontier_and_disjoint_of_compl_not_nonempty
    {S' : Type*} [MetricSpace S'] (T : PartialTriangulation S')
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U) (hComp : ¬ Uᶜ.Nonempty)
    (g : T.toIntrinsic.realization → S') :
    MatchesAtFrontier U g T.embed ∧ Disjoint (g '' U) (T.embed '' Uᶜ) := by
  constructor
  · intro x hx
    exfalso
    apply hComp
    have hxcomp : x ∈ Uᶜ := by
      rw [← frontier_compl U] at hx
      exact hU.isClosed_compl.frontier_subset hx
    exact ⟨x, hxcomp⟩
  · rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, -⟩
    exact hComp ⟨y, hy⟩

/-- Relative form of the chart matching control.  On an arbitrary open subset of the chart
overlap, one control simultaneously makes the replacement converge to the old embedding at the
new frontier and keeps its image disjoint from the unchanged complement. -/
theorem exists_chartMatchingControlOn_of_metricSpace
    {S' : Type*} [MetricSpace S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (hsub : U ⊆ T.chartOverlap c) :
    ∃ mu : U → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : U → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S'),
        (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : U,
          dist (g' y : Plane)
            (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ≤ mu y) →
        MatchesAtFrontier U g T.embed ∧
          Disjoint (g '' U) (T.embed '' Uᶜ) := by
  classical
  let toOverlap : U → T.chartOverlap c := fun y ↦ ⟨y.1, hsub y.2⟩
  have htoOverlapCont : Continuous toOverlap :=
    Continuous.subtype_mk continuous_subtype_val _
  let model : U → c.kind.modelRegion :=
    fun y ↦ T.chartOverlapModelMap c (toOverlap y)
  let coord : U → Plane := fun y ↦ (model y : Plane)
  have hmodelCont : Continuous model :=
    (T.isEmbedding_chartOverlapModelMap c).continuous.comp htoOverlapCont
  have hcoordCont : Continuous coord :=
    continuous_subtype_val.comp hmodelCont
  by_cases hComp : Uᶜ.Nonempty
  swap
  · refine ⟨fun _ ↦ 1, fun C _ _ ↦ ⟨1, one_pos, fun _ _ ↦ le_rfl⟩, ?_⟩
    intro g' g hgval hclose
    exact matchesAtFrontier_and_disjoint_of_compl_not_nonempty T U hU hComp g
  have hCompCompact : IsCompact (T.embed '' Uᶜ) :=
    hU.isClosed_compl.isCompact.image T.isEmbedding.continuous
  have hCompNe : (T.embed '' Uᶜ).Nonempty := hComp.image _
  set sS : U → ℝ := fun y ↦
    Metric.infDist (T.embed y.1) (T.embed '' Uᶜ) / 2 with hsS
  have hsSpos : ∀ y : U, 0 < sS y := by
    intro y
    rw [hsS]
    apply half_pos
    apply (hCompCompact.isClosed.notMem_iff_infDist_pos hCompNe).mp
    rintro ⟨x, hxComp, hxy⟩
    have hxval : x = y.1 := T.isEmbedding.injective hxy
    rw [hxval] at hxComp
    exact hxComp y.2
  have hsScont : Continuous sS := by
    rw [hsS]
    exact ((Metric.continuous_infDist_pt _).comp
      (T.isEmbedding.continuous.comp continuous_subtype_val)).div_const 2
  set psi : c.kind.modelRegion → S' := fun z ↦ (c.chart.symm z).1 with hpsi
  have hpsiCont : Continuous psi :=
    continuous_subtype_val.comp c.chart.symm.continuous
  have hpsiModel : ∀ y : U, psi (model y) = T.embed y.1 := by
    intro y
    change (c.chart.symm
      (c.chart (T.chartOverlapToDomain c (toOverlap y)))).1 = T.embed y.1
    rw [c.chart.symm_apply_apply]
    rfl
  set A : U → Set ℝ := fun y ↦
    {r | 0 ≤ r ∧ r ≤ 1 ∧ ∀ z : c.kind.modelRegion,
      dist (z : Plane) (coord y) < r →
        dist (psi z) (T.embed y.1) ≤ sS y} with hA
  have hANe : ∀ y, (A y).Nonempty := by
    intro y
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    intro z hz
    exact absurd hz (not_lt.mpr dist_nonneg)
  have hAbdd : ∀ y, BddAbove (A y) := fun y ↦ ⟨1, fun r hr ↦ hr.2.1⟩
  have hUniform : ∀ C : Set U, IsCompact C → C.Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ C, min δ 1 ∈ A y := by
    intro C hC hCne
    obtain ⟨y₀, hy₀C, hy₀min⟩ :=
      hC.exists_isMinOn hCne hsScont.continuousOn
    have hmpos : 0 < sS y₀ := hsSpos y₀
    set Z : Set Plane := coord '' C with hZ
    have hZcompact : IsCompact Z := hC.image hcoordCont
    have hZball : Z ⊆ Metric.ball (0 : Plane) 1 := by
      rintro z ⟨y, -, rfl⟩
      exact c.kind.modelRegion_subset_perturbationRegion (model y).2
    obtain ⟨δ₀, hδ₀, hthick⟩ :=
      hZcompact.exists_cthickening_subset_open Metric.isOpen_ball hZball
    set Kpl : Set Plane :=
      Metric.cthickening δ₀ Z ∩ closure c.kind.modelRegion with hKpl
    have hKplCompact : IsCompact Kpl :=
      hZcompact.cthickening.inter_right isClosed_closure
    have hKplModel : Kpl ⊆ c.kind.modelRegion := by
      rintro z ⟨hzthick, hzcl⟩
      exact c.kind.ball_inter_closure_modelRegion_subset
        ⟨hthick hzthick, hzcl⟩
    set KM : Set c.kind.modelRegion := Subtype.val ⁻¹' Kpl with hKM
    have hKMcompact : IsCompact KM :=
      LocallyFiniteTriangleComplex.PlaneGraphRealization.isCompact_preimage_subtypeVal_of_subset
        hKplCompact hKplModel
    set Phi : U × c.kind.modelRegion → ℝ := fun p ↦
      dist (psi p.2) (T.embed p.1.1) with hPhi
    have hPhiCont : Continuous Phi := by
      apply Continuous.dist
      · exact hpsiCont.comp continuous_snd
      · exact T.isEmbedding.continuous.comp
          (continuous_subtype_val.comp continuous_fst)
    obtain ⟨δ₁, hδ₁, hδ₁close⟩ :=
      (Metric.uniformContinuousOn_iff.mp
        ((hC.prod hKMcompact).uniformContinuousOn_of_continuous
          hPhiCont.continuousOn)) (sS y₀) hmpos
    refine ⟨min δ₁ δ₀, lt_min hδ₁ hδ₀, ?_⟩
    intro y hyC
    refine ⟨le_min (lt_min hδ₁ hδ₀).le zero_le_one,
      min_le_right _ _, ?_⟩
    intro z hz
    have hzδ : dist (z : Plane) (coord y) < min δ₁ δ₀ :=
      lt_of_lt_of_le hz (min_le_left _ _)
    have hcenter : coord y ∈ Z := Set.mem_image_of_mem _ hyC
    have hzK : z ∈ KM := by
      have hzball : (z : Plane) ∈ Metric.closedBall (coord y) δ₀ :=
        Metric.mem_closedBall.mpr ((hzδ.trans_le (min_le_right _ _)).le)
      have hz1 : (z : Plane) ∈ Metric.cthickening δ₀ Z :=
        Metric.closedBall_subset_cthickening hcenter δ₀ hzball
      exact ⟨hz1, subset_closure z.2⟩
    have hpair : ((y, z) : U × c.kind.modelRegion) ∈ C ×ˢ KM :=
      ⟨hyC, hzK⟩
    have hbase : ((y, model y) : U × c.kind.modelRegion) ∈ C ×ˢ KM := by
      refine ⟨hyC, Metric.self_subset_cthickening _ hcenter, ?_⟩
      exact subset_closure (model y).2
    have hdistPair : dist ((y, z) : U × c.kind.modelRegion)
        (y, model y) < δ₁ := by
      rw [Prod.dist_eq]
      apply max_lt (by simpa using hδ₁)
      rw [Subtype.dist_eq]
      exact hzδ.trans_le (min_le_left _ _)
    have hPhiZero : Phi (y, model y) = 0 := by
      simp only [hPhi]
      rw [hpsiModel y, dist_self]
    have hlt := hδ₁close _ hpair _ hbase hdistPair
    rw [hPhiZero, Real.dist_eq, sub_zero,
      abs_of_nonneg dist_nonneg] at hlt
    exact hlt.le.trans (hy₀min hyC)
  have hsSupPos : ∀ y : U, 0 < sSup (A y) := by
    intro y
    obtain ⟨δ, hδ, hmem⟩ :=
      hUniform {y} isCompact_singleton ⟨y, rfl⟩
    exact lt_of_lt_of_le (lt_min hδ one_pos)
      (le_csSup (hAbdd y) (hmem y rfl))
  refine ⟨fun y ↦ sSup (A y) / 2, ?_, ?_⟩
  · intro C hC _
    rcases C.eq_empty_or_nonempty with rfl | hCne
    · exact ⟨1, one_pos, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
    obtain ⟨δ, hδ, hmem⟩ := hUniform C hC hCne
    refine ⟨min δ 1 / 2, by positivity, ?_⟩
    intro y hy
    have := le_csSup (hAbdd y) (hmem y hy)
    linarith
  · intro g' g hgval hclose
    have replacementClose (y : U) : dist (g y.1) (T.embed y.1) ≤ sS y := by
      obtain ⟨r, hrA, hr⟩ :=
        exists_lt_of_lt_csSup (hANe y) (half_lt_self (hsSupPos y))
      have hdist : dist ((g' y : Plane)) (coord y) < r :=
        lt_of_le_of_lt (hclose y) hr
      have hval := hrA.2.2 (g' y) hdist
      rw [show g y.1 = psi (g' y) from hgval y]
      exact hval
    constructor
    · intro x hx
      rw [tendsto_iff_dist_tendsto_zero]
      have hbase : Filter.Tendsto
          (fun y' : T.toIntrinsic.realization ↦
            2 * dist (T.embed y') (T.embed x))
          (nhdsWithin x U) (nhds 0) := by
        have hcont : Filter.Tendsto
            (fun y' : T.toIntrinsic.realization ↦
              dist (T.embed y') (T.embed x))
            (nhdsWithin x U) (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp
            ((T.isEmbedding.continuous.tendsto x).mono_left nhdsWithin_le_nhds)
        have h2 := hcont.const_mul (2 : ℝ)
        rw [mul_zero] at h2
        exact h2
      apply squeeze_zero'
        (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hbase
      filter_upwards [self_mem_nhdsWithin] with y' hy'
      have hkey := replacementClose ⟨y', hy'⟩
      have hxcomp : x ∈ Uᶜ := by
        rw [← frontier_compl U] at hx
        exact hU.isClosed_compl.frontier_subset hx
      have hSle : sS ⟨y', hy'⟩ ≤
          dist (T.embed y') (T.embed x) := by
        rw [hsS]
        have hinf : Metric.infDist (T.embed y') (T.embed '' Uᶜ) ≤
            dist (T.embed y') (T.embed x) :=
          Metric.infDist_le_dist_of_mem ⟨x, hxcomp, rfl⟩
        have hnonneg : 0 ≤ Metric.infDist (T.embed y') (T.embed '' Uᶜ) :=
          Metric.infDist_nonneg
        linarith
      calc
        dist (g y') (T.embed x) ≤
            dist (g y') (T.embed y') + dist (T.embed y') (T.embed x) :=
          dist_triangle _ _ _
        _ ≤ dist (T.embed y') (T.embed x) +
            dist (T.embed y') (T.embed x) :=
          add_le_add (hkey.trans hSle) le_rfl
        _ = 2 * dist (T.embed y') (T.embed x) := by ring
    · rw [Set.disjoint_left]
      rintro z ⟨x, hxU, rfl⟩ ⟨y, hyComp, hyEq⟩
      have hkey := replacementClose ⟨x, hxU⟩
      have hinf : Metric.infDist (T.embed x) (T.embed '' Uᶜ) ≤
          dist (T.embed x) (T.embed y) :=
        Metric.infDist_le_dist_of_mem ⟨y, hyComp, rfl⟩
      have heqdist : dist (T.embed x) (T.embed y) =
          dist (g x) (T.embed x) := by
        rw [← hyEq, dist_comm]
      rw [hsS] at hkey
      have hpos := hsSpos ⟨x, hxU⟩
      rw [hsS] at hpos
      linarith

/-- Crossing-weld plan, item 2, matching half, on the ambient surface.  The statement is
metric-free; the compact second-countable surface is metrized and the metric-target version is
applied at the compatible metric. -/
theorem exists_chartMatchingControl [T2Space S] [CompactSpace S]
    [SecondCountableTopology S] (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ mu : T.chartOverlap c → ℝ,
      StronglyPositiveOn Set.univ mu ∧
      ∀ (g' : T.chartOverlap c → c.kind.modelRegion)
        (g : T.toIntrinsic.realization → S),
        (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) →
        (∀ y : T.chartOverlap c,
          dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y) →
        MatchesAtFrontier (T.chartOverlap c) g T.embed := by
  let : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  exact exists_chartMatchingControl_of_metricSpace T c

/-- The geometric certificate retained from a controlled chart replacement.  Besides the
homeomorphism from the source open set, it records that every replacement face is exactly a
polygonal closed disk.  Keeping this witness exposed is what the final Radó conforming step
needs in order to take a finite arrangement near the compact chart patch. -/
structure PolygonalReplacementPresentation
    (X : Type*) [TopologicalSpace X] (V : Set Plane) where
  /-- The `complex` declaration. -/
  complex : LocallyFiniteTriangleComplex V
  /-- The `sourceHomeomorph` declaration. -/
  sourceHomeomorph : X ≃ₜ complex.support
  /-- The `facePolygon` declaration. -/
  facePolygon : complex.Face → PolygonalCircle
  /-- The plane map used to fill each abstract source triangle. -/
  faceFillingMap : complex.Face → Plane → Plane
  /-- The ambient face map is the retained filling in standard triangle coordinates. -/
  faceMap_eq : ∀ f x, (complex.faceMap f x).1 =
    faceFillingMap f (complex.facePlaneHomeomorph f x).1
  /-- The filling is genuinely finite PL, so its boundary marks can be pulled back to a
  finite source subdivision in the relative conforming step. -/
  faceCertificate : ∀ f, Nonempty (FinitePLHomeomorphBetween
    (faceFillingMap f) LocallyFiniteTriangleComplex.standardFaceRegion
      (facePolygon f).closedRegion)
  faceClosedRegion_subset : ∀ f, (facePolygon f).closedRegion ⊆ V
  faceCarrier_eq : ∀ f,
    complex.faceCarrier f =
      {q : V | q.1 ∈ (facePolygon f).closedRegion}

/-- The source points carried by one named polygonal replacement face. -/
def PolygonalReplacementPresentation.sourceFaceSet
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (Q : PolygonalReplacementPresentation U V) (f : Q.complex.Face) :
    Set K.realization :=
  {x | ∃ hx : x ∈ U,
    (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ Q.complex.faceCarrier f}

/-- Finite-source bookkeeping retained from an adaptive polygonal replacement.

Faces are grouped into finite adaptive tiles.  Any finite tile family is represented exactly
by a finite family of faces at one common midpoint level of the original intrinsic complex.
This is the missing source-side content behind Moise's conditions (f)--(h); keeping it separate
from the coordinate presentation lets the finite arrangement machinery remain generic. -/
structure PolygonalReplacementSourceAtlas
    (K : IntrinsicTwoComplex) (U : Set K.realization) (V : Set Plane)
    (Q : PolygonalReplacementPresentation U V) where
  /-- The `Tile` declaration. -/
  Tile : Type
  tileDecidableEq : DecidableEq Tile
  /-- The `tile` declaration. -/
  tile : Q.complex.Face → Tile
  /-- The `tileFaces` declaration. -/
  tileFaces : Tile → Finset Q.complex.Face
  mem_tileFaces : ∀ t f, f ∈ tileFaces t ↔ tile f = t
  /-- The `sourceTileCarrier` declaration. -/
  sourceTileCarrier : Tile → Set K.realization
  sourceTileCarrier_subset_open : ∀ t, sourceTileCarrier t ⊆ U
  sourceTileCarrier_locallyFinite :
    LocallyFinite fun t ↦ {x : U | x.1 ∈ sourceTileCarrier t}
  sourceTileCarrier_eq_faces : ∀ t,
    sourceTileCarrier t =
      ⋃ f : {f : Q.complex.Face // f ∈ tileFaces t},
        Q.sourceFaceSet f.1
  /-- An original maximal face containing each retained source fan face. -/
  sourceFaceParent : Q.complex.Face → K.Face
  sourceFaceSet_subset_parent : ∀ f,
    Q.sourceFaceSet f ⊆ K.faceCarrier (sourceFaceParent f).1
  /-- Every retained source face has one affine formula in the original intrinsic barycentric
  coordinates as a function of its standard planar face coordinates. -/
  sourceFaceStandardAffine : ∀ f : Q.complex.Face,
    ∃ a : Plane →ᵃ[ℝ] (K.Vertex → ℝ),
      ∀ x : Q.complex.ClosedFace f,
        (Q.sourceHomeomorph.symm
          (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := Q.complex) f x)).1.1 =
          a (Q.complex.facePlaneHomeomorph f x).1
  /-- The `commonLevel` declaration. -/
  commonLevel : Finset Tile → ℕ
  /-- The `levelFaces` declaration. -/
  levelFaces : (F : Finset Tile) → Finset (K.LevelFace (commonLevel F))
  sourceTiles_eq_levelFaces : ∀ F : Finset Tile,
    (⋃ t : {t : Tile // t ∈ F}, sourceTileCarrier t.1) =
      ⋃ u : {u : K.LevelFace (commonLevel F) // u ∈ levelFaces F},
        K.levelFaceCarrier u.1

attribute [instance] PolygonalReplacementSourceAtlas.tileDecidableEq

namespace PolygonalReplacementPresentation

variable {X : Type*} [TopologicalSpace X] {V : Set Plane}

open LocallyFiniteTriangleComplex.PlaneGraphRealization

/-- The canonical source parametrization of one retained replacement face.  It is obtained by
pulling the replacement face parametrization back through the presentation homeomorphism, so it
uses exactly the same abstract barycentric coordinates as `Q.complex.faceMap`. -/
noncomputable def sourceFaceMap
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face) :
    Q.complex.ClosedFace f → X :=
  Q.sourceHomeomorph.symm ∘ faceToSupport (K := Q.complex) f

theorem sourceHomeomorph_sourceFaceMap
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face)
    (x : Q.complex.ClosedFace f) :
    Q.sourceHomeomorph (Q.sourceFaceMap f x) =
      faceToSupport (K := Q.complex) f x := by
  exact Q.sourceHomeomorph.apply_symm_apply _

/-- Each canonical source face parametrization is an embedding. -/
theorem isEmbedding_sourceFaceMap [T2Space V]
    (Q : PolygonalReplacementPresentation X V) (f : Q.complex.Face) :
    _root_.Topology.IsEmbedding (Q.sourceFaceMap f) := by
  exact Q.sourceHomeomorph.symm.isEmbedding.comp
    (Q.complex.isEmbedding_faceToSupport f)

/-- Two canonical source-face points agree exactly when their zero-extended barycentric
coordinates agree.  This is the source-side face-to-face law inherited from the retained
replacement complex. -/
theorem sourceFaceMap_eq_iff
    (Q : PolygonalReplacementPresentation X V)
    {f g : Q.complex.Face}
    {x : Q.complex.ClosedFace f} {y : Q.complex.ClosedFace g} :
    Q.sourceFaceMap f x = Q.sourceFaceMap g y ↔
      extendFaceCoordinates (Q.complex.faceVertices f) x =
        extendFaceCoordinates (Q.complex.faceVertices g) y := by
  rw [← Q.sourceHomeomorph.injective.eq_iff,
    Q.sourceHomeomorph_sourceFaceMap f x,
    Q.sourceHomeomorph_sourceFaceMap g y]
  constructor
  · intro h
    exact Q.complex.faceMap_eq_iff.mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact Q.complex.faceMap_eq_iff.mpr h

/-- The canonical source parametrization has exactly the retained source face as its range. -/
theorem range_val_sourceFaceMap
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (Q : PolygonalReplacementPresentation U V) (f : Q.complex.Face) :
    Set.range (fun z ↦ (Q.sourceFaceMap f z).1) = Q.sourceFaceSet f := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    refine ⟨(Q.sourceFaceMap f z).2, ?_⟩
    rw [Q.sourceHomeomorph_sourceFaceMap f z]
    exact Set.mem_range_self z
  · rintro x ⟨hxU, hxFace⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqFace : q ∈ faceInSupport (K := Q.complex) f := by
      rw [Q.complex.faceInSupport_eq_preimage]
      exact hxFace
    obtain ⟨z, hz⟩ := hqFace
    refine ⟨z, ?_⟩
    change (Q.sourceHomeomorph.symm
      (faceToSupport (K := Q.complex) f z)).1 = x
    rw [hz]
    exact congrArg Subtype.val (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

/-- Only finitely many polygonal replacement faces meet a compact chart set.  This is the
finiteness cut used before passing to the common supporting-line arrangement. -/
theorem finite_facesMeeting
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    {f : Q.complex.Face | (Q.complex.faceCarrier f ∩ C).Nonempty}.Finite :=
  Q.complex.locallyFinite.finite_nonempty_inter_compact hC

/-- The finite subtype of replacement faces meeting a specified compact chart set. -/
noncomputable def FacesMeeting
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (_ : IsCompact C) : Type :=
  {f : Q.complex.Face | (Q.complex.faceCarrier f ∩ C).Nonempty}

noncomputable instance facesMeetingFintype
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (hC : IsCompact C) : Fintype (Q.FacesMeeting C hC) :=
  (Q.finite_facesMeeting hC).fintype

noncomputable instance facesMeetingDecidableEq
    (Q : PolygonalReplacementPresentation X V) (C : Set V)
    (hC : IsCompact C) : DecidableEq (Q.FacesMeeting C hC) :=
  Classical.decEq _

/-- A compact part of a locally finite replacement support is carried by the finitely many
faces which meet it.  This is the exact compact-to-finite cut used in Moise's condition (b). -/
theorem support_inter_subset_iUnion_facesMeeting
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    Q.complex.support ∩ C ⊆
      ⋃ f : Q.FacesMeeting C hC, Q.complex.faceCarrier f.1 := by
  rintro x ⟨hxSupport, hxC⟩
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxSupport
  let F : Q.FacesMeeting C hC :=
    ⟨f, ⟨x, hxf, hxC⟩⟩
  exact Set.mem_iUnion.mpr ⟨F, hxf⟩

/-- On the selected finite family, the preceding carrier union is the union of the retained
polygonal closed disks. -/
theorem support_inter_subset_selectedClosedRegion
    (Q : PolygonalReplacementPresentation X V) {C : Set V}
    (hC : IsCompact C) :
    Q.complex.support ∩ C ⊆
      {x : V | x.1 ∈ PolygonalFamily.closedRegion
        (fun f : Q.FacesMeeting C hC ↦ Q.facePolygon f.1)} := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp
    (Q.support_inter_subset_iUnion_facesMeeting hC hx)
  apply Set.mem_iUnion.mpr
  refine ⟨f, ?_⟩
  change x ∈ {q : V | q.1 ∈ (Q.facePolygon f.1).closedRegion}
  rw [← Q.faceCarrier_eq f.1]
  exact hxf

/-- The finite replacement faces which meet the fixed chart patch. -/
abbrev PatchFaces (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :=
  Q.FacesMeeting k.patchInPerturbation k.isCompact_patchInPerturbation

end PolygonalReplacementPresentation

namespace PolygonalReplacementSourceAtlas

/-- The finite family of adaptive source tiles touched by an arbitrary compact coordinate set.
This is the relative form needed after deleting the protected old trace: the compact set used
in the weld need not be the whole fixed chart patch. -/
noncomputable def tilesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    Finset A.Tile :=
  Finset.univ.image fun f : Q.FacesMeeting C hC ↦ A.tile f.1

theorem mem_tilesMeeting_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (t : A.Tile) :
    t ∈ A.tilesMeeting C hC ↔
      ∃ f : Q.FacesMeeting C hC, A.tile f.1 = t := by
  simp [PolygonalReplacementSourceAtlas.tilesMeeting]

/-- All replacement fan faces belonging to a tile touched by `C`. -/
noncomputable def tileFaceFinsetMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    Finset Q.complex.Face :=
  (A.tilesMeeting C hC).biUnion A.tileFaces

/-- The `TileFacesMeeting` declaration. -/
abbrev TileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :=
  {f : Q.complex.Face // f ∈ A.tileFaceFinsetMeeting C hC}

theorem mem_tileFaceFinsetMeeting_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : Q.complex.Face) :
    f ∈ A.tileFaceFinsetMeeting C hC ↔
      ∃ t ∈ A.tilesMeeting C hC, f ∈ A.tileFaces t := by
  simp [PolygonalReplacementSourceAtlas.tileFaceFinsetMeeting]

/-- Every face meeting `C` belongs to the whole-tile closure of the selected family. -/
theorem faceMeeting_mem_tileFaceFinsetMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : Q.FacesMeeting C hC) :
    f.1 ∈ A.tileFaceFinsetMeeting C hC := by
  apply (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mpr
  refine ⟨A.tile f.1, ?_, ?_⟩
  · exact (A.mem_tilesMeeting_iff C hC (A.tile f.1)).mpr ⟨f, rfl⟩
  · exact (A.mem_tileFaces (A.tile f.1) f.1).2 rfl

/-- Closing under the adaptive tiles touched by `C` is exactly the union of their named
replacement faces. -/
theorem sourceTilesMeeting_eq_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ t : {t : A.Tile // t ∈ A.tilesMeeting C hC},
        A.sourceTileCarrier t.1) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    rw [A.sourceTileCarrier_eq_faces t.1] at hxt
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxt
    let f' : A.TileFacesMeeting C hC :=
      ⟨f.1, (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mpr
        ⟨t.1, t.2, f.2⟩⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩
  · intro x hx
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, hft⟩ :=
      (A.mem_tileFaceFinsetMeeting_iff C hC f.1).mp f.2
    let t' : {t : A.Tile // t ∈ A.tilesMeeting C hC} := ⟨t, ht⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t', ?_⟩
    rw [A.sourceTileCarrier_eq_faces t]
    let f' : {q : Q.complex.Face // q ∈ A.tileFaces t} := ⟨f.1, hft⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩

/-- The source selected by an arbitrary compact coordinate set is a literal finite subcomplex
at one common midpoint level of the original intrinsic triangulation. -/
theorem sourceTileFacesMeeting_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 := by
  rw [← A.sourceTilesMeeting_eq_faces C hC]
  exact A.sourceTiles_eq_levelFaces (A.tilesMeeting C hC)

theorem isCompact_sourceTileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    IsCompact (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) := by
  rw [A.sourceTileFacesMeeting_eq_levelFaces C hC]
  exact isCompact_iUnion fun u ↦ K.isCompact_levelFaceCarrier u.1

theorem sourceTileFacesMeeting_subset_open
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) ⊆ U := by
  intro x hx
  obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
  exact hxFace.choose

/-- The coordinate preimage of `C` is contained in its whole-tile source closure. -/
theorem coordinatePreimage_subset_sourceTileFacesMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ C} ⊆
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rintro x ⟨hxU, hxC⟩
  let y := Q.sourceHomeomorph ⟨x, hxU⟩
  have hySelected := Q.support_inter_subset_iUnion_facesMeeting hC ⟨y.2, hxC⟩
  obtain ⟨f, hyFace⟩ := Set.mem_iUnion.mp hySelected
  let f' : A.TileFacesMeeting C hC :=
    ⟨f.1, A.faceMeeting_mem_tileFaceFinsetMeeting C hC f⟩
  apply Set.mem_iUnion.mpr
  exact ⟨f', hxU, hyFace⟩

/-- The finite family of adaptive source tiles touched by the compact patch.  The conforming
extension must retain whole tiles, rather than only the individual fan faces which happen to
meet the patch. -/
noncomputable def patchTiles
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    Finset A.Tile :=
  Finset.univ.image fun f : Q.PatchFaces k ↦ A.tile f.1

theorem mem_patchTiles_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (t : A.Tile) :
    t ∈ A.patchTiles ↔ ∃ f : Q.PatchFaces k, A.tile f.1 = t := by
  simp [PolygonalReplacementSourceAtlas.patchTiles]

/-- All replacement fan faces belonging to a tile touched by the patch. -/
noncomputable def patchTileFaceFinset
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    Finset Q.complex.Face :=
  A.patchTiles.biUnion A.tileFaces

/-- The `PatchTileFaces` declaration. -/
abbrev PatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :=
  {f : Q.complex.Face // f ∈ A.patchTileFaceFinset}

theorem mem_patchTileFaceFinset_iff
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : Q.complex.Face) :
    f ∈ A.patchTileFaceFinset ↔
      ∃ t ∈ A.patchTiles, f ∈ A.tileFaces t := by
  simp [PolygonalReplacementSourceAtlas.patchTileFaceFinset]

/-- Every face which meets the patch belongs to the whole-tile closure. -/
theorem patchFace_mem_patchTileFaceFinset
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : Q.PatchFaces k) :
    f.1 ∈ A.patchTileFaceFinset := by
  apply (A.mem_patchTileFaceFinset_iff f.1).mpr
  refine ⟨A.tile f.1, ?_, ?_⟩
  · exact (A.mem_patchTiles_iff (A.tile f.1)).mpr ⟨f, rfl⟩
  · exact (A.mem_tileFaces (A.tile f.1) f.1).2 rfl

/-- Closing under touched adaptive tiles changes the finite coordinate family, but its source is
still exactly the union of those finitely many named tiles. -/
theorem sourcePatchTiles_eq_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ t : {t : A.Tile // t ∈ A.patchTiles}, A.sourceTileCarrier t.1) =
      ⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    rw [A.sourceTileCarrier_eq_faces t.1] at hxt
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxt
    let f' : A.PatchTileFaces :=
      ⟨f.1, (A.mem_patchTileFaceFinset_iff f.1).mpr ⟨t.1, t.2, f.2⟩⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩
  · intro x hx
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, hft⟩ := (A.mem_patchTileFaceFinset_iff f.1).mp f.2
    let t' : {t : A.Tile // t ∈ A.patchTiles} := ⟨t, ht⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t', ?_⟩
    rw [A.sourceTileCarrier_eq_faces t]
    let f' : {q : Q.complex.Face // q ∈ A.tileFaces t} := ⟨f.1, hft⟩
    exact Set.mem_iUnion.mpr ⟨f', hxf⟩

/-- The whole-tile closure is therefore a literal finite subcomplex at one common midpoint
level of the original intrinsic triangulation. -/
theorem sourcePatchTileFaces_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) =
      ⋃ u : {u : K.LevelFace (A.commonLevel A.patchTiles) //
          u ∈ A.levelFaces A.patchTiles},
        K.levelFaceCarrier u.1 := by
  rw [← A.sourcePatchTiles_eq_faces]
  exact A.sourceTiles_eq_levelFaces A.patchTiles

/-- The tile-closed source selected for the finite weld is compact.  This is the compact
subpolyhedron on which the later relative boundary extension is allowed to change the old
triangulation. -/
theorem isCompact_sourcePatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    IsCompact (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) := by
  rw [A.sourcePatchTileFaces_eq_levelFaces]
  exact isCompact_iUnion fun u ↦ K.isCompact_levelFaceCarrier u.1

/-- Every point of the tile-closed source subcomplex still lies in the open region on which
the controlled replacement was constructed. -/
theorem sourcePatchTileFaces_subset_open
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) ⊆ U := by
  intro x hx
  obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
  exact hxFace.choose

/-- The whole old trace over the fixed patch is carried by the tile-closed source selection.
This is the source-side coverage needed before cutting the old complex along its finite
attaching boundary. -/
theorem coordinatePreimage_patch_subset_sourcePatchTileFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1 ∈ k.patchInPerturbation} ⊆
      ⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1 := by
  rintro x ⟨hxU, hxPatch⟩
  let y := Q.sourceHomeomorph ⟨x, hxU⟩
  have hySelected := Q.support_inter_subset_iUnion_facesMeeting
    k.isCompact_patchInPerturbation ⟨y.2, hxPatch⟩
  obtain ⟨f, hyFace⟩ := Set.mem_iUnion.mp hySelected
  let f' : A.PatchTileFaces := ⟨f.1, A.patchFace_mem_patchTileFaceFinset f⟩
  apply Set.mem_iUnion.mpr
  exact ⟨f', hxU, hyFace⟩

end PolygonalReplacementSourceAtlas

namespace PolygonalReplacementPresentation

variable {X : Type*} [TopologicalSpace X] {V : Set Plane}

/-- The polygonal disk belonging to one replacement face meeting the chart patch. -/
def patchFacePolygon (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    Q.PatchFaces k → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The fixed patch lies in the enclosing triangle used for the finite family of all
replacement faces which meet it.  The point is that every chart patch lies in the unit ball,
while `PolygonalFamily.enclosingRadius` is at least one. -/
theorem patchComplex_support_subset_arrangementMesh
    (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    k.patchComplex.support ⊆
      (PolygonalFamily.arrangementMesh (Q.patchFacePolygon k)).toPlaneComplex.support := by
  rw [PolygonalFamily.arrangementMesh_support,
    PolygonalFamily.enclosingMesh, TriangleMesh.single_support]
  apply k.patchComplex_support_subset_modelRegion.trans
  apply k.modelRegion_subset_perturbationRegion.trans
  apply Metric.ball_subset_closedBall.trans
  apply (Metric.closedBall_subset_closedBall
    (le_max_right
      ((PolygonalFamily.isCompact_closedRegion
        (Q.patchFacePolygon k)).isBounded.subset_closedBall (0 : Plane)).choose 1)).trans
  exact PolygonalCircle.closedBall_subset_enclosingTriangle
    (PolygonalFamily.enclosingRadius_pos (Q.patchFacePolygon k))

/-- The old replacement trace over the fixed patch is contained in the finite polygonal family
selected above. -/
theorem support_inter_patch_subset_closedRegion
    (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    Q.complex.support ∩ k.patchInPerturbation ⊆
      {x : k.perturbationRegion |
        x.1 ∈ PolygonalFamily.closedRegion (Q.patchFacePolygon k)} := by
  exact Q.support_inter_subset_selectedClosedRegion
    k.isCompact_patchInPerturbation

/-- The fixed patch as a triangle mesh, for synchronization with the replacement polygons. -/
noncomputable def patchTriangleMesh (k : ChartKind) : TriangleMesh :=
  k.patchComplex.toTriangleMesh

/-- The finite old-side coordinate mesh in the common old/patch arrangement. -/
noncomputable def patchOldMesh (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh (Q.patchFacePolygon k)
    (patchTriangleMesh k) (fun _ ↦ True)

/-- The finite new-patch coordinate mesh in the same common arrangement. -/
noncomputable def patchNewMesh (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh (Q.patchFacePolygon k)
    (patchTriangleMesh k)

theorem patchOldMesh_support (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    (Q.patchOldMesh k).toPlaneComplex.support =
      PolygonalFamily.closedRegion (Q.patchFacePolygon k) := by
  simpa [patchOldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support
      (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True))

theorem patchNewMesh_support (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    (Q.patchNewMesh k).toPlaneComplex.support = k.patchComplex.support := by
  have hsub : (patchTriangleMesh k).toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (Q.patchFacePolygon k)).toPlaneComplex.support := by
    rw [patchTriangleMesh, k.patchComplex.toTriangleMesh_support
      k.patchComplex_pure]
    exact Q.patchComplex_support_subset_arrangementMesh k
  exact (PolygonalFamily.targetSynchronizedMesh_support
    (Q.patchFacePolygon k) (patchTriangleMesh k) hsub).trans
      (k.patchComplex.toTriangleMesh_support k.patchComplex_pure)

/-- Both coordinate sides are restrictions of one ambient triangle mesh, so every retained
maximal face is a triangle. -/
theorem patchMeshes_triangle_card (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    ∀ t ∈ (Q.patchOldMesh k).triangles ∪ (Q.patchNewMesh k).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (Q.patchOldMesh k).card_triangle t htOld
  · exact (Q.patchNewMesh k).card_triangle t htNew

/-- The two finite coordinate sides satisfy the joint surface edge-incidence bound. -/
theorem patchMeshes_joint_edge_valence (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (e : Finset (Q.patchOldMesh k).Vertex) (he : e.card = 2) :
    (((Q.patchOldMesh k).triangles ∪
        (Q.patchNewMesh k).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence
    (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True) e he

theorem patchMeshes_surface_edge_valence (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion) :
    ∀ e ∈ ((Q.patchOldMesh k).triangles ∪
        (Q.patchNewMesh k).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((Q.patchOldMesh k).triangles ∪
          (Q.patchNewMesh k).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact Q.patchMeshes_joint_edge_valence k e (Finset.mem_powersetCard.mp het).2

/-- The two coordinate embeddings agree exactly when their common barycentric coordinates do.
This is both interface clauses (`hagree` and `hsep`) of the later ambient weld, before composing
with the chart homeomorphism. -/
theorem patchMeshes_coordinateEmbed_eq_iff (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (x : GeometricRealization (Q.patchOldMesh k).Vertex
      (Q.patchOldMesh k).triangles)
    (y : GeometricRealization (Q.patchNewMesh k).Vertex
      (Q.patchNewMesh k).triangles) :
    (Q.patchOldMesh k).coordinateEmbed x =
        (Q.patchNewMesh k).coordinateEmbed y ↔
      (x : (Q.patchOldMesh k).Vertex → ℝ) =
        (y : (Q.patchNewMesh k).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement (Q.patchFacePolygon k)
    (patchTriangleMesh k)
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem
        (Q.patchFacePolygon k) (patchTriangleMesh k) (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem
        (Q.patchFacePolygon k) (patchTriangleMesh k)).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- If the retained source coordinates land in a closed model region, the whole replacement
support does too. -/
theorem support_subset_modelRegion_of_coordinate (k : ChartKind)
    (Q : PolygonalReplacementPresentation X V)
    (g' : X → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    Q.complex.support ⊆ {z : V | z.1 ∈ k.modelRegion} := by
  intro z hz
  let zSupport : Q.complex.support := ⟨z, hz⟩
  obtain ⟨y, hy⟩ := Q.sourceHomeomorph.surjective zSupport
  have hyval : (Q.sourceHomeomorph y).1.1 = z.1 :=
    congrArg (fun w : Q.complex.support ↦ w.1.1) hy
  change z.1 ∈ k.modelRegion
  rw [← hyval, ← hcoord y]
  exact (g' y).2

/-- Consequently every selected face polygon used by the finite patch arrangement lies in the
chart model, including the half-plane condition in the bordered case. -/
theorem patchFaceClosedRegion_subset_modelRegion (k : ChartKind)
    (Q : PolygonalReplacementPresentation X k.perturbationRegion)
    (g' : X → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion (Q.patchFacePolygon k) ⊆ k.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ k.perturbationRegion :=
    Q.faceClosedRegion_subset f.1 hxf
  let z : k.perturbationRegion := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate k g' hcoord hzSupport

/-- The old finite coordinate side transported back to the ambient surface chart. -/
noncomputable def patchOldSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    GeometricRealization (Q.patchOldMesh c.kind).Vertex
      (Q.patchOldMesh c.kind).triangles → S :=
  fun x ↦ (c.chart.symm
    ((Q.patchOldMesh c.kind).coordinateEmbedInto c.kind.modelRegion (by
      rw [Q.patchOldMesh_support c.kind]
      exact Q.patchFaceClosedRegion_subset_modelRegion c.kind g' hcoord) x)).1

/-- The synchronized fixed-patch side transported back by the same chart. -/
noncomputable def patchNewSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion) :
    GeometricRealization (Q.patchNewMesh c.kind).Vertex
      (Q.patchNewMesh c.kind).triangles → S :=
  fun x ↦ (c.chart.symm
    ((Q.patchNewMesh c.kind).coordinateEmbedInto c.kind.modelRegion (by
      rw [Q.patchNewMesh_support c.kind]
      exact c.kind.patchComplex_support_subset_modelRegion) x)).1

theorem isEmbedding_patchOldSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    _root_.Topology.IsEmbedding (Q.patchOldSurfaceEmbed c g' hcoord) := by
  let hmodel : (Q.patchOldMesh c.kind).toPlaneComplex.support ⊆
      c.kind.modelRegion := by
    rw [Q.patchOldMesh_support c.kind]
    exact Q.patchFaceClosedRegion_subset_modelRegion c.kind g' hcoord
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((Q.patchOldMesh c.kind).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion hmodel))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (Q.patchOldMesh c.kind).coordinateEmbedInto
        c.kind.modelRegion hmodel) =
      Q.patchOldSurfaceEmbed c g' hcoord := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_patchNewSurfaceEmbed {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion) :
    _root_.Topology.IsEmbedding (Q.patchNewSurfaceEmbed c) := by
  let hmodel : (Q.patchNewMesh c.kind).toPlaneComplex.support ⊆
      c.kind.modelRegion := by
    rw [Q.patchNewMesh_support c.kind]
    exact c.kind.patchComplex_support_subset_modelRegion
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((Q.patchNewMesh c.kind).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion hmodel))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (Q.patchNewMesh c.kind).coordinateEmbedInto
        c.kind.modelRegion hmodel) = Q.patchNewSurfaceEmbed c := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- After transport by the chart, equality of old- and new-side points is still exactly equality
of their common barycentric coordinate functions. -/
theorem patchSurfaceEmbed_eq_iff {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1)
    (x : GeometricRealization (Q.patchOldMesh c.kind).Vertex
      (Q.patchOldMesh c.kind).triangles)
    (y : GeometricRealization (Q.patchNewMesh c.kind).Vertex
      (Q.patchNewMesh c.kind).triangles) :
    Q.patchOldSurfaceEmbed c g' hcoord x = Q.patchNewSurfaceEmbed c y ↔
      (x : (Q.patchOldMesh c.kind).Vertex → ℝ) =
        (y : (Q.patchNewMesh c.kind).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold patchOldSurfaceEmbed patchNewSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hmodel := c.chart.symm.injective hchart
    have hplane := congrArg Subtype.val hmodel
    exact (Q.patchMeshes_coordinateEmbed_eq_iff c.kind x y).mp hplane
  · intro hxy
    have hplane :=
      (Q.patchMeshes_coordinateEmbed_eq_iff c.kind x y).mpr hxy
    unfold patchOldSurfaceEmbed patchNewSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

/-- The finite compact part of the crossing construction already has exactly the common-vertex
interface consumed by `PartialTriangulation.exists_glued`.  What remains in the global Radó
step is to extend its old side over the complement of the selected adaptive faces. -/
theorem exists_patch_local_weld {S : Type*} [TopologicalSpace S]
    (c : MoiseChart S)
    (Q : PolygonalReplacementPresentation X c.kind.perturbationRegion)
    (g' : X → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁)
          (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁)
          (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t => t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t => e ⊆ t).card ≤ 2) := by
  refine ⟨(Q.patchOldMesh c.kind).Vertex, inferInstance, inferInstance,
    (Q.patchOldMesh c.kind).triangles, (Q.patchNewMesh c.kind).triangles,
    Q.patchOldSurfaceEmbed c g' hcoord, Q.patchNewSurfaceEmbed c,
    Q.patchMeshes_triangle_card c.kind,
    Q.isEmbedding_patchOldSurfaceEmbed c g' hcoord,
    Q.isEmbedding_patchNewSurfaceEmbed c, ?_, ?_,
    Q.patchMeshes_surface_edge_valence c.kind⟩
  · intro x y hxy
    exact (Q.patchSurfaceEmbed_eq_iff c g' hcoord x y).mpr hxy
  · intro x y hxy
    exact (Q.patchSurfaceEmbed_eq_iff c g' hcoord x y).mp hxy

end PolygonalReplacementPresentation

namespace SynchronizedPatch

variable {ι : Type*} [Fintype ι]

/-- The part of a synchronized arrangement belonging to one named polygon. -/
noncomputable def singlePolygonMesh (J : ι → PolygonalCircle)
    (N : TriangleMesh) (i : ι) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J N (fun j ↦ j = i)

theorem singlePolygonMesh_support (J : ι → PolygonalCircle)
    (N : TriangleMesh) (i : ι) :
    (singlePolygonMesh J N i).toPlaneComplex.support = (J i).closedRegion := by
  rw [singlePolygonMesh, PolygonalFamily.selectedSynchronizedMesh_support]
  simp only [PolygonalFamily.selectedClosedRegion]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji, hxj⟩ := Set.mem_iUnion.mp hj
    simpa only [hji] using hxj
  · intro x hx
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩

/-- Every fixed chart patch lies in the enclosing arrangement used to synchronize it with an
arbitrary finite polygonal family. -/
theorem patchComplex_support_subset_arrangementMesh (k : ChartKind)
    (J : ι → PolygonalCircle) :
    k.patchComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support := by
  rw [PolygonalFamily.arrangementMesh_support, PolygonalFamily.enclosingMesh,
    TriangleMesh.single_support]
  apply k.patchComplex_support_subset_modelRegion.trans
  apply k.modelRegion_subset_perturbationRegion.trans
  apply Metric.ball_subset_closedBall.trans
  apply (Metric.closedBall_subset_closedBall
    (le_max_right ((PolygonalFamily.isCompact_closedRegion J).isBounded.subset_closedBall
      (0 : Plane)).choose 1)).trans
  exact PolygonalCircle.closedBall_subset_enclosingTriangle
    (PolygonalFamily.enclosingRadius_pos J)

/-- The old member of the common arrangement, restricted to the chosen polygonal union. -/
noncomputable def synchronizedPatchOldMesh (k : ChartKind)
    (J : ι → PolygonalCircle) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J k.patchComplex.toTriangleMesh (fun _ ↦ True)

/-- The fixed chart patch in the same common arrangement. -/
noncomputable def synchronizedPatchNewMesh (k : ChartKind)
    (J : ι → PolygonalCircle) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh J k.patchComplex.toTriangleMesh

theorem synchronizedPatchOldMesh_support (k : ChartKind)
    (J : ι → PolygonalCircle) :
    (synchronizedPatchOldMesh k J).toPlaneComplex.support =
      PolygonalFamily.closedRegion J := by
  simpa [synchronizedPatchOldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support J k.patchComplex.toTriangleMesh
      (fun _ ↦ True))

theorem synchronizedPatchNewMesh_support (k : ChartKind)
    (J : ι → PolygonalCircle) :
    (synchronizedPatchNewMesh k J).toPlaneComplex.support = k.patchComplex.support := by
  have hsub : k.patchComplex.toTriangleMesh.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support := by
    rw [k.patchComplex.toTriangleMesh_support k.patchComplex_pure]
    exact patchComplex_support_subset_arrangementMesh k J
  exact (PolygonalFamily.targetSynchronizedMesh_support J
    k.patchComplex.toTriangleMesh hsub).trans
    (k.patchComplex.toTriangleMesh_support k.patchComplex_pure)

theorem synchronizedPatchMeshes_triangle_card (k : ChartKind)
    (J : ι → PolygonalCircle) :
    ∀ t ∈ (synchronizedPatchOldMesh k J).triangles ∪
        (synchronizedPatchNewMesh k J).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (synchronizedPatchOldMesh k J).card_triangle t htOld
  · exact (synchronizedPatchNewMesh k J).card_triangle t htNew

theorem synchronizedPatchMeshes_surface_edge_valence (k : ChartKind)
    (J : ι → PolygonalCircle) :
    ∀ e ∈ ((synchronizedPatchOldMesh k J).triangles ∪
        (synchronizedPatchNewMesh k J).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((synchronizedPatchOldMesh k J).triangles ∪
          (synchronizedPatchNewMesh k J).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence J
    k.patchComplex.toTriangleMesh
    (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- Both restrictions of the synchronized arrangement use literally the same ambient vertex
coordinates. -/
theorem synchronizedPatchMeshes_coordinateEmbed_eq_iff (k : ChartKind)
    (J : ι → PolygonalCircle)
    (x : GeometricRealization (synchronizedPatchOldMesh k J).Vertex
      (synchronizedPatchOldMesh k J).triangles)
    (y : GeometricRealization (synchronizedPatchNewMesh k J).Vertex
      (synchronizedPatchNewMesh k J).triangles) :
    (synchronizedPatchOldMesh k J).coordinateEmbed x =
        (synchronizedPatchNewMesh k J).coordinateEmbed y ↔
      (x : (synchronizedPatchOldMesh k J).Vertex → ℝ) =
        (y : (synchronizedPatchNewMesh k J).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement J k.patchComplex.toTriangleMesh
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem J
        k.patchComplex.toTriangleMesh
        (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem J
        k.patchComplex.toTriangleMesh).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- Transport the finite polygonal member of a synchronized patch weld to the surface. -/
noncomputable def synchronizedPatchOldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (synchronizedPatchOldMesh c.kind J).Vertex
      (synchronizedPatchOldMesh c.kind J).triangles → S :=
  fun x ↦ (c.chart.symm
    ((synchronizedPatchOldMesh c.kind J).coordinateEmbedInto c.kind.modelRegion (by
      rw [synchronizedPatchOldMesh_support]
      exact hmodel) x)).1

/-- Transport the fixed-patch member of a synchronized weld by the same chart. -/
noncomputable def synchronizedPatchNewSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) :
    GeometricRealization (synchronizedPatchNewMesh c.kind J).Vertex
      (synchronizedPatchNewMesh c.kind J).triangles → S :=
  fun x ↦ (c.chart.symm
    ((synchronizedPatchNewMesh c.kind J).coordinateEmbedInto c.kind.modelRegion (by
      rw [synchronizedPatchNewMesh_support]
      exact c.kind.patchComplex_support_subset_modelRegion) x)).1

theorem isEmbedding_synchronizedPatchOldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (synchronizedPatchOldSurfaceEmbed c J hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((synchronizedPatchOldMesh c.kind J).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchOldMesh_support]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (synchronizedPatchOldMesh c.kind J).coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchOldMesh_support]
          exact hmodel)) = synchronizedPatchOldSurfaceEmbed c J hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_synchronizedPatchNewSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) :
    _root_.Topology.IsEmbedding (synchronizedPatchNewSurfaceEmbed c J) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((synchronizedPatchNewMesh c.kind J).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchNewMesh_support]
          exact c.kind.patchComplex_support_subset_modelRegion)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (synchronizedPatchNewMesh c.kind J).coordinateEmbedInto
        c.kind.modelRegion (by
          rw [synchronizedPatchNewMesh_support]
          exact c.kind.patchComplex_support_subset_modelRegion)) =
      synchronizedPatchNewSurfaceEmbed c J := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem synchronizedPatchSurfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (x : GeometricRealization (synchronizedPatchOldMesh c.kind J).Vertex
      (synchronizedPatchOldMesh c.kind J).triangles)
    (y : GeometricRealization (synchronizedPatchNewMesh c.kind J).Vertex
      (synchronizedPatchNewMesh c.kind J).triangles) :
    synchronizedPatchOldSurfaceEmbed c J hmodel x =
        synchronizedPatchNewSurfaceEmbed c J y ↔
      (x : (synchronizedPatchOldMesh c.kind J).Vertex → ℝ) =
        (y : (synchronizedPatchNewMesh c.kind J).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold synchronizedPatchOldSurfaceEmbed synchronizedPatchNewSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (synchronizedPatchMeshes_coordinateEmbed_eq_iff c.kind J x y).mp hplane
  · intro hxy
    have hplane :=
      (synchronizedPatchMeshes_coordinateEmbed_eq_iff c.kind J x y).mpr hxy
    unfold synchronizedPatchOldSurfaceEmbed synchronizedPatchNewSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

omit [Fintype ι] in
/-- Generic finite synchronized weld for a polygonal old-side family and the fixed chart patch. -/
theorem exists_synchronizedPatch_local_weld
    {S : Type*} [TopologicalSpace S] [Finite ι] (c : MoiseChart S)
    (J : ι → PolygonalCircle)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) := by
  let := Fintype.ofFinite ι
  refine ⟨(synchronizedPatchOldMesh c.kind J).Vertex, inferInstance, inferInstance,
    (synchronizedPatchOldMesh c.kind J).triangles,
    (synchronizedPatchNewMesh c.kind J).triangles,
    synchronizedPatchOldSurfaceEmbed c J hmodel,
    synchronizedPatchNewSurfaceEmbed c J,
    synchronizedPatchMeshes_triangle_card c.kind J,
    isEmbedding_synchronizedPatchOldSurfaceEmbed c J hmodel,
    isEmbedding_synchronizedPatchNewSurfaceEmbed c J, ?_, ?_,
    synchronizedPatchMeshes_surface_edge_valence c.kind J⟩
  · intro x y hxy
    exact (synchronizedPatchSurfaceEmbed_eq_iff c J hmodel x y).mpr hxy
  · intro x y hxy
    exact (synchronizedPatchSurfaceEmbed_eq_iff c J hmodel x y).mp hxy

end SynchronizedPatch

/-! ## A synchronized weld against an arbitrary finite target mesh -/

namespace SynchronizedTarget

variable {ι : Type*} [Fintype ι]

/-- The old polygonal member of the common arrangement with an arbitrary finite target mesh. -/
noncomputable def oldMesh (J : ι → PolygonalCircle) (N : TriangleMesh) : TriangleMesh :=
  PolygonalFamily.selectedSynchronizedMesh J N (fun _ ↦ True)

/-- The prescribed finite target member of the same common arrangement. -/
noncomputable def newMesh (J : ι → PolygonalCircle) (N : TriangleMesh) : TriangleMesh :=
  PolygonalFamily.targetSynchronizedMesh J N

theorem oldMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh) :
    (oldMesh J N).toPlaneComplex.support = PolygonalFamily.closedRegion J := by
  simpa [oldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedSynchronizedMesh_support J N (fun _ ↦ True))

theorem newMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support) :
    (newMesh J N).toPlaneComplex.support = N.toPlaneComplex.support :=
  PolygonalFamily.targetSynchronizedMesh_support J N hN

theorem meshes_triangle_card (J : ι → PolygonalCircle) (N : TriangleMesh) :
    ∀ t ∈ (oldMesh J N).triangles ∪ (newMesh J N).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (oldMesh J N).card_triangle t htOld
  · exact (newMesh J N).card_triangle t htNew

theorem meshes_surface_edge_valence (J : ι → PolygonalCircle) (N : TriangleMesh) :
    ∀ e ∈ ((oldMesh J N).triangles ∪
        (newMesh J N).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((oldMesh J N).triangles ∪
          (newMesh J N).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.synchronizedMeshes_joint_edge_valence J N
    (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- The two restrictions use the same ambient arrangement vertices, so equality in the plane
is exactly equality of their zero-extended barycentric coordinate functions. -/
theorem meshes_coordinateEmbed_eq_iff (J : ι → PolygonalCircle) (N : TriangleMesh)
    (x : GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles)
    (y : GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles) :
    (oldMesh J N).coordinateEmbed x = (newMesh J N).coordinateEmbed y ↔
      (x : (oldMesh J N).Vertex → ℝ) =
        (y : (newMesh J N).Vertex → ℝ) := by
  let R := PolygonalFamily.synchronizedArrangement J N
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact (PolygonalFamily.selectedSynchronizedMesh_triangle_mem J N
        (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact (PolygonalFamily.targetSynchronizedMesh_triangle_mem J N).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- Transport the selected polygonal member of an arbitrary synchronized weld to the surface. -/
noncomputable def oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles → S :=
  fun x ↦ (c.chart.symm
    ((oldMesh J N).coordinateEmbedInto c.kind.modelRegion (by
      rw [oldMesh_support]
      exact hmodel) x)).1

/-- Transport the prescribed target member of an arbitrary synchronized weld to the surface. -/
noncomputable def newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles → S :=
  fun x ↦ (c.chart.symm
    ((newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
      rw [newMesh_support J N harr]
      exact hmodel) x)).1

theorem isEmbedding_oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (oldSurfaceEmbed c J N hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((oldMesh J N).isEmbedding_coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (oldMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)) = oldSurfaceEmbed c J N hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (newSurfaceEmbed c J N harr hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((newMesh J N).isEmbedding_coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel)) = newSurfaceEmbed c J N harr hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

/-- The target surface embedding has exactly the chart image of the prescribed mesh support. -/
theorem range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Set.range (newSurfaceEmbed c J N harr hmodel) =
      Subtype.val '' (c.chart.symm ''
        {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let p : c.kind.modelRegion :=
      (newMesh J N).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N harr]
        exact hmodel) x
    refine ⟨c.chart.symm p, ?_, rfl⟩
    refine ⟨p, ?_, rfl⟩
    change (newMesh J N).coordinateEmbed x ∈ N.toPlaneComplex.support
    rw [← newMesh_support J N harr, ← (newMesh J N).range_coordinateEmbed]
    exact Set.mem_range_self x
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    have hpNew : (p : Plane) ∈ (newMesh J N).toPlaneComplex.support := by
      rw [newMesh_support J N harr]
      exact hp
    rw [← (newMesh J N).range_coordinateEmbed] at hpNew
    obtain ⟨x, hx⟩ := hpNew
    refine ⟨x, ?_⟩
    unfold newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hx

/-- Relative interior of the target mesh in the chart model maps to ambient interior in the
surface.  For half-disk charts this includes points on the model boundary line. -/
theorem modelInterior_subset_interior_range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Subtype.val '' (c.chart.symm ''
        interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support}) ⊆
      interior (Set.range (newSurfaceEmbed c J N harr hmodel)) := by
  let P : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ N.toPlaneComplex.support}
  let O : Set S := Subtype.val '' interior (c.chart.symm '' P)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆ Set.range (newSurfaceEmbed c J N harr hmodel) := by
    rw [range_newSurfaceEmbed c J N harr hmodel]
    exact Set.image_mono interior_subset
  rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
  apply interior_maximal hOsub hOopen
  have hzInterior :
      c.chart.symm p ∈ interior (c.chart.symm '' P) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hp, rfl⟩
  exact ⟨c.chart.symm p, hzInterior, rfl⟩

theorem surfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion)
    (x : GeometricRealization (oldMesh J N).Vertex (oldMesh J N).triangles)
    (y : GeometricRealization (newMesh J N).Vertex (newMesh J N).triangles) :
    oldSurfaceEmbed c J N hold x = newSurfaceEmbed c J N harr hnew y ↔
      (x : (oldMesh J N).Vertex → ℝ) =
        (y : (newMesh J N).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold oldSurfaceEmbed newSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (meshes_coordinateEmbed_eq_iff J N x y).mp hplane
  · intro hxy
    have hplane := (meshes_coordinateEmbed_eq_iff J N x y).mpr hxy
    unfold oldSurfaceEmbed newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

/-- Generic finite synchronized weld for a polygonal old-side family and any prescribed finite
target mesh lying in the chart model. -/
theorem exists_local_weld
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) := by
  refine ⟨(oldMesh J N).Vertex, inferInstance, inferInstance,
    (oldMesh J N).triangles, (newMesh J N).triangles,
    oldSurfaceEmbed c J N hold, newSurfaceEmbed c J N harr hnew,
    meshes_triangle_card J N, isEmbedding_oldSurfaceEmbed c J N hold,
    isEmbedding_newSurfaceEmbed c J N harr hnew, ?_, ?_,
    meshes_surface_edge_valence J N⟩
  · intro x y hxy
    exact (surfaceEmbed_eq_iff c J N harr hold hnew x y).mpr hxy
  · intro x y hxy
    exact (surfaceEmbed_eq_iff c J N harr hold hnew x y).mp hxy

end SynchronizedTarget

/-! ## A synchronized weld retaining additional certificate lines -/

namespace RelativeSynchronizedTarget

variable {ι : Type*} [Fintype ι]

/-- The selected polygonal side of the common arrangement after finitely many additional
certificate cuts. -/
noncomputable def oldMesh (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  PolygonalFamily.selectedRelativeSynchronizedMesh J N lines (fun _ ↦ True)

/-- The target side of the same additionally cut arrangement. -/
noncomputable def newMesh (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  PolygonalFamily.targetRelativeSynchronizedMesh J N lines

theorem oldMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (oldMesh J N lines).toPlaneComplex.support =
      PolygonalFamily.closedRegion J := by
  simpa [oldMesh, PolygonalFamily.selectedClosedRegion,
    PolygonalFamily.closedRegion] using
    (PolygonalFamily.selectedRelativeSynchronizedMesh_support
      J N lines (fun _ ↦ True))

theorem newMesh_support (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support) :
    (newMesh J N lines).toPlaneComplex.support = N.toPlaneComplex.support :=
  PolygonalFamily.targetRelativeSynchronizedMesh_support J N lines hN

theorem meshes_triangle_card (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    ∀ t ∈ (oldMesh J N lines).triangles ∪ (newMesh J N lines).triangles,
      t.card = 3 := by
  intro t ht
  rcases Finset.mem_union.mp ht with htOld | htNew
  · exact (oldMesh J N lines).card_triangle t htOld
  · exact (newMesh J N lines).card_triangle t htNew

theorem meshes_surface_edge_valence
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    ∀ e ∈ ((oldMesh J N lines).triangles ∪
        (newMesh J N lines).triangles).biUnion fun t ↦ t.powersetCard 2,
      (((oldMesh J N lines).triangles ∪
          (newMesh J N lines).triangles).filter fun t ↦ e ⊆ t).card ≤ 2 := by
  intro e he
  obtain ⟨t, -, het⟩ := Finset.mem_biUnion.mp he
  exact PolygonalFamily.relativeSynchronizedMeshes_joint_edge_valence
    J N lines (fun _ ↦ True) e (Finset.mem_powersetCard.mp het).2

/-- Regard a retained old-side chamber as a chamber of the common ambient arrangement. -/
def oldFaceToAmbient (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    TriangleFamily.Face (oldMesh J N lines).triangles →
      TriangleFamily.Face
        (PolygonalFamily.relativeSynchronizedArrangement J N lines).triangles :=
  fun f => ⟨f.1,
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J N lines (fun _ ↦ True)).mp f.2 |>.1⟩

/-- Regard a retained target-side chamber as a chamber of the common ambient arrangement. -/
def newFaceToAmbient (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    TriangleFamily.Face (newMesh J N lines).triangles →
      TriangleFamily.Face
        (PolygonalFamily.relativeSynchronizedArrangement J N lines).triangles :=
  fun f => ⟨f.1,
    (PolygonalFamily.targetRelativeSynchronizedMesh_triangle_mem
      J N lines).mp f.2 |>.1⟩

@[simp]
theorem oldFaceToAmbient_val (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (f : TriangleFamily.Face (oldMesh J N lines).triangles) :
    (oldFaceToAmbient J N lines f).1 = f.1 :=
  rfl

@[simp]
theorem newFaceToAmbient_val (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (f : TriangleFamily.Face (newMesh J N lines).triangles) :
    (newFaceToAmbient J N lines f).1 = f.1 :=
  rfl

/-- Ambient-adjacent chambers retained on opposite sides give a genuine cross-edge certificate
for the two synchronized submeshes. -/
theorem hasCrossEdge_of_ambientAdjacent
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (fOld : TriangleFamily.Face (oldMesh J N lines).triangles)
    (fNew : TriangleFamily.Face (newMesh J N lines).triangles)
    (hadj : TriangleFamily.FaceAdjacent
      (PolygonalFamily.relativeSynchronizedArrangement J N lines).triangles
      (oldFaceToAmbient J N lines fOld)
      (newFaceToAmbient J N lines fNew)) :
    TriangleFamily.HasCrossEdge
      (oldMesh J N lines).triangles (newMesh J N lines).triangles := by
  rcases hadj with ⟨edge, hedgeCard, hedgeOld, hedgeNew⟩
  exact ⟨fOld, fNew, edge, hedgeCard, hedgeOld, hedgeNew⟩

/-- A chamber retained by both synchronized submeshes supplies a cross-edge certificate. -/
theorem hasCrossEdge_of_common_triangle
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (oldMesh J N lines).Vertex}
    (hOld : t ∈ (oldMesh J N lines).triangles)
    (hNew : t ∈ (newMesh J N lines).triangles) :
    TriangleFamily.HasCrossEdge
      (oldMesh J N lines).triangles (newMesh J N lines).triangles := by
  have htCard : t.card = 3 := (oldMesh J N lines).card_triangle t hOld
  obtain ⟨edge, hedge, hedgeCard⟩ :=
    Finset.exists_subset_card_eq (show 2 ≤ t.card by omega)
  exact ⟨⟨t, hOld⟩, ⟨t, hNew⟩, edge, hedgeCard, hedge, hedge⟩

/-- Both relative members retain the vertex type of their one ambient arrangement, so planar
equality is precisely equality of zero-extended barycentric coordinates. -/
theorem meshes_coordinateEmbed_eq_iff
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (x : GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles)
    (y : GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles) :
    (oldMesh J N lines).coordinateEmbed x =
        (newMesh J N lines).coordinateEmbed y ↔
      (x : (oldMesh J N lines).Vertex → ℝ) =
        (y : (newMesh J N lines).Vertex → ℝ) := by
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let xR : GeometricRealization R.Vertex R.triangles :=
    ⟨x.1, x.2.1, by
      obtain ⟨t, ht, hxt⟩ := x.2.2
      refine ⟨t, ?_, hxt⟩
      exact
        (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
          J N lines (fun _ ↦ True)).mp ht |>.1⟩
  let yR : GeometricRealization R.Vertex R.triangles :=
    ⟨y.1, y.2.1, by
      obtain ⟨t, ht, hyt⟩ := y.2.2
      refine ⟨t, ?_, hyt⟩
      exact
        (PolygonalFamily.targetRelativeSynchronizedMesh_triangle_mem
          J N lines).mp ht |>.1⟩
  constructor
  · intro hxy
    have hR : R.coordinateEmbed xR = R.coordinateEmbed yR := hxy
    exact congrArg Subtype.val (R.isEmbedding_coordinateEmbed.injective hR)
  · intro hxy
    exact congrArg (fun z ↦ R.toPlaneComplex.baryEval z) hxy

/-- The `oldSurfaceEmbed` declaration. -/
noncomputable def oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles → S :=
  fun x ↦ (c.chart.symm
    ((oldMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
      rw [oldMesh_support]
      exact hmodel) x)).1

/-- The `newSurfaceEmbed` declaration. -/
noncomputable def newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles → S :=
  fun x ↦ (c.chart.symm
    ((newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
      rw [newMesh_support J N lines harr]
      exact hmodel) x)).1

theorem isEmbedding_oldSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hmodel : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding (oldSurfaceEmbed c J N lines hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((oldMesh J N lines).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [oldMesh_support]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (oldMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [oldMesh_support]
        exact hmodel)) = oldSurfaceEmbed c J N lines hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem isEmbedding_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    _root_.Topology.IsEmbedding
      (newSurfaceEmbed c J N lines harr hmodel) := by
  have h := _root_.Topology.IsEmbedding.subtypeVal.comp
    (c.chart.symm.isEmbedding.comp
      ((newMesh J N lines).isEmbedding_coordinateEmbedInto
        c.kind.modelRegion (by
          rw [newMesh_support J N lines harr]
          exact hmodel)))
  have heq : (Subtype.val ∘ c.chart.symm ∘
      (newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N lines harr]
        exact hmodel)) = newSurfaceEmbed c J N lines harr hmodel := by
    funext x
    rfl
  rw [heq] at h
  exact h

theorem range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Set.range (newSurfaceEmbed c J N lines harr hmodel) =
      Subtype.val '' (c.chart.symm ''
        {p : c.kind.modelRegion | (p : Plane) ∈ N.toPlaneComplex.support}) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    let p : c.kind.modelRegion :=
      (newMesh J N lines).coordinateEmbedInto c.kind.modelRegion (by
        rw [newMesh_support J N lines harr]
        exact hmodel) x
    refine ⟨c.chart.symm p, ?_, rfl⟩
    refine ⟨p, ?_, rfl⟩
    change (newMesh J N lines).coordinateEmbed x ∈
      N.toPlaneComplex.support
    rw [← newMesh_support J N lines harr,
      ← (newMesh J N lines).range_coordinateEmbed]
    exact Set.mem_range_self x
  · rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    have hpNew : (p : Plane) ∈
        (newMesh J N lines).toPlaneComplex.support := by
      rw [newMesh_support J N lines harr]
      exact hp
    rw [← (newMesh J N lines).range_coordinateEmbed] at hpNew
    obtain ⟨x, hx⟩ := hpNew
    refine ⟨x, ?_⟩
    unfold newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hx

theorem modelInterior_subset_interior_range_newSurfaceEmbed
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hmodel : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    Subtype.val '' (c.chart.symm ''
        interior {p : c.kind.modelRegion |
          (p : Plane) ∈ N.toPlaneComplex.support}) ⊆
      interior (Set.range
        (newSurfaceEmbed c J N lines harr hmodel)) := by
  let P : Set c.kind.modelRegion :=
    {p | (p : Plane) ∈ N.toPlaneComplex.support}
  let O : Set S := Subtype.val '' interior (c.chart.symm '' P)
  have hOopen : IsOpen O :=
    c.isOpen_domain.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hOsub : O ⊆
      Set.range (newSurfaceEmbed c J N lines harr hmodel) := by
    rw [range_newSurfaceEmbed c J N lines harr hmodel]
    exact Set.image_mono interior_subset
  rintro y ⟨z, ⟨p, hp, rfl⟩, rfl⟩
  apply interior_maximal hOsub hOopen
  have hzInterior :
      c.chart.symm p ∈ interior (c.chart.symm '' P) := by
    rw [← c.chart.symm.image_interior]
    exact ⟨p, hp, rfl⟩
  exact ⟨c.chart.symm p, hzInterior, rfl⟩

theorem surfaceEmbed_eq_iff
    {S : Type*} [TopologicalSpace S] (c : MoiseChart S)
    (J : ι → PolygonalCircle) (N : TriangleMesh)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh J).toPlaneComplex.support)
    (hold : PolygonalFamily.closedRegion J ⊆ c.kind.modelRegion)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion)
    (x : GeometricRealization (oldMesh J N lines).Vertex
      (oldMesh J N lines).triangles)
    (y : GeometricRealization (newMesh J N lines).Vertex
      (newMesh J N lines).triangles) :
    oldSurfaceEmbed c J N lines hold x =
        newSurfaceEmbed c J N lines harr hnew y ↔
      (x : (oldMesh J N lines).Vertex → ℝ) =
        (y : (newMesh J N lines).Vertex → ℝ) := by
  constructor
  · intro hxy
    unfold oldSurfaceEmbed newSurfaceEmbed at hxy
    have hchart := Subtype.ext hxy
    have hplane := congrArg Subtype.val (c.chart.symm.injective hchart)
    exact (meshes_coordinateEmbed_eq_iff J N lines x y).mp hplane
  · intro hxy
    have hplane :=
      (meshes_coordinateEmbed_eq_iff J N lines x y).mpr hxy
    unfold oldSurfaceEmbed newSurfaceEmbed
    apply congrArg Subtype.val
    apply congrArg c.chart.symm
    exact Subtype.ext hplane

end RelativeSynchronizedTarget

open LocallyFiniteTriangleComplex PolygonalReplacementSourceAtlas RelativeSynchronizedTarget

namespace PolygonalReplacementSourceAtlas

/-- The polygonal family obtained by closing the faces meeting an arbitrary compact coordinate
set under their whole adaptive source tiles. -/
def tileFacePolygonMeeting
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    A.TileFacesMeeting C hC → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The retained finite PL filling certificate for one face in a compactly selected
whole-tile family. -/
noncomputable def tileFaceMeetingCertificate
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (f : A.TileFacesMeeting C hC) :
    FinitePLHomeomorphBetween (Q.faceFillingMap f.1)
      LocallyFiniteTriangleComplex.standardFaceRegion
      (A.tileFacePolygonMeeting C hC f).closedRegion :=
  Classical.choice (Q.faceCertificate f.1)

/-- Pull the synchronized mesh of one compactly selected polygon back to its standard source
triangle.  The common target refinement includes both the synchronized chart mesh and the
retained PL certificate, so the certified inverse is affine on every resulting source piece. -/
noncomputable def tileFaceMeetingPullback
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (f : A.TileFacesMeeting C hC) :
    (A.tileFaceMeetingCertificate C hC f).PullbackSubdivision
      (SynchronizedPatch.singlePolygonMesh
        (A.tileFacePolygonMeeting C hC) N f).toPlaneComplex :=
  (A.tileFaceMeetingCertificate C hC f).pullbackSubdivision _
    (SynchronizedPatch.singlePolygonMesh
      (A.tileFacePolygonMeeting C hC) N f).toPlaneComplex_isPure2
    (SynchronizedPatch.singlePolygonMesh_support
      (A.tileFacePolygonMeeting C hC) N f)

/-- All target-side coordinate lines required by the retained PL certificates of the finite
selected face family.  Cutting the synchronized arrangement by this one finite list makes every
selected chamber subordinate to every certificate whose polygon contains its interior. -/
noncomputable def tileFaceMeetingCertificateLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (A.TileFacesMeeting C hC)).toList.flatMap fun f ↦
    ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines

theorem tileFaceMeetingPullback_coordinateLine_mem
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (f : A.TileFacesMeeting C hC)
    {a : Plane →ᵃ[ℝ] ℝ}
    (ha : a ∈
      ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines) :
    a ∈ A.tileFaceMeetingCertificateLines C hC N := by
  rw [tileFaceMeetingCertificateLines, List.mem_flatMap]
  exact ⟨f, by simp, ha⟩

/-- The retained certificate lines together with any additional finite conforming cuts. -/
noncomputable def tileFaceMeetingLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  A.tileFaceMeetingCertificateLines C hC N ++ extraLines

theorem tileFaceMeetingPullback_coordinateLine_mem_lines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (f : A.TileFacesMeeting C hC)
    {a : Plane →ᵃ[ℝ] ℝ}
    (ha : a ∈
      ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).coordinateLines) :
    a ∈ A.tileFaceMeetingLines C hC N extraLines := by
  exact List.mem_append_left _
    (A.tileFaceMeetingPullback_coordinateLine_mem C hC N f ha)

/-- Two transverse coordinate cuts through each point in a finite family. -/
noncomputable def coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset α).toList.flatMap fun a ↦
    [BrokenLineData.verticalLine (p a),
      BrokenLineData.horizontalLine (p a)]

theorem verticalLine_mem_coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) (a : α) :
    BrokenLineData.verticalLine (p a) ∈ coordinateAnchorLines p := by
  classical
  rw [coordinateAnchorLines, List.mem_flatMap]
  exact ⟨a, by simp, by simp⟩

theorem horizontalLine_mem_coordinateAnchorLines
    {α : Type*} [Fintype α] (p : α → Plane) (a : α) :
    BrokenLineData.horizontalLine (p a) ∈ coordinateAnchorLines p := by
  classical
  rw [coordinateAnchorLines, List.mem_flatMap]
  exact ⟨a, by simp, by simp⟩

/-- The certificate-cut synchronized old mesh over the finite selected source family. -/
noncomputable def tileFacesMeetingRelativeOldMesh
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  RelativeSynchronizedTarget.oldMesh
    (A.tileFacePolygonMeeting C hC) N
    (A.tileFaceMeetingLines C hC N extraLines)

/-- The target member of the same certificate-cut synchronized arrangement. -/
noncomputable def tileFacesMeetingRelativeNewMesh
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) : TriangleMesh :=
  RelativeSynchronizedTarget.newMesh
    (A.tileFacePolygonMeeting C hC) N
    (A.tileFaceMeetingLines C hC N extraLines)

theorem tileFacesMeetingRelativeOldMesh_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).toPlaneComplex.support =
      PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) :=
  RelativeSynchronizedTarget.oldMesh_support _ _ _

theorem tileFacesMeetingRelativeNewMesh_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (hN : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (A.tileFacePolygonMeeting C hC)).toPlaneComplex.support) :
    (A.tileFacesMeetingRelativeNewMesh C hC N extraLines).toPlaneComplex.support =
      N.toPlaneComplex.support :=
  RelativeSynchronizedTarget.newMesh_support _ _ _ hN

/-- A relative synchronized chamber lying in one selected polygon is contained in a maximal
target triangle of that face's retained pullback certificate.  This is the precise payoff of
putting every certificate coordinate line into the one common arrangement. -/
theorem exists_pullbackTargetTriangle_of_relativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (f : A.TileFacesMeeting C hC)
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈ (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (htf : interior
        ((PolygonalFamily.relativeSynchronizedArrangement
          (A.tileFacePolygonMeeting C hC) N
          (A.tileFaceMeetingLines C hC N extraLines)).triangleCarrier t) ⊆
      (A.tileFacePolygonMeeting C hC f).interiorRegion) :
    ∃ u ∈
        ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).triangles,
      (PolygonalFamily.relativeSynchronizedArrangement
          (A.tileFacePolygonMeeting C hC) N
          (A.tileFaceMeetingLines C hC N extraLines)).triangleCarrier t ⊆
        ((A.tileFaceMeetingPullback C hC N f).target.toTriangleMesh).triangleCarrier u := by
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let P := A.tileFaceMeetingPullback C hC N f
  let M := P.target.toTriangleMesh
  have htR : t ∈ R.triangles := by
    exact
      (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
        J N lines (fun _ ↦ True)).mp ht |>.1
  let T : R.Triangle := ⟨t, htR⟩
  have hlines :
      ∀ a ∈ M.coordinateLines, a ∈ N.coordinateLines ++ lines := by
    intro a ha
    apply List.mem_append_right
    exact A.tileFaceMeetingPullback_coordinateLine_mem_lines
      C hC N extraLines f ha
  have hhit :
      (interior (R.triangleCarrier t) ∩
        M.toPlaneComplex.support).Nonempty := by
    obtain ⟨x, hx⟩ := R.interior_triangleCarrier_nonempty T
    refine ⟨x, hx, ?_⟩
    rw [show M.toPlaneComplex.support = P.target.support by
      exact P.target.toTriangleMesh_support P.target_pure, P.target_support]
    rw [(A.tileFacePolygonMeeting C hC f).closedRegion_eq_union]
    exact Or.inl (htf hx)
  obtain ⟨W, hTW⟩ :=
    TriangleMesh.exists_target_triangle_of_refineByLines_of_interior_inter_support
      (PolygonalFamily.arrangementMesh J) M
      (N.coordinateLines ++ lines) hlines T hhit
  exact ⟨W.1, W.2, hTW⟩

/-- The compactly selected polygonal union remains in the coordinate region of the
replacement presentation. -/
theorem tileFacePolygonMeeting_closedRegion_subset_region
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) ⊆ V := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  exact Q.faceClosedRegion_subset f.1 hxf

/-- The same polygonal union, lifted to the coordinate-region subtype, lies in the support of
the global polygonal replacement complex. -/
theorem tileFacePolygonMeeting_subset_complex_support
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    {x : V | x.1 ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)} ⊆
      Q.complex.support := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨f.1, ?_⟩
  rw [Q.faceCarrier_eq f.1]
  exact hxf

/-- The coordinate union of a compactly selected tile family is exactly the image of its
common-level source subcomplex. -/
theorem sourceTileFacesMeeting_eq_coordinatePreimage
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) :
    (⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1) =
      {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1.1 ∈
          PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxU, hxQ⟩ := hxFace
    refine ⟨hxU, Set.mem_iUnion.mpr ⟨f, ?_⟩⟩
    rw [Q.faceCarrier_eq f.1] at hxQ
    simpa [tileFacePolygonMeeting] using hxQ
  · rintro x ⟨hxU, hxFamily⟩
    obtain ⟨f, hxPolygon⟩ := Set.mem_iUnion.mp hxFamily
    apply Set.mem_iUnion.mpr
    refine ⟨f, hxU, ?_⟩
    rw [Q.faceCarrier_eq f.1]
    exact hxPolygon

/-- The certificate-cut synchronized old mesh, regarded as a subspace of the global
replacement support. -/
noncomputable def tileFacesMeetingRelativeOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    GeometricRealization
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles →
      Q.complex.support :=
  fun x => by
    let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
    let p : Plane := M.coordinateEmbed x
    have hpClosed :
        p ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
        ← M.range_coordinateEmbed]
      exact Set.mem_range_self x
    let pV : V :=
      ⟨p, A.tileFacePolygonMeeting_closedRegion_subset_region C hC hpClosed⟩
    exact ⟨pV,
      A.tileFacePolygonMeeting_subset_complex_support C hC hpClosed⟩

theorem isEmbedding_tileFacesMeetingRelativeOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  have hclosed (x : GeometricRealization M.Vertex M.triangles) :
      M.coordinateEmbed x ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
    rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
      ← M.range_coordinateEmbed]
    exact Set.mem_range_self x
  let fV : GeometricRealization M.Vertex M.triangles → V :=
    Set.codRestrict M.coordinateEmbed V fun x =>
      A.tileFacePolygonMeeting_closedRegion_subset_region C hC (hclosed x)
  have hfV : _root_.Topology.IsEmbedding fV :=
    M.isEmbedding_coordinateEmbed.codRestrict V _
  have hfQ : _root_.Topology.IsEmbedding
      (Set.codRestrict fV Q.complex.support fun x =>
        A.tileFacePolygonMeeting_subset_complex_support C hC (hclosed x)) :=
    hfV.codRestrict Q.complex.support _
  convert hfQ using 1
  funext x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Pull the certificate-cut old coordinate triangulation back through the retained source
homeomorphism. -/
noncomputable def tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    GeometricRealization
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles →
      K.realization :=
  Subtype.val ∘ Q.sourceHomeomorph.symm ∘
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines

theorem isEmbedding_tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (Q.sourceHomeomorph.symm.isEmbedding.comp
      (A.isEmbedding_tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines))

/-- Changing only the finite line refinement does not change the source point represented by
one fixed planar coordinate. -/
theorem tileFacesMeetingRelativeSourceEmbed_eq_of_coordinateEmbed_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    {extraLines₁ extraLines₂ : List (Plane →ᵃ[ℝ] ℝ)}
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).triangles)
    (y : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).triangles)
    (hxy :
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₁).coordinateEmbed x =
        (A.tileFacesMeetingRelativeOldMesh C hC N extraLines₂).coordinateEmbed y) :
    A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines₁ x =
      A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines₂ y := by
  change
    (Q.sourceHomeomorph.symm
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines₁ x)).1 =
    (Q.sourceHomeomorph.symm
      (A.tileFacesMeetingRelativeOldCoordinateSupport
        C hC N extraLines₂ y)).1
  apply congrArg Subtype.val
  apply congrArg Q.sourceHomeomorph.symm
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- The intrinsic finite complex underlying the certificate-cut selected source mesh. -/
noncomputable abbrev tileFacesMeetingRelativeSourceComplex
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    IntrinsicTwoComplex := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact
    { Vertex := M.Vertex
      faces := M.triangles
      faces_card := M.card_triangle }

@[simp] theorem tileFacesMeetingRelativeSourceComplex_faces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    (A.tileFacesMeetingRelativeSourceComplex C hC N extraLines).faces =
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles :=
  rfl

/-- The original intrinsic point represented by one used vertex of the certificate-cut local
source mesh. -/
noncomputable def tileFacesMeetingRelativeSourceVertexPoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    K.realization :=
  A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
    ((A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).vertexPoint v)

/-- The same local source vertex, retaining its proof of membership in the replacement
domain. -/
noncomputable def tileFacesMeetingRelativeSourceVertexPointInOpen
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) : U :=
  Q.sourceHomeomorph.symm
    (A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines
      ((A.tileFacesMeetingRelativeSourceComplex
        C hC N extraLines).vertexPoint v))

@[simp] theorem tileFacesMeetingRelativeSourceVertexPointInOpen_val
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    (A.tileFacesMeetingRelativeSourceVertexPointInOpen
      C hC N extraLines v).1 =
      A.tileFacesMeetingRelativeSourceVertexPoint C hC N extraLines v :=
  rfl

/-- In replacement coordinates, a used local source vertex is its literal plane-mesh
vertex. -/
theorem sourceHomeomorph_relativeSourceVertexPointInOpen
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (v : (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).UsedVertex) :
    (Q.sourceHomeomorph
      (A.tileFacesMeetingRelativeSourceVertexPointInOpen
        C hC N extraLines v)).1.1 =
      (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).position v.1 := by
  classical
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  change {w : M.Vertex // ∃ t ∈ M.triangles, w ∈ t} at v
  unfold tileFacesMeetingRelativeSourceVertexPointInOpen
  rw [Q.sourceHomeomorph.apply_symm_apply]
  change
    M.toPlaneComplex.baryEval (Pi.single v.1 1) = M.position v.1
  unfold PlaneComplex.baryEval
  change (∑ w : M.Vertex, Pi.single v.1 1 w • M.position w) =
    M.position v.1
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro w _ hw
    simp [hw]
  · simp

theorem injective_tileFacesMeetingRelativeSourceVertexPoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Function.Injective
      (A.tileFacesMeetingRelativeSourceVertexPoint C hC N extraLines) :=
  (A.isEmbedding_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).injective.comp
    (A.tileFacesMeetingRelativeSourceComplex
      C hC N extraLines).injective_vertexPoint

/-- The certificate cuts change only the triangulation, not the selected whole-tile source
support. -/
theorem range_tileFacesMeetingRelativeSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Set.range (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rw [A.sourceTileFacesMeeting_eq_coordinatePreimage C hC]
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    let q : Q.complex.support :=
      A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines z
    refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
    have hqClosed :
        q.1.1 ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      change M.coordinateEmbed z ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)
      rw [← A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines,
        ← M.range_coordinateEmbed]
      exact Set.mem_range_self z
    have harg :
        (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines z,
            (Q.sourceHomeomorph.symm q).2⟩ : U) =
          Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [harg, Q.sourceHomeomorph.apply_symm_apply]
    exact hqClosed
  · rintro x ⟨hxU, hxClosed⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqM : q.1.1 ∈ M.toPlaneComplex.support := by
      rw [A.tileFacesMeetingRelativeOldMesh_support C hC N extraLines]
      exact hxClosed
    rw [← M.range_coordinateEmbed] at hqM
    obtain ⟨z, hz⟩ := hqM
    refine ⟨z, ?_⟩
    change
      (Q.sourceHomeomorph.symm
        (A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z)).1 = x
    have hsupportEq :
        A.tileFacesMeetingRelativeOldCoordinateSupport
          C hC N extraLines z = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    rw [hsupportEq]
    exact congrArg Subtype.val
      (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

theorem range_tileFacesMeetingRelativeSourceEmbed_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ)) :
    Set.range (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 :=
  (A.range_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).trans
    (A.sourceTileFacesMeeting_eq_levelFaces C hC)

/-- On every certificate-cut synchronized triangle, the pulled-back source embedding is one
affine function in the original intrinsic barycentric coordinates. -/
theorem tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles) :
    ∃ a :
        ((A.tileFacesMeetingRelativeOldMesh
          C hC N extraLines).Vertex → ℝ) →ᵃ[ℝ]
          (K.Vertex → ℝ),
      ∀ x : GeometricRealization
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles,
        (∀ v ∉ t, x.1 v = 0) →
          (A.tileFacesMeetingRelativeSourceEmbed
            C hC N extraLines x).1 = a x.1 := by
  classical
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨htR, f, -, htf⟩ :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J N lines (fun _ ↦ True)).mp ht
  let P := A.tileFaceMeetingPullback C hC N f
  obtain ⟨u, hu, htu⟩ :=
    A.exists_pullbackTargetTriangle_of_relativeOldTriangle
      C hC N extraLines f ht htf
  have huSimplex : u ∈ P.target.simplexes :=
    P.target.mem_simplexes_of_mem_cells hu
  obtain ⟨ainv, hainv⟩ := P.inverseAffine u huSimplex
  obtain ⟨b, hb⟩ := A.sourceFaceStandardAffine f.1
  refine
    ⟨b.comp (ainv.comp M.toPlaneComplex.baryEvalAffine), ?_⟩
  intro x hx
  let p : Plane := M.coordinateEmbed x
  have hpCarrierM : p ∈ M.toPlaneComplex.cellCarrier t := by
    apply M.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  have hpCarrierR : p ∈ R.triangleCarrier t := hpCarrierM
  have hpTarget : p ∈ P.target.cellCarrier u :=
    htu hpCarrierR
  have hpPolygon : p ∈ (J f).closedRegion := by
    let T : R.Triangle := ⟨t, htR⟩
    have hpClosure : p ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hpCarrierR
    simpa only [PolygonalCircle.closedRegion] using
      closure_mono htf hpClosure
  have hpInv :
      (A.tileFaceMeetingCertificate C hC f).inverseOn p ∈
        LocallyFiniteTriangleComplex.standardFaceRegion :=
    (A.tileFaceMeetingCertificate C hC f).inverseOn_mem hpPolygon
  let z : standardTrianglePlaneComplex.support :=
    ⟨(A.tileFaceMeetingCertificate C hC f).inverseOn p, hpInv⟩
  let xf : Q.complex.ClosedFace f.1 :=
    (Q.complex.facePlaneHomeomorph f.1).symm z
  let q : Q.complex.support :=
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines x
  have hqFace :
      q =
        LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
          (K := Q.complex) f.1 xf := by
    apply Subtype.ext
    apply Subtype.ext
    change p = (Q.complex.faceMap f.1 xf).1
    rw [Q.faceMap_eq]
    rw [(Q.complex.facePlaneHomeomorph f.1).apply_symm_apply z]
    exact
      ((A.tileFaceMeetingCertificate C hC f).apply_inverseOn hpPolygon).symm
  change (Q.sourceHomeomorph.symm q).1.1 =
    (b.comp (ainv.comp M.toPlaneComplex.baryEvalAffine)) x.1
  rw [hqFace, hb xf]
  have hzapply :
      ((Q.complex.facePlaneHomeomorph f.1) xf).1 = z.1 :=
    congrArg Subtype.val
      ((Q.complex.facePlaneHomeomorph f.1).apply_symm_apply z)
  rw [hzapply]
  simp only [AffineMap.comp_apply]
  have hpBary : M.toPlaneComplex.baryEvalAffine x.1 = p := by
    rw [PlaneComplex.baryEvalAffine_apply]
    rfl
  rw [hpBary]
  change b z.1 = b (ainv p)
  apply congrArg b
  change
    (A.tileFaceMeetingCertificate C hC f).inverseOn p = ainv p
  exact hainv hpTarget

/-- Every relative source triangle lies in one original maximal face. -/
theorem exists_parentFace_of_relativeOldTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    {t : Finset (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex}
    (ht : t ∈
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles) :
    ∃ u : K.Face,
      ∀ x : GeometricRealization
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
          (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles,
        (∀ v ∉ t, x.1 v = 0) →
          A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x ∈
            K.faceCarrier u.1 := by
  classical
  let J := A.tileFacePolygonMeeting C hC
  let lines := A.tileFaceMeetingLines C hC N extraLines
  let R := PolygonalFamily.relativeSynchronizedArrangement J N lines
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  obtain ⟨htR, f, -, htf⟩ :=
    (PolygonalFamily.selectedRelativeSynchronizedMesh_triangle_mem
      J N lines (fun _ ↦ True)).mp ht
  refine ⟨A.sourceFaceParent f.1, ?_⟩
  intro x hx
  let p : Plane := M.coordinateEmbed x
  have hpCarrierM : p ∈ M.toPlaneComplex.cellCarrier t := by
    apply M.toPlaneComplex.baryEval_mem_cellCarrier hx x.2.1.1 x.2.1.2
  have hpCarrierR : p ∈ R.triangleCarrier t := hpCarrierM
  have hpPolygon : p ∈ (J f).closedRegion := by
    let T : R.Triangle := ⟨t, htR⟩
    have hpClosure : p ∈ closure (interior (R.triangleCarrier t)) := by
      rw [R.closure_interior_triangleCarrier T]
      exact hpCarrierR
    simpa only [PolygonalCircle.closedRegion] using
      closure_mono htf hpClosure
  let q : Q.complex.support :=
    A.tileFacesMeetingRelativeOldCoordinateSupport C hC N extraLines x
  apply A.sourceFaceSet_subset_parent f.1
  refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
  have harg :
      (⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x,
          (Q.sourceHomeomorph.symm q).2⟩ : U) =
        Q.sourceHomeomorph.symm q :=
    Subtype.ext rfl
  rw [harg, Q.sourceHomeomorph.apply_symm_apply]
  rw [Q.faceCarrier_eq f.1]
  exact hpPolygon

/-- A canonical original parent face for one triangle of the relative source mesh. -/
noncomputable def relativeOldTriangleParent
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) : K.Face :=
  Classical.choose
    (A.exists_parentFace_of_relativeOldTriangle
      C hC N extraLines t.2)

/-- The chosen parent contains the complete image of the relative source triangle. -/
theorem relativeOldTriangleParent_contains
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x ∈
      K.faceCarrier
        (A.relativeOldTriangleParent C hC N extraLines t).1 :=
  Classical.choose_spec
    (A.exists_parentFace_of_relativeOldTriangle
      C hC N extraLines t.2) x hx

/-- The canonical affine formula for the source embedding on one relative triangle. -/
noncomputable def relativeOldTriangleSourceAffine
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    ((A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Vertex → ℝ) →ᵃ[ℝ] (K.Vertex → ℝ) :=
  Classical.choose
    (A.tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
      C hC N extraLines t.2)

/-- The chosen source affine formula agrees with the source embedding on its triangle. -/
theorem relativeOldTriangleSourceAffine_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x).1 =
      A.relativeOldTriangleSourceAffine C hC N extraLines t x.1 :=
  Classical.choose_spec
    (A.tileFacesMeetingRelativeSourceEmbed_affineOn_triangle
      C hC N extraLines t.2) x hx

/-- On one relative source triangle, the source map is the affine combination of its three
actual source-vertex images. -/
theorem relativeSourceFaceMap_eq_vertex_sum
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (x : GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles)
    (hx : ∀ v ∉ t.1, x.1 v = 0) :
    (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines x).1 =
      ∑ v : t.1, x.1 v.1 •
        (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          ((A.tileFacesMeetingRelativeSourceComplex
            C hC N extraLines).vertexPoint
              ⟨v.1, ⟨t.1, t.2, v.2⟩⟩)).1 := by
  classical
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let L := A.tileFacesMeetingRelativeSourceComplex C hC N extraLines
  let a := A.relativeOldTriangleSourceAffine C hC N extraLines t
  let p : t.1 → (M.Vertex → ℝ) := fun v ↦ Pi.single v.1 1
  let w : t.1 → ℝ := fun v ↦ x.1 v.1
  have hsum : ∑ v : t.1, w v = 1 := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach t.1 (fun v ↦ x.1 v)]
    exact
      (Finset.sum_subset (Finset.subset_univ t.1)
        (fun v _ hv => hx v hv)).trans x.2.1.2
  have hcomb :
      (Finset.univ : Finset t.1).affineCombination ℝ p w = x.1 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, p, w,
      Pi.single_apply]
    by_cases hzt : z ∈ t.1
    · let zt : t.1 := ⟨z, hzt⟩
      rw [Finset.sum_eq_single zt]
      · simp [zt]
      · intro b _ hb
        have hbval : b.1 ≠ z := by
          intro h
          apply hb
          exact Subtype.ext h
        simp [Ne.symm hbval]
      · simp
    · have hxz : x.1 z = 0 := hx z hzt
      rw [hxz]
      apply Finset.sum_eq_zero
      intro b _
      have hbval : z ≠ b.1 := fun h => hzt (h ▸ b.2)
      simp [hbval]
  have hmap :
      a x.1 =
        ∑ v : t.1, w v • a (p v) := by
    calc
      a x.1 =
          a ((Finset.univ : Finset t.1).affineCombination ℝ p w) :=
        congrArg a hcomb.symm
      _ =
          (Finset.univ : Finset t.1).affineCombination ℝ (a ∘ p) w :=
        (Finset.univ : Finset t.1).map_affineCombination p w hsum a
      _ = ∑ v : t.1, w v • a (p v) := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
        rfl
  rw [A.relativeOldTriangleSourceAffine_eq
    C hC N extraLines t x hx]
  rw [hmap]
  apply Finset.sum_congr rfl
  intro v _
  apply congrArg (w v • ·)
  symm
  apply A.relativeOldTriangleSourceAffine_eq
    C hC N extraLines t
  intro z hz
  change Pi.single v.1 1 z = 0
  have hzv : z ≠ v.1 := fun h => hz (h ▸ v.2)
  simp [hzv]

/-- The same abstract triangle, viewed as a maximal triangle of the plane complex generated by
the relative mesh. -/
noncomputable def relativeOldTriangleAsPlaneTriangle
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    (((A.tileFacesMeetingRelativeOldMesh C hC N extraLines).toPlaneComplex
      ).toTriangleMesh).Triangle := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact ⟨t.1, by
    change t.1 ∈ M.toPlaneComplex.cells
    rw [M.toPlaneComplex_cells]
    exact t.2⟩

/-- A point of a relative old plane triangle, regarded as the corresponding point of its
barycentric realization. -/
noncomputable def relativeOldTrianglePoint
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    GeometricRealization
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).Vertex
      (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).triangles := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact
    ⟨M.triangleCoords t p.1,
      ⟨M.triangleCoords_nonneg_of_mem t p.2,
        M.sum_triangleCoords t p.1⟩,
      t.1, t.2, M.triangleCoords_support t p.1⟩

@[simp] theorem relativeOldTrianglePoint_coordinateEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    (A.tileFacesMeetingRelativeOldMesh C hC N extraLines).coordinateEmbed
        (A.relativeOldTrianglePoint C hC N extraLines t p) = p.1 := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  exact M.baryEval_triangleCoords t p.1

theorem relativeOldTrianglePoint_val_eq_triangleCoords
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    (A.relativeOldTrianglePoint C hC N extraLines t p).1 =
      (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCoords t p.1 :=
  rfl

theorem relativeOldTrianglePoint_supported
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    ∀ v ∉ t.1,
      (A.relativeOldTrianglePoint C hC N extraLines t p).1 v = 0 := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  intro v hv
  rw [A.relativeOldTrianglePoint_val_eq_triangleCoords
    C hC N extraLines t p]
  exact M.triangleCoords_apply_of_notMem t hv p.1

/-- The source triangle written in the standard plane coordinates of its original parent
face. -/
noncomputable def relativeOldTriangleParentPlaneAffine
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) : Plane →ᵃ[ℝ] Plane :=
  (K.facePlaneForwardAffine
      (A.relativeOldTriangleParent C hC N extraLines t)).comp
    ((A.relativeOldTriangleSourceAffine C hC N extraLines t).comp
      ((A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCoords t))

theorem relativeOldTriangleParentPlaneAffine_eq
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle)
    (p : {p : Plane //
      p ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1}) :
    A.relativeOldTriangleParentPlaneAffine C hC N extraLines t p.1 =
      (K.facePlaneHomeomorph
        (A.relativeOldTriangleParent C hC N extraLines t)
        ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
            (A.relativeOldTrianglePoint C hC N extraLines t p),
          A.relativeOldTriangleParent_contains C hC N extraLines t _
            (A.relativeOldTrianglePoint_supported
              C hC N extraLines t p)⟩).1 := by
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine]
  simp only [relativeOldTriangleParentPlaneAffine, AffineMap.comp_apply]
  apply congrArg
    (K.facePlaneForwardAffine
      (A.relativeOldTriangleParent C hC N extraLines t))
  calc
    (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        ((A.tileFacesMeetingRelativeOldMesh
          C hC N extraLines).triangleCoords t p.1) =
      (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        (A.relativeOldTrianglePoint C hC N extraLines t p).1 :=
      congrArg
        (A.relativeOldTriangleSourceAffine C hC N extraLines t)
        (A.relativeOldTrianglePoint_val_eq_triangleCoords
          C hC N extraLines t p).symm
    _ = (A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
        (A.relativeOldTrianglePoint C hC N extraLines t p)).1 :=
      (A.relativeOldTriangleSourceAffine_eq C hC N extraLines t _
        (A.relativeOldTrianglePoint_supported
          C hC N extraLines t p)).symm

/-- The parent-plane formula is locally injective on its source triangle. -/
theorem relativeOldTriangleParentPlaneAffine_injOn
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Set.InjOn
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t)
      ((A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1) := by
  intro p hp q hq hpq
  let pp : {z : Plane //
      z ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1} := ⟨p, hp⟩
  let qq : {z : Plane //
      z ∈ (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).triangleCarrier t.1} := ⟨q, hq⟩
  have hchart :
      K.facePlaneHomeomorph
          (A.relativeOldTriangleParent C hC N extraLines t)
          ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
              (A.relativeOldTrianglePoint C hC N extraLines t pp),
            A.relativeOldTriangleParent_contains C hC N extraLines t _
              (A.relativeOldTrianglePoint_supported
                C hC N extraLines t pp)⟩ =
        K.facePlaneHomeomorph
          (A.relativeOldTriangleParent C hC N extraLines t)
          ⟨A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
              (A.relativeOldTrianglePoint C hC N extraLines t qq),
            A.relativeOldTriangleParent_contains C hC N extraLines t _
              (A.relativeOldTrianglePoint_supported
                C hC N extraLines t qq)⟩ := by
    apply Subtype.ext
    rw [← A.relativeOldTriangleParentPlaneAffine_eq
        C hC N extraLines t pp,
      ← A.relativeOldTriangleParentPlaneAffine_eq
        C hC N extraLines t qq]
    exact hpq
  have hsource :
      A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          (A.relativeOldTrianglePoint C hC N extraLines t pp) =
        A.tileFacesMeetingRelativeSourceEmbed C hC N extraLines
          (A.relativeOldTrianglePoint C hC N extraLines t qq) := by
    exact congrArg (fun z => z.1)
      ((K.facePlaneHomeomorph
        (A.relativeOldTriangleParent C hC N extraLines t)).injective hchart)
  have hpoint :
      A.relativeOldTrianglePoint C hC N extraLines t pp =
        A.relativeOldTrianglePoint C hC N extraLines t qq :=
    (A.isEmbedding_tileFacesMeetingRelativeSourceEmbed
      C hC N extraLines).injective hsource
  calc
    p = (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).coordinateEmbed
          (A.relativeOldTrianglePoint C hC N extraLines t pp) :=
      (A.relativeOldTrianglePoint_coordinateEmbed
        C hC N extraLines t pp).symm
    _ = (A.tileFacesMeetingRelativeOldMesh
        C hC N extraLines).coordinateEmbed
          (A.relativeOldTrianglePoint C hC N extraLines t qq) :=
      congrArg _ hpoint
    _ = q :=
      A.relativeOldTrianglePoint_coordinateEmbed
        C hC N extraLines t qq

/-- Consequently, the parent-plane formula is a global affine equivalence at the level of
functions. -/
theorem relativeOldTriangleParentPlaneAffine_injective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Function.Injective
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hcarrier :
      M.triangleCarrier t.1 = convexHull ℝ (Set.range p) := by
    unfold TriangleMesh.triangleCarrier
    rw [Set.range_comp, M.range_orderedVertex t]
  apply affineMap_injective_of_injOn_convexHull p
    (M.orderedVertex_affineIndependent t)
  rw [← hcarrier]
  exact A.relativeOldTriangleParentPlaneAffine_injOn
    C hC N extraLines t

theorem relativeOldTriangleParentPlaneAffine_surjective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (extraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N extraLines).Triangle) :
    Function.Surjective
      (A.relativeOldTriangleParentPlaneAffine C hC N extraLines t) := by
  let M := A.tileFacesMeetingRelativeOldMesh C hC N extraLines
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hcarrier :
      M.triangleCarrier t.1 = convexHull ℝ (Set.range p) := by
    unfold TriangleMesh.triangleCarrier
    rw [Set.range_comp, M.range_orderedVertex t]
  apply affineMap_surjective_of_injOn_convexHull p
    (M.orderedVertex_affineIndependent t)
  rw [← hcarrier]
  exact A.relativeOldTriangleParentPlaneAffine_injOn
    C hC N extraLines t

/-- A canonical original parent of one face at a fixed midpoint level. -/
noncomputable def levelFaceParent
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) : K.Face :=
  ⟨Classical.choose ((K.safeSubdivision n).subordinate s.1 s.2),
    (Classical.choose_spec
      ((K.safeSubdivision n).subordinate s.1 s.2)).1⟩

theorem levelFaceParent_contains
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (x : (K.safeSubdivision n).refined.realization)
    (hx : x ∈ (K.safeSubdivision n).refined.faceCarrier s.1) :
    (K.safeSubdivision n).homeo x ∈
      K.faceCarrier (levelFaceParent K s).1 :=
  (Classical.choose_spec
    ((K.safeSubdivision n).subordinate s.1 s.2)).2 x hx

/-- The canonical affine formula of the midpoint-subdivision homeomorphism on one level
face. -/
noncomputable def levelFaceSourceAffine
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    ((K.safeSubdivision n).refined.Vertex → ℝ) →ᵃ[ℝ]
      (K.Vertex → ℝ) :=
  Classical.choose ((K.safeSubdivision n).affineOnFace s.1 s.2)

theorem levelFaceSourceAffine_eq
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (x : (K.safeSubdivision n).refined.realization)
    (hx : x ∈ (K.safeSubdivision n).refined.faceCarrier s.1) :
    ((K.safeSubdivision n).homeo x).1 =
      levelFaceSourceAffine K s x.1 :=
  Classical.choose_spec
    ((K.safeSubdivision n).affineOnFace s.1 s.2) x hx

/-- A level face, transported to the standard plane chart of its original parent, is affine
in its own standard triangle coordinates. -/
noncomputable def levelFaceParentPlaneAffine
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Plane →ᵃ[ℝ] Plane :=
  (K.facePlaneForwardAffine (levelFaceParent K s)).comp
    ((levelFaceSourceAffine K s).comp
      ((K.safeSubdivision n).refined.facePlaneInverseAffine s))

theorem levelFaceParentPlaneAffine_eq
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (p : standardTrianglePlaneComplex.support) :
    levelFaceParentPlaneAffine K s p.1 =
      (K.facePlaneHomeomorph (levelFaceParent K s)
        ⟨(K.safeSubdivision n).homeo
            ((K.safeSubdivision n).refined.facePlaneHomeomorph s |>.symm p),
          levelFaceParent_contains K s _
            (((K.safeSubdivision n).refined.facePlaneHomeomorph s).symm p).2⟩).1 := by
  let R := K.safeSubdivision n
  let x : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm p
  rw [K.facePlaneHomeomorph_val_eq_forwardAffine]
  simp only [levelFaceParentPlaneAffine, AffineMap.comp_apply]
  apply congrArg (K.facePlaneForwardAffine (levelFaceParent K s))
  calc
    levelFaceSourceAffine K s
        (R.refined.facePlaneInverseAffine s p.1) =
      levelFaceSourceAffine K s x.1.1 := by
        apply congrArg (levelFaceSourceAffine K s)
        exact (R.refined.facePlaneHomeomorph_symm_val s p).symm
    _ = (R.homeo x.1).1 :=
      (levelFaceSourceAffine_eq K s x.1 x.2).symm

/-- The parent-plane formula for a level face is injective on the standard closed triangle. -/
theorem levelFaceParentPlaneAffine_injOn
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Set.InjOn (levelFaceParentPlaneAffine K s)
      standardTrianglePlaneComplex.support := by
  intro p hp q hq hpq
  let pp : standardTrianglePlaneComplex.support := ⟨p, hp⟩
  let qq : standardTrianglePlaneComplex.support := ⟨q, hq⟩
  let R := K.safeSubdivision n
  let x : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm pp
  let y : R.refined.ClosedFace s :=
    (R.refined.facePlaneHomeomorph s).symm qq
  have hchart :
      K.facePlaneHomeomorph (levelFaceParent K s)
          ⟨R.homeo x.1, levelFaceParent_contains K s x.1 x.2⟩ =
        K.facePlaneHomeomorph (levelFaceParent K s)
          ⟨R.homeo y.1, levelFaceParent_contains K s y.1 y.2⟩ := by
    apply Subtype.ext
    rw [← levelFaceParentPlaneAffine_eq K s pp,
      ← levelFaceParentPlaneAffine_eq K s qq]
    exact hpq
  have hhomeo : R.homeo x.1 = R.homeo y.1 := by
    exact congrArg (fun z => z.1)
      ((K.facePlaneHomeomorph (levelFaceParent K s)).injective hchart)
  have hxy : x = y := by
    apply Subtype.ext
    exact R.homeo.injective hhomeo
  calc
    p = ((R.refined.facePlaneHomeomorph s) x).1 := by
      change pp.1 = ((R.refined.facePlaneHomeomorph s)
        ((R.refined.facePlaneHomeomorph s).symm pp)).1
      exact congrArg Subtype.val
        ((R.refined.facePlaneHomeomorph s).apply_symm_apply pp).symm
    _ = ((R.refined.facePlaneHomeomorph s) y).1 :=
      congrArg (fun z => ((R.refined.facePlaneHomeomorph s) z).1) hxy
    _ = q := by
      change ((R.refined.facePlaneHomeomorph s)
        ((R.refined.facePlaneHomeomorph s).symm qq)).1 = qq.1
      exact congrArg Subtype.val
        ((R.refined.facePlaneHomeomorph s).apply_symm_apply qq)

theorem levelFaceParentPlaneAffine_injective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Function.Injective (levelFaceParentPlaneAffine K s) := by
  apply affineMap_injective_of_injOn_convexHull
    standardTriangleVertex standardTriangleVertex_affineIndependent
  rw [← standardTrianglePlaneComplex_support]
  exact levelFaceParentPlaneAffine_injOn K s

theorem levelFaceParentPlaneAffine_surjective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n) :
    Function.Surjective (levelFaceParentPlaneAffine K s) := by
  apply affineMap_surjective_of_injOn_convexHull
    standardTriangleVertex standardTriangleVertex_affineIndependent
  rw [← standardTrianglePlaneComplex_support]
  exact levelFaceParentPlaneAffine_injOn K s

/-- Barycentric coordinate of a level face after transport to its original parent plane. -/
noncomputable def levelFaceParentCoord
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (affineBasisOfTriangle
    (levelFaceParentPlaneAffine K s ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent
      (levelFaceParentPlaneAffine K s) (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s))).coord k

@[simp] theorem levelFaceParentCoord_vertex
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k i : Fin 3) :
    levelFaceParentCoord K s k
      (levelFaceParentPlaneAffine K s (standardTriangleVertex i)) =
        if k = i then 1 else 0 := by
  exact AffineBasis.coord_apply _ _ _

theorem levelFaceParentCoord_surjective
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) :
    Function.Surjective (levelFaceParentCoord K s k) := by
  simpa only [levelFaceParentCoord] using
    (affineBasisOfTriangle
      (levelFaceParentPlaneAffine K s ∘ standardTriangleVertex)
      (affineIndependent_comp_of_injOn_convexHull
        standardTriangleVertex standardTriangleVertex_affineIndependent
        (levelFaceParentPlaneAffine K s) (by
          rw [← standardTrianglePlaneComplex_support]
          exact levelFaceParentPlaneAffine_injOn K s))).surjective_coord k

theorem levelFaceParentCoord_nonneg
    (K : IntrinsicTwoComplex) {n : ℕ} (s : K.LevelFace n)
    (k : Fin 3) (p : standardTrianglePlaneComplex.support) :
    0 ≤ levelFaceParentCoord K s k
      (levelFaceParentPlaneAffine K s p.1) := by
  let F := levelFaceParentPlaneAffine K s
  let b := affineBasisOfTriangle
    (F ∘ standardTriangleVertex)
    (affineIndependent_comp_of_injOn_convexHull
      standardTriangleVertex standardTriangleVertex_affineIndependent F (by
        rw [← standardTrianglePlaneComplex_support]
        exact levelFaceParentPlaneAffine_injOn K s))
  have hp :
      F p.1 ∈ convexHull ℝ
        (Set.range (F ∘ standardTriangleVertex)) := by
    rw [Set.range_comp, ← F.image_convexHull,
      ← standardTrianglePlaneComplex_support]
    exact ⟨p.1, p.2, rfl⟩
  have hb : (fun i => b i) = F ∘ standardTriangleVertex := by
    funext i
    rfl
  have hp' : F p.1 ∈ convexHull ℝ (Set.range b) := by
    rw [show Set.range b =
        Set.range (F ∘ standardTriangleVertex) by
      exact congrArg Set.range hb]
    exact hp
  have hpk : 0 ≤ b.coord k (F p.1) := by
    rw [b.convexHull_eq_nonneg_coord] at hp'
    exact hp' k
  exact hpk

/-- A point in the relative interior of an original maximal face cannot also belong to a
distinct original maximal face.  The relative interior is detected in the canonical standard
plane chart. -/
theorem face_eq_of_mem_faceCarriers_of_facePlane_mem_interior
    (K : IntrinsicTwoComplex) (t u : K.Face) (x : K.realization)
    (hxt : x ∈ K.faceCarrier t.1) (hxu : x ∈ K.faceCarrier u.1)
    (hxint :
      (K.facePlaneHomeomorph t ⟨x, hxt⟩).1 ∈
        interior standardTrianglePlaneComplex.support) :
    t = u := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro v hvt
    by_contra hvu
    have hxzero : x.1 v = 0 := hxu v hvu
    let p : standardTrianglePlaneComplex.support :=
      K.facePlaneHomeomorph t ⟨x, hxt⟩
    let i : Fin 3 := (K.faceVertexEquiv t).symm ⟨v, hvt⟩
    have hpint :
        p.1 ∈ interior
          (standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
            standardTriangleMeshFace.1) := by
      rw [show
          standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
              standardTriangleMeshFace.1 =
            standardTrianglePlaneComplex.support by
        exact standardTriangle_cellCarrier_univ]
      exact hxint
    have hcoordpos :
        0 <
          standardTrianglePlaneComplex.faceCoords
            standardTriangleMeshFace p.1 i := by
      rw [standardTrianglePlaneComplex.faceCoords_apply_of_mem
        standardTriangleMeshFace (Finset.mem_univ i)]
      rw [standardTrianglePlaneComplex.toTriangleMesh.interior_triangleCarrier
        standardTriangleMeshFace] at hpint
      exact hpint
        (standardTrianglePlaneComplex.toTriangleMesh.triangleEquiv
          standardTriangleMeshFace ⟨i, Finset.mem_univ i⟩)
    have hxcoord :
        x.1 v =
          standardTrianglePlaneComplex.faceCoords
            standardTriangleMeshFace p.1 i := by
      calc
        x.1 v =
            ((K.facePlaneHomeomorph t).symm p).1.1 v := by
              have h :=
                (K.facePlaneHomeomorph t).symm_apply_apply ⟨x, hxt⟩
              exact congrFun (congrArg (fun z => z.1.1) h.symm) v
        _ = K.facePlaneInverseAffine t p.1 v :=
          congrFun (K.facePlaneHomeomorph_symm_val t p) v
        _ =
            standardTrianglePlaneComplex.faceCoords
              standardTriangleMeshFace p.1 i := by
          simp only [IntrinsicTwoComplex.facePlaneInverseAffine, AffineMap.comp_apply,
            K.faceCoordExtensionAffine_apply_of_mem _ _ hvt]
          rfl
    linarith
  · rw [K.faces_card t.1 t.2, K.faces_card u.1 u.2]

/-- Pull every fixed-level face coordinate back through every relative source triangle whose
chosen original parent agrees.  Cutting by these finitely many affine lines makes the next
relative source mesh subordinate to the fixed-level triangulation. -/
noncomputable def relativeLevelAlignmentLines
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ)) (n : ℕ) :
    List (Plane →ᵃ[ℝ] ℝ) :=
  let M := A.tileFacesMeetingRelativeOldMesh C hC N baseExtraLines
  (Finset.univ : Finset M.Triangle).toList.flatMap fun t =>
    (Finset.univ : Finset (K.LevelFace n)).toList.flatMap fun s =>
      if levelFaceParent K s =
          A.relativeOldTriangleParent C hC N baseExtraLines t then
        (Finset.univ : Finset (Fin 3)).toList.map fun k =>
          (levelFaceParentCoord K s k).comp
            (A.relativeOldTriangleParentPlaneAffine
              C hC N baseExtraLines t)
      else
        []

theorem relativeLevelAlignmentLine_mem
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ)) (n : ℕ)
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N baseExtraLines).Triangle)
    (s : K.LevelFace n)
    (hparent :
      levelFaceParent K s =
        A.relativeOldTriangleParent C hC N baseExtraLines t)
    (k : Fin 3) :
    (levelFaceParentCoord K s k).comp
        (A.relativeOldTriangleParentPlaneAffine
          C hC N baseExtraLines t) ∈
      A.relativeLevelAlignmentLines C hC N baseExtraLines n := by
  classical
  unfold relativeLevelAlignmentLines
  apply List.mem_flatMap.mpr
  refine ⟨t, Finset.mem_toList.mpr (Finset.mem_univ t), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨s, Finset.mem_toList.mpr (Finset.mem_univ s), ?_⟩
  rw [ite_eq_left hparent]
  apply List.mem_map.mpr
  exact ⟨k, Finset.mem_toList.mpr (Finset.mem_univ k), rfl⟩

theorem relativeLevelAlignmentLine_surjective
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh)
    (baseExtraLines : List (Plane →ᵃ[ℝ] ℝ))
    (t : (A.tileFacesMeetingRelativeOldMesh
      C hC N baseExtraLines).Triangle)
    {n : ℕ} (s : K.LevelFace n) (k : Fin 3) :
    Function.Surjective
      ((levelFaceParentCoord K s k).comp
        (A.relativeOldTriangleParentPlaneAffine
          C hC N baseExtraLines t)) := by
  intro y
  obtain ⟨q, hq⟩ := levelFaceParentCoord_surjective K s k y
  obtain ⟨p, hp⟩ :=
    A.relativeOldTriangleParentPlaneAffine_surjective
      C hC N baseExtraLines t q
  exact ⟨p, by simp only [AffineMap.comp_apply, hp, hq]⟩

/-- The synchronized old coordinate mesh, regarded as a subspace of the global replacement
support. -/
noncomputable def tileFacesMeetingOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    GeometricRealization
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).Vertex
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).triangles →
      Q.complex.support :=
  fun x => by
    let p : Plane :=
      (SynchronizedTarget.oldMesh
        (A.tileFacePolygonMeeting C hC) N).coordinateEmbed x
    have hpClosed :
        p ∈ PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
      rw [← SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N,
        ← (SynchronizedTarget.oldMesh
          (A.tileFacePolygonMeeting C hC) N).range_coordinateEmbed]
      exact Set.mem_range_self x
    let pV : V :=
      ⟨p, A.tileFacePolygonMeeting_closedRegion_subset_region C hC hpClosed⟩
    exact ⟨pV,
      A.tileFacePolygonMeeting_subset_complex_support C hC hpClosed⟩

theorem isEmbedding_tileFacesMeetingOldCoordinateSupport
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    _root_.Topology.IsEmbedding
      (A.tileFacesMeetingOldCoordinateSupport C hC N) := by
  let M := SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N
  have hclosed (x : GeometricRealization M.Vertex M.triangles) :
      M.coordinateEmbed x ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) := by
    rw [← SynchronizedTarget.oldMesh_support
      (A.tileFacePolygonMeeting C hC) N, ← M.range_coordinateEmbed]
    exact Set.mem_range_self x
  let fV : GeometricRealization M.Vertex M.triangles → V :=
    Set.codRestrict M.coordinateEmbed V fun x =>
      A.tileFacePolygonMeeting_closedRegion_subset_region C hC (hclosed x)
  have hfV : _root_.Topology.IsEmbedding fV :=
    M.isEmbedding_coordinateEmbed.codRestrict V _
  have hfQ : _root_.Topology.IsEmbedding
      (Set.codRestrict fV Q.complex.support fun x =>
        A.tileFacePolygonMeeting_subset_complex_support C hC (hclosed x)) :=
    hfV.codRestrict Q.complex.support _
  convert hfQ using 1
  funext x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Pull the synchronized old coordinate triangulation back through the retained source
homeomorphism to the original finite intrinsic realization. -/
noncomputable def tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    GeometricRealization
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).Vertex
        (SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N).triangles →
      K.realization :=
  Subtype.val ∘ Q.sourceHomeomorph.symm ∘
    A.tileFacesMeetingOldCoordinateSupport C hC N

theorem isEmbedding_tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    _root_.Topology.IsEmbedding (A.tileFacesMeetingSourceEmbed C hC N) :=
  _root_.Topology.IsEmbedding.subtypeVal.comp
    (Q.sourceHomeomorph.symm.isEmbedding.comp
      (A.isEmbedding_tileFacesMeetingOldCoordinateSupport C hC N))

/-- The synchronized old mesh pulls back onto exactly the finite whole-tile source
subcomplex. -/
theorem range_tileFacesMeetingSourceEmbed
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    Set.range (A.tileFacesMeetingSourceEmbed C hC N) =
      ⋃ f : A.TileFacesMeeting C hC, Q.sourceFaceSet f.1 := by
  rw [A.sourceTileFacesMeeting_eq_coordinatePreimage C hC]
  let M := SynchronizedTarget.oldMesh (A.tileFacePolygonMeeting C hC) N
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    let q : Q.complex.support :=
      A.tileFacesMeetingOldCoordinateSupport C hC N z
    refine ⟨(Q.sourceHomeomorph.symm q).2, ?_⟩
    have hqClosed :
        q.1.1 ∈ PolygonalFamily.closedRegion
          (A.tileFacePolygonMeeting C hC) := by
      change M.coordinateEmbed z ∈
        PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC)
      rw [← SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N, ← M.range_coordinateEmbed]
      exact Set.mem_range_self z
    have harg :
        (⟨A.tileFacesMeetingSourceEmbed C hC N z,
            (Q.sourceHomeomorph.symm q).2⟩ : U) =
          Q.sourceHomeomorph.symm q :=
      Subtype.ext rfl
    rw [harg, Q.sourceHomeomorph.apply_symm_apply]
    exact hqClosed
  · rintro x ⟨hxU, hxClosed⟩
    let q : Q.complex.support := Q.sourceHomeomorph ⟨x, hxU⟩
    have hqM : q.1.1 ∈ M.toPlaneComplex.support := by
      rw [SynchronizedTarget.oldMesh_support
        (A.tileFacePolygonMeeting C hC) N]
      exact hxClosed
    rw [← M.range_coordinateEmbed] at hqM
    obtain ⟨z, hz⟩ := hqM
    refine ⟨z, ?_⟩
    change
      (Q.sourceHomeomorph.symm
        (A.tileFacesMeetingOldCoordinateSupport C hC N z)).1 = x
    have hsupportEq :
        A.tileFacesMeetingOldCoordinateSupport C hC N z = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hz
    rw [hsupportEq]
    exact congrArg Subtype.val (Q.sourceHomeomorph.symm_apply_apply ⟨x, hxU⟩)

/-- In intrinsic terms, the range is a literal subcomplex of one finite midpoint level. -/
theorem range_tileFacesMeetingSourceEmbed_eq_levelFaces
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C) (N : TriangleMesh) :
    Set.range (A.tileFacesMeetingSourceEmbed C hC N) =
      ⋃ u : {u : K.LevelFace (A.commonLevel (A.tilesMeeting C hC)) //
          u ∈ A.levelFaces (A.tilesMeeting C hC)},
        K.levelFaceCarrier u.1 :=
  (A.range_tileFacesMeetingSourceEmbed C hC N).trans
    (A.sourceTileFacesMeeting_eq_levelFaces C hC)

/-- Every polygon in a compactly selected tile family lies in the chart model whenever the
retained coordinate homeomorphism does. -/
theorem tileFacePolygonMeeting_closedRegion_subset_modelRegion
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion (A.tileFacePolygonMeeting C hC) ⊆
      c.kind.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ V := Q.faceClosedRegion_subset f.1 hxf
  let z : V := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate c.kind g' hcoord hzSupport

/-- A compactly selected whole-tile family admits a synchronized local weld with any prescribed
finite target mesh in the same chart model. -/
theorem exists_tileFacesMeeting_local_weld
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization} {V : Set Plane}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U V}
    (A : PolygonalReplacementSourceAtlas K U V Q)
    (C : Set V) (hC : IsCompact C)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1)
    (N : TriangleMesh)
    (harr : N.toPlaneComplex.support ⊆
      (PolygonalFamily.arrangementMesh
        (A.tileFacePolygonMeeting C hC)).toPlaneComplex.support)
    (hnew : N.toPlaneComplex.support ⊆ c.kind.modelRegion) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (F₁ F₂ : Finset (Finset W))
      (e₁ : GeometricRealization W F₁ → S)
      (e₂ : GeometricRealization W F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization W F₁) (y : GeometricRealization W F₂),
        (x : W → ℝ) = (y : W → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization W F₁) (y : GeometricRealization W F₂),
        e₁ x = e₂ y → (x : W → ℝ) = (y : W → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) :=
  SynchronizedTarget.exists_local_weld c
    (A.tileFacePolygonMeeting C hC) N harr
    (A.tileFacePolygonMeeting_closedRegion_subset_modelRegion c C hC g' hcoord)
    hnew

/-- The polygonal family obtained by retaining every fan face in every adaptive tile touched by
the patch. -/
def patchTileFacePolygon
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    A.PatchTileFaces → PolygonalCircle :=
  fun f ↦ Q.facePolygon f.1

/-- The retained finite PL certificate for one face of the tile-closed source family. -/
noncomputable def patchTileFaceCertificate
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (f : A.PatchTileFaces) :
    FinitePLHomeomorphBetween (Q.faceFillingMap f.1)
      LocallyFiniteTriangleComplex.standardFaceRegion
      (A.patchTileFacePolygon f).closedRegion :=
  Classical.choice (Q.faceCertificate f.1)

/-- Pull the synchronized mesh of one selected polygon back to its standard source triangle.
The target side is first commonly refined with the original Schoenflies certificate, so the
result carries every chart-patch intersection vertex. -/
noncomputable def patchTileFacePullback
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (N : TriangleMesh) (f : A.PatchTileFaces) :
    (A.patchTileFaceCertificate f).PullbackSubdivision
      (SynchronizedPatch.singlePolygonMesh A.patchTileFacePolygon N f).toPlaneComplex :=
  (A.patchTileFaceCertificate f).pullbackSubdivision _
    (SynchronizedPatch.singlePolygonMesh A.patchTileFacePolygon N f).toPlaneComplex_isPure2
    (SynchronizedPatch.singlePolygonMesh_support A.patchTileFacePolygon N f)

/-- The exact coordinate union of the tile-closed family is the image, under the retained source
homeomorphism, of its exact common-level source subcomplex. -/
theorem sourcePatchTileFaces_eq_coordinatePreimage
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q) :
    (⋃ f : A.PatchTileFaces, Q.sourceFaceSet f.1) =
      {x : K.realization | ∃ hx : x ∈ U,
        (Q.sourceHomeomorph ⟨x, hx⟩).1.1 ∈
          PolygonalFamily.closedRegion A.patchTileFacePolygon} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨f, hxFace⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hxU, hxQ⟩ := hxFace
    refine ⟨hxU, Set.mem_iUnion.mpr ⟨f, ?_⟩⟩
    rw [Q.faceCarrier_eq f.1] at hxQ
    simpa [patchTileFacePolygon] using hxQ
  · rintro x ⟨hxU, hxFamily⟩
    obtain ⟨f, hxPolygon⟩ := Set.mem_iUnion.mp hxFamily
    apply Set.mem_iUnion.mpr
    refine ⟨f, hxU, ?_⟩
    rw [Q.faceCarrier_eq f.1]
    exact hxPolygon

/-- Every polygon in the tile-closed family still lies in the chart model (including the
half-plane condition in the bordered case). -/
theorem patchTileFaceClosedRegion_subset_modelRegion
    {K : IntrinsicTwoComplex} {U : Set K.realization} {k : ChartKind}
    {Q : PolygonalReplacementPresentation U k.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U k.perturbationRegion Q)
    (g' : U → k.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    PolygonalFamily.closedRegion A.patchTileFacePolygon ⊆ k.modelRegion := by
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
  have hxV : x ∈ k.perturbationRegion := Q.faceClosedRegion_subset f.1 hxf
  let z : k.perturbationRegion := ⟨x, hxV⟩
  have hzFace : z ∈ Q.complex.faceCarrier f.1 := by
    rw [Q.faceCarrier_eq f.1]
    exact hxf
  have hzSupport : z ∈ Q.complex.support :=
    Set.mem_iUnion.mpr ⟨f.1, hzFace⟩
  exact Q.support_subset_modelRegion_of_coordinate k g' hcoord hzSupport

/-- The corrected finite local weld: its old side is closed under whole adaptive source tiles,
so it is exactly supported on a finite common-level source subcomplex. -/
theorem exists_patchTile_local_weld
    {S : Type*} [TopologicalSpace S]
    {K : IntrinsicTwoComplex} {U : Set K.realization}
    (c : MoiseChart S)
    {Q : PolygonalReplacementPresentation U c.kind.perturbationRegion}
    (A : PolygonalReplacementSourceAtlas K U c.kind.perturbationRegion Q)
    (g' : U → c.kind.modelRegion)
    (hcoord : ∀ y, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (F₁ F₂ : Finset (Finset V))
      (e₁ : GeometricRealization V F₁ → S)
      (e₂ : GeometricRealization V F₂ → S),
      (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
      _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
      (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
        e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
      (∀ e ∈ (F₁ ∪ F₂).biUnion fun t ↦ t.powersetCard 2,
        ((F₁ ∪ F₂).filter fun t ↦ e ⊆ t).card ≤ 2) :=
  SynchronizedPatch.exists_synchronizedPatch_local_weld c A.patchTileFacePolygon
    (A.patchTileFaceClosedRegion_subset_modelRegion g' hcoord)

end PolygonalReplacementSourceAtlas

private noncomputable def straightenedChartOpenSourceHomeomorph
    {K : IntrinsicTwoComplex} {U : Set K.realization}
    (R : LocallyFiniteTriangleComplex U)
    (G : R.PlaneGraphRealization) (H : R.CellwiseCompatibility G)
    (hRsupport : R.support = Set.univ) :
    U ≃ₜ (R.polygonalReplacementComplex H).support := by
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  exact eU.trans (R.polygonalReplacementHomeomorph H)

private noncomputable def straightenedChartOpenPresentation
    {K : IntrinsicTwoComplex} {U : Set K.realization}
    (R : LocallyFiniteTriangleComplex U)
    (G : R.PlaneGraphRealization) (H : R.CellwiseCompatibility G)
    (hRsupport : R.support = Set.univ) :
    PolygonalReplacementPresentation U G.region :=
  let q := straightenedChartOpenSourceHomeomorph R G H hRsupport
  { complex := R.polygonalReplacementComplex H
    sourceHomeomorph := q
    facePolygon := fun f ↦ R.facePolygonalCircle (G := G) f
    faceFillingMap := fun f ↦ (R.facePLFilling (G := G) f).map
    faceMap_eq := fun _ _ ↦ rfl
    faceCertificate := fun f ↦ (R.facePLFilling (G := G) f).certificate
    faceClosedRegion_subset := fun f ↦ H.closedRegions_mem_region f
    faceCarrier_eq := fun f ↦ R.polygonalReplacementComplex_faceCarrier H f }

@[simp]
private theorem straightenedChartOpenPresentation_sourceHomeomorph
    {K : IntrinsicTwoComplex} {U : Set K.realization}
    (R : LocallyFiniteTriangleComplex U)
    (G : R.PlaneGraphRealization) (H : R.CellwiseCompatibility G)
    (hRsupport : R.support = Set.univ) :
    (straightenedChartOpenPresentation R G H hRsupport).sourceHomeomorph =
      straightenedChartOpenSourceHomeomorph R G H hRsupport := rfl

private noncomputable def straightenedChartOpenSourceAtlas
    {S' : Type*} [TopologicalSpace S']
    (T : PartialTriangulation S')
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (V : Set Plane) (hV : IsOpen V)
    (f : U → Plane) (hf : Continuous f) (hmem : ∀ x, f x ∈ V)
    (mu : U → ℝ) (hmu : StronglyPositiveOn Set.univ mu)
    (G :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem
        mu hmu).PlaneGraphRealization)
    (H :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem
        mu hmu).CellwiseCompatibility G)
    (hRsupport :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu).support =
        Set.univ) :
    PolygonalReplacementSourceAtlas T.toIntrinsic U G.region
      (straightenedChartOpenPresentation
        (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu)
        G H hRsupport) := by
  classical
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  letI : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  letI : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  let Q := straightenedChartOpenPresentation R G H hRsupport
  let q := straightenedChartOpenSourceHomeomorph R G H hRsupport
  let uToSupport : U → R.support := fun x ↦ ⟨x, by
    rw [hRsupport]
    trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let sourceParent (a : T.toIntrinsic.AdaptiveFanFace U hU) : T.toIntrinsic.Face := by
    let Rt := T.toIntrinsic.safeSubdivision a.1.1
    let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
    exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  refine
    { Tile := T.toIntrinsic.AdaptiveFace U
      tileDecidableEq := Classical.decEq _
      tile := fun f ↦ f.1
      tileFaces := T.toIntrinsic.adaptiveFanFacesOver U hU
      mem_tileFaces := fun t f ↦ T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t f
      sourceTileCarrier := T.toIntrinsic.adaptiveFaceCarrier U
      sourceTileCarrier_subset_open := fun t ↦
        T.toIntrinsic.adaptiveFaceCarrier_subset U t
      sourceTileCarrier_locallyFinite :=
        T.toIntrinsic.locallyFinite_adaptiveFaceCarrierInOpen U hU
      sourceTileCarrier_eq_faces := ?_
      sourceFaceParent := sourceParent
      sourceFaceSet_subset_parent := ?_
      sourceFaceStandardAffine := ?_
      commonLevel := T.toIntrinsic.adaptiveFaceCommonLevel U
      levelFaces := fun F ↦
        (Finset.univ : Finset
          (T.toIntrinsic.LevelFace (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
          fun u ↦ ∃ t ∈ F,
            T.toIntrinsic.levelFaceCarrier u ⊆ T.toIntrinsic.adaptiveFaceCarrier U t
      sourceTiles_eq_levelFaces := ?_ }
  · intro t
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, j, z, hz⟩ :=
        T.toIntrinsic.exists_adaptiveFanFaceMap_eq_of_mem_adaptiveFaceCarrier U hU t hx
      let a : T.toIntrinsic.AdaptiveFanFace U hU := ⟨t, i, j⟩
      have ha : a ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t :=
        (T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a).2 rfl
      let a' : {f : Q.complex.Face //
          f ∈ T.toIntrinsic.adaptiveFanFacesOver U hU t} := ⟨a, ha⟩
      apply Set.mem_iUnion.mpr
      refine ⟨a', ?_⟩
      let hxU : x ∈ U := T.toIntrinsic.adaptiveFaceCarrier_subset U t hx
      refine ⟨hxU, ?_⟩
      apply (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
        (eU ⟨x, hxU⟩)).2
      change ⟨x, hxU⟩ ∈ Set.range (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a)
      rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a]
      exact ⟨z, hz⟩
    · intro x hx
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hxU, hxaQ⟩ := hxa
      have hxaR := (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a.1
        (eU ⟨x, hxU⟩)).1 hxaQ
      change ⟨x, hxU⟩ ∈ Set.range
        (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a.1) at hxaR
      rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a.1] at hxaR
      have hxt := T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a.1 hxaR
      change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1.1 at hxt
      rw [(T.toIntrinsic.mem_adaptiveFanFacesOver_iff U hU t a.1).1 a.2] at hxt
      exact hxt
  · intro a x hx
    change T.toIntrinsic.AdaptiveFanFace U hU at a
    obtain ⟨hxU, hxaQ⟩ := hx
    have hxaR := (R.polygonalReplacementHomeomorph_mem_faceCarrier_iff H a
      (eU ⟨x, hxU⟩)).1 hxaQ
    change ⟨x, hxU⟩ ∈ Set.range
      (T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a) at hxaR
    rw [T.toIntrinsic.range_adaptiveGlobalFanFaceMap U hU a] at hxaR
    have hxt := T.toIntrinsic.range_adaptiveFanFaceMap_subset_tile U hU a hxaR
    change x ∈ T.toIntrinsic.adaptiveFaceCarrier U a.1 at hxt
    obtain ⟨z, hz, hzx⟩ := hxt
    let Rt := T.toIntrinsic.safeSubdivision a.1.1
    let h := Rt.subordinate a.1.2.1.1 a.1.2.1.2
    have hzParent := (Classical.choose_spec h).2 z hz
    change x ∈ T.toIntrinsic.faceCarrier (Classical.choose h)
    rw [← hzx]
    exact hzParent
  · intro a
    change T.toIntrinsic.AdaptiveFanFace U hU at a
    obtain ⟨b, hb⟩ := T.toIntrinsic.adaptiveGlobalFanFaceMap_standardAffine hU a
    refine ⟨b, ?_⟩
    intro x
    have hsource :
        q.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := Q.complex) a x) =
          eU.symm (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := R) a x) := by
      change eU.symm ((R.polygonalReplacementHomeomorph H).symm
          (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := Q.complex) a x)) = _
      congr 1
      exact R.polygonalReplacementInverse_faceToSupport H a x
    change (q.symm
        (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
          (K := Q.complex) a x)).1.1 = b (Q.complex.facePlaneHomeomorph a x).1
    rw [hsource]
    exact hb x
  · intro F
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
      rw [T.toIntrinsic.adaptiveFaceCarrier_eq_iUnion_commonLevel_descendants U F t.2] at hxt
      obtain ⟨u, hxt⟩ := Set.mem_iUnion.mp hxt
      obtain ⟨hut, hxu⟩ := Set.mem_iUnion.mp hxt
      let u' : {u : T.toIntrinsic.LevelFace
          (T.toIntrinsic.adaptiveFaceCommonLevel U F) //
          u ∈ (Finset.univ : Finset
            (T.toIntrinsic.LevelFace
              (T.toIntrinsic.adaptiveFaceCommonLevel U F))).filter
              (fun u ↦ ∃ t ∈ F,
                T.toIntrinsic.levelFaceCarrier u ⊆
                  T.toIntrinsic.adaptiveFaceCarrier U t)} :=
        ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨t.1, t.2, hut⟩⟩⟩
      exact Set.mem_iUnion.mpr ⟨u', hxu⟩
    · intro x hx
      obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hx
      obtain ⟨-, t, htF, hut⟩ := Finset.mem_filter.mp u.2
      let t' : {t : T.toIntrinsic.AdaptiveFace U // t ∈ F} := ⟨t, htF⟩
      exact Set.mem_iUnion.mpr ⟨t', hut hxu⟩

private theorem straightenedChartOpen_coordZero_iff_boundary
    {S' : Type*} [TopologicalSpace S'] [ChartedSpace (EuclideanHalfSpace 2) S']
    (T : PartialTriangulation S') (c : MoiseChart S') (hc : c.BoundaryFaithful)
    (hboundary : T.BoundaryFacewiseRegular)
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (hsub : U ⊆ T.chartOverlap c)
    (V : Set Plane) (hV : IsOpen V)
    (f : U → Plane) (hf : Continuous f) (hmem : ∀ x, f x ∈ V)
    (hfcoord : ∀ x, f x = T.chartOverlapMap c ⟨x.1, hsub x.2⟩)
    (mu : U → ℝ) (hmu : StronglyPositiveOn Set.univ mu)
    (G :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem
        mu hmu).PlaneGraphRealization)
    (H :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem
        mu hmu).CellwiseCompatibility G)
    (hRsupport :
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu).support =
        Set.univ)
    (hGmap : ∀ p, G.map p = f p.1) :
    let q := straightenedChartOpenSourceHomeomorph
      (T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu)
      G H hRsupport
    ∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
      (q y).1.1 0 = 0 ↔
        T.embed y.1 ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S' := by
  classical
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  let : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  let : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  let q := straightenedChartOpenSourceHomeomorph R G H hRsupport
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let toOverlap : U → T.chartOverlap c := fun x ↦ ⟨x.1, hsub x.2⟩
  dsimp only
  intro hk y
  have hfHalf : Set.range G.map ⊆ HalfPlaneSet := by
    rintro z ⟨p, rfl⟩
    rw [hGmap]
    have hpModel : f p.1 ∈ c.kind.modelRegion := by
      rw [hfcoord p.1]
      exact (T.chartOverlapModelMap c (toOverlap p.1)).2
    rw [hk] at hpModel
    exact hpModel.2
  have hGface :
      LocallyFiniteTriangleComplex.PlaneGraphRealization.FacewiseCoordZeroExposed G := by
    intro a
    let Rt := T.toIntrinsic.safeSubdivision a.1.1
    let hs := Rt.subordinate a.1.2.1.1 a.1.2.1.2
    let t : T.toIntrinsic.Face := ⟨Classical.choose hs, (Classical.choose_spec hs).1⟩
    obtain ⟨b, hbt, hbcard, hb⟩ := hboundary t.1 t.2
    let E := T.toIntrinsic.adaptiveFanFaceVertexEquiv U hU a
    let v₀ : {v // v ∈ T.toIntrinsic.adaptiveGlobalFanFaceVertices U hU a} :=
      E.symm (T.toIntrinsic.adaptiveFanCenterVertex U hU a)
    have hv₀ : v₀.1.1 ∉ T.toIntrinsic.faceCarrier b := by
      change T.toIntrinsic.adaptiveFaceCenter U a.1 ∉ T.toIntrinsic.faceCarrier b
      apply T.toIntrinsic.adaptiveFaceCenter_not_mem_faceCarrier_of_subordinate hU a t
      · exact (Classical.choose_spec hs).2
      · exact hbt
      · exact hbcard
    obtain ⟨d, hda, hdcard, hd⟩ :=
      T.toIntrinsic.adaptiveGlobalFanFaceMap_exists_exposedFace hU a b v₀ hv₀
    refine ⟨d, hda, hdcard, ?_⟩
    intro x
    let z : U := T.toIntrinsic.adaptiveGlobalFanFaceMap U hU a x
    have hzt : z.1 ∈ T.toIntrinsic.faceCarrier t.1 :=
      (Classical.choose_spec hs).2
        (T.toIntrinsic.adaptiveFanSourcePoint U hU a
          (T.toIntrinsic.adaptiveFanRelabelSimplex U hU a x))
        (T.toIntrinsic.adaptiveFanSourcePoint_mem_carrier U hU a _)
    have hsurface :
        T.embed z.1 ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S' ↔
          z.1 ∈ T.toIntrinsic.faceCarrier b := hb z.1 hzt
    have hchart :
        T.embed z.1 ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S' ↔
          f z 0 = 0 := by
      have h := MoiseChart.BoundaryFaithful.mem_boundary_iff_isModelBoundary
        c hc (T.embed z.1) (hsub z.2)
      have hmodel : c.kind.IsModelBoundary
          (c.chart ⟨T.embed z.1, hsub z.2⟩ : Plane) ↔ f z 0 = 0 := by
        change c.kind.IsModelBoundary (T.chartOverlapMap c ⟨z.1, hsub z.2⟩) ↔
          f z 0 = 0
        rw [← hfcoord z]
        rw [hk]
        rfl
      exact h.trans hmodel
    have hsource : G.map
          (LocallyFiniteTriangleComplex.PlaneGraphRealization.faceToSupport
            (K := R) a x) 0 = 0 ↔ z.1 ∈ T.toIntrinsic.faceCarrier b := by
      rw [hGmap]
      exact hchart.symm.trans hsurface
    exact hsource.trans (hd x)
  have hzero := polygonalReplacementHomeomorph_coordZero_iff_of_facewiseCoordZeroExposed
    G H hfHalf hGface (eU y)
  rw [hGmap] at hzero
  have heUy : (eU y).1 = y := rfl
  rw [heUy] at hzero
  have hqy : q y = R.polygonalReplacementHomeomorph H (eU y) := by
    apply congrArg (R.polygonalReplacementHomeomorph H)
    apply Subtype.ext
    rfl
  have hzero' : (q y).1.1 0 = 0 ↔ f y 0 = 0 := by
    rw [hqy]
    exact hzero
  have hchart := MoiseChart.BoundaryFaithful.mem_boundary_iff_isModelBoundary
    c hc (T.embed y.1) (hsub y.2)
  have hmodel : c.kind.IsModelBoundary
      (c.chart ⟨T.embed y.1, hsub y.2⟩ : Plane) ↔ f y 0 = 0 := by
    change c.kind.IsModelBoundary (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ↔
      f y 0 = 0
    rw [← hfcoord y]
    rw [hk]
    rfl
  exact hzero'.trans (hchart.trans hmodel).symm

/-- Assemble the controlled polygonal replacement over an arbitrary open chart region whose
coordinate image is closed relative to the chosen plane perturbation region. -/
theorem exists_straightenedChartOpen
    {S' : Type*} [TopologicalSpace S'] [T2Space S'] [CompactSpace S']
    [SecondCountableTopology S']
    [ChartedSpace (EuclideanHalfSpace 2) S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (hc : c.BoundaryFaithful)
    (hboundary : T.BoundaryFacewiseRegular)
    (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
    (hsub : U ⊆ T.chartOverlap c)
    (V : Set Plane) (hV : IsOpen V)
    (hVsub : V ⊆ c.kind.perturbationRegion)
    (hmem : ∀ x : U,
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V)
    (hfVclosed : _root_.Topology.IsClosedEmbedding
      (fun x : U ↦
        (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V))) :
    ∃ (Q : PolygonalReplacementPresentation U V)
      (_ : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
      (g' : U → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S'),
      (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      (∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
        (Q.sourceHomeomorph y).1.1 0 = 0 ↔
          T.embed y.1 ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S') ∧
      (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
      (∀ x, x ∉ U → g x = T.embed x) ∧
      MatchesAtFrontier U g T.embed ∧
      ContinuousOn g U ∧
      Set.InjOn g U ∧
      Disjoint (g '' U) (T.embed '' Uᶜ) ∧
      _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
  classical
  let : MetricSpace S' := TopologicalSpace.metrizableSpaceMetric S'
  let toOverlap : U → T.chartOverlap c := fun x ↦ ⟨x.1, hsub x.2⟩
  have htoOverlapEmbedding : _root_.Topology.IsEmbedding toOverlap := by
    simpa [toOverlap] using _root_.Topology.IsEmbedding.inclusion hsub
  let f : U → Plane := fun x ↦ T.chartOverlapMap c (toOverlap x)
  have hf : Continuous f :=
    (T.isEmbedding_chartOverlapMap c).continuous.comp
      htoOverlapEmbedding.continuous
  obtain ⟨mu, hmu, hmatch⟩ :=
    exists_chartMatchingControlOn_of_metricSpace T c U hU hsub
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  let : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  let : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  have hRsupport : R.support = Set.univ := by
    exact IntrinsicTwoComplex.AdaptiveOpenCover.locallyFiniteTriangleComplex_support
      T.toIntrinsic U
      (T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
        (regionSafeControl V f mu)
        (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)) hU
  let toU : R.support → U := Subtype.val
  have htoUclosed : _root_.Topology.IsClosedEmbedding toU := by
    refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [show Set.range toU = R.support by exact Subtype.range_val, hRsupport]
    exact isClosed_univ
  have hfVrestricted : _root_.Topology.IsClosedEmbedding
      (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) := by
    have heq : (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) =
        (fun x : U ↦
          (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V)) ∘ toU := by
      funext p
      apply Subtype.ext
      rfl
    rw [heq]
    exact hfVclosed.comp htoUclosed
  let G : R.PlaneGraphRealization :=
    LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
      V hV (fun p ↦ f p.1)
      ((T.isEmbedding_chartOverlapMap c).comp htoOverlapEmbedding |>.comp
        _root_.Topology.IsEmbedding.subtypeVal)
      (fun p ↦ hmem p.1) hfVrestricted.isClosed_range
  have hGmap : ∀ p, G.map p = f p.1 := fun _ ↦ rfl
  have hGregion : G.region = V := rfl
  obtain ⟨vc, hvc, ec, hec, H, hclose⟩ :=
    IntrinsicTwoComplex.RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison
      T.toIntrinsic U hU V hV f hf hmem mu hmu G hGmap hGregion
  let G' := G.withApproximationControls vc hvc ec hec
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let q := straightenedChartOpenSourceHomeomorph R G' H hRsupport
  let Q := straightenedChartOpenPresentation R G' H hRsupport
  have hfcoord : ∀ x, f x = T.chartOverlapMap c ⟨x.1, hsub x.2⟩ := fun _ ↦ rfl
  have hqzero :
      ∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
        (q y).1.1 0 = 0 ↔
          T.embed y.1 ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S' := by
    exact straightenedChartOpen_coordZero_iff_boundary T c hc hboundary U hU hsub V hV
      f hf hmem hfcoord mu hmu G' H hRsupport hGmap
  let A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q :=
    straightenedChartOpenSourceAtlas T U hU V hV f hf hmem mu hmu G' H hRsupport
  have hqmodel : ∀ y : U, (q y).1.1 ∈ c.kind.modelRegion := by
    intro y
    cases hk : c.kind with
    | disk =>
        have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
          hVsub (q y).1.2
        simpa [ChartKind.modelRegion, ChartKind.perturbationRegion, hk] using
          hyPerturb
    | halfDisk =>
        have hfHalf : Set.range f ⊆ HalfPlaneSet := by
          rintro z ⟨x, rfl⟩
          have hx := (T.chartOverlapModelMap c (toOverlap x)).2
          change f x ∈ c.kind.modelRegion at hx
          rw [hk] at hx
          simpa [ChartKind.modelRegion, HalfPlaneSet] using hx.2
        have hgraph : Set.range G'.graphReplacementMap ⊆ HalfPlaneSet := by
          apply
            IntrinsicTwoComplex.ControlledAdaptiveComplex.range_graphReplacementMap_subset_halfPlane
            T.toIntrinsic U hU f hf (regionSafeControl V f mu)
              (stronglyPositiveOn_regionSafeControl hV hf hmem hmu) G'
          · intro p
            rfl
          · exact hfHalf
        have hhalf : (q y).1.1 ∈ HalfPlaneSet := by
          exact LocallyFiniteTriangleComplex.polygonalReplacementHomeomorph_mem_halfPlane
            G' H hgraph (eU y)
        exact ⟨by
            have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
              hVsub (q y).1.2
            simpa [ChartKind.perturbationRegion, hk] using hyPerturb,
          by simpa [HalfPlaneSet] using hhalf⟩
  let g' : U → c.kind.modelRegion := fun y ↦ ⟨(q y).1.1, hqmodel y⟩
  let g : T.toIntrinsic.realization → S' := fun x ↦
    if hx : x ∈ U then (c.chart.symm (g' ⟨x, hx⟩)).1 else T.embed x
  have hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1 := by
    intro y
    simp [g, y.2]
  have hgoutside : ∀ x, x ∉ U → g x = T.embed x := by
    intro x hx
    simp [g, hx]
  have hgclose : ∀ y : U,
      dist (g' y : Plane)
        (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ≤ mu y := by
    intro y
    change dist (q y).1.1 (f y) ≤ mu y
    have h := hclose (eU y)
    change dist (q y).1.1 (G.map (eU y)) ≤ mu y at h
    rw [hGmap] at h
    exact h
  obtain ⟨hgmatch, hcross⟩ := hmatch g' g hgval hgclose
  have hgcont : ContinuousOn g U := by
    have hg'cont : Continuous g' := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_subtype_val.comp q.continuous))
    have hcomp : Continuous (fun y : U ↦ (c.chart.symm (g' y)).1) :=
      continuous_subtype_val.comp (c.chart.symm.continuous.comp hg'cont)
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcomp.congr fun y ↦ (hgval y).symm
  have hginj : Set.InjOn g U := by
    intro x hx y hy hxy
    let xU : U := ⟨x, hx⟩
    let yU : U := ⟨y, hy⟩
    have hchart : c.chart.symm (g' xU) = c.chart.symm (g' yU) := by
      apply Subtype.ext
      rw [← hgval xU, ← hgval yU]
      exact hxy
    have hg'eq : g' xU = g' yU := c.chart.symm.injective hchart
    have hqeq : q xU = q yU := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : c.kind.modelRegion => (z : Plane)) hg'eq
    exact congrArg Subtype.val (q.injective hqeq)
  have hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed) :=
    isEmbedding_frontierGlue_of_matches hU hgcont T.isEmbedding.continuous
      hgmatch hginj T.isEmbedding.injective hcross
  exact ⟨Q, A, g', g, fun _ ↦ rfl, hqzero, hgval, hgoutside, hgmatch, hgcont,
    hginj, hcross, hembed⟩

/-- Straighten the old complex in a chart while fixing every source point whose old image lies
in a prescribed closed protected set.  The perturbation region is obtained by deleting the
protected chart trace; closedness of the full overlap embedding makes the restricted trace
closed in that new open region. -/
theorem exists_straightenedChartAway
    {S' : Type*} [TopologicalSpace S'] [T2Space S'] [CompactSpace S']
    [SecondCountableTopology S']
    [ChartedSpace (EuclideanHalfSpace 2) S']
    (T : PartialTriangulation S') (c : MoiseChart S')
    (hc : c.BoundaryFaithful)
    (hboundary : T.BoundaryFacewiseRegular)
    (A : Set S') (hA : IsClosed A) :
    ∃ (U : Set T.toIntrinsic.realization) (_ : IsOpen U)
      (V : Set Plane) (_ : IsOpen V)
      (Q : PolygonalReplacementPresentation U V)
      (_ : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
      (g' : U → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S'),
      V ⊆ c.kind.perturbationRegion ∧
      (∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
        (c.chart.symm z).1 ∈ A) ∧
      (∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
        T.chartOverlapMap c y ∉ V) ∧
      (∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ A) ∧
      (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      (∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
        (Q.sourceHomeomorph y).1.1 0 = 0 ↔
          T.embed y.1 ∈
            (modelWithCornersEuclideanHalfSpace 2).boundary S') ∧
      U ⊆ T.chartOverlap c ∧
      (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
      (∀ x, T.embed x ∈ A → g x = T.embed x) ∧
      MatchesAtFrontier U g T.embed ∧
      ContinuousOn g U ∧
      Set.InjOn g U ∧
      Disjoint (g '' U) (T.embed '' Uᶜ) ∧
      _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
  classical
  let O : Set T.toIntrinsic.realization := T.chartOverlap c
  let F : O → c.kind.perturbationRegion :=
    T.chartOverlapPerturbationMap c
  let B : Set O := {y | T.embed y.1 ∈ A}
  have hBclosed : IsClosed B := by
    exact hA.preimage
      (T.isEmbedding.continuous.comp continuous_subtype_val)
  let K : Set c.kind.perturbationRegion := F '' B
  have hKclosed : IsClosed K := by
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosedMap B hBclosed
  let V : Set Plane := Subtype.val '' Kᶜ
  have hV : IsOpen V := by
    exact c.kind.isOpen_perturbationRegion.isOpenEmbedding_subtypeVal.isOpenMap
      Kᶜ hKclosed.isOpen_compl
  have hVsub : V ⊆ c.kind.perturbationRegion := by
    rintro z ⟨w, -, rfl⟩
    exact w.2
  have hVavoid : ∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
      (c.chart.symm z).1 ∈ A := by
    intro z hzV
    let zPert : c.kind.perturbationRegion :=
      c.kind.modelToPerturbation z
    have hzK : zPert ∈ K := by
      by_contra hzK
      apply hzV
      exact ⟨zPert, hzK, rfl⟩
    obtain ⟨y, hyB, hFy⟩ := hzK
    have hmodel : T.chartOverlapModelMap c y = z := by
      apply c.kind.isClosedEmbedding_modelToPerturbation.injective
      exact hFy
    have hsurface : T.embed y.1 = (c.chart.symm z).1 := by
      calc
        T.embed y.1 =
            (c.chart.symm (T.chartOverlapModelMap c y)).1 := by
          symm
          exact congrArg Subtype.val
            (c.chart.symm_apply_apply (T.chartOverlapToDomain c y))
        _ = (c.chart.symm z).1 :=
          congrArg (fun w : c.kind.modelRegion ↦ (c.chart.symm w).1) hmodel
    rw [← hsurface]
    exact hyB
  have hVprotected : ∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
      T.chartOverlapMap c y ∉ V := by
    intro y hyA hyV
    obtain ⟨z, hzNotK, hzval⟩ := hyV
    have hFy : F y = z := by
      apply Subtype.ext
      exact hzval.symm
    apply hzNotK
    rw [← hFy]
    exact ⟨y, hyA, rfl⟩
  let U : Set T.toIntrinsic.realization := Subtype.val '' Bᶜ
  have hU : IsOpen U := by
    exact (T.isOpen_chartOverlap c).isOpenEmbedding_subtypeVal.isOpenMap
      Bᶜ hBclosed.isOpen_compl
  have hsub : U ⊆ T.chartOverlap c := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hUprotected : ∀ y : T.chartOverlap c, y.1 ∉ U →
      T.embed y.1 ∈ A := by
    intro y hyU
    by_contra hyA
    apply hyU
    exact ⟨y, hyA, rfl⟩
  have hmem : ∀ x : U,
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V := by
    intro x
    rcases x.2 with ⟨y, hyB, hyx⟩
    have hyval : y.1 = x.1 := hyx
    have hnotK : F y ∈ Kᶜ := by
      intro hyK
      rcases hyK with ⟨b, hbB, hFb⟩
      have hyb : y = b :=
        (T.isClosedEmbedding_chartOverlapPerturbationMap c).injective
          (by simpa [F] using hFb.symm)
      exact hyB (hyb ▸ hbB)
    refine ⟨F y, hnotK, ?_⟩
    change (F y : Plane) =
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩
    change T.chartOverlapMap c y =
      T.chartOverlapMap c ⟨x.1, hsub x.2⟩
    congr 1
    exact Subtype.ext hyval
  let fV : U → V := fun x ↦
    ⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩
  have hfVembed : _root_.Topology.IsEmbedding fV := by
    apply (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
    have hinc : _root_.Topology.IsEmbedding
        (Set.inclusion hsub : U → T.chartOverlap c) :=
      _root_.Topology.IsEmbedding.inclusion hsub
    have hcomp := (T.isEmbedding_chartOverlapMap c).comp hinc
    simpa [fV, Function.comp_def] using hcomp
  let j : V → c.kind.perturbationRegion :=
    fun z ↦ ⟨z.1, hVsub z.2⟩
  have hjcont : Continuous j :=
    Continuous.subtype_mk continuous_subtype_val _
  have hrange : Set.range fV = j ⁻¹' Set.range F := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨x.1, hsub x.2⟩, ?_⟩
      apply Subtype.ext
      rfl
    · rintro ⟨y, hyF⟩
      have hyPlane : (F y : Plane) = z.1 :=
        congrArg Subtype.val hyF
      have hyNotB : y ∈ Bᶜ := by
        intro hyB
        have hjK : j z ∈ K := ⟨y, hyB, hyF⟩
        rcases z.2 with ⟨w, hwNotK, hwz⟩
        have hwEq : w = j z := by
          apply Subtype.ext
          exact hwz
        exact hwNotK (hwEq ▸ hjK)
      let x : U := ⟨y.1, ⟨y, hyNotB, rfl⟩⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hyPlane
  have hfVclosed : _root_.Topology.IsClosedEmbedding fV := by
    refine ⟨hfVembed, ?_⟩
    rw [hrange]
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosed_range.preimage
      hjcont
  obtain ⟨Q, Qatlas, g', g, hgcoord, hqzero, hgval, hgoutside, hgmatch, hgcont,
      hginj, hcross, hembed⟩ :=
    exists_straightenedChartOpen T c hc hboundary U hU hsub V hV hVsub hmem
      hfVclosed
  have hgfix : ∀ x, T.embed x ∈ A → g x = T.embed x := by
    intro x hxA
    apply hgoutside x
    rintro ⟨y, hyNotB, hyx⟩
    have hyval : y.1 = x := hyx
    apply hyNotB
    change T.embed y.1 ∈ A
    rw [hyval]
    exact hxA
  exact ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
    hUprotected, hgcoord, hqzero, hsub, hgval, hgfix, hgmatch, hgcont, hginj,
    hcross, hembed⟩

end PartialTriangulation

open PartialTriangulation.RelativeSynchronizedTarget

/-- **Theorem boundary** (Moise Thm. 7.6 for partial triangulations).

Two partial triangulations presented on a common vertex type, whose embeddings agree exactly on
the shared part of their realizations (`hagree` and `hsep` together say the images meet only
where the barycentric points coincide), glue to a single partial triangulation on the union face
family, supported on the union of the two images.

The realization of the union family is the set-union of the two realizations, so the glued
embedding is the pasting of the two embeddings along a closed common part; it is a continuous
injection from a compact space into a Hausdorff space, hence an embedding.  The edge-face count
hypothesis is passed through to the glued complex.  The conclusion retains an equivalence from
the glued vertex type to `V` under which its face family relabels to `F₁ ∪ F₂`, so later incidence
certificates can use the two source-family proofs without reconstructing provenance from the
embedding. -/
theorem PartialTriangulation.exists_glued {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (V : Type) [Fintype V] [DecidableEq V]
    (F₁ F₂ : Finset (Finset V))
    (hcard : ∀ t ∈ F₁ ∪ F₂, t.card = 3)
    (e₁ : GeometricRealization V F₁ → S) (e₂ : GeometricRealization V F₂ → S)
    (he₁ : _root_.Topology.IsEmbedding e₁) (he₂ : _root_.Topology.IsEmbedding e₂)
    (hagree : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y)
    (hsep : ∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
      e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ))
    (hboundary₁ : BoundaryFacewiseRegularEmbedding F₁ e₁)
    (hboundary₂ : BoundaryFacewiseRegularEmbedding F₂ e₂) :
    ∃ T' : PartialTriangulation S,
      ∃ vertexEquiv : T'.Vertex ≃ V,
      Moise.relabelFaceFamily vertexEquiv.toEmbedding T'.faces = F₁ ∪ F₂ ∧
      T'.support = Set.range e₁ ∪ Set.range e₂ ∧
      (∀ e ∈ T'.edges, (T'.faces.filter fun t => e ⊆ t).card ≤ 2) ∧
      T'.BoundaryFacewiseRegular := by
  classical
  -- the realization of the union family is the union of the realizations
  have hunion : ∀ x : V → ℝ, x ∈ GeometricRealization V (F₁ ∪ F₂) ↔
      x ∈ GeometricRealization V F₁ ∨ x ∈ GeometricRealization V F₂ := by
    intro x
    simp only [GeometricRealization, Set.mem_ofPred_eq, Finset.mem_union]
    constructor
    · rintro ⟨hstd, t, ht | ht, hsupp⟩
      · exact Or.inl ⟨hstd, t, ht, hsupp⟩
      · exact Or.inr ⟨hstd, t, ht, hsupp⟩
    · rintro (⟨hstd, t, ht, hsupp⟩ | ⟨hstd, t, ht, hsupp⟩)
      · exact ⟨hstd, t, Or.inl ht, hsupp⟩
      · exact ⟨hstd, t, Or.inr ht, hsupp⟩
  -- the pasted embedding
  have hmem₂ : ∀ x : GeometricRealization V (F₁ ∪ F₂),
      (x : V → ℝ) ∉ GeometricRealization V F₁ → (x : V → ℝ) ∈ GeometricRealization V F₂ :=
    fun x hx => ((hunion x.1).mp x.2).resolve_left hx
  set glue : GeometricRealization V (F₁ ∪ F₂) → S := fun x =>
    if hx : (x : V → ℝ) ∈ GeometricRealization V F₁ then e₁ ⟨x.1, hx⟩
    else e₂ ⟨x.1, hmem₂ x hx⟩ with hglue
  -- the glued value is independent of the side used
  have hglue_left : ∀ (x : GeometricRealization V (F₁ ∪ F₂))
      (hx : (x : V → ℝ) ∈ GeometricRealization V F₁), glue x = e₁ ⟨x.1, hx⟩ := by
    intro x hx
    simp [hglue, hx]
  have hglue_right : ∀ (x : GeometricRealization V (F₁ ∪ F₂))
      (hx : (x : V → ℝ) ∈ GeometricRealization V F₂), glue x = e₂ ⟨x.1, hx⟩ := by
    intro x hx
    by_cases hx₁ : (x : V → ℝ) ∈ GeometricRealization V F₁
    · rw [hglue_left x hx₁]
      exact hagree ⟨x.1, hx₁⟩ ⟨x.1, hx⟩ rfl
    · simp [hglue, hx₁]
  -- injectivity
  have hinj : Function.Injective glue := by
    intro x y hxy
    apply Subtype.ext
    by_cases hx : (x : V → ℝ) ∈ GeometricRealization V F₁ <;>
      by_cases hy : (y : V → ℝ) ∈ GeometricRealization V F₁
    · rw [hglue_left x hx, hglue_left y hy] at hxy
      exact Subtype.mk_eq_mk.mp (he₁.injective hxy)
    · rw [hglue_left x hx, hglue_right y (hmem₂ y hy)] at hxy
      exact hsep ⟨x.1, hx⟩ ⟨y.1, hmem₂ y hy⟩ hxy
    · rw [hglue_right x (hmem₂ x hx), hglue_left y hy] at hxy
      exact (hsep ⟨y.1, hy⟩ ⟨x.1, hmem₂ x hx⟩ hxy.symm).symm
    · rw [hglue_right x (hmem₂ x hx), hglue_right y (hmem₂ y hy)] at hxy
      exact Subtype.mk_eq_mk.mp (he₂.injective hxy)
  -- continuity via closed preimages: both restriction inclusions have compact images
  have hcont : Continuous glue := by
    rw [continuous_iff_isClosed]
    intro C hC
    -- describe the preimage as a union of two compact images
    have hdesc : glue ⁻¹' C =
        ((fun z : GeometricRealization V F₁ =>
          (⟨z.1, (hunion z.1).mpr (Or.inl z.2)⟩ : GeometricRealization V (F₁ ∪ F₂))) ''
            (e₁ ⁻¹' C)) ∪
        ((fun z : GeometricRealization V F₂ =>
          (⟨z.1, (hunion z.1).mpr (Or.inr z.2)⟩ : GeometricRealization V (F₁ ∪ F₂))) ''
            (e₂ ⁻¹' C)) := by
      ext x
      constructor
      · intro hx
        by_cases hx₁ : (x : V → ℝ) ∈ GeometricRealization V F₁
        · refine Or.inl ⟨⟨x.1, hx₁⟩, ?_, Subtype.ext rfl⟩
          rw [Set.mem_preimage, ← hglue_left x hx₁]
          exact hx
        · refine Or.inr ⟨⟨x.1, hmem₂ x hx₁⟩, ?_, Subtype.ext rfl⟩
          rw [Set.mem_preimage, ← hglue_right x (hmem₂ x hx₁)]
          exact hx
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · change glue _ ∈ C
          rw [hglue_left _ z.2]
          exact hz
        · change glue _ ∈ C
          rw [hglue_right _ z.2]
          exact hz
    rw [hdesc]
    have hcompact : ∀ (F : Finset (Finset V)) (e : GeometricRealization V F → S)
        (he : _root_.Topology.IsEmbedding e)
        (ι : GeometricRealization V F → GeometricRealization V (F₁ ∪ F₂))
        (hι : Continuous ι),
        IsCompact (ι '' (e ⁻¹' C)) := by
      intro F e he ι hιc
      exact ((hC.preimage he.continuous).isCompact).image hιc
    refine IsClosed.union ?_ ?_
    · exact (hcompact F₁ e₁ he₁ _
        (Continuous.subtype_mk continuous_subtype_val _)).isClosed
    · exact (hcompact F₂ e₂ he₂ _
        (Continuous.subtype_mk continuous_subtype_val _)).isClosed
  -- assemble the glued partial triangulation
  refine ⟨{ Vertex := V, faces := F₁ ∪ F₂, faces_card := hcard, embed := glue,
            isEmbedding := ?_ }, Equiv.refl V, ?_, ?_, ?_, ?_⟩
  · exact (hcont.isClosedEmbedding hinj).isEmbedding
  · simp [Moise.relabelFaceFamily]
  · -- the support is the union of the two images
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      by_cases hx : (x : V → ℝ) ∈ GeometricRealization V F₁
      · exact Or.inl ⟨⟨x.1, hx⟩, (hglue_left x hx).symm⟩
      · exact Or.inr ⟨⟨x.1, hmem₂ x hx⟩, (hglue_right x (hmem₂ x hx)).symm⟩
    · rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨⟨x.1, (hunion x.1).mpr (Or.inl x.2)⟩, hglue_left _ x.2⟩
      · exact ⟨⟨x.1, (hunion x.1).mpr (Or.inr x.2)⟩, hglue_right _ x.2⟩
  · -- An embedded triangle family in a surface automatically has edge valence at most two.
    intro e he
    apply edge_valence_le_two_of_isEmbedding (F₁ ∪ F₂) hcard glue
      ((hcont.isClosedEmbedding hinj).isEmbedding) e
    rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
    exact (Finset.mem_powersetCard.mp het).2
  · intro t ht
    rcases Finset.mem_union.mp ht with ht₁ | ht₂
    · obtain ⟨b, hbt, hbcard, hb⟩ := hboundary₁ t ht₁
      refine ⟨b, hbt, hbcard, ?_⟩
      intro x hxt
      have hxt' : ∀ v ∉ t, x.1 v = 0 := hxt
      let x₁ : GeometricRealization V F₁ :=
        ⟨x.1, x.2.1, t, ht₁, hxt'⟩
      change glue x ∈
          (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        ∀ v ∉ b, x.1 v = 0
      rw [hglue_left x x₁.2]
      exact hb x₁ hxt'
    · obtain ⟨b, hbt, hbcard, hb⟩ := hboundary₂ t ht₂
      refine ⟨b, hbt, hbcard, ?_⟩
      intro x hxt
      have hxt' : ∀ v ∉ t, x.1 v = 0 := hxt
      let x₂ : GeometricRealization V F₂ :=
        ⟨x.1, x.2.1, t, ht₂, hxt'⟩
      change glue x ∈
          (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        ∀ v ∉ b, x.1 v = 0
      rw [hglue_right x x₂.2]
      exact hb x₂ hxt'

/-- A glued partial triangulation is dual-connected once both source families are dual-connected
and one source face on each side shares an edge in the union family. -/
theorem PartialTriangulation.isDualConnected_of_faces_eq_union
    {S : Type*} [TopologicalSpace S] (T : PartialTriangulation S)
    {F₁ F₂ : Finset (Finset T.Vertex)} (hfaces : T.faces = F₁ ∪ F₂)
    (hdual₁ : TriangleFamily.IsDualConnected F₁)
    (hdual₂ : TriangleFamily.IsDualConnected F₂)
    (hcross : TriangleFamily.HasCrossEdge F₁ F₂) :
    T.IsDualConnected := by
  change TriangleFamily.IsDualConnected T.faces
  rw [hfaces]
  exact TriangleFamily.isDualConnected_union_of_hasCrossEdge hdual₁ hdual₂ hcross

/-- The invariant carried through the bordered Radó induction: every edge of the built complex
lies in at most two faces, every triangle has a regular exposed intersection with the ambient
manifold boundary, and the region `A` absorbed so far lies in the topological interior of its
support in `S`.

For a surface without boundary this agrees with Moise Ch. 8, Thm. 3, invariant (4), after the
usual identification of topological and combinatorial interior.  The ambient topological
interior is essential in the bordered case: a half-disk core contains points of `∂S`, and those
points belong to the interior of a half-disk neighborhood *as a subset of `S`*, although they lie
on its combinatorial boundary.  Requiring such points to lie in a combinatorial-interior subset
would make the bordered induction statement false.

This deliberately does not call the intermediate support a combinatorial manifold: edge valence
alone does not imply connected vertex links.  The crossing construction needs the stated
edge/boundary regularity and exact embedded gluing; after the final support is all of `S`, the
homeomorphism to `S` supplies the topological surface conclusion directly. -/
structure RadoInvariant {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (T : PartialTriangulation S) (A : Set S) : Prop where
  /-- The finitely many absorbed chart cores form a compact set.  This is needed to choose the
  finite collars and positive separation scales in the induction step. -/
  coresCompact : IsCompact A
  combSurface : ∀ e ∈ T.edges, (T.faces.filter fun t => e ⊆ t).card ≤ 2
  /-- Every triangle meets the ambient manifold boundary in one exposed simplicial face. -/
  boundaryFacewiseRegular : T.BoundaryFacewiseRegular
  coresInside : A ⊆ interior T.support

theorem RadoInvariant.coresCovered {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    A ⊆ T.support :=
  hT.coresInside.trans interior_subset

/-- The already absorbed compact set has a closed buffer still lying in the ambient interior of
the old support.  Protecting this whole buffer during chart straightening, rather than merely
protecting `A` pointwise, makes preservation of the Radó interior invariant immediate. -/
theorem RadoInvariant.exists_closedBuffer {S : Type*} [TopologicalSpace S]
    [T2Space S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {T : PartialTriangulation S} {A : Set S} (hT : RadoInvariant T A) :
    ∃ C : Set S,
      IsClosed C ∧ A ⊆ interior C ∧ C ⊆ interior T.support := by
  obtain ⟨V, hVopen, hAV, hclosure⟩ :=
    hT.coresCompact.exists_isOpen_closure_subset
      (isOpen_interior.mem_nhdsSet.mpr hT.coresInside)
  refine ⟨closure V, isClosed_closure, ?_, hclosure⟩
  calc
    A ⊆ V := hAV
    _ = interior V := hVopen.interior_eq.symm
    _ ⊆ interior (closure V) := interior_mono subset_closure

/-- Enlarge the recorded absorbed set without changing the triangulation when the added set is
already in the interior of its support. -/
theorem RadoInvariant.absorb_of_subset {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {T : PartialTriangulation S} {A B : Set S} (hT : RadoInvariant T A)
    (hBcompact : IsCompact B) (hB : B ⊆ interior T.support) :
    RadoInvariant T (A ∪ B) where
  coresCompact := hT.coresCompact.union hBcompact
  combSurface := hT.combSurface
  boundaryFacewiseRegular := hT.boundaryFacewiseRegular
  coresInside := Set.union_subset hT.coresInside hB

/-- A single chart has a concrete finite partial triangulation satisfying the bordered Rado
invariant.  This is the honest nonempty base patch used by the induction step. -/
theorem radoInvariant_chartPatch {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (c : MoiseChart S) (hc : c.BoundaryFaithful) :
    RadoInvariant c.patchPartialTriangulation c.core where
  coresCompact := c.isCompact_core
  combSurface := by
    intro e he
    have hecard := c.patchPartialTriangulation.card_of_mem_edges he
    change (c.kind.patchComplex.cells.filter fun t => e ⊆ t).card ≤ 2
    exact c.kind.patchComplex_edge_valence e hecard
  boundaryFacewiseRegular := c.patchPartialTriangulation_boundaryFacewiseRegular hc
  coresInside := c.core_subset_interior_patchPartialTriangulation_support

/-- If the fixed patch of the new chart already contains the previously absorbed region in its
ambient interior, that patch alone is a valid next induction stage. -/
theorem radoInvariant_chartPatch_absorb {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (c : MoiseChart S) (hc : c.BoundaryFaithful)
    {A : Set S} (hAcompact : IsCompact A)
    (hA : A ⊆ interior c.patchPartialTriangulation.support) :
    RadoInvariant c.patchPartialTriangulation (A ∪ c.core) :=
  by simpa [Set.union_comm] using
    (radoInvariant_chartPatch c hc).absorb_of_subset hAcompact hA

/-- The empty partial triangulation satisfies the invariant for the empty region: the base case
of the Radó induction. -/
theorem radoInvariant_empty (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] :
    RadoInvariant (PartialTriangulation.empty S) ∅ where
  coresCompact := isCompact_empty
  combSurface := by
    intro e he
    simp only [PartialTriangulation.edges, PartialTriangulation.empty] at he
    exact absurd he (Finset.notMem_empty e)
  boundaryFacewiseRegular := by
    intro t ht
    have ht' :
        t ∈ (∅ :
          Finset (Finset (PartialTriangulation.empty S).Vertex)) := ht
    exact (Finset.notMem_empty t ht').elim
  coresInside := Set.empty_subset _

section EvalHypotheses

variable (S : Type*) [TopologicalSpace S]
variable [T2Space S] [ConnectedSpace S] [CompactSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]
variable [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]

omit [T2Space S] [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- A compact Eval surface has a finite cover by interiors of boundary-faithful Moise chart
cores.  Because the ambient surface is connected, the graph joining two cores when their
interiors overlap is connected as well. -/
theorem moise_finite_chart_open_cover :
    ∃ (m : ℕ) (charts : Fin m → MoiseChart S),
      (⋃ i, interior (charts i).core) = Set.univ ∧
      (∀ i, (charts i).BoundaryFaithful) ∧
      ∀ i j, Relation.TransGen
        (fun a b : Fin m =>
          (interior (charts a).core ∩ interior (charts b).core).Nonempty)
        i j := by
  classical
  choose c hfaithful hcore using exists_moiseChart_core_mem_nhds S
  have hcover : (Set.univ : Set S) ⊆ ⋃ x : S, interior (c x).core := by
    intro x _
    exact Set.mem_iUnion.mpr
      ⟨x, mem_interior_iff_mem_nhds.mpr (hcore x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S => interior (c x).core) (fun _ => isOpen_interior) hcover
  obtain ⟨m, e⟩ := Finite.exists_equiv_fin t
  let e' := Classical.choice e
  let charts : Fin m → MoiseChart S := fun i => c (e'.symm i).1
  have hopen : (⋃ i, interior (charts i).core) = (Set.univ : Set S) := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with
      ⟨y, hyt, hxy⟩
    exact Set.mem_iUnion.mpr ⟨e' ⟨y, hyt⟩, by
      simpa [charts] using hxy⟩
  have hnonempty (i : Fin m) :
      (interior (charts i).core).Nonempty := by
    refine ⟨(e'.symm i).1, ?_⟩
    exact mem_interior_iff_mem_nhds.mpr (hcore (e'.symm i).1)
  refine ⟨m, charts, hopen, ?_, ?_⟩
  · intro i
    exact hfaithful (e'.symm i).1
  · have hpreconnected :
        IsPreconnected (⋃ i, interior (charts i).core) := by
      rw [hopen]
      exact isPreconnected_univ
    intro i j
    exact hpreconnected.transGen_of_iUnion
      (fun _ => isOpen_interior) i j (hnonempty i) (hnonempty j)

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- A compact Eval surface has a finite cover by boundary-faithful Moise chart cores (Moise
Ch. 8, Thm. 1, plus compactness).  Proved by a finite subcover of the core interiors from the
local chart extraction (`exists_moiseChart_core_mem_nhds`, `Moise/ChartExtraction.lean`). -/
theorem moise_finite_chart_cover :
    ∃ (m : ℕ) (charts : Fin m → MoiseChart S),
      (⋃ i, (charts i).core) = Set.univ ∧
      ∀ i, (charts i).BoundaryFaithful := by
  classical
  choose c hfaithful hcore using exists_moiseChart_core_mem_nhds S
  have hcover : (Set.univ : Set S) ⊆ ⋃ x : S, interior (c x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hcore x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S => interior (c x).core) (fun x => isOpen_interior) hcover
  obtain ⟨m, e⟩ := Finite.exists_equiv_fin t
  let e' := Classical.choice e
  refine ⟨m, fun i => c (e'.symm i).1, ?_, fun i => hfaithful (e'.symm i).1⟩
  apply Set.eq_univ_of_univ_subset
  intro x hx
  rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with ⟨y, hyt, hxy⟩
  exact Set.mem_iUnion.mpr ⟨e' ⟨y, hyt⟩, by
    simpa using interior_subset hxy⟩

omit [T2Space S] [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- Compact Eval surfaces are second countable.  We derive this from the finite Moise chart
cover instead of asking typeclass search to infer second countability of the half-space model:
each chart domain is homeomorphic to a second-countable disk or half-disk, and finitely many
open chart domains cover the surface. -/
theorem moise_secondCountableTopology : SecondCountableTopology S := by
  obtain ⟨m, charts, hcover, _⟩ := moise_finite_chart_cover S
  let U : Fin m → Set S := fun i ↦ (charts i).domain
  have : ∀ i, SecondCountableTopology (U i) :=
    fun i ↦ (charts i).chart.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · exact fun i ↦ (charts i).isOpen_domain
  · apply Set.eq_univ_of_univ_subset
    intro x _
    rw [← hcover] at *
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (show x ∈ ⋃ i, (charts i).core from ‹_›)
    exact Set.mem_iUnion.mpr ⟨i, (charts i).core_subset_domain hi⟩

/-- Two embeddings of the same source preserve the ambient manifold-boundary stratum
pointwise.  This is the exact relative certificate needed by the crossing weld. -/
def PreservesManifoldBoundary {X : Type*} (f g : X → S) : Prop :=
  ∀ x,
    f x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
      g x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S

/-- The raw chart straightening, augmented only with the certificate that its frontier-glued
embedding preserves ambient boundary membership.  The crossing-weld implementation consumes this
proposition to retain the boundary-line subcomplex during the bordered induction. -/
def PartialTriangulation.BoundaryPreservingStraightening
    (T : PartialTriangulation S) (c : MoiseChart S) : Prop :=
  ∀ (A : Set S), IsClosed A →
    ∃ (U : Set T.toIntrinsic.realization) (_ : IsOpen U)
      (V : Set Plane) (_ : IsOpen V)
      (Q : PolygonalReplacementPresentation U V)
      (_ : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
      (g' : U → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S),
      V ⊆ c.kind.perturbationRegion ∧
      (∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
        (c.chart.symm z).1 ∈ A) ∧
      (∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
        T.chartOverlapMap c y ∉ V) ∧
      (∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ A) ∧
      (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      U ⊆ T.chartOverlap c ∧
      (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
      (∀ x, T.embed x ∈ A → g x = T.embed x) ∧
      MatchesAtFrontier U g T.embed ∧
      ContinuousOn g U ∧
      Set.InjOn g U ∧
      Disjoint (g '' U) (T.embed '' Uᶜ) ∧
      _root_.Topology.IsEmbedding (frontierGlue U g T.embed) ∧
      PreservesManifoldBoundary S
        (frontierGlue U g T.embed) T.embed

omit [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- The relative polygonal straightening preserves the ambient boundary stratum. -/
theorem PartialTriangulation.exists_boundaryPreservingStraightening
    (T : PartialTriangulation S) (c : MoiseChart S) (hc : c.BoundaryFaithful)
    (hboundary : T.BoundaryFacewiseRegular) :
    PartialTriangulation.BoundaryPreservingStraightening S T c := by
  let : SecondCountableTopology S := moise_secondCountableTopology S
  intro A hA
  obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
      hUprotected, hgcoord, hqzero, hUsub, hgval, hgfix, hgmatch, hgcont, hginj,
      hcross, hembed⟩ :=
    T.exists_straightenedChartAway c hc hboundary A hA
  refine ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
    hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
    hembed, ?_⟩
  intro y
  by_cases hyU : y ∈ U
  · let yU : U := ⟨y, hyU⟩
    rw [frontierGlue_of_mem hyU, hgval yU]
    by_cases hk : c.kind = ChartKind.disk
    · constructor
      · exact fun hy ↦ False.elim
          ((hc.1 hk (c.chart.symm (g' yU)).1
            (c.chart.symm (g' yU)).2) hy)
      · exact fun hy ↦ False.elim
          ((hc.1 hk (T.embed y) (hUsub hyU)) hy)
    · have hkHalf : c.kind = ChartKind.halfDisk := by
        cases hkind : c.kind
        · exact (hk hkind).elim
        · rfl
      have hnew :
          (c.chart.symm (g' yU)).1 ∈
              (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
            (g' yU : Plane) 0 = 0 := by
        have h :=
          hc.2 hkHalf (c.chart.symm (g' yU)).1
            (c.chart.symm (g' yU)).2
        have happly := c.chart.apply_symm_apply (g' yU)
        have hplane :=
          congrArg (fun z : c.kind.modelRegion ↦ (z : Plane)) happly
        rw [hplane] at h
        exact h
      calc
        (c.chart.symm (g' yU)).1 ∈
              (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
            (g' yU : Plane) 0 = 0 := hnew
        _ ↔ (Q.sourceHomeomorph yU).1.1 0 = 0 := by
          rw [hgcoord yU]
        _ ↔ T.embed y ∈
              (modelWithCornersEuclideanHalfSpace 2).boundary S :=
          hqzero hkHalf yU
  · rw [frontierGlue_of_notMem hyU]

omit [ConnectedSpace S]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] in
/-- The controlled locally finite polygonal replacement on the full chart overlap assembles
with the unchanged old embedding across the overlap frontier.

This is the analytic half of Moise's crossing step.  The replacement stays in the chart model
(including the closed half-plane in the bordered case), converges to the old embedding at the
frontier, and is disjoint from the unchanged image outside the overlap.  Consequently the
frontier paste is again an embedding of the original finite intrinsic complex. -/
theorem PartialTriangulation.exists_straightenedChartOverlap
    (T : PartialTriangulation S) (c : MoiseChart S) :
    ∃ (Q : PolygonalReplacementPresentation (T.chartOverlap c)
        c.kind.perturbationRegion)
      (_ : PolygonalReplacementSourceAtlas T.toIntrinsic (T.chartOverlap c)
        c.kind.perturbationRegion Q)
      (g' : T.chartOverlap c → c.kind.modelRegion)
      (g : T.toIntrinsic.realization → S),
      (∀ y : T.chartOverlap c,
        (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
      (∀ y : T.chartOverlap c, g y.1 = (c.chart.symm (g' y)).1) ∧
      MatchesAtFrontier (T.chartOverlap c) g T.embed ∧
      ContinuousOn g (T.chartOverlap c) ∧
      Set.InjOn g (T.chartOverlap c) ∧
      Disjoint (g '' T.chartOverlap c) (T.embed '' (T.chartOverlap c)ᶜ) ∧
      _root_.Topology.IsEmbedding
        (frontierGlue (T.chartOverlap c) g T.embed) := by
  let : SecondCountableTopology S := moise_secondCountableTopology S
  classical
  let U : Set T.toIntrinsic.realization := T.chartOverlap c
  let hU : IsOpen U := T.isOpen_chartOverlap c
  let f : U → Plane := T.chartOverlapMap c
  let hf : Continuous f := (T.isEmbedding_chartOverlapMap c).continuous
  let V : Set Plane := c.kind.perturbationRegion
  let hV : IsOpen V := c.kind.isOpen_perturbationRegion
  have hmem : ∀ x : U, f x ∈ V := by
    intro x
    exact c.kind.modelRegion_subset_perturbationRegion
      (T.chartOverlapModelMap c x).2
  obtain ⟨mu, hmu, hmatch⟩ := T.exists_chartMatchingControl c
  let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
    (regionSafeControl V f mu)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
  let : T.toIntrinsic.AdaptiveSafety U := C₀.safety
  let : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
      (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
  let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
  have hRsupport : R.support = Set.univ := by
    exact IntrinsicTwoComplex.AdaptiveOpenCover.locallyFiniteTriangleComplex_support
      T.toIntrinsic U
      (T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
        (regionSafeControl V f mu)
        (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)) hU
  let toU : R.support → U := Subtype.val
  have htoUclosed : _root_.Topology.IsClosedEmbedding toU := by
    refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [show Set.range toU = R.support by exact Subtype.range_val, hRsupport]
    exact isClosed_univ
  let fV : R.support → V := fun p ↦ ⟨f p.1, hmem p.1⟩
  have hfVclosed : _root_.Topology.IsClosedEmbedding fV := by
    have heq : fV =
        (c.kind.modelToPerturbation ∘ T.chartOverlapModelMap c) ∘ toU := by
      funext p
      apply Subtype.ext
      rfl
    rw [heq]
    exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).comp htoUclosed
  let G : R.PlaneGraphRealization :=
    LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
      V hV (fun p ↦ f p.1)
      ((T.isEmbedding_chartOverlapMap c).comp
        _root_.Topology.IsEmbedding.subtypeVal)
      (fun p ↦ hmem p.1) hfVclosed.isClosed_range
  have hGmap : ∀ p, G.map p = f p.1 := fun _ ↦ rfl
  have hGregion : G.region = V := rfl
  obtain ⟨vc, hvc, ec, hec, H, hclose⟩ :=
    IntrinsicTwoComplex.RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison
      T.toIntrinsic U hU V hV f hf hmem mu hmu G hGmap hGregion
  let G' := G.withApproximationControls vc hvc ec hec
  let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
  let eU : U ≃ₜ R.support :=
    { toFun := uToSupport
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      continuous_toFun := Continuous.subtype_mk continuous_id _
      continuous_invFun := continuous_subtype_val }
  let q := straightenedChartOpenSourceHomeomorph R G' H hRsupport
  let Q : PolygonalReplacementPresentation U V :=
    straightenedChartOpenPresentation R G' H hRsupport
  let A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q :=
    straightenedChartOpenSourceAtlas T U hU V hV f hf hmem mu hmu G' H hRsupport
  have hqmodel : ∀ y : U, (q y).1.1 ∈ c.kind.modelRegion := by
    intro y
    cases hk : c.kind with
    | disk =>
        have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
          (q y).1.2
        simpa [ChartKind.modelRegion, ChartKind.perturbationRegion, hk] using
          hyPerturb
    | halfDisk =>
        have hfHalf : Set.range f ⊆ HalfPlaneSet := by
          rintro z ⟨x, rfl⟩
          have hx := (T.chartOverlapModelMap c x).2
          change f x ∈ c.kind.modelRegion at hx
          rw [hk] at hx
          simpa [ChartKind.modelRegion, HalfPlaneSet] using hx.2
        have hgraph : Set.range G'.graphReplacementMap ⊆ HalfPlaneSet := by
          apply
            IntrinsicTwoComplex.ControlledAdaptiveComplex.range_graphReplacementMap_subset_halfPlane
            T.toIntrinsic U hU f hf (regionSafeControl V f mu)
              (stronglyPositiveOn_regionSafeControl hV hf hmem hmu) G'
          · intro p
            rfl
          · exact hfHalf
        have hhalf : (q y).1.1 ∈ HalfPlaneSet := by
          exact LocallyFiniteTriangleComplex.polygonalReplacementHomeomorph_mem_halfPlane
            G' H hgraph (eU y)
        exact ⟨by
            exact (q y).1.2,
          by simpa [HalfPlaneSet] using hhalf⟩
  let g' : U → c.kind.modelRegion := fun y ↦ ⟨(q y).1.1, hqmodel y⟩
  let g : T.toIntrinsic.realization → S := fun x ↦
    if hx : x ∈ U then (c.chart.symm (g' ⟨x, hx⟩)).1 else T.embed x
  have hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1 := by
    intro y
    simp [g, y.2]
  have hgclose : ∀ y : U,
      dist (g' y : Plane) (T.chartOverlapMap c y) ≤ mu y := by
    intro y
    change dist (q y).1.1 (f y) ≤ mu y
    have h := hclose (eU y)
    change dist (q y).1.1 (G.map (eU y)) ≤ mu y at h
    rw [hGmap] at h
    exact h
  have hgmatch : MatchesAtFrontier U g T.embed := by
    exact hmatch g' g hgval hgclose
  have hgcont : ContinuousOn g U := by
    have hg'cont : Continuous g' := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp
        (continuous_subtype_val.comp q.continuous))
    have hcomp : Continuous (fun y : U ↦ (c.chart.symm (g' y)).1) :=
      continuous_subtype_val.comp (c.chart.symm.continuous.comp hg'cont)
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcomp.congr fun y ↦ (hgval y).symm
  have hginj : Set.InjOn g U := by
    intro x hx y hy hxy
    let xU : U := ⟨x, hx⟩
    let yU : U := ⟨y, hy⟩
    have hchart : c.chart.symm (g' xU) = c.chart.symm (g' yU) := by
      apply Subtype.ext
      rw [← hgval xU, ← hgval yU]
      exact hxy
    have hg'eq : g' xU = g' yU := c.chart.symm.injective hchart
    have hqeq : q xU = q yU := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : c.kind.modelRegion => (z : Plane)) hg'eq
    exact congrArg Subtype.val (q.injective hqeq)
  have hcross : Disjoint (g '' U) (T.embed '' Uᶜ) := by
    apply T.disjoint_image_chartOverlap_embed_compl c
    intro x hx
    rw [hgval ⟨x, hx⟩]
    exact (c.chart.symm (g' ⟨x, hx⟩)).2
  have hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed) :=
    isEmbedding_frontierGlue_of_matches hU hgcont T.isEmbedding.continuous
      hgmatch hginj T.isEmbedding.injective hcross
  exact ⟨Q, A, g', g, fun _ ↦ rfl, hgval, hgmatch, hgcont, hginj, hcross, hembed⟩

open PartialTriangulation.PolygonalReplacementSourceAtlas

/-- If a convex average lies strictly inside a gap avoided by every positively weighted value,
then some positive weight occurs on each side of the gap.  Keeping this order argument separate
prevents the crossing-weld elaborator from repeatedly reducing its large dependent local types. -/
theorem exists_positive_weight_on_both_sides_of_gap
    {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ) (a b z : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (hzAverage : z = ∑ i, weight i * value i)
    (hgap : ∀ i, 0 < weight i → ¬ value i ∈ Set.Ioo a b)
    (hzGap : z ∈ Set.Ioo a b) :
    (∃ i, 0 < weight i ∧ value i ≤ a) ∧
      ∃ i, 0 < weight i ∧ b ≤ value i := by
  classical
  constructor
  · by_contra hLow
    have hterm (i : ι) : weight i * b ≤ weight i * value i := by
      by_cases hi : weight i = 0
      · simp [hi]
      · have hiPos : 0 < weight i :=
          lt_of_le_of_ne (hweight i) (Ne.symm hi)
        have hiNotLow : ¬ value i ≤ a := by
          intro hiLow
          exact hLow ⟨i, hiPos, hiLow⟩
        have hiAbove : b ≤ value i := by
          apply le_of_not_gt
          intro hiBelow
          exact hgap i hiPos ⟨lt_of_not_ge hiNotLow, hiBelow⟩
        exact mul_le_mul_of_nonneg_left hiAbove (hweight i)
    have hsum : b ≤ ∑ i, weight i * value i := by
      calc
        b = (∑ i, weight i) * b := by rw [hweightSum, one_mul]
        _ = ∑ i, weight i * b := by rw [Finset.sum_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ hterm i
    rw [← hzAverage] at hsum
    exact (not_le_of_gt hzGap.2) hsum
  · by_contra hHigh
    have hterm (i : ι) : weight i * value i ≤ weight i * a := by
      by_cases hi : weight i = 0
      · simp [hi]
      · have hiPos : 0 < weight i :=
          lt_of_le_of_ne (hweight i) (Ne.symm hi)
        have hiNotHigh : ¬ b ≤ value i := by
          intro hiHigh
          exact hHigh ⟨i, hiPos, hiHigh⟩
        have hiBelow : value i ≤ a := by
          apply le_of_not_gt
          intro hiAbove
          exact hgap i hiPos ⟨hiAbove, lt_of_not_ge hiNotHigh⟩
        exact mul_le_mul_of_nonneg_left hiBelow (hweight i)
    have hsum : (∑ i, weight i * value i) ≤ a := by
      calc
        _ ≤ ∑ i, weight i * a :=
          Finset.sum_le_sum fun i _ ↦ hterm i
        _ = (∑ i, weight i) * a := by rw [Finset.sum_mul]
        _ = a := by rw [hweightSum, one_mul]
    rw [← hzAverage] at hsum
    exact (not_le_of_gt hzGap.1) hsum

end EvalHypotheses

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
