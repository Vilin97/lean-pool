/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.AdaptiveOpenCover
import LeanPool.ClassificationOfSurfaces.Moise.HalfPlanePolygon
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteControlledApproximation
import LeanPool.ClassificationOfSurfaces.Moise.FacewiseComparison

/-!
# Adaptive meshes for strongly-positive metric controls

Moise Chapter 6 first subdivides the source until every simplex is small compared with the
prescribed strongly-positive tolerance.  This file supplies that step for the locally finite
adaptive triangulation.  Strong positivity gives a uniform lower bound on a compact
neighborhood of each point; continuity then shrinks that neighborhood until its image has small
diameter.  Subordination to the resulting open cover converts the existing setwise polygonal
graph replacement into a pointwise controlled approximation.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open Filter

/-- A neighborhood on which `phi` has a fixed positive lower bound and the image of `f` has
diameter at most one quarter of that bound. -/
structure ControlledNeighborhood {X : Type*} [TopologicalSpace X]
    (f : X → Plane) (phi : X → ℝ) (x : X) where
  /-- The `set` declaration. -/
  set : Set X
  isOpen : IsOpen set
  mem_set : x ∈ set
  /-- The `scale` declaration. -/
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  scale_le : ∀ y ∈ set, scale ≤ phi y
  dist_le_quarter : ∀ y ∈ set, ∀ z ∈ set,
    dist (f y) (f z) ≤ scale / 4

/-- Strong positivity and local compactness produce controlled neighborhoods for every point. -/
theorem exists_controlledNeighborhood {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {f : X → Plane} (hf : Continuous f)
    {phi : X → ℝ} (hphi : StronglyPositiveOn Set.univ phi) (x : X) :
    Nonempty (ControlledNeighborhood f phi x) := by
  obtain ⟨C, hCcompact, hCnhds⟩ := exists_compact_mem_nhds x
  obtain ⟨eps, heps, heps_le⟩ := hphi C hCcompact (Set.subset_univ C)
  let delta := min eps 1
  have hdelta : 0 < delta := lt_min heps zero_lt_one
  let W : Set X := interior C ∩ f ⁻¹' Metric.ball (f x) (delta / 8)
  have hxInterior : x ∈ interior C := mem_interior_iff_mem_nhds.mpr hCnhds
  have hxBall : f x ∈ Metric.ball (f x) (delta / 8) :=
    Metric.mem_ball_self (by positivity)
  refine ⟨{
    set := W
    isOpen := isOpen_interior.inter (Metric.isOpen_ball.preimage hf)
    mem_set := ⟨hxInterior, hxBall⟩
    scale := delta
    scale_pos := hdelta
    scale_le_one := min_le_right _ _
    scale_le := ?_
    dist_le_quarter := ?_ }⟩
  · intro y hy
    exact (min_le_left eps 1).trans (heps_le y (interior_subset hy.1))
  · intro y hy z hz
    have hyx : dist (f y) (f x) < delta / 8 := Metric.mem_ball.mp hy.2
    have hxz : dist (f x) (f z) < delta / 8 := by
      simpa only [dist_comm] using Metric.mem_ball.mp hz.2
    apply le_of_lt
    calc
      dist (f y) (f z) ≤ dist (f y) (f x) + dist (f x) (f z) :=
        dist_triangle _ _ _
      _ < delta / 8 + delta / 8 := add_lt_add hyx hxz
      _ = delta / 4 := by ring

/-- A chosen controlled neighborhood at every point. -/
noncomputable def controlledNeighborhood {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {f : X → Plane} (hf : Continuous f)
    {phi : X → ℝ} (hphi : StronglyPositiveOn Set.univ phi) (x : X) :
    ControlledNeighborhood f phi x :=
  Classical.choice (exists_controlledNeighborhood hf hphi x)

/-- The part of a mesh tolerance reserved for staying inside an open target region.  When the
region is all of the plane, the constant bound `1` is used instead. -/
noncomputable def regionMeshControl {X : Type*} (V : Set Plane)
    (f : X → Plane) (x : X) : ℝ := by
  classical
  exact if hcomp : Vᶜ.Nonempty then min 1 (frontierDistance V (f x) / 4) else 1

theorem regionMeshControl_le_one {X : Type*} (V : Set Plane)
    (f : X → Plane) (x : X) : regionMeshControl V f x ≤ 1 := by
  by_cases hcomp : Vᶜ.Nonempty
  · simp [regionMeshControl, hcomp]
  · simp [regionMeshControl, hcomp]

theorem regionMeshControl_le_frontier {X : Type*} {V : Set Plane}
    (hcomp : Vᶜ.Nonempty) (f : X → Plane) (x : X) :
    regionMeshControl V f x ≤ frontierDistance V (f x) / 4 := by
  simp [regionMeshControl, hcomp]

/-- The target-region mesh control is strongly positive along any continuous map landing in
that region. -/
theorem stronglyPositiveOn_regionMeshControl {X : Type*} [TopologicalSpace X]
    {V : Set Plane} (hV : IsOpen V) {f : X → Plane} (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) :
    StronglyPositiveOn Set.univ (regionMeshControl V f) := by
  intro C hC _hCU
  by_cases hcomp : Vᶜ.Nonempty
  · have hImageCompact : IsCompact (f '' C) := hC.image hf
    have hImageSubset : f '' C ⊆ V := by
      rintro _ ⟨x, -, rfl⟩
      exact hmem x
    obtain ⟨eps, heps, hepsLe⟩ :=
      stronglyPositiveOn_frontierDistance hV hcomp (f '' C)
        hImageCompact hImageSubset
    let delta := min 1 (eps / 4)
    have hdelta : 0 < delta := lt_min zero_lt_one (div_pos heps (by norm_num))
    refine ⟨delta, hdelta, ?_⟩
    intro x hx
    rw [regionMeshControl]
    simp only [hcomp, ↓reduceDIte]
    dsimp only [delta]
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_right (hepsLe (f x) ⟨x, hx, rfl⟩) (by norm_num)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _hx
    simp [regionMeshControl, hcomp]

/-- Combine a requested approximation tolerance with the target-region mesh control. -/
noncomputable def regionSafeControl {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) : ℝ :=
  min (phi x) (regionMeshControl V f x)

theorem regionSafeControl_le_left {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ phi x := min_le_left _ _

theorem regionSafeControl_le_one {X : Type*} (V : Set Plane)
    (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ 1 :=
  (min_le_right _ _).trans (regionMeshControl_le_one V f x)

theorem regionSafeControl_le_frontier {X : Type*} {V : Set Plane}
    (hcomp : Vᶜ.Nonempty) (f : X → Plane) (phi : X → ℝ) (x : X) :
    regionSafeControl V f phi x ≤ frontierDistance V (f x) / 4 :=
  (min_le_right _ _).trans (regionMeshControl_le_frontier hcomp f x)

/-- A minimum of two strongly-positive controls is strongly positive. -/
theorem StronglyPositiveOn.min_control {X : Type*} [TopologicalSpace X]
    {U : Set X} {phi psi : X → ℝ}
    (hphi : StronglyPositiveOn U phi) (hpsi : StronglyPositiveOn U psi) :
    StronglyPositiveOn U (fun x ↦ min (phi x) (psi x)) := by
  intro C hC hCU
  obtain ⟨eps, heps, hepsLe⟩ := hphi C hC hCU
  obtain ⟨delta, hdelta, hdeltaLe⟩ := hpsi C hC hCU
  refine ⟨min eps delta, lt_min heps hdelta, ?_⟩
  intro x hx
  exact min_le_min (hepsLe x hx) (hdeltaLe x hx)

theorem stronglyPositiveOn_regionSafeControl {X : Type*} [TopologicalSpace X]
    {V : Set Plane} (hV : IsOpen V) {f : X → Plane} (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) {phi : X → ℝ}
    (hphi : StronglyPositiveOn Set.univ phi) :
    StronglyPositiveOn Set.univ (regionSafeControl V f phi) :=
  StronglyPositiveOn.min_control hphi
    (stronglyPositiveOn_regionMeshControl hV hf hmem)

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- The ambient open cover obtained from controlled neighborhoods in the open subspace `U`. -/
noncomputable def controlledAdaptiveOpenCover (hU : IsOpen U)
    (f : U → Plane) (hf : Continuous f) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : K.AdaptiveOpenCover U := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let N : ∀ x : U, ControlledNeighborhood f phi x :=
    fun x ↦ controlledNeighborhood hf hphi x
  exact {
    Index := U
    set := fun x ↦ Subtype.val '' (N x).set
    isOpen := fun x ↦ hU.isOpenEmbedding_subtypeVal.isOpenMap _ (N x).isOpen
    subset := by
      rintro x _ ⟨y, -, rfl⟩
      exact y.2
    covers := by
      intro p hp
      let x : U := ⟨p, hp⟩
      exact ⟨x, ⟨x, (N x).mem_set, rfl⟩⟩ }

namespace ControlledAdaptiveOpenCover

variable (hU : IsOpen U) (f : U → Plane) (hf : Continuous f)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable def N (x : U) : ControlledNeighborhood f phi x := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact controlledNeighborhood hf hphi x

/-- Every selected cover set retains its quantitative scale and image-diameter bounds. -/
theorem cover_set_control (x : U) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      (∀ y : U, y.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        eps ≤ phi y) ∧
      ∀ y z : U,
        y.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        z.1 ∈ (K.controlledAdaptiveOpenCover U hU f hf phi hphi).set x →
        dist (f y) (f z) ≤ eps / 4 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let M := N K U hU f hf phi hphi x
  refine ⟨M.scale, M.scale_pos, M.scale_le_one, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzx : z = y := Subtype.ext hzy
    exact M.scale_le y (hzx ▸ hz)
  · intro y z hy hz
    obtain ⟨y', hy', hy'eq⟩ := hy
    obtain ⟨z', hz', hz'eq⟩ := hz
    have hyy' : y' = y := Subtype.ext hy'eq
    have hzz' : z' = z := Subtype.ext hz'eq
    exact M.dist_le_quarter y (hyy' ▸ hy') z (hzz' ▸ hz')

end ControlledAdaptiveOpenCover

/-- The adaptive locally finite triangle complex subordinate to the quantitative cover. -/
noncomputable abbrev controlledAdaptiveComplex (hU : IsOpen U)
    (f : U → Plane) (hf : Continuous f) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : LocallyFiniteTriangleComplex U :=
  AdaptiveOpenCover.locallyFiniteTriangleComplex K U
    (K.controlledAdaptiveOpenCover U hU f hf phi hphi) hU

/-- The controlled adaptive complex with its tolerance automatically reduced near the frontier
of an open target region. -/
noncomputable abbrev regionControlledAdaptiveComplex (hU : IsOpen U)
    (V : Set Plane) (hV : IsOpen V) (f : U → Plane) (hf : Continuous f)
    (hmem : ∀ x, f x ∈ V) (phi : U → ℝ)
    (hphi : StronglyPositiveOn Set.univ phi) : LocallyFiniteTriangleComplex U :=
  K.controlledAdaptiveComplex U hU f hf (regionSafeControl V f phi)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hphi)

namespace ControlledAdaptiveComplex

variable (hU : IsOpen U) (f : U → Plane) (hf : Continuous f)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable abbrev L : LocallyFiniteTriangleComplex U :=
  K.controlledAdaptiveComplex U hU f hf phi hphi

/-- Each adaptive face inherits one quantitative scale from the cover member containing it. -/
theorem exists_face_scale (t : (L K U hU f hf phi hphi).Face) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      (∀ p ∈ (L K U hU f hf phi hphi).faceCarrier t, eps ≤ phi p) ∧
      ∀ p q : U,
        p ∈ (L K U hU f hf phi hphi).faceCarrier t →
        q ∈ (L K U hU f hf phi hphi).faceCarrier t →
        dist (f p) (f q) ≤ eps / 4 := by
  let C := K.controlledAdaptiveOpenCover U hU f hf phi hphi
  obtain ⟨i, hti⟩ := AdaptiveOpenCover.exists_cover_set_of_complex_face K U C hU t
  obtain ⟨eps, heps, hepsOne, hepsPhi, hepsDist⟩ :=
    ControlledAdaptiveOpenCover.cover_set_control K U hU f hf phi hphi i
  refine ⟨eps, heps, hepsOne, ?_, ?_⟩
  · intro p hp
    exact hepsPhi p (hti ⟨p, hp, rfl⟩)
  · intro p q hp hq
    exact hepsDist p q (hti ⟨p, hp, rfl⟩) (hti ⟨q, hq, rfl⟩)

/-- Subordination makes every edge image small enough for the canonical simultaneous
polygonal replacement to satisfy the original strongly-positive pointwise control. -/
theorem edgeImagesControlled
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    G.EdgeImagesControlled (fun p ↦ phi p.1) := by
  intro e p hp
  let t := (L K U hU f hf phi hphi).edgeFace e
  obtain ⟨eps, heps, -, hepsPhi, hepsDist⟩ :=
    exists_face_scale K U hU f hf phi hphi t
  have hdiam : Metric.diam (G.edgeImage e) ≤ eps / 4 := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro y hy z hz
    obtain ⟨py, hpy, rfl⟩ := hy
    obtain ⟨pz, hpz, rfl⟩ := hz
    have hpyFace : py.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
      apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
      exact hpy
    have hpzFace : pz.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
      apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
      exact hpz
    rw [hmap py, hmap pz]
    exact hepsDist py.1 pz.1 hpyFace hpzFace
  have hpFace : p.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
    apply (L K U hU f hf phi hphi).edgeCarrier_subset_faceCarrier e
    have hp' : p ∈ Subtype.val ⁻¹'
        (L K U hU f hf phi hphi).edgeCarrier e := by
      rw [← LocallyFiniteTriangleComplex.PlaneGraphRealization.edgeInSupport_eq_preimage
        (K := L K U hU f hf phi hphi) e]
      exact hp
    exact hp'
  calc
    2 * Metric.diam (G.edgeImage e) ≤ 2 * (eps / 4) := by gcongr
    _ < eps := by linarith
    _ ≤ phi p.1 := hepsPhi p.1 hpFace

/-- The canonical replacement graph on the controlled adaptive mesh is a pointwise
`phi`-approximation of the original realization. -/
theorem isPhiApproximation_graphReplacementMap
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    ∀ p : LocallyFiniteTriangleComplex.PlaneGraphRealization.oneSkeletonInSupport
        (K := L K U hU f hf phi hphi),
      dist (G.graphReplacementMap p) (f p.1.1) < phi p.1.1 := by
  intro p
  rw [← hmap p.1]
  exact G.isPhiApproximation_graphReplacementMap
    (edgeImagesControlled K U hU f hf phi hphi G hmap) p

/-- Every edge belonging to a controlled adaptive face has image diameter bounded by that
face's selected scale. -/
theorem edgeImage_diam_le_face_scale
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (t : (L K U hU f hf phi hphi).Face)
    (e : (L K U hU f hf phi hphi).Edge)
    (het : e.1 ⊆ (L K U hU f hf phi hphi).faceVertices t)
    {eps : ℝ}
    (heps : 0 < eps)
    (hepsDist : ∀ p q : U,
      p ∈ (L K U hU f hf phi hphi).faceCarrier t →
      q ∈ (L K U hU f hf phi hphi).faceCarrier t →
      dist (f p) (f q) ≤ eps / 4) :
    Metric.diam (G.edgeImage e) ≤ eps / 4 := by
  apply Metric.diam_le_of_forall_dist_le
  · positivity
  · intro y hy z hz
    obtain ⟨py, hpy, rfl⟩ := hy
    obtain ⟨pz, hpz, rfl⟩ := hz
    have hpyCarrier : py.1 ∈ (L K U hU f hf phi hphi).edgeCarrier e := hpy
    have hpzCarrier : pz.1 ∈ (L K U hU f hf phi hphi).edgeCarrier e := hpz
    have hedgeFace : (L K U hU f hf phi hphi).edgeCarrier e ⊆
        (L K U hU f hf phi hphi).faceCarrier t := by
      rintro _ ⟨x, rfl⟩
      refine ⟨stdSimplex.map (fun v : {v // v ∈ e.1} ↦
        (⟨v.1, het v.2⟩ : {w // w ∈ (L K U hU f hf phi hphi).faceVertices t})) x, ?_⟩
      exact ((L K U hU f hf phi hphi).edgeMap_eq_faceMap e t het x).symm
    have hpyFace : py.1 ∈ (L K U hU f hf phi hphi).faceCarrier t :=
      hedgeFace hpyCarrier
    have hpzFace : pz.1 ∈ (L K U hU f hf phi hphi).faceCarrier t :=
      hedgeFace hpzCarrier
    rw [hmap py, hmap pz]
    exact hepsDist py.1 pz.1 hpyFace hpzFace

/-- The boundary error on one adaptive face is bounded by a positive scale which is at most
both the prescribed pointwise tolerance and one. -/
theorem exists_faceBoundary_control
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (t : (L K U hU f hf phi hphi).Face)
    (p : (L K U hU f hf phi hphi).support)
    (hp : p ∈ LocallyFiniteTriangleComplex.PlaneGraphRealization.faceInSupport t)
    (q : LocallyFiniteTriangleComplex.StandardFaceBoundary) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      dist
          (G.graphReplacementMap
            ((L K U hU f hf phi hphi).faceBoundaryLift t q))
          (G.map ((L K U hU f hf phi hphi).faceBoundaryLift t q).1) +
        dist (G.map ((L K U hU f hf phi hphi).faceBoundaryLift t q).1)
          (G.map p) ≤ eps ∧
      eps ≤ phi p.1 := by
  obtain ⟨eps, heps, hepsOne, hepsPhi, hepsDist⟩ :=
    exists_face_scale K U hU f hf phi hphi t
  let b := (L K U hU f hf phi hphi).faceBoundaryLift t q
  have hpCarrier : p.1 ∈ (L K U hU f hf phi hphi).faceCarrier t := by
    obtain ⟨x, rfl⟩ := hp
    exact Set.mem_range_self x
  have hqCarrier : b.1.1 ∈
      (L K U hU f hf phi hphi).faceCarrier t := by
    change (L K U hU f hf phi hphi).faceMap t _ ∈
      Set.range ((L K U hU f hf phi hphi).faceMap t)
    exact Set.mem_range_self _
  have hqSide : q.1 ∈ standardTriangleCircle.carrier := by
    rw [standardTriangleCircle_carrier]
    simpa only [standardFaceRegion, standardTrianglePlaneComplex_support] using q.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqSide
  let e := (L K U hU f hf phi hphi).faceEdge t i
  have hqe : b.1 ∈
      LocallyFiniteTriangleComplex.PlaneGraphRealization.edgeInSupport e :=
    (L K U hU f hf phi hphi).faceBoundarySupportPoint_mem_edge t i q hi
  have hdiam : Metric.diam (G.edgeImage e) ≤ eps / 4 :=
    edgeImage_diam_le_face_scale K U hU f hf phi hphi G hmap t e
      ((L K U hU f hf phi hphi).faceEdge_subset_faceVertices t i) heps hepsDist
  have hgraph : dist
      (G.graphReplacementMap b) (G.map b.1) < eps / 2 := by
    rw [G.graphReplacementMap_eq e _ hqe]
    exact (G.replacementEdgeMap_dist_lt_two_mul_edgeImage_diam e
      ⟨b.1, hqe⟩).trans_le (by
        linarith)
  have hosc : dist
      (G.map b.1) (G.map p) ≤ eps / 4 := by
    rw [hmap, hmap]
    exact hepsDist _ _ hqCarrier hpCarrier
  have hlt :
      dist (G.graphReplacementMap b) (G.map b.1) +
          dist (G.map b.1) (G.map p) < eps := by
    calc
      dist
          (G.graphReplacementMap b) (G.map b.1) +
          dist (G.map b.1) (G.map p) < eps / 2 + eps / 4 :=
        add_lt_add_of_lt_of_le hgraph hosc
      _ < eps := by linarith
  exact ⟨eps, heps, hepsOne, hlt.le, hepsPhi p.1 hpCarrier⟩

/-- The adaptive mesh discharges the exact face-boundary estimate consumed by the cellwise
Schoenflies extension. -/
theorem faceBoundariesControlled
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    LocallyFiniteTriangleComplex.FaceBoundariesControlled G (fun p ↦ phi p.1) := by
  intro t p hp q
  obtain ⟨eps, -, -, hcontrol, hepsPhi⟩ :=
    exists_faceBoundary_control K U hU f hf phi hphi G hmap t p hp q
  exact hcontrol.trans hepsPhi

/-- If the original controlled realization lies in the model half-plane, so does its entire
simultaneous polygonal replacement graph. -/
theorem range_graphReplacementMap_subset_halfPlane
    (G : (L K U hU f hf phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1)
    (hfHalf : Set.range f ⊆ HalfPlaneSet) :
    Set.range G.graphReplacementMap ⊆ HalfPlaneSet := by
  rw [G.range_graphReplacementMap]
  intro y hy
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hy
  apply convexHull_min _ convex_halfPlaneSet
  · exact (G.replacementArc e).completeCarrier_subset_edgeConvexHull hye
  · rintro z ⟨p, -, rfl⟩
    rw [hmap p]
    exact hfHalf (Set.mem_range_self p.1)

end ControlledAdaptiveComplex

namespace RegionControlledAdaptiveComplex

variable (hU : IsOpen U) (V : Set Plane) (hV : IsOpen V)
  (f : U → Plane) (hf : Continuous f) (hmem : ∀ x, f x ∈ V)
  (phi : U → ℝ) (hphi : StronglyPositiveOn Set.univ phi)

private noncomputable abbrev R : LocallyFiniteTriangleComplex U :=
  K.regionControlledAdaptiveComplex U hU V hV f hf hmem phi hphi

/-- The adaptive face-boundary estimate for the frontier-reduced tolerance. -/
theorem faceBoundariesControlled
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) :
    LocallyFiniteTriangleComplex.FaceBoundariesControlled G
      (fun p ↦ regionSafeControl V f phi p.1) :=
  ControlledAdaptiveComplex.faceBoundariesControlled K U hU f hf
    (regionSafeControl V f phi)
    (stronglyPositiveOn_regionSafeControl hV hf hmem hphi) G hmap

/-- The tolerance consumed by the filling is uniformly bounded and frontier-relative. -/
theorem uniformFrontierControl
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    G.UniformFrontierControl
      (fun p ↦ regionSafeControl V f phi p.1) := by
  constructor
  · intro p
    exact regionSafeControl_le_one V f phi p.1
  · intro hcomp p
    have hcompV : Vᶜ.Nonempty := by rwa [← hregion]
    calc
      regionSafeControl V f phi p.1 ≤ frontierDistance V (f p.1) / 4 :=
        regionSafeControl_le_frontier hcompV f phi p.1
      _ = Metric.infDist (G.map p) G.regionᶜ / 4 := by
        rw [hmap p, hregion]
        rfl

/-- The frontier-reduced adaptive fillings lie in the open target region. -/
theorem closedRegions_mem_region
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    ∀ t : (R K U hU V hV f hf hmem phi hphi).Face,
      ((R K U hU V hV f hf hmem phi hphi).facePolygonalCircle
        (G := G) t).closedRegion ⊆ G.region := by
  exact LocallyFiniteTriangleComplex.closedRegions_mem_region_of_uniformFrontierControl
    G (faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap)
      (uniformFrontierControl K U hU V hV f hf hmem phi hphi G hmap hregion)

/-- The frontier-reduced adaptive fillings form a locally finite family in the open target. -/
theorem locallyFinite_closedRegions
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    LocallyFinite fun t : (R K U hU V hV f hf hmem phi hphi).Face ↦
      {q : G.region | q.1 ∈
        ((R K U hU V hV f hf hmem phi hphi).facePolygonalCircle
          (G := G) t).closedRegion} := by
  exact LocallyFiniteTriangleComplex.locallyFinite_closedRegions_of_uniformFrontierControl
    G (faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap)
      (uniformFrontierControl K U hU V hV f hf hmem phi hphi G hmap hregion)

/-- The region-controlled adaptive complex carries distinct vertex triples on distinct faces:
the `hfaces` entry condition of `exists_polygonalReplacement` holds unconditionally. -/
theorem faceVertices_injective :
    Function.Injective (R K U hU V hV f hf hmem phi hphi).faceVertices :=
  AdaptiveOpenCover.faceVertices_injective K U
    (K.controlledAdaptiveOpenCover U hU f hf (regionSafeControl V f phi)
      (stronglyPositiveOn_regionSafeControl hV hf hmem hphi)) hU

/-- Complete locally finite cellwise replacement once the remaining side-separation condition
is supplied.  Region containment and local finiteness are now consequences, not hypotheses. -/
theorem exists_polygonalReplacement
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V)
    (hfaces : Function.Injective
      (R K U hU V hV f hf hmem phi hphi).faceVertices)
    (hsep : LocallyFiniteTriangleComplex.SeparatesVerticesFromFaces G
      (fun p ↦ regionSafeControl V f phi p.1)) :
    ∃ H : (R K U hU V hV f hf hmem phi hphi).CellwiseCompatibility G,
      ∀ p : (R K U hU V hV f hf hmem phi hphi).support,
        dist
          ((R K U hU V hV f hf hmem phi hphi).polygonalReplacementHomeomorph H p).1.1
          (G.map p) ≤ phi p.1 := by
  have hcontrol := faceBoundariesControlled K U hU V hV f hf hmem phi hphi G hmap
  obtain ⟨H, hH⟩ :=
    LocallyFiniteTriangleComplex.exists_controlled_polygonalReplacement G hfaces
      hcontrol hsep
      (closedRegions_mem_region K U hU V hV f hf hmem phi hphi G hmap hregion)
      (locallyFinite_closedRegions K U hU V hV f hf hmem phi hphi G hmap hregion)
  refine ⟨H, fun p ↦ (hH p).trans ?_⟩
  exact regionSafeControl_le_left V f phi p.1

/-- **Complete locally finite cellwise replacement with no residual side hypothesis.**  The
separation entry of `exists_polygonalReplacement` is discharged by the facewise comparison
map after shrinking the arc approximation controls; the shrunken realization keeps the map,
the region, and the frontier-reduced tolerance, so all adaptive control theorems reapply. -/
theorem exists_polygonalReplacement_of_comparison
    (G : (R K U hU V hV f hf hmem phi hphi).PlaneGraphRealization)
    (hmap : ∀ p, G.map p = f p.1) (hregion : G.region = V) :
    ∃ (vc : (R K U hU V hV f hf hmem phi hphi).Vertex → ℝ)
      (hvc : ∀ v, 0 < vc v)
      (ec : (R K U hU V hV f hf hmem phi hphi).Edge → ℝ)
      (hec : ∀ e, 0 < ec e)
      (H : (R K U hU V hV f hf hmem phi hphi).CellwiseCompatibility
        (G.withApproximationControls vc hvc ec hec)),
      ∀ p : (R K U hU V hV f hf hmem phi hphi).support,
        dist
          ((R K U hU V hV f hf hmem phi hphi).polygonalReplacementHomeomorph H p).1.1
          (G.map p) ≤ phi p.1 := by
  obtain ⟨vc, hvc, ec, hec, hpack⟩ :=
    LocallyFiniteTriangleComplex.exists_controls_cellwiseCompatibility G
      (faceVertices_injective K U hU V hV f hf hmem phi hphi)
  set G' := G.withApproximationControls vc hvc ec hec with hG'
  have hmap' : ∀ p, G'.map p = f p.1 := hmap
  have hregion' : G'.region = V := hregion
  obtain ⟨H⟩ := hpack
    (closedRegions_mem_region K U hU V hV f hf hmem phi hphi G' hmap' hregion')
    (locallyFinite_closedRegions K U hU V hV f hf hmem phi hphi G' hmap' hregion')
  refine ⟨vc, hvc, ec, hec, H, ?_⟩
  intro p
  have hcontrol :=
    faceBoundariesControlled K U hU V hV f hf hmem phi hphi G' hmap'
  have hdist :=
    LocallyFiniteTriangleComplex.polygonalReplacementMap_dist_le H hcontrol p
  have hmapeq : G'.map p = G.map p := rfl
  rw [hmapeq] at hdist
  exact hdist.trans (regionSafeControl_le_left V f phi p.1)

end RegionControlledAdaptiveComplex

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
