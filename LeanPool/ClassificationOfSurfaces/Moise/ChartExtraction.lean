/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex
import LeanPool.ClassificationOfSurfaces.Moise.BoundaryInvariant

/-!
# Extraction of Moise charts from the mathlib atlas

Discharges `exists_moiseChart_core_mem_nhds`: every point of an Eval surface has a
boundary-faithful Moise chart (standard unit disk or half-disk model) whose core is a
neighborhood.  This is the port of the proven chart spine of `PL.lean`
(`RadoChartPair.fromChartAt` and the `euclideanHalfSpace` neighborhood lemmas) to the fresh
`MoiseChart` objects; the only new geometry is straightening a small chart ball onto the standard
model by the recentering homeomorphism `v ↦ ε⁻¹ • (v - p)`.

The construction: take the preferred chart `φ = chartAt (EuclideanHalfSpace 2) x` and let
`p = (φ x).1` in the closed half-plane.  Either `0 < p 0` (then a small ball about `p` lies in
the chart image away from the edge, giving a disk chart) or `p 0 = 0` (then a small relative
half-ball lies in the chart image, giving a half-disk chart).  C0 invariance of domain supplies
boundary-faithfulness: manifold-boundary points in the chart land on the frontier of the extended
target, hence on the model edge line.
-/

open scoped Manifold
open Topology

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open InvarianceOfDomain

/-- The closed right half-plane, the ambient model for `EuclideanHalfSpace 2`. -/
def HalfPlaneSet : Set Plane :=
  {v : Plane | 0 ≤ v 0}

theorem continuous_coordZero : Continuous fun v : Plane => v 0 :=
  PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)

theorem isOpen_posCoord : IsOpen {v : Plane | 0 < v 0} :=
  isOpen_lt continuous_const continuous_coordZero

section Recenter

/-- The recentering homeomorphism `v ↦ ε⁻¹ • (v - p)`, straightening the ball `ball p ε` onto
the unit ball. -/
noncomputable def recenter (p : Plane) (ε : ℝ) (hε : ε ≠ 0) : Plane ≃ₜ Plane :=
  (Homeomorph.addRight (-p)).trans (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε))

variable {p : Plane} {ε : ℝ}

theorem recenter_apply (hε : ε ≠ 0) (v : Plane) :
    recenter p ε hε v = ε⁻¹ • (v + -p) := rfl

theorem recenter_symm_apply (hε : ε ≠ 0) (w : Plane) :
    (recenter p ε hε).symm w = ε • w + p := by
  apply (recenter p ε hε).injective
  rw [Homeomorph.apply_symm_apply, recenter_apply]
  simp [add_assoc, smul_smul, inv_mul_cancel₀ hε]

theorem recenter_dist (hε : 0 < ε) (v : Plane) :
    dist (recenter p ε hε.ne' v) 0 = ε⁻¹ * dist v p := by
  rw [recenter_apply, dist_eq_norm, dist_eq_norm, sub_zero, ← sub_eq_add_neg, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hε]

theorem recenter_mem_ball_iff (hε : 0 < ε) {v : Plane} :
    recenter p ε hε.ne' v ∈ Metric.ball 0 1 ↔ v ∈ Metric.ball p ε := by
  rw [Metric.mem_ball, Metric.mem_ball, recenter_dist hε, inv_mul_lt_iff₀ hε, mul_one]

theorem recenter_mem_closedBall_iff (hε : 0 < ε) {v : Plane} :
    recenter p ε hε.ne' v ∈ Metric.closedBall 0 (1 / 2) ↔
      v ∈ Metric.closedBall p (ε / 2) := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall, recenter_dist hε,
    inv_mul_le_iff₀ hε]
  constructor <;> intro h <;> linarith

theorem recenter_coordZero (hε : ε ≠ 0) (v : Plane) :
    recenter p ε hε v 0 = ε⁻¹ * (v 0 - p 0) := by
  rw [recenter_apply, sub_eq_add_neg]
  simp
  ring

/-- When the center sits on the edge line, recentering preserves the half-plane condition. -/
theorem recenter_mem_halfPlane_iff (hε : 0 < ε) (hp : p 0 = 0) {v : Plane} :
    recenter p ε hε.ne' v ∈ HalfPlaneSet ↔ v ∈ HalfPlaneSet := by
  simp only [HalfPlaneSet, Set.mem_ofPred_eq, recenter_coordZero, hp, sub_zero]
  constructor
  · intro h
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [inv_pos.mpr hε]
  · intro h
    positivity

end Recenter

section HalfSpacePlumbing

/-- A relatively open subset of the closed half-plane meets its own frontier only on the edge
line.  This is the geometric fact behind boundary-faithfulness of the extracted charts. -/
theorem coordZero_eq_zero_of_mem_frontier {V : Set Plane} (hV : IsOpen V)
    {z : Plane} (hzmem : z ∈ V ∩ HalfPlaneSet) (hz : z ∈ frontier (V ∩ HalfPlaneSet)) :
    z 0 = 0 := by
  by_contra hne
  have hz0 : (0 : ℝ) ≤ z 0 := hzmem.2
  have hpos : 0 < z 0 := lt_of_le_of_ne hz0 (Ne.symm hne)
  have hopen : IsOpen (V ∩ {v : Plane | 0 < v 0}) := hV.inter isOpen_posCoord
  have hsub : V ∩ {v : Plane | 0 < v 0} ⊆ V ∩ HalfPlaneSet := by
    rintro v ⟨hv, hv0⟩
    exact ⟨hv, show (0 : ℝ) ≤ v 0 from le_of_lt hv0⟩
  have hzint : z ∈ interior (V ∩ HalfPlaneSet) :=
    interior_mono hsub (hopen.subset_interior_iff.mpr subset_rfl ⟨hzmem.1, hpos⟩)
  exact (hz.2 hzint).elim

end HalfSpacePlumbing

/-! ## Moise charts -/

/-- The kind of a Moise chart: interior charts are disks, boundary charts are half-disks. -/
inductive ChartKind where
  | disk
  | halfDisk
deriving DecidableEq, Repr

/-- The model region of a chart kind: the open unit disk, or its closed-right half. -/
def ChartKind.modelRegion : ChartKind → Set Plane
  | .disk => Metric.ball 0 1
  | .halfDisk => {x ∈ Metric.ball 0 1 | 0 ≤ x 0}

/-- The model core of a chart kind: the closed disk of radius one half, or its right half.  Cores
are compact and their union over a chart cover is what the Radó induction absorbs. -/
def ChartKind.modelCore : ChartKind → Set Plane
  | .disk => Metric.closedBall 0 (1 / 2)
  | .halfDisk => {x ∈ Metric.closedBall 0 (1 / 2) | 0 ≤ x 0}

theorem ChartKind.isCompact_modelCore (k : ChartKind) : IsCompact k.modelCore := by
  cases k with
  | disk => exact isCompact_closedBall _ _
  | halfDisk =>
      exact (isCompact_closedBall (0 : Plane) (1 / 2)).inter_right
        (isClosed_le continuous_const continuous_coordZero)

theorem ChartKind.modelCore_subset_modelRegion (k : ChartKind) :
    k.modelCore ⊆ k.modelRegion := by
  cases k with
  | disk =>
      exact (Metric.closedBall_subset_ball (by norm_num))
  | halfDisk =>
      rintro x ⟨hx, hx0⟩
      exact ⟨Metric.closedBall_subset_ball (by norm_num) hx, hx0⟩

/-- Forget the unit-ball condition on a half-disk model point while retaining its
half-space coordinate. -/
def halfDiskModelToHalfSpace :
    ChartKind.halfDisk.modelRegion → EuclideanHalfSpace 2 :=
  fun p => ⟨p.1, p.2.2⟩

@[simp] theorem halfDiskModelToHalfSpace_val
    (p : ChartKind.halfDisk.modelRegion) :
    (halfDiskModelToHalfSpace p).1 = p.1 :=
  rfl

/-- The half-disk model is an open subset of the Euclidean half-space. -/
theorem isOpenEmbedding_halfDiskModelToHalfSpace :
    _root_.Topology.IsOpenEmbedding halfDiskModelToHalfSpace := by
  have hembed :
      _root_.Topology.IsEmbedding halfDiskModelToHalfSpace :=
    by
      apply (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
      have h :=
        (_root_.Topology.IsEmbedding.subtypeVal :
          _root_.Topology.IsEmbedding
            (Subtype.val : ChartKind.halfDisk.modelRegion → Plane))
      convert h using 1
      funext p
      rfl
  refine ⟨hembed, ?_⟩
  have hrange :
      Set.range halfDiskModelToHalfSpace =
        {p : EuclideanHalfSpace 2 | p.1 ∈ Metric.ball (0 : Plane) 1} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact q.2.1
    · intro hp
      let q : ChartKind.halfDisk.modelRegion :=
        ⟨p.1, hp, p.2⟩
      exact ⟨q, EuclideanHalfSpace.ext _ _ rfl⟩
  rw [hrange]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- Boundary-relative invariance of domain in a half-disk chart.

Suppose two embeddings of the same source preserve the ambient manifold-boundary stratum.
If the corresponding source point is fixed and its old physical image is an interior point of
the old range, then that physical point remains in the interior of the new range.  The proof
restricts to the old physical interior, writes both embeddings in the half-disk chart, applies
the half-plane doubling theorem, and transports the resulting open coordinate image back to
the surface. -/
theorem mem_interior_range_of_fixed_boundary_preserving_in_halfDiskChart
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    {X : Type*} [TopologicalSpace X]
    (D : Set S) (hD : IsOpen D)
    (chart : D ≃ₜ ChartKind.halfDisk.modelRegion)
    (hchartBoundary :
      ∀ y (hy : y ∈ D),
        y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          ((chart ⟨y, hy⟩ : Plane) 0 = 0))
    {f g : X → S}
    (hf : _root_.Topology.IsEmbedding f)
    (hg : _root_.Topology.IsEmbedding g)
    (hboundary :
      ∀ y : X,
        g y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          f y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S)
    {x : X} (hxInterior : f x ∈ interior (Set.range f))
    (hxDomain : f x ∈ D) (hxFixed : g x = f x) :
    f x ∈ interior (Set.range g) := by
  let O : Set S := interior (Set.range f)
  let intoOldRange : O → Set.range f :=
    Set.inclusion interior_subset
  let source : O → X :=
    hf.toHomeomorph.symm ∘ intoOldRange
  have hsourceEmbedding : _root_.Topology.IsEmbedding source :=
    hf.toHomeomorph.symm.isEmbedding.comp
      (_root_.Topology.IsEmbedding.inclusion interior_subset)
  have hsourceValue (z : O) : f (source z) = z.1 := by
    exact congrArg Subtype.val
      (hf.toHomeomorph.apply_symm_apply (intoOldRange z))
  let transition : O → S := g ∘ source
  have htransitionEmbedding : _root_.Topology.IsEmbedding transition :=
    hg.comp hsourceEmbedding
  let W : Set O :=
    {z | z.1 ∈ D ∧ transition z ∈ D}
  have hWopen : IsOpen W := by
    exact
      (hD.preimage continuous_subtype_val).inter
        (hD.preimage htransitionEmbedding.continuous)
  let oldToDomain : W → D :=
    fun z => ⟨z.1.1, z.2.1⟩
  have holdToDomainOpen :
      _root_.Topology.IsOpenEmbedding oldToDomain := by
    let e : O → S := Subtype.val
    have he : _root_.Topology.IsOpenEmbedding e :=
      isOpen_interior.isOpenEmbedding_subtypeVal
    have hrestrict :=
      he.restrict (s := W) (t := D)
        (fun z hz => hz.1) hWopen
    convert hrestrict using 1
    funext z
    rfl
  let newToDomain : W → D :=
    fun z => ⟨transition z.1, z.2.2⟩
  have hnewToDomainEmbedding :
      _root_.Topology.IsEmbedding newToDomain := by
    have he :
        _root_.Topology.IsEmbedding
          (transition ∘ (Subtype.val : W → O)) :=
      htransitionEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal
    apply he.codRestrict D
  let surfaceChart : D → EuclideanHalfSpace 2 :=
    halfDiskModelToHalfSpace ∘ chart
  have hsurfaceChartOpen :
      _root_.Topology.IsOpenEmbedding surfaceChart :=
    isOpenEmbedding_halfDiskModelToHalfSpace.comp chart.isOpenEmbedding
  let oldMap : W → EuclideanHalfSpace 2 :=
    surfaceChart ∘ oldToDomain
  have holdMapOpen : _root_.Topology.IsOpenEmbedding oldMap :=
    hsurfaceChartOpen.comp holdToDomainOpen
  let newMap : W → EuclideanHalfSpace 2 :=
    surfaceChart ∘ newToDomain
  have hnewMapEmbedding : _root_.Topology.IsEmbedding newMap :=
    hsurfaceChartOpen.isEmbedding.comp hnewToDomainEmbedding
  have hmapBoundary :
      ∀ z : W, (newMap z).1 0 = 0 ↔ (oldMap z).1 0 = 0 := by
    intro z
    change
      ((chart ⟨transition z.1, z.2.2⟩ : Plane) 0 = 0) ↔
        ((chart ⟨z.1.1, z.2.1⟩ : Plane) 0 = 0)
    rw [← hchartBoundary (transition z.1) z.2.2,
      ← hchartBoundary z.1.1 z.2.1]
    change
      g (source z.1) ∈
          (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        z.1.1 ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S
    rw [hboundary (source z.1), hsourceValue z.1]
  have hnewMapOpen : IsOpen (Set.range newMap) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨z, rfl⟩
    apply mem_interior_iff_mem_nhds.mp
    apply mem_interior_range_halfSpace_of_isEmbedding_of_boundary
      holdMapOpen.isEmbedding hnewMapEmbedding hmapBoundary
    rw [holdMapOpen.isOpen_range.interior_eq]
    exact Set.mem_range_self z
  let z : O := ⟨f x, hxInterior⟩
  have hsourceZ : source z = x := by
    apply hf.injective
    exact hsourceValue z
  have hzW : z ∈ W := by
    refine ⟨hxDomain, ?_⟩
    change g (source z) ∈ D
    rw [hsourceZ, hxFixed]
    exact hxDomain
  let zw : W := ⟨z, hzW⟩
  let N : Set D := surfaceChart ⁻¹' Set.range newMap
  have hNopen : IsOpen N :=
    hnewMapOpen.preimage hsurfaceChartOpen.continuous
  have hxN : (⟨f x, hxDomain⟩ : D) ∈ N := by
    refine ⟨zw, ?_⟩
    change
      surfaceChart ⟨transition z, hzW.2⟩ =
        surfaceChart ⟨f x, hxDomain⟩
    apply congrArg surfaceChart
    apply Subtype.ext
    change g (source z) = f x
    rw [hsourceZ, hxFixed]
  have hNsubset :
      Subtype.val '' N ⊆ Set.range g := by
    rintro y ⟨yd, hyN, rfl⟩
    obtain ⟨w, hw⟩ := hyN
    have hdomainEq : newToDomain w = yd := by
      apply hsurfaceChartOpen.injective
      exact hw
    refine ⟨source w.1, ?_⟩
    exact congrArg Subtype.val hdomainEq
  have hNimageOpen : IsOpen (Subtype.val '' N) :=
    hD.isOpenEmbedding_subtypeVal.isOpenMap N hNopen
  apply interior_maximal hNsubset hNimageOpen
  exact ⟨⟨f x, hxDomain⟩, hxN, rfl⟩

/-- A chart of the Moise cover: an open domain homeomorphic to the model disk or half-disk, with
the compact core marked out by the chart. -/
structure MoiseChart (S : Type*) [TopologicalSpace S] where
  /-- Whether this is an interior (disk) or boundary (half-disk) chart. -/
  kind : ChartKind
  /-- The chart domain. -/
  domain : Set S
  /-- Chart domains are open. -/
  isOpen_domain : IsOpen domain
  /-- The chart homeomorphism onto the model region. -/
  chart : domain ≃ₜ kind.modelRegion

namespace MoiseChart

variable {S : Type*} [TopologicalSpace S] (c : MoiseChart S)

/-- The core of a chart: the part of the domain corresponding to the model core. -/
def core : Set S :=
  Subtype.val '' (c.chart ⁻¹' {p : c.kind.modelRegion | (p : Plane) ∈ c.kind.modelCore})

theorem core_subset_domain : c.core ⊆ c.domain := by
  rintro x ⟨p, -, rfl⟩
  exact p.2

/-- Chart cores are compact closed disks or half-disks transported through the chart. -/
theorem isCompact_core : IsCompact c.core := by
  let C : Set c.kind.modelRegion :=
    Subtype.val ⁻¹' c.kind.modelCore
  have hC : IsCompact C := by
    exact _root_.Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      c.kind.isCompact_modelCore fun x hx ↦
        ⟨⟨x, c.kind.modelCore_subset_modelRegion hx⟩, rfl⟩
  let f : c.kind.modelRegion → S := fun p ↦ (c.chart.symm p).1
  have hf : Continuous f :=
    continuous_subtype_val.comp c.chart.symm.continuous
  have hcore : c.core = f '' C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      let p : c.kind.modelRegion := c.chart y
      refine ⟨p, hy, ?_⟩
      exact congrArg Subtype.val (c.chart.symm_apply_apply y)
    · rintro ⟨p, hp, rfl⟩
      refine ⟨c.chart.symm p, ?_, rfl⟩
      simpa [C] using hp
  rw [hcore]
  exact hC.image hf

theorem mem_core_iff {s : S} :
    s ∈ c.core ↔ ∃ hs : s ∈ c.domain, ((c.chart ⟨s, hs⟩ : Plane) ∈ c.kind.modelCore) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using hy⟩
  · rintro ⟨hs, h⟩
    exact ⟨⟨s, hs⟩, h, rfl⟩

end MoiseChart

/-! ## Extraction from the mathlib atlas -/

section Extraction

open scoped Manifold

variable (S : Type*) [TopologicalSpace S]
variable [ChartedSpace (EuclideanHalfSpace 2) S]

/-- A chart is boundary-faithful when its model kind honestly reflects the manifold boundary:
disk charts contain no manifold-boundary points, and in a half-disk chart the
manifold-boundary stratum is exactly the model edge line.

The forward half-disk implication is `ChartBoundaryInvariant`.  The reverse implication follows
from the same invariance-of-domain layer: chart independence identifies a zero normal coordinate
with the frontier of the half-space model. -/
def MoiseChart.BoundaryFaithful {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] (c : MoiseChart S) : Prop :=
  (c.kind = ChartKind.disk →
    ∀ y ∈ c.domain, y ∉ (modelWithCornersEuclideanHalfSpace 2).boundary S) ∧
  (c.kind = ChartKind.halfDisk →
    ∀ y (hy : y ∈ c.domain),
      y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
        ((c.chart ⟨y, hy⟩ : Plane) 0 = 0))

/-- The image of the preferred chart's target in the plane is a relatively open subset of the
closed half-plane. -/
theorem chartImage_eq_inter (x : S) :
    Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target =
      ((modelWithCornersEuclideanHalfSpace 2).symm ⁻¹'
          (chartAt (EuclideanHalfSpace 2) x).target) ∩ HalfPlaneSet := by
  have h1 := (chartAt (EuclideanHalfSpace 2) x).extend_target
    (I := modelWithCornersEuclideanHalfSpace 2)
  have h2 := (chartAt (EuclideanHalfSpace 2) x).extend_target'
    (I := modelWithCornersEuclideanHalfSpace 2)
  have hval : (modelWithCornersEuclideanHalfSpace 2) ''
      (chartAt (EuclideanHalfSpace 2) x).target =
        Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target := rfl
  have hrange : Set.range (modelWithCornersEuclideanHalfSpace 2) = HalfPlaneSet :=
    range_modelWithCornersEuclideanHalfSpace 2
  rw [← hval, ← h2, h1, hrange]

/-- The chart image is an ambient plane neighborhood of the center's image when the latter is
away from the edge. -/
theorem chartImage_mem_nhds_of_coord_pos (x : S)
    (hpt : (0 : ℝ) <
      (((chartAt (EuclideanHalfSpace 2) x) x)).1 0) :
    Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target ∈
      𝓝 ((((chartAt (EuclideanHalfSpace 2) x) x)).1) := by
  have hxsource : x ∈ (chartAt (EuclideanHalfSpace 2) x).source :=
    mem_chart_source (EuclideanHalfSpace 2) x
  have hptE : (((chartAt (EuclideanHalfSpace 2) x) x)).1 ∈
      Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target :=
    ⟨_, (chartAt (EuclideanHalfSpace 2) x).map_source hxsource, rfl⟩
  rw [chartImage_eq_inter] at hptE ⊢
  have hVopen : IsOpen ((modelWithCornersEuclideanHalfSpace 2).symm ⁻¹'
      (chartAt (EuclideanHalfSpace 2) x).target) :=
    (chartAt (EuclideanHalfSpace 2) x).open_target.preimage
      (modelWithCornersEuclideanHalfSpace 2).continuous_symm
  have hH : HalfPlaneSet ∈
      𝓝 ((((chartAt (EuclideanHalfSpace 2) x) x)).1) :=
    Filter.mem_of_superset (isOpen_posCoord.mem_nhds hpt) fun v hv =>
      show (0 : ℝ) ≤ v 0 from le_of_lt hv
  exact Filter.inter_mem (hVopen.mem_nhds hptE.1) hH

/-- The chart image is a relative half-plane neighborhood of the center's image. -/
theorem chartImage_mem_nhdsWithin (x : S) :
    Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target ∈
      𝓝[HalfPlaneSet] (((chartAt (EuclideanHalfSpace 2) x) x).1) := by
  have hxsource : x ∈ (chartAt (EuclideanHalfSpace 2) x).source :=
    mem_chart_source (EuclideanHalfSpace 2) x
  have hptE : (((chartAt (EuclideanHalfSpace 2) x) x)).1 ∈
      Subtype.val '' (chartAt (EuclideanHalfSpace 2) x).target :=
    ⟨_, (chartAt (EuclideanHalfSpace 2) x).map_source hxsource, rfl⟩
  rw [chartImage_eq_inter] at hptE ⊢
  have hVopen : IsOpen ((modelWithCornersEuclideanHalfSpace 2).symm ⁻¹'
      (chartAt (EuclideanHalfSpace 2) x).target) :=
    (chartAt (EuclideanHalfSpace 2) x).open_target.preimage
      (modelWithCornersEuclideanHalfSpace 2).continuous_symm
  exact mem_nhdsWithin.mpr ⟨_, hVopen, hptE.1, subset_rfl⟩

/-- Boundary points of the chart source have edge-line chart coordinates: the chart-level
consequence of planar invariance of domain. -/
theorem coordZero_of_boundary (x : S) {y : S}
    (hy : y ∈ (chartAt (EuclideanHalfSpace 2) x).source)
    (hybd : y ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S) :
    (((chartAt (EuclideanHalfSpace 2) x) y)).1 0 = 0 := by
  have hcbi := ChartBoundaryInvariant.chartAt_extend_mem_frontier_target_of_boundary
    (S := S) x hy hybd
  have hmem : ((chartAt (EuclideanHalfSpace 2) x).extend
      (modelWithCornersEuclideanHalfSpace 2)) y ∈
        ((chartAt (EuclideanHalfSpace 2) x).extend
          (modelWithCornersEuclideanHalfSpace 2)).target := by
    apply PartialEquiv.map_source
    rw [(chartAt (EuclideanHalfSpace 2) x).extend_source
      (I := modelWithCornersEuclideanHalfSpace 2)]
    exact hy
  have htarget_eq : ((chartAt (EuclideanHalfSpace 2) x).extend
      (modelWithCornersEuclideanHalfSpace 2)).target =
        ((modelWithCornersEuclideanHalfSpace 2).symm ⁻¹'
          (chartAt (EuclideanHalfSpace 2) x).target) ∩ HalfPlaneSet := by
    rw [(chartAt (EuclideanHalfSpace 2) x).extend_target
      (I := modelWithCornersEuclideanHalfSpace 2),
      range_modelWithCornersEuclideanHalfSpace]
    rfl
  have hVopen : IsOpen ((modelWithCornersEuclideanHalfSpace 2).symm ⁻¹'
      (chartAt (EuclideanHalfSpace 2) x).target) :=
    (chartAt (EuclideanHalfSpace 2) x).open_target.preimage
      (modelWithCornersEuclideanHalfSpace 2).continuous_symm
  rw [htarget_eq] at hmem hcbi
  exact coordZero_eq_zero_of_mem_frontier hVopen hmem hcbi

/-- Interior case of the chart extraction: a disk chart at a point whose preferred chart
coordinate is away from the edge. -/
theorem exists_moiseChart_of_coord_pos (x : S)
    (hpt : (0 : ℝ) <
      (((chartAt (EuclideanHalfSpace 2) x) x)).1 0) :
    ∃ c : MoiseChart S, c.BoundaryFaithful ∧ c.core ∈ 𝓝 x := by
  classical
  have hxsource : x ∈ (chartAt (EuclideanHalfSpace 2) x).source :=
    mem_chart_source (EuclideanHalfSpace 2) x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (chartImage_mem_nhds_of_coord_pos S x hpt)
      (isOpen_posCoord.mem_nhds hpt))
  set pt : Plane := (((chartAt (EuclideanHalfSpace 2) x) x)).1
    with hptdef
  set domain : Set S := (chartAt (EuclideanHalfSpace 2) x).source ∩
      (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt ε) with hdomdef
  have hdomOpen : IsOpen domain :=
    (chartAt (EuclideanHalfSpace 2) x).isOpen_inter_preimage
      (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hdom_sub : domain ⊆ (chartAt (EuclideanHalfSpace 2) x).source := Set.inter_subset_left
  set f : domain → Plane := fun y =>
    recenter pt ε hε.ne'
      (((chartAt (EuclideanHalfSpace 2) x) y.1)).1 with hfdef
  have hf_emb : Topology.IsEmbedding f := by
    have hcomp := ((recenter pt ε hε.ne').isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp
          ((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.isEmbedding.comp
            (Topology.IsEmbedding.inclusion hdom_sub)))))
    convert hcomp using 1
    funext y
    simp [hfdef, Function.comp]
  have hrange : Set.range f = Metric.ball 0 1 := by
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact (recenter_mem_ball_iff hε).mpr y.2.2
    · intro hw
      have hv : recenter pt ε hε.ne' ((recenter pt ε hε.ne').symm w) ∈ Metric.ball 0 1 := by
        rw [Homeomorph.apply_symm_apply]
        exact hw
      have hvball : (recenter pt ε hε.ne').symm w ∈ Metric.ball pt ε :=
        (recenter_mem_ball_iff hε).mp hv
      obtain ⟨⟨u, hu_target, hu_val⟩, -⟩ := hball hvball
      have hy0source : (chartAt (EuclideanHalfSpace 2) x).symm u ∈
          (chartAt (EuclideanHalfSpace 2) x).source :=
        (chartAt (EuclideanHalfSpace 2) x).map_target hu_target
      have hy0img : (chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u) = u :=
        (chartAt (EuclideanHalfSpace 2) x).right_inv hu_target
      have hy0dom : (chartAt (EuclideanHalfSpace 2) x).symm u ∈ domain := by
        refine ⟨hy0source, ?_⟩
        change ((chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u) : EuclideanHalfSpace 2) ∈
            Subtype.val ⁻¹' Metric.ball pt ε
        rw [hy0img]
        change u.1 ∈ Metric.ball pt ε
        rw [hu_val]
        exact hvball
      refine ⟨⟨_, hy0dom⟩, ?_⟩
      change recenter pt ε hε.ne'
        (((chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u))).1 = w
      rw [hy0img, hu_val]
      exact (recenter pt ε hε.ne').apply_symm_apply w
  refine ⟨⟨ChartKind.disk, domain, hdomOpen,
    hf_emb.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩, ⟨?_, ?_⟩, ?_⟩
  · -- disk charts contain no manifold-boundary points
    intro _ y hydom hybd
    have h0 := coordZero_of_boundary S x (hdom_sub hydom) hybd
    obtain ⟨-, hpos⟩ := hball hydom.2
    exact absurd h0 (ne_of_gt hpos)
  · -- vacuous: the kind is not halfDisk
    intro hk
    simp at hk
  · -- the core is a neighborhood of the center
    have hNopen : IsOpen ((chartAt (EuclideanHalfSpace 2) x).source ∩
        (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt (ε / 2))) :=
      (chartAt (EuclideanHalfSpace 2) x).isOpen_inter_preimage
        (Metric.isOpen_ball.preimage continuous_subtype_val)
    have hxN : x ∈ (chartAt (EuclideanHalfSpace 2) x).source ∩
        (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt (ε / 2)) := by
      refine ⟨hxsource, ?_⟩
      change pt ∈ Metric.ball pt (ε / 2)
      exact Metric.mem_ball_self (by positivity)
    refine Filter.mem_of_superset (hNopen.mem_nhds hxN) ?_
    intro s hs
    rw [MoiseChart.mem_core_iff]
    have hsdom : s ∈ domain :=
      ⟨hs.1, Metric.ball_subset_ball (by linarith) hs.2⟩
    refine ⟨hsdom, ?_⟩
    change f ⟨s, hsdom⟩ ∈ ChartKind.disk.modelCore
    exact (recenter_mem_closedBall_iff hε).mpr (Metric.ball_subset_closedBall hs.2)

/-- Boundary case of the chart extraction: a half-disk chart at a point whose preferred chart
coordinate lies on the edge line. -/
theorem exists_moiseChart_of_coord_zero (x : S)
    (hpt : (((chartAt (EuclideanHalfSpace 2) x) x)).1 0 = 0) :
    ∃ c : MoiseChart S, c.BoundaryFaithful ∧ c.core ∈ 𝓝 x := by
  classical
  have hxsource : x ∈ (chartAt (EuclideanHalfSpace 2) x).source :=
    mem_chart_source (EuclideanHalfSpace 2) x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp (chartImage_mem_nhdsWithin S x)
  set pt : Plane := (((chartAt (EuclideanHalfSpace 2) x) x)).1
    with hptdef
  set domain : Set S := (chartAt (EuclideanHalfSpace 2) x).source ∩
      (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt ε) with hdomdef
  have hdomOpen : IsOpen domain :=
    (chartAt (EuclideanHalfSpace 2) x).isOpen_inter_preimage
      (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hdom_sub : domain ⊆ (chartAt (EuclideanHalfSpace 2) x).source := Set.inter_subset_left
  set f : domain → Plane := fun y =>
    recenter pt ε hε.ne'
      (((chartAt (EuclideanHalfSpace 2) x) y.1)).1 with hfdef
  have hf_emb : Topology.IsEmbedding f := by
    have hcomp := ((recenter pt ε hε.ne').isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (Topology.IsEmbedding.subtypeVal.comp
          ((chartAt (EuclideanHalfSpace 2) x).toHomeomorphSourceTarget.isEmbedding.comp
            (Topology.IsEmbedding.inclusion hdom_sub)))))
    convert hcomp using 1
    funext y
    simp [hfdef, Function.comp]
  have hrange : Set.range f = ChartKind.halfDisk.modelRegion := by
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(recenter_mem_ball_iff hε).mpr y.2.2, ?_⟩
      have hyH : (((chartAt (EuclideanHalfSpace 2) x) y.1)).1 ∈
          HalfPlaneSet :=
        ((chartAt (EuclideanHalfSpace 2) x) y.1).2
      exact (recenter_mem_halfPlane_iff hε hpt).mpr hyH
    · rintro ⟨hw1, hw0⟩
      have hv : recenter pt ε hε.ne' ((recenter pt ε hε.ne').symm w) = w :=
        (recenter pt ε hε.ne').apply_symm_apply w
      have hvball : (recenter pt ε hε.ne').symm w ∈ Metric.ball pt ε := by
        apply (recenter_mem_ball_iff hε).mp
        rw [hv]
        exact hw1
      have hvH : (recenter pt ε hε.ne').symm w ∈ HalfPlaneSet := by
        apply (recenter_mem_halfPlane_iff hε hpt).mp
        rw [hv]
        exact hw0
      obtain ⟨u, hu_target, hu_val⟩ := hball ⟨hvball, hvH⟩
      have hy0source : (chartAt (EuclideanHalfSpace 2) x).symm u ∈
          (chartAt (EuclideanHalfSpace 2) x).source :=
        (chartAt (EuclideanHalfSpace 2) x).map_target hu_target
      have hy0img : (chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u) = u :=
        (chartAt (EuclideanHalfSpace 2) x).right_inv hu_target
      have hy0dom : (chartAt (EuclideanHalfSpace 2) x).symm u ∈ domain := by
        refine ⟨hy0source, ?_⟩
        change ((chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u) : EuclideanHalfSpace 2) ∈
            Subtype.val ⁻¹' Metric.ball pt ε
        rw [hy0img]
        change u.1 ∈ Metric.ball pt ε
        rw [hu_val]
        exact hvball
      refine ⟨⟨_, hy0dom⟩, ?_⟩
      change recenter pt ε hε.ne'
        (((chartAt (EuclideanHalfSpace 2) x)
          ((chartAt (EuclideanHalfSpace 2) x).symm u))).1 = w
      rw [hy0img, hu_val]
      exact (recenter pt ε hε.ne').apply_symm_apply w
  refine ⟨⟨ChartKind.halfDisk, domain, hdomOpen,
    hf_emb.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩, ⟨?_, ?_⟩, ?_⟩
  · -- vacuous: the kind is not disk
    intro hk
    simp at hk
  · -- the manifold boundary is exactly the model edge line
    intro _ y hydom
    constructor
    · intro hybd
      have h0 := coordZero_of_boundary S x (hdom_sub hydom) hybd
      change (f ⟨y, hydom⟩) 0 = 0
      rw [hfdef]
      simp only [recenter_coordZero, hpt, sub_zero]
      rw [h0]
      ring
    · intro hline
      have h0 :
          (((chartAt (EuclideanHalfSpace 2) x) y)).1 0 = 0 := by
        change (f ⟨y, hydom⟩) 0 = 0 at hline
        rw [hfdef] at hline
        simp only [recenter_coordZero, hpt, sub_zero] at hline
        exact (mul_eq_zero.mp hline).resolve_left (inv_ne_zero hε.ne')
      apply
        (isBoundaryPoint_iff_any_chart
          (M := S) (modelWithCornersEuclideanHalfSpace 2)
          (f := chartAt (EuclideanHalfSpace 2) x)
          (hdom_sub hydom)).mpr
      rw [frontier_range_modelWithCornersEuclideanHalfSpace]
      exact h0.symm
  · -- the core is a neighborhood of the center
    have hNopen : IsOpen ((chartAt (EuclideanHalfSpace 2) x).source ∩
        (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt (ε / 2))) :=
      (chartAt (EuclideanHalfSpace 2) x).isOpen_inter_preimage
        (Metric.isOpen_ball.preimage continuous_subtype_val)
    have hxN : x ∈ (chartAt (EuclideanHalfSpace 2) x).source ∩
        (chartAt (EuclideanHalfSpace 2) x) ⁻¹' (Subtype.val ⁻¹' Metric.ball pt (ε / 2)) := by
      refine ⟨hxsource, ?_⟩
      change pt ∈ Metric.ball pt (ε / 2)
      exact Metric.mem_ball_self (by positivity)
    refine Filter.mem_of_superset (hNopen.mem_nhds hxN) ?_
    intro s hs
    rw [MoiseChart.mem_core_iff]
    have hsdom : s ∈ domain :=
      ⟨hs.1, Metric.ball_subset_ball (by linarith) hs.2⟩
    refine ⟨hsdom, ?_⟩
    change f ⟨s, hsdom⟩ ∈ ChartKind.halfDisk.modelCore
    refine ⟨(recenter_mem_closedBall_iff hε).mpr (Metric.ball_subset_closedBall hs.2), ?_⟩
    have hsH : (((chartAt (EuclideanHalfSpace 2) x) s)).1 ∈
        HalfPlaneSet :=
      ((chartAt (EuclideanHalfSpace 2) x) s).2
    exact (recenter_mem_halfPlane_iff hε hpt).mpr hsH

/-- **Local chart extraction** (Moise Ch. 8, Thm. 1, local part; bordered version).

Every point of an Eval surface has a boundary-faithful Moise chart whose core is a neighborhood
of the point: interior points get disk charts, edge points get half-disk charts, and invariance of
domain supplies boundary-faithfulness. -/
theorem exists_moiseChart_core_mem_nhds (x : S) :
    ∃ c : MoiseChart S, c.BoundaryFaithful ∧ c.core ∈ 𝓝 x := by
  rcases lt_or_eq_of_le
      (((chartAt (EuclideanHalfSpace 2) x) x : EuclideanHalfSpace 2)).2 with h | h
  · exact exists_moiseChart_of_coord_pos S x h
  · exact exists_moiseChart_of_coord_zero S x h.symm

end Extraction

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
