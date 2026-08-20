/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicComplex
import LeanPool.ClassificationOfSurfaces.Moise.GraphPolygonalization

/-!
# Polygonal approximation of intrinsic finite graphs

This file ports the source-independent part of Moise Chapter 6, Theorem 2 from plane complexes
to canonical barycentric realizations.  The target geometry is unchanged: finitely many compact
embedded arcs admit uniform disjoint vertex disks and nonincident edge tubes.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex)

/-- Uniform target disks around the images of the used intrinsic vertices. -/
structure VertexDiskControl (h : K.realization → Plane) where
  /-- The `radius` declaration. -/
  radius : ℝ
  radius_pos : 0 < radius
  vertices_disjoint : ∀ v w : K.UsedVertex, v ≠ w →
    Disjoint (Metric.closedBall (h (K.vertexPoint v)) radius)
      (Metric.closedBall (h (K.vertexPoint w)) radius)
  avoids_nonincident_edge : ∀ v : K.UsedVertex, ∀ e : K.Edge, v.1 ∉ e.1 →
    Disjoint (Metric.closedBall (h (K.vertexPoint v)) radius)
      (Metric.cthickening radius (Set.range (K.mappedEdgePath h e)))

private theorem disjoint_vertex_images {h : K.realization → Plane}
    (hinj : Function.Injective h) {v w : K.UsedVertex} (hvw : v ≠ w) :
    Disjoint ({h (K.vertexPoint v)} : Set Plane) {h (K.vertexPoint w)} := by
  rw [Set.disjoint_singleton]
  exact hinj.ne (K.injective_vertexPoint.ne hvw)

private theorem disjoint_vertex_edge_image {h : K.realization → Plane}
    (hinj : Function.Injective h) {v : K.UsedVertex} {e : K.Edge} (hve : v.1 ∉ e.1) :
    Disjoint ({h (K.vertexPoint v)} : Set Plane)
      (Set.range (K.mappedEdgePath h e)) := by
  rw [Set.disjoint_singleton_left]
  intro hv
  rw [K.range_mappedEdgePath h e] at hv
  rcases hv with ⟨x, hx, hvx⟩
  have hpoint : K.vertexPoint v = x := hinj hvx.symm
  rw [← hpoint] at hx
  exact hve ((K.vertexPoint_mem_faceCarrier_iff v e.1).mp hx)

/-- The finite uniform vertex-disk construction for an intrinsic embedded graph. -/
theorem exists_vertexDiskControl {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h) :
    Nonempty (K.VertexDiskControl h) := by
  classical
  let I := Option ((K.UsedVertex × K.UsedVertex) ⊕ (K.UsedVertex × K.Edge))
  let P : I → ℝ → Prop
    | none, _ => True
    | some (Sum.inl (v, w)), δ => v = w ∨
        Disjoint (Metric.cthickening δ ({h (K.vertexPoint v)} : Set Plane))
          (Metric.cthickening δ ({h (K.vertexPoint w)} : Set Plane))
    | some (Sum.inr (v, e)), δ => v.1 ∈ e.1 ∨
        Disjoint (Metric.cthickening δ ({h (K.vertexPoint v)} : Set Plane))
          (Metric.cthickening δ (Set.range (K.mappedEdgePath h e)))
  have hlocal : ∀ i : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P i δ := by
    intro i
    rcases i with _ | i
    · exact ⟨1, by norm_num, fun _ _ _ => trivial⟩
    · rcases i with ⟨v, w⟩ | ⟨v, e⟩
      · by_cases hvw : v = w
        · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hvw⟩
        · have hdis := K.disjoint_vertex_images hinj hvw
          obtain ⟨ε, hε, hthick⟩ :=
            hdis.exists_thickenings isCompact_singleton isClosed_singleton
          refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
          exact hthick.mono
            (Metric.cthickening_subset_thickening' hε hδε _)
            (Metric.cthickening_subset_thickening' hε hδε _)
      · by_cases hve : v.1 ∈ e.1
        · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hve⟩
        · have hdis := K.disjoint_vertex_edge_image hinj hve
          obtain ⟨ε, hε, hthick⟩ := hdis.exists_thickenings isCompact_singleton
            (K.isCompact_range_mappedEdgePath hcont e).isClosed
          refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
          exact hthick.mono
            (Metric.cthickening_subset_thickening' hε hδε _)
            (Metric.cthickening_subset_thickening' hε hδε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  refine ⟨{
    radius := r
    radius_pos := hr
    vertices_disjoint := ?_
    avoids_nonincident_edge := ?_ }⟩
  · intro v w hvw
    have hP := huniform (some (Sum.inl (v, w))) r hr (half_lt_self hε)
    rcases hP with heq | hdis
    · exact (hvw heq).elim
    · exact hdis.mono
        (Metric.closedBall_subset_cthickening (Set.mem_singleton _) r)
        (Metric.closedBall_subset_cthickening (Set.mem_singleton _) r)
  · intro v e hve
    have hP := huniform (some (Sum.inr (v, e))) r hr (half_lt_self hε)
    rcases hP with hmem | hdis
    · exact (hve hmem).elim
    · exact hdis.mono_left
        (Metric.closedBall_subset_cthickening (Set.mem_singleton _) r)

namespace VertexDiskControl

/-- All intrinsic vertex and nonincident-edge separation properties survive shrinking the
common target radius. -/
def shrink {h : K.realization → Plane} (D : K.VertexDiskControl h) (r : ℝ)
    (hr : 0 < r) (hrD : r ≤ D.radius) : K.VertexDiskControl h where
  radius := r
  radius_pos := hr
  vertices_disjoint v w hvw :=
    (D.vertices_disjoint v w hvw).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.closedBall_subset_closedBall hrD)
  avoids_nonincident_edge v e hve :=
    (D.avoids_nonincident_edge v e hve).mono
      (Metric.closedBall_subset_closedBall hrD)
      (Metric.cthickening_mono hrD _)

end VertexDiskControl

/-- Intrinsic vertex-disk controls can be chosen below any prescribed positive radius. -/
theorem exists_vertexDiskControl_lt {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    {η : ℝ} (hη : 0 < η) :
    ∃ D : K.VertexDiskControl h, D.radius < η := by
  obtain ⟨D⟩ := K.exists_vertexDiskControl hcont hinj
  let r := min (D.radius / 2) (η / 2)
  have hr : 0 < r := lt_min (half_pos D.radius_pos) (half_pos hη)
  have hrD : r ≤ D.radius :=
    (min_le_left _ _).trans (half_le_self D.radius_pos.le)
  refine ⟨VertexDiskControl.shrink K D r hr hrD, ?_⟩
  exact (min_le_right _ _).trans_lt (half_lt_self hη)

/-- A globally defined version of an intrinsic mapped edge, clamped to the unit interval. -/
noncomputable def edgeCurve (h : K.realization → Plane) (e : K.Edge) (t : ℝ) : Plane :=
  K.mappedEdgePath h e (Set.projIcc 0 1 zero_le_one t)

theorem continuous_edgeCurve {h : K.realization → Plane} (hcont : Continuous h) (e : K.Edge) :
    Continuous (K.edgeCurve h e) :=
  (K.continuous_mappedEdgePath hcont e).comp continuous_projIcc

theorem edgeCurve_eq_of_mem {h : K.realization → Plane} (e : K.Edge) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    K.edgeCurve h e t = K.mappedEdgePath h e ⟨t, ht⟩ := by
  apply congrArg (K.mappedEdgePath h e)
  apply Subtype.ext
  rw [Set.coe_projIcc]
  simp [ht.1, ht.2]

@[simp] theorem edgeCurve_zero (h : K.realization → Plane) (e : K.Edge) :
    K.edgeCurve h e 0 = h (K.edgeFirstPoint e) := by
  rw [K.edgeCurve_eq_of_mem e (by simp)]
  exact K.mappedEdgePath_zero h e

@[simp] theorem edgeCurve_one (h : K.realization → Plane) (e : K.Edge) :
    K.edgeCurve h e 1 = h (K.edgeSecondPoint e) := by
  rw [K.edgeCurve_eq_of_mem e (by simp)]
  exact K.mappedEdgePath_one h e

/-- The two ordered circle crossings delimiting the central part of an intrinsic mapped edge. -/
structure EdgeTrimData (h : K.realization → Plane) (D : K.VertexDiskControl h) (e : K.Edge) where
  /-- The `left` declaration. -/
  left : ℝ
  /-- The `right` declaration. -/
  right : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_one : right < 1
  left_on_sphere : dist (K.edgeCurve h e left)
    (h (K.edgeFirstPoint e)) = D.radius
  right_on_sphere : dist (K.edgeCurve h e right)
    (h (K.edgeSecondPoint e)) = D.radius
  after_left : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t →
    K.edgeCurve h e t ∉ Metric.closedBall (h (K.edgeFirstPoint e)) D.radius
  before_right : ∀ t ∈ Set.Icc (0 : ℝ) 1, left < t → t < right →
    K.edgeCurve h e t ∉ Metric.closedBall (h (K.edgeSecondPoint e)) D.radius

/-- Moise's two-sided last-exit construction for an intrinsic edge. -/
theorem exists_edgeTrimData {h : K.realization → Plane} (hcont : Continuous h)
    (D : K.VertexDiskControl h) (e : K.Edge) : Nonempty (K.EdgeTrimData h D e) := by
  have hends : K.edgeFirstUsed e ≠ K.edgeSecondUsed e :=
    K.edgeFirstUsed_ne_edgeSecondUsed e
  have hsecondBall : h (K.edgeSecondPoint e) ∈
      Metric.closedBall (h (K.edgeSecondPoint e)) D.radius := by
    rw [Metric.mem_closedBall, dist_self]
    exact D.radius_pos.le
  have hfinishOutside : K.edgeCurve h e 1 ∉
      Metric.closedBall (h (K.edgeFirstPoint e)) D.radius := by
    rw [K.edgeCurve_one]
    intro hfirstBall
    exact Set.disjoint_left.mp
      (by simpa only [K.vertexPoint_edgeFirstUsed e, K.vertexPoint_edgeSecondUsed e] using
        D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e) hends)
      hfirstBall hsecondBall
  obtain ⟨L⟩ := exists_lastExitData D.radius_pos
    (K.continuous_edgeCurve hcont e).continuousOn (K.edgeCurve_zero h e) hfinishOutside
  let a := L.parameter
  let q : ℝ → ℝ := fun s => 1 - (1 - a) * s
  let rho : ℝ → Plane := fun s => K.edgeCurve h e (q s)
  have hqMaps : Set.MapsTo q (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hqeq : q s = (1 - s) + s * a := by
      dsimp [q]
      ring
    rw [hqeq]
    constructor
    · exact add_nonneg (sub_nonneg.mpr hs.2) (mul_nonneg hs.1 L.parameter_mem.1)
    · have hsa : s * a ≤ s * 1 := mul_le_mul_of_nonneg_left L.parameter_mem.2 hs.1
      linarith
  have hqcont : Continuous q := by fun_prop
  have hrhoCont : ContinuousOn rho (Set.Icc (0 : ℝ) 1) :=
    (K.continuous_edgeCurve hcont e).continuousOn.comp hqcont.continuousOn hqMaps
  have hrhoZero : rho 0 = h (K.edgeSecondPoint e) := by
    simp [rho, q]
  have hleftFirstBall : K.edgeCurve h e a ∈
      Metric.closedBall (h (K.edgeFirstPoint e)) D.radius := by
    rw [Metric.mem_closedBall]
    exact L.on_sphere.le
  have hleftOutsideSecond : rho 1 ∉
      Metric.closedBall (h (K.edgeSecondPoint e)) D.radius := by
    have hrhoOne : rho 1 = K.edgeCurve h e a := by simp [rho, q, a]
    rw [hrhoOne]
    intro hsecond
    exact Set.disjoint_left.mp
      (by simpa only [K.vertexPoint_edgeFirstUsed e, K.vertexPoint_edgeSecondUsed e] using
        D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e) hends)
      hleftFirstBall hsecond
  obtain ⟨R⟩ := exists_lastExitData D.radius_pos hrhoCont hrhoZero hleftOutsideSecond
  let b : ℝ := q R.parameter
  have hab : a < b := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_lt_one]
  have hb1 : b < 1 := by
    dsimp [b, q]
    nlinarith [L.parameter_lt_one, R.parameter_pos]
  refine ⟨{
    left := a
    right := b
    left_pos := L.parameter_pos
    left_lt_right := hab
    right_lt_one := hb1
    left_on_sphere := L.on_sphere
    right_on_sphere := R.on_sphere
    after_left := L.after_exit
    before_right := ?_ }⟩
  intro t ht hat htb
  have ha1 : a < 1 := L.parameter_lt_one
  let s : ℝ := (1 - t) / (1 - a)
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha1.le)
    · apply (div_le_one (sub_pos.mpr ha1)).mpr
      linarith
  have hRs : R.parameter < s := by
    dsimp [b, q] at htb
    dsimp [s]
    apply (lt_div_iff₀ (sub_pos.mpr ha1)).mpr
    nlinarith
  have hrhos : rho s = K.edgeCurve h e t := by
    dsimp [rho, q, s]
    congr 2
    rw [mul_div_cancel₀ (1 - t) (sub_ne_zero.mpr ha1.ne')]
    ring
  rw [← hrhos]
  exact R.after_exit s hs hRs

namespace EdgeTrimData

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {D : K.VertexDiskControl h} {e : K.Edge}

/-- The compact middle of an intrinsic edge after removing its two vertex-disk ends. -/
def centralCarrier (T : K.EdgeTrimData h D e) : Set Plane :=
  K.edgeCurve h e '' Set.Icc T.left T.right

theorem isCompact_centralCarrier (T : K.EdgeTrimData h D e)
    (hcont : Continuous h) : IsCompact T.centralCarrier := by
  apply isCompact_Icc.image_of_continuousOn
  exact (K.continuous_edgeCurve hcont e).continuousOn

theorem centralCarrier_subset_mapped_openEdge (T : K.EdgeTrimData h D e) :
    T.centralCarrier ⊆ K.mappedEdgePath h e ''
      {r : Set.Icc (0 : ℝ) 1 | 0 < r.1 ∧ r.1 < 1} := by
  rintro y ⟨t, ht, rfl⟩
  have htUnit : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨T.left_pos.le.trans ht.1, ht.2.trans T.right_lt_one.le⟩
  rw [K.edgeCurve_eq_of_mem e htUnit]
  exact ⟨⟨t, htUnit⟩, ⟨T.left_pos.trans_le ht.1,
    ht.2.trans_lt T.right_lt_one⟩, rfl⟩

theorem disjoint_centralCarrier {d : K.Edge} {T' : K.EdgeTrimData h D d}
    (T : K.EdgeTrimData h D e) (hinj : Function.Injective h) (hed : e ≠ d) :
    Disjoint T.centralCarrier T'.centralCarrier := by
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨r, hr, hry⟩ := T.centralCarrier_subset_mapped_openEdge hy
  obtain ⟨s, hs, hsy⟩ := T'.centralCarrier_subset_mapped_openEdge hy'
  have hpaths : K.edgePath e r = K.edgePath d s :=
    hinj (hry.trans hsy.symm)
  exact Set.disjoint_left.mp (K.disjoint_edgePath_image_Ioo hed)
    ⟨r, hr, rfl⟩ ⟨s, hs, hpaths.symm⟩

end EdgeTrimData

/-- A chosen last-exit trim for each intrinsic edge. -/
noncomputable def edgeTrim {h : K.realization → Plane} (hcont : Continuous h)
    (D : K.VertexDiskControl h) (e : K.Edge) : K.EdgeTrimData h D e :=
  Classical.choice (K.exists_edgeTrimData hcont D e)

/-- Pairwise-disjoint closed tubes around all trimmed central intrinsic arcs. -/
structure CentralTubeControl {h : K.realization → Plane} (hcont : Continuous h)
    (hinj : Function.Injective h) (D : K.VertexDiskControl h) where
  /-- The `radius` declaration. -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_vertex : radius < D.radius
  pairwise_disjoint : ∀ e d : K.Edge, e ≠ d →
    Disjoint
      (Metric.cthickening radius (K.edgeTrim hcont D e).centralCarrier)
      (Metric.cthickening radius (K.edgeTrim hcont D d).centralCarrier)

theorem exists_centralTubeControl {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) : Nonempty (K.CentralTubeControl hcont hinj D) := by
  classical
  let I := Option (K.Edge × K.Edge)
  let P : I → ℝ → Prop
    | none, _ => True
    | some (e, d), δ => e = d ∨
        Disjoint (Metric.cthickening δ (K.edgeTrim hcont D e).centralCarrier)
          (Metric.cthickening δ (K.edgeTrim hcont D d).centralCarrier)
  have hlocal : ∀ c : I, ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε → P c δ := by
    intro c
    rcases c with _ | ⟨e, d⟩
    · exact ⟨1, by norm_num, fun _ _ _ => trivial⟩
    · by_cases hed : e = d
      · exact ⟨1, by norm_num, fun _ _ _ => Or.inl hed⟩
      · have hdis : Disjoint (K.edgeTrim hcont D e).centralCarrier
            (K.edgeTrim hcont D d).centralCarrier :=
          EdgeTrimData.disjoint_centralCarrier (T' := K.edgeTrim hcont D d)
            (K.edgeTrim hcont D e) hinj hed
        have hcompactE := (K.edgeTrim hcont D e).isCompact_centralCarrier hcont
        have hcompactD := (K.edgeTrim hcont D d).isCompact_centralCarrier hcont
        obtain ⟨ε, hε, hthick⟩ := hdis.exists_thickenings hcompactE hcompactD.isClosed
        refine ⟨ε, hε, fun δ hδ hδε => Or.inr ?_⟩
        exact hthick.mono (Metric.cthickening_subset_thickening' hε hδε _)
          (Metric.cthickening_subset_thickening' hε hδε _)
  obtain ⟨ε, hε, huniform⟩ := exists_pos_uniform_fintype' P hlocal
  let r := min (ε / 2) (D.radius / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos D.radius_pos)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrD : r < D.radius :=
    (min_le_right _ _).trans_lt (half_lt_self D.radius_pos)
  refine ⟨{
    radius := r
    radius_pos := hr
    radius_lt_vertex := hrD
    pairwise_disjoint := ?_ }⟩
  intro e d hed
  rcases huniform (some (e, d)) r hr hrε with heq | hdis
  · exact (hed heq).elim
  · exact hdis

namespace EdgeTrimData

theorem isPreconnected_centralCarrier {h : K.realization → Plane}
    (hcont : Continuous h) (D : K.VertexDiskControl h) (e : K.Edge) :
    IsPreconnected (K.edgeTrim hcont D e).centralCarrier := by
  apply IsPreconnected.image (convex_Icc _ _).isPreconnected
  exact (K.continuous_edgeCurve hcont e).continuousOn

theorem left_mem_centralCarrier {h : K.realization → Plane}
    (hcont : Continuous h) (D : K.VertexDiskControl h) (e : K.Edge) :
    K.edgeCurve h e (K.edgeTrim hcont D e).left ∈
      (K.edgeTrim hcont D e).centralCarrier :=
  ⟨_, ⟨le_rfl, (K.edgeTrim hcont D e).left_lt_right.le⟩, rfl⟩

theorem right_mem_centralCarrier {h : K.realization → Plane}
    (hcont : Continuous h) (D : K.VertexDiskControl h) (e : K.Edge) :
    K.edgeCurve h e (K.edgeTrim hcont D e).right ∈
      (K.edgeTrim hcont D e).centralCarrier :=
  ⟨_, ⟨(K.edgeTrim hcont D e).left_lt_right.le, le_rfl⟩, rfl⟩

end EdgeTrimData

/-- A polygonal replacement for one trimmed central intrinsic arc, kept inside its tube. -/
structure CentralPolygonalArc {h : K.realization → Plane} (hcont : Continuous h)
    (hinj : Function.Injective h) (D : K.VertexDiskControl h)
    (C : K.CentralTubeControl hcont hinj D) (e : K.Edge) where
  /-- The `data` declaration. -/
  data : BrokenLineData
    (Metric.thickening C.radius (K.edgeTrim hcont D e).centralCarrier)
  start_eq : data.start = K.edgeCurve h e (K.edgeTrim hcont D e).left
  finish_eq : data.finish = K.edgeCurve h e (K.edgeTrim hcont D e).right

theorem exists_centralPolygonalArc {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) : Nonempty (K.CentralPolygonalArc hcont hinj D C e) := by
  let A := (K.edgeTrim hcont D e).centralCarrier
  have hjoined : JoinedByBrokenLine (Metric.thickening C.radius A)
      (K.edgeCurve h e (K.edgeTrim hcont D e).left)
      (K.edgeCurve h e (K.edgeTrim hcont D e).right) := by
    apply brokenLine_in_thickening_of_preconnected
      (EdgeTrimData.isPreconnected_centralCarrier K hcont D e)
      (EdgeTrimData.left_mem_centralCarrier K hcont D e)
      (EdgeTrimData.right_mem_centralCarrier K hcont D e) C.radius_pos
  obtain ⟨B, hstart, hfinish⟩ := BrokenLineData.exists_data_of_joined hjoined
  exact ⟨⟨B, hstart, hfinish⟩⟩

/-- The `centralPolygonalArc` declaration. -/
noncomputable def centralPolygonalArc {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) : K.CentralPolygonalArc hcont hinj D C e :=
  Classical.choice (K.exists_centralPolygonalArc hcont hinj D C e)

namespace CentralPolygonalArc

variable {K : IntrinsicTwoComplex} {h : K.realization → Plane}
  {hcont : Continuous h} {hinj : Function.Injective h}
  {D : K.VertexDiskControl h} {C : K.CentralTubeControl hcont hinj D}
  {e : K.Edge}

theorem resolvedCarrier_subset_tube
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.data.resolvedCarrier ⊆
      Metric.thickening C.radius (K.edgeTrim hcont D e).centralCarrier := by
  apply A.data.resolvedCarrier_subset
  rw [A.start_eq]
  exact Metric.self_subset_thickening C.radius_pos _
    (EdgeTrimData.left_mem_centralCarrier K hcont D e)

theorem disjoint_resolvedCarrier {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.data.resolvedCarrier A'.data.resolvedCarrier :=
  (C.pairwise_disjoint e d hed).mono
    (A.resolvedCarrier_subset_tube.trans (Metric.thickening_subset_cthickening _ _))
    (A'.resolvedCarrier_subset_tube.trans (Metric.thickening_subset_cthickening _ _))

/-- A simple parameterization of the polygonal replacement, normalized to the unit interval. -/
structure Parameterization (A : K.CentralPolygonalArc hcont hinj D C e) where
  /-- The `source` declaration. -/
  source : PlaneComplex
  /-- The `map` declaration. -/
  map : Plane → Plane
  /-- The `curve` declaration. -/
  curve : ℝ → Plane
  source_support : source.support =
    segment ℝ (planePoint 0 0) (planePoint A.data.resolvedWalk.length 0)
  map_isPL : IsPLOn source map
  map_injectiveOn : Set.InjOn map source.support
  map_affineOn : ∀ s ∈ source.simplexes, IsAffineOn map (source.cellCarrier s)
  source_card_le_two : ∀ s ∈ source.simplexes, s.card ≤ 2
  source_vertex_mem : ∀ v, source.position v ∈ source.support
  curve_eq : ∀ t, curve t = map (planePoint (A.data.resolvedWalk.length * t) 0)
  continuousOn : ContinuousOn curve (Set.Icc (0 : ℝ) 1)
  injectiveOn : Set.InjOn curve (Set.Icc (0 : ℝ) 1)
  image_eq : curve '' Set.Icc (0 : ℝ) 1 = A.data.resolvedCarrier
  start_eq : curve 0 = A.data.start
  finish_eq : curve 1 = A.data.finish

theorem start_ne_finish (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.data.start ≠ A.data.finish := by
  have hleft : K.edgeCurve h e (K.edgeTrim hcont D e).left ∈
      Metric.closedBall (h (K.edgeFirstPoint e)) D.radius := by
    rw [Metric.mem_closedBall]
    exact (K.edgeTrim hcont D e).left_on_sphere.le
  have hright : K.edgeCurve h e (K.edgeTrim hcont D e).right ∈
      Metric.closedBall (h (K.edgeSecondPoint e)) D.radius := by
    rw [Metric.mem_closedBall]
    exact (K.edgeTrim hcont D e).right_on_sphere.le
  rw [A.start_eq, A.finish_eq]
  intro heq
  have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
    (K.edgeFirstUsed_ne_edgeSecondUsed e)
  exact Set.disjoint_left.mp
    (by simpa only [K.vertexPoint_edgeFirstUsed e, K.vertexPoint_edgeSecondUsed e] using hdis)
    hleft (heq ▸ hright)

theorem resolvedWalk_length_pos (A : K.CentralPolygonalArc hcont hinj D C e) :
    0 < A.data.resolvedWalk.length := by
  by_contra hnot
  have hzero : A.data.resolvedWalk.length = 0 := Nat.eq_zero_of_not_pos hnot
  apply A.start_ne_finish
  rw [← A.data.resolvedVertex_start, ← A.data.resolvedVertex_finish]
  congr 2
  exact Fin.ext (by simp [hzero])

theorem exists_parameterization (A : K.CentralPolygonalArc hcont hinj D C e) :
    Nonempty A.Parameterization := by
  obtain ⟨S, F, hSsupport, hpl, hSgraph, hFinj, himage, hstart, hfinish⟩ :=
    A.data.exists_PL_segment_model
  have hplS := hpl
  obtain ⟨L, hLsub, hLaffine⟩ := hpl
  let n : ℝ := A.data.resolvedWalk.length
  let axis : ℝ → Plane := fun t => planePoint (n * t) 0
  let curve : ℝ → Plane := fun t => F (axis t)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast A.resolvedWalk_length_pos
  have haxisLine : axis = AffineMap.lineMap (planePoint 0 0) (planePoint n 0) := by
    funext t
    ext k
    fin_cases k <;> simp [axis, planePoint, AffineMap.lineMap_apply_module, mul_comm]
  have haxisImage : axis '' Set.Icc (0 : ℝ) 1 =
      segment ℝ (planePoint 0 0) (planePoint n 0) := by
    rw [haxisLine, segment_eq_image_lineMap]
  have haxisMaps : Set.MapsTo axis (Set.Icc (0 : ℝ) 1) S.support := by
    rw [hSsupport]
    simpa [n] using Set.mapsTo_iff_image_subset.mpr haxisImage.le
  have haxisCont : Continuous axis := by
    rw [haxisLine]
    exact AffineMap.lineMap_continuous
  have hcurveCont : ContinuousOn curve (Set.Icc (0 : ℝ) 1) :=
    hplS.continuousOn.comp haxisCont.continuousOn haxisMaps
  have haxisInj : Set.InjOn axis (Set.Icc (0 : ℝ) 1) := by
    intro x _ y _ hxy
    have hcoord := congrArg (fun p : Plane => p 0) hxy
    change n * x = n * y at hcoord
    exact mul_left_cancel₀ hn.ne' hcoord
  have hcurveInj : Set.InjOn curve (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply haxisInj hx hy
    exact hFinj (haxisMaps hx) (haxisMaps hy) hxy
  have hcurveImage : curve '' Set.Icc (0 : ℝ) 1 = A.data.resolvedCarrier := by
    rw [show curve '' Set.Icc (0 : ℝ) 1 = F '' (axis '' Set.Icc (0 : ℝ) 1) by
      exact (Set.image_image F axis (Set.Icc (0 : ℝ) 1)).symm]
    rw [haxisImage, ← hSsupport, himage]
  refine ⟨{
    source := PlaneComplex.active L
    map := F
    curve := curve
    source_support := by rw [L.active_support, hLsub.1, hSsupport]
    map_isPL := by
      refine ⟨PlaneComplex.active L, PlaneComplex.Subdivides.refl _, ?_⟩
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    map_injectiveOn := by
      intro x hx y hy hxy
      apply hFinj
      · rw [← hLsub.1]
        simpa only [L.active_support] using hx
      · rw [← hLsub.1]
        simpa only [L.active_support] using hy
      · exact hxy
    map_affineOn := by
      intro s hs
      exact (L.active_cellCarrier s).symm ▸
        hLaffine (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    source_card_le_two := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := (PlaneComplex.active_subdivides_left hLsub).2 s hs
      exact PlaneComplex.card_le_two_of_cellCarrier_subset_face hs ht (hSgraph t ht) hst
    source_vertex_mem := by
      intro v
      change L.position v.1 ∈ (PlaneComplex.active L).support
      rw [L.active_support]
      exact v.2
    curve_eq := by intro t; rfl
    continuousOn := hcurveCont
    injectiveOn := hcurveInj
    image_eq := hcurveImage
    start_eq := ?_
    finish_eq := ?_ }⟩
  · simpa [curve, axis, n] using hstart
  · simpa [curve, axis, n] using hfinish

/-- The `parameterization` declaration. -/
noncomputable def parameterization (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.Parameterization :=
  Classical.choice A.exists_parameterization

/-- The ordered exits of the polygonal middle from the two endpoint disks. -/
noncomputable def exitData (A : K.CentralPolygonalArc hcont hinj D C e) :
    BoundaryExitData A.parameterization.curve
      (h (K.edgeFirstPoint e)) (h (K.edgeSecondPoint e)) D.radius := by
  apply Classical.choice
  apply exists_boundaryExitData D.radius_pos A.parameterization.continuousOn
  · rw [A.parameterization.start_eq, A.start_eq]
    exact (K.edgeTrim hcont D e).left_on_sphere
  · rw [A.parameterization.finish_eq, A.finish_eq]
    exact (K.edgeTrim hcont D e).right_on_sphere
  · simpa only [K.vertexPoint_edgeFirstUsed e, K.vertexPoint_edgeSecondUsed e] using
      D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
        (K.edgeFirstUsed_ne_edgeSecondUsed e)

/-- The `trimmedCarrier` declaration. -/
def trimmedCarrier (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  A.parameterization.curve '' Set.Icc A.exitData.left A.exitData.right

theorem trimmedCarrier_subset_resolvedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.trimmedCarrier ⊆ A.data.resolvedCarrier := by
  rw [← A.parameterization.image_eq]
  exact Set.image_mono fun _ ht =>
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩

theorem trimmedCarrier_avoids_first
    (A : K.CentralPolygonalArc hcont hinj D C e) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxleft : x ≠ A.parameterization.curve A.exitData.left) :
    x ∉ Metric.closedBall (h (K.edgeFirstPoint e)) D.radius := by
  obtain ⟨t, ht, rfl⟩ := hx
  apply A.exitData.after_left t
  · exact ⟨A.exitData.left_nonneg.trans ht.1,
      ht.2.trans A.exitData.right_le_one⟩
  · exact lt_of_le_of_ne ht.1 fun heq => hxleft (by rw [heq])

theorem trimmedCarrier_avoids_second
    (A : K.CentralPolygonalArc hcont hinj D C e) {x : Plane}
    (hx : x ∈ A.trimmedCarrier)
    (hxright : x ≠ A.parameterization.curve A.exitData.right) :
    x ∉ Metric.closedBall (h (K.edgeSecondPoint e)) D.radius := by
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases hleft : t = A.exitData.left
  · subst t
    have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
      (K.edgeFirstUsed_ne_edgeSecondUsed e)
    apply Set.disjoint_left.mp
      (by simpa only [K.vertexPoint_edgeFirstUsed e, K.vertexPoint_edgeSecondUsed e] using hdis)
    · rw [Metric.mem_closedBall]
      exact A.exitData.left_on_sphere.le
  · apply A.exitData.before_right t
    · exact ⟨A.exitData.left_nonneg.trans ht.1,
        ht.2.trans A.exitData.right_le_one⟩
    · exact lt_of_le_of_ne ht.1 (Ne.symm hleft)
    · exact lt_of_le_of_ne ht.2 fun heq => hxright (by rw [heq])

theorem trimmedCarrier_avoids_nonincident
    (A : K.CentralPolygonalArc hcont hinj D C e) (v : K.UsedVertex)
    (hv : v.1 ∉ e.1) :
    Disjoint (Metric.closedBall (h (K.vertexPoint v)) D.radius) A.trimmedCarrier := by
  apply (D.avoids_nonincident_edge v e hv).mono_right
  apply A.trimmedCarrier_subset_resolvedCarrier.trans
  apply A.resolvedCarrier_subset_tube.trans
  apply (Metric.thickening_subset_cthickening_of_le C.radius_lt_vertex.le
    (K.edgeTrim hcont D e).centralCarrier).trans
  apply Metric.cthickening_subset_of_subset
  exact (K.edgeTrim hcont D e).centralCarrier_subset_mapped_openEdge.trans
    (Set.image_subset_range _ _)

/-- The `leftEndpoint` declaration. -/
noncomputable def leftEndpoint
    (A : K.CentralPolygonalArc hcont hinj D C e) : Plane :=
  A.parameterization.curve A.exitData.left

/-- The `rightEndpoint` declaration. -/
noncomputable def rightEndpoint
    (A : K.CentralPolygonalArc hcont hinj D C e) : Plane :=
  A.parameterization.curve A.exitData.right

/-- The `leftSpoke` declaration. -/
noncomputable def leftSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  segment ℝ (h (K.edgeFirstPoint e)) A.leftEndpoint

/-- The `rightSpoke` declaration. -/
noncomputable def rightSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  segment ℝ A.rightEndpoint (h (K.edgeSecondPoint e))

/-- The complete replacement carrier of one intrinsic edge. -/
noncomputable def completeCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  A.leftSpoke ∪ A.trimmedCarrier ∪ A.rightSpoke

/-- The `leftOpenSpoke` declaration. -/
noncomputable def leftOpenSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  A.leftSpoke \ {h (K.edgeFirstPoint e)}

/-- The `rightOpenSpoke` declaration. -/
noncomputable def rightOpenSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  A.rightSpoke \ {h (K.edgeSecondPoint e)}

/-- The `interiorCarrier` declaration. -/
noncomputable def interiorCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) : Set Plane :=
  A.leftOpenSpoke ∪ A.trimmedCarrier ∪ A.rightOpenSpoke

theorem leftEndpoint_mem_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.leftEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.left, ⟨le_rfl, A.exitData.left_lt_right.le⟩, rfl⟩

theorem rightEndpoint_mem_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.rightEndpoint ∈ A.trimmedCarrier :=
  ⟨A.exitData.right, ⟨A.exitData.left_lt_right.le, le_rfl⟩, rfl⟩

theorem leftEndpoint_on_sphere
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    dist A.leftEndpoint (h (K.edgeFirstPoint e)) = D.radius :=
  A.exitData.left_on_sphere

theorem rightEndpoint_on_sphere
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    dist A.rightEndpoint (h (K.edgeSecondPoint e)) = D.radius :=
  A.exitData.right_on_sphere

/-- The trimmed polygonal middle as a path. -/
noncomputable def middlePath (A : K.CentralPolygonalArc hcont hinj D C e) :
    Path A.leftEndpoint A.rightEndpoint where
  toFun t := A.parameterization.curve
    (Path.segment A.exitData.left A.exitData.right t)
  continuous_toFun := by
    apply A.parameterization.continuousOn.comp_continuous
    · exact (Path.segment A.exitData.left A.exitData.right).continuous
    · intro t
      have ht : Path.segment A.exitData.left A.exitData.right t ∈
          segment ℝ A.exitData.left A.exitData.right := by
        rw [← Path.range_segment]
        exact ⟨t, rfl⟩
      rw [segment_eq_Icc A.exitData.left_lt_right.le] at ht
      exact ⟨A.exitData.left_nonneg.trans ht.1,
        ht.2.trans A.exitData.right_le_one⟩
  source' := by simp [leftEndpoint]
  target' := by simp [rightEndpoint]

theorem range_middlePath (A : K.CentralPolygonalArc hcont hinj D C e) :
    Set.range A.middlePath = A.trimmedCarrier := by
  rw [trimmedCarrier]
  have hsegment : segment ℝ A.exitData.left A.exitData.right =
      Set.Icc A.exitData.left A.exitData.right :=
    segment_eq_Icc A.exitData.left_lt_right.le
  rw [← hsegment, ← Path.range_segment]
  ext x
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Path.segment A.exitData.left A.exitData.right t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- The complete polygonal replacement path for one intrinsic edge. -/
noncomputable def completePath (A : K.CentralPolygonalArc hcont hinj D C e) :
    Path (h (K.edgeFirstPoint e)) (h (K.edgeSecondPoint e)) :=
  (Path.segment (h (K.edgeFirstPoint e)) A.leftEndpoint).trans
    (A.middlePath.trans (Path.segment A.rightEndpoint (h (K.edgeSecondPoint e))))

theorem range_completePath (A : K.CentralPolygonalArc hcont hinj D C e) :
    Set.range A.completePath = A.completeCarrier := by
  rw [completePath, Path.trans_range, Path.trans_range, Path.range_segment,
    Path.range_segment, A.range_middlePath]
  simp [completeCarrier, leftSpoke, rightSpoke, Set.union_assoc]

theorem middlePath_injective (A : K.CentralPolygonalArc hcont hinj D C e) :
    Function.Injective A.middlePath := by
  intro s t hst
  have hs : Path.segment A.exitData.left A.exitData.right s ∈
      Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨s, rfl⟩
  have ht : Path.segment A.exitData.left A.exitData.right t ∈
      Set.Icc A.exitData.left A.exitData.right := by
    rw [← segment_eq_Icc A.exitData.left_lt_right.le, ← Path.range_segment]
    exact ⟨t, rfl⟩
  have hparam := A.parameterization.injectiveOn
    ⟨A.exitData.left_nonneg.trans hs.1, hs.2.trans A.exitData.right_le_one⟩
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩ hst
  exact Path.segment_injective_of_ne A.exitData.left_lt_right.ne hparam

theorem disjoint_trimmedCarrier {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.trimmedCarrier A'.trimmedCarrier :=
  (CentralPolygonalArc.disjoint_resolvedCarrier (A' := A') A hed).mono
    A.trimmedCarrier_subset_resolvedCarrier A'.trimmedCarrier_subset_resolvedCarrier

theorem leftEndpoint_ne_leftEndpoint {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    A.leftEndpoint ≠ A'.leftEndpoint := by
  intro heq
  have hmem : A.leftEndpoint ∈ A'.trimmedCarrier := heq ▸ A'.leftEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (A' := A') hed)
    A.leftEndpoint_mem_trimmedCarrier hmem

theorem leftEndpoint_ne_rightEndpoint {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    A.leftEndpoint ≠ A'.rightEndpoint := by
  intro heq
  have hmem : A.leftEndpoint ∈ A'.trimmedCarrier := heq ▸ A'.rightEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (A' := A') hed)
    A.leftEndpoint_mem_trimmedCarrier hmem

theorem rightEndpoint_ne_leftEndpoint {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    A.rightEndpoint ≠ A'.leftEndpoint := by
  intro heq
  have hmem : A.rightEndpoint ∈ A'.trimmedCarrier := heq ▸ A'.leftEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (A' := A') hed)
    A.rightEndpoint_mem_trimmedCarrier hmem

theorem rightEndpoint_ne_rightEndpoint {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    A.rightEndpoint ≠ A'.rightEndpoint := by
  intro heq
  have hmem : A.rightEndpoint ∈ A'.trimmedCarrier := heq ▸ A'.rightEndpoint_mem_trimmedCarrier
  exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (A' := A') hed)
    A.rightEndpoint_mem_trimmedCarrier hmem

theorem leftSpoke_subset_disk (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.leftSpoke ⊆ Metric.closedBall (h (K.edgeFirstPoint e)) D.radius := by
  apply (convex_closedBall _ _).segment_subset
  · exact Metric.mem_closedBall_self D.radius_pos.le
  · rw [Metric.mem_closedBall]
    simpa [dist_comm] using A.leftEndpoint_on_sphere.le

theorem rightSpoke_subset_disk (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.rightSpoke ⊆ Metric.closedBall (h (K.edgeSecondPoint e)) D.radius := by
  apply (convex_closedBall _ _).segment_subset
  · rw [Metric.mem_closedBall]
    exact A.rightEndpoint_on_sphere.le
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem leftSpoke_inter_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.leftSpoke ∩ A.trimmedCarrier = {A.leftEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_first hxTrim hx (A.leftSpoke_subset_disk hxSpoke)
  · rintro x rfl
    exact ⟨right_mem_segment ℝ _ _, A.leftEndpoint_mem_trimmedCarrier⟩

theorem rightSpoke_inter_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.rightSpoke ∩ A.trimmedCarrier = {A.rightEndpoint} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxSpoke, hxTrim⟩
    by_contra hx
    exact A.trimmedCarrier_avoids_second hxTrim hx (A.rightSpoke_subset_disk hxSpoke)
  · rintro x rfl
    exact ⟨left_mem_segment ℝ _ _, A.rightEndpoint_mem_trimmedCarrier⟩

theorem leftSpoke_disjoint_rightSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    Disjoint A.leftSpoke A.rightSpoke := by
  have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
    (K.edgeFirstUsed_ne_edgeSecondUsed e)
  have hdis' : Disjoint
      (Metric.closedBall (h (K.edgeFirstPoint e)) D.radius)
      (Metric.closedBall (h (K.edgeSecondPoint e)) D.radius) := by
    simpa only [K.vertexPoint_edgeFirstUsed e,
      K.vertexPoint_edgeSecondUsed e] using hdis
  exact hdis'.mono A.leftSpoke_subset_disk A.rightSpoke_subset_disk

/-- Every complete intrinsic replacement edge is a simple path. -/
theorem completePath_injective (A : K.CentralPolygonalArc hcont hinj D C e) :
    Function.Injective A.completePath := by
  let first := Path.segment (h (K.edgeFirstPoint e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (h (K.edgeSecondPoint e))
  have hfirstNe : h (K.edgeFirstPoint e) ≠ A.leftEndpoint := by
    intro heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq, dist_self] at hs
    linarith [D.radius_pos]
  have hlastNe : A.rightEndpoint ≠ h (K.edgeSecondPoint e) := by
    intro heq
    have hs := A.rightEndpoint_on_sphere
    rw [heq, dist_self] at hs
    linarith [D.radius_pos]
  have hfirstInj : Function.Injective first := Path.segment_injective_of_ne hfirstNe
  have hlastInj : Function.Injective last := Path.segment_injective_of_ne hlastNe
  have hmiddleLastInter : Set.range A.middlePath ∩ Set.range last = {A.rightEndpoint} := by
    rw [A.range_middlePath, Path.range_segment, Set.inter_comm]
    exact A.rightSpoke_inter_trimmedCarrier
  have htailInj : Function.Injective (A.middlePath.trans last) :=
    Path.trans_injective_of_range_inter A.middlePath last A.middlePath_injective
      hlastInj hmiddleLastInter
  have hfirstMiddleInter : Set.range first ∩ Set.range A.middlePath = {A.leftEndpoint} := by
    rw [Path.range_segment, A.range_middlePath]
    exact A.leftSpoke_inter_trimmedCarrier
  have hfirstLast : Disjoint (Set.range first) (Set.range last) := by
    rw [Path.range_segment, Path.range_segment]
    exact A.leftSpoke_disjoint_rightSpoke
  have hfirstTailInter : Set.range first ∩ Set.range (A.middlePath.trans last) =
      {A.leftEndpoint} := by
    rw [Path.trans_range, Set.inter_union_distrib_left, hfirstMiddleInter,
      Set.disjoint_iff_inter_eq_empty.mp hfirstLast, Set.union_empty]
  exact Path.trans_injective_of_range_inter first (A.middlePath.trans last)
    hfirstInj htailInj hfirstTailInter

theorem firstCenter_not_mem_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    h (K.edgeFirstPoint e) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_first hx
  · intro heq
    have heq' : h (K.edgeFirstPoint e) = A.leftEndpoint := by
      simpa [leftEndpoint] using heq
    have hs := A.leftEndpoint_on_sphere
    rw [← heq', dist_self] at hs
    linarith [D.radius_pos]
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem secondCenter_not_mem_trimmedCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    h (K.edgeSecondPoint e) ∉ A.trimmedCarrier := by
  intro hx
  apply A.trimmedCarrier_avoids_second hx
  · intro heq
    have heq' : h (K.edgeSecondPoint e) = A.rightEndpoint := by
      simpa [rightEndpoint] using heq
    have hs := A.rightEndpoint_on_sphere
    rw [← heq', dist_self] at hs
    linarith [D.radius_pos]
  · exact Metric.mem_closedBall_self D.radius_pos.le

theorem firstCenter_not_mem_rightSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    h (K.edgeFirstPoint e) ∉ A.rightSpoke := by
  intro hx
  have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
    (K.edgeFirstUsed_ne_edgeSecondUsed e)
  exact Set.disjoint_left.mp
    (by simpa only [K.vertexPoint_edgeFirstUsed e,
      K.vertexPoint_edgeSecondUsed e] using hdis)
    (Metric.mem_closedBall_self D.radius_pos.le) (A.rightSpoke_subset_disk hx)

theorem secondCenter_not_mem_leftSpoke
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    h (K.edgeSecondPoint e) ∉ A.leftSpoke := by
  intro hx
  have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed e)
    (K.edgeFirstUsed_ne_edgeSecondUsed e)
  exact Set.disjoint_left.mp
    (by simpa only [K.vertexPoint_edgeFirstUsed e,
      K.vertexPoint_edgeSecondUsed e] using hdis)
    (A.leftSpoke_subset_disk hx) (Metric.mem_closedBall_self D.radius_pos.le)

theorem completeCarrier_sdiff_endpoints
    (A : K.CentralPolygonalArc hcont hinj D C e) :
    A.completeCarrier \ {h (K.edgeFirstPoint e), h (K.edgeSecondPoint e)} =
      A.interiorCarrier := by
  ext x
  simp only [completeCarrier, interiorCarrier, leftOpenSpoke, rightOpenSpoke,
    Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  constructor
  · rintro ⟨(hL | hT) | hR, hne⟩
    · exact Or.inl (Or.inl ⟨hL, fun hx => hne (Or.inl hx)⟩)
    · exact Or.inl (Or.inr hT)
    · exact Or.inr ⟨hR, fun hx => hne (Or.inr hx)⟩
  · rintro ((⟨hL, hx0⟩ | hT) | ⟨hR, hx1⟩)
    · refine ⟨Or.inl (Or.inl hL), ?_⟩
      rintro (hx | hx)
      · exact hx0 hx
      · exact A.secondCenter_not_mem_leftSpoke (hx ▸ hL)
    · refine ⟨Or.inl (Or.inr hT), ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_trimmedCarrier (hx ▸ hT)
      · exact A.secondCenter_not_mem_trimmedCarrier (hx ▸ hT)
    · refine ⟨Or.inr hR, ?_⟩
      rintro (hx | hx)
      · exact A.firstCenter_not_mem_rightSpoke (hx ▸ hR)
      · exact hx1 hx

theorem disjoint_leftSpoke_trimmedCarrier {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.leftSpoke A'.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxBall := A.leftSpoke_subset_disk hxSpoke
  by_cases hv : K.edgeFirst e ∈ d.1
  · rw [K.edge_eq_pair d] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hp : K.edgeFirstPoint e = K.edgeFirstPoint d := by
        rw [← K.vertexPoint_edgeFirstUsed e, ← K.vertexPoint_edgeFirstUsed d]
        congr 1
        exact Subtype.ext hv
      have hxEq : x = A'.leftEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_first hxTrim hne
        simpa only [hp] using hxBall
      have hxSphere : dist x (h (K.edgeFirstPoint e)) = D.radius := by
        rw [hxEq, hp]
        exact A'.leftEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.leftEndpoint_on_sphere
          hxSpoke hxSphere
      exact A.leftEndpoint_ne_leftEndpoint (A' := A') hed (hxOwn.symm.trans hxEq)
    · have hp : K.edgeFirstPoint e = K.edgeSecondPoint d := by
        rw [← K.vertexPoint_edgeFirstUsed e, ← K.vertexPoint_edgeSecondUsed d]
        congr 1
        exact Subtype.ext hv
      have hxEq : x = A'.rightEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_second hxTrim hne
        simpa only [hp] using hxBall
      have hxSphere : dist x (h (K.edgeFirstPoint e)) = D.radius := by
        rw [hxEq, hp]
        exact A'.rightEndpoint_on_sphere
      have hxOwn : x = A.leftEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.leftEndpoint_on_sphere
          hxSpoke hxSphere
      exact A.leftEndpoint_ne_rightEndpoint (A' := A') hed (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp
      (A'.trimmedCarrier_avoids_nonincident (K.edgeFirstUsed e) hv)
      (by simpa only [K.vertexPoint_edgeFirstUsed e] using hxBall) hxTrim

theorem disjoint_rightSpoke_trimmedCarrier {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.rightSpoke A'.trimmedCarrier := by
  rw [Set.disjoint_left]
  intro x hxSpoke hxTrim
  have hxBall := A.rightSpoke_subset_disk hxSpoke
  have hxSpoke' : x ∈ segment ℝ (h (K.edgeSecondPoint e)) A.rightEndpoint := by
    rwa [segment_symm]
  by_cases hv : K.edgeSecond e ∈ d.1
  · rw [K.edge_eq_pair d] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · have hp : K.edgeSecondPoint e = K.edgeFirstPoint d := by
        rw [← K.vertexPoint_edgeSecondUsed e, ← K.vertexPoint_edgeFirstUsed d]
        congr 1
        exact Subtype.ext hv
      have hxEq : x = A'.leftEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_first hxTrim hne
        simpa only [hp] using hxBall
      have hxSphere : dist x (h (K.edgeSecondPoint e)) = D.radius := by
        rw [hxEq, hp]
        exact A'.leftEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.rightEndpoint_on_sphere
          hxSpoke' hxSphere
      exact A.rightEndpoint_ne_leftEndpoint (A' := A') hed (hxOwn.symm.trans hxEq)
    · have hp : K.edgeSecondPoint e = K.edgeSecondPoint d := by
        rw [← K.vertexPoint_edgeSecondUsed e, ← K.vertexPoint_edgeSecondUsed d]
        congr 1
        exact Subtype.ext hv
      have hxEq : x = A'.rightEndpoint := by
        by_contra hne
        apply A'.trimmedCarrier_avoids_second hxTrim hne
        simpa only [hp] using hxBall
      have hxSphere : dist x (h (K.edgeSecondPoint e)) = D.radius := by
        rw [hxEq, hp]
        exact A'.rightEndpoint_on_sphere
      have hxOwn : x = A.rightEndpoint :=
        eq_endpoint_of_mem_radial_segment D.radius_pos A.rightEndpoint_on_sphere
          hxSpoke' hxSphere
      exact A.rightEndpoint_ne_rightEndpoint (A' := A') hed (hxOwn.symm.trans hxEq)
  · exact Set.disjoint_left.mp
      (A'.trimmedCarrier_avoids_nonincident (K.edgeSecondUsed e) hv)
      (by simpa only [K.vertexPoint_edgeSecondUsed e] using hxBall) hxTrim

theorem disjoint_leftOpenSpoke_leftOpenSpoke {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.leftOpenSpoke A'.leftOpenSpoke := by
  by_cases hv : K.edgeFirstUsed e = K.edgeFirstUsed d
  · have hp : K.edgeFirstPoint e = K.edgeFirstPoint d := by
      rw [← K.vertexPoint_edgeFirstUsed e, ← K.vertexPoint_edgeFirstUsed d, hv]
    simpa [leftOpenSpoke, leftSpoke, hp] using
      disjoint_radial_segments_away_center D.radius_pos A.leftEndpoint_on_sphere
        (by simpa only [hp] using A'.leftEndpoint_on_sphere)
        (A.leftEndpoint_ne_leftEndpoint (A' := A') hed)
  · have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeFirstUsed d) hv
    apply hdis.mono
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeFirstUsed e] using A.leftSpoke_subset_disk)
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeFirstUsed d] using A'.leftSpoke_subset_disk)

theorem disjoint_leftOpenSpoke_rightOpenSpoke {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.leftOpenSpoke A'.rightOpenSpoke := by
  by_cases hv : K.edgeFirstUsed e = K.edgeSecondUsed d
  · have hp : K.edgeFirstPoint e = K.edgeSecondPoint d := by
      rw [← K.vertexPoint_edgeFirstUsed e, ← K.vertexPoint_edgeSecondUsed d, hv]
    simpa [leftOpenSpoke, leftSpoke, rightOpenSpoke, rightSpoke, hp, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.leftEndpoint_on_sphere
        (by simpa only [hp] using A'.rightEndpoint_on_sphere)
        (A.leftEndpoint_ne_rightEndpoint (A' := A') hed)
  · have hdis := D.vertices_disjoint (K.edgeFirstUsed e) (K.edgeSecondUsed d) hv
    apply hdis.mono
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeFirstUsed e] using A.leftSpoke_subset_disk)
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeSecondUsed d] using A'.rightSpoke_subset_disk)

theorem disjoint_rightOpenSpoke_leftOpenSpoke {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.rightOpenSpoke A'.leftOpenSpoke := by
  by_cases hv : K.edgeSecondUsed e = K.edgeFirstUsed d
  · have hp : K.edgeSecondPoint e = K.edgeFirstPoint d := by
      rw [← K.vertexPoint_edgeSecondUsed e, ← K.vertexPoint_edgeFirstUsed d, hv]
    simpa [rightOpenSpoke, rightSpoke, leftOpenSpoke, leftSpoke, hp, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.rightEndpoint_on_sphere
        (by simpa only [hp] using A'.leftEndpoint_on_sphere)
        (A.rightEndpoint_ne_leftEndpoint (A' := A') hed)
  · have hdis := D.vertices_disjoint (K.edgeSecondUsed e) (K.edgeFirstUsed d) hv
    apply hdis.mono
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeSecondUsed e] using A.rightSpoke_subset_disk)
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeFirstUsed d] using A'.leftSpoke_subset_disk)

theorem disjoint_rightOpenSpoke_rightOpenSpoke {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.rightOpenSpoke A'.rightOpenSpoke := by
  by_cases hv : K.edgeSecondUsed e = K.edgeSecondUsed d
  · have hp : K.edgeSecondPoint e = K.edgeSecondPoint d := by
      rw [← K.vertexPoint_edgeSecondUsed e, ← K.vertexPoint_edgeSecondUsed d, hv]
    simpa [rightOpenSpoke, rightSpoke, hp, segment_symm] using
      disjoint_radial_segments_away_center D.radius_pos A.rightEndpoint_on_sphere
        (by simpa only [hp] using A'.rightEndpoint_on_sphere)
        (A.rightEndpoint_ne_rightEndpoint (A' := A') hed)
  · have hdis := D.vertices_disjoint (K.edgeSecondUsed e) (K.edgeSecondUsed d) hv
    apply hdis.mono
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeSecondUsed e] using A.rightSpoke_subset_disk)
    · exact Set.sdiff_subset.trans (by
        simpa only [K.vertexPoint_edgeSecondUsed d] using A'.rightSpoke_subset_disk)

/-- Distinct intrinsic replacement edges have disjoint relative interiors. -/
theorem disjoint_interiorCarrier {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d) :
    Disjoint A.interiorCarrier A'.interiorCarrier := by
  have hLT' : Disjoint A.leftOpenSpoke A'.trimmedCarrier :=
    (A.disjoint_leftSpoke_trimmedCarrier (A' := A') hed).mono_left Set.sdiff_subset
  have hRT' : Disjoint A.rightOpenSpoke A'.trimmedCarrier :=
    (A.disjoint_rightSpoke_trimmedCarrier (A' := A') hed).mono_left Set.sdiff_subset
  have hTL' : Disjoint A.trimmedCarrier A'.leftOpenSpoke :=
    ((A'.disjoint_leftSpoke_trimmedCarrier (A' := A) hed.symm).mono_left
      Set.sdiff_subset).symm
  have hTR' : Disjoint A.trimmedCarrier A'.rightOpenSpoke :=
    ((A'.disjoint_rightSpoke_trimmedCarrier (A' := A) hed.symm).mono_left
      Set.sdiff_subset).symm
  rw [Set.disjoint_left]
  intro x hx hx'
  change x ∈ (A.leftOpenSpoke ∪ A.trimmedCarrier) ∪ A.rightOpenSpoke at hx
  change x ∈ (A'.leftOpenSpoke ∪ A'.trimmedCarrier) ∪ A'.rightOpenSpoke at hx'
  rcases hx with (hL | hT) | hR <;> rcases hx' with (hL' | hT') | hR'
  · exact Set.disjoint_left.mp (A.disjoint_leftOpenSpoke_leftOpenSpoke
      (A' := A') hed) hL hL'
  · exact Set.disjoint_left.mp hLT' hL hT'
  · exact Set.disjoint_left.mp (A.disjoint_leftOpenSpoke_rightOpenSpoke
      (A' := A') hed) hL hR'
  · exact Set.disjoint_left.mp hTL' hT hL'
  · exact Set.disjoint_left.mp (A.disjoint_trimmedCarrier (A' := A') hed) hT hT'
  · exact Set.disjoint_left.mp hTR' hT hR'
  · exact Set.disjoint_left.mp (A.disjoint_rightOpenSpoke_leftOpenSpoke
      (A' := A') hed) hR hL'
  · exact Set.disjoint_left.mp hRT' hR hT'
  · exact Set.disjoint_left.mp (A.disjoint_rightOpenSpoke_rightOpenSpoke
      (A' := A') hed) hR hR'

theorem completeCarrier_avoids_nonincident
    (A : K.CentralPolygonalArc hcont hinj D C e) (v : K.UsedVertex)
    (hv : v.1 ∉ e.1) :
    Disjoint (Metric.closedBall (h (K.vertexPoint v)) D.radius) A.completeCarrier := by
  have hvFirst : v ≠ K.edgeFirstUsed e := by
    intro heq
    apply hv
    have hval : v.1 = K.edgeFirst e := congrArg Subtype.val heq
    rw [hval]
    exact K.edgeFirst_mem e
  have hvSecond : v ≠ K.edgeSecondUsed e := by
    intro heq
    apply hv
    have hval : v.1 = K.edgeSecond e := congrArg Subtype.val heq
    rw [hval]
    exact K.edgeSecond_mem e
  rw [Set.disjoint_left]
  intro x hxBall hxCarrier
  rcases hxCarrier with (hxLeft | hxTrim) | hxRight
  · exact Set.disjoint_left.mp (D.vertices_disjoint v (K.edgeFirstUsed e) hvFirst)
      hxBall (by simpa only [K.vertexPoint_edgeFirstUsed e] using
        A.leftSpoke_subset_disk hxLeft)
  · exact Set.disjoint_left.mp (A.trimmedCarrier_avoids_nonincident v hv)
      hxBall hxTrim
  · exact Set.disjoint_left.mp (D.vertices_disjoint v (K.edgeSecondUsed e) hvSecond)
      hxBall (by simpa only [K.vertexPoint_edgeSecondUsed e] using
        A.rightSpoke_subset_disk hxRight)

/-- The image of either abstract endpoint belongs to its replacement edge carrier. -/
theorem vertex_mem_completeCarrier
    (A : K.CentralPolygonalArc hcont hinj D C e) (v : K.UsedVertex)
    (hv : v.1 ∈ e.1) : h (K.vertexPoint v) ∈ A.completeCarrier := by
  rw [K.edge_eq_pair e] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · have hp : K.vertexPoint v = K.edgeFirstPoint e := by
      apply Subtype.ext
      simp [vertexPoint, edgeFirstPoint, edgeVertexPoint, hv]
    rw [hp]
    exact Or.inl (Or.inl (left_mem_segment ℝ _ _))
  · have hp : K.vertexPoint v = K.edgeSecondPoint e := by
      apply Subtype.ext
      simp [vertexPoint, edgeSecondPoint, edgeVertexPoint, hv]
    rw [hp]
    exact Or.inr (right_mem_segment ℝ _ _)

/-- Distinct replacement edges can meet only at the image of an abstract vertex belonging to
both edges.  This is the exact face-to-face statement behind the polygonal boundary of every
intrinsic triangle. -/
theorem exists_shared_vertex_of_mem_completeCarriers {d : K.Edge}
    {A' : K.CentralPolygonalArc hcont hinj D C d}
    (A : K.CentralPolygonalArc hcont hinj D C e) (hed : e ≠ d)
    {x : Plane} (hx : x ∈ A.completeCarrier) (hx' : x ∈ A'.completeCarrier) :
    ∃ v : K.UsedVertex,
      v.1 ∈ (e.1 ∩ d.1 : Finset K.Vertex) ∧ x = h (K.vertexPoint v) := by
  have hend : x = h (K.edgeFirstPoint e) ∨
      x = h (K.edgeSecondPoint e) ∨
      x = h (K.edgeFirstPoint d) ∨ x = h (K.edgeSecondPoint d) := by
    by_contra hn
    push Not at hn
    have hxInt : x ∈ A.interiorCarrier := by
      rw [← A.completeCarrier_sdiff_endpoints]
      exact ⟨hx, by simp [hn.1, hn.2.1]⟩
    have hxInt' : x ∈ A'.interiorCarrier := by
      rw [← A'.completeCarrier_sdiff_endpoints]
      exact ⟨hx', by simp [hn.2.2.1, hn.2.2.2]⟩
    exact Set.disjoint_left.mp (A.disjoint_interiorCarrier (A' := A') hed)
      hxInt hxInt'
  rcases hend with hfirst | hsecond | hfirst' | hsecond'
  · let v := K.edgeFirstUsed e
    have hvd : v.1 ∈ d.1 := by
      by_contra hvd
      exact Set.disjoint_left.mp (A'.completeCarrier_avoids_nonincident v hvd)
        (by simpa [v, K.vertexPoint_edgeFirstUsed e, hfirst] using
          (Metric.mem_closedBall_self D.radius_pos.le :
            h (K.edgeFirstPoint e) ∈ Metric.closedBall (h (K.edgeFirstPoint e)) D.radius))
        hx'
    refine ⟨v, Finset.mem_inter.mpr ⟨K.edgeFirst_mem e, hvd⟩, ?_⟩
    simpa [v, K.vertexPoint_edgeFirstUsed e] using hfirst
  · let v := K.edgeSecondUsed e
    have hvd : v.1 ∈ d.1 := by
      by_contra hvd
      exact Set.disjoint_left.mp (A'.completeCarrier_avoids_nonincident v hvd)
        (by simpa [v, K.vertexPoint_edgeSecondUsed e, hsecond] using
          (Metric.mem_closedBall_self D.radius_pos.le :
            h (K.edgeSecondPoint e) ∈ Metric.closedBall (h (K.edgeSecondPoint e)) D.radius))
        hx'
    refine ⟨v, Finset.mem_inter.mpr ⟨K.edgeSecond_mem e, hvd⟩, ?_⟩
    simpa [v, K.vertexPoint_edgeSecondUsed e] using hsecond
  · let v := K.edgeFirstUsed d
    have hve : v.1 ∈ e.1 := by
      by_contra hve
      exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hve)
        (by simpa [v, K.vertexPoint_edgeFirstUsed d, hfirst'] using
          (Metric.mem_closedBall_self D.radius_pos.le :
            h (K.edgeFirstPoint d) ∈ Metric.closedBall (h (K.edgeFirstPoint d)) D.radius))
        hx
    refine ⟨v, Finset.mem_inter.mpr ⟨hve, K.edgeFirst_mem d⟩, ?_⟩
    simpa [v, K.vertexPoint_edgeFirstUsed d] using hfirst'
  · let v := K.edgeSecondUsed d
    have hve : v.1 ∈ e.1 := by
      by_contra hve
      exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hve)
        (by simpa [v, K.vertexPoint_edgeSecondUsed d, hsecond'] using
          (Metric.mem_closedBall_self D.radius_pos.le :
            h (K.edgeSecondPoint d) ∈ Metric.closedBall (h (K.edgeSecondPoint d)) D.radius))
        hx
    refine ⟨v, Finset.mem_inter.mpr ⟨hve, K.edgeSecond_mem d⟩, ?_⟩
    simpa [v, K.vertexPoint_edgeSecondUsed d] using hsecond'

end CentralPolygonalArc

/-- The selected polygonal replacement for an intrinsic edge. -/
noncomputable def replacementArc {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) : K.CentralPolygonalArc hcont hinj D C e :=
  K.centralPolygonalArc hcont hinj D C e

/-- Consecutive replacement edges around one intrinsic face meet exactly at the image of their
shared cyclic vertex. -/
theorem faceReplacementCarrier_inter_next {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (t : K.Face) (i : ZMod 3) :
    (K.replacementArc hcont hinj D C (K.faceEdge t i)).completeCarrier ∩
        (K.replacementArc hcont hinj D C (K.faceEdge t (i + 1))).completeCarrier =
      {h (K.vertexPoint (K.faceUsedVertex t (i + 1)))} := by
  let A := K.replacementArc hcont hinj D C (K.faceEdge t i)
  let A' := K.replacementArc hcont hinj D C (K.faceEdge t (i + 1))
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hx'⟩
    obtain ⟨v, hv, hxv⟩ := A.exists_shared_vertex_of_mem_completeCarriers
      (A' := A') (K.faceEdge_ne_next t i) hx hx'
    have hv' : v.1 = K.faceVertex t (i + 1) := by
      have hvMem : v.1 ∈
          (K.faceEdge t i).1 ∩ (K.faceEdge t (i + 1)).1 := hv
      rw [K.faceEdge_inter_next t i] at hvMem
      exact Finset.mem_singleton.mp hvMem
    have hvUsed : v = K.faceUsedVertex t (i + 1) := Subtype.ext hv'
    rw [Set.mem_singleton_iff, hxv, hvUsed]
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    constructor
    · apply A.vertex_mem_completeCarrier
      simp [IntrinsicTwoComplex.faceUsedVertex]
    · apply A'.vertex_mem_completeCarrier
      simp [IntrinsicTwoComplex.faceUsedVertex, add_assoc]

/-- A point is an active graph vertex when it is a canonical used-vertex point. -/
def IsGraphVertexPoint (x : K.realization) : Prop :=
  ∃ v : K.UsedVertex, x = K.vertexPoint v

/-- The unique unit-interval parameter of a point on an intrinsic edge. -/
noncomputable def edgeParameter (e : K.Edge) (x : K.realization)
    (hx : x ∈ K.faceCarrier e.1) : Set.Icc (0 : ℝ) 1 :=
  Classical.choose (show x ∈ Set.range (K.edgePath e) by
    rwa [K.range_edgePath e])

theorem edgePath_edgeParameter (e : K.Edge) (x : K.realization)
    (hx : x ∈ K.faceCarrier e.1) :
    K.edgePath e (K.edgeParameter e x hx) = x :=
  Classical.choose_spec (show x ∈ Set.range (K.edgePath e) by
    rwa [K.range_edgePath e])

theorem edgeParameter_eq_secondCoordinate (e : K.Edge) (x : K.realization)
    (hx : x ∈ K.faceCarrier e.1) :
    (K.edgeParameter e x hx : ℝ) = x.1 (K.edgeSecond e) := by
  have hcoord := congrArg (fun y : K.realization => y.1 (K.edgeSecond e))
    (K.edgePath_edgeParameter e x hx)
  simpa using hcoord

theorem edgeParameter_mem_open_of_not_vertex (e : K.Edge) (x : K.realization)
    (hx : x ∈ K.faceCarrier e.1) (hnv : ¬K.IsGraphVertexPoint x) :
    0 < (K.edgeParameter e x hx : ℝ) ∧
      (K.edgeParameter e x hx : ℝ) < 1 := by
  let r := K.edgeParameter e x hx
  have hr := r.2
  constructor
  · apply lt_of_le_of_ne hr.1
    intro heq
    have hr0 : r = ⟨0, by simp⟩ := Subtype.ext heq.symm
    change K.edgeParameter e x hx = ⟨0, by simp⟩ at hr0
    apply hnv
    refine ⟨K.edgeFirstUsed e, ?_⟩
    rw [← K.edgePath_edgeParameter e x hx, hr0, K.edgePath_zero,
      K.vertexPoint_edgeFirstUsed e]
  · apply lt_of_le_of_ne hr.2
    intro heq
    have hr1 : r = ⟨1, by simp⟩ := Subtype.ext heq
    change K.edgeParameter e x hx = ⟨1, by simp⟩ at hr1
    apply hnv
    refine ⟨K.edgeSecondUsed e, ?_⟩
    rw [← K.edgePath_edgeParameter e x hx, hr1, K.edgePath_one,
      K.vertexPoint_edgeSecondUsed e]

/-- A chosen intrinsic edge through a point of the one-skeleton. -/
noncomputable def edgeAt (x : K.realization) (hx : x ∈ K.oneSkeleton) : K.Edge :=
  Classical.choose hx

theorem edgeAt_spec (x : K.realization) (hx : x ∈ K.oneSkeleton) :
    x ∈ K.faceCarrier (K.edgeAt x hx).1 :=
  Classical.choose_spec hx

/-- The edgewise replacement map, expressed on the intrinsic edge carrier. -/
noncomputable def edgeReplacementMap {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) : Plane :=
  (K.replacementArc hcont hinj D C e).completePath.extend
    (x.1 (K.edgeSecond e))

theorem edgeReplacementMap_mem_completeCarrier {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) (hx : x ∈ K.faceCarrier e.1) :
    K.edgeReplacementMap hcont hinj D C e x ∈
      (K.replacementArc hcont hinj D C e).completeCarrier := by
  rw [← (K.replacementArc hcont hinj D C e).range_completePath]
  refine ⟨K.edgeParameter e x hx, ?_⟩
  rw [edgeReplacementMap, ← K.edgeParameter_eq_secondCoordinate e x hx]
  exact (Path.extend_apply (K.replacementArc hcont hinj D C e).completePath
    (K.edgeParameter e x hx).2).symm

/-- Simultaneous replacement of every intrinsic edge. Vertices are handled first, so the
definition is independent of the arbitrary chosen incident edge. -/
noncomputable def graphReplacementMap {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (x : K.realization) : Plane := by
  classical
  exact if K.IsGraphVertexPoint x then h x
    else if hx : x ∈ K.oneSkeleton then
      K.edgeReplacementMap hcont hinj D C (K.edgeAt x hx) x
    else h x

theorem graphReplacementMap_vertex {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (v : K.UsedVertex) :
    K.graphReplacementMap hcont hinj D C (K.vertexPoint v) = h (K.vertexPoint v) := by
  classical
  rw [graphReplacementMap, if_pos ⟨v, rfl⟩]

private theorem edgeReplacementMap_eq_vertex {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) (hx : x ∈ K.faceCarrier e.1)
    (hv : K.IsGraphVertexPoint x) :
    K.edgeReplacementMap hcont hinj D C e x = h x := by
  obtain ⟨v, rfl⟩ := hv
  have hve : v.1 ∈ e.1 := (K.vertexPoint_mem_faceCarrier_iff v e.1).mp hx
  rw [K.edge_eq_pair e] at hve
  simp only [Finset.mem_insert, Finset.mem_singleton] at hve
  rcases hve with hfirst | hsecond
  · have hp : K.vertexPoint v = K.edgeFirstPoint e := by
      rw [← K.vertexPoint_edgeFirstUsed e]
      congr 1
      exact Subtype.ext hfirst
    have hparam : K.edgeParameter e (K.vertexPoint v) hx = ⟨0, by simp⟩ := by
      apply K.injective_edgePath e
      rw [K.edgePath_edgeParameter, K.edgePath_zero, ← hp]
    rw [edgeReplacementMap, ← K.edgeParameter_eq_secondCoordinate e (K.vertexPoint v) hx,
      hparam, Path.extend_apply]
    exact (K.replacementArc hcont hinj D C e).completePath.source.trans
      (congrArg h hp.symm)
  · have hp : K.vertexPoint v = K.edgeSecondPoint e := by
      rw [← K.vertexPoint_edgeSecondUsed e]
      congr 1
      exact Subtype.ext hsecond
    have hparam : K.edgeParameter e (K.vertexPoint v) hx = ⟨1, by simp⟩ := by
      apply K.injective_edgePath e
      rw [K.edgePath_edgeParameter, K.edgePath_one, ← hp]
    rw [edgeReplacementMap, ← K.edgeParameter_eq_secondCoordinate e (K.vertexPoint v) hx,
      hparam, Path.extend_apply]
    exact (K.replacementArc hcont hinj D C e).completePath.target.trans
      (congrArg h hp.symm)

theorem graphReplacementMap_eq_edge {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) (hx : x ∈ K.faceCarrier e.1) :
    K.graphReplacementMap hcont hinj D C x =
      K.edgeReplacementMap hcont hinj D C e x := by
  classical
  by_cases hv : K.IsGraphVertexPoint x
  · rw [graphReplacementMap, if_pos hv]
    exact (K.edgeReplacementMap_eq_vertex hcont hinj D C e x hx hv).symm
  · have hxOne : x ∈ K.oneSkeleton := ⟨e, hx⟩
    rw [graphReplacementMap, if_neg hv, dif_pos hxOne]
    let d := K.edgeAt x hxOne
    have hxd := K.edgeAt_spec x hxOne
    change x ∈ K.faceCarrier d.1 at hxd
    change K.edgeReplacementMap hcont hinj D C d x = _
    have hrd := K.edgeParameter_mem_open_of_not_vertex d x hxd hv
    have hre := K.edgeParameter_mem_open_of_not_vertex e x hx hv
    have hde : d = e := by
      by_contra hne
      have hpaths : K.edgePath d (K.edgeParameter d x hxd) =
          K.edgePath e (K.edgeParameter e x hx) :=
        (K.edgePath_edgeParameter d x hxd).trans
          (K.edgePath_edgeParameter e x hx).symm
      apply Set.disjoint_left.mp (K.disjoint_edgePath_image_Ioo hne)
        ⟨K.edgeParameter d x hxd, hrd,
          rfl⟩
        ⟨K.edgeParameter e x hx, hre,
          hpaths.symm⟩
    rw [hde]

theorem continuousOn_graphReplacementMap_faceCarrier
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) : ContinuousOn (K.graphReplacementMap hcont hinj D C)
      (K.faceCarrier e.1) := by
  let A := K.replacementArc hcont hinj D C e
  let q : K.realization → ℝ := fun x => x.1 (K.edgeSecond e)
  have hq : Continuous q := (continuous_apply (K.edgeSecond e)).comp continuous_subtype_val
  have hmodel : Continuous (fun x : K.realization => A.completePath.extend (q x)) :=
    A.completePath.continuous_extend.comp hq
  apply hmodel.continuousOn.congr
  intro x hx
  rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hx]
  rfl

/-- The simultaneous intrinsic edge replacement is continuous on the entire one-skeleton. -/
theorem continuousOn_graphReplacementMap_oneSkeleton
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D) :
    ContinuousOn (K.graphReplacementMap hcont hinj D C) K.oneSkeleton := by
  let carriers : K.Edge → Set K.realization := fun e => K.faceCarrier e.1
  have hfinite : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hglue := hfinite.continuousOn_iUnion
    (fun e => K.faceCarrier_closed e.1)
    (fun e => K.continuousOn_graphReplacementMap_faceCarrier hcont hinj D C e)
  simpa only [carriers, ← K.oneSkeleton_eq_iUnion_faceCarrier] using hglue

theorem edgeReplacementMap_eq_path {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) (hx : x ∈ K.faceCarrier e.1) :
    K.edgeReplacementMap hcont hinj D C e x =
      (K.replacementArc hcont hinj D C e).completePath
        (K.edgeParameter e x hx) := by
  rw [edgeReplacementMap, ← K.edgeParameter_eq_secondCoordinate e x hx]
  exact Path.extend_apply _ (K.edgeParameter e x hx).2

theorem edgeReplacementMap_mem_interiorCarrier {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (e : K.Edge) (x : K.realization) (hx : x ∈ K.faceCarrier e.1)
    (hnv : ¬K.IsGraphVertexPoint x) :
    K.edgeReplacementMap hcont hinj D C e x ∈
      (K.replacementArc hcont hinj D C e).interiorCarrier := by
  let A := K.replacementArc hcont hinj D C e
  have hcarrier : K.edgeReplacementMap hcont hinj D C e x ∈ A.completeCarrier :=
    K.edgeReplacementMap_mem_completeCarrier hcont hinj D C e x hx
  rw [← A.completeCarrier_sdiff_endpoints]
  refine ⟨hcarrier, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hopen := K.edgeParameter_mem_open_of_not_vertex e x hx hnv
  constructor
  · intro heq
    have hpath := K.edgeReplacementMap_eq_path hcont hinj D C e x hx
    have hzero : A.completePath (K.edgeParameter e x hx) = A.completePath 0 := by
      rw [← hpath, heq]
      exact A.completePath.source.symm
    have := congrArg Subtype.val (A.completePath_injective hzero)
    exact (ne_of_gt hopen.1) this
  · intro heq
    have hpath := K.edgeReplacementMap_eq_path hcont hinj D C e x hx
    have hone : A.completePath (K.edgeParameter e x hx) = A.completePath 1 := by
      rw [← hpath, heq]
      exact A.completePath.target.symm
    have := congrArg Subtype.val (A.completePath_injective hone)
    exact (ne_of_lt hopen.2) this

theorem vertex_image_ne_edgeReplacementMap {h : K.realization → Plane}
    (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D)
    (v : K.UsedVertex) (e : K.Edge) (x : K.realization)
    (hx : x ∈ K.faceCarrier e.1) (hnv : ¬K.IsGraphVertexPoint x) :
    h (K.vertexPoint v) ≠ K.edgeReplacementMap hcont hinj D C e x := by
  let A := K.replacementArc hcont hinj D C e
  have hxInterior := K.edgeReplacementMap_mem_interiorCarrier
    hcont hinj D C e x hx hnv
  have hxCarrier := K.edgeReplacementMap_mem_completeCarrier hcont hinj D C e x hx
  by_cases hv : v.1 ∈ e.1
  · rw [K.edge_eq_pair e] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rw [← A.completeCarrier_sdiff_endpoints] at hxInterior
    rcases hxInterior with ⟨_, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    rcases hv with hfirst | hsecond
    · have hp : K.vertexPoint v = K.edgeFirstPoint e := by
        rw [← K.vertexPoint_edgeFirstUsed e]
        congr 1
        exact Subtype.ext hfirst
      exact fun heq => hne.1 (heq.symm.trans (congrArg h hp))
    · have hp : K.vertexPoint v = K.edgeSecondPoint e := by
        rw [← K.vertexPoint_edgeSecondUsed e]
        congr 1
        exact Subtype.ext hsecond
      exact fun heq => hne.2 (heq.symm.trans (congrArg h hp))
  · intro heq
    exact Set.disjoint_left.mp (A.completeCarrier_avoids_nonincident v hv)
      (Metric.mem_closedBall_self D.radius_pos.le) (heq ▸ hxCarrier)

/-- The simultaneous intrinsic graph replacement is injective on the one-skeleton. -/
theorem graphReplacementMap_injectiveOn_oneSkeleton
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D) :
    Set.InjOn (K.graphReplacementMap hcont hinj D C) K.oneSkeleton := by
  intro x hx y hy hxy
  by_cases hvx : K.IsGraphVertexPoint x
  · obtain ⟨v, rfl⟩ := hvx
    by_cases hvy : K.IsGraphVertexPoint y
    · obtain ⟨w, rfl⟩ := hvy
      rw [K.graphReplacementMap_vertex hcont hinj D C,
        K.graphReplacementMap_vertex hcont hinj D C] at hxy
      exact hinj hxy
    · obtain ⟨e, hye⟩ := hy
      exfalso
      apply K.vertex_image_ne_edgeReplacementMap hcont hinj D C v e y hye hvy
      rw [← K.graphReplacementMap_vertex hcont hinj D C v,
        ← K.graphReplacementMap_eq_edge hcont hinj D C e y hye]
      exact hxy
  · obtain ⟨e, hxe⟩ := hx
    by_cases hvy : K.IsGraphVertexPoint y
    · obtain ⟨w, rfl⟩ := hvy
      exfalso
      apply K.vertex_image_ne_edgeReplacementMap hcont hinj D C w e x hxe hvx
      rw [← K.graphReplacementMap_vertex hcont hinj D C w,
        ← K.graphReplacementMap_eq_edge hcont hinj D C e x hxe]
      exact hxy.symm
    · obtain ⟨d, hyd⟩ := hy
      rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hxe,
        K.graphReplacementMap_eq_edge hcont hinj D C d y hyd] at hxy
      by_cases hed : e = d
      · subst d
        have hpathX := K.edgeReplacementMap_eq_path hcont hinj D C e x hxe
        have hpathY := K.edgeReplacementMap_eq_path hcont hinj D C e y hyd
        have hparam : K.edgeParameter e x hxe = K.edgeParameter e y hyd :=
          (K.replacementArc hcont hinj D C e).completePath_injective
            (hpathX.symm.trans (hxy.trans hpathY))
        calc
          x = K.edgePath e (K.edgeParameter e x hxe) :=
            (K.edgePath_edgeParameter e x hxe).symm
          _ = K.edgePath e (K.edgeParameter e y hyd) := by rw [hparam]
          _ = y := K.edgePath_edgeParameter e y hyd
      · have hxInt := K.edgeReplacementMap_mem_interiorCarrier
          hcont hinj D C e x hxe hvx
        have hyInt := K.edgeReplacementMap_mem_interiorCarrier
          hcont hinj D C d y hyd hvy
        exact (Set.disjoint_left.mp
          ((K.replacementArc hcont hinj D C e).disjoint_interiorCarrier
            (A' := K.replacementArc hcont hinj D C d) hed)
          hxInt (hxy ▸ hyInt)).elim

/-- The topological part of the intrinsic one-skeleton approximation: a continuous embedding
assembled from finitely many polygonal edge paths. -/
theorem graphReplacementMap_isEmbedding_oneSkeleton
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D) :
    _root_.Topology.IsEmbedding
      (fun x : K.oneSkeleton => K.graphReplacementMap hcont hinj D C x.1) := by
  letI : CompactSpace K.oneSkeleton :=
    isCompact_iff_compactSpace.mp K.oneSkeleton_closed.isCompact
  apply Topology.IsClosedEmbedding.toIsEmbedding
  apply Continuous.isClosedEmbedding
  · exact continuousOn_iff_continuous_restrict.mp
      (K.continuousOn_graphReplacementMap_oneSkeleton hcont hinj D C)
  · intro x y hxy
    exact Subtype.ext (K.graphReplacementMap_injectiveOn_oneSkeleton hcont hinj D C
      x.2 y.2 hxy)

/-- Quantitative control for simultaneous intrinsic edge replacement.  The remaining input is
the usual fine-mesh condition: the image of each source edge has diameter below `η`. -/
theorem graphReplacementMap_dist_lt_two_mul
    {h : K.realization → Plane} (hcont : Continuous h) (hinj : Function.Injective h)
    (D : K.VertexDiskControl h) (C : K.CentralTubeControl hcont hinj D) {η : ℝ}
    (hsmall : ∀ e : K.Edge, ∀ x ∈ K.faceCarrier e.1,
      ∀ y ∈ K.faceCarrier e.1, dist (h x) (h y) < η)
    (hD : D.radius < η) :
    ∀ x ∈ K.oneSkeleton,
      dist (K.graphReplacementMap hcont hinj D C x) (h x) < 2 * η := by
  intro x hx
  obtain ⟨e, hxe⟩ := hx
  let A := K.replacementArc hcont hinj D C e
  have hyCarrier : K.edgeReplacementMap hcont hinj D C e x ∈ A.completeCarrier :=
    K.edgeReplacementMap_mem_completeCarrier hcont hinj D C e x hxe
  rw [K.graphReplacementMap_eq_edge hcont hinj D C e x hxe]
  have hfirst : K.edgeFirstPoint e ∈ K.faceCarrier e.1 := by
    rw [← K.range_edgePath e]
    exact ⟨⟨0, by simp⟩, K.edgePath_zero e⟩
  have hsecond : K.edgeSecondPoint e ∈ K.faceCarrier e.1 := by
    rw [← K.range_edgePath e]
    exact ⟨⟨1, by simp⟩, K.edgePath_one e⟩
  rcases hyCarrier with (hyLeft | hyMiddle) | hyRight
  · have hyBall := A.leftSpoke_subset_disk hyLeft
    calc
      dist (K.edgeReplacementMap hcont hinj D C e x) (h x) ≤
          dist (K.edgeReplacementMap hcont hinj D C e x) (h (K.edgeFirstPoint e)) +
            dist (h (K.edgeFirstPoint e)) (h x) := dist_triangle _ _ _
      _ < η + η := add_lt_add
        ((Metric.mem_closedBall.mp hyBall).trans_lt hD)
        (by simpa [dist_comm] using hsmall e x hxe _ hfirst)
      _ = 2 * η := by ring
  · have hyTube := A.resolvedCarrier_subset_tube
        (A.trimmedCarrier_subset_resolvedCarrier hyMiddle)
    obtain ⟨z, hzCentral, hdist⟩ := Metric.mem_thickening_iff.mp hyTube
    obtain ⟨r, hrOpen, hzr⟩ :=
      (K.edgeTrim hcont D e).centralCarrier_subset_mapped_openEdge hzCentral
    have hrCarrier : K.edgePath e r ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨r, rfl⟩
    have hz : z = h (K.edgePath e r) := hzr.symm
    calc
      dist (K.edgeReplacementMap hcont hinj D C e x) (h x) ≤
          dist (K.edgeReplacementMap hcont hinj D C e x) z + dist z (h x) :=
        dist_triangle _ _ _
      _ < η + η := add_lt_add
        (hdist.trans (C.radius_lt_vertex.trans hD))
        (by rw [hz]; simpa [dist_comm] using hsmall e x hxe _ hrCarrier)
      _ = 2 * η := by ring
  · have hyBall := A.rightSpoke_subset_disk hyRight
    calc
      dist (K.edgeReplacementMap hcont hinj D C e x) (h x) ≤
          dist (K.edgeReplacementMap hcont hinj D C e x) (h (K.edgeSecondPoint e)) +
            dist (h (K.edgeSecondPoint e)) (h x) := dist_triangle _ _ _
      _ < η + η := add_lt_add
        ((Metric.mem_closedBall.mp hyBall).trans_lt hD)
        (by simpa [dist_comm] using hsmall e x hxe _ hsecond)
      _ = 2 * η := by ring

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
