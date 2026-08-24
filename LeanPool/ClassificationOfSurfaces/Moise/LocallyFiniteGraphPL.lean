/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteGraphApproximation

/-!
# Finite PL models for locally finite graph replacements

Each edge of the locally finite replacement graph is still a finite polygonal arc. This file
marks its two last-exit parameters, restricts the finite source model to the intervening arc,
and adds the two radial spokes. The resulting finite plane complex has exactly the complete
replacement edge as support. It is the edge-level input for assembling polygonal face
boundaries in a common arrangement.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace LocallyFiniteTriangleComplex

variable {S : Type*} [TopologicalSpace S] {K : LocallyFiniteTriangleComplex S}
  {G : K.PlaneGraphRealization} {e : K.Edge}

open PlaneGraphRealization

/-! ## Piecewise-affine formulas on the canonical edge parameter -/

/-- On the first piece, the complete replacement path is the affine first spoke. -/
theorem CentralPolygonalArc.completePath_eq_left
    (A : G.CentralPolygonalArc e) (r : Set.Icc (0 : ℝ) 1)
    (hr : r.1 ≤ (1 / 2 : ℝ)) :
    A.completePath r =
      AffineMap.lineMap (G.vertexImage (K.edgeFirst e)) A.leftEndpoint (2 * r.1) := by
  let first := Path.segment (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
  let tail := A.middlePath.trans
    (Path.segment A.rightEndpoint (G.vertexImage (K.edgeSecond e)))
  rw [show A.completePath = first.trans tail by rfl,
    ← Path.extend_apply (first.trans tail) r.2,
    Path.extend_trans_of_le_half first tail hr]
  have h2r : 2 * r.1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [r.2.1, r.2.2]
  rw [Path.extend_apply first h2r]
  rfl

/-- On the middle piece, the complete replacement path uses its finite PL segment model. -/
theorem CentralPolygonalArc.completePath_eq_middle
    (A : G.CentralPolygonalArc e) (r : Set.Icc (0 : ℝ) 1)
    (hr0 : (1 / 2 : ℝ) ≤ r.1) (hr1 : r.1 ≤ (3 / 4 : ℝ)) :
    A.completePath r = A.parameterization.map
      (planePoint (A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * r.1 - 2))) 0) := by
  let first := Path.segment (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (G.vertexImage (K.edgeSecond e))
  rw [show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    ← Path.extend_apply (first.trans (A.middlePath.trans last)) r.2,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) hr0]
  have hinner : 2 * r.1 - 1 ≤ (1 / 2 : ℝ) := by linarith
  rw [Path.extend_trans_of_le_half A.middlePath last hinner]
  have hu : 2 * (2 * r.1 - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [r.2.1, r.2.2]
  rw [Path.extend_apply A.middlePath hu]
  change A.parameterization.curve
      (Path.segment A.exitData.left A.exitData.right
        ⟨2 * (2 * r.1 - 1), hu⟩) = _
  rw [A.parameterization.curve_eq]
  congr 1
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul]
  ring

/-- On the final piece, the complete replacement path is the affine second spoke. -/
theorem CentralPolygonalArc.completePath_eq_right
    (A : G.CentralPolygonalArc e) (r : Set.Icc (0 : ℝ) 1)
    (hr : (3 / 4 : ℝ) ≤ r.1) :
    A.completePath r =
      AffineMap.lineMap A.rightEndpoint (G.vertexImage (K.edgeSecond e))
        (4 * r.1 - 3) := by
  let first := Path.segment (G.vertexImage (K.edgeFirst e)) A.leftEndpoint
  let last := Path.segment A.rightEndpoint (G.vertexImage (K.edgeSecond e))
  have houter : (1 / 2 : ℝ) ≤ r.1 := by linarith
  rw [show A.completePath = first.trans (A.middlePath.trans last) by rfl,
    ← Path.extend_apply (first.trans (A.middlePath.trans last)) r.2,
    Path.extend_trans_of_half_le first (A.middlePath.trans last) houter]
  have hinner : (1 / 2 : ℝ) ≤ 2 * r.1 - 1 := by linarith
  rw [Path.extend_trans_of_half_le A.middlePath last hinner]
  have hu : 2 * (2 * r.1 - 1) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [r.2.1, r.2.2]
  rw [Path.extend_apply last hu]
  exact congrArg (AffineMap.lineMap A.rightEndpoint
    (G.vertexImage (K.edgeSecond e))) (by ring)

/-- Evaluating the edge replacement on its canonical source path recovers the same unit
interval parameter on the complete polygonal path. -/
theorem replacementEdgeMap_edgePath (G : K.PlaneGraphRealization) (e : K.Edge)
    (r : Set.Icc (0 : ℝ) 1) :
    G.replacementEdgeMap e
      ⟨edgePathInSupport (K := K) e r, by
        rw [← range_edgePathInSupport (K := K) e]
        exact Set.mem_range_self r⟩ =
      (G.replacementArc e).completePath r := by
  rw [PlaneGraphRealization.replacementEdgeMap]
  congr 1
  apply (G.edgePathInSupportHomeomorph e).injective
  rw [(G.edgePathInSupportHomeomorph e).apply_symm_apply]
  rfl

/-! ## The finite source breakpoint family -/

/-- The `rawEdgeMiddleBreakpoint` declaration. -/
noncomputable def rawEdgeMiddleBreakpoint
    (A : G.CentralPolygonalArc e) (v : A.parameterization.source.Vertex) : ℝ :=
  (((A.parameterization.source.position v) 0 /
      A.parameterization.length - A.exitData.left) /
      (A.exitData.right - A.exitData.left) + 2) / 4

/-- The `edgeMiddleBreakpoint` declaration. -/
noncomputable def edgeMiddleBreakpoint
    (A : G.CentralPolygonalArc e) (v : A.parameterization.source.Vertex) : ℝ :=
  max (1 / 2 : ℝ) (min (3 / 4 : ℝ) (rawEdgeMiddleBreakpoint A v))

theorem edgeMiddleBreakpoint_mem
    (A : G.CentralPolygonalArc e) (v : A.parameterization.source.Vertex) :
    edgeMiddleBreakpoint A v ∈ Set.Icc (1 / 2 : ℝ) (3 / 4 : ℝ) := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem edgeMiddleBreakpoint_eq_raw_of_mem
    (A : G.CentralPolygonalArc e) (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.parameterization.length)
    (hv1 : A.parameterization.source.position v 0 / A.parameterization.length ≤
      A.exitData.right) :
    edgeMiddleBreakpoint A v = rawEdgeMiddleBreakpoint A v := by
  have hden : 0 < A.exitData.right - A.exitData.left :=
    sub_pos.mpr A.exitData.left_lt_right
  have hfrac0 : 0 ≤
      (A.parameterization.source.position v 0 / A.parameterization.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) :=
    div_nonneg (sub_nonneg.mpr hv0) hden.le
  have hfrac1 :
      (A.parameterization.source.position v 0 / A.parameterization.length -
        A.exitData.left) / (A.exitData.right - A.exitData.left) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith
  have hraw0 : (1 / 2 : ℝ) ≤ rawEdgeMiddleBreakpoint A v := by
    dsimp [rawEdgeMiddleBreakpoint]
    linarith
  have hraw1 : rawEdgeMiddleBreakpoint A v ≤ (3 / 4 : ℝ) := by
    dsimp [rawEdgeMiddleBreakpoint]
    linarith
  rw [edgeMiddleBreakpoint, min_eq_right hraw1, max_eq_right hraw0]

theorem edgeMiddleSourceScalar_breakpoint
    (A : G.CentralPolygonalArc e) (v : A.parameterization.source.Vertex)
    (hv0 : A.exitData.left ≤
      A.parameterization.source.position v 0 / A.parameterization.length)
    (hv1 : A.parameterization.source.position v 0 / A.parameterization.length ≤
      A.exitData.right) :
    A.parameterization.length *
        (A.exitData.left + (A.exitData.right - A.exitData.left) *
          (4 * edgeMiddleBreakpoint A v - 2)) =
      A.parameterization.source.position v 0 := by
  rw [edgeMiddleBreakpoint_eq_raw_of_mem A v hv0 hv1]
  have hn : (A.parameterization.length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.resolvedWalk_length_pos)
  have hden : A.exitData.right - A.exitData.left ≠ 0 :=
    sub_ne_zero.mpr A.exitData.left_lt_right.ne'
  dsimp [rawEdgeMiddleBreakpoint]
  field_simp [hn, hden]
  ring

/-- The spoke joins and all vertices of the finite middle PL model. -/
abbrev EdgeBreakpoint (A : G.CentralPolygonalArc e) :=
  Option (Option A.parameterization.source.Vertex)

/-- The `edgeBreakpointParameter` declaration. -/
noncomputable def edgeBreakpointParameter
    (A : G.CentralPolygonalArc e) (b : EdgeBreakpoint A) : ℝ :=
  match b with
  | none => 1 / 2
  | some none => 3 / 4
  | some (some v) => edgeMiddleBreakpoint A v

theorem edgeBreakpointParameter_mem
    (A : G.CentralPolygonalArc e) (b : EdgeBreakpoint A) :
    edgeBreakpointParameter A b ∈ Set.Icc (0 : ℝ) 1 := by
  rcases b with _ | _ | v
  · norm_num [edgeBreakpointParameter]
  · norm_num [edgeBreakpointParameter]
  · have hb := edgeMiddleBreakpoint_mem A v
    change edgeMiddleBreakpoint A v ∈ Set.Icc (0 : ℝ) 1
    constructor <;> linarith [hb.1, hb.2]

namespace PlaneGraphRealization
namespace CentralPolygonalArc

variable (A : G.CentralPolygonalArc e)

/-- The `leftSourcePoint` declaration. -/
noncomputable def leftSourcePoint : Plane :=
  planePoint (A.parameterization.length * A.exitData.left) 0

/-- The `rightSourcePoint` declaration. -/
noncomputable def rightSourcePoint : Plane :=
  planePoint (A.parameterization.length * A.exitData.right) 0

theorem leftSourcePoint_mem_source : A.leftSourcePoint ∈ A.parameterization.source.support := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap]
  refine ⟨A.exitData.left, ⟨A.exitData.left_nonneg,
    A.exitData.left_lt_right.le.trans A.exitData.right_le_one⟩, ?_⟩
  ext i
  fin_cases i <;>
    simp [leftSourcePoint, planePoint, AffineMap.lineMap_apply_module]; ring

theorem rightSourcePoint_mem_source : A.rightSourcePoint ∈ A.parameterization.source.support := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap]
  refine ⟨A.exitData.right, ⟨A.exitData.left_nonneg.trans
    A.exitData.left_lt_right.le, A.exitData.right_le_one⟩, ?_⟩
  ext i
  fin_cases i <;>
    simp [rightSourcePoint, planePoint, AffineMap.lineMap_apply_module]; ring

theorem leftSourcePoint_ne_rightSourcePoint : A.leftSourcePoint ≠ A.rightSourcePoint := by
  intro hp
  have hcoord := congrArg (fun p : Plane => p 0) hp
  have hn : (0 : ℝ) < A.parameterization.length := by
    exact_mod_cast A.resolvedWalk_length_pos
  simp only [leftSourcePoint, rightSourcePoint, planePoint_apply_zero] at hcoord
  nlinarith [A.exitData.left_lt_right]

theorem leftSourcePoint_zero_lt_right :
    A.leftSourcePoint 0 < A.rightSourcePoint 0 := by
  have hn : (0 : ℝ) < A.parameterization.length := by
    exact_mod_cast A.resolvedWalk_length_pos
  simp only [leftSourcePoint, rightSourcePoint, planePoint_apply_zero]
  nlinarith [A.exitData.left_lt_right]

/-- The two source points at which the middle polygonal path exits the endpoint disks. -/
noncomputable def trimMark : Fin 2 → Plane
  | ⟨0, _⟩ => A.leftSourcePoint
  | ⟨1, _⟩ => A.rightSourcePoint

@[simp] theorem trimMark_zero : A.trimMark 0 = A.leftSourcePoint := rfl

@[simp] theorem trimMark_one : A.trimMark 1 = A.rightSourcePoint := rfl

/-- The source graph refined at both last-exit points. -/
noncomputable def trimSubdivision : PlaneComplex :=
  A.parameterization.source.markedEdgeSubdivision A.trimMark

/-- The exact closed source interval between the two exits. -/
noncomputable def trimSource : PlaneComplex :=
  A.trimSubdivision.restrictedTo (segment ℝ A.leftSourcePoint A.rightSourcePoint)

private theorem sourcePoint_mem_axis_segment_iff {p : Plane}
    (hp : p ∈ A.parameterization.source.support) :
    p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ A.parameterization.length := by
  rw [A.parameterization.source_support, segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  constructor
  · simp [AffineMap.lineMap_apply_module, planePoint]
  · have hn : (0 : ℝ) ≤ A.parameterization.length := by positivity
    constructor
    · simpa [AffineMap.lineMap_apply_module, planePoint] using mul_nonneg ht.1 hn
    · simp [AffineMap.lineMap_apply_module, planePoint]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hn]

private theorem mem_sourceSubsegment_of_axis_bounds {p : Plane}
    (hpAxis : p 1 = 0)
    (hpLeft : A.leftSourcePoint 0 ≤ p 0)
    (hpRight : p 0 ≤ A.rightSourcePoint 0) :
    p ∈ segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  rw [segment_eq_image_lineMap]
  let q : ℝ := (p 0 - A.leftSourcePoint 0) /
    (A.rightSourcePoint 0 - A.leftSourcePoint 0)
  have hden : 0 < A.rightSourcePoint 0 - A.leftSourcePoint 0 :=
    sub_pos.mpr A.leftSourcePoint_zero_lt_right
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hpLeft) hden.le
    · exact (div_le_one hden).mpr (by linarith)
  refine ⟨q, hq, ?_⟩
  ext i
  fin_cases i
  · simp only [AffineMap.lineMap_apply_module]
    dsimp [q]
    field_simp [hden.ne']
    ring
  · simp [AffineMap.lineMap_apply_module, leftSourcePoint, rightSourcePoint,
      planePoint, hpAxis]

private theorem exists_trimSubdivision_vertex (i : Fin 2) :
    ∃ w : A.trimSubdivision.Vertex,
      ({w} : Finset A.trimSubdivision.Vertex) ∈ A.trimSubdivision.simplexes ∧
        A.trimSubdivision.position w = A.trimMark i := by
  apply A.parameterization.source.exists_markedEdgeSubdivision_vertex A.trimMark i
  fin_cases i
  · exact A.leftSourcePoint_mem_source
  · exact A.rightSourcePoint_mem_source

/-- Marking the two exits makes the interval between them an exact finite subcomplex. -/
theorem trimSource_support :
    A.trimSource.support = segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  unfold trimSource
  apply A.trimSubdivision.restrictedTo_support_eq
  intro x hx
  by_cases hxL : x = A.leftSourcePoint
  · obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex 0
    have hpos' : A.trimSubdivision.position w = A.leftSourcePoint :=
      hpos.trans A.trimMark_zero
    refine ⟨{w}, hw, ?_, ?_⟩
    · rw [hxL, ← hpos']
      exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩
    · intro y hy
      have hy' : y = A.trimSubdivision.position w := by
        rw [PlaneComplex.cellCarrier] at hy
        have himage : A.trimSubdivision.position ''
            (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
            {A.trimSubdivision.position w} := by
          ext z
          simp
        rw [himage, convexHull_singleton] at hy
        exact hy
      rw [hy', hpos']
      exact left_mem_segment ℝ _ _
  · by_cases hxR : x = A.rightSourcePoint
    · obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex 1
      have hpos' : A.trimSubdivision.position w = A.rightSourcePoint :=
        hpos.trans A.trimMark_one
      refine ⟨{w}, hw, ?_, ?_⟩
      · rw [hxR, ← hpos']
        exact subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩
      · intro y hy
        have hy' : y = A.trimSubdivision.position w := by
          rw [PlaneComplex.cellCarrier] at hy
          have himage : A.trimSubdivision.position ''
              (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
              {A.trimSubdivision.position w} := by
            ext z
            simp
          rw [himage, convexHull_singleton] at hy
          exact hy
        rw [hy', hpos']
        exact right_mem_segment ℝ _ _
    · have hxSource : x ∈ A.parameterization.source.support := by
        rw [A.parameterization.source_support]
        apply (convex_segment (planePoint 0 0)
          (planePoint A.parameterization.length 0)).segment_subset
        · rw [← A.parameterization.source_support]
          exact A.leftSourcePoint_mem_source
        · rw [← A.parameterization.source_support]
          exact A.rightSourcePoint_mem_source
        · exact hx
      have hxTrimSupport : x ∈ A.trimSubdivision.support := by
        rw [trimSubdivision,
          A.parameterization.source.markedEdgeSubdivision_support_eq A.trimMark
            A.parameterization.source_card_le_two]
        exact hxSource
      rw [PlaneComplex.support] at hxTrimSupport
      simp only [Set.mem_iUnion] at hxTrimSupport
      obtain ⟨u, hu, hxu⟩ := hxTrimSupport
      have huData := (A.parameterization.source.markedEdgeChain A.trimMark
        |>.arrangementMesh.toPlaneComplex.mem_subordinateTo_simplexes_iff
          A.parameterization.source).mp hu
      obtain ⟨huArr, s, hs, hus⟩ := huData
      let M := (A.parameterization.source.markedEdgeChain A.trimMark).arrangementMesh
      have hxCoord := A.sourcePoint_mem_axis_segment_iff hxSource
      have hxBounds : A.leftSourcePoint 0 < x 0 ∧
          x 0 < A.rightSourcePoint 0 := by
        have hxClosed : A.leftSourcePoint 0 ≤ x 0 ∧
            x 0 ≤ A.rightSourcePoint 0 := by
          rw [segment_eq_image_lineMap] at hx
          obtain ⟨t, ht, rfl⟩ := hx
          constructor <;>
            simp [AffineMap.lineMap_apply_module] <;>
            nlinarith [A.leftSourcePoint_zero_lt_right, ht.1, ht.2]
        exact ⟨lt_of_le_of_ne hxClosed.1
            (Ne.symm (fun h => hxL (plane_ext h hxCoord.1))),
          lt_of_le_of_ne hxClosed.2 (fun h => hxR (plane_ext h hxCoord.1))⟩
      have hlow := M.nonneg_on_face_of_monochromatic_of_pos
        (A.parameterization.source.markedEdgeArrangement_monochromatic_vertical
          A.trimMark 0) huArr hxu (by
            change 0 < x 0 - A.leftSourcePoint 0
            linarith [hxBounds.1])
      have hhigh := M.nonpos_on_face_of_monochromatic_of_neg
        (A.parameterization.source.markedEdgeArrangement_monochromatic_vertical
          A.trimMark 1) huArr hxu (by
            change x 0 - A.rightSourcePoint 0 < 0
            linarith [hxBounds.2])
      have huSegment : A.trimSubdivision.cellCarrier u ⊆
          segment ℝ A.leftSourcePoint A.rightSourcePoint := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          have hvSource : M.position v ∈ A.parameterization.source.support := by
            apply A.parameterization.source.cellCarrier_subset_support hs
            apply hus
            exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
          have hvAxis := A.sourcePoint_mem_axis_segment_iff hvSource
          apply A.mem_sourceSubsegment_of_axis_bounds hvAxis.1
          · have hlo := hlow v hv
            change 0 ≤ M.position v 0 - A.leftSourcePoint 0 at hlo
            linarith
          · have hhi := hhigh v hv
            change M.position v 0 - A.rightSourcePoint 0 ≤ 0 at hhi
            linarith
        · exact convex_segment _ _
      exact ⟨u, hu, hxu, huSegment⟩

/-- Remove the unused vertices retained by `restrictedTo`. -/
noncomputable def trimActive : PlaneComplex :=
  PlaneComplex.active A.trimSource

theorem trimActive_support :
    A.trimActive.support = segment ℝ A.leftSourcePoint A.rightSourcePoint := by
  rw [trimActive, A.trimSource.active_support, A.trimSource_support]

theorem trimActive_vertex_mem_support (v : A.trimActive.Vertex) :
    A.trimActive.position v ∈ A.trimActive.support := by
  change A.trimSource.position v.1 ∈ (PlaneComplex.active A.trimSource).support
  rw [A.trimSource.active_support]
  exact v.2

theorem trimActive_card_le_two :
    ∀ s ∈ A.trimActive.simplexes, s.card ≤ 2 := by
  intro s hs
  let u : Finset A.trimSubdivision.Vertex := s.map A.trimSource.activeEmbedding
  have huTrim : u ∈ A.trimSource.simplexes := A.trimSource.mem_activeSimplexes.mp hs
  have huR : u ∈ A.trimSubdivision.simplexes :=
    (A.trimSubdivision.mem_restrictedTo_simplexes_iff _).mp huTrim |>.1
  have hsub := A.parameterization.source.markedEdgeSubdivision_subdivides A.trimMark
    A.parameterization.source_card_le_two
  obtain ⟨t, ht, hut⟩ := hsub.2 u huR
  have huCard : u.card ≤ 2 :=
    PlaneComplex.card_le_two_of_cellCarrier_subset_face huR ht
      (A.parameterization.source_card_le_two t ht) hut
  calc
    s.card = u.card := by
      dsimp [u]
      exact (Finset.card_map _).symm
    _ ≤ 2 := huCard

theorem trimActive_map_injective :
    Set.InjOn A.parameterization.map A.trimActive.support := by
  apply A.parameterization.map_injectiveOn.mono
  rw [A.trimActive_support]
  intro x hx
  rw [A.parameterization.source_support]
  apply (convex_segment (planePoint 0 0)
    (planePoint A.parameterization.length 0)).segment_subset
  · rw [← A.parameterization.source_support]
    exact A.leftSourcePoint_mem_source
  · rw [← A.parameterization.source_support]
    exact A.rightSourcePoint_mem_source
  · exact hx

theorem trimActive_map_affine :
    ∀ s ∈ A.trimActive.simplexes,
      IsAffineOn A.parameterization.map (A.trimActive.cellCarrier s) := by
  intro s hs
  let u : Finset A.trimSubdivision.Vertex := s.map A.trimSource.activeEmbedding
  have huTrim : u ∈ A.trimSource.simplexes := A.trimSource.mem_activeSimplexes.mp hs
  have huR : u ∈ A.trimSubdivision.simplexes :=
    (A.trimSubdivision.mem_restrictedTo_simplexes_iff _).mp huTrim |>.1
  have hsub := A.parameterization.source.markedEdgeSubdivision_subdivides A.trimMark
    A.parameterization.source_card_le_two
  obtain ⟨t, ht, hut⟩ := hsub.2 u huR
  apply (A.parameterization.map_affineOn t ht).mono
  intro x hx
  apply hut
  have hx' := A.trimSource.active_cellCarrier s ▸ hx
  change x ∈ A.trimSource.cellCarrier u at hx'
  unfold trimSource at hx'
  rw [A.trimSubdivision.restrictedTo_cellCarrier] at hx'
  exact hx'

/-- The finite target graph carried by the trimmed polygonal middle. -/
noncomputable def trimTarget : PlaneComplex :=
  A.trimActive.mapGraph A.parameterization.map A.trimActive_vertex_mem_support
    A.trimActive_map_injective A.trimActive_card_le_two A.trimActive_map_affine

theorem map_image_sourceSegment :
    A.parameterization.map '' segment ℝ A.leftSourcePoint A.rightSourcePoint =
      A.trimmedCarrier := by
  rw [trimmedCarrier]
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    let t : ℝ := AffineMap.lineMap A.exitData.left A.exitData.right u
    have ht : t ∈ Set.Icc A.exitData.left A.exitData.right := by
      rw [← segment_eq_Icc A.exitData.left_lt_right.le, segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
    refine ⟨t, ht, ?_⟩
    rw [A.parameterization.curve_eq]
    congr 2
    ext i
    fin_cases i <;>
      simp [t, leftSourcePoint, rightSourcePoint, planePoint,
        AffineMap.lineMap_apply_module]; ring
  · rintro ⟨t, ht, rfl⟩
    have htSeg : t ∈ segment ℝ A.exitData.left A.exitData.right := by
      rwa [segment_eq_Icc A.exitData.left_lt_right.le]
    rw [segment_eq_image_lineMap] at htSeg
    obtain ⟨u, hu, rfl⟩ := htSeg
    refine ⟨AffineMap.lineMap A.leftSourcePoint A.rightSourcePoint u,
      ?_, ?_⟩
    · rw [segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
    rw [A.parameterization.curve_eq]
    congr 2
    ext i
    fin_cases i <;>
      simp [leftSourcePoint, rightSourcePoint, planePoint,
        AffineMap.lineMap_apply_module]; ring

theorem trimTarget_support : A.trimTarget.support = A.trimmedCarrier := by
  rw [trimTarget, A.trimActive.mapGraph_support A.parameterization.map
    A.trimActive_vertex_mem_support A.trimActive_map_injective
    A.trimActive_card_le_two A.trimActive_map_affine,
    A.trimActive_support, A.map_image_sourceSegment]

private theorem exists_trimActive_vertex (i : Fin 2) :
    ∃ v : A.trimActive.Vertex,
      ({v} : Finset A.trimActive.Vertex) ∈ A.trimActive.simplexes ∧
        A.trimActive.position v = A.trimMark i := by
  obtain ⟨w, hw, hpos⟩ := A.exists_trimSubdivision_vertex i
  have hmarkSegment : A.trimMark i ∈
      segment ℝ A.leftSourcePoint A.rightSourcePoint := by
    fin_cases i <;> simp [trimMark, left_mem_segment, right_mem_segment]
  have hwSub : A.trimSubdivision.cellCarrier {w} ⊆
      segment ℝ A.leftSourcePoint A.rightSourcePoint := by
    intro x hx
    have hxw : x = A.trimSubdivision.position w := by
      rw [PlaneComplex.cellCarrier] at hx
      have himage : A.trimSubdivision.position ''
          (({w} : Finset A.trimSubdivision.Vertex) : Set A.trimSubdivision.Vertex) =
          {A.trimSubdivision.position w} := by
        ext z
        simp
      rw [himage, convexHull_singleton] at hx
      exact hx
    rw [hxw, hpos]
    exact hmarkSegment
  have hwTrim : ({w} : Finset A.trimSource.Vertex) ∈ A.trimSource.simplexes := by
    unfold trimSource
    exact A.trimSubdivision.mem_restrictedTo_simplexes_iff _ |>.mpr ⟨hw, hwSub⟩
  have hwSupport : A.trimSource.position w ∈ A.trimSource.support :=
    A.trimSource.cellCarrier_subset_support hwTrim
      (subset_convexHull ℝ _ ⟨w, Finset.mem_singleton_self _, rfl⟩)
  let v : A.trimSource.ActiveVertex := ⟨w, hwSupport⟩
  refine ⟨v, ?_, ?_⟩
  · change ({v} : Finset A.trimSource.ActiveVertex) ∈
      (PlaneComplex.active A.trimSource).simplexes
    apply A.trimSource.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    exact hwTrim
  · exact hpos

/-- The `leftTrimVertex` declaration. -/
noncomputable def leftTrimVertex : A.trimTarget.Vertex :=
  Classical.choose (A.exists_trimActive_vertex 0)

/-- The `rightTrimVertex` declaration. -/
noncomputable def rightTrimVertex : A.trimTarget.Vertex :=
  Classical.choose (A.exists_trimActive_vertex 1)

theorem leftTrimVertex_face :
    ({A.leftTrimVertex} : Finset A.trimTarget.Vertex) ∈ A.trimTarget.simplexes :=
  (Classical.choose_spec (A.exists_trimActive_vertex 0)).1

theorem rightTrimVertex_face :
    ({A.rightTrimVertex} : Finset A.trimTarget.Vertex) ∈ A.trimTarget.simplexes :=
  (Classical.choose_spec (A.exists_trimActive_vertex 1)).1

theorem leftTrimVertex_sourcePosition :
    A.trimActive.position A.leftTrimVertex = A.leftSourcePoint := by
  change A.trimActive.position
    (Classical.choose (A.exists_trimActive_vertex 0)) = A.leftSourcePoint
  exact (Classical.choose_spec (A.exists_trimActive_vertex 0)).2.trans A.trimMark_zero

theorem rightTrimVertex_sourcePosition :
    A.trimActive.position A.rightTrimVertex = A.rightSourcePoint := by
  change A.trimActive.position
    (Classical.choose (A.exists_trimActive_vertex 1)) = A.rightSourcePoint
  exact (Classical.choose_spec (A.exists_trimActive_vertex 1)).2.trans A.trimMark_one

theorem map_leftSourcePoint :
    A.parameterization.map A.leftSourcePoint = A.leftEndpoint := by
  rw [leftEndpoint, A.parameterization.curve_eq]
  rfl

theorem map_rightSourcePoint :
    A.parameterization.map A.rightSourcePoint = A.rightEndpoint := by
  rw [rightEndpoint, A.parameterization.curve_eq]
  rfl

theorem trimTarget_position_left :
    A.trimTarget.position A.leftTrimVertex = A.leftEndpoint := by
  change A.parameterization.map (A.trimActive.position A.leftTrimVertex) = _
  rw [A.leftTrimVertex_sourcePosition, A.map_leftSourcePoint]

theorem trimTarget_position_right :
    A.trimTarget.position A.rightTrimVertex = A.rightEndpoint := by
  change A.parameterization.map (A.trimActive.position A.rightTrimVertex) = _
  rw [A.rightTrimVertex_sourcePosition, A.map_rightSourcePoint]

theorem isPreconnected_trimTarget_support : IsPreconnected A.trimTarget.support := by
  rw [A.trimTarget_support, trimmedCarrier]
  apply IsPreconnected.image (convex_Icc _ _).isPreconnected
  exact A.parameterization.continuousOn.mono fun _ ht =>
    ⟨A.exitData.left_nonneg.trans ht.1, ht.2.trans A.exitData.right_le_one⟩

/-- A simple finite graph path traversing the trimmed target arc. -/
noncomputable def middleVertexPath : A.trimTarget.vertexGraph.Path
    A.leftTrimVertex A.rightTrimVertex := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := (A.trimTarget.vertexGraph_reachable_of_isPreconnected
    A.isPreconnected_trimTarget_support A.leftTrimVertex_face
      A.rightTrimVertex_face).exists_isPath
  exact ⟨⟨p, hp⟩⟩

/-- An auxiliary broken line which lists the two spokes and every edge and vertex of the trimmed
target.  Connector segments between listed pieces are harmless: `completeTarget` below retains
only arrangement faces contained in the actual replacement carrier. -/
noncomputable def completeChain : BrokenLineData (Set.univ : Set Plane) := by
  classical
  let B := A.trimTarget.edgeChain
  let vertex : Fin (B.n + 5) → Plane := fun k =>
    if k.val = 0 then G.vertexImage (K.edgeFirst e)
    else if k.val = 1 then A.leftEndpoint
    else if hk : k.val < B.n + 3 then B.vertex ⟨k.val - 2, by omega⟩
    else if k.val = B.n + 3 then A.rightEndpoint
    else G.vertexImage (K.edgeSecond e)
  exact {
    n := B.n + 4
    vertex := vertex
    segment_subset := fun _ _ _ => Set.mem_univ _ }

@[simp] theorem completeChain_vertex_zero :
    A.completeChain.vertex 0 = G.vertexImage (K.edgeFirst e) := by
  simp [completeChain]

@[simp] theorem completeChain_vertex_one :
    A.completeChain.vertex ⟨1, by simp [completeChain]⟩ = A.leftEndpoint := by
  simp [completeChain]

theorem completeChain_vertex_middle
    (i : Fin (A.trimTarget.edgeChain.n + 1)) :
    A.completeChain.vertex ⟨i.val + 2, by simp [completeChain]; omega⟩ =
      A.trimTarget.edgeChain.vertex i := by
  simp only [completeChain]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2

theorem completeChain_vertex_rightEndpoint :
    A.completeChain.vertex
        ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩ =
      A.rightEndpoint := by
  simp [completeChain]

theorem completeChain_vertex_finish :
    A.completeChain.vertex (Fin.last A.completeChain.n) =
      G.vertexImage (K.edgeSecond e) := by
  simp [completeChain]

/-- The finite plane complex carried by one complete replacement edge. -/
noncomputable def completeTarget : PlaneComplex :=
  A.completeChain.arrangementMesh.toPlaneComplex.restrictedTo A.completeCarrier

/-- Every point of a complete replacement edge lies in a one-dimensional arrangement face
subordinate to that edge.  The cardinality conclusion is what permits several replacement edges
to be resolved in one common line arrangement. -/
theorem exists_completeTarget_face {x : Plane} (hx : x ∈ A.completeCarrier) :
    ∃ s ∈ A.completeChain.arrangementMesh.toPlaneComplex.simplexes,
      x ∈ A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ∧
        A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
          A.completeCarrier ∧ s.card ≤ 2 := by
  classical
  rcases hx with (hxLeft | hxMiddle) | hxRight
  · let i : Fin A.completeChain.n := ⟨0, by simp [completeChain]⟩
    have hsegment : segment ℝ
        (A.completeChain.vertex i.castSucc) (A.completeChain.vertex i.succ) =
        A.leftSpoke := by
      simp [i, completeChain, leftSpoke]
    obtain ⟨s, hs, hxs, hsSegment⟩ :=
      A.completeChain.exists_face_on_segment i (hsegment.symm ▸ hxLeft)
    refine ⟨s, hs, hxs, ?_,
      A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
        hs hsSegment⟩
    have hsub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        A.leftSpoke := by
      rw [← hsegment]
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hsub.trans (Set.subset_union_left.trans Set.subset_union_left)
  · have hxSupport : x ∈ A.trimTarget.support := by
      rwa [A.trimTarget_support]
    rw [PlaneComplex.support] at hxSupport
    simp only [Set.mem_iUnion] at hxSupport
    obtain ⟨s, hs, hxs⟩ := hxSupport
    have hsPos : 0 < s.card := Finset.card_pos.mpr
      (A.trimTarget.nonempty_of_mem s hs)
    have hsLe : s.card ≤ 2 := A.trimActive_card_le_two s hs
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsOne | hsTwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsOne
      have hxv : x = A.trimTarget.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨j, hj⟩ := A.trimTarget.exists_vertexAt v
      let q : Fin (A.trimTarget.edgeChain.n + 1) :=
        ⟨2 * Fintype.card A.trimTarget.EdgeFace + j.val, by
          simp [PlaneComplex.edgeChain]
          ⟩
      let k : Fin (A.completeChain.n + 1) :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      have hk : A.completeChain.vertex k = A.trimTarget.position v := by
        calc
          A.completeChain.vertex k = A.trimTarget.edgeChain.vertex q := by
            simpa [k] using A.completeChain_vertex_middle q
          _ = A.trimTarget.position (A.trimTarget.vertexAt j) := by
            simpa [q] using A.trimTarget.edgeChain_vertex_original j
          _ = A.trimTarget.position v := by rw [hj]
      obtain ⟨w, hwpos, hwface⟩ :=
        A.completeChain.exists_arrangementVertex_position_eq k
      have hwcard : ({w} : Finset A.completeChain.arrangementMesh.Vertex).card ≤ 2 := by
        simp
      refine ⟨{w}, hwface, ?_, ?_, hwcard⟩
      · rw [hxv]
        apply subset_convexHull ℝ _
        exact ⟨w, Finset.mem_singleton_self _, hwpos.trans hk⟩
      · intro y hy
        have hyw : y = A.completeChain.arrangementMesh.toPlaneComplex.position w := by
          rw [PlaneComplex.cellCarrier] at hy
          have himage : A.completeChain.arrangementMesh.toPlaneComplex.position ''
              (({w} : Finset A.completeChain.arrangementMesh.toPlaneComplex.Vertex) :
                Set A.completeChain.arrangementMesh.toPlaneComplex.Vertex) =
              {A.completeChain.arrangementMesh.toPlaneComplex.position w} := by
            ext z
            constructor
            · rintro ⟨u, hu, rfl⟩
              rw [Finset.mem_singleton.mp hu]
              exact Set.mem_singleton _
            · intro hz
              rw [Set.mem_singleton_iff] at hz
              subst z
              exact ⟨w, Finset.mem_singleton_self _, rfl⟩
          rwa [himage, convexHull_singleton] at hy
        rw [hyw, hwpos, hk]
        apply Or.inl
        apply Or.inr
        rw [← A.trimTarget_support]
        exact A.trimTarget.cellCarrier_subset_support hs
          (subset_convexHull ℝ _ ⟨v, Finset.mem_singleton_self _, rfl⟩)
    · let E : A.trimTarget.EdgeFace :=
        ⟨s, Finset.mem_filter.mpr ⟨hs, hsTwo⟩⟩
      obtain ⟨j, hj⟩ := A.trimTarget.exists_edgeAt E
      let q : Fin A.trimTarget.edgeChain.n := A.trimTarget.edgeChainIndex j
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      have hleft : A.completeChain.vertex k.castSucc =
          A.trimTarget.edgeChain.vertex q.castSucc := by
        simpa [k, q] using A.completeChain_vertex_middle q.castSucc
      have hright : A.completeChain.vertex k.succ =
          A.trimTarget.edgeChain.vertex q.succ := by
        simpa [k, q] using A.completeChain_vertex_middle q.succ
      have hsegment : segment ℝ
          (A.completeChain.vertex k.castSucc) (A.completeChain.vertex k.succ) =
          A.trimTarget.cellCarrier s := by
        rw [hleft, hright]
        calc
          segment ℝ (A.trimTarget.edgeChain.vertex q.castSucc)
              (A.trimTarget.edgeChain.vertex q.succ) =
              A.trimTarget.cellCarrier (A.trimTarget.edgeAt j).1 := by
                simpa [q] using A.trimTarget.edgeChain_segment j
          _ = A.trimTarget.cellCarrier s := by rw [hj]
      obtain ⟨u, hu, hxu, huSegment⟩ :=
        A.completeChain.exists_face_on_segment k (hsegment.symm ▸ hxs)
      refine ⟨u, hu, hxu, ?_,
        A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
          hu huSegment⟩
      have huSub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier u ⊆
          A.trimTarget.cellCarrier s := by
        rw [← hsegment]
        apply convexHull_min _ (convex_segment _ _)
        rintro y ⟨v, hv, rfl⟩
        exact huSegment v hv
      intro y hy
      apply Or.inl
      apply Or.inr
      rw [← A.trimTarget_support]
      exact A.trimTarget.cellCarrier_subset_support hs (huSub hy)
  · let i : Fin A.completeChain.n :=
      ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩
    have hsegment : segment ℝ
        (A.completeChain.vertex i.castSucc) (A.completeChain.vertex i.succ) =
        A.rightSpoke := by
      simp [i, completeChain, rightSpoke]
    obtain ⟨s, hs, hxs, hsSegment⟩ :=
      A.completeChain.exists_face_on_segment i (hsegment.symm ▸ hxRight)
    refine ⟨s, hs, hxs, ?_,
      A.completeChain.arrangementMesh.toPlaneComplex.card_le_two_of_vertices_mem_segment
        hs hsSegment⟩
    have hsub : A.completeChain.arrangementMesh.toPlaneComplex.cellCarrier s ⊆
        A.rightSpoke := by
      rw [← hsegment]
      apply convexHull_min _ (convex_segment _ _)
      rintro y ⟨v, hv, rfl⟩
      exact hsSegment v hv
    exact hsub.trans Set.subset_union_right

/-- Exact finite-complex realization of the complete replacement edge. -/
theorem completeTarget_support : A.completeTarget.support = A.completeCarrier := by
  unfold completeTarget
  apply A.completeChain.arrangementMesh.toPlaneComplex.restrictedTo_support_eq
  intro x hx
  obtain ⟨s, hs, hxs, hsub, -⟩ := A.exists_completeTarget_face hx
  exact ⟨s, hs, hxs, hsub⟩

/-- Every point of a complete replacement edge lies on one of the finitely listed segments of
its auxiliary chain.  This is the coverage input used when the three edge chains of a face are
placed into one common line arrangement. -/
theorem completeCarrier_subset_segmentCarrier :
    A.completeCarrier ⊆ A.completeChain.segmentCarrier := by
  classical
  rintro x ((hxLeft | hxMiddle) | hxRight)
  · apply Set.mem_iUnion.mpr
    let i : Fin A.completeChain.n := ⟨0, by simp [completeChain]⟩
    refine ⟨i, ?_⟩
    simpa [i, completeChain, leftSpoke] using hxLeft
  · have hxSupport : x ∈ A.trimTarget.support := by
      rwa [A.trimTarget_support]
    rw [PlaneComplex.support] at hxSupport
    simp only [Set.mem_iUnion] at hxSupport
    obtain ⟨s, hs, hxs⟩ := hxSupport
    have hsPos : 0 < s.card := Finset.card_pos.mpr
      (A.trimTarget.nonempty_of_mem s hs)
    have hsLe : s.card ≤ 2 := A.trimActive_card_le_two s hs
    have hsCases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hsCases with hsOne | hsTwo
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsOne
      have hxv : x = A.trimTarget.position v := by
        simpa [PlaneComplex.cellCarrier] using hxs
      obtain ⟨j, hj⟩ := A.trimTarget.exists_vertexAt v
      let q : Fin A.trimTarget.edgeChain.n :=
        ⟨2 * Fintype.card A.trimTarget.EdgeFace + j.val, by
          simp [PlaneComplex.edgeChain]
          ⟩
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rw [hxv]
      have hleft : A.completeChain.vertex k.castSucc = A.trimTarget.position v := by
        calc
          A.completeChain.vertex k.castSucc = A.trimTarget.edgeChain.vertex q.castSucc := by
            simpa [k, q] using A.completeChain_vertex_middle q.castSucc
          _ = A.trimTarget.position (A.trimTarget.vertexAt j) := by
            simpa [q] using A.trimTarget.edgeChain_vertex_original j
          _ = A.trimTarget.position v := by rw [hj]
      rw [← hleft]
      exact left_mem_segment ℝ _ _
    · let E : A.trimTarget.EdgeFace :=
        ⟨s, Finset.mem_filter.mpr ⟨hs, hsTwo⟩⟩
      obtain ⟨j, hj⟩ := A.trimTarget.exists_edgeAt E
      let q : Fin A.trimTarget.edgeChain.n := A.trimTarget.edgeChainIndex j
      let k : Fin A.completeChain.n :=
        ⟨q.val + 2, by simp [completeChain]; omega⟩
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      have hleft : A.completeChain.vertex k.castSucc =
          A.trimTarget.edgeChain.vertex q.castSucc := by
        simpa [k, q] using A.completeChain_vertex_middle q.castSucc
      have hright : A.completeChain.vertex k.succ =
          A.trimTarget.edgeChain.vertex q.succ := by
        simpa [k, q] using A.completeChain_vertex_middle q.succ
      rw [hleft, hright]
      have hsegment := A.trimTarget.edgeChain_segment j
      rw [hj] at hsegment
      rw [hsegment]
      exact hxs
  · apply Set.mem_iUnion.mpr
    let i : Fin A.completeChain.n :=
      ⟨A.trimTarget.edgeChain.n + 3, by simp [completeChain]⟩
    refine ⟨i, ?_⟩
    simpa [i, completeChain, rightSpoke] using hxRight

/-- The first intrinsic endpoint as a vertex of the finite complete-edge complex. -/
noncomputable def completeStartVertex : A.completeTarget.Vertex :=
  A.completeChain.arrangementVertex 0

/-- The second intrinsic endpoint as a vertex of the finite complete-edge complex. -/
noncomputable def completeFinishVertex : A.completeTarget.Vertex :=
  A.completeChain.arrangementVertex (Fin.last A.completeChain.n)

theorem completeTarget_position_start :
    A.completeTarget.position A.completeStartVertex = G.vertexImage (K.edgeFirst e) := by
  change A.completeChain.arrangementMesh.toPlaneComplex.position
    (A.completeChain.arrangementVertex 0) = _
  rw [A.completeChain.arrangementVertex_position, A.completeChain_vertex_zero]

theorem completeTarget_position_finish :
    A.completeTarget.position A.completeFinishVertex = G.vertexImage (K.edgeSecond e) := by
  change A.completeChain.arrangementMesh.toPlaneComplex.position
    (A.completeChain.arrangementVertex (Fin.last A.completeChain.n)) = _
  rw [A.completeChain.arrangementVertex_position, A.completeChain_vertex_finish]

private theorem singleton_cellCarrier_subset_completeCarrier
    (v : A.completeTarget.Vertex) (p : Plane)
    (hp : A.completeTarget.position v = p) (hpmem : p ∈ A.completeCarrier) :
    A.completeTarget.cellCarrier {v} ⊆ A.completeCarrier := by
  intro x hx
  have hxv : x = A.completeTarget.position v := by
    rw [PlaneComplex.cellCarrier] at hx
    have himage : A.completeTarget.position ''
        (({v} : Finset A.completeTarget.Vertex) : Set A.completeTarget.Vertex) =
        {A.completeTarget.position v} := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_singleton.mp hw]
        exact Set.mem_singleton _
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨v, Finset.mem_singleton_self _, rfl⟩
    rwa [himage, convexHull_singleton] at hx
  rw [hxv, hp]
  exact hpmem

theorem completeStartVertex_face :
    ({A.completeStartVertex} : Finset A.completeTarget.Vertex) ∈
      A.completeTarget.simplexes := by
  apply (A.completeChain.arrangementMesh.toPlaneComplex
    |>.mem_restrictedTo_simplexes_iff A.completeCarrier).mpr
  refine ⟨A.completeChain.arrangementVertex_face 0, ?_⟩
  apply A.singleton_cellCarrier_subset_completeCarrier A.completeStartVertex
    (G.vertexImage (K.edgeFirst e)) A.completeTarget_position_start
  exact Or.inl (Or.inl (left_mem_segment ℝ _ _))

theorem completeFinishVertex_face :
    ({A.completeFinishVertex} : Finset A.completeTarget.Vertex) ∈
      A.completeTarget.simplexes := by
  apply (A.completeChain.arrangementMesh.toPlaneComplex
    |>.mem_restrictedTo_simplexes_iff A.completeCarrier).mpr
  refine ⟨A.completeChain.arrangementVertex_face (Fin.last A.completeChain.n), ?_⟩
  apply A.singleton_cellCarrier_subset_completeCarrier A.completeFinishVertex
    (G.vertexImage (K.edgeSecond e)) A.completeTarget_position_finish
  exact Or.inr (right_mem_segment ℝ _ _)

theorem isPreconnected_completeTarget_support :
    IsPreconnected A.completeTarget.support := by
  rw [A.completeTarget_support, ← A.range_completePath]
  exact (isConnected_range A.completePath.continuous).isPreconnected

/-- A simple finite graph path whose geometric carrier runs from one abstract endpoint to the
other inside the complete replacement edge. -/
noncomputable def completeVertexPath : A.completeTarget.vertexGraph.Path
    A.completeStartVertex A.completeFinishVertex := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := (A.completeTarget.vertexGraph_reachable_of_isPreconnected
    A.isPreconnected_completeTarget_support A.completeStartVertex_face
      A.completeFinishVertex_face).exists_isPath
  exact ⟨⟨p, hp⟩⟩


end CentralPolygonalArc
end PlaneGraphRealization
end LocallyFiniteTriangleComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
