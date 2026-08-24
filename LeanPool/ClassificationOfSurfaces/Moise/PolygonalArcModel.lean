/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension
import LeanPool.ClassificationOfSurfaces.Moise.PolygonalArc

/-! # PL segment models for polygonal arcs -/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace BrokenLineData

/-- A polygonal arc extracted from a broken line is the endpoint-preserving PL image of a
straight segment. -/
theorem exists_PL_segment_model {U : Set Plane} (B : BrokenLineData U) :
    ∃ (S : PlaneComplex) (F : Plane → Plane),
      S.support = segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) ∧
      IsPLOn S F ∧ (∀ s ∈ S.simplexes, s.card ≤ 2) ∧
      Set.InjOn F S.support ∧ F '' S.support = B.resolvedCarrier ∧
      F (planePoint 0 0) = B.start ∧
      F (planePoint B.resolvedWalk.length 0) = B.finish := by
  let A : PlaneComplex := PlaneComplex.active B.resolvedComplex
  have hAvertex : ∀ v, A.position v ∈ A.support := by
    intro v
    change B.resolvedComplex.position v.1 ∈ A.support
    rw [B.resolvedComplex.active_support]
    exact v.2
  have hAgraph : ∀ s ∈ A.simplexes, s.card ≤ 2 := by
    intro s hs
    have hsResolved := B.resolvedComplex.mem_activeSimplexes.mp hs
    calc
      s.card = (s.map B.resolvedComplex.activeEmbedding).card :=
        (Finset.card_map B.resolvedComplex.activeEmbedding).symm
      _ ≤ 2 := B.resolvedComplex_card_le_two hsResolved
  have hAaffine : ∀ s ∈ A.simplexes,
      IsAffineOn B.resolvedStraighten (A.cellCarrier s) := by
    intro s hs
    exact (B.resolvedComplex.active_cellCarrier s).symm ▸
      B.resolvedStraighten_affineOn_faces _
        (B.resolvedComplex.mem_activeSimplexes.mp hs)
  have hAinj : Set.InjOn B.resolvedStraighten A.support := by
    rw [B.resolvedComplex.active_support, B.resolvedComplex_support]
    exact B.resolvedStraighten_injectiveOn
  let S : PlaneComplex :=
    A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine
  have hSsupport : S.support =
      segment ℝ (planePoint 0 0) (planePoint B.resolvedWalk.length 0) := by
    change (A.mapGraph B.resolvedStraighten hAvertex hAinj hAgraph hAaffine).support = _
    rw [A.mapGraph_support B.resolvedStraighten hAvertex hAinj hAgraph hAaffine,
      B.resolvedComplex.active_support, B.resolvedComplex_support,
      B.resolvedStraighten_image]
  let qpos : S.Vertex → Plane := A.position
  have qinj : Function.Injective qpos := A.position_injective
  have qaff : ∀ s ∈ S.simplexes, AffineIndependent ℝ fun v : s => qpos v := by
    intro s hs
    exact A.affineIndependent s hs
  have qface : ∀ s ∈ S.simplexes, ∀ t ∈ S.simplexes,
      convexHull ℝ (qpos '' (s : Set S.Vertex)) ∩
          convexHull ℝ (qpos '' (t : Set S.Vertex)) =
        convexHull ℝ (qpos '' ((s ∩ t : Finset S.Vertex) : Set S.Vertex)) := by
    intro s hs t ht
    exact A.face_inter s hs t ht
  let F : Plane → Plane := S.repositionMap qpos qinj qaff qface
  have hRsupport : (S.reposition qpos qinj qaff qface).support = A.support := by
    rfl
  let v0R : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert 0, B.resolvedVertex_mem_support 0⟩
  let vnR : B.resolvedComplex.ActiveVertex :=
    ⟨B.resolvedWalk.getVert B.resolvedWalk.length,
      B.resolvedVertex_mem_support (Fin.last B.resolvedWalk.length)⟩
  let v0A : A.Vertex := v0R
  let vnA : A.Vertex := vnR
  let v0 : S.Vertex := v0A
  let vn : S.Vertex := vnA
  have hv0 : ({v0} : Finset S.Vertex) ∈ S.simplexes := by
    change ({v0R} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert 0} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face 0
  have hvn : ({vn} : Finset S.Vertex) ∈ S.simplexes := by
    change ({vnR} : Finset B.resolvedComplex.ActiveVertex) ∈
      B.resolvedComplex.activeSimplexes
    apply B.resolvedComplex.mem_activeSimplexes.mpr
    rw [Finset.map_singleton]
    change ({B.resolvedWalk.getVert B.resolvedWalk.length} :
      Finset B.arrangementMesh.toPlaneComplex.Vertex) ∈ B.resolvedComplex.simplexes
    exact B.resolvedVertex_face (Fin.last B.resolvedWalk.length)
  have hSpos0 : S.position v0 = planePoint 0 0 := B.resolvedStraighten_start
  have hSposn : S.position vn = planePoint B.resolvedWalk.length 0 :=
    B.resolvedStraighten_finish
  have hqpos0 : qpos v0 = B.start := B.resolvedVertex_start
  have hqposn : qpos vn = B.finish := B.resolvedVertex_finish
  refine ⟨S, F, hSsupport, S.repositionMap_isPL qpos qinj qaff qface,
    (fun s hs => hAgraph s hs), ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxF : F x =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hx]
    have hyF : F y =
        (S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩).1 := by
      simp [F, PlaneComplex.repositionMap, hy]
    have heq : S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx⟩ =
        S.repositionHomeomorphAll qpos qinj qaff qface ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa [← hxF, ← hyF] using hxy
    exact congrArg Subtype.val
      ((S.repositionHomeomorphAll qpos qinj qaff qface).injective heq)
  · rw [← B.resolvedComplex_support, ← B.resolvedComplex.active_support,
      ← hRsupport]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ S.support := hx
      have hFx : F x =
          (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).1 := by
        simp [F, PlaneComplex.repositionMap, hx']
      rw [hFx]
      exact (S.repositionHomeomorphAll qpos qinj qaff qface ⟨x, hx'⟩).2
    · intro hy
      obtain ⟨x, hx⟩ :=
        (S.repositionHomeomorphAll qpos qinj qaff qface).surjective ⟨y, hy⟩
      refine ⟨x.1, x.2, ?_⟩
      rw [show F x.1 =
        (S.repositionHomeomorphAll qpos qinj qaff qface x).1 by
          simp [F, PlaneComplex.repositionMap, x.2]]
      exact congrArg Subtype.val hx
  · calc
      F (planePoint 0 0) = F (S.position v0) := congrArg F hSpos0.symm
      _ = qpos v0 := S.repositionMap_position qpos qinj qaff qface v0 hv0
      _ = B.start := hqpos0
  · calc
      F (planePoint B.resolvedWalk.length 0) = F (S.position vn) :=
        congrArg F hSposn.symm
      _ = qpos vn := S.repositionMap_position qpos qinj qaff qface vn hvn
      _ = B.finish := hqposn

end BrokenLineData

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
