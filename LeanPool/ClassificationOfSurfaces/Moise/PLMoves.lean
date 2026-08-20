/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.FinitePLHomeomorph
import LeanPool.ClassificationOfSurfaces.Moise.ConeExtension
import LeanPool.ClassificationOfSurfaces.Moise.FreeTriangleMove

/-!
# PL certificates for the elementary Schoenflies moves

The topological homeomorphisms used by the Chapter 3 ear shelling were constructed earlier by
barycentric repositioning.  This file records the missing PL certificates used in Chapter 5.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Extending a self-homeomorphism of a closed patch by the identity preserves that patch
setwise. -/
theorem extendHomeomorphByIdentity_image {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x) :
    extendHomeomorphByIdentity hP e hfrontier '' P = P := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [extendHomeomorphByIdentity_apply_mem hP e hfrontier hx]
    exact (e ⟨x, hx⟩).property
  · intro y hy
    let x : P := e.symm ⟨y, hy⟩
    refine ⟨x, x.property, ?_⟩
    rw [extendHomeomorphByIdentity_apply_mem hP e hfrontier x.property]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- An affine equivalence is finite PL on the support of any explicit pure complex. -/
def affineEquivHomeomorphFinitePL (e : Plane ≃ᵃ[ℝ] Plane)
    (K : PlaneComplex) (hpure : K.IsPure2) :
    FinitePLHomeomorphOn (affineEquivHomeomorph e) K.support where
  complex := K
  support_eq := rfl
  pure := hpure
  affineOn := by
    intro s hs
    exact ⟨e.toAffineMap, fun _ _ => rfl⟩

namespace TriangleMesh

variable (M : TriangleMesh)

/-- All nonempty faces of the incidence-one edges of a triangle mesh. -/
noncomputable def boundaryFaces : Finset (Finset M.Vertex) := by
  classical
  exact M.allBoundaryEdges.biUnion fun e => e.powerset.filter (·.Nonempty)

theorem mem_boundaryFaces_iff {s : Finset M.Vertex} :
    s ∈ M.boundaryFaces ↔ s.Nonempty ∧ ∃ e ∈ M.allBoundaryEdges, s ⊆ e := by
  classical
  simp [boundaryFaces, and_assoc, and_comm]

/-- The incidence-one edges and their faces form a finite one-dimensional plane complex. -/
noncomputable def boundaryComplex : PlaneComplex where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  simplexes := M.boundaryFaces
  nonempty_of_mem := fun s hs => (M.mem_boundaryFaces_iff.mp hs).1
  card_le_three := by
    intro s hs
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    have hecard : e.card = 2 :=
      M.card_of_mem_edges (M.mem_allBoundaryEdges_iff.mp he).1
    exact (Finset.card_le_card hse).trans (by omega)
  down_closed := by
    intro s hs t hts ht
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    exact M.mem_boundaryFaces_iff.mpr ⟨ht, e, he, hts.trans hse⟩
  affineIndependent := by
    intro s hs
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    obtain ⟨u, hu, heu⟩ :=
      Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp he).1
    exact (M.affineIndependent_triangle u hu).comp_embedding
      ⟨fun v : s => (⟨v.1, (Finset.mem_powersetCard.mp heu).1 (hse v.2)⟩ : u), by
        intro v w hvw
        apply Subtype.ext
        exact congrArg (fun q : u => q.1) hvw⟩
  face_inter := by
    intro s hs t ht
    obtain ⟨hsne, es, hes, hses⟩ := M.mem_boundaryFaces_iff.mp hs
    obtain ⟨htne, et, het, htet⟩ := M.mem_boundaryFaces_iff.mp ht
    have hsM : s ∈ M.toPlaneComplex.simplexes := by
      apply M.mem_faces_iff.mpr
      obtain ⟨u, hu, heu⟩ :=
        Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp hes).1
      exact ⟨hsne, u, hu, hses.trans (Finset.mem_powersetCard.mp heu).1⟩
    have htM : t ∈ M.toPlaneComplex.simplexes := by
      apply M.mem_faces_iff.mpr
      obtain ⟨u, hu, heu⟩ :=
        Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp het).1
      exact ⟨htne, u, hu, htet.trans (Finset.mem_powersetCard.mp heu).1⟩
    exact M.toPlaneComplex.face_inter s hsM t htM

theorem boundaryComplex_support :
    M.boundaryComplex.support = M.boundaryCarrier := by
  classical
  rw [PlaneComplex.support, boundaryCarrier]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨-, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
    exact ⟨e, he, convexHull_mono (Set.image_mono hse) hxs⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨e, he, hxe⟩ := hx
    have hene : e.Nonempty := Finset.card_pos.mp (by
      rw [M.card_of_mem_edges (M.mem_allBoundaryEdges_iff.mp he).1]
      omega)
    exact ⟨e, M.mem_boundaryFaces_iff.mpr ⟨hene, e, he, subset_rfl⟩, hxe⟩

/-- Every boundary-complex face is a face of the full mesh complex. -/
theorem boundaryComplex_simplex_mem_toPlaneComplex {s : Finset M.Vertex}
    (hs : s ∈ M.boundaryComplex.simplexes) :
    s ∈ M.toPlaneComplex.simplexes := by
  obtain ⟨hsne, e, he, hse⟩ := M.mem_boundaryFaces_iff.mp hs
  obtain ⟨u, hu, heu⟩ :=
    Finset.mem_biUnion.mp (M.mem_allBoundaryEdges_iff.mp he).1
  exact M.mem_faces_iff.mpr
    ⟨hsne, u, hu, hse.trans (Finset.mem_powersetCard.mp heu).1⟩

/-- On its closed patch, an ambient barycentric repositioning agrees with the facewise-affine
`PlaneComplex.repositionMap`. -/
theorem ambientRepositionHomeomorph_eq_repositionMap_on_support
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Set.EqOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      (M.toPlaneComplex.repositionMap position' hinj
        (fun s hs =>
          (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.affineIndependent
            s hs)
        (fun s hs t ht =>
          (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.face_inter
            s hs t ht))
      M.toPlaneComplex.support := by
  classical
  let K := M.toPlaneComplex
  let N := M.reposition position' hinj haffTriangle hinterTriangle
  have hKpure : K.IsPure2 := by
    simpa only [K] using M.toPlaneComplex_isPure2
  let haff : ∀ s : Finset M.Vertex, s ∈ K.simplexes →
      AffineIndependent ℝ fun v : s => position' v := by
    intro s hs
    exact N.toPlaneComplex.affineIndependent s hs
  let hface : ∀ s : Finset M.Vertex, s ∈ K.simplexes →
      ∀ t : Finset M.Vertex, t ∈ K.simplexes →
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)) :=
    fun s hs t ht => N.toPlaneComplex.face_inter s hs t ht
  intro x hx
  have hxK : x ∈ K.support := by simpa only [K] using hx
  rw [PlaneComplex.support] at hxK
  simp only [Set.mem_iUnion] at hxK
  obtain ⟨s, hs, hxs⟩ := hxK
  obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hxs
  obtain ⟨u, hu, hsu, hucard⟩ := hKpure s hs
  have hucell : u ∈ K.cells := Finset.mem_filter.mpr ⟨hu, hucard⟩
  have hzu : ∀ v ∉ u, z v = 0 := fun v hv => hzsupp v (fun hvs => hv (hsu hvs))
  let xa : GeometricRealization K.Vertex K.simplexes :=
    ⟨z, ⟨hz0, hz1⟩, s, hs, hzsupp⟩
  let xc : GeometricRealization K.Vertex K.cells :=
    ⟨z, ⟨hz0, hz1⟩, u, hucell, hzu⟩
  have hrmap : K.repositionMap position' hinj haff hface x =
      (K.reposition position' hinj haff hface).baryEval z := by
    rw [← hzeval]
    exact K.repositionMap_apply_realization position' hinj haff hface xa
  have hambient :
      M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
          hsupport hfrontier x = N.toPlaneComplex.baryEval z := by
    rw [ambientRepositionHomeomorph,
      extendHomeomorphByIdentity_apply_mem _ _ _ (by simpa only [K] using hx)]
    have hxc :
        (K.realizationHomeomorph hKpure).symm
          ⟨x, by simpa only [K] using hx⟩ = xc := by
      apply (K.realizationHomeomorph hKpure).injective
      apply Subtype.ext
      simpa [xc] using hzeval.symm
    rw [TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply, hxc]
  rw [hrmap, hambient]
  rfl

/-- An ambient barycentric repositioning is affine on every face of its source mesh. -/
theorem ambientRepositionHomeomorph_affineOn
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x)
    {s : Finset M.Vertex} (hs : s ∈ M.toPlaneComplex.simplexes) :
    IsAffineOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      (M.toPlaneComplex.cellCarrier s) := by
  let haff : ∀ u : Finset M.Vertex, u ∈ M.toPlaneComplex.simplexes →
      AffineIndependent ℝ fun v : u => position' v :=
    fun u hu =>
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.affineIndependent
        u hu
  let hface : ∀ u : Finset M.Vertex, u ∈ M.toPlaneComplex.simplexes →
      ∀ v : Finset M.Vertex, v ∈ M.toPlaneComplex.simplexes →
      convexHull ℝ (position' '' (u : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (v : Set M.Vertex)) =
        convexHull ℝ (position' '' ((u ∩ v : Finset M.Vertex) : Set M.Vertex)) :=
    fun u hu v hv =>
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.face_inter
        u hu v hv
  obtain ⟨g, hg⟩ := M.toPlaneComplex.repositionMap_affineOn_face
    position' hinj haff hface hs
  refine ⟨g, fun x hx => ?_⟩
  exact (M.ambientRepositionHomeomorph_eq_repositionMap_on_support position' hinj
    haffTriangle hinterTriangle hsupport hfrontier
      (M.toPlaneComplex.cellCarrier_subset_support hs hx)).trans (hg hx)

/-- An ambient barycentric repositioning, together with its original mesh, is a finite PL
homeomorphism on the closed patch. -/
noncomputable def ambientRepositionHomeomorphFinitePL
    (position' : M.Vertex → Plane)
    (hinj : Function.Injective position')
    (haffTriangle : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (hinterTriangle : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' (s : Set M.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set M.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hinj haffTriangle hinterTriangle).toPlaneComplex.support =
        M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hinj haffTriangle hinterTriangle).trans
        (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    FinitePLHomeomorphOn
      (M.ambientRepositionHomeomorph position' hinj haffTriangle hinterTriangle
        hsupport hfrontier)
      M.toPlaneComplex.support where
  complex := M.toPlaneComplex
  support_eq := rfl
  pure := M.toPlaneComplex_isPure2
  affineOn := by
    intro s hs
    exact M.ambientRepositionHomeomorph_affineOn position' hinj haffTriangle
      hinterTriangle hsupport hfrontier hs

end TriangleMesh

/-- The elementary diamond fan move is a finite PL homeomorphism on the diamond. -/
noncomputable def diamondFanAmbientHomeomorphFinitePL (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    FinitePLHomeomorphOn (diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1)
      diamondPatch := by
  refine {
    complex := (diamondFanMesh a ha0 ha1).toPlaneComplex
    support_eq := diamondFanMesh_support a ha0 ha1
    pure := (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  exact (diamondFanMesh a ha0 ha1).ambientRepositionHomeomorph_affineOn
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanReposition_support_eq_source a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1) hs

theorem diamondFanAmbientHomeomorph_image (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1 '' diamondPatch = diamondPatch := by
  rw [← diamondFanMesh_support a ha0 ha1]
  exact extendHomeomorphByIdentity_image
    (diamondFanMesh a ha0 ha1).toPlaneComplex.isCompact_support.isClosed
    (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1)
    (diamondFanPatchHomeomorph_fixed_frontier a b ha0 ha1 hb0 hb1)

/-! ## The outer kite coordinate change -/

/-- The affine formula for `thinKiteMap` on the left half-plane. -/
noncomputable def thinKiteLeftAffine (δ : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.toAffineMap.comp
    (AffineMap.pi ![cartesianX,
      thinKiteScale δ • cartesianY + (2 : ℝ)⁻¹ • cartesianX +
        AffineMap.const ℝ Plane (2 : ℝ)⁻¹])

/-- The affine formula for `thinKiteMap` on the right half-plane. -/
noncomputable def thinKiteRightAffine (δ : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.toAffineMap.comp
    (AffineMap.pi ![cartesianX,
      thinKiteScale δ • cartesianY - (2 : ℝ)⁻¹ • cartesianX +
        AffineMap.const ℝ Plane (2 : ℝ)⁻¹])

theorem thinKiteMap_eq_leftAffine (δ : ℝ) {p : Plane} (hp : p 0 ≤ 0) :
    thinKiteMap δ p = thinKiteLeftAffine δ p := by
  apply plane_ext
  · simp [thinKiteMap, thinKiteLeftAffine]
  · simp only [thinKiteMap, planePoint_apply_one]
    rw [show |p 0| = -p 0 from abs_of_nonpos hp]
    simp [thinKiteLeftAffine]
    ring

theorem thinKiteMap_eq_rightAffine (δ : ℝ) {p : Plane} (hp : 0 ≤ p 0) :
    thinKiteMap δ p = thinKiteRightAffine δ p := by
  apply plane_ext
  · simp [thinKiteMap, thinKiteRightAffine]
  · simp only [thinKiteMap, planePoint_apply_one]
    rw [show |p 0| = p 0 from abs_of_nonneg hp]
    simp [thinKiteRightAffine]
    ring

theorem nonpos_zero_of_mem_axisKite_left {lo hi : ℝ} {p : Plane}
    (hp : p ∈ convexHull ℝ
      (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _))) :
    p 0 ≤ 0 := by
  have hp' : p ∈ {q : Plane | cartesianX q ∈ Set.Iic (0 : ℝ)} := by
    apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨v, hv, rfl⟩
    fin_cases v <;> simp [axisKitePosition] at hv ⊢
  exact hp'

theorem nonneg_zero_of_mem_axisKite_right {lo hi : ℝ} {p : Plane}
    (hp : p ∈ convexHull ℝ
      (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _))) :
    0 ≤ p 0 := by
  have hp' : p ∈ {q : Plane | cartesianX q ∈ Set.Ici (0 : ℝ)} := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hp
    rintro q ⟨v, hv, rfl⟩
    fin_cases v <;> simp [axisKitePosition] at hv ⊢
  exact hp'

/-- The explicit global change from the fixed diamond to a thin kite is finite PL on the
diamond's two-triangle mesh. -/
noncomputable def thinKiteGlobalHomeomorphFinitePL (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (thinKiteGlobalHomeomorph δ hδ) diamondPatch := by
  refine {
    complex := (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).toPlaneComplex
    support_eq := (axisKiteMesh_support (-2) 2 (by norm_num) (by norm_num)).trans
      axisKitePatch_negTwo_two
    pure := (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).toPlaneComplex_isPure2
    affineOn := ?_ }
  intro s hs
  obtain ⟨-, t, ht, hst⟩ :=
    (axisKiteMesh (-2) 2 (by norm_num) (by norm_num)).mem_faces_iff.mp hs
  change Finset (Fin 4) at t
  change t ∈ axisKiteTriangles at ht
  have ht' : t = {0, 2, 3} ∨ t = {1, 2, 3} := by
    simpa [axisKiteTriangles] using ht
  rcases ht' with ht' | ht'
  · subst t
    refine ⟨thinKiteLeftAffine δ, fun p hp => ?_⟩
    change thinKiteMap δ p = thinKiteLeftAffine δ p
    apply thinKiteMap_eq_leftAffine
    apply nonpos_zero_of_mem_axisKite_left
    exact convexHull_mono (Set.image_mono hst) hp
  · subst t
    refine ⟨thinKiteRightAffine δ, fun p hp => ?_⟩
    change thinKiteMap δ p = thinKiteRightAffine δ p
    apply thinKiteMap_eq_rightAffine
    apply nonneg_zero_of_mem_axisKite_right
    exact convexHull_mono (Set.image_mono hst) hp

theorem thinKiteGlobalHomeomorph_image (δ : ℝ) (hδ : 0 < δ) :
    thinKiteGlobalHomeomorph δ hδ '' diamondPatch = thinKitePatch δ := by
  rfl

/-- The normalized thin-kite shelling move is finite PL on its kite patch. -/
noncomputable def thinKiteAmbientHomeomorphFinitePL (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (thinKiteAmbientHomeomorph δ hδ) (thinKitePatch δ) := by
  let outer := thinKiteGlobalHomeomorph δ hδ
  let move := diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  let Fouter := thinKiteGlobalHomeomorphFinitePL δ hδ
  let Fmove := diamondFanAmbientHomeomorphFinitePL
    (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  have houter : outer '' diamondPatch = thinKitePatch δ :=
    thinKiteGlobalHomeomorph_image δ hδ
  have hpull : outer.symm '' thinKitePatch δ = diamondPatch := by
    rw [← houter]
    ext p
    simp
  have hmove : move '' diamondPatch = diamondPatch :=
    diamondFanAmbientHomeomorph_image
      (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  let Fpull := Fouter.symm |>.congrSet houter
  let Fmove' := Fmove.congrSet hpull.symm
  let Ffirst := Fpull.trans Fmove'
  have hfirst : (outer.symm.trans move) '' thinKitePatch δ = diamondPatch := by
    change (fun p => move (outer.symm p)) '' thinKitePatch δ = diamondPatch
    rw [← Set.image_image, hpull, hmove]
  let Fouter' := Fouter.congrSet hfirst.symm
  let Ftotal := Ffirst.trans Fouter'
  apply Ftotal.congrHomeomorph
  apply Homeomorph.ext
  intro p
  rfl

theorem thinKiteAmbientHomeomorph_image (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ '' thinKitePatch δ = thinKitePatch δ := by
  let outer := thinKiteGlobalHomeomorph δ hδ
  let move := diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
    (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
    (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  have houter : outer '' diamondPatch = thinKitePatch δ :=
    thinKiteGlobalHomeomorph_image δ hδ
  have hpull : outer.symm '' thinKitePatch δ = diamondPatch := by
    rw [← houter]
    ext p
    simp
  have hmove : move '' diamondPatch = diamondPatch :=
    diamondFanAmbientHomeomorph_image
      (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
  change (fun p => outer (move (outer.symm p))) '' thinKitePatch δ =
    thinKitePatch δ
  rw [← Set.image_image outer (fun p => move (outer.symm p)),
    ← Set.image_image move outer.symm, hpull, hmove, houter]

/-- Affine transport preserves the finite-PL certificate for the local thin-kite move. -/
noncomputable def transportedThinKiteHomeomorphFinitePL
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ)
      (transportedThinKitePatch e δ) := by
  let affine := affineEquivHomeomorph e
  let thin := thinKiteAmbientHomeomorph δ hδ
  let Fthin := thinKiteAmbientHomeomorphFinitePL δ hδ
  let Faff := (affineEquivHomeomorphFinitePL e Fthin.complex Fthin.pure).congrSet
    Fthin.support_eq
  have hpull : affine.symm '' (affine '' thinKitePatch δ) = thinKitePatch δ := by
    ext p
    simp [affine]
  have hthin : thin '' thinKitePatch δ = thinKitePatch δ :=
    thinKiteAmbientHomeomorph_image δ hδ
  let Fpull := Faff.symm
  let Fthin' := Fthin.congrSet hpull.symm
  let Ffirst := Fpull.trans Fthin'
  have hfirst : (affine.symm.trans thin) '' (affine '' thinKitePatch δ) =
      thinKitePatch δ := by
    change (fun p => thin (affine.symm p)) '' (affine '' thinKitePatch δ) =
      thinKitePatch δ
    rw [← Set.image_image, hpull, hthin]
  let Faff' := Faff.congrSet hfirst.symm
  let Ftotal := Ffirst.trans Faff'
  have hhome : (affine.symm.trans thin).trans affine =
      transportedThinKiteHomeomorph e δ hδ := by
    apply Homeomorph.ext
    intro p
    rfl
  exact (Ftotal.congrHomeomorph hhome).congrSet rfl

theorem transportedThinKiteHomeomorph_image
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ) :
    transportedThinKiteHomeomorph e δ hδ '' transportedThinKitePatch e δ =
      transportedThinKitePatch e δ := by
  let affine := affineEquivHomeomorph e
  let thin := thinKiteAmbientHomeomorph δ hδ
  have hpull : affine.symm '' (affine '' thinKitePatch δ) = thinKitePatch δ := by
    ext p
    simp [affine]
  change (fun p => affine (thin (affine.symm p))) '' (affine '' thinKitePatch δ) =
    affine '' thinKitePatch δ
  rw [← Set.image_image affine (fun p => thin (affine.symm p)),
    ← Set.image_image thin affine.symm, hpull,
    thinKiteAmbientHomeomorph_image δ hδ]

/-- A transported local move is finite PL on any finite pure source polyhedron. -/
noncomputable def transportedThinKiteHomeomorphFinitePLOn
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ)
    (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ) K.support :=
  (transportedThinKiteHomeomorphFinitePL e δ hδ).extendByIdentity
    (transportedThinKiteHomeomorph_eqOn_compl e δ hδ) K hKpure

/-- The inverse transported local move is likewise finite PL on any finite pure polyhedron. -/
noncomputable def transportedThinKiteHomeomorphSymmFinitePLOn
    (e : Plane ≃ᵃ[ℝ] Plane) (δ : ℝ) (hδ : 0 < δ)
    (K : PlaneComplex) (hKpure : K.IsPure2) :
    FinitePLHomeomorphOn (transportedThinKiteHomeomorph e δ hδ).symm K.support := by
  let g := transportedThinKiteHomeomorph e δ hδ
  let P := transportedThinKitePatch e δ
  let F := transportedThinKiteHomeomorphFinitePL e δ hδ
  have himage : g '' P = P := transportedThinKiteHomeomorph_image e δ hδ
  let Finv := F.symm |>.congrSet himage
  have hfixInv : Set.EqOn g.symm id Pᶜ := by
    intro p hp
    apply g.symm_apply_eq.mpr
    exact (transportedThinKiteHomeomorph_eqOn_compl e δ hδ hp).symm
  exact Finv.extendByIdentity hfixInv K hKpure

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
