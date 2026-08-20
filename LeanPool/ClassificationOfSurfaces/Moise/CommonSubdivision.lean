/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.FreeTriangle

/-!
# Common subdivisions of finite plane triangle meshes

The finite common-refinement theorem used in Moise Chapter 5.  To make a source mesh
subordinate to a target mesh with the same support, cut it by every barycentric-coordinate
hyperplane of every target triangle.  The resulting chambers lie in target triangles.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- An affine map which is injective on a nondegenerate closed triangle sends its three
vertices to an affinely independent triple.

The hypothesis is deliberately local.  This is the form needed when a facewise-affine
embedding is known to be injective only on the simplex on which its affine formula is valid. -/
theorem affineIndependent_comp_of_injOn_convexHull
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] V)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    AffineIndependent ℝ (f ∘ p) := by
  classical
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro w₁ w₂ hw₁ hw₂ hw
  let B : ℝ := ∑ i : Fin 3, (|w₁ i| + |w₂ i|)
  have hB : 0 ≤ B := by
    exact Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  let r : ℝ := (6 * (B + 1))⁻¹
  have hden : 0 < 6 * (B + 1) := mul_pos (by norm_num) (by linarith)
  have hr : 0 < r := inv_pos.mpr hden
  have hrmul : r * (B + 1) = 1 / 6 := by
    dsimp only [r]
    rw [inv_mul_eq_div]
    field_simp [ne_of_gt hden]
  let u : Fin 3 → ℝ := fun _ => 1 / 3
  let x : Fin 3 → ℝ := AffineMap.lineMap u w₁ r
  let y : Fin 3 → ℝ := AffineMap.lineMap u w₂ r
  have hw₁lower (i : Fin 3) : -B ≤ w₁ i := by
    have hi :
        |w₁ i| ≤ ∑ j : Fin 3, (|w₁ j| + |w₂ j|) := by
      apply le_trans (le_add_of_nonneg_right (abs_nonneg (w₂ i)))
      exact Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (w₁ j)) (abs_nonneg (w₂ j)))
        (Finset.mem_univ i)
    exact (neg_le_of_abs_le hi)
  have hw₂lower (i : Fin 3) : -B ≤ w₂ i := by
    have hi :
        |w₂ i| ≤ ∑ j : Fin 3, (|w₁ j| + |w₂ j|) := by
      apply le_trans (le_add_of_nonneg_left (abs_nonneg (w₁ i)))
      exact Finset.single_le_sum
        (fun j _ => add_nonneg (abs_nonneg (w₁ j)) (abs_nonneg (w₂ j)))
        (Finset.mem_univ i)
    exact (neg_le_of_abs_le hi)
  have hx0 (i : Fin 3) : 0 ≤ x i := by
    have hmul := mul_le_mul_of_nonneg_left (hw₁lower i) hr.le
    dsimp only [x, u]
    rw [AffineMap.lineMap_apply_module]
    change 0 ≤ (1 - r) * (1 / 3) + r * w₁ i
    nlinarith
  have hy0 (i : Fin 3) : 0 ≤ y i := by
    have hmul := mul_le_mul_of_nonneg_left (hw₂lower i) hr.le
    dsimp only [y, u]
    rw [AffineMap.lineMap_apply_module]
    change 0 ≤ (1 - r) * (1 / 3) + r * w₂ i
    nlinarith
  have hu : ∑ i : Fin 3, u i = 1 := by
    simp [u]
  have hxsum : ∑ i : Fin 3, x i = 1 := by
    simp only [x, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hu, hw₁]
    ring
  have hysum : ∑ i : Fin 3, y i = 1 := by
    simp only [y, AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hu, hw₂]
    ring
  let px := Finset.univ.affineCombination ℝ p x
  let py := Finset.univ.affineCombination ℝ p y
  have hpx : px ∈ convexHull ℝ (Set.range p) := by
    exact affineCombination_mem_convexHull (fun i _ => hx0 i) hxsum
  have hpy : py ∈ convexHull ℝ (Set.range p) := by
    exact affineCombination_mem_convexHull (fun i _ => hy0 i) hysum
  have hfw :
      f (Finset.univ.affineCombination ℝ p w₁) =
        f (Finset.univ.affineCombination ℝ p w₂) := by
    rw [Finset.univ.map_affineCombination p w₁ hw₁ f,
      Finset.univ.map_affineCombination p w₂ hw₂ f]
    exact hw
  have hfxy : f px = f py := by
    change
      f (Finset.univ.affineCombination ℝ p x) =
        f (Finset.univ.affineCombination ℝ p y)
    rw [← Finset.univ.lineMap_affineCombination u w₁ r p,
      ← Finset.univ.lineMap_affineCombination u w₂ r p,
      f.apply_lineMap, f.apply_lineMap, hfw]
  have hpxy : px = py := hf hpx hpy hfxy
  have hxy : x = y :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ p).mp hp
      x y hxsum hysum hpxy
  funext i
  have hi := congrFun hxy i
  dsimp only [x, y, u] at hi
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hi
  change (1 - r) * (1 / 3) + r * w₁ i =
    (1 - r) * (1 / 3) + r * w₂ i at hi
  exact (mul_left_cancel₀ hr.ne' (by linarith : r * w₁ i = r * w₂ i))

/-- In the plane, local injectivity of an affine map on one nondegenerate triangle already
forces global injectivity. -/
theorem affineMap_injective_of_injOn_convexHull
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] Plane)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    Function.Injective f := by
  let q : Fin 3 → Plane := f ∘ p
  have hq : AffineIndependent ℝ q :=
    affineIndependent_comp_of_injOn_convexHull p hp f hf
  let e : Plane ≃ᵃ[ℝ] Plane := triangleAffineEquiv p q hp hq
  have hfe : f = e.toAffineMap := by
    apply AffineMap.ext_on
      ((hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp [Plane]))
    rintro x ⟨i, rfl⟩
    exact (triangleAffineEquiv_apply p q hp hq i).symm
  rw [hfe]
  exact e.injective

/-- The same local hypothesis makes a planar affine map surjective. -/
theorem affineMap_surjective_of_injOn_convexHull
    (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] Plane)
    (hf : Set.InjOn f (convexHull ℝ (Set.range p))) :
    Function.Surjective f := by
  let q : Fin 3 → Plane := f ∘ p
  have hq : AffineIndependent ℝ q :=
    affineIndependent_comp_of_injOn_convexHull p hp f hf
  let e : Plane ≃ᵃ[ℝ] Plane := triangleAffineEquiv p q hp hq
  have hfe : f = e.toAffineMap := by
    apply AffineMap.ext_on
      ((hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp [Plane]))
    rintro x ⟨i, rfl⟩
    exact (triangleAffineEquiv_apply p q hp hq i).symm
  rw [hfe]
  exact e.surjective

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Barycentric coordinates in one maximal mesh triangle, extended by zero to all mesh
vertices.  This is the triangle-mesh-native counterpart of `PlaneComplex.faceCoords`; keeping
the codomain definitionally equal to `M.Vertex → ℝ` avoids transports through
`M.toPlaneComplex.Vertex`. -/
noncomputable def triangleCoords (T : M.Triangle) :
    Plane →ᵃ[ℝ] (M.Vertex → ℝ) := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  exact AffineMap.pi fun v =>
    if hv : v ∈ T.1 then
      b.coord (M.triangleEquiv T ⟨v, hv⟩)
    else
      AffineMap.const ℝ Plane 0

@[simp] theorem triangleCoords_apply_of_mem (T : M.Triangle)
    {v : M.Vertex} (hv : v ∈ T.1) (p : Plane) :
    M.triangleCoords T p v =
      (affineBasisOfTriangle
        (M.position ∘ M.orderedVertex T)
        (M.orderedVertex_affineIndependent T)).coord
          (M.triangleEquiv T ⟨v, hv⟩) p := by
  classical
  simp [triangleCoords, hv]

@[simp] theorem triangleCoords_apply_of_notMem (T : M.Triangle)
    {v : M.Vertex} (hv : v ∉ T.1) (p : Plane) :
    M.triangleCoords T p v = 0 := by
  classical
  simp [triangleCoords, hv]

theorem triangleCoords_support (T : M.Triangle) (p : Plane) :
    ∀ v ∉ T.1, M.triangleCoords T p v = 0 :=
  fun _ hv => M.triangleCoords_apply_of_notMem T hv p

theorem sum_triangleCoords (T : M.Triangle) (p : Plane) :
    ∑ v, M.triangleCoords T p v = 1 := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  calc
    ∑ v, M.triangleCoords T p v =
        ∑ v ∈ T.1, M.triangleCoords T p v := by
      symm
      exact Finset.sum_subset (Finset.subset_univ T.1)
        (fun v _ hv => M.triangleCoords_apply_of_notMem T hv p)
    _ = ∑ v : T.1, M.triangleCoords T p v.1 := by
      rw [Finset.sum_coe_sort]
    _ =
        ∑ v : T.1, b.coord (M.triangleEquiv T v) p := by
      apply Finset.sum_congr rfl
      intro v hv
      exact M.triangleCoords_apply_of_mem T v.2 p
    _ = ∑ i : Fin 3, b.coord i p :=
      (M.triangleEquiv T).sum_comp (fun i => b.coord i p)
    _ = 1 := b.sum_coord_apply_eq_one p

theorem baryEval_triangleCoords (T : M.Triangle) (p : Plane) :
    M.toPlaneComplex.baryEval (M.triangleCoords T p) = p := by
  classical
  let b := affineBasisOfTriangle
    (M.position ∘ M.orderedVertex T)
    (M.orderedVertex_affineIndependent T)
  rw [M.toPlaneComplex.baryEval_eq_sum_of_support
    (M.triangleCoords_support T p)]
  calc
    ∑ v ∈ T.1, M.triangleCoords T p v • M.toPlaneComplex.position v =
        ∑ v : T.1, M.triangleCoords T p v.1 •
          M.toPlaneComplex.position v.1 := (Finset.sum_coe_sort T.1 _).symm
    _ = ∑ v : T.1, M.triangleCoords T p v.1 • M.position v.1 := rfl
    _ =
        ∑ v : T.1, b.coord (M.triangleEquiv T v) p •
          M.position v.1 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [M.triangleCoords_apply_of_mem T v.2 p]
    _ = ∑ i : Fin 3, b.coord i p •
          M.position (M.orderedVertex T i) := by
      calc
        _ = ∑ v : T.1, b.coord (M.triangleEquiv T v) p •
            M.position (M.orderedVertex T (M.triangleEquiv T v)) := by
          apply Finset.sum_congr rfl
          intro v hv
          congr 2
          exact congrArg Subtype.val
            ((M.triangleEquiv T).symm_apply_apply v).symm
        _ = _ :=
          (M.triangleEquiv T).sum_comp
            (fun i => b.coord i p • M.position (M.orderedVertex T i))
    _ = p := by
      change ∑ i : Fin 3, b.coord i p • b i = p
      exact b.linear_combination_coord_eq_self p

theorem triangleCoords_nonneg_of_mem (T : M.Triangle) {p : Plane}
    (hp : p ∈ M.triangleCarrier T.1) (v : M.Vertex) :
    0 ≤ M.triangleCoords T p v := by
  by_cases hv : v ∈ T.1
  · let k : Fin 3 := M.triangleEquiv T ⟨v, hv⟩
    rw [M.triangleCoords_apply_of_mem T hv p]
    change 0 ≤ M.oppositeCoord T k p
    exact M.oppositeCoord_nonneg_of_mem_parent T k hp
  · rw [M.triangleCoords_apply_of_notMem T hv p]

/-- The barycentric-coordinate hyperplanes of all maximal triangles. -/
noncomputable def coordinateLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset M.Triangle).toList.flatMap fun t =>
    (Finset.univ : Finset (Fin 3)).toList.map (M.oppositeCoord t)

theorem oppositeCoord_mem_coordinateLines (t : M.Triangle) (k : Fin 3) :
    M.oppositeCoord t k ∈ M.coordinateLines := by
  simp [coordinateLines]

/-- Cut `M` by every coordinate hyperplane of `N`. -/
noncomputable def refineTo (M N : TriangleMesh) : TriangleMesh :=
  M.refineByLines N.coordinateLines

theorem refineTo_support (N : TriangleMesh) :
    (M.refineTo N).toPlaneComplex.support = M.toPlaneComplex.support :=
  M.refineByLines_support N.coordinateLines

theorem refineTo_subdivides_left (N : TriangleMesh) :
    (M.refineTo N).toPlaneComplex.Subdivides M.toPlaneComplex :=
  M.refineByLines_subdivides N.coordinateLines

theorem refineTo_isMonochromatic (N : TriangleMesh) (t : N.Triangle) (k : Fin 3) :
    (M.refineTo N).IsMonochromatic (N.oppositeCoord t k) :=
  M.refineByLines_isMonochromatic_of_mem N.coordinateLines
    (N.oppositeCoord_mem_coordinateLines t k)

/-- The interior of a nonnegative affine half-space is its strictly positive half-space. -/
theorem interior_affine_nonneg_of_surjective (f : Plane →ᵃ[ℝ] ℝ)
    (hf : Function.Surjective f) :
    interior {x | 0 ≤ f x} = {x | 0 < f x} := by
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional hf).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

/-- The interior of a nonpositive affine half-space is its strictly negative half-space. -/
theorem interior_affine_nonpos_of_surjective (f : Plane →ᵃ[ℝ] ℝ)
    (hf : Function.Surjective f) :
    interior {x | f x ≤ 0} = {x | f x < 0} := by
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional hf).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

/-- Every maximal chamber of `M.refineTo N` lies in a maximal triangle of `N`, provided the
two original meshes have the same support. -/
theorem exists_target_triangle_of_refineTo
    (N : TriangleMesh) (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support)
    (T : (M.refineTo N).Triangle) :
    ∃ U : N.Triangle,
      (M.refineTo N).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  let R := M.refineTo N
  obtain ⟨x, hx⟩ := R.interior_triangleCarrier_nonempty T
  have hxSupport : x ∈ N.toPlaneComplex.support := by
    rw [← hsupport, ← M.refineTo_support N]
    rw [R.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨T.1, Set.mem_iUnion.mpr ⟨T.2, interior_subset hx⟩⟩
  rw [N.toPlaneComplex_support] at hxSupport
  simp only [Set.mem_iUnion] at hxSupport
  obtain ⟨u, hu, hxu⟩ := hxSupport
  let U : N.Triangle := ⟨u, hu⟩
  refine ⟨U, ?_⟩
  have hxCoordPos (k : Fin 3) : 0 < N.oppositeCoord U k x := by
    have hxnonneg : 0 ≤ N.oppositeCoord U k x :=
      N.oppositeCoord_nonneg_of_mem_parent U k hxu
    rcases M.refineTo_isMonochromatic N U k T.1 T.2 with hpos | hneg
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | 0 ≤ N.oppositeCoord U k p} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint := interior_mono hsubset hx
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonneg_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint
      exact hxint
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | N.oppositeCoord U k p ≤ 0} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint := interior_mono hsubset hx
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonpos_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint
      change N.oppositeCoord U k x < 0 at hxint
      linarith
  intro p hp
  let b := affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
    (N.orderedVertex_affineIndependent U)
  have hcarrier : N.triangleCarrier U.1 = {q | ∀ k : Fin 3, 0 ≤ b.coord k q} := by
    rw [TriangleMesh.triangleCarrier]
    have hrange : N.position '' (U.1 : Set N.Vertex) = Set.range b := by
      change N.position '' (U.1 : Set N.Vertex) =
        Set.range (N.position ∘ N.orderedVertex U)
      rw [Set.range_comp, N.range_orderedVertex U]
    rw [hrange, b.convexHull_eq_nonneg_coord]
  rw [hcarrier]
  intro k
  change 0 ≤ N.oppositeCoord U k p
  rcases M.refineTo_isMonochromatic N U k T.1 T.2 with hpos | hneg
  · apply convexHull_min ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k)) hp
    rintro q ⟨v, hv, rfl⟩
    exact hpos v hv
  · have hsubset : R.triangleCarrier T.1 ⊆ {q | N.oppositeCoord U k q ≤ 0} := by
      apply convexHull_min
      · rintro q ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
    have hpnonpos := hsubset hp
    have hxpos := hxCoordPos k
    have hxnonpos := hsubset (interior_subset hx)
    exfalso
    exact (not_lt_of_ge hxnonpos) hxpos

/-- A chamber cut by at least all target coordinate lines and whose interior meets the target
support lies in one target triangle. -/
theorem exists_target_triangle_of_refineByLines_of_interior_inter_support
    (N : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hlines : ∀ a ∈ N.coordinateLines, a ∈ lines)
    (T : (M.refineByLines lines).Triangle)
    (hhit : (interior ((M.refineByLines lines).triangleCarrier T.1) ∩
      N.toPlaneComplex.support).Nonempty) :
    ∃ U : N.Triangle,
      (M.refineByLines lines).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  let R := M.refineByLines lines
  obtain ⟨x, hxint, hxSupport⟩ := hhit
  rw [N.toPlaneComplex_support] at hxSupport
  simp only [Set.mem_iUnion] at hxSupport
  obtain ⟨u, hu, hxu⟩ := hxSupport
  let U : N.Triangle := ⟨u, hu⟩
  refine ⟨U, ?_⟩
  have hmono (k : Fin 3) : R.IsMonochromatic (N.oppositeCoord U k) :=
    M.refineByLines_isMonochromatic_of_mem lines
      (hlines _ (N.oppositeCoord_mem_coordinateLines U k))
  have hxCoordPos (k : Fin 3) : 0 < N.oppositeCoord U k x := by
    have hxnonneg : 0 ≤ N.oppositeCoord U k x :=
      N.oppositeCoord_nonneg_of_mem_parent U k hxu
    rcases hmono k T.1 T.2 with hpos | hneg
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | 0 ≤ N.oppositeCoord U k p} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hpos v hv
        · exact ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint' := interior_mono hsubset hxint
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonneg_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint'
      exact hxint'
    · have hsubset : R.triangleCarrier T.1 ⊆ {p | N.oppositeCoord U k p ≤ 0} := by
        apply convexHull_min
        · rintro p ⟨v, hv, rfl⟩
          exact hneg v hv
        · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
      have hxint' := interior_mono hsubset hxint
      have hsurj : Function.Surjective (N.oppositeCoord U k) := by
        simpa only [oppositeCoord] using
          (affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
            (N.orderedVertex_affineIndependent U)).surjective_coord k
      rw [interior_affine_nonpos_of_surjective (N.oppositeCoord U k)
        hsurj] at hxint'
      change N.oppositeCoord U k x < 0 at hxint'
      linarith
  intro p hp
  let b := affineBasisOfTriangle (N.position ∘ N.orderedVertex U)
    (N.orderedVertex_affineIndependent U)
  have hcarrier : N.triangleCarrier U.1 = {q | ∀ k : Fin 3, 0 ≤ b.coord k q} := by
    rw [TriangleMesh.triangleCarrier]
    have hrange : N.position '' (U.1 : Set N.Vertex) = Set.range b := by
      change N.position '' (U.1 : Set N.Vertex) =
        Set.range (N.position ∘ N.orderedVertex U)
      rw [Set.range_comp, N.range_orderedVertex U]
    rw [hrange, b.convexHull_eq_nonneg_coord]
  rw [hcarrier]
  intro k
  change 0 ≤ N.oppositeCoord U k p
  rcases hmono k T.1 T.2 with hpos | hneg
  · apply convexHull_min ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (N.oppositeCoord U k)) hp
    rintro q ⟨v, hv, rfl⟩
    exact hpos v hv
  · have hsubset : R.triangleCarrier T.1 ⊆ {q | N.oppositeCoord U k q ≤ 0} := by
      apply convexHull_min
      · rintro q ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact ((convex_Iic (0 : ℝ)).affine_preimage (N.oppositeCoord U k))
    have hxnonpos := hsubset (interior_subset hxint)
    exact False.elim ((not_lt_of_ge hxnonpos) (hxCoordPos k))

/-- A chamber whose interior meets the target support lies in one target triangle.  Unlike
`exists_target_triangle_of_refineTo`, the source and target supports need not agree. -/
theorem exists_target_triangle_of_refineTo_of_interior_inter_support
    (N : TriangleMesh) (T : (M.refineTo N).Triangle)
    (hhit : (interior ((M.refineTo N).triangleCarrier T.1) ∩
      N.toPlaneComplex.support).Nonempty) :
    ∃ U : N.Triangle,
      (M.refineTo N).triangleCarrier T.1 ⊆ N.triangleCarrier U.1 := by
  exact M.exists_target_triangle_of_refineByLines_of_interior_inter_support N
    N.coordinateLines (fun _ ha => ha) T hhit

/-- Cut `M` by every face line of `N`, then retain exactly the chambers whose interiors meet
the support of `N`.  This is the unequal-support version of common refinement used in the local
Radó weld. -/
noncomputable def refineToSupport (N : TriangleMesh) : TriangleMesh :=
  by
    classical
    exact (M.refineTo N).restrictTriangles fun t ↦
      (interior ((M.refineTo N).triangleCarrier t) ∩
        N.toPlaneComplex.support).Nonempty

theorem refineToSupport_triangle_mem (N : TriangleMesh)
    {t : Finset (M.refineToSupport N).Vertex} :
    t ∈ (M.refineToSupport N).triangles ↔
      t ∈ (M.refineTo N).triangles ∧
        (interior ((M.refineTo N).triangleCarrier t) ∩
          N.toPlaneComplex.support).Nonempty := by
  classical
  exact (M.refineTo N).mem_restrictTriangles_triangles _

/-- If the source mesh contains the target support, restricting their line refinement recovers
the target support exactly. -/
theorem refineToSupport_support (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆ M.toPlaneComplex.support) :
    (M.refineToSupport N).toPlaneComplex.support =
      N.toPlaneComplex.support := by
  classical
  let R := M.refineTo N
  let L := M.refineToSupport N
  apply Set.Subset.antisymm
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    have htData := (M.refineToSupport_triangle_mem N).mp ht
    let T : R.Triangle := ⟨t, htData.1⟩
    obtain ⟨U, hTU⟩ :=
      M.exists_target_triangle_of_refineTo_of_interior_inter_support N T htData.2
    rw [TriangleMesh.toPlaneComplex_support]
    exact Set.mem_iUnion.mpr ⟨U.1, Set.mem_iUnion.mpr ⟨U.2, hTU hxt⟩⟩
  · rw [TriangleMesh.toPlaneComplex_support]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    let U : N.Triangle := ⟨u, hu⟩
    have hinterior : interior (N.triangleCarrier u) ⊆
        L.toPlaneComplex.support := by
      intro y hy
      have hyN : y ∈ N.toPlaneComplex.support := by
        rw [TriangleMesh.toPlaneComplex_support]
        exact Set.mem_iUnion.mpr
          ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hy⟩⟩
      have hyR₀ : y ∈ (M.refineTo N).toPlaneComplex.support := by
        rw [M.refineTo_support N]
        exact hsub hyN
      have hyR : y ∈ R.toPlaneComplex.support := by
        simpa only [R] using hyR₀
      rw [TriangleMesh.toPlaneComplex_support] at hyR
      simp only [Set.mem_iUnion] at hyR
      obtain ⟨t, ht, hyt⟩ := hyR
      let T : R.Triangle := ⟨t, ht⟩
      have hyClosure : y ∈ closure (interior (R.triangleCarrier t)) := by
        rw [R.closure_interior_triangleCarrier T]
        exact hyt
      have hyInterClosure : y ∈ closure
          (interior (N.triangleCarrier u) ∩
            interior (R.triangleCarrier t)) :=
        isOpen_interior.inter_closure ⟨hy, hyClosure⟩
      obtain ⟨z, hzN, hzR⟩ := Set.Nonempty.of_closure ⟨y, hyInterClosure⟩
      have htKeep : t ∈ L.triangles :=
        (M.refineToSupport_triangle_mem N).mpr
          ⟨ht, ⟨z, hzR, by
            rw [TriangleMesh.toPlaneComplex_support]
            exact Set.mem_iUnion.mpr
              ⟨u, Set.mem_iUnion.mpr ⟨hu, interior_subset hzN⟩⟩⟩⟩
      rw [TriangleMesh.toPlaneComplex_support]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨htKeep, hyt⟩⟩
    change x ∈ N.triangleCarrier u at hxu
    rw [← N.closure_interior_triangleCarrier U] at hxu
    exact closure_minimal hinterior L.toPlaneComplex.isCompact_support.isClosed hxu

/-- The support-restricted refinement is a genuine subdivision of the smaller target mesh. -/
theorem refineToSupport_subdivides (N : TriangleMesh)
    (hsub : N.toPlaneComplex.support ⊆ M.toPlaneComplex.support) :
    (M.refineToSupport N).toPlaneComplex.Subdivides N.toPlaneComplex := by
  constructor
  · exact M.refineToSupport_support N hsub
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := (M.refineToSupport N).mem_faces_iff.mp hs
    have htData := (M.refineToSupport_triangle_mem N).mp ht
    let T : (M.refineTo N).Triangle := ⟨t, htData.1⟩
    obtain ⟨U, hTU⟩ :=
      M.exists_target_triangle_of_refineTo_of_interior_inter_support N T htData.2
    refine ⟨U.1, N.mem_faces_iff.mpr ⟨?_, U.1, U.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [N.card_triangle U.1 U.2]; omega)
    · exact (convexHull_mono (Set.image_mono hst)).trans hTU

/-- `M.refineTo N` is a subdivision of `N` when the two meshes have the same support. -/
theorem refineTo_subdivides_right (N : TriangleMesh)
    (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support) :
    (M.refineTo N).toPlaneComplex.Subdivides N.toPlaneComplex := by
  constructor
  · exact (M.refineTo_support N).trans hsupport
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := (M.refineTo N).mem_faces_iff.mp hs
    let T : (M.refineTo N).Triangle := ⟨t, ht⟩
    obtain ⟨U, hTU⟩ := M.exists_target_triangle_of_refineTo N hsupport T
    refine ⟨U.1, N.mem_faces_iff.mpr ⟨?_, U.1, U.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [N.card_triangle U.1 U.2]; omega)
    · exact (convexHull_mono (Set.image_mono hst)).trans hTU

/-- Two finite plane triangle meshes with equal support have an explicit common subdivision. -/
theorem exists_common_subdivision (N : TriangleMesh)
    (hsupport : M.toPlaneComplex.support = N.toPlaneComplex.support) :
    ∃ R : TriangleMesh,
      R.toPlaneComplex.Subdivides M.toPlaneComplex ∧
        R.toPlaneComplex.Subdivides N.toPlaneComplex := by
  exact ⟨M.refineTo N, M.refineTo_subdivides_left N,
    M.refineTo_subdivides_right N hsupport⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Regard the two-dimensional faces of a plane complex as the maximal triangles of a mesh. -/
noncomputable def toTriangleMesh : TriangleMesh where
  Vertex := K.Vertex
  position := K.position
  position_injective := K.position_injective
  triangles := K.cells
  card_triangle := fun _ ht => K.card_of_mem_cells ht
  affineIndependent_triangle := fun t ht => K.affineIndependent t (K.mem_simplexes_of_mem_cells ht)
  triangle_inter := fun s hs t ht =>
    K.face_inter s (K.mem_simplexes_of_mem_cells hs) t (K.mem_simplexes_of_mem_cells ht)

@[simp] theorem toTriangleMesh_position : K.toTriangleMesh.position = K.position := rfl

@[simp] theorem toTriangleMesh_triangles : K.toTriangleMesh.triangles = K.cells := rfl

/-- Passing a pure two-dimensional complex to its maximal-triangle mesh preserves support. -/
theorem toTriangleMesh_support (hpure : K.IsPure2) :
    K.toTriangleMesh.toPlaneComplex.support = K.support := by
  rw [TriangleMesh.toPlaneComplex_support]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    exact K.cellCarrier_subset_support (K.mem_simplexes_of_mem_cells ht) hxt
  · intro x hx
    rw [PlaneComplex.support] at hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    have htcell : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    exact ⟨t, htcell, convexHull_mono (Set.image_mono hst) hxs⟩

/-- The maximal-triangle mesh of a pure complex is a subdivision of the original complex. -/
theorem toTriangleMesh_toPlaneComplex_subdivides (hpure : K.IsPure2) :
    K.toTriangleMesh.toPlaneComplex.Subdivides K := by
  constructor
  · exact K.toTriangleMesh_support hpure
  · intro s hs
    obtain ⟨-, t, ht, hst⟩ := K.toTriangleMesh.mem_faces_iff.mp hs
    exact ⟨t, K.mem_simplexes_of_mem_cells ht,
      convexHull_mono (Set.image_mono hst)⟩

/-- Pure finite plane complexes with equal support have a common triangle-mesh subdivision. -/
theorem exists_common_subdivision {K L : PlaneComplex}
    (hKpure : K.IsPure2) (hLpure : L.IsPure2) (hsupport : K.support = L.support) :
    ∃ R : TriangleMesh,
      R.toPlaneComplex.Subdivides K ∧ R.toPlaneComplex.Subdivides L := by
  have hmeshSupport : K.toTriangleMesh.toPlaneComplex.support =
      L.toTriangleMesh.toPlaneComplex.support := by
    rw [K.toTriangleMesh_support hKpure, L.toTriangleMesh_support hLpure, hsupport]
  obtain ⟨R, hRK, hRL⟩ := K.toTriangleMesh.exists_common_subdivision
    L.toTriangleMesh hmeshSupport
  refine ⟨R, hRK.trans ?_, hRL.trans ?_⟩
  · constructor
    · exact K.toTriangleMesh_support hKpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := K.toTriangleMesh.mem_faces_iff.mp hs
      exact ⟨t, K.mem_simplexes_of_mem_cells ht,
        convexHull_mono (Set.image_mono hst)⟩
  · constructor
    · exact L.toTriangleMesh_support hLpure
    · intro s hs
      obtain ⟨-, t, ht, hst⟩ := L.toTriangleMesh.mem_faces_iff.mp hs
      exact ⟨t, L.mem_simplexes_of_mem_cells ht,
        convexHull_mono (Set.image_mono hst)⟩

end PlaneComplex

/-- An affine self-map of the plane which is injective on a set with nonempty interior is
injective everywhere. -/
theorem affineMap_injective_of_injOn_of_interior_nonempty
    (g : Plane →ᵃ[ℝ] Plane) {A : Set Plane} (hA : (interior A).Nonempty)
    (hinj : Set.InjOn g A) : Function.Injective g := by
  intro p q hpq
  by_contra hpqne
  obtain ⟨x, hx⟩ := hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let d : Plane := q - p
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hpqne)
  have hnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let t : ℝ := r / (2 * ‖d‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hnorm)
  let y : Plane := t • d + x
  have hyball : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show y - x = t • d by simp [y]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hnormne : ‖d‖ ≠ 0 := hnorm.ne'
    field_simp [hnormne]
    nlinarith
  have hyA : y ∈ A := hball hyball
  have hxA : x ∈ A := interior_subset hx
  have hgy : g y = g x := by
    change g (t • d +ᵥ x) = g x
    rw [g.map_vadd, map_smul, show d = q -ᵥ p by rfl, g.linearMap_vsub, hpq,
      vsub_self, smul_zero, zero_vadd]
  have hyx : y = x := hinj hyA hxA hgy
  have htd : t • d = 0 := by
    change t • d + x = x at hyx
    exact add_right_cancel (hyx.trans (zero_add x).symm)
  exact hd ((smul_eq_zero.mp htd).resolve_left ht.ne')

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Map a complex through a facewise-affine map which is injective only on its support.

Unlike `mapComplex`, this construction does not require an irrelevant global injectivity
hypothesis.  The additional vertex hypothesis excludes unused vertices, whose images would not
be controlled by injectivity on the support. -/
noncomputable def mapComplexOn (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := by
    intro v w hvw
    exact K.position_injective (hinj (hvertex v) (hvertex w) hvw)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    by_cases hcard : s.card ≤ 2
    · let A : Finset Plane := s.image (f ∘ K.position)
      have hAcard : A.card ≤ 2 := Finset.card_image_le.trans hcard
      let e : s ↪ A :=
        { toFun := fun v =>
            ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
          inj' := by
            intro v w hvw
            apply Subtype.ext
            apply K.position_injective
            apply hinj (hvertex v) (hvertex w)
            exact congrArg Subtype.val hvw }
      exact (affineIndependent_finset_of_card_le_two A hAcard).comp_embedding e
    · have hcard3 : s.card = 3 := by
        have := K.card_le_three s hs
        omega
      obtain ⟨g, hfg⟩ := haffine s hs
      have hinterior : (interior (K.cellCarrier s)).Nonempty := by
        rw [PlaneComplex.cellCarrier]
        have hrange : Set.range (fun v : s => K.position v) =
            K.position '' (s : Set K.Vertex) := by
          ext x
          simp
        rw [← hrange]
        apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
        exact ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
          (by simp [hcard3, Plane])
      have hgInjOn : Set.InjOn g (K.cellCarrier s) := by
        intro x hx y hy hxy
        apply hinj (K.cellCarrier_subset_support hs hx) (K.cellCarrier_subset_support hs hy)
        rw [hfg hx, hfg hy]
        exact hxy
      have hgInj : Function.Injective g :=
        affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
      have hmap := (K.affineIndependent s hs).map' g hgInj
      convert hmap using 1
      funext v
      simpa only [Function.comp_apply] using
        hfg (subset_convexHull ℝ _ ⟨v, v.2, rfl⟩)
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hsource : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hsource]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

theorem mapComplexOn_cellCarrier (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapComplexOn f hvertex hinj haffine).cellCarrier s =
      f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

theorem mapComplexOn_support (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplexOn f hvertex hinj haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapComplexOn_cellCarrier f hvertex hinj haffine hs] at hxs
    obtain ⟨y, hys, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hys⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hys⟩, rfl⟩
    exact ⟨s, hs, by
      rw [K.mapComplexOn_cellCarrier f hvertex hinj haffine hs]
      exact ⟨y, hys, rfl⟩⟩

theorem IsPure2.mapComplexOn (hpure : K.IsPure2) (f : Plane → Plane)
    (hvertex : ∀ v : K.Vertex, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplexOn f hvertex hinj haffine).IsPure2 := by
  intro s hs
  exact hpure s hs

/-- Map every face of a finite plane complex through a facewise-affine embedding. -/
noncomputable def mapComplex (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := by
    intro v w hvw
    exact K.position_injective (hinj hvw)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    by_cases hcard : s.card ≤ 2
    · let A : Finset Plane := s.image (f ∘ K.position)
      have hAcard : A.card ≤ 2 := (Finset.card_image_le.trans hcard)
      have hAI := affineIndependent_finset_of_card_le_two A hAcard
      let e : s ↪ A :=
        { toFun := fun v => ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
          inj' := by
            intro v w hvw
            apply Subtype.ext
            apply K.position_injective
            apply hinj
            exact congrArg Subtype.val hvw }
      exact hAI.comp_embedding e
    · have hcard3 : s.card = 3 := by
        have := K.card_le_three s hs
        omega
      obtain ⟨g, hfg⟩ := haffine s hs
      have hinterior : (interior (K.cellCarrier s)).Nonempty := by
        rw [PlaneComplex.cellCarrier]
        have hrange : Set.range (fun v : s => K.position v) =
            K.position '' (s : Set K.Vertex) := by
          ext x
          simp
        rw [← hrange]
        apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
        exact ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
          (by simp [hcard3, Plane])
      have hgInjOn : Set.InjOn g (K.cellCarrier s) := by
        intro x hx y hy hxy
        apply hinj
        rw [hfg hx, hfg hy]
        exact hxy
      have hgInj : Function.Injective g :=
        affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
      have hmap := (K.affineIndependent s hs).map' g hgInj
      convert hmap using 1
      funext v
      simpa only [Function.comp_apply] using
        hfg (subset_convexHull ℝ _ ⟨v, v.2, rfl⟩)
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.injOn.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hsource : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hsource]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

theorem mapComplex_cellCarrier (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapComplex f hinj haffine).cellCarrier s = f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

theorem mapComplex_support (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplex f hinj haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapComplex_cellCarrier f hinj haffine hs] at hxs
    obtain ⟨y, hys, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hys⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hys⟩, rfl⟩
    exact ⟨s, hs, by
      rw [K.mapComplex_cellCarrier f hinj haffine hs]
      exact ⟨y, hys, rfl⟩⟩

theorem IsPure2.mapComplex (hpure : K.IsPure2) (f : Plane → Plane)
    (hinj : Function.Injective f)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapComplex f hinj haffine).IsPure2 := by
  intro s hs
  exact hpure s hs

/-- On every subdivision of the image complex, the inverse homeomorphism is affine facewise.
The proof enlarges each image face to a 2-face, where its affine witness is globally invertible. -/
theorem inverse_affineOn_of_subdivides_mapComplex
    (hpure : K.IsPure2) (h : Plane ≃ₜ Plane)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn h (K.cellCarrier s))
    {R : PlaneComplex}
    (hR : R.Subdivides (K.mapComplex h h.injective haffine)) :
    ∀ s ∈ R.simplexes, IsAffineOn h.symm (R.cellCarrier s) := by
  intro s hs
  obtain ⟨u, hu, hsu⟩ := hR.2 s hs
  obtain ⟨t, ht, hut, htcard⟩ := hpure u hu
  have htcell : t ∈ K.simplexes := ht
  have hutCarrier :
      (K.mapComplex h h.injective haffine).cellCarrier u ⊆
        (K.mapComplex h h.injective haffine).cellCarrier t :=
    convexHull_mono (Set.image_mono hut)
  have hsTarget : R.cellCarrier s ⊆ h '' K.cellCarrier t := by
    exact hsu.trans (hutCarrier.trans_eq
      (K.mapComplex_cellCarrier h h.injective haffine htcell))
  obtain ⟨g, hgh⟩ := haffine t htcell
  have hinterior : (interior (K.cellCarrier t)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have hrange : Set.range (fun v : t => K.position v) =
        K.position '' (t : Set K.Vertex) := by
      ext x
      simp
    rw [← hrange]
    apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
    exact ((K.affineIndependent t htcell).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr
      (by simp [htcard, Plane])
  have hgInjOn : Set.InjOn g (K.cellCarrier t) := by
    intro x hx y hy hxy
    apply h.injective
    rw [hgh hx, hgh hy]
    exact hxy
  have hgInj : Function.Injective g :=
    affineMap_injective_of_injOn_of_interior_nonempty g hinterior hgInjOn
  have hgLinearInj : Function.Injective g.linear := g.linear_injective_iff.mpr hgInj
  have hgLinearSurj : Function.Surjective g.linear :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hgLinearInj
  have hgBij : Function.Bijective g := g.linear_bijective_iff.mp
    ⟨hgLinearInj, hgLinearSurj⟩
  let e : Plane ≃ᵃ[ℝ] Plane := AffineEquiv.ofBijective hgBij
  refine ⟨e.symm.toAffineMap, fun y hy => ?_⟩
  obtain ⟨x, hxt, hxy⟩ := hsTarget hy
  subst y
  change h.symm (h x) = e.symm (h x)
  rw [h.symm_apply_apply, hgh hxt]
  exact (e.symm_apply_apply x).symm

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
