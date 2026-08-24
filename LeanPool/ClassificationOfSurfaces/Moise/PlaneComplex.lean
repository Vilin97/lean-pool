/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Topology.LocallyFinite
import LeanPool.ClassificationOfSurfaces.Moise.GeometricTriangulation

/-!
# Finite simplicial complexes in the plane

The shared geometric foundation for the Moise route (Moise, *Geometric Topology in Dimensions
2 and 3*, Ch. 0 and Ch. 7 conventions): finite complexes of genuine affine simplexes in the
Euclidean plane.

The support of a `PlaneComplex` is *defined* as the union of the convex hulls of its faces, vertex
positions are actual points, faces are affinely independent, and distinct faces meet in the hull
of their shared vertex set. None of these fields is satisfiable by bookkeeping alone:
`face_inter` is a genuine geometric constraint (it fails, for example, for two triangles that
overlap in an open region).

`IsAffineOn`/`IsPLOn` give the honest piecewise-linear predicates: a map is PL on a complex when
it is affine on every face of some subdivision.  A generic continuous map is *not* PL on any
complex with a 2-face, in contrast to the vacuous `IsPLOnSimplexes` this replaces.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

instance finsetMemDecidablePred {α : Type*} [DecidableEq α] (v : α) :
    DecidablePred (fun s : Finset α => v ∈ s) :=
  fun s => Finset.decidableMem v s

/-- The Euclidean plane used throughout the Moise route. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- A closed triangle in the plane: the convex hull of three affinely independent points. -/
def IsTriangle (C : Set Plane) : Prop :=
  ∃ p : Fin 3 → Plane, AffineIndependent ℝ p ∧ C = convexHull ℝ (Set.range p)

/-- Two plane points with equal coordinates are equal. -/
theorem plane_ext {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Affine independence transports to the inclusion of a finite set of points contained in the
range of the independent family. -/
theorem affineIndependent_finset_coe {ι : Type*} {f : ι → Plane}
    (hf : AffineIndependent ℝ f) {S : Finset Plane} (hS : ∀ a ∈ S, a ∈ Set.range f) :
    AffineIndependent ℝ ((↑) : S → Plane) := by
  classical
  choose g hg using fun a : S => hS a.1 a.2
  have hinj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    rw [← hg a, ← hg b, hab]
  have heq : ((↑) : S → Plane) = f ∘ g := by
    funext a
    exact (hg a).symm
  rw [heq]
  exact hf.comp_embedding ⟨g, hinj⟩

/-- Every finite set of at most two distinct plane points is affinely independent. -/
theorem affineIndependent_finset_of_card_le_two (A : Finset Plane) (hcard : A.card ≤ 2) :
    AffineIndependent ℝ ((↑) : A → Plane) := by
  interval_cases h : A.card
  · rw [Finset.card_eq_zero.mp h]
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    have hp : AffineIndependent ℝ ![a, b] := affineIndependent_of_ne (k := ℝ) hab
    apply affineIndependent_finset_coe hp
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- Adjacent edges of an affinely independent triple meet exactly in the shared vertex. -/
theorem segment_inter_segment_of_affineIndependent {x y z : Plane}
    (h : AffineIndependent ℝ ![x, y, z]) :
    segment ℝ x y ∩ segment ℝ y z = {y} := by
  classical
  have hxz : x ≠ z := h.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hS : AffineIndependent ℝ ((↑) : ({x, y, z} : Finset Plane) → Plane) := by
    refine affineIndependent_finset_coe h fun a ha => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hsub₁ : ({x, y} : Finset Plane) ⊆ {x, y, z} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    tauto
  have hsub₂ : ({y, z} : Finset Plane) ⊆ {x, y, z} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    tauto
  have hmain := hS.convexHull_inter hsub₁ hsub₂
  have hinter : ({x, y} ∩ {y, z} : Finset Plane) = {y} := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h₁, rfl | rfl⟩
      · rfl
      · rcases h₁ with rfl | rfl
        · exact absurd rfl hxz
        · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  rw [← Finset.coe_inter, hinter] at hmain
  simpa [Finset.coe_insert, Finset.coe_singleton, convexHull_pair, convexHull_singleton]
    using hmain.symm

/-- Every positive ball about one endpoint of a nondegenerate segment contains a relative
interior point of that segment. -/
theorem exists_mem_openSegment_inter_ball {a b : Plane} (hab : a ≠ b)
    {r : ℝ} (hr : 0 < r) :
    ∃ x : Plane, x ∈ openSegment ℝ a b ∧ x ∈ Metric.ball a r := by
  let d := dist a b
  have hd : 0 < d := dist_pos.mpr hab
  let t := min ((1 : ℝ) / 2) (r / (2 * d))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let x := AffineMap.lineMap a b t
  refine ⟨x, ?_, ?_⟩
  · rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨ht, ht1⟩, rfl⟩
  · rw [Metric.mem_ball, show dist x a = ‖t‖ * d by
      simp [x, d]]
    rw [Real.norm_eq_abs, abs_of_pos ht]
    have htle : t ≤ r / (2 * d) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right htle hd.le
    have hcalc : (r / (2 * d)) * d = r / 2 := by
      field_simp [hd.ne']
    rw [hcalc] at hmul
    linarith

/-- An endpoint of a nondegenerate segment cannot lie strictly between two distinct points of
that segment. -/
theorem endpoint_not_mem_openSegment_of_mem_segment {a b x y : Plane}
    (hab : a ≠ b) (hxy : x ≠ y) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) : a ∉ openSegment ℝ x y := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  intro ha
  rw [openSegment_eq_image_lineMap] at ha
  obtain ⟨u, hu, huEq⟩ := ha
  let c := (1 - u) * s + u * t
  have hmaps : AffineMap.lineMap (k := ℝ) a b 0 = AffineMap.lineMap (k := ℝ) a b c := by
    calc
      AffineMap.lineMap (k := ℝ) a b 0 = a := by simp
      _ = AffineMap.lineMap (k := ℝ) (AffineMap.lineMap (k := ℝ) a b s)
          (AffineMap.lineMap (k := ℝ) a b t) u := huEq.symm
      _ = AffineMap.lineMap (k := ℝ) a b c := by
        ext i
        simp [c, AffineMap.lineMap_apply_module]
        ring
  have hc : c = 0 := by
    exact (AffineMap.lineMap_injective ℝ hab hmaps).symm
  have hcoeff : 0 < 1 - u := sub_pos.mpr hu.2
  have htermS : 0 ≤ (1 - u) * s := mul_nonneg hcoeff.le hs.1
  have htermT : 0 ≤ u * t := mul_nonneg hu.1.le ht.1
  have htermS0 : (1 - u) * s = 0 := by
    dsimp [c] at hc
    nlinarith
  have htermT0 : u * t = 0 := by
    dsimp [c] at hc
    nlinarith
  have hs0 : s = 0 := (mul_eq_zero.mp htermS0).resolve_left hcoeff.ne'
  have ht0 : t = 0 := (mul_eq_zero.mp htermT0).resolve_left hu.1.ne'
  apply hxy
  rw [hs0, ht0]

/-- If two collinear points bracket the midpoint of a segment and neither lies in its relative
interior, then they bracket the whole segment. -/
theorem segment_subset_of_midpoint_mem_openSegment
    {P Q A B : Plane} (hPQ : P ≠ Q)
    (hAline : A ∈ affineSpan ℝ ({P, Q} : Set Plane))
    (hBline : B ∈ affineSpan ℝ ({P, Q} : Set Plane))
    (hmid : AffineMap.lineMap P Q (1 / 2 : ℝ) ∈ openSegment ℝ A B)
    (hAoutside : A ∉ openSegment ℝ P Q)
    (hBoutside : B ∉ openSegment ℝ P Q) :
    segment ℝ P Q ⊆ segment ℝ A B := by
  obtain ⟨a, ha⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hAline
  obtain ⟨b, hb⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hBline
  rw [openSegment_eq_image_lineMap] at hmid
  obtain ⟨u, hu, hum⟩ := hmid
  have hcompose :
      AffineMap.lineMap A B u =
        AffineMap.lineMap P Q ((1 - u) * a + u * b) := by
    rw [← ha, ← hb]
    ext k
    simp [AffineMap.lineMap_apply_module]
    ring
  have hparam : (1 - u) * a + u * b = 1 / 2 := by
    apply AffineMap.lineMap_injective ℝ hPQ
    rw [← hcompose]
    exact hum
  have haOutside : a ≤ 0 ∨ 1 ≤ a := by
    by_cases ha0 : a ≤ 0
    · exact Or.inl ha0
    · right
      apply le_of_not_gt
      intro ha1
      exact hAoutside (ha ▸ lineMap_mem_openSegment ℝ P Q ⟨lt_of_not_ge ha0, ha1⟩)
  have hbOutside : b ≤ 0 ∨ 1 ≤ b := by
    by_cases hb0 : b ≤ 0
    · exact Or.inl hb0
    · right
      apply le_of_not_gt
      intro hb1
      exact hBoutside (hb ▸ lineMap_mem_openSegment ℝ P Q ⟨lt_of_not_ge hb0, hb1⟩)
  have hbracket : (a ≤ 0 ∧ 1 ≤ b) ∨ (b ≤ 0 ∧ 1 ≤ a) := by
    rcases haOutside with ha0 | ha1 <;> rcases hbOutside with hb0 | hb1
    · have hleft : (1 - u) * a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.2]) ha0
      have hright : u * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1.le hb0
      exfalso
      norm_num at hparam
      linarith
    · exact Or.inl ⟨ha0, hb1⟩
    · exact Or.inr ⟨hb0, ha1⟩
    · have hleft : 0 ≤ (1 - u) * (a - 1) :=
        mul_nonneg (by linarith [hu.2]) (sub_nonneg.mpr ha1)
      have hright : 0 ≤ u * (b - 1) :=
        mul_nonneg hu.1.le (sub_nonneg.mpr hb1)
      exfalso
      norm_num at hparam
      nlinarith
  have endpoints_mem (h : a ≤ 0 ∧ 1 ≤ b) :
      P ∈ segment ℝ A B ∧ Q ∈ segment ℝ A B := by
    have hab : a ≤ b := (h.1.trans (by norm_num : (0 : ℝ) ≤ 1)).trans h.2
    have hpScalar : Wbtw ℝ a 0 b :=
      (wbtw_iff_of_le hab).mpr ⟨h.1, (by norm_num : (0 : ℝ) ≤ 1).trans h.2⟩
    have hqScalar : Wbtw ℝ a 1 b :=
      (wbtw_iff_of_le hab).mpr ⟨h.1.trans (by norm_num), h.2⟩
    have hp := hpScalar.map (AffineMap.lineMap P Q)
    have hq := hqScalar.map (AffineMap.lineMap P Q)
    rw [ha, hb] at hp hq
    simpa using And.intro hp.mem_segment hq.mem_segment
  have endpoints_mem_rev (h : b ≤ 0 ∧ 1 ≤ a) :
      P ∈ segment ℝ B A ∧ Q ∈ segment ℝ B A := by
    have hba : b ≤ a := (h.1.trans (by norm_num : (0 : ℝ) ≤ 1)).trans h.2
    have hpScalar : Wbtw ℝ b 0 a :=
      (wbtw_iff_of_le hba).mpr ⟨h.1, (by norm_num : (0 : ℝ) ≤ 1).trans h.2⟩
    have hqScalar : Wbtw ℝ b 1 a :=
      (wbtw_iff_of_le hba).mpr ⟨h.1.trans (by norm_num), h.2⟩
    have hp := hpScalar.map (AffineMap.lineMap P Q)
    have hq := hqScalar.map (AffineMap.lineMap P Q)
    rw [ha, hb] at hp hq
    simpa using And.intro hp.mem_segment hq.mem_segment
  rcases hbracket with hab | hba
  · obtain ⟨hp, hq⟩ := endpoints_mem hab
    exact (convex_segment A B).segment_subset hp hq
  · obtain ⟨hp, hq⟩ := endpoints_mem_rev hba
    rw [segment_symm] at hp hq
    exact (convex_segment A B).segment_subset hp hq

/-- If a nondegenerate segment contains two distinct points on the horizontal axis, then both
endpoints lie on that axis. -/
theorem endpoint_secondCoords_eq_zero_of_two_axis_points {a b x y : Plane}
    (_ : a ≠ b) (hxy : x ≠ y) (hx : x ∈ segment ℝ a b)
    (hy : y ∈ segment ℝ a b) (hx0 : x 1 = 0) (hy0 : y 1 = 0) :
    a 1 = 0 ∧ b 1 = 0 := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  have hst : s ≠ t := by
    intro h
    apply hxy
    rw [← hsx, ← hty, h]
  have hsCoord := congrArg (fun p : Plane => p 1) hsx
  have htCoord := congrArg (fun p : Plane => p 1) hty
  simp only [Fin.isValue, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, hx0] at hsCoord
  simp only [Fin.isValue, AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, hy0] at htCoord
  have hprod : (s - t) * (b 1 - a 1) = 0 := by
    nlinarith
  have hba : b 1 = a 1 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hst))
  have ha : a 1 = 0 := by
    rw [hba] at hsCoord
    nlinarith
  exact ⟨ha, hba.trans ha⟩

/-- A finite simplicial complex of affine simplexes in the plane: finitely many vertices at
genuine positions, faces of at most three affinely independent vertices, closed under nonempty
subsets, with any two face carriers meeting exactly in the carrier of their shared vertex set. -/
structure PlaneComplex where
  /-- The (finite) vertex type. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The position of each vertex in the plane. -/
  position : Vertex → Plane
  /-- Distinct vertices sit at distinct points. -/
  position_injective : Function.Injective position
  /-- The faces (simplexes) of the complex, as vertex sets. -/
  simplexes : Finset (Finset Vertex)
  /-- Faces are nonempty. -/
  nonempty_of_mem : ∀ s ∈ simplexes, s.Nonempty
  /-- Faces have at most three vertices: the complex is at most two-dimensional. -/
  card_le_three : ∀ s ∈ simplexes, s.card ≤ 3
  /-- Faces are closed under passing to nonempty subsets. -/
  down_closed : ∀ s ∈ simplexes, ∀ s' ⊆ s, s'.Nonempty → s' ∈ simplexes
  /-- The vertices of each face are affinely independent, so its carrier is a genuine geometric
  simplex of dimension `card - 1`. -/
  affineIndependent : ∀ s ∈ simplexes, AffineIndependent ℝ fun v : s => position v
  /-- Face carriers intersect exactly in the carrier of their shared vertices.  This is the
  face-to-face condition that makes the complex simplicial rather than an arbitrary union. -/
  face_inter : ∀ s ∈ simplexes, ∀ t ∈ simplexes,
    convexHull ℝ (position '' s) ∩ convexHull ℝ (position '' t) =
      convexHull ℝ (position '' ((s ∩ t : Finset Vertex) : Set Vertex))

/-- A finite mesh specified only by its maximal triangles.  This is the convenient construction
interface for line subdivision: all vertices, edges, and singleton faces are generated by
`TriangleMesh.toPlaneComplex`. -/
structure TriangleMesh where
  /-- The `Vertex` declaration. -/
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The `position` declaration. -/
  position : Vertex → Plane
  position_injective : Function.Injective position
  /-- The `triangles` declaration. -/
  triangles : Finset (Finset Vertex)
  card_triangle : ∀ t ∈ triangles, t.card = 3
  affineIndependent_triangle : ∀ t ∈ triangles,
    AffineIndependent ℝ fun v : t => position v
  triangle_inter : ∀ s ∈ triangles, ∀ t ∈ triangles,
    convexHull ℝ (position '' s) ∩ convexHull ℝ (position '' t) =
      convexHull ℝ (position '' ((s ∩ t : Finset Vertex) : Set Vertex))

attribute [instance] PlaneComplex.vertexFintype
attribute [instance] PlaneComplex.vertexDecidableEq
attribute [instance] TriangleMesh.vertexFintype
attribute [instance] TriangleMesh.vertexDecidableEq

namespace TriangleMesh

variable (M : TriangleMesh)

/-- The mesh consisting of one geometric triangle. -/
noncomputable def single (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) : TriangleMesh where
  Vertex := Fin 3
  position := p
  position_injective := hp.injective
  triangles := {Finset.univ}
  card_triangle := by simp
  affineIndependent_triangle := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    exact hp.comp_embedding (Function.Embedding.subtype _)
  triangle_inter := by
    intro s hs t ht
    simp only [Finset.mem_singleton] at hs ht
    subst s
    subst t
    simp

/-- Transport a triangle mesh by an affine equivalence of the plane. -/
noncomputable abbrev mapAffineEquiv (e : Plane ≃ᵃ[ℝ] Plane) : TriangleMesh where
  Vertex := M.Vertex
  position := e ∘ M.position
  position_injective := e.injective.comp M.position_injective
  triangles := M.triangles
  card_triangle := M.card_triangle
  affineIndependent_triangle := by
    intro t ht
    exact (M.affineIndependent_triangle t ht).map' e.toAffineMap e.injective
  triangle_inter := by
    intro s hs t ht
    have hinter := M.triangle_inter s hs t ht
    simp only [Function.comp_apply, ← Set.image_image]
    change convexHull ℝ (e.toAffineMap '' (M.position '' (s : Set M.Vertex))) ∩
        convexHull ℝ (e.toAffineMap '' (M.position '' (t : Set M.Vertex))) =
      convexHull ℝ (e.toAffineMap '' (M.position '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    rw [← e.toAffineMap.image_convexHull, ← e.toAffineMap.image_convexHull,
      ← e.toAffineMap.image_convexHull]
    have hinj : Function.Injective e.toAffineMap := e.injective
    rw [← Set.image_inter hinj, hinter]

/-- Reposition the vertices of a triangle mesh while retaining its abstract triangles.  The
caller supplies the geometric nondegeneracy and face-to-face proofs for the new positions. -/
noncomputable def reposition (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    TriangleMesh where
  Vertex := M.Vertex
  position := position'
  position_injective := hposition_injective
  triangles := M.triangles
  card_triangle := M.card_triangle
  affineIndependent_triangle := haffineIndependent
  triangle_inter := htriangle_inter

@[simp] theorem reposition_triangles (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    (M.reposition position' hposition_injective haffineIndependent htriangle_inter).triangles =
      M.triangles := rfl

/-- Delete one maximal triangle from a mesh.  Vertices no longer used by any triangle are retained;
this keeps the vertex type and geometric positions definitionally unchanged. -/
noncomputable def eraseTriangle (t : Finset M.Vertex) : TriangleMesh where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  triangles := M.triangles.erase t
  card_triangle := by
    intro s hs
    exact M.card_triangle s (Finset.mem_of_mem_erase hs)
  affineIndependent_triangle := by
    intro s hs
    exact M.affineIndependent_triangle s (Finset.mem_of_mem_erase hs)
  triangle_inter := by
    intro s hs u hu
    exact M.triangle_inter s (Finset.mem_of_mem_erase hs) u (Finset.mem_of_mem_erase hu)

@[simp] theorem eraseTriangle_triangles (t : Finset M.Vertex) :
    (M.eraseTriangle t).triangles = M.triangles.erase t := rfl

theorem card_eraseTriangle_triangles {t : Finset M.Vertex} (ht : t ∈ M.triangles) :
    (M.eraseTriangle t).triangles.card + 1 = M.triangles.card := by
  change (M.triangles.erase t).card + 1 = M.triangles.card
  rw [Finset.card_erase_of_mem ht]
  have : 0 < M.triangles.card := Finset.card_pos.mpr ⟨t, ht⟩
  omega

/-- Reindex a triangle mesh inside a larger finite vertex type without changing any geometric
positions.  Extra vertices of the target type may be unused. -/
noncomputable def reindex {V' : Type} [Fintype V'] [DecidableEq V']
    (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : M.Vertex ↪ V')
    (hposition : ∀ v, position' (e v) = M.position v) : TriangleMesh where
  Vertex := V'
  position := position'
  position_injective := hposition_injective
  triangles := M.triangles.image fun t => t.map e
  card_triangle := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.card_map, M.card_triangle s hs]
  affineIndependent_triangle := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    let es : s ≃ s.map e := Equiv.ofBijective
      (fun v => ⟨e v, Finset.mem_map.mpr ⟨v, v.2, rfl⟩⟩)
      ⟨fun u v huv => Subtype.ext (e.injective (congrArg Subtype.val huv)), by
        rintro ⟨v', hv'⟩
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hv'
        exact ⟨⟨v, hv⟩, rfl⟩⟩
    apply (affineIndependent_equiv es).mp
    have h := M.affineIndependent_triangle s hs
    convert h using 1
    funext v
    exact hposition v
  triangle_inter := by
    intro s hs t ht
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    have hinter := M.triangle_inter S hS T hT
    have himage (A : Finset M.Vertex) :
        position' '' ((A.map e : Finset V') : Set V') = M.position '' (A : Set M.Vertex) := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_map]
      constructor
      · rintro ⟨v', ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, (hposition v).symm⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨e v, ⟨v, hv, rfl⟩, hposition v⟩
    rw [himage, himage]
    rw [← Finset.map_inter, himage]
    exact hinter

/-- Keep a selected collection of maximal triangles.  Unused vertices remain in the ambient
finite vertex type; they do not contribute faces or support. -/
noncomputable abbrev restrictTriangles (p : Finset M.Vertex → Prop) [DecidablePred p] :
    TriangleMesh where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  triangles := M.triangles.filter p
  card_triangle := fun t ht => M.card_triangle t (Finset.mem_filter.mp ht).1
  affineIndependent_triangle := fun t ht =>
    M.affineIndependent_triangle t (Finset.mem_filter.mp ht).1
  triangle_inter := fun s hs t ht =>
    M.triangle_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

theorem mem_restrictTriangles_triangles (p : Finset M.Vertex → Prop)
    [DecidablePred p] {t : Finset M.Vertex} :
    t ∈ (M.restrictTriangles p).triangles ↔ t ∈ M.triangles ∧ p t := by
  change t ∈ M.triangles.filter p ↔ t ∈ M.triangles ∧ p t
  rw [Finset.mem_filter]

theorem mapAffineEquiv_triangles (e : Plane ≃ᵃ[ℝ] Plane) :
    (M.mapAffineEquiv e).triangles = M.triangles := rfl

/-- The nonempty subfaces of all maximal triangles in a triangle mesh. -/
def faces : Finset (Finset M.Vertex) :=
  M.triangles.biUnion fun t => t.powerset.filter (·.Nonempty)

theorem mem_faces_iff {s : Finset M.Vertex} :
    s ∈ M.faces ↔ s.Nonempty ∧ ∃ t ∈ M.triangles, s ⊆ t := by
  simp only [faces, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  aesop

/-- Every finite triangle mesh determines a finite plane complex. -/
noncomputable abbrev toPlaneComplex : PlaneComplex where
  Vertex := M.Vertex
  position := M.position
  position_injective := M.position_injective
  simplexes := M.faces
  nonempty_of_mem := fun _ hs => (M.mem_faces_iff.mp hs).1
  card_le_three := by
    intro s hs
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact (Finset.card_le_card hst).trans (M.card_triangle t ht).le
  down_closed := by
    intro s hs s' hs's hs'ne
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact M.mem_faces_iff.mpr ⟨hs'ne, t, ht, hs's.trans hst⟩
  affineIndependent := by
    intro s hs
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact (M.affineIndependent_triangle t ht).comp_embedding
      ⟨fun v : s => (⟨v.1, hst v.2⟩ : t), by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun q : t => q.1) h⟩
  face_inter := by
    intro s hs t ht
    obtain ⟨-, S, hS, hsS⟩ := M.mem_faces_iff.mp hs
    obtain ⟨-, T, hT, htT⟩ := M.mem_faces_iff.mp ht
    have hparent := M.triangle_inter S hS T hT
    have hposS : M.position '' (s : Set M.Vertex) ⊆ M.position '' (S : Set M.Vertex) :=
      Set.image_mono hsS
    have hposT : M.position '' (t : Set M.Vertex) ⊆ M.position '' (T : Set M.Vertex) :=
      Set.image_mono htT
    apply Set.Subset.antisymm
    · intro x hx
      have hxparent : x ∈ convexHull ℝ (M.position '' (S : Set M.Vertex)) ∩
          convexHull ℝ (M.position '' (T : Set M.Vertex)) :=
        ⟨convexHull_mono hposS hx.1, convexHull_mono hposT hx.2⟩
      rw [hparent] at hxparent
      have hSI : AffineIndependent ℝ
          ((↑) : (S.image M.position) → Plane) := by
        let e : S ≃ S.image M.position := Equiv.ofBijective
          (fun v => ⟨M.position v, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩)
          ⟨fun a b hab => Subtype.ext (M.position_injective (congrArg Subtype.val hab)), by
            rintro ⟨p, hp⟩
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
            exact ⟨⟨v, hv⟩, rfl⟩⟩
        have heq : ((↑) : (S.image M.position) → Plane) ∘ e =
            (fun v : S => M.position v) := by rfl
        have hmono : AffineIndependent ℝ (((↑) : (S.image M.position) → Plane) ∘ e) := by
          rw [heq]
          exact M.affineIndependent_triangle S hS
        exact (affineIndependent_equiv e).mp hmono
      have hTI : AffineIndependent ℝ
          ((↑) : (T.image M.position) → Plane) := by
        let e : T ≃ T.image M.position := Equiv.ofBijective
          (fun v => ⟨M.position v, Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩)
          ⟨fun a b hab => Subtype.ext (M.position_injective (congrArg Subtype.val hab)), by
            rintro ⟨p, hp⟩
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
            exact ⟨⟨v, hv⟩, rfl⟩⟩
        have heq : ((↑) : (T.image M.position) → Plane) ∘ e =
            (fun v : T => M.position v) := by rfl
        have hmono : AffineIndependent ℝ (((↑) : (T.image M.position) → Plane) ∘ e) := by
          rw [heq]
          exact M.affineIndependent_triangle T hT
        exact (affineIndependent_equiv e).mp hmono
      have hsImage : s.image M.position ⊆ S.image M.position :=
        Finset.image_subset_image hsS
      have hSTImage : (S ∩ T).image M.position ⊆ S.image M.position :=
        Finset.image_subset_image Finset.inter_subset_left
      have hfirst := hSI.convexHull_inter hsImage hSTImage
      rw [← Finset.coe_inter] at hfirst
      have hxfirst : x ∈ convexHull ℝ ((s ∩ (S ∩ T)).image M.position : Set Plane) := by
        rw [Finset.image_inter _ _ M.position_injective, hfirst]
        constructor
        · simpa only [Finset.coe_image] using hx.1
        · simpa only [Finset.coe_image] using hxparent
      have hsST : s ∩ (S ∩ T) = s ∩ T := by
        ext v
        simp only [Finset.mem_inter]
        aesop
      rw [hsST] at hxfirst
      have hsTImage : (s ∩ T).image M.position ⊆ T.image M.position :=
        Finset.image_subset_image Finset.inter_subset_right
      have htImage : t.image M.position ⊆ T.image M.position :=
        Finset.image_subset_image htT
      have hsecond := hTI.convexHull_inter hsTImage htImage
      rw [← Finset.coe_inter] at hsecond
      have hxsecond : x ∈ convexHull ℝ (((s ∩ T) ∩ t).image M.position : Set Plane) := by
        rw [Finset.image_inter _ _ M.position_injective, hsecond]
        exact ⟨hxfirst, by simpa only [Finset.coe_image] using hx.2⟩
      have hinter : (s ∩ T) ∩ t = s ∩ t := by
        ext v
        simp only [Finset.mem_inter]
        aesop
      rw [hinter] at hxsecond
      simpa only [Finset.coe_image] using hxsecond
    · intro x hx
      exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
        convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- The carrier of a face: the convex hull of its vertex positions. -/
def cellCarrier (s : Finset K.Vertex) : Set Plane :=
  convexHull ℝ (K.position '' s)

/-- The support of the complex: the union of its face carriers. -/
def support : Set Plane :=
  ⋃ s ∈ K.simplexes, K.cellCarrier s

theorem cellCarrier_subset_support {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    K.cellCarrier s ⊆ K.support :=
  Set.subset_biUnion_of_mem hs

theorem isCompact_cellCarrier (s : Finset K.Vertex) : IsCompact (K.cellCarrier s) :=
  Set.Finite.isCompact_convexHull (𝕜 := ℝ) (s.finite_toSet.image K.position)

/-- The support of a finite plane complex is compact. -/
theorem isCompact_support : IsCompact K.support :=
  K.simplexes.finite_toSet.isCompact_biUnion fun s _ => K.isCompact_cellCarrier s

/-- Transport a finite plane complex through an affine equivalence. -/
noncomputable def mapAffineEquiv (e : Plane ≃ᵃ[ℝ] Plane) : PlaneComplex where
  Vertex := K.Vertex
  position := e ∘ K.position
  position_injective := e.injective.comp K.position_injective
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    exact (K.affineIndependent s hs).map' e.toAffineMap e.injective
  face_inter := by
    intro s hs t ht
    have hinter := K.face_inter s hs t ht
    simp only [Function.comp_apply, ← Set.image_image]
    change convexHull ℝ (e.toAffineMap '' (K.position '' (s : Set K.Vertex))) ∩
        convexHull ℝ (e.toAffineMap '' (K.position '' (t : Set K.Vertex))) =
      convexHull ℝ
        (e.toAffineMap '' (K.position '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    rw [← e.toAffineMap.image_convexHull, ← e.toAffineMap.image_convexHull,
      ← e.toAffineMap.image_convexHull]
    rw [← Set.image_inter (f := e.toAffineMap) e.injective, hinter]

@[simp] theorem mapAffineEquiv_simplexes (e : Plane ≃ᵃ[ℝ] Plane) :
    (K.mapAffineEquiv e).simplexes = K.simplexes := rfl

theorem mapAffineEquiv_cellCarrier (e : Plane ≃ᵃ[ℝ] Plane)
    (s : Finset K.Vertex) :
    (K.mapAffineEquiv e).cellCarrier s = e '' K.cellCarrier s := by
  change convexHull ℝ ((e ∘ K.position) '' (s : Set K.Vertex)) =
    e '' convexHull ℝ (K.position '' (s : Set K.Vertex))
  rw [Set.image_comp]
  exact (e.toAffineMap.image_convexHull _).symm

theorem mapAffineEquiv_support (e : Plane ≃ᵃ[ℝ] Plane) :
    (K.mapAffineEquiv e).support = e '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  rw [mapAffineEquiv_simplexes]
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨s, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hs, hx⟩ := hx
    rw [show (K.mapAffineEquiv e).cellCarrier s = e '' K.cellCarrier s from
      K.mapAffineEquiv_cellCarrier e s] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    rw [Set.mem_iUnion]
    exact ⟨s, Set.mem_iUnion_of_mem hs hy⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Set.mem_iUnion] at hy
    obtain ⟨s, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨hs, hy⟩ := hy
    rw [Set.mem_iUnion]
    refine ⟨s, Set.mem_iUnion_of_mem hs ?_⟩
    rw [show (K.mapAffineEquiv e).cellCarrier s = e '' K.cellCarrier s from
      K.mapAffineEquiv_cellCarrier e s]
    exact ⟨_, hy, rfl⟩

/-- The two-dimensional faces. -/
def cells : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 3

/-- The edges (one-dimensional faces). -/
def edges : Finset (Finset K.Vertex) :=
  K.simplexes.filter fun s => s.card = 2

/-- The subcomplex consisting of the vertices and edges of `K`. -/
noncomputable abbrev oneSkeleton : PlaneComplex where
  Vertex := K.Vertex
  position := K.position
  position_injective := K.position_injective
  simplexes := K.simplexes.filter fun s => s.card ≤ 2
  nonempty_of_mem := by
    intro s hs
    exact K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
  card_le_three := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2.trans (by omega)
  down_closed := by
    intro s hs t hts ht
    apply Finset.mem_filter.mpr
    exact ⟨K.down_closed s (Finset.mem_filter.mp hs).1 t hts ht,
      (Finset.card_le_card hts).trans (Finset.mem_filter.mp hs).2⟩
  affineIndependent := by
    intro s hs
    exact K.affineIndependent s (Finset.mem_filter.mp hs).1
  face_inter := by
    intro s hs t ht
    exact K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1

theorem mem_oneSkeleton_simplexes {s : Finset K.Vertex} :
    s ∈ K.oneSkeleton.simplexes ↔ s ∈ K.simplexes ∧ s.card ≤ 2 := by
  classical
  exact Finset.mem_filter

@[simp] theorem oneSkeleton_position : K.oneSkeleton.position = K.position := rfl

@[simp] theorem oneSkeleton_cellCarrier (s : Finset K.Vertex) :
    K.oneSkeleton.cellCarrier s = K.cellCarrier s := rfl

theorem oneSkeleton_support_subset : K.oneSkeleton.support ⊆ K.support := by
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨hsK, -⟩ := K.mem_oneSkeleton_simplexes.mp hs
  exact ⟨s, hsK, hxs⟩

theorem oneSkeleton_support_eq (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2) :
    K.oneSkeleton.support = K.support := by
  apply Set.Subset.antisymm K.oneSkeleton_support_subset
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  exact ⟨s, K.mem_oneSkeleton_simplexes.mpr ⟨hs, hgraph s hs⟩, hxs⟩

theorem oneSkeleton_isGraph :
    ∀ s ∈ K.oneSkeleton.simplexes, s.card ≤ 2 := by
  intro s hs
  exact (K.mem_oneSkeleton_simplexes.mp hs).2

/-- Keep the faces of `L` which lie in a face of `K`.  This is the standard way to turn an
ambient line arrangement into a subdivision subordinate to a pre-existing complex. -/
noncomputable def subordinateTo (L K : PlaneComplex) : PlaneComplex := by
  classical
  exact {
    Vertex := L.Vertex
    position := L.position
    position_injective := L.position_injective
    simplexes := L.simplexes.filter fun s =>
      ∃ t ∈ K.simplexes, L.cellCarrier s ⊆ K.cellCarrier t
    nonempty_of_mem := by
      intro s hs
      exact L.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := by
      intro s hs
      exact L.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs u hus hu
      obtain ⟨hsL, t, htK, hst⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨L.down_closed s hsL u hus hu, t, htK, ?_⟩
      exact (convexHull_mono (Set.image_mono hus)).trans hst
    affineIndependent := by
      intro s hs
      exact L.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := by
      intro s hs t ht
      exact L.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

theorem mem_subordinateTo_simplexes_iff (L K : PlaneComplex) {s : Finset L.Vertex} :
    s ∈ (L.subordinateTo K).simplexes ↔
      s ∈ L.simplexes ∧ ∃ t ∈ K.simplexes, L.cellCarrier s ⊆ K.cellCarrier t := by
  classical
  exact Finset.mem_filter

@[simp] theorem subordinateTo_position (L K : PlaneComplex) :
    (L.subordinateTo K).position = L.position := rfl

@[simp] theorem subordinateTo_cellCarrier (L K : PlaneComplex) (s : Finset L.Vertex) :
    (L.subordinateTo K).cellCarrier s = L.cellCarrier s := rfl

theorem subordinateTo_support_subset (L K : PlaneComplex) :
    (L.subordinateTo K).support ⊆ K.support := by
  intro x hx
  rw [PlaneComplex.support] at hx ⊢
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨-, t, ht, hst⟩ := (L.mem_subordinateTo_simplexes_iff K).mp hs
  exact ⟨t, ht, hst hxs⟩

/-- Keep precisely the faces whose carriers lie in a prescribed geometric set. -/
noncomputable def restrictToSet (K : PlaneComplex) (A : Set Plane) : PlaneComplex := by
  classical
  exact {
    Vertex := K.Vertex
    position := K.position
    position_injective := K.position_injective
    simplexes := K.simplexes.filter fun s => K.cellCarrier s ⊆ A
    nonempty_of_mem := fun s hs => K.nonempty_of_mem s (Finset.mem_filter.mp hs).1
    card_le_three := fun s hs => K.card_le_three s (Finset.mem_filter.mp hs).1
    down_closed := by
      intro s hs t hts ht
      obtain ⟨hsK, hsA⟩ := Finset.mem_filter.mp hs
      apply Finset.mem_filter.mpr
      exact ⟨K.down_closed s hsK t hts ht,
        (convexHull_mono (Set.image_mono hts)).trans hsA⟩
    affineIndependent := fun s hs => K.affineIndependent s (Finset.mem_filter.mp hs).1
    face_inter := fun s hs t ht =>
      K.face_inter s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 }

@[simp] theorem mem_restrictToSet_simplexes_iff (K : PlaneComplex) (A : Set Plane)
    {s : Finset K.Vertex} :
    s ∈ (K.restrictToSet A).simplexes ↔ s ∈ K.simplexes ∧ K.cellCarrier s ⊆ A := by
  classical
  exact Finset.mem_filter

@[simp] theorem restrictToSet_cellCarrier (K : PlaneComplex) (A : Set Plane)
    (s : Finset K.Vertex) :
    (K.restrictToSet A).cellCarrier s = K.cellCarrier s := rfl

theorem restrictToSet_support_subset (K : PlaneComplex) (A : Set Plane) :
    (K.restrictToSet A).support ⊆ A := by
  intro x hx
  rw [PlaneComplex.support] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  exact (K.mem_restrictToSet_simplexes_iff A).mp hs |>.2 hxs

/-- A complex is purely two-dimensional when every face lies in a two-dimensional one. -/
def IsPure2 : Prop :=
  ∀ s ∈ K.simplexes, ∃ t ∈ K.simplexes, s ⊆ t ∧ t.card = 3

end PlaneComplex

namespace TriangleMesh

variable (M : TriangleMesh)

theorem toPlaneComplex_support :
    M.toPlaneComplex.support = ⋃ t ∈ M.triangles,
      convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
  ext x
  rw [PlaneComplex.support]
  simp only [toPlaneComplex, PlaneComplex.cellCarrier, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
    exact ⟨t, ht, convexHull_mono (Set.image_mono hst) hxs⟩
  · rintro ⟨t, ht, hxt⟩
    refine ⟨t, ?_, hxt⟩
    exact M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
      t, ht, subset_rfl⟩

theorem eraseTriangle_support_subset (t : Finset M.Vertex) :
    (M.eraseTriangle t).toPlaneComplex.support ⊆ M.toPlaneComplex.support := by
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support]
  intro p hp
  simp only [eraseTriangle_triangles, Set.mem_iUnion] at hp ⊢
  obtain ⟨s, hs, hps⟩ := hp
  obtain ⟨_, hsM⟩ := Finset.mem_erase.mp hs
  exact ⟨s, hsM, hps⟩

/-- The support of a mesh is the union of one maximal triangle and the support left after
deleting it. -/
theorem support_eq_eraseTriangle_union_triangleCarrier {t : Finset M.Vertex}
    (ht : t ∈ M.triangles) :
    M.toPlaneComplex.support =
      (M.eraseTriangle t).toPlaneComplex.support ∪
        convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support]
  ext p
  simp only [eraseTriangle_triangles, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨s, hs, hps⟩
    by_cases hst : s = t
    · exact Or.inr (hst ▸ hps)
    · exact Or.inl ⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hps⟩
  · rintro (⟨s, hs, hps⟩ | hpt)
    · exact ⟨s, (Finset.mem_erase.mp hs).2, hps⟩
    · exact ⟨t, ht, hpt⟩

theorem single_support (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) :
    (single p hp).toPlaneComplex.support = convexHull ℝ (Set.range p) := by
  rw [toPlaneComplex_support]
  ext x
  simp only [Set.mem_iUnion]
  unfold single
  constructor
  · rintro ⟨t, ht, hxt⟩
    change t ∈ ({Finset.univ} : Finset (Finset (Fin 3))) at ht
    have ht' : t = Finset.univ := Finset.mem_singleton.mp ht
    subst t
    change x ∈ convexHull ℝ
      (p '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3))) at hxt
    simpa using hxt
  · intro hx
    refine ⟨Finset.univ, ?_, ?_⟩
    · change (Finset.univ : Finset (Fin 3)) ∈
        ({Finset.univ} : Finset (Finset (Fin 3)))
      exact Finset.mem_singleton_self _
    · change x ∈ convexHull ℝ
        (p '' (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)))
      simpa using hx

theorem toPlaneComplex_isPure2 : M.toPlaneComplex.IsPure2 := by
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hs
  exact ⟨t, M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t ht]; omega),
      t, ht, subset_rfl⟩, hst, M.card_triangle t ht⟩

/-- The two-dimensional cells generated by a triangle mesh are exactly its listed maximal
triangles. -/
theorem toPlaneComplex_cells : M.toPlaneComplex.cells = M.triangles := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsFace, hsCard⟩
    obtain ⟨-, t, ht, hst⟩ := M.mem_faces_iff.mp hsFace
    have hstEq : s = t := by
      apply Finset.eq_of_subset_of_card_le hst
      change t.card ≤ s.card
      rw [M.card_triangle t ht, hsCard]
    rwa [hstEq]
  · intro hs
    apply Finset.mem_filter.mpr
    exact ⟨M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by
      rw [M.card_triangle s hs]
      omega), s, hs, subset_rfl⟩, M.card_triangle s hs⟩

/-- Affine transport carries the support of a triangle mesh to the affine image of its original
support. -/
theorem mapAffineEquiv_support (e : Plane ≃ᵃ[ℝ] Plane) :
    (M.mapAffineEquiv e).toPlaneComplex.support = e '' M.toPlaneComplex.support := by
  rw [toPlaneComplex_support, toPlaneComplex_support]
  change (⋃ t ∈ M.triangles,
      convexHull ℝ ((fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex))) =
    e '' (⋃ t ∈ M.triangles, convexHull ℝ (M.position '' (t : Set M.Vertex)))
  have hcarrier (t : Finset M.Vertex) :
      convexHull ℝ ((fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex)) =
        e '' convexHull ℝ (M.position '' (t : Set M.Vertex)) := by
    have himage : (fun a : M.Vertex => e (M.position a)) '' (t : Set M.Vertex) =
        e '' (M.position '' (t : Set M.Vertex)) := by
      exact (Set.image_image e M.position (t : Set M.Vertex)).symm
    rw [himage]
    change convexHull ℝ (e.toAffineMap '' (M.position '' (t : Set M.Vertex))) =
      e.toAffineMap '' convexHull ℝ (M.position '' (t : Set M.Vertex))
    exact (e.toAffineMap.image_convexHull _).symm
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨t, ht, hxt⟩
    rw [hcarrier] at hxt
    obtain ⟨y, hyt, rfl⟩ := hxt
    exact ⟨y, ⟨t, ht, hyt⟩, rfl⟩
  · rintro ⟨y, ⟨t, ht, hyt⟩, rfl⟩
    exact ⟨t, ht, by rw [hcarrier]; exact ⟨y, hyt, rfl⟩⟩

/-- Reindexing without changing positions preserves support. -/
theorem reindex_support {V' : Type} [Fintype V'] [DecidableEq V']
    (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : M.Vertex ↪ V') (hposition : ∀ v, position' (e v) = M.position v) :
    (M.reindex position' hposition_injective e hposition).toPlaneComplex.support =
      M.toPlaneComplex.support := by
  rw [toPlaneComplex_support, toPlaneComplex_support]
  change (⋃ t ∈ M.triangles.image fun s => s.map e,
      convexHull ℝ (position' '' (t : Set V'))) =
    ⋃ s ∈ M.triangles, convexHull ℝ (M.position '' (s : Set M.Vertex))
  have himage (s : Finset M.Vertex) :
      position' '' ((s.map e : Finset V') : Set V') = M.position '' (s : Set M.Vertex) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_map]
    constructor
    · rintro ⟨v', ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (hposition v).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨e v, ⟨v, hv, rfl⟩, hposition v⟩
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨s, hs, by rw [← himage]; exact hxt⟩
  · rintro ⟨s, hs, hxs⟩
    exact ⟨s.map e, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      by rw [himage]; exact hxs⟩

end TriangleMesh

namespace PlaneComplex

variable (K : PlaneComplex)

/-- `K'` subdivides `K`: same support, and every face carrier of `K'` lies inside some face
carrier of `K`. -/
def Subdivides (K' K : PlaneComplex) : Prop :=
  K'.support = K.support ∧
    ∀ s' ∈ K'.simplexes, ∃ s ∈ K.simplexes, K'.cellCarrier s' ⊆ K.cellCarrier s

theorem Subdivides.refl (K : PlaneComplex) : K.Subdivides K :=
  ⟨rfl, fun s hs => ⟨s, hs, subset_rfl⟩⟩

theorem Subdivides.trans {K₂ K₁ K₀ : PlaneComplex}
    (h₂₁ : K₂.Subdivides K₁) (h₁₀ : K₁.Subdivides K₀) :
    K₂.Subdivides K₀ := by
  constructor
  · exact h₂₁.1.trans h₁₀.1
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h₂₁.2 s hs
    obtain ⟨u, hu, htu⟩ := h₁₀.2 t ht
    exact ⟨u, hu, hst.trans htu⟩

theorem Subdivides.mapAffineEquiv {K' K : PlaneComplex} (h : K'.Subdivides K)
    (e : Plane ≃ᵃ[ℝ] Plane) :
    (K'.mapAffineEquiv e).Subdivides (K.mapAffineEquiv e) := by
  constructor
  · rw [K'.mapAffineEquiv_support, K.mapAffineEquiv_support, h.1]
  · intro s hs
    change s ∈ K'.simplexes at hs
    obtain ⟨t, ht, hst⟩ := h.2 s hs
    refine ⟨t, ht, ?_⟩
    rw [show (K'.mapAffineEquiv e).cellCarrier s = e '' K'.cellCarrier s from
      K'.mapAffineEquiv_cellCarrier e s]
    rw [show (K.mapAffineEquiv e).cellCarrier t = e '' K.cellCarrier t from
      K.mapAffineEquiv_cellCarrier e t]
    exact Set.image_mono hst

theorem subordinateTo_subdivides (L K : PlaneComplex)
    (hsupport : (L.subordinateTo K).support = K.support) :
    (L.subordinateTo K).Subdivides K := by
  refine ⟨hsupport, ?_⟩
  intro s hs
  obtain ⟨-, t, ht, hst⟩ := (L.mem_subordinateTo_simplexes_iff K).mp hs
  exact ⟨t, ht, hst⟩

end PlaneComplex

/-- `f` agrees with an affine map on `A`. -/
def IsAffineOn (f : Plane → Plane) (A : Set Plane) : Prop :=
  ∃ g : Plane →ᵃ[ℝ] Plane, Set.EqOn f g A

/-- `f` is piecewise linear on the complex `K`: affine on every face of some subdivision.

This is the honest PL predicate: a map that is not affine on any neighborhood of a point interior
to a 2-cell of `K` cannot satisfy it, in contrast to the vacuous `IsPLOnSimplexes` of the
retiring `PL.lean` layer. -/
def IsPLOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  ∃ K' : PlaneComplex, K'.Subdivides K ∧
    ∀ s' ∈ K'.simplexes, IsAffineOn f (K'.cellCarrier s')

/-- `f` is a PL embedding of the support of `K`: piecewise linear and injective on the support. -/
def IsPLEmbeddingOn (K : PlaneComplex) (f : Plane → Plane) : Prop :=
  IsPLOn K f ∧ Set.InjOn f K.support

/-- A function is PL on a geometric set when the set is the support of a finite plane complex
on which the function is PL. -/
def IsPLOnSet (A : Set Plane) (f : Plane → Plane) : Prop :=
  ∃ K : PlaneComplex, K.support = A ∧ IsPLOn K f

namespace IsAffineOn

/-- Restrict an affine-on-set witness to a smaller set. -/
theorem mono {f : Plane → Plane} {A B : Set Plane} (hf : IsAffineOn f A) (hBA : B ⊆ A) :
    IsAffineOn f B := by
  obtain ⟨g, hfg⟩ := hf
  exact ⟨g, hfg.mono hBA⟩

/-- Composition of affine-on-set maps is affine when the first map carries the source set into
the set on which the second map is affine. -/
theorem comp {f g : Plane → Plane} {A B : Set Plane}
    (hg : IsAffineOn g B) (hf : IsAffineOn f A) (hmap : Set.MapsTo f A B) :
    IsAffineOn (g ∘ f) A := by
  obtain ⟨F, hfF⟩ := hf
  obtain ⟨G, hgG⟩ := hg
  refine ⟨G.comp F, fun x hx => ?_⟩
  change g (f x) = G (F x)
  rw [hfF hx, hgG (by rw [← hfF hx]; exact hmap hx)]

/-- A function agreeing with an affine map on a set is continuous there. -/
theorem continuousOn {f : Plane → Plane} {A : Set Plane} (hf : IsAffineOn f A) :
    ContinuousOn f A := by
  obtain ⟨g, hfg⟩ := hf
  exact g.continuous_of_finiteDimensional.continuousOn.congr fun x hx => hfg hx

/-- An affine-on-set map sends every segment contained in the set to the segment between the
endpoint images. -/
theorem image_segment {f : Plane → Plane} {A : Set Plane} (hf : IsAffineOn f A)
    {x y : Plane} (hsegment : segment ℝ x y ⊆ A) :
    f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  obtain ⟨g, hfg⟩ := hf
  calc
    f '' segment ℝ x y = g '' segment ℝ x y :=
      Set.image_congr fun z hz => hfg (hsegment hz)
    _ = segment ℝ (g x) (g y) := _root_.image_segment ℝ g x y
    _ = segment ℝ (f x) (f y) := by
      rw [hfg (hsegment (left_mem_segment ℝ x y)),
        hfg (hsegment (right_mem_segment ℝ x y))]

/-- An affine-on-hull map carries a finite convex hull to the convex hull of the images. -/
theorem image_convexHull {f : Plane → Plane} {A : Set Plane}
    (hf : IsAffineOn f (convexHull ℝ A)) :
    convexHull ℝ (f '' A) = f '' convexHull ℝ A := by
  obtain ⟨g, hfg⟩ := hf
  have himageA : f '' A = g '' A := Set.image_congr fun x hx =>
    hfg (subset_convexHull ℝ A hx)
  rw [himageA, ← g.image_convexHull]
  exact Set.image_congr fun x hx => (hfg hx).symm

end IsAffineOn

namespace IsPLOn

/-- A map affine on the support is PL without further subdivision. -/
theorem of_affineOn_support {K : PlaneComplex} {f : Plane → Plane}
    (hf : IsAffineOn f K.support) : IsPLOn K f := by
  refine ⟨K, PlaneComplex.Subdivides.refl K, ?_⟩
  intro s hs
  obtain ⟨g, hfg⟩ := hf
  exact ⟨g, hfg.mono (K.cellCarrier_subset_support hs)⟩

/-- A PL witness on a subdivision is also a PL witness on the original complex. -/
theorem of_subdivision {K' K : PlaneComplex} {f : Plane → Plane}
    (hsubdivision : K'.Subdivides K) (hf : IsPLOn K' f) : IsPLOn K f := by
  obtain ⟨L, hL, haffine⟩ := hf
  exact ⟨L, hL.trans hsubdivision, haffine⟩

/-- A PL map is continuous on the support of its complex. -/
theorem continuousOn {K : PlaneComplex} {f : Plane → Plane} (hf : IsPLOn K f) :
    ContinuousOn f K.support := by
  obtain ⟨K', hsubdivision, haffine⟩ := hf
  rw [← hsubdivision.1]
  let carriers : K'.simplexes → Set Plane := fun s => K'.cellCarrier s.1
  have hlocal : LocallyFinite carriers := locallyFinite_of_finite carriers
  have hclosed : ∀ s, IsClosed (carriers s) := fun s =>
    (K'.isCompact_cellCarrier s.1).isClosed
  have hcontinuous : ∀ s, ContinuousOn f (carriers s) := fun s =>
    (haffine s.1 s.2).continuousOn
  have hglued := hlocal.continuousOn_iUnion hclosed hcontinuous
  simpa only [PlaneComplex.support, carriers, Set.iUnion_subtype] using hglued

/-- PL maps remain PL after affine changes of coordinates in source and target. -/
theorem affineConjugate {K : PlaneComplex} {f : Plane → Plane} (hf : IsPLOn K f)
    (source target : Plane ≃ᵃ[ℝ] Plane) :
    IsPLOn (K.mapAffineEquiv source) (fun x => target (f (source.symm x))) := by
  obtain ⟨K', hsubdivision, haffine⟩ := hf
  refine ⟨K'.mapAffineEquiv source, hsubdivision.mapAffineEquiv source, ?_⟩
  intro s hs
  change s ∈ K'.simplexes at hs
  obtain ⟨g, hfg⟩ := haffine s hs
  refine ⟨target.toAffineMap.comp (g.comp source.symm.toAffineMap), ?_⟩
  intro x hx
  rw [show (K'.mapAffineEquiv source).cellCarrier s = source '' K'.cellCarrier s from
    K'.mapAffineEquiv_cellCarrier source s] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change target (f (source.symm (source y))) =
    target (g (source.symm (source y)))
  rw [source.symm_apply_apply]
  exact congrArg target (hfg hy)

end IsPLOn

namespace PlaneComplex

variable (K : PlaneComplex)

theorem mem_simplexes_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) :
    t ∈ K.simplexes :=
  (Finset.mem_filter.mp ht).1

theorem card_of_mem_cells {t : Finset K.Vertex} (ht : t ∈ K.cells) : t.card = 3 :=
  (Finset.mem_filter.mp ht).2

/-- Barycentric evaluation: the point of the plane with the given barycentric weights. -/
noncomputable def baryEval (x : K.Vertex → ℝ) : Plane :=
  ∑ v, x v • K.position v

theorem continuous_baryEval :
    Continuous fun x : K.Vertex → ℝ => K.baryEval x := by
  unfold baryEval
  exact continuous_finsetSum _ fun v _ => (continuous_apply v).smul continuous_const

theorem baryEval_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    K.baryEval x = ∑ v ∈ t, x v • K.position v :=
  (Finset.sum_subset (Finset.subset_univ t)
    (fun v _ hv => by rw [hsupp v hv, zero_smul])).symm

theorem sum_eq_sum_of_support {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) :
    ∑ v, x v = ∑ v ∈ t, x v :=
  (Finset.sum_subset (Finset.subset_univ t) (fun v _ hv => hsupp v hv)).symm

/-- Barycentric evaluation of weights supported on a face lands in that face's carrier. -/
theorem baryEval_mem_cellCarrier {x : K.Vertex → ℝ} {t : Finset K.Vertex}
    (hsupp : ∀ v ∉ t, x v = 0) (h0 : ∀ v, 0 ≤ x v) (h1 : ∑ v, x v = 1) :
    K.baryEval x ∈ K.cellCarrier t := by
  have hsum_t : ∑ v ∈ t, x v = 1 := by
    rw [← K.sum_eq_sum_of_support hsupp]
    exact h1
  rw [K.baryEval_eq_sum_of_support hsupp, cellCarrier,
    ← Finset.centerMass_eq_of_sum_1 _ _ hsum_t]
  exact Finset.centerMass_mem_convexHull t (fun v _ => h0 v) (by rw [hsum_t]; norm_num)
    (fun v hv => Set.mem_image_of_mem _ hv)

/-- Every point of a face carrier has barycentric weights supported on that face. -/
theorem exists_weights_of_mem_cellCarrier {p : Plane} {t : Finset K.Vertex}
    (hp : p ∈ K.cellCarrier t) :
    ∃ x : K.Vertex → ℝ, (∀ v ∉ t, x v = 0) ∧ (∀ v, 0 ≤ x v) ∧ (∑ v, x v = 1) ∧
      K.baryEval x = p := by
  classical
  rw [cellCarrier, ← Finset.coe_image, Finset.convexHull_eq] at hp
  obtain ⟨w, hw0, hw1, hwp⟩ := hp
  have himg : ∀ g : Plane → ℝ, ∑ q ∈ t.image K.position, g q = ∑ v ∈ t, g (K.position v) :=
    fun g => Finset.sum_image fun v _ v' _ h => K.position_injective h
  refine ⟨fun v => if v ∈ t then w (K.position v) else 0, fun v hv => by simp [hv], ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ t
    · simpa [hv] using hw0 _ (Finset.mem_image_of_mem _ hv)
    · simp [hv]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, ← himg]
    exact hw1
  · have hsupp : ∀ v ∉ t, (fun v => if v ∈ t then w (K.position v) else 0) v = 0 :=
      fun v hv => by simp [hv]
    rw [K.baryEval_eq_sum_of_support hsupp]
    have hite : ∑ v ∈ t, (if v ∈ t then w (K.position v) else 0) • K.position v =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_congr rfl fun v hv => by rw [ite_eq_left hv]
    have himg2 : ∑ q ∈ t.image K.position, w q • q =
        ∑ v ∈ t, w (K.position v) • K.position v :=
      Finset.sum_image fun v _ v' _ h => K.position_injective h
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hwp
    simp only [id_eq] at hwp
    rw [hite, ← himg2]
    exact hwp

/-- Barycentric weights on an affinely independent face are unique. -/
theorem baryEval_injOn_face {t : Finset K.Vertex} (ht : t ∈ K.simplexes)
    {x y : K.Vertex → ℝ}
    (hx : ∀ v ∉ t, x v = 0) (hy : ∀ v ∉ t, y v = 0)
    (hx1 : ∑ v, x v = 1) (hy1 : ∑ v, y v = 1)
    (heq : K.baryEval x = K.baryEval y) : x = y := by
  classical
  have hAI := K.affineIndependent t ht
  have hx1' : ∑ v : ↥t, x v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => x v), ← K.sum_eq_sum_of_support hx]
    exact hx1
  have hy1' : ∑ v : ↥t, y v.1 = 1 := by
    rw [Finset.sum_coe_sort t (fun v => y v), ← K.sum_eq_sum_of_support hy]
    exact hy1
  have hxcomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => x v.1) = K.baryEval x := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hx1',
      K.baryEval_eq_sum_of_support hx, ← Finset.sum_coe_sort t (fun v => x v • K.position v)]
  have hycomb : Finset.univ.affineCombination ℝ (fun v : ↥t => K.position v)
      (fun v : ↥t => y v.1) = K.baryEval y := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hy1',
      K.baryEval_eq_sum_of_support hy, ← Finset.sum_coe_sort t (fun v => y v • K.position v)]
  have hind := hAI.indicator_eq_of_affineCombination_eq Finset.univ Finset.univ _ _ hx1' hy1'
    (by rw [hxcomb, hycomb, heq])
  funext v
  by_cases hv : v ∈ t
  · have := congrFun hind ⟨v, hv⟩
    simpa using this
  · rw [hx v hv, hy v hv]

end PlaneComplex

/-- The canonical barycentric homeomorphism from the abstract realization of a pure plane
complex to its geometric support. -/
noncomputable def PlaneComplex.realizationHomeomorph (K : PlaneComplex) (hpure : K.IsPure2) :
    GeometricRealization K.Vertex K.cells ≃ₜ K.support := by
  classical
  have hmem : ∀ x : GeometricRealization K.Vertex K.cells, K.baryEval x.1 ∈ K.support := by
    rintro ⟨x, ⟨h0, h1⟩, t, ht, hsupp⟩
    exact Set.mem_biUnion (K.mem_simplexes_of_mem_cells ht)
      (K.baryEval_mem_cellCarrier hsupp h0 h1)
  let φ : GeometricRealization K.Vertex K.cells → K.support :=
    fun x => ⟨K.baryEval x.1, hmem x⟩
  have hcont : Continuous φ :=
    Continuous.subtype_mk (K.continuous_baryEval.comp continuous_subtype_val) _
  have hinj : Function.Injective φ := by
    rintro ⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩ ⟨y, ⟨hy0, hy1⟩, u, hu, hysupp⟩ heqφ
    have heval : K.baryEval x = K.baryEval y := congrArg Subtype.val heqφ
    have hpx := K.baryEval_mem_cellCarrier hxsupp hx0 hx1
    have hpy := K.baryEval_mem_cellCarrier hysupp hy0 hy1
    have hpint : K.baryEval x ∈ K.cellCarrier (t ∩ u) := by
      have hfi := K.face_inter t (K.mem_simplexes_of_mem_cells ht) u
        (K.mem_simplexes_of_mem_cells hu)
      have : K.baryEval x ∈
          convexHull ℝ (K.position '' t) ∩ convexHull ℝ (K.position '' u) :=
        ⟨hpx, by rw [heval]; exact hpy⟩
      rw [hfi] at this
      exact this
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hpint
    have hzt : ∀ v ∉ t, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_left hmem)
    have hzu : ∀ v ∉ u, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_right hmem)
    have hxz : x = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells ht)
      hxsupp hzt hx1 hz1 (by rw [hzeval])
    have hyz : y = z := K.baryEval_injOn_face (K.mem_simplexes_of_mem_cells hu)
      hysupp hzu hy1 hz1 (by rw [hzeval, ← heval])
    exact Subtype.ext (hxz.trans hyz.symm)
  have hsurj : Function.Surjective φ := by
    rintro ⟨p, hp⟩
    rw [PlaneComplex.support, Set.mem_iUnion₂] at hp
    obtain ⟨σ, hσ, hpσ⟩ := hp
    obtain ⟨t, ht, hσt, htcard⟩ := hpure σ hσ
    have hpt : p ∈ K.cellCarrier t := by
      rw [PlaneComplex.cellCarrier] at hpσ ⊢
      exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr hσt)) hpσ
    have htcells : t ∈ K.cells := Finset.mem_filter.mpr ⟨ht, htcard⟩
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hpt
    exact ⟨⟨x, ⟨hx0, hx1⟩, t, htcells, hxsupp⟩, Subtype.ext hxeval⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective φ ⟨hinj, hsurj⟩) hcont

@[simp] theorem PlaneComplex.realizationHomeomorph_apply (K : PlaneComplex)
    (hpure : K.IsPure2) (x : GeometricRealization K.Vertex K.cells) :
    ((K.realizationHomeomorph hpure) x).1 = K.baryEval x.1 := rfl

/-- **Realization bridge** (elementary): a purely two-dimensional plane complex induces a
geometric triangulation of its support, by barycentric coordinates in the face containing each
point.  Injectivity is the uniqueness of barycentric coordinates on each affinely independent
face, glued across faces by the face-to-face intersection condition. -/
theorem PlaneComplex.toGeometricTriangulation (K : PlaneComplex) (hpure : K.IsPure2) :
    Nonempty (GeometricTriangulation K.support) := by
  exact ⟨{ Vertex := K.Vertex
           faces := K.cells
           faces_card := fun t ht => K.card_of_mem_cells ht
           homeo := K.realizationHomeomorph hpure }⟩

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
