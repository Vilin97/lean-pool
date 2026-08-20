/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.PlaneComplex
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Order.Fin.Finset

/-!
# Subdividing finite plane complexes by affine lines

Moise Chapter 2 cuts a polygonal region by the finitely many lines containing its edges.  This
file develops that construction from its local primitive: when an affine functional has opposite
signs at the endpoints of an edge, its zero gives the new subdivision vertex on that edge.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Three affinely independent points form an affine basis of the plane. -/
noncomputable def affineBasisOfTriangle (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p) :
    AffineBasis (Fin 3) ℝ Plane where
  toFun := p
  ind' := hp
  tot' := (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by
    simp [Plane])

/-- The affine equivalence carrying one ordered nondegenerate plane triangle to another. -/
noncomputable def triangleAffineEquiv (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) : Plane ≃ᵃ[ℝ] Plane :=
  let bp := affineBasisOfTriangle p hp
  let bq := affineBasisOfTriangle q hq
  AffineEquiv.ofLinearEquiv
    ((bp.basisOf 0).equiv (bq.basisOf 0) (Equiv.refl _)) (p 0) (q 0)

@[simp] theorem triangleAffineEquiv_apply (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) (i : Fin 3) :
    triangleAffineEquiv p q hp hq (p i) = q i := by
  fin_cases i
  · simp [triangleAffineEquiv]
  · change ((affineBasisOfTriangle p hp).basisOf 0).equiv
        ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
          (p 1 - p 0) + q 0 = q 1
    let j : {j : Fin 3 // j ≠ 0} := ⟨1, by decide⟩
    have hpvec : p 1 - p 0 =
        (affineBasisOfTriangle p hp).basisOf 0 j := by
      have h := (affineBasisOfTriangle p hp).basisOf_apply 0 j
      change (affineBasisOfTriangle p hp).basisOf 0 j = p 1 - p 0 at h
      exact h.symm
    have hqvec : (affineBasisOfTriangle q hq).basisOf 0 j =
        q 1 - q 0 := by
      have h := (affineBasisOfTriangle q hq).basisOf_apply 0 j
      change (affineBasisOfTriangle q hq).basisOf 0 j = q 1 - q 0 at h
      exact h
    have hequiv := ((affineBasisOfTriangle p hp).basisOf 0).equiv_apply
      j ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
    rw [hpvec]
    rw [hequiv]
    simp only [Equiv.refl_apply]
    rw [hqvec]
    abel
  · change ((affineBasisOfTriangle p hp).basisOf 0).equiv
        ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
          (p 2 - p 0) + q 0 = q 2
    let j : {j : Fin 3 // j ≠ 0} := ⟨2, by decide⟩
    have hpvec : p 2 - p 0 =
        (affineBasisOfTriangle p hp).basisOf 0 j := by
      have h := (affineBasisOfTriangle p hp).basisOf_apply 0 j
      change (affineBasisOfTriangle p hp).basisOf 0 j = p 2 - p 0 at h
      exact h.symm
    have hqvec : (affineBasisOfTriangle q hq).basisOf 0 j =
        q 2 - q 0 := by
      have h := (affineBasisOfTriangle q hq).basisOf_apply 0 j
      change (affineBasisOfTriangle q hq).basisOf 0 j = q 2 - q 0 at h
      exact h
    have hequiv := ((affineBasisOfTriangle p hp).basisOf 0).equiv_apply
      j ((affineBasisOfTriangle q hq).basisOf 0) (Equiv.refl _)
    rw [hpvec]
    rw [hequiv]
    simp only [Equiv.refl_apply]
    rw [hqvec]
    abel

theorem triangleAffineEquiv_image_convexHull (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q) :
    triangleAffineEquiv p q hp hq '' convexHull ℝ (Set.range p) =
      convexHull ℝ (Set.range q) := by
  change (triangleAffineEquiv p q hp hq).toAffineMap '' convexHull ℝ (Set.range p) = _
  rw [(triangleAffineEquiv p q hp hq).toAffineMap.image_convexHull]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (triangleAffineEquiv_apply p q hp hq i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p i, ⟨i, rfl⟩, triangleAffineEquiv_apply p q hp hq i⟩

/-- The affine equivalence between ordered triangles carries corresponding line-map points to
corresponding line-map points. -/
theorem triangleAffineEquiv_apply_lineMap (p q : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (hq : AffineIndependent ℝ q)
    (i j : Fin 3) (c : ℝ) :
    triangleAffineEquiv p q hp hq (AffineMap.lineMap (p i) (p j) c) =
      AffineMap.lineMap (q i) (q j) c := by
  let e := triangleAffineEquiv p q hp hq
  have h := AffineMap.apply_lineMap e.toAffineMap (p i) (p j) c
  change e (AffineMap.lineMap (p i) (p j) c) =
    AffineMap.lineMap (e (p i)) (e (p j)) c at h
  rw [h, triangleAffineEquiv_apply, triangleAffineEquiv_apply]

/-- The determinant criterion for three points in the Euclidean plane. -/
theorem affineIndependent_plane_triple_of_det_ne_zero {p₀ p₁ p₂ : Plane}
    (hdet : (p₁ - p₀) 0 * (p₂ - p₀) 1 - (p₁ - p₀) 1 * (p₂ - p₀) 0 ≠ 0) :
    AffineIndependent ℝ ![p₀, p₁, p₂] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Set.mem_insert p₀ {p₁, p₂})).mp hcol
  obtain ⟨a, ha⟩ := hv p₁ (by simp)
  obtain ⟨b, hb⟩ := hv p₂ (by simp)
  have ha0 := congrArg (fun x : Plane => x 0) ha
  have ha1 := congrArg (fun x : Plane => x 1) ha
  have hb0 := congrArg (fun x : Plane => x 0) hb
  have hb1 := congrArg (fun x : Plane => x 1) hb
  apply hdet
  simp only [PiLp.sub_apply, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    at ha0 ha1 hb0 hb1 ⊢
  rw [ha0, ha1, hb0, hb1]
  ring

/-- An affine supporting hyperplane cuts a finite convex hull in precisely the hull of the
vertices lying on that hyperplane. -/
theorem convexHull_inter_affine_zero_of_nonneg (s : Finset Plane) (f : Plane →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    convexHull ℝ (s : Set Plane) ∩ {x | f x = 0} =
      convexHull ℝ ((s.filter fun x => f x = 0 : Finset Plane) : Set Plane) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxconv, hxzero⟩
    obtain ⟨w, hw0, hw1, hwcenter⟩ := Finset.mem_convexHull.mp hxconv
    have hsumf : ∑ y ∈ s, w y * f y = 0 := by
      calc
        ∑ y ∈ s, w y * f y = s.affineCombination ℝ f w := by
          simpa only [smul_eq_mul] using
            (Finset.affineCombination_eq_linear_combination s f w hw1).symm
        _ = f (s.affineCombination ℝ id w) :=
          (s.map_affineCombination id w hw1 f).symm
        _ = f (s.centerMass w id) := by
          congr 1
          rw [Finset.affineCombination_eq_linear_combination s id w hw1,
            Finset.centerMass_eq_of_sum_1 s id hw1]
        _ = f x := by rw [hwcenter]
        _ = 0 := hxzero
    have hterm0 : ∀ y ∈ s, w y * f y = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y hy => mul_nonneg (hw0 y hy) (hf y hy)).mp hsumf
    have hwzero : ∀ y ∈ s, f y ≠ 0 → w y = 0 := by
      intro y hy hfy
      exact (mul_eq_zero.mp (hterm0 y hy)).resolve_right hfy
    let z := s.filter fun y => f y = 0
    have hzsub : z ⊆ s := Finset.filter_subset _ _
    have hsumz : ∑ y ∈ z, w y = 1 := by
      calc
        ∑ y ∈ z, w y = ∑ y ∈ s, w y := Finset.sum_subset hzsub fun y hy hynot =>
          hwzero y hy (by
            intro hfy
            apply hynot
            simp only [z, Finset.mem_filter, hy, hfy, and_self])
        _ = 1 := hw1
    apply Finset.mem_convexHull.mpr
    refine ⟨w, fun y hy => hw0 y (hzsub hy), hsumz, ?_⟩
    have hcenter : z.centerMass w id = s.centerMass w id := by
      rw [Finset.centerMass_eq_of_sum_1 z id hsumz,
        Finset.centerMass_eq_of_sum_1 s id hw1]
      exact Finset.sum_subset hzsub fun y hy hynot => by
        rw [hwzero y hy (by
          intro hfy
          apply hynot
          simp only [z, Finset.mem_filter, hy, hfy, and_self]), zero_smul]
    exact hcenter.trans hwcenter
  · apply convexHull_min
    · intro x hx
      have hx' := subset_convexHull ℝ (s : Set Plane)
        (show x ∈ s from (Finset.mem_filter.mp hx).1)
      exact ⟨hx', (Finset.mem_filter.mp hx).2⟩
    · exact (convex_convexHull ℝ (s : Set Plane)).inter
        ((convex_singleton (0 : ℝ)).affine_preimage f)

/-- Set-valued version of the supporting-hyperplane face formula.  Convex-hull membership uses
only finitely many points, so the finite formula above applies to each witness. -/
theorem convexHull_inter_affine_zero_of_nonneg_set (s : Set Plane)
    (f : Plane →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ s, 0 ≤ f x) :
    convexHull ℝ s ∩ {x | f x = 0} =
      convexHull ℝ (s ∩ {x | f x = 0}) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxHull, hxZero⟩
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hwz⟩ :=
      (mem_convexHull_iff_exists_fintype.mp hxHull)
    let t : Finset Plane := Finset.univ.image z
    have hxt : x ∈ convexHull ℝ (t : Set Plane) := by
      exact mem_convexHull_of_exists_fintype w z hw0 hw1
        (fun i => Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
        (by simp only [hwz])
    have htNonneg : ∀ y ∈ t, 0 ≤ f y := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hf (z i) (hz i)
    have hxFace :
        x ∈ convexHull ℝ ((t.filter fun y => f y = 0 : Finset Plane) : Set Plane) := by
      rw [← convexHull_inter_affine_zero_of_nonneg t f htNonneg]
      exact ⟨hxt, hxZero⟩
    apply convexHull_mono ?_ hxFace
    intro y hy
    have hyt := Finset.mem_filter.mp hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyt.1
    exact ⟨hz i, hyt.2⟩
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull ℝ s hx.1, hx.2⟩
    · exact (convex_convexHull ℝ s).inter
        ((convex_singleton (0 : ℝ)).affine_preimage f)

/-- Two finite convex hulls lying on opposite sides of an affine hyperplane intersect in their
common zero face. -/
theorem convexHull_inter_of_affine_separation (s t u : Finset Plane)
    (f : Plane →ᵃ[ℝ] ℝ) (hs : ∀ x ∈ s, 0 ≤ f x) (ht : ∀ x ∈ t, f x ≤ 0)
    (hszero : s.filter (fun x => f x = 0) = u)
    (htzero : t.filter (fun x => f x = 0) = u) :
    convexHull ℝ (s : Set Plane) ∩ convexHull ℝ (t : Set Plane) =
      convexHull ℝ (u : Set Plane) := by
  let g : Plane →ᵃ[ℝ] ℝ := -f
  have hg : ∀ x ∈ t, 0 ≤ g x := by
    intro x hx
    change 0 ≤ -f x
    linarith [ht x hx]
  have hgzero : t.filter (fun x => g x = 0) = u := by
    rw [← htzero]
    apply Finset.filter_congr
    intro x hx
    simp [g]
  have hsface := convexHull_inter_affine_zero_of_nonneg s f hs
  rw [hszero] at hsface
  have htface := convexHull_inter_affine_zero_of_nonneg t g hg
  rw [hgzero] at htface
  apply Set.Subset.antisymm
  · intro x hx
    have hsnonneg : 0 ≤ f x := by
      apply convexHull_min (fun y hy => hs y hy)
        ((convex_Ici (0 : ℝ)).affine_preimage f) hx.1
    have htnonpos : f x ≤ 0 := by
      apply convexHull_min (fun y hy => ht y hy)
        ((convex_Iic (0 : ℝ)).affine_preimage f) hx.2
    have hxzero : f x = 0 := le_antisymm htnonpos hsnonneg
    rw [← hsface]
    exact ⟨hx.1, hxzero⟩
  · intro x hx
    have hxs : x ∈ convexHull ℝ (s : Set Plane) := by
      rw [← hsface] at hx
      exact hx.1
    have hxt : x ∈ convexHull ℝ (t : Set Plane) := by
      rw [← htface] at hx
      exact hx.1
    exact ⟨hxs, hxt⟩

/-- Vertex-indexed form of `convexHull_inter_of_affine_separation`.  This is the form used when
checking the maximal triangles of a mesh. -/
theorem convexHull_image_inter_of_affine_separation {V : Type*} [DecidableEq V]
    (position : V → Plane) (_ : Function.Injective position) (s t : Finset V)
    (f : Plane →ᵃ[ℝ] ℝ) (hs : ∀ v ∈ s, 0 ≤ f (position v))
    (ht : ∀ v ∈ t, f (position v) ≤ 0)
    (hszero : ∀ v ∈ s, f (position v) = 0 ↔ v ∈ (s ∩ t))
    (htzero : ∀ v ∈ t, f (position v) = 0 ↔ v ∈ (s ∩ t)) :
    convexHull ℝ (position '' (s : Set V)) ∩ convexHull ℝ (position '' (t : Set V)) =
      convexHull ℝ (position '' ((s ∩ t : Finset V) : Set V)) := by
  classical
  have hsfilter : (s.image position).filter (fun x => f x = 0) =
      (s ∩ t).image position := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvzero⟩
      exact ⟨v, (hszero v hv).mp hvzero, rfl⟩
    · rintro ⟨v, hvst, rfl⟩
      exact ⟨⟨v, (Finset.mem_inter.mp hvst).1, rfl⟩,
        (hszero v (Finset.mem_inter.mp hvst).1).mpr hvst⟩
  have htfilter : (t.image position).filter (fun x => f x = 0) =
      (s ∩ t).image position := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hvzero⟩
      exact ⟨v, (htzero v hv).mp hvzero, rfl⟩
    · rintro ⟨v, hvst, rfl⟩
      exact ⟨⟨v, (Finset.mem_inter.mp hvst).2, rfl⟩,
        (htzero v (Finset.mem_inter.mp hvst).2).mpr hvst⟩
  simpa only [Finset.coe_image] using
    convexHull_inter_of_affine_separation (s.image position) (t.image position)
      ((s ∩ t).image position) f
      (by rintro x hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx; exact hs v hv)
      (by rintro x hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx; exact ht v hv)
      hsfilter htfilter

/-! ## The reference split of a triangle -/

/-- A point of the Euclidean plane with the displayed Cartesian coordinates. -/
def planePoint (x y : ℝ) : Plane :=
  WithLp.toLp 2 ![x, y]

@[simp] theorem planePoint_apply_zero (x y : ℝ) : planePoint x y 0 = x := rfl
@[simp] theorem planePoint_apply_one (x y : ℝ) : planePoint x y 1 = y := rfl

/-- Vertices of the reference line split: the standard triangle vertices followed by one point
on each edge issuing from the origin. -/
def referenceSplitPosition (a b : ℝ) : Fin 5 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1, planePoint a 0, planePoint 0 b]

/-- The `referenceSplitTriangles` declaration. -/
def referenceSplitTriangles : Finset (Finset (Fin 5)) :=
  {{0, 3, 4}, {1, 2, 3}, {2, 3, 4}}

theorem referenceSplitPosition_injective {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : Function.Injective (referenceSplitPosition a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    dsimp [referenceSplitPosition] at hij
    have h0 := congrArg (fun x : Plane => x 0) hij
    have h1 := congrArg (fun x : Plane => x 1) hij
    simp only [planePoint_apply_zero] at h0
    simp only [planePoint_apply_one] at h1
    linarith

theorem referenceSplit_triangle0_affineIndependent {a b : ℝ} (ha0 : 0 < a)
    (hb0 : 0 < b) :
    AffineIndependent ℝ ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem referenceSplit_triangle1_affineIndependent {a : ℝ} (ha1 : a < 1) :
    AffineIndependent ℝ ![planePoint a 0, planePoint 1 0, planePoint 0 1] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

theorem referenceSplit_triangle2_affineIndependent {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) :
    AffineIndependent ℝ ![planePoint a 0, planePoint 0 1, planePoint 0 b] := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

/-- The first Cartesian coordinate, regarded as an affine functional. -/
noncomputable def cartesianX : Plane →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toAffineMap

/-- The second Cartesian coordinate, regarded as an affine functional. -/
noncomputable def cartesianY : Plane →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap).toAffineMap

@[simp] theorem cartesianX_apply (p : Plane) : cartesianX p = p 0 := rfl
@[simp] theorem cartesianY_apply (p : Plane) : cartesianY p = p 1 := rfl

/-- The affine line through the two new edge points in the reference split. -/
noncomputable def referenceOuterAffine (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  a⁻¹ • cartesianX + b⁻¹ • cartesianY - AffineMap.const ℝ Plane 1

/-- The affine line through `(a,0)` and `(0,1)` in the reference split. -/
noncomputable def referenceDiagonalAffine (a : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + a • cartesianY - AffineMap.const ℝ Plane a

/-- A line through `(a,0)` lying strictly between the other two rays of the reference split.
Its second coefficient is chosen between `a` and `a / b`. -/
noncomputable def referenceVertexAffine (a b : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  cartesianX + (a * (1 + b) / (2 * b)) • cartesianY - AffineMap.const ℝ Plane a

@[simp] theorem referenceOuterAffine_planePoint (a b x y : ℝ) :
    referenceOuterAffine a b (planePoint x y) = a⁻¹ * x + b⁻¹ * y - 1 := rfl

@[simp] theorem referenceDiagonalAffine_planePoint (a x y : ℝ) :
    referenceDiagonalAffine a (planePoint x y) = x + a * y - a := rfl

@[simp] theorem referenceVertexAffine_planePoint (a b x y : ℝ) :
    referenceVertexAffine a b (planePoint x y) =
      x + (a * (1 + b) / (2 * b)) * y - a := rfl

private theorem affineIndependent_referenceTriangle0 {a b : ℝ} (ha0 : 0 < a)
    (hb0 : 0 < b) :
    AffineIndependent ℝ fun v : ({0, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (0 : Fin 5) 3 4 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have heq : ((fun v : ({0, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact referenceSplit_triangle0_affineIndependent ha0 hb0

private theorem affineIndependent_referenceTriangle1 {a b : ℝ} (ha1 : a < 1) :
    AffineIndependent ℝ fun v : ({1, 2, 3} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (1 : Fin 5) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({1, 2, 3} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

private theorem affineIndependent_referenceTriangle2 {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < 1) :
    AffineIndependent ℝ fun v : ({2, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v := by
  let e := (Fin.orderIsoTriple (2 : Fin 5) 3 4 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({2, 3, 4} : Finset (Fin 5)) =>
      referenceSplitPosition a b v) ∘ e) =
      ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

/-- The three triangles produced when a line meets the two edges issuing from the origin of the
standard triangle. -/
noncomputable def referenceSplitMesh (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : TriangleMesh where
  Vertex := Fin 5
  position := referenceSplitPosition a b
  position_injective := referenceSplitPosition_injective ha0 ha1 hb0 hb1
  triangles := referenceSplitTriangles
  card_triangle := by
    intro t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide
  affineIndependent_triangle := by
    intro t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact affineIndependent_referenceTriangle0 ha0 hb0
    · exact affineIndependent_referenceTriangle1 ha1
    · exact affineIndependent_referenceTriangle2 ha0 hb1
  triangle_inter := by
    intro s hs t ht
    simp only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceVertexAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_zero, AffineMap.coe_neg,
            Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero, zero_sub, neg_neg,
            Matrix.cons_val, sub_self, neg_zero, Std.le_refl, zero_add, neg_sub, sub_nonneg] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, tsub_le_iff_right,
            zero_add, Matrix.cons_val, mul_one, sub_self, neg_zero, Std.le_refl] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, Fin.reduceEq,
            Finset.mem_singleton, or_self, or_false, referenceSplitPosition, Matrix.cons_val_zero,
            AffineMap.coe_neg, Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero,
            zero_sub, neg_neg, one_ne_zero, not_false_eq_true, Finset.inter_insert_of_notMem,
            or_true, Finset.inter_singleton_of_mem, iff_false, Fin.mk_one, Fin.reduceFinMk,
            Matrix.cons_val, sub_self, neg_zero, zero_add, neg_sub] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq,
            Finset.mem_singleton, or_self, Fin.mk_one, or_false, referenceSplitPosition,
            Matrix.cons_val_one, Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, one_ne_zero,
            not_false_eq_true, Finset.inter_insert_of_notMem, or_true,
            Finset.inter_singleton_of_mem, iff_false, Fin.reduceFinMk, Matrix.cons_val, mul_one,
            zero_add, sub_self, neg_zero] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceOuterAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne']
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val, AffineMap.coe_neg,
            Pi.neg_apply, referenceOuterAffine_planePoint, mul_zero, mul_one, zero_add, neg_sub,
            tsub_le_iff_right, ne_eq, ha0.ne', not_false_eq_true, inv_mul_cancel₀, add_zero,
            sub_self, neg_zero, Std.le_refl, hb0.ne'];
          (try field_simp); nlinarith
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢; field_simp; nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceVertexAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_zero, AffineMap.coe_neg,
            Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero, zero_sub, neg_neg,
            Matrix.cons_val, sub_self, neg_zero, Std.le_refl, zero_add, neg_sub, sub_nonneg] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp only [referenceSplitPosition, Fin.isValue, Matrix.cons_val_one,
            Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, tsub_le_iff_right,
            zero_add, Matrix.cons_val, mul_one, sub_self, neg_zero, Std.le_refl] <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, Fin.reduceEq,
            Finset.mem_singleton, or_self, or_false, referenceSplitPosition, Matrix.cons_val_zero,
            AffineMap.coe_neg, Pi.neg_apply, referenceVertexAffine_planePoint, mul_zero, add_zero,
            zero_sub, neg_neg, one_ne_zero, not_false_eq_true, Finset.inter_insert_of_notMem,
            or_true, Finset.inter_singleton_of_mem, iff_false, Fin.mk_one, Fin.reduceFinMk,
            Matrix.cons_val, sub_self, neg_zero, zero_add, neg_sub] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
      · intro x hx
        fin_cases x <;>
          simp only [Fin.isValue, Fin.zero_eta, Finset.mem_insert, zero_ne_one, Fin.reduceEq,
            Finset.mem_singleton, or_self, Fin.mk_one, or_false, referenceSplitPosition,
            Matrix.cons_val_one, Matrix.cons_val_zero, AffineMap.coe_neg, Pi.neg_apply,
            referenceVertexAffine_planePoint, mul_zero, add_zero, neg_sub, one_ne_zero,
            not_false_eq_true, Finset.inter_insert_of_notMem, or_true,
            Finset.inter_singleton_of_mem, iff_false, Fin.reduceFinMk, Matrix.cons_val, mul_one,
            zero_add, sub_self, neg_zero] at hx ⊢ <;>
          (try field_simp) <;> nlinarith
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (referenceDiagonalAffine a)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (-referenceOuterAffine a b)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne']
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceOuterAffine_planePoint, ha0.ne', hb0.ne'];
          field_simp; nlinarith
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢
      · intro x hx
        fin_cases x <;> simp [referenceSplitPosition, referenceOuterAffine_planePoint,
          ha0.ne', hb0.ne'] at hx ⊢; field_simp; nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceSplitPosition_injective ha0 ha1 hb0 hb1) _ _ (referenceDiagonalAffine a)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · simp

/-- A three-term nonnegative affine combination belongs to the corresponding triangle. -/
theorem mem_convexHull_range_fin3_of_weights (p : Fin 3 → Plane) (x : Plane)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : w 0 + w 1 + w 2 = 1)
    (hx : w 0 • p 0 + w 1 • p 1 + w 2 • p 2 = x) :
    x ∈ convexHull ℝ (Set.range p) := by
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨Finset.univ, w, fun i _ => hw i, ?_, ?_⟩
  · simpa [Fin.sum_univ_succ, add_assoc] using hsum
  · rw [Finset.affineCombination_eq_linear_combination]
    · simpa [Fin.sum_univ_succ, add_assoc] using hx
    · simpa [Fin.sum_univ_succ, add_assoc] using hsum

/-- Cartesian membership criterion for the standard closed triangle. -/
theorem mem_standardTriangle_iff (x : Plane) :
    x ∈ convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) ↔
      0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianX) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp
    · apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage cartesianY) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp
    · let f : Plane →ᵃ[ℝ] ℝ := cartesianX + cartesianY
      apply convexHull_min _ ((convex_Iic (1 : ℝ)).affine_preimage f) hx
      rintro p ⟨i, rfl⟩
      fin_cases i <;> simp [f]
  · rintro ⟨hx0, hx1, hxsum⟩
    apply mem_convexHull_range_fin3_of_weights _ x
      ![1 - x 0 - x 1, x 0, x 1]
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp
      ring
    · ext i
      fin_cases i <;> simp [planePoint]

private theorem referenceTriangle0_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({0, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 0 0, planePoint a 0, planePoint 0 b] := by
  ext x
  simp [referenceSplitPosition]
  tauto

private theorem referenceTriangle1_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({1, 2, 3} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 1 0, planePoint 0 1, planePoint a 0] := by
  ext x
  simp [referenceSplitPosition]
  tauto

private theorem referenceTriangle2_carrier (a b : ℝ) :
    referenceSplitPosition a b '' (({2, 3, 4} : Finset (Fin 5)) : Set (Fin 5)) =
      Set.range ![planePoint 0 1, planePoint a 0, planePoint 0 b] := by
  ext x
  simp [referenceSplitPosition]
  tauto

/-- The three reference triangles cover exactly the standard triangle. -/
theorem referenceSplit_union (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    (⋃ t ∈ referenceSplitTriangles,
      convexHull ℝ (referenceSplitPosition a b '' (t : Set (Fin 5)))) =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    have ht' : t = {0, 3, 4} ∨ t = {1, 2, 3} ∨ t = {2, 3, 4} := by
      simpa only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] using ht
    rcases ht' with rfl | rfl | rfl
    · rw [referenceTriangle0_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le, hb0.le, hb1.le]
    · rw [referenceTriangle1_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le]
    · rw [referenceTriangle2_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;>
        simp [ha0.le, ha1.le, hb0.le, hb1.le]
  · intro hx
    obtain ⟨hx0, hx1, hxsum⟩ := (mem_standardTriangle_iff x).mp hx
    by_cases houter : x 0 / a + x 1 / b ≤ 1
    · refine ⟨{0, 3, 4}, Finset.mem_insert_self _ _, ?_⟩
      rw [referenceTriangle0_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![1 - x 0 / a - x 1 / b, x 0 / a, x 1 / b]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, sub_nonneg]
          linarith
        · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          exact div_nonneg hx0 ha0.le
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg hx1 hb0.le
      · simp
        ring
      · ext i
        fin_cases i <;> simp [planePoint] <;> field_simp
    · have houter' : 1 ≤ x 0 / a + x 1 / b := le_of_not_ge houter
      by_cases hdiag : 0 ≤ x 0 + a * x 1 - a
      · have h1a : 1 - a ≠ 0 := by linarith
        refine ⟨{1, 2, 3}, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
        rw [referenceTriangle1_carrier]
        apply mem_convexHull_range_fin3_of_weights _ x
          ![(x 0 + a * x 1 - a) / (1 - a), x 1,
            (1 - x 0 - x 1) / (1 - a)]
        · intro i
          fin_cases i
          · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
            exact div_nonneg hdiag (by linarith)
          · simpa using hx1
          · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
            exact div_nonneg (by linarith) (by linarith)
        · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val]
          field_simp [h1a]
          ring
        · ext i
          fin_cases i <;> simp [planePoint] ; field_simp [h1a] ; ring
      · have hdiag' : x 0 + a * x 1 - a ≤ 0 := le_of_not_ge hdiag
        have h1b : 1 - b ≠ 0 := by linarith
        have hnum0 : 0 ≤ x 1 - b + b * (x 0 / a) := by
          have hy : 1 - x 0 / a ≤ x 1 / b := by linarith
          have hy' : (1 - x 0 / a) * b ≤ x 1 := (le_div_iff₀ hb0).mp hy
          linarith
        have hnum2 : 0 ≤ 1 - x 1 - x 0 / a := by
          have hxdiv : x 0 / a ≤ 1 - x 1 :=
            (div_le_iff₀ ha0).mpr (by nlinarith [hdiag'])
          linarith
        refine ⟨{2, 3, 4}, Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
        rw [referenceTriangle2_carrier]
        apply mem_convexHull_range_fin3_of_weights _ x
          ![(x 1 - b + b * (x 0 / a)) / (1 - b), x 0 / a,
            (1 - x 1 - x 0 / a) / (1 - b)]
        · intro i
          fin_cases i
          · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
            exact div_nonneg hnum0 (by linarith)
          · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
            exact div_nonneg hx0 ha0.le
          · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
            exact div_nonneg hnum2 (by linarith)
        · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          field_simp [h1b, ha0.ne']
          ring
        · ext i
          fin_cases i <;> simp [planePoint] <;>
            field_simp [h1b, ha0.ne']; ring

/-- The reference line split preserves the support of the standard triangle. -/
theorem referenceSplitMesh_support (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    (referenceSplitMesh a b ha0 ha1 hb0 hb1).toPlaneComplex.support =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ referenceSplitTriangles,
    convexHull ℝ (referenceSplitPosition a b '' (t : Set (Fin 5)))) = _
  exact referenceSplit_union a b ha0 ha1 hb0 hb1

/-! ## The reference split through one vertex -/

/-- The `referenceEdgeSplitPosition` declaration. -/
def referenceEdgeSplitPosition (c : ℝ) : Fin 4 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1, planePoint c 0]

/-- The `referenceEdgeSplitTriangles` declaration. -/
def referenceEdgeSplitTriangles : Finset (Finset (Fin 4)) :=
  {{0, 2, 3}, {1, 2, 3}}

theorem referenceEdgeSplitPosition_injective {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Function.Injective (referenceEdgeSplitPosition c) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    dsimp [referenceEdgeSplitPosition] at hij
    have h0 := congrArg (fun x : Plane => x 0) hij
    have h1 := congrArg (fun x : Plane => x 1) hij
    simp only [planePoint_apply_zero] at h0
    simp only [planePoint_apply_one] at h1
    linarith

private theorem affineIndependent_referenceEdgeTriangle0 {c : ℝ} (hc0 : 0 < c) :
    AffineIndependent ℝ fun v : ({0, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v := by
  let e := (Fin.orderIsoTriple (0 : Fin 4) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({0, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v) ∘ e) =
      ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

private theorem affineIndependent_referenceEdgeTriangle1 {c : ℝ} (hc1 : c < 1) :
    AffineIndependent ℝ fun v : ({1, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v := by
  let e := (Fin.orderIsoTriple (1 : Fin 4) 2 3 (by decide) (by decide)).toEquiv
  apply (affineIndependent_equiv e).mp
  have h : AffineIndependent ℝ ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
    apply affineIndependent_plane_triple_of_det_ne_zero
    simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
    nlinarith
  have heq : ((fun v : ({1, 2, 3} : Finset (Fin 4)) =>
      referenceEdgeSplitPosition c v) ∘ e) =
      ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
    funext i
    fin_cases i <;> rfl
  rw [heq]
  exact h

/-- The two-triangle reference mesh used when the cutting line passes through vertex `2`. -/
noncomputable def referenceEdgeSplitMesh (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    TriangleMesh where
  Vertex := Fin 4
  position := referenceEdgeSplitPosition c
  position_injective := referenceEdgeSplitPosition_injective hc0 hc1
  triangles := referenceEdgeSplitTriangles
  card_triangle := by
    intro t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide
  affineIndependent_triangle := by
    intro t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact affineIndependent_referenceEdgeTriangle0 hc0
    · exact affineIndependent_referenceEdgeTriangle1 hc1
  triangle_inter := by
    intro s hs t ht
    simp only [referenceEdgeSplitTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simp
    · apply convexHull_image_inter_of_affine_separation _
        (referenceEdgeSplitPosition_injective hc0 hc1) _ _ (-referenceDiagonalAffine c)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · rw [Set.inter_comm]
      apply convexHull_image_inter_of_affine_separation _
        (referenceEdgeSplitPosition_injective hc0 hc1) _ _ (-referenceDiagonalAffine c)
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint]; nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
      · intro x hx
        fin_cases x <;>
          simp [referenceEdgeSplitPosition, referenceDiagonalAffine_planePoint] at hx ⊢;
          nlinarith
    · simp

private theorem referenceEdgeTriangle0_carrier (c : ℝ) :
    referenceEdgeSplitPosition c '' (({0, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) =
      Set.range ![planePoint 0 0, planePoint 0 1, planePoint c 0] := by
  ext x
  simp [referenceEdgeSplitPosition]
  tauto

private theorem referenceEdgeTriangle1_carrier (c : ℝ) :
    referenceEdgeSplitPosition c '' (({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) =
      Set.range ![planePoint 1 0, planePoint 0 1, planePoint c 0] := by
  ext x
  simp [referenceEdgeSplitPosition]
  tauto

theorem referenceEdgeSplit_union (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (⋃ t ∈ referenceEdgeSplitTriangles,
      convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set (Fin 4)))) =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hxt⟩
    have ht' : t = {0, 2, 3} ∨ t = {1, 2, 3} := by
      simpa only [referenceEdgeSplitTriangles, Finset.mem_insert,
        Finset.mem_singleton, or_false] using ht
    rcases ht' with rfl | rfl
    · rw [referenceEdgeTriangle0_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;> simp [hc0.le, hc1.le]
    · rw [referenceEdgeTriangle1_carrier] at hxt
      apply convexHull_min _ (convex_convexHull ℝ _) hxt
      rintro p ⟨i, rfl⟩
      fin_cases i <;> apply (mem_standardTriangle_iff _).mpr <;> simp [hc0.le, hc1.le]
  · intro hx
    obtain ⟨hx0, hx1, hxsum⟩ := (mem_standardTriangle_iff x).mp hx
    by_cases hd : x 0 + c * x 1 - c ≤ 0
    · refine ⟨{0, 2, 3}, Finset.mem_insert_self _ _, ?_⟩
      rw [referenceEdgeTriangle0_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![1 - x 1 - x 0 / c, x 1, x 0 / c]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, sub_nonneg]
          have hxdiv : x 0 / c ≤ 1 - x 1 :=
            (div_le_iff₀ hc0).mpr (by nlinarith [hd])
          have : x 0 / c + x 1 ≤ 1 := by linarith
          linarith
        · simpa using hx1
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg hx0 hc0.le
      · simp
        ring
      · ext i
        fin_cases i <;> simp [planePoint] ; field_simp [hc0.ne']
    · have hd' : 0 ≤ x 0 + c * x 1 - c := le_of_not_ge hd
      have h1c : 1 - c ≠ 0 := by linarith
      refine ⟨{1, 2, 3}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
      rw [referenceEdgeTriangle1_carrier]
      apply mem_convexHull_range_fin3_of_weights _ x
        ![(x 0 + c * x 1 - c) / (1 - c), x 1,
          (1 - x 0 - x 1) / (1 - c)]
      · intro i
        fin_cases i
        · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
          exact div_nonneg hd' (by linarith)
        · simpa using hx1
        · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
          exact div_nonneg (by linarith) (by linarith)
      · simp
        field_simp [h1c]
        ring
      · ext i
        fin_cases i <;> simp [planePoint] ; field_simp [h1c] ; ring

theorem referenceEdgeSplitMesh_support (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (referenceEdgeSplitMesh c hc0 hc1).toPlaneComplex.support =
      convexHull ℝ (Set.range ![planePoint 0 0, planePoint 1 0, planePoint 0 1]) := by
  rw [TriangleMesh.toPlaneComplex_support]
  change (⋃ t ∈ referenceEdgeSplitTriangles,
    convexHull ℝ (referenceEdgeSplitPosition c '' (t : Set (Fin 4)))) = _
  exact referenceEdgeSplit_union c hc0 hc1

/-- The point where the affine functional `f` vanishes along the oriented edge from `p` to `q`.
The useful case is `f p > 0 > f q`. -/
noncomputable def affineCutPoint (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : Plane :=
  AffineMap.lineMap p q (f p / (f p - f q))

namespace affineCutPoint

variable (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane)

theorem parameter_pos (hp : 0 < f p) (hq : f q < 0) :
    0 < f p / (f p - f q) := by
  exact div_pos hp (by linarith)

theorem parameter_lt_one (hp : 0 < f p) (hq : f q < 0) :
    f p / (f p - f q) < 1 := by
  apply (div_lt_one (by linarith : 0 < f p - f q)).mpr
  linarith

theorem parameter_mem_Icc (hp : 0 < f p) (hq : f q < 0) :
    f p / (f p - f q) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(parameter_pos f p q hp hq).le, (parameter_lt_one f p q hp hq).le⟩

theorem mem_segment (hp : 0 < f p) (hq : f q < 0) :
    affineCutPoint f p q ∈ segment ℝ p q := by
  rw [segment_eq_image_lineMap]
  exact ⟨f p / (f p - f q), parameter_mem_Icc f p q hp hq, rfl⟩

@[simp] theorem apply_eq_zero (hp : 0 < f p) (hq : f q < 0) :
    f (affineCutPoint f p q) = 0 := by
  rw [affineCutPoint, f.apply_lineMap, AffineMap.lineMap_apply_module]
  have hden : f p - f q ≠ 0 := by linarith
  field_simp [hden]
  ring

theorem ne_left (hp : 0 < f p) (hq : f q < 0) : affineCutPoint f p q ≠ p := by
  intro h
  have := congrArg f h
  rw [apply_eq_zero f p q hp hq] at this
  linarith

theorem ne_right (hp : 0 < f p) (hq : f q < 0) : affineCutPoint f p q ≠ q := by
  intro h
  have := congrArg f h
  rw [apply_eq_zero f p q hp hq] at this
  linarith

theorem eq_reverse (hp : 0 < f p) (hq : f q < 0) :
    affineCutPoint f p q = affineCutPoint f q p := by
  unfold affineCutPoint
  rw [← AffineMap.lineMap_apply_one_sub p q]
  congr 1
  have hden : f p - f q ≠ 0 := by linarith
  have hden' : f q - f p ≠ 0 := by linarith
  field_simp [hden, hden']
  ring

/-- The cut point is the unique zero of `f` on an oppositely signed edge. -/
theorem eq_of_mem_segment_of_apply_eq_zero (hp : 0 < f p) (hq : f q < 0)
    {x : Plane} (hx : x ∈ segment ℝ p q) (hfx : f x = 0) :
    x = affineCutPoint f p q := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [f.apply_lineMap, AffineMap.lineMap_apply_module] at hfx
  have hden : f p - f q ≠ 0 := by linarith
  unfold affineCutPoint
  congr 1
  apply (eq_div_iff hden).mpr
  simp only [smul_eq_mul] at hfx
  linarith

/-- Negating the affine functional does not change its geometric cut point. -/
theorem neg (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) :
    affineCutPoint (-f) p q = affineCutPoint f p q := by
  unfold affineCutPoint
  congr 1
  simp only [AffineMap.coe_neg, Pi.neg_apply]
  by_cases h : f p - f q = 0
  · have hpq : f p = f q := sub_eq_zero.mp h
    rw [hpq]
    simp
  · have hneg : -f p + f q ≠ 0 := by
      intro hneg
      apply h
      linarith
    field_simp [h, hneg]
    ring

end affineCutPoint

/-! ## The transported split of an arbitrary triangle -/

/-- The ordered vertices of the standard triangle. -/
def standardTrianglePosition : Fin 3 → Plane :=
  ![planePoint 0 0, planePoint 1 0, planePoint 0 1]

theorem standardTrianglePosition_affineIndependent :
    AffineIndependent ℝ standardTrianglePosition := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [standardTrianglePosition, planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]

/-- The parameter at which a line cuts the edge from the positive vertex to a negative vertex. -/
noncomputable def triangleCutParameter (f : Plane →ᵃ[ℝ] ℝ) (p q : Plane) : ℝ :=
  f p / (f p - f q)

/-- The reference split transported to an arbitrary ordered triangle.  The first vertex is on
the positive side of the line and the other two are on its negative side. -/
noncomputable def triangleLineSplitMesh (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] ℝ) (hp0 : 0 < f (p 0)) (hp1 : f (p 1) < 0)
    (hp2 : f (p 2) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (p 0) (p 1)
  let b := triangleCutParameter f (p 0) (p 2)
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f (p 0) (p 1) hp0 hp1)
    (affineCutPoint.parameter_lt_one f (p 0) (p 1) hp0 hp1)
    (affineCutPoint.parameter_pos f (p 0) (p 2) hp0 hp2)
    (affineCutPoint.parameter_lt_one f (p 0) (p 2) hp0 hp2)
  R.mapAffineEquiv
    (triangleAffineEquiv standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp)

/-- Splitting a triangle along an affine line preserves its support. -/
theorem triangleLineSplitMesh_support (p : Fin 3 → Plane) (hp : AffineIndependent ℝ p)
    (f : Plane →ᵃ[ℝ] ℝ) (hp0 : 0 < f (p 0)) (hp1 : f (p 1) < 0)
    (hp2 : f (p 2) < 0) :
    (triangleLineSplitMesh p hp f hp0 hp1 hp2).toPlaneComplex.support =
      convexHull ℝ (Set.range p) := by
  let a := triangleCutParameter f (p 0) (p 1)
  let b := triangleCutParameter f (p 0) (p 2)
  have ha0 : 0 < a := affineCutPoint.parameter_pos f (p 0) (p 1) hp0 hp1
  have ha1 : a < 1 := affineCutPoint.parameter_lt_one f (p 0) (p 1) hp0 hp1
  have hb0 : 0 < b := affineCutPoint.parameter_pos f (p 0) (p 2) hp0 hp2
  have hb1 : b < 1 := affineCutPoint.parameter_lt_one f (p 0) (p 2) hp0 hp2
  change ((referenceSplitMesh a b ha0 ha1 hb0 hb1).mapAffineEquiv
    (triangleAffineEquiv standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp)).toPlaneComplex.support = _
  rw [TriangleMesh.mapAffineEquiv_support,
    referenceSplitMesh_support a b ha0 ha1 hb0 hb1]
  exact triangleAffineEquiv_image_convexHull standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp

/-! ## Coherent cut vertices for a finite mesh -/

namespace TriangleMesh

variable (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ)

/-- The maximal triangles, packaged with their membership proof. -/
abbrev Triangle := {t : Finset M.Vertex // t ∈ M.triangles}

/-- A proof-independent ordering of the three vertices of a maximal triangle. -/
noncomputable def triangleEquiv (t : M.Triangle) : t.1 ≃ Fin 3 :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, M.card_triangle t.1 t.2])

/-- A proof-independent ordering of the three vertices of a maximal triangle. -/
noncomputable def orderedVertex (t : M.Triangle) : Fin 3 → M.Vertex :=
  fun i => ((M.triangleEquiv t).symm i).1

theorem orderedVertex_injective (t : M.Triangle) :
    Function.Injective (M.orderedVertex t) := by
  intro i j hij
  exact (M.triangleEquiv t).symm.injective (Subtype.ext hij)

theorem range_orderedVertex (t : M.Triangle) :
    Set.range (M.orderedVertex t) = (t.1 : Set M.Vertex) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ((M.triangleEquiv t).symm i).2
  · intro hv
    let vt : t.1 := ⟨v, hv⟩
    exact ⟨M.triangleEquiv t vt, by
      simp only [orderedVertex, Equiv.symm_apply_apply, vt]⟩

theorem orderedVertex_mem (t : M.Triangle) (i : Fin 3) : M.orderedVertex t i ∈ t.1 := by
  have h : M.orderedVertex t i ∈ Set.range (M.orderedVertex t) := Set.mem_range_self i
  rwa [M.range_orderedVertex t] at h

theorem orderedVertex_affineIndependent (t : M.Triangle) :
    AffineIndependent ℝ (M.position ∘ M.orderedVertex t) := by
  let e : Fin 3 ≃ t.1 := (M.triangleEquiv t).symm
  have h := (affineIndependent_equiv e).mpr (M.affineIndependent_triangle t.1 t.2)
  have heq : ((fun v : t.1 => M.position v) ∘ e) =
      M.position ∘ M.orderedVertex t := by
    rfl
  rw [← heq]
  exact h

/-- Ordered pairs of old vertices whose values under `f` have opposite signs.  Both orientations
are retained; their geometric cut positions are equal and are deduplicated in `refinementPoints`.
-/
noncomputable def crossingPairs : Finset (M.Vertex × M.Vertex) :=
  (Finset.univ ×ˢ Finset.univ).filter fun uv =>
    f (M.position uv.1) * f (M.position uv.2) < 0

/-- The geometric zero of `f` on an oppositely signed pair of old vertices. -/
noncomputable def pairCutPosition (u v : M.Vertex) : Plane :=
  affineCutPoint f (M.position u) (M.position v)

/-- All old vertex positions together with all possible cut positions.  Using geometric points
as the new vertex labels automatically identifies the cut computed from the two orientations of
one edge, and the same edge as seen from its two incident triangles. -/
noncomputable def refinementPoints : Finset Plane :=
  Finset.univ.image M.position ∪
    (M.crossingPairs f).image fun uv => M.pairCutPosition f uv.1 uv.2

/-- Vertex type used by the coherent refinement. -/
abbrev RefinedVertex := {p : Plane // p ∈ M.refinementPoints f}

/-- An old vertex as a vertex of the coherent refinement. -/
noncomputable def oldRefinedVertex (v : M.Vertex) : M.RefinedVertex f :=
  ⟨M.position v, by
    unfold refinementPoints
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩

/-- The cut point of an oppositely signed pair as a vertex of the coherent refinement. -/
noncomputable def cutRefinedVertex (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) : M.RefinedVertex f :=
  ⟨M.pairCutPosition f u v, by
    unfold refinementPoints
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(u, v), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, huv⟩, rfl⟩⟩

@[simp] theorem oldRefinedVertex_val (v : M.Vertex) :
    (M.oldRefinedVertex f v : Plane) = M.position v := rfl

@[simp] theorem cutRefinedVertex_val (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    (M.cutRefinedVertex f u v huv : Plane) = M.pairCutPosition f u v := rfl

theorem pairCutPosition_eq_reverse (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    M.pairCutPosition f u v = M.pairCutPosition f v u := by
  rcases mul_neg_iff.mp huv with huv | huv
  · exact affineCutPoint.eq_reverse f (M.position u) (M.position v) huv.1 huv.2
  · exact (affineCutPoint.eq_reverse f (M.position v) (M.position u) huv.2 huv.1).symm

theorem pairCutPosition_apply_eq_zero (u v : M.Vertex)
    (huv : f (M.position u) * f (M.position v) < 0) :
    f (M.pairCutPosition f u v) = 0 := by
  rcases mul_neg_iff.mp huv with huv | huv
  · exact affineCutPoint.apply_eq_zero f (M.position u) (M.position v) huv.1 huv.2
  · rw [M.pairCutPosition_eq_reverse f u v (mul_neg_iff.mpr (Or.inr huv))]
    exact affineCutPoint.apply_eq_zero f (M.position v) (M.position u) huv.2 huv.1

theorem crossingPairs_neg : M.crossingPairs (-f) = M.crossingPairs f := by
  classical
  unfold crossingPairs
  apply Finset.filter_congr
  intro uv huv
  simp only [AffineMap.coe_neg, Pi.neg_apply]
  ring_nf

theorem refinementPoints_neg : M.refinementPoints (-f) = M.refinementPoints f := by
  classical
  unfold refinementPoints pairCutPosition
  rw [M.crossingPairs_neg f]
  congr 1
  apply Finset.image_congr
  intro uv huv
  exact affineCutPoint.neg f (M.position uv.1) (M.position uv.2)

/-- Identifying the coherent vertex pools for `f` and `-f`; geometrically this is the identity. -/
noncomputable def refinedVertexNegEquiv : M.RefinedVertex (-f) ≃ M.RefinedVertex f where
  toFun v := ⟨v.1, by rw [← M.refinementPoints_neg f]; exact v.2⟩
  invFun v := ⟨v.1, by rw [M.refinementPoints_neg f]; exact v.2⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

@[simp] theorem refinedVertexNegEquiv_val (v : M.RefinedVertex (-f)) :
    (M.refinedVertexNegEquiv f v : Plane) = v := rfl

/-- The five vertices of the strict `+--` model in the coherent global vertex pool. -/
noncomputable def strictModelVertex (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : Fin 5 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (M.orderedVertex t 0),
    M.oldRefinedVertex f (M.orderedVertex t 1),
    M.oldRefinedVertex f (M.orderedVertex t 2),
    M.cutRefinedVertex f (M.orderedVertex t 0) (M.orderedVertex t 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩)),
    M.cutRefinedVertex f (M.orderedVertex t 0) (M.orderedVertex t 2)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))]

/-- The geometric five-point list underlying a strict split. -/
noncomputable def strictModelPosition (p : Fin 3 → Plane) (f : Plane →ᵃ[ℝ] ℝ) : Fin 5 → Plane :=
  ![p 0, p 1, p 2, affineCutPoint f (p 0) (p 1), affineCutPoint f (p 0) (p 2)]

theorem strictModelVertex_val (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) (i : Fin 5) :
    (M.strictModelVertex f t h0 h1 h2 i : Plane) =
      strictModelPosition (M.position ∘ M.orderedVertex t) f i := by
  fin_cases i <;> rfl

/-- Geometric identification of the strict five-point list with the affine image of the reference
split. -/
theorem strictModelPosition_eq_affineReference (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (_ : 0 < f (p 0)) (_ : f (p 1) < 0)
    (_ : f (p 2) < 0) (i : Fin 5) :
    strictModelPosition p f i =
      triangleAffineEquiv standardTrianglePosition p standardTrianglePosition_affineIndependent hp
        (referenceSplitPosition (triangleCutParameter f (p 0) (p 1))
          (triangleCutParameter f (p 0) (p 2)) i) := by
  let e := triangleAffineEquiv standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp
  fin_cases i
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 1).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 2).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    change affineCutPoint f (p 0) (p 1) =
      e (planePoint (triangleCutParameter f (p 0) (p 1)) 0)
    rw [show planePoint (triangleCutParameter f (p 0) (p 1)) 0 =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 1)
          (triangleCutParameter f (p 0) (p 1)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 1
        (triangleCutParameter f (p 0) (p 1))).symm
  · simp only [strictModelPosition, referenceSplitPosition]
    change affineCutPoint f (p 0) (p 2) =
      e (planePoint 0 (triangleCutParameter f (p 0) (p 2)))
    rw [show planePoint 0 (triangleCutParameter f (p 0) (p 2)) =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 2)
          (triangleCutParameter f (p 0) (p 2)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 2
        (triangleCutParameter f (p 0) (p 2))).symm

/-- The strict local model embedded into the shared refinement vertex type. -/
noncomputable def strictLocalEmbedding (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : Fin 5 ↪ M.RefinedVertex f where
  toFun := M.strictModelVertex f t h0 h1 h2
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.strictModelVertex_val f t h0 h1 h2,
      M.strictModelVertex_val f t h0 h1 h2,
      strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t) h0 h1 h2,
      strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t) h0 h1 h2]
      at hpos
    apply (referenceSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
      (affineCutPoint.parameter_pos f _ _ h0 h2)
      (affineCutPoint.parameter_lt_one f _ _ h0 h2))
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
      standardTrianglePosition_affineIndependent
        (M.orderedVertex_affineIndependent t)).injective hpos

/-- The strict local split, now using the coherent global vertex pool. -/
noncomputable def strictLocalMesh (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 1))
  let b := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
    standardTrianglePosition_affineIndependent (M.orderedVertex_affineIndependent t)
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.strictLocalEmbedding f t h0 h1 h2) (by
      intro i
      calc
        ((M.strictLocalEmbedding f t h0 h1 h2 i : M.RefinedVertex f) : Plane) =
            strictModelPosition (M.position ∘ M.orderedVertex t) f i :=
          M.strictModelVertex_val f t h0 h1 h2 i
        _ = e (referenceSplitPosition a b i) :=
          strictModelPosition_eq_affineReference f _ (M.orderedVertex_affineIndependent t)
            h0 h1 h2 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem strictLocalMesh_support (t : M.Triangle)
    (h0 : 0 < f (M.position (M.orderedVertex t 0)))
    (h1 : f (M.position (M.orderedVertex t 1)) < 0)
    (h2 : f (M.position (M.orderedVertex t 2)) < 0) :
    (M.strictLocalMesh f t h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  let a := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 1))
  let b := triangleCutParameter f (M.position (M.orderedVertex t 0))
    (M.position (M.orderedVertex t 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ M.orderedVertex t)
    standardTrianglePosition_affineIndependent (M.orderedVertex_affineIndependent t)
  rw [show M.strictLocalMesh f t h0 h1 h2 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.strictLocalEmbedding f t h0 h1 h2) (by
          intro i
          calc
            ((M.strictLocalEmbedding f t h0 h1 h2 i : M.RefinedVertex f) : Plane) =
                strictModelPosition (M.position ∘ M.orderedVertex t) f i :=
              M.strictModelVertex_val f t h0 h1 h2 i
            _ = e (referenceSplitPosition a b i) :=
              strictModelPosition_eq_affineReference f _
                (M.orderedVertex_affineIndependent t) h0 h1 h2 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  calc
    _ = (R.mapAffineEquiv e).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
      rw [TriangleMesh.mapAffineEquiv_support]
      rw [show R.toPlaneComplex.support =
          convexHull ℝ (Set.range standardTrianglePosition) from
        referenceSplitMesh_support a b _ _ _ _]
      change e '' convexHull ℝ (Set.range standardTrianglePosition) =
        convexHull ℝ (M.position '' (t.1 : Set M.Vertex))
      have hrange : Set.range (M.position ∘ M.orderedVertex t) =
          M.position '' (t.1 : Set M.Vertex) := by
        rw [Set.range_comp, M.range_orderedVertex t]
      rw [← hrange]
      exact triangleAffineEquiv_image_convexHull standardTrianglePosition
        (M.position ∘ M.orderedVertex t) standardTrianglePosition_affineIndependent
          (M.orderedVertex_affineIndependent t)

/-- The strict `-++` local split, obtained by applying the `+--` model to `-f` and identifying
the two coherent vertex pools. -/
noncomputable def strictNegativeLocalMesh (t : M.Triangle)
    (h0 : f (M.position (M.orderedVertex t 0)) < 0)
    (h1 : 0 < f (M.position (M.orderedVertex t 1)))
    (h2 : 0 < f (M.position (M.orderedVertex t 2))) : TriangleMesh :=
  let N := M.strictLocalMesh (-f) t (by simpa) (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem strictNegativeLocalMesh_support (t : M.Triangle)
    (h0 : f (M.position (M.orderedVertex t 0)) < 0)
    (h1 : 0 < f (M.position (M.orderedVertex t 1)))
    (h2 : 0 < f (M.position (M.orderedVertex t 2))) :
    (M.strictNegativeLocalMesh f t h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  rw [show M.strictNegativeLocalMesh f t h0 h1 h2 =
      (M.strictLocalMesh (-f) t (by simpa) (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  calc
    _ = (M.strictLocalMesh (-f) t (by simpa) (by simpa) (by simpa)).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) :=
      M.strictLocalMesh_support (-f) t (by simpa) (by simpa) (by simpa)

/-! The same strict model for an arbitrary ordering of three vertices. -/

/-- The `strictVertices` declaration. -/
noncomputable def strictVertices (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : Fin 5 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (v 0), M.oldRefinedVertex f (v 1), M.oldRefinedVertex f (v 2),
    M.cutRefinedVertex f (v 0) (v 1) (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩)),
    M.cutRefinedVertex f (v 0) (v 2) (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))]

theorem strictVertices_val (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 5) :
    (M.strictVertices f v h0 h1 h2 i : Plane) = strictModelPosition (M.position ∘ v) f i := by
  fin_cases i <;> rfl

/-- The `strictVerticesEmbedding` declaration. -/
noncomputable def strictVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : Fin 5 ↪ M.RefinedVertex f where
  toFun := M.strictVertices f v h0 h1 h2
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.strictVertices_val f v h0 h1 h2, M.strictVertices_val f v h0 h1 h2,
      strictModelPosition_eq_affineReference f _ hv h0 h1 h2,
      strictModelPosition_eq_affineReference f _ hv h0 h1 h2] at hpos
    apply referenceSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
      (affineCutPoint.parameter_pos f _ _ h0 h2)
      (affineCutPoint.parameter_lt_one f _ _ h0 h2)
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
      standardTrianglePosition_affineIndependent hv).injective hpos

/-- The `strictMeshFor` declaration. -/
noncomputable def strictMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) : TriangleMesh :=
  let a := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let b := triangleCutParameter f (M.position (v 0)) (M.position (v 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.strictVerticesEmbedding f v hv h0 h1 h2) (by
      intro i
      calc
        ((M.strictVerticesEmbedding f v hv h0 h1 h2 i : M.RefinedVertex f) : Plane) =
            strictModelPosition (M.position ∘ v) f i := M.strictVertices_val f v h0 h1 h2 i
        _ = e (referenceSplitPosition a b i) :=
          strictModelPosition_eq_affineReference f _ hv h0 h1 h2 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem strictMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    (M.strictMeshFor f v hv h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  let a := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let b := triangleCutParameter f (M.position (v 0)) (M.position (v 2))
  let R := referenceSplitMesh a b
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    (affineCutPoint.parameter_pos f _ _ h0 h2)
    (affineCutPoint.parameter_lt_one f _ _ h0 h2)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  rw [show M.strictMeshFor f v hv h0 h1 h2 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.strictVerticesEmbedding f v hv h0 h1 h2) (by
          intro i
          calc
            ((M.strictVerticesEmbedding f v hv h0 h1 h2 i : M.RefinedVertex f) : Plane) =
                strictModelPosition (M.position ∘ v) f i :=
              M.strictVertices_val f v h0 h1 h2 i
            _ = e (referenceSplitPosition a b i) :=
              strictModelPosition_eq_affineReference f _ hv h0 h1 h2 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  calc
    _ = (R.mapAffineEquiv e).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (Set.range (M.position ∘ v)) := by
      rw [TriangleMesh.mapAffineEquiv_support]
      rw [show R.toPlaneComplex.support =
          convexHull ℝ (Set.range standardTrianglePosition) from
        referenceSplitMesh_support a b _ _ _ _]
      change e '' convexHull ℝ (Set.range standardTrianglePosition) =
        convexHull ℝ (Set.range (M.position ∘ v))
      exact triangleAffineEquiv_image_convexHull standardTrianglePosition (M.position ∘ v)
        standardTrianglePosition_affineIndependent hv

/-- The `strictNegativeMeshFor` declaration. -/
noncomputable def strictNegativeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) : TriangleMesh :=
  let N := M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem strictNegativeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) :
    (M.strictNegativeMeshFor f v hv h0 h1 h2).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.strictNegativeMeshFor f v hv h0 h1 h2 =
      (M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  calc
    _ = (M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (Set.range (M.position ∘ v)) :=
      M.strictMeshFor_support (-f) v hv (by simpa) (by simpa) (by simpa)

/-! The two-triangle model when vertex `2` lies on the cutting line. -/

/-- The `edgeModelPosition` declaration. -/
noncomputable def edgeModelPosition (p : Fin 3 → Plane) (f : Plane →ᵃ[ℝ] ℝ) : Fin 4 → Plane :=
  ![p 0, p 1, p 2, affineCutPoint f (p 0) (p 1)]

theorem edgeModelPosition_eq_affineReference (p : Fin 3 → Plane)
    (hp : AffineIndependent ℝ p) (_ : 0 < f (p 0)) (_ : f (p 1) < 0)
    (i : Fin 4) :
    edgeModelPosition p f i =
      triangleAffineEquiv standardTrianglePosition p standardTrianglePosition_affineIndependent hp
        (referenceEdgeSplitPosition (triangleCutParameter f (p 0) (p 1)) i) := by
  let e := triangleAffineEquiv standardTrianglePosition p
    standardTrianglePosition_affineIndependent hp
  fin_cases i
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 1).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    exact (triangleAffineEquiv_apply standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 2).symm
  · simp only [edgeModelPosition, referenceEdgeSplitPosition]
    change affineCutPoint f (p 0) (p 1) =
      e (planePoint (triangleCutParameter f (p 0) (p 1)) 0)
    rw [show planePoint (triangleCutParameter f (p 0) (p 1)) 0 =
        AffineMap.lineMap (standardTrianglePosition 0) (standardTrianglePosition 1)
          (triangleCutParameter f (p 0) (p 1)) by
      ext j; fin_cases j <;> simp [standardTrianglePosition, planePoint,
        AffineMap.lineMap_apply_module]]
    exact (triangleAffineEquiv_apply_lineMap standardTrianglePosition p
      standardTrianglePosition_affineIndependent hp 0 1
        (triangleCutParameter f (p 0) (p 1))).symm

/-- The `edgeVertices` declaration. -/
noncomputable def edgeVertices (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Fin 4 → M.RefinedVertex f :=
  ![M.oldRefinedVertex f (v 0), M.oldRefinedVertex f (v 1), M.oldRefinedVertex f (v 2),
    M.cutRefinedVertex f (v 0) (v 1) (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))]

theorem edgeVertices_val (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) (i : Fin 4) :
    (M.edgeVertices f v h0 h1 i : Plane) = edgeModelPosition (M.position ∘ v) f i := by
  fin_cases i <;> rfl

/-- The `edgeVerticesEmbedding` declaration. -/
noncomputable def edgeVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    Fin 4 ↪ M.RefinedVertex f where
  toFun := M.edgeVertices f v h0 h1
  inj' := by
    intro i j hij
    have hpos := congrArg Subtype.val hij
    rw [M.edgeVertices_val f v h0 h1, M.edgeVertices_val f v h0 h1,
      edgeModelPosition_eq_affineReference f _ hv h0 h1,
      edgeModelPosition_eq_affineReference f _ hv h0 h1] at hpos
    apply referenceEdgeSplitPosition_injective
      (affineCutPoint.parameter_pos f _ _ h0 h1)
      (affineCutPoint.parameter_lt_one f _ _ h0 h1)
    exact (triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
      standardTrianglePosition_affineIndependent hv).injective hpos

/-- The `edgeMeshFor` declaration. -/
noncomputable def edgeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) : TriangleMesh :=
  let c := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let R := referenceEdgeSplitMesh c
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.edgeVerticesEmbedding f v hv h0 h1) (by
      intro i
      calc
        ((M.edgeVerticesEmbedding f v hv h0 h1 i : M.RefinedVertex f) : Plane) =
            edgeModelPosition (M.position ∘ v) f i := M.edgeVertices_val f v h0 h1 i
        _ = e (referenceEdgeSplitPosition c i) :=
          edgeModelPosition_eq_affineReference f _ hv h0 h1 i
        _ = (R.mapAffineEquiv e).position i := rfl)

theorem edgeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    (M.edgeMeshFor f v hv h0 h1).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  let c := triangleCutParameter f (M.position (v 0)) (M.position (v 1))
  let R := referenceEdgeSplitMesh c
    (affineCutPoint.parameter_pos f _ _ h0 h1)
    (affineCutPoint.parameter_lt_one f _ _ h0 h1)
  let e := triangleAffineEquiv standardTrianglePosition (M.position ∘ v)
    standardTrianglePosition_affineIndependent hv
  rw [show M.edgeMeshFor f v hv h0 h1 =
      (R.mapAffineEquiv e).reindex ((↑) : M.RefinedVertex f → Plane)
        Subtype.val_injective (M.edgeVerticesEmbedding f v hv h0 h1) (by
          intro i
          calc
            ((M.edgeVerticesEmbedding f v hv h0 h1 i : M.RefinedVertex f) : Plane) =
                edgeModelPosition (M.position ∘ v) f i := M.edgeVertices_val f v h0 h1 i
            _ = e (referenceEdgeSplitPosition c i) :=
              edgeModelPosition_eq_affineReference f _ hv h0 h1 i
            _ = (R.mapAffineEquiv e).position i := rfl) by rfl]
  calc
    _ = (R.mapAffineEquiv e).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (Set.range (M.position ∘ v)) := by
      rw [TriangleMesh.mapAffineEquiv_support]
      rw [show R.toPlaneComplex.support =
          convexHull ℝ (Set.range standardTrianglePosition) from
        referenceEdgeSplitMesh_support c _ _]
      change e '' convexHull ℝ (Set.range standardTrianglePosition) =
        convexHull ℝ (Set.range (M.position ∘ v))
      exact triangleAffineEquiv_image_convexHull standardTrianglePosition (M.position ∘ v)
        standardTrianglePosition_affineIndependent hv

/-- The `edgeNegativeMeshFor` declaration. -/
noncomputable def edgeNegativeMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1))) : TriangleMesh :=
  let N := M.edgeMeshFor (-f) v hv (by simpa) (by simpa)
  N.reindex ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
    (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl)

theorem edgeNegativeMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1))) :
    (M.edgeNegativeMeshFor f v hv h0 h1).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.edgeNegativeMeshFor f v hv h0 h1 =
      (M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
        (M.refinedVertexNegEquiv f).toEmbedding (fun _ => rfl) by rfl]
  calc
    _ = (M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (Set.range (M.position ∘ v)) :=
      M.edgeMeshFor_support (-f) v hv (by simpa) (by simpa)

/-! ## Choosing the local model from the signs -/

theorem orderedVertex_perm_affineIndependent (t : M.Triangle) (σ : Equiv.Perm (Fin 3)) :
    AffineIndependent ℝ (M.position ∘ M.orderedVertex t ∘ σ) := by
  exact (M.orderedVertex_affineIndependent t).comp_embedding σ.toEmbedding

theorem range_orderedVertex_perm (t : M.Triangle) (σ : Equiv.Perm (Fin 3)) :
    Set.range (M.position ∘ M.orderedVertex t ∘ σ) =
      M.position '' (t.1 : Set M.Vertex) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨M.orderedVertex t (σ i), ?_, rfl⟩
    have hmem : M.orderedVertex t (σ i) ∈ Set.range (M.orderedVertex t) :=
      Set.mem_range_self (σ i)
    rw [M.range_orderedVertex t] at hmem
    exact hmem
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ Set.range (M.orderedVertex t) := by
      rw [M.range_orderedVertex t]
      exact hv
    obtain ⟨j, rfl⟩ := hv'
    exact ⟨σ.symm j, by simp⟩

/-- A vertex ordering with one positive value followed by two negative values. -/
structure PositiveStrictOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  positive : 0 < f (M.position (M.orderedVertex t (perm 0)))
  negative_one : f (M.position (M.orderedVertex t (perm 1))) < 0
  negative_two : f (M.position (M.orderedVertex t (perm 2))) < 0

/-- A vertex ordering with one negative value followed by two positive values. -/
structure NegativeStrictOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  negative : f (M.position (M.orderedVertex t (perm 0))) < 0
  positive_one : 0 < f (M.position (M.orderedVertex t (perm 1)))
  positive_two : 0 < f (M.position (M.orderedVertex t (perm 2)))

/-- A vertex ordering with one positive, one negative, and one zero value. -/
structure PositiveEdgeOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  positive : 0 < f (M.position (M.orderedVertex t (perm 0)))
  negative : f (M.position (M.orderedVertex t (perm 1))) < 0
  zero : f (M.position (M.orderedVertex t (perm 2))) = 0

/-- A vertex ordering with one negative, one positive, and one zero value. -/
structure NegativeEdgeOrdering (t : M.Triangle) where
  /-- The `perm` declaration. -/
  perm : Equiv.Perm (Fin 3)
  negative : f (M.position (M.orderedVertex t (perm 0))) < 0
  positive : 0 < f (M.position (M.orderedVertex t (perm 1)))
  zero : f (M.position (M.orderedVertex t (perm 2))) = 0

/-- The `oldVerticesEmbedding` declaration. -/
noncomputable def oldVerticesEmbedding (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) : Fin 3 ↪ M.RefinedVertex f where
  toFun i := M.oldRefinedVertex f (v i)
  inj' := by
    intro i j hij
    apply hv.injective
    exact congrArg Subtype.val hij

/-- The `unchangedMeshFor` declaration. -/
noncomputable def unchangedMeshFor (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) : TriangleMesh :=
  (TriangleMesh.single (M.position ∘ v) hv).reindex
    ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
      (M.oldVerticesEmbedding f v hv) (fun _ => rfl)

theorem unchangedMeshFor_support (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v)) :
    (M.unchangedMeshFor f v hv).toPlaneComplex.support =
      convexHull ℝ (Set.range (M.position ∘ v)) := by
  rw [show M.unchangedMeshFor f v hv =
      (TriangleMesh.single (M.position ∘ v) hv).reindex
        ((↑) : M.RefinedVertex f → Plane) Subtype.val_injective
          (M.oldVerticesEmbedding f v hv) (fun _ => rfl) by rfl]
  calc
    _ = (TriangleMesh.single (M.position ∘ v) hv).toPlaneComplex.support := by
      apply TriangleMesh.reindex_support
    _ = convexHull ℝ (Set.range (M.position ∘ v)) := TriangleMesh.single_support _ _

/-- The canonical local refinement mesh for one old triangle. -/
noncomputable def localRefinementMesh (t : M.Triangle) : TriangleMesh := by
  classical
  exact if hp : Nonempty (M.PositiveStrictOrdering f t) then
    let o := Classical.choice hp
    M.strictMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two
  else if hn : Nonempty (M.NegativeStrictOrdering f t) then
    let o := Classical.choice hn
    M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two
  else if hep : Nonempty (M.PositiveEdgeOrdering f t) then
    let o := Classical.choice hep
    M.edgeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative
  else if hen : Nonempty (M.NegativeEdgeOrdering f t) then
    let o := Classical.choice hen
    M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive
  else
    M.unchangedMeshFor f (M.orderedVertex t) (M.orderedVertex_affineIndependent t)

theorem localRefinementMesh_support (t : M.Triangle) :
    (M.localRefinementMesh f t).toPlaneComplex.support =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  classical
  unfold localRefinementMesh
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    rw [M.strictMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hn
    rw [M.strictNegativeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hep
    rw [M.edgeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · let o := Classical.choice hen
    rw [M.edgeNegativeMeshFor_support]
    exact congrArg (convexHull ℝ) (M.range_orderedVertex_perm t o.perm)
  · rw [M.unchangedMeshFor_support]
    congr 1
    rw [Set.range_comp, M.range_orderedVertex t]

/-- Every maximal triangle lies wholly on one closed side of the cutting line. -/
def IsMonochromatic (N : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s ∈ N.triangles,
    (∀ v ∈ s, 0 ≤ f (N.position v)) ∨ (∀ v ∈ s, f (N.position v) ≤ 0)

theorem IsMonochromatic.of_neg {N : TriangleMesh}
    (hN : N.IsMonochromatic (-f)) : N.IsMonochromatic f := by
  intro s hs
  rcases hN s hs with h | h
  · right
    intro v hv
    simpa using h v hv
  · left
    intro v hv
    simpa using h v hv

theorem IsMonochromatic.reindex {N : TriangleMesh} {V' : Type} [Fintype V']
    [DecidableEq V'] (position' : V' → Plane) (hposition_injective : Function.Injective position')
    (e : N.Vertex ↪ V') (hposition : ∀ v, position' (e v) = N.position v)
    (g : Plane →ᵃ[ℝ] ℝ) (hN : N.IsMonochromatic g) :
    (N.reindex position' hposition_injective e hposition).IsMonochromatic g := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  rcases hN t ht with h | h
  · left
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    change 0 ≤ g (position' (e w))
    rw [hposition]
    exact h w hw
  · right
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    change g (position' (e w)) ≤ 0
    rw [hposition]
    exact h w hw

theorem strictVertices_f (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) (i : Fin 5) :
    f (M.strictVertices f v h0 h1 h2 i : Plane) =
      ![f (M.position (v 0)), f (M.position (v 1)), f (M.position (v 2)), 0, 0] i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 2)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h2⟩))

theorem edgeVertices_f (v : Fin 3 → M.Vertex)
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (hzero : f (M.position (v 2)) = 0) (i : Fin 4) :
    f (M.edgeVertices f v h0 h1 i : Plane) =
      ![f (M.position (v 0)), f (M.position (v 1)), 0, 0] i := by
  fin_cases i
  · rfl
  · rfl
  · exact hzero
  · exact M.pairCutPosition_apply_eq_zero f (v 0) (v 1)
      (mul_neg_iff.mpr (Or.inl ⟨h0, h1⟩))

/-- Monochromaticity stated directly for triangles in the shared refined vertex pool. -/
def RefinedTrianglesMonochromatic (T : Finset (Finset (M.RefinedVertex f))) : Prop :=
  ∀ s ∈ T,
    (∀ x ∈ s, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ s, f (x : Plane) ≤ 0)

theorem strictTriangles_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    M.RefinedTrianglesMonochromatic f
      (referenceSplitTriangles.image fun t =>
        t.map (M.strictVerticesEmbedding f v hv h0 h1 h2)) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr' : r = {0, 3, 4} ∨ r = {1, 2, 3} ∨ r = {2, 3, 4} := by
    simpa only [referenceSplitTriangles, Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hr' with rfl | rfl | rfl
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0.le
    · change 0 ≤ f (M.strictVertices f v h0 h1 h2 3 : Plane)
      rw [M.strictVertices_f f v h0 h1 h2]
      change 0 ≤ (0 : ℝ)
      norm_num
    · change 0 ≤ f (M.strictVertices f v h0 h1 h2 4 : Plane)
      rw [M.strictVertices_f f v h0 h1 h2]
      change 0 ≤ (0 : ℝ)
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h1.le
    · exact h2.le
    · change f (M.strictVertices f v h0 h1 h2 3 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h2.le
    · change f (M.strictVertices f v h0 h1 h2 3 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num
    · change f (M.strictVertices f v h0 h1 h2 4 : Plane) ≤ 0
      rw [M.strictVertices_f f v h0 h1 h2]
      change (0 : ℝ) ≤ 0
      norm_num

theorem edgeTriangles_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (hzero : f (M.position (v 2)) = 0) :
    M.RefinedTrianglesMonochromatic f
      (referenceEdgeSplitTriangles.image fun t =>
        t.map (M.edgeVerticesEmbedding f v hv h0 h1)) := by
  intro s hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr' : r = {0, 2, 3} ∨ r = {1, 2, 3} := by
    simpa only [referenceEdgeSplitTriangles, Finset.mem_insert,
      Finset.mem_singleton, or_false] using hr
  rcases hr' with rfl | rfl
  · left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h0.le
    · change 0 ≤ f (M.edgeVertices f v h0 h1 2 : Plane)
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change 0 ≤ (0 : ℝ)
      norm_num
    · change 0 ≤ f (M.edgeVertices f v h0 h1 3 : Plane)
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change 0 ≤ (0 : ℝ)
      norm_num
  · right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h1.le
    · change f (M.edgeVertices f v h0 h1 2 : Plane) ≤ 0
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change (0 : ℝ) ≤ 0
      norm_num
    · change f (M.edgeVertices f v h0 h1 3 : Plane) ≤ 0
      rw [M.edgeVertices_f f v h0 h1 hzero]
      change (0 : ℝ) ≤ 0
      norm_num

/-- The abstract three-triangle combinatorial pattern of a strict cut. -/
def strictPatternTriangles {V : Type*} [DecidableEq V] (z : Fin 5 → V) :
    Finset (Finset V) :=
  {{z 0, z 3, z 4}, {z 1, z 2, z 3}, {z 2, z 3, z 4}}

/-- The abstract two-triangle combinatorial pattern of a cut through vertex `2`. -/
def edgePatternTriangles {V : Type*} [DecidableEq V] (z : Fin 4 → V) :
    Finset (Finset V) :=
  {{z 0, z 2, z 3}, {z 1, z 2, z 3}}

theorem exists_index_of_mem_strictPattern {V : Type*} [DecidableEq V]
    (z : Fin 5 → V) {s : Finset V} (hs : s ∈ strictPatternTriangles z)
    {x : V} (hx : x ∈ s) : ∃ i, x = z i := by
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

theorem exists_index_of_mem_edgePattern {V : Type*} [DecidableEq V]
    (z : Fin 4 → V) {s : Finset V} (hs : s ∈ edgePatternTriangles z)
    {x : V} (hx : x ∈ s) : ∃ i, x = z i := by
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem strictMeshFor_triangles (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0)
    (h2 : f (M.position (v 2)) < 0) :
    (M.strictMeshFor f v hv h0 h1 h2).triangles =
      strictPatternTriangles (M.strictVertices f v h0 h1 h2) := by
  ext s
  simp [strictMeshFor, strictPatternTriangles, referenceSplitMesh,
    referenceSplitTriangles, TriangleMesh.reindex, TriangleMesh.mapAffineEquiv,
    strictVerticesEmbedding]
  rfl

theorem edgeMeshFor_triangles (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : 0 < f (M.position (v 0))) (h1 : f (M.position (v 1)) < 0) :
    (M.edgeMeshFor f v hv h0 h1).triangles =
      edgePatternTriangles (M.edgeVertices f v h0 h1) := by
  simp [edgeMeshFor, edgePatternTriangles, referenceEdgeSplitMesh,
    referenceEdgeSplitTriangles, TriangleMesh.reindex, TriangleMesh.mapAffineEquiv,
    edgeVerticesEmbedding]
  rfl

theorem strictNegativeMeshFor_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : 0 < f (M.position (v 2))) :
    M.RefinedTrianglesMonochromatic f
      (M.strictNegativeMeshFor f v hv h0 h1 h2).triangles := by
  intro s hs
  unfold strictNegativeMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hm := M.strictTriangles_monochromatic (-f) v hv (by simpa) (by simpa) (by simpa) r
  have hr' : r ∈ referenceSplitTriangles.image (fun t ↦
      t.map (M.strictVerticesEmbedding (-f) v hv (by simpa) (by simpa) (by simpa))) := hr
  rcases hm hr' with hm | hm
  · right
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change f ((M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).position y) ≤ 0
    simpa only [strictMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonneg] using hm y hy
  · left
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change 0 ≤ f ((M.strictMeshFor (-f) v hv (by simpa) (by simpa) (by simpa)).position y)
    simpa only [strictMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonpos] using hm y hy

theorem edgeNegativeMeshFor_monochromatic (v : Fin 3 → M.Vertex)
    (hv : AffineIndependent ℝ (M.position ∘ v))
    (h0 : f (M.position (v 0)) < 0) (h1 : 0 < f (M.position (v 1)))
    (h2 : f (M.position (v 2)) = 0) :
    M.RefinedTrianglesMonochromatic f
      (M.edgeNegativeMeshFor f v hv h0 h1).triangles := by
  intro s hs
  unfold edgeNegativeMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hm := M.edgeTriangles_monochromatic (-f) v hv (by simpa) (by simpa) (by simpa) r
  have hr' : r ∈ referenceEdgeSplitTriangles.image (fun t ↦
      t.map (M.edgeVerticesEmbedding (-f) v hv (by simpa) (by simpa))) := hr
  rcases hm hr' with hm | hm
  · right
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change f ((M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).position y) ≤ 0
    simpa only [edgeMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonneg] using hm y hy
  · left
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    change 0 ≤ f ((M.edgeMeshFor (-f) v hv (by simpa) (by simpa)).position y)
    simpa only [edgeMeshFor, TriangleMesh.reindex, AffineMap.coe_neg, Pi.neg_apply,
      neg_nonpos] using hm y hy

theorem strictPattern_monochromatic_positive (z : Fin 5 → M.RefinedVertex f)
    (h0 : 0 ≤ f (z 0 : Plane)) (h1 : f (z 1 : Plane) ≤ 0)
    (h2 : f (z 2 : Plane) ≤ 0) (h3 : f (z 3 : Plane) = 0)
    (h4 : f (z 4 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (strictPatternTriangles z) := by
  intro s hs
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem strictPattern_monochromatic_negative (z : Fin 5 → M.RefinedVertex f)
    (h0 : f (z 0 : Plane) ≤ 0) (h1 : 0 ≤ f (z 1 : Plane))
    (h2 : 0 ≤ f (z 2 : Plane)) (h3 : f (z 3 : Plane) = 0)
    (h4 : f (z 4 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (strictPatternTriangles z) := by
  intro s hs
  simp only [strictPatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem edgePattern_monochromatic_positive (z : Fin 4 → M.RefinedVertex f)
    (h0 : 0 ≤ f (z 0 : Plane)) (h1 : f (z 1 : Plane) ≤ 0)
    (h2 : f (z 2 : Plane) = 0) (h3 : f (z 3 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (edgePatternTriangles z) := by
  intro s hs
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

theorem edgePattern_monochromatic_negative (z : Fin 4 → M.RefinedVertex f)
    (h0 : f (z 0 : Plane) ≤ 0) (h1 : 0 ≤ f (z 1 : Plane))
    (h2 : f (z 2 : Plane) = 0) (h3 : f (z 3 : Plane) = 0) :
    M.RefinedTrianglesMonochromatic f (edgePatternTriangles z) := by
  intro s hs
  simp only [edgePatternTriangles, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · right
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith
  · left
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

private theorem same_closed_side_of_pairwise_products {a b c : ℝ}
    (hab : 0 ≤ a * b) (hac : 0 ≤ a * c) (hbc : 0 ≤ b * c) :
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · by_cases hc : 0 ≤ c
      · exact Or.inl ⟨ha, hb, hc⟩
      · have hc' : c < 0 := lt_of_not_ge hc
        have ha0 : a = 0 := by nlinarith [hac]
        have hb0 : b = 0 := by nlinarith [hbc]
        exact Or.inr ⟨ha0.le, hb0.le, hc'.le⟩
    · have hb' : b < 0 := lt_of_not_ge hb
      have ha0 : a = 0 := by nlinarith [hab]
      have hc : c ≤ 0 := by
        by_contra hc
        have hc' : 0 < c := lt_of_not_ge hc
        nlinarith [hbc]
      exact Or.inr ⟨ha0.le, hb'.le, hc⟩
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb : b ≤ 0 := by
      by_contra hb
      have hb' : 0 < b := lt_of_not_ge hb
      nlinarith [hab]
    have hc : c ≤ 0 := by
      by_contra hc
      have hc' : 0 < c := lt_of_not_ge hc
      nlinarith [hac]
    exact Or.inr ⟨ha'.le, hb, hc⟩

private theorem signs_of_two_crossings {a b c : ℝ}
    (hab : a * b < 0) (hac : a * c < 0) :
    (0 < a ∧ b < 0 ∧ c < 0) ∨ (a < 0 ∧ 0 < b ∧ 0 < c) := by
  rcases mul_neg_iff.mp hab with hab | hab
  · rcases mul_neg_iff.mp hac with hac | hac
    · exact Or.inl ⟨hab.1, hab.2, hac.2⟩
    · linarith
  · rcases mul_neg_iff.mp hac with hac | hac
    · linarith
    · exact Or.inr ⟨hab.1, hab.2, hac.2⟩

private theorem third_eq_zero_of_one_crossing {a b c : ℝ}
    (hab : a * b < 0) (hac : ¬ a * c < 0) (hbc : ¬ b * c < 0) : c = 0 := by
  rcases mul_neg_iff.mp hab with hab | hab
  · by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · exact hac (mul_neg_of_pos_of_neg hab.1 hc)
    · exact hbc (mul_neg_of_neg_of_pos hab.2 hc)
  · by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · exact hbc (mul_neg_of_pos_of_neg hab.2 hc)
    · exact hac (mul_neg_of_neg_of_pos hab.1 hc)

/-- The old vertex numbered `i` in a triangle, regarded as a refined vertex. -/
noncomputable def localOldVertex (t : M.Triangle) (i : Fin 3) : M.RefinedVertex f :=
  M.oldRefinedVertex f (M.orderedVertex t i)

/-- The cut vertex on the pair of locally numbered vertices `i,j`. -/
noncomputable def localCutVertex (t : M.Triangle) (i j : Fin 3)
    (hij : f (M.position (M.orderedVertex t i)) *
      f (M.position (M.orderedVertex t j)) < 0) : M.RefinedVertex f :=
  M.cutRefinedVertex f (M.orderedVertex t i) (M.orderedVertex t j) hij

@[simp] theorem localOldVertex_val (t : M.Triangle) (i : Fin 3) :
    (M.localOldVertex f t i : Plane) = M.position (M.orderedVertex t i) := rfl

theorem localCutVertex_apply_eq_zero (t : M.Triangle) (i j : Fin 3)
    (hij : f (M.position (M.orderedVertex t i)) *
      f (M.position (M.orderedVertex t j)) < 0) :
    f (M.localCutVertex f t i j hij : Plane) = 0 :=
  M.pairCutPosition_apply_eq_zero f _ _ hij

private theorem pairwise_nonnegative_of_no_orderings (t : M.Triangle)
    (hp : ¬ Nonempty (M.PositiveStrictOrdering f t))
    (hn : ¬ Nonempty (M.NegativeStrictOrdering f t))
    (hep : ¬ Nonempty (M.PositiveEdgeOrdering f t))
    (hen : ¬ Nonempty (M.NegativeEdgeOrdering f t)) :
    0 ≤ f (M.position (M.orderedVertex t 0)) * f (M.position (M.orderedVertex t 1)) ∧
    0 ≤ f (M.position (M.orderedVertex t 0)) * f (M.position (M.orderedVertex t 2)) ∧
    0 ≤ f (M.position (M.orderedVertex t 1)) * f (M.position (M.orderedVertex t 2)) := by
  let a := f (M.position (M.orderedVertex t 0))
  let b := f (M.position (M.orderedVertex t 1))
  let c := f (M.position (M.orderedVertex t 2))
  have h01 : ¬ a * b < 0 := by
    intro hab
    rcases mul_neg_iff.mp hab with hab | hab
    · rcases lt_trichotomy c 0 with hc | hc | hc
      · apply hp
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hep
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hn
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hab.2
        · simpa [a, Equiv.swap_apply_def] using hab.1
        · simpa [c, Equiv.swap_apply_def] using hc
    · rcases lt_trichotomy c 0 with hc | hc | hc
      · apply hp
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hab.2
        · simpa [a, Equiv.swap_apply_def] using hab.1
        · simpa [c, Equiv.swap_apply_def] using hc
      · apply hen
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
      · apply hn
        exact ⟨⟨Equiv.refl _, hab.1, hab.2, hc⟩⟩
  have h02 : ¬ a * c < 0 := by
    intro hac
    rcases mul_neg_iff.mp hac with hac | hac
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · apply hp
        exact ⟨⟨Equiv.refl _, hac.1, hb, hac.2⟩⟩
      · apply hep
        refine ⟨⟨Equiv.swap 1 2, ?_, ?_, ?_⟩⟩
        · simpa [a, Equiv.swap_apply_def] using hac.1
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
      · apply hn
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
        · simpa [a, Equiv.swap_apply_def] using hac.1
    · rcases lt_trichotomy b 0 with hb | hb | hb
      · apply hp
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
        · simpa [a, Equiv.swap_apply_def] using hac.1
      · apply hen
        refine ⟨⟨Equiv.swap 1 2, ?_, ?_, ?_⟩⟩
        · simpa [a, Equiv.swap_apply_def] using hac.1
        · simpa [c, Equiv.swap_apply_def] using hac.2
        · simpa [b, Equiv.swap_apply_def] using hb
      · apply hn
        exact ⟨⟨Equiv.refl _, hac.1, hb, hac.2⟩⟩
  have h12 : ¬ b * c < 0 := by
    intro hbc
    rcases mul_neg_iff.mp hbc with hbc | hbc
    · rcases lt_trichotomy a 0 with ha | ha | ha
      · apply hp
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
        · simpa [c, Equiv.swap_apply_def] using hbc.2
      · apply hen
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hn
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
    · rcases lt_trichotomy a 0 with ha | ha | ha
      · apply hp
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hep
        refine ⟨⟨Equiv.swap 0 2, ?_, ?_, ?_⟩⟩
        · simpa [c, Equiv.swap_apply_def] using hbc.2
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
      · apply hn
        refine ⟨⟨Equiv.swap 0 1, ?_, ?_, ?_⟩⟩
        · simpa [b, Equiv.swap_apply_def] using hbc.1
        · simpa [a, Equiv.swap_apply_def] using ha
        · simpa [c, Equiv.swap_apply_def] using hbc.2
  exact ⟨not_lt.mp h01, not_lt.mp h02, not_lt.mp h12⟩

/-- Canonical local triangulation after cutting one old triangle by `f`.  There are three
triangles when one vertex is strictly separated from the other two, two triangles when the line
passes through one vertex and cuts the opposite edge, and the old triangle when the line already
meets it in a face. -/
noncomputable def localRefinementTriangles (t : M.Triangle) :
    Finset (Finset (M.RefinedVertex f)) := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  let o : Fin 3 → M.RefinedVertex f := M.localOldVertex f t
  if h01 : f (p 0) * f (p 1) < 0 then
    let q01 := M.localCutVertex f t 0 1 h01
    if h02 : f (p 0) * f (p 2) < 0 then
      let q02 := M.localCutVertex f t 0 2 h02
      exact strictPatternTriangles ![o 0, o 1, o 2, q01, q02]
    else if h12 : f (p 1) * f (p 2) < 0 then
      let q12 := M.localCutVertex f t 1 2 h12
      exact strictPatternTriangles ![o 1, o 0, o 2, q01, q12]
    else
      exact edgePatternTriangles ![o 0, o 1, o 2, q01]
  else if h02 : f (p 0) * f (p 2) < 0 then
    let q02 := M.localCutVertex f t 0 2 h02
    if h12 : f (p 1) * f (p 2) < 0 then
      let q12 := M.localCutVertex f t 1 2 h12
      exact strictPatternTriangles ![o 2, o 0, o 1, q02, q12]
    else
      exact edgePatternTriangles ![o 0, o 2, o 1, q02]
  else if h12 : f (p 1) * f (p 2) < 0 then
    let q12 := M.localCutVertex f t 1 2 h12
    exact edgePatternTriangles ![o 1, o 2, o 0, q12]
  else
    exact {{o 0, o 1, o 2}}

/-- Cutting one old triangle by an affine line produces triangles contained in the two closed
half-planes. -/
theorem localRefinementTriangles_monochromatic (t : M.Triangle) :
    M.RefinedTrianglesMonochromatic f (M.localRefinementTriangles f t) := by
  classical
  unfold localRefinementTriangles
  dsimp only
  split_ifs with h01 h02 h12 h02' h12' h12''
  · rcases signs_of_two_crossings h01 h02 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02
  · have h10 : f (M.position (M.orderedVertex t 1)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h01
    rcases signs_of_two_crossings h10 h12 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12
  · have hz := third_eq_zero_of_one_crossing h01 h02 h12
    rcases mul_neg_iff.mp h01 with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 1 h01
  · have h20 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h02'
    have h21 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12'
    rcases signs_of_two_crossings h20 h21 with h | h
    · apply M.strictPattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12'
    · apply M.strictPattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.1.le
      · simpa using h.2.2.le
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12'
  · have h21 : ¬ f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12'
    have hz := third_eq_zero_of_one_crossing h02' h01 h21
    rcases mul_neg_iff.mp h02' with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 0 2 h02'
  · have h21 : f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 1)) < 0 := by simpa [mul_comm] using h12''
    have h10 : ¬ f (M.position (M.orderedVertex t 1)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h01
    have h20 : ¬ f (M.position (M.orderedVertex t 2)) *
        f (M.position (M.orderedVertex t 0)) < 0 := by simpa [mul_comm] using h02'
    have hz := third_eq_zero_of_one_crossing h12'' h10 h20
    rcases mul_neg_iff.mp h12'' with h | h
    · apply M.edgePattern_monochromatic_positive
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12''
    · apply M.edgePattern_monochromatic_negative
      · simpa using h.1.le
      · simpa using h.2.le
      · simpa using hz
      · simpa using M.localCutVertex_apply_eq_zero f t 1 2 h12''
  · have hsign := same_closed_side_of_pairwise_products
        (not_lt.mp h01) (not_lt.mp h02') (not_lt.mp h12'')
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst s
    rcases hsign with h | h
    · left
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2
    · right
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simpa using h.1
      · simpa using h.2.1
      · simpa using h.2.2

/-- View a mesh whose vertex type is identified with the refined vertex pool as a family of
triangles on that fixed pool. -/
noncomputable def refinedMeshTriangles (N : TriangleMesh)
    (h : N.Vertex = M.RefinedVertex f) : Finset (Finset (M.RefinedVertex f)) :=
  h ▸ N.triangles

/-- The maximal triangles selected by the certified local model, exposed on the fixed shared
vertex pool. -/
noncomputable def localMeshTriangles (t : M.Triangle) :
    Finset (Finset (M.RefinedVertex f)) := by
  classical
  exact if hp : Nonempty (M.PositiveStrictOrdering f t) then
    let o := Classical.choice hp
    M.refinedMeshTriangles f (M.strictMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two) rfl
  else if hn : Nonempty (M.NegativeStrictOrdering f t) then
    let o := Classical.choice hn
    M.refinedMeshTriangles f (M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two) rfl
  else if hep : Nonempty (M.PositiveEdgeOrdering f t) then
    let o := Classical.choice hep
    M.refinedMeshTriangles f (M.edgeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative) rfl
  else if hen : Nonempty (M.NegativeEdgeOrdering f t) then
    let o := Classical.choice hen
    M.refinedMeshTriangles f (M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive) rfl
  else
    M.refinedMeshTriangles f (M.unchangedMeshFor f (M.orderedVertex t)
      (M.orderedVertex_affineIndependent t)) rfl

theorem card_of_mem_localMeshTriangles (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) : s.card = 3 := by
  classical
  unfold localMeshTriangles at hs
  split_ifs at hs with hp hn hep hen
  · exact (M.strictMeshFor f _ _ _ _ _).card_triangle s hs
  · exact (M.strictNegativeMeshFor f _ _ _ _ _).card_triangle s hs
  · exact (M.edgeMeshFor f _ _ _ _).card_triangle s hs
  · exact (M.edgeNegativeMeshFor f _ _ _ _).card_triangle s hs
  · exact (M.unchangedMeshFor f _ _).card_triangle s hs

theorem affineIndependent_of_mem_localMeshTriangles (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    AffineIndependent ℝ fun v : s => (v.1 : Plane) := by
  classical
  unfold localMeshTriangles at hs
  split_ifs at hs with hp hn hep hen
  · exact (M.strictMeshFor f _ _ _ _ _).affineIndependent_triangle s hs
  · exact (M.strictNegativeMeshFor f _ _ _ _ _).affineIndependent_triangle s hs
  · exact (M.edgeMeshFor f _ _ _ _).affineIndependent_triangle s hs
  · exact (M.edgeNegativeMeshFor f _ _ _ _).affineIndependent_triangle s hs
  · exact (M.unchangedMeshFor f _ _).affineIndependent_triangle s hs

theorem localMeshTriangles_monochromatic (t : M.Triangle) :
    M.RefinedTrianglesMonochromatic f (M.localMeshTriangles f t) := by
  classical
  unfold localMeshTriangles
  split_ifs with hp hn hep hen
  all_goals simp only [refinedMeshTriangles]
  · let o := Classical.choice hp
    rw [M.strictMeshFor_triangles]
    apply M.strictPattern_monochromatic_positive
    · simpa [o, strictVertices, Function.comp_apply] using o.positive.le
    · simpa [o, strictVertices, Function.comp_apply] using o.negative_one.le
    · simpa [o, strictVertices, Function.comp_apply] using o.negative_two.le
    · rw [M.strictVertices_f]
      simp
    · rw [M.strictVertices_f]
      simp
  · let o := Classical.choice hn
    exact M.strictNegativeMeshFor_monochromatic f _ _
      o.negative o.positive_one o.positive_two
  · let o := Classical.choice hep
    rw [M.edgeMeshFor_triangles]
    apply M.edgePattern_monochromatic_positive
    · simpa [o, edgeVertices, Function.comp_apply] using o.positive.le
    · simpa [o, edgeVertices, Function.comp_apply] using o.negative.le
    · rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
    · rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
  · let o := Classical.choice hen
    exact M.edgeNegativeMeshFor_monochromatic f _ _ o.negative o.positive o.zero
  · have hpair := pairwise_nonnegative_of_no_orderings M f t hp hn hep hen
    have hsign := same_closed_side_of_pairwise_products hpair.1 hpair.2.1 hpair.2.2
    intro s hs
    unfold unchangedMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hr : r = Finset.univ := Finset.mem_singleton.mp hr
    subst r
    rcases hsign with h | h
    · left
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      fin_cases i
      · change 0 ≤ f (M.position (M.orderedVertex t 0)); exact h.1
      · change 0 ≤ f (M.position (M.orderedVertex t 1)); exact h.2.1
      · change 0 ≤ f (M.position (M.orderedVertex t 2)); exact h.2.2
    · right
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      fin_cases i
      · change f (M.position (M.orderedVertex t 0)) ≤ 0; exact h.1
      · change f (M.position (M.orderedVertex t 1)) ≤ 0; exact h.2.1
      · change f (M.position (M.orderedVertex t 2)) ≤ 0; exact h.2.2

/-- A vertex used by a local line refinement is either an old vertex of its parent triangle or
lies on the cutting line. -/
theorem local_child_vertex_old_or_zero (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ s) :
    (∃ v ∈ t.1, (x : Plane) = M.position v) ∨ f (x : Plane) = 0 := by
  classical
  unfold localMeshTriangles at hs
  split_ifs at hs with hp hn hep hen
  all_goals simp only [refinedMeshTriangles] at hs
  · let o := Classical.choice hp
    rw [M.strictMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := exists_index_of_mem_strictPattern _ hs hx
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      rw [M.strictVertices_f]
      rfl
    · right
      rw [M.strictVertices_f]
      rfl
  · let o := Classical.choice hn
    unfold strictNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.strictMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := exists_index_of_mem_strictPattern _ hr hy
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change f (M.strictVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 3 : Plane) = 0
      have h := M.strictVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 3
      simpa using h
    · right
      change f (M.strictVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 4 : Plane) = 0
      have h := M.strictVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive_one)
        (by simpa using o.positive_two) 4
      simpa using h
  · let o := Classical.choice hep
    rw [M.edgeMeshFor_triangles] at hs
    obtain ⟨i, rfl⟩ := exists_index_of_mem_edgePattern _ hs hx
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      rw [M.edgeVertices_f f _ o.positive o.negative o.zero]
      rfl
  · let o := Classical.choice hen
    unfold edgeNegativeMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [M.edgeMeshFor_triangles] at hr
    obtain ⟨i, rfl⟩ := exists_index_of_mem_edgePattern _ hr hy
    fin_cases i
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · left; exact ⟨_, M.orderedVertex_mem t _, rfl⟩
    · right
      change f (M.edgeVertices (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive) 3 : Plane) = 0
      have h := M.edgeVertices_f (-f) (M.orderedVertex t ∘ o.perm)
        (by simpa using o.negative) (by simpa using o.positive) (by simpa using o.zero) 3
      simpa using h
  · unfold unchangedMeshFor at hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hr : r = Finset.univ := Finset.mem_singleton.mp hr
    subst r
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    left
    exact ⟨_, M.orderedVertex_mem t i, rfl⟩

theorem localMeshTriangles_support (t : M.Triangle) :
    (⋃ s ∈ M.localMeshTriangles f t,
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))) =
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  classical
  unfold localMeshTriangles
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    dsimp only [Function.comp_apply]
    have h := M.strictMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.positive o.negative_one o.negative_two
    rw [(M.strictMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.positive o.negative_one o.negative_two).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  · let o := Classical.choice hn
    dsimp only [Function.comp_apply]
    have h := M.strictNegativeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm)
      o.negative o.positive_one o.positive_two
    rw [(M.strictNegativeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.negative o.positive_one o.positive_two).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  · let o := Classical.choice hep
    dsimp only [Function.comp_apply]
    have h := M.edgeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.positive o.negative
    rw [(M.edgeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.positive o.negative).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  · let o := Classical.choice hen
    dsimp only [Function.comp_apply]
    have h := M.edgeNegativeMeshFor_support f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) o.negative o.positive
    rw [(M.edgeNegativeMeshFor f (M.orderedVertex t ∘ o.perm) _
      o.negative o.positive).toPlaneComplex_support] at h
    rw [M.range_orderedVertex_perm t o.perm] at h
    exact h
  · simp only [unchangedMeshFor, TriangleMesh.reindex, TriangleMesh.single,
      oldVerticesEmbedding]
    have h := M.unchangedMeshFor_support f (M.orderedVertex t)
      (M.orderedVertex_affineIndependent t)
    rw [(M.unchangedMeshFor f (M.orderedVertex t) _).toPlaneComplex_support] at h
    rw [Set.range_comp, M.range_orderedVertex t] at h
    exact h

theorem localMeshTriangles_inter (t : M.Triangle)
    {s u : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hu : u ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (u : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ u : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  unfold localMeshTriangles at hs hu
  split_ifs at hs hu with hp hn hep hen
  · exact (M.strictMeshFor f _ _ _ _ _).triangle_inter s hs u hu
  · exact (M.strictNegativeMeshFor f _ _ _ _ _).triangle_inter s hs u hu
  · exact (M.edgeMeshFor f _ _ _ _).triangle_inter s hs u hu
  · exact (M.edgeNegativeMeshFor f _ _ _ _).triangle_inter s hs u hu
  · exact (M.unchangedMeshFor f _ _).triangle_inter s hs u hu

theorem convexHull_child_subset_parent (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ⊆
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  rw [← M.localMeshTriangles_support f t]
  exact Set.subset_iUnion_of_subset s
    (Set.subset_iUnion_of_subset hs subset_rfl)

theorem child_vertex_mem_parent (t : M.Triangle)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {v : M.RefinedVertex f} (hv : v ∈ s) :
    (v : Plane) ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
  apply M.convexHull_child_subset_parent f t hs
  exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩

/-! ## Barycentric traces on old parent edges -/

/-- The barycentric coordinate opposite the `k`-th edge of an old triangle. -/
noncomputable def oppositeCoord (t : M.Triangle) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  (affineBasisOfTriangle (M.position ∘ M.orderedVertex t)
    (M.orderedVertex_affineIndependent t)).coord k

@[simp] theorem oppositeCoord_vertex (t : M.Triangle) (k i : Fin 3) :
    M.oppositeCoord t k (M.position (M.orderedVertex t i)) = if k = i then 1 else 0 := by
  exact AffineBasis.coord_apply _ _ _

/-- The two old geometric vertices of the edge opposite `k`. -/
noncomputable def oppositeEdgePoints (t : M.Triangle) (k : Fin 3) : Finset Plane :=
  (Finset.univ.erase k).image (M.position ∘ M.orderedVertex t)

theorem oppositeEdgePoints_subset_parentPoints (t : M.Triangle) (k : Fin 3) :
    M.oppositeEdgePoints t k ⊆ Finset.univ.image (M.position ∘ M.orderedVertex t) := by
  exact Finset.image_subset_image (Finset.erase_subset _ _)

theorem oppositeCoord_nonneg_of_mem_parent (t : M.Triangle) (k : Fin 3)
    {x : Plane} (hx : x ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex))) :
    0 ≤ M.oppositeCoord t k x := by
  have hrange : Set.range (M.position ∘ M.orderedVertex t) =
      M.position '' (t.1 : Set M.Vertex) := by
    rw [Set.range_comp, M.range_orderedVertex t]
  rw [← hrange] at hx
  apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (M.oppositeCoord t k)) hx
  rintro x ⟨i, rfl⟩
  change 0 ≤ M.oppositeCoord t k (M.position (M.orderedVertex t i))
  rw [M.oppositeCoord_vertex]
  split_ifs <;> norm_num

theorem parent_inter_oppositeCoord_zero (t : M.Triangle) (k : Fin 3) :
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩
        {x | M.oppositeCoord t k x = 0} =
      convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hp : Function.Injective p :=
    M.position_injective.comp (M.orderedVertex_injective t)
  have hrange : M.position '' (t.1 : Set M.Vertex) =
      ((Finset.univ.image p : Finset Plane) : Set Plane) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp,
      M.range_orderedVertex t]
  rw [hrange]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · apply congrArg (convexHull ℝ)
    ext x
    change x ∈ (Finset.univ.image p).filter (fun x ↦ M.oppositeCoord t k x = 0) ↔
      x ∈ M.oppositeEdgePoints t k
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      oppositeEdgePoints, Finset.mem_erase]
    constructor
    · rintro ⟨⟨i, hix⟩, hi⟩
      refine ⟨i, ⟨?_, trivial⟩, hix⟩
      intro hki
      subst i
      have hzero : M.oppositeCoord t k (M.position (M.orderedVertex t k)) = 0 := by
        change M.oppositeCoord t k (p k) = 0
        rw [hix]
        exact hi
      rw [M.oppositeCoord_vertex] at hzero
      norm_num at hzero
    · rintro ⟨i, ⟨hik, -⟩, hix⟩
      refine ⟨⟨i, hix⟩, ?_⟩
      rw [← hix]
      change M.oppositeCoord t k (M.position (M.orderedVertex t i)) = 0
      rw [M.oppositeCoord_vertex]
      simp [Ne.symm hik]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ M.oppositeCoord t k (M.position (M.orderedVertex t i))
    rw [M.oppositeCoord_vertex]
    split_ifs <;> norm_num

/-- Vertices of a child triangle lying on the old edge opposite `k`. -/
noncomputable def childEdgeTrace (t : M.Triangle) (k : Fin 3)
    (s : Finset (M.RefinedVertex f)) : Finset (M.RefinedVertex f) :=
  s.filter fun v => M.oppositeCoord t k (v : Plane) = 0

theorem child_inter_oppositeEdge (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (M.childEdgeTrace f t k s : Set (M.RefinedVertex f))) := by
  classical
  let A := convexHull ℝ
    (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))
  let P := convexHull ℝ (M.position '' (t.1 : Set M.Vertex))
  let Z : Set Plane := {x | M.oppositeCoord t k x = 0}
  have hAP : A ⊆ P := M.convexHull_child_subset_parent f t hs
  have hedge : P ∩ Z =
      convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) :=
    M.parent_inter_oppositeCoord_zero t k
  rw [← hedge]
  have hinter : A ∩ (P ∩ Z) = A ∩ Z := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1, hx.2.2⟩
    · exact fun hx => ⟨hx.1, hAP hx.1, hx.2⟩
  rw [hinter]
  dsimp only [A]
  simp only [← Finset.coe_image]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · apply congrArg (convexHull ℝ)
    ext x
    change x ∈ (s.image ((↑) : M.RefinedVertex f → Plane)).filter
        (fun x ↦ M.oppositeCoord t k x = 0) ↔
      x ∈ (M.childEdgeTrace f t k s).image ((↑) : M.RefinedVertex f → Plane)
    simp only [Finset.mem_filter, Finset.mem_image, childEdgeTrace]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hz⟩
      exact ⟨v, ⟨hv, hz⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv.1, rfl⟩, hv.2⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact M.oppositeCoord_nonneg_of_mem_parent t k
      (M.child_vertex_mem_parent f t hs hv)

theorem exists_oppositeEdgePoints_eq (t : M.Triangle) {e : Finset M.Vertex}
    (het : e ⊆ t.1) (hecard : e.card = 2) :
    ∃ k : Fin 3, M.oppositeEdgePoints t k = e.image M.position := by
  have hne : e ≠ t.1 := by
    intro h
    have hc := hecard
    rw [h, M.card_triangle t.1 t.2] at hc
    omega
  have hss : e ⊂ t.1 := Finset.ssubset_iff_subset_ne.mpr ⟨het, hne⟩
  obtain ⟨w, hwt, hwe⟩ := Finset.exists_of_ssubset hss
  have hwrange : w ∈ Set.range (M.orderedVertex t) := by
    rw [M.range_orderedVertex t]
    exact hwt
  obtain ⟨k, hwk⟩ := hwrange
  have herase : t.1.erase w = e := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun hvw => hwe (hvw ▸ hv), het hv⟩
    · rw [Finset.card_erase_of_mem hwt, M.card_triangle t.1 t.2, hecard]
  refine ⟨k, ?_⟩
  apply Finset.ext
  intro x
  simp only [oppositeEdgePoints, Finset.mem_image, Finset.mem_erase, Finset.mem_univ,
    and_true]
  constructor
  · rintro ⟨i, hik, rfl⟩
    refine ⟨M.orderedVertex t i, ?_, rfl⟩
    rw [← herase]
    exact Finset.mem_erase.mpr ⟨fun hiw => hik (M.orderedVertex_injective t
      (hiw.trans hwk.symm)), M.orderedVertex_mem t i⟩
  · rintro ⟨v, hve, rfl⟩
    have hvt : v ∈ t.1 := het hve
    have hvrange : v ∈ Set.range (M.orderedVertex t) := by
      rw [M.range_orderedVertex t]
      exact hvt
    obtain ⟨i, rfl⟩ := hvrange
    refine ⟨i, ?_, rfl⟩
    intro hik
    subst i
    apply hwe
    simpa [hwk] using hve

/-- An affine functional taking different values at the endpoints of a segment is injective on
that segment. -/
theorem affine_apply_injectiveOn_segment {g : Plane →ᵃ[ℝ] ℝ} {p q : Plane}
    (hpq : g p ≠ g q) : Set.InjOn g (segment ℝ p q) := by
  intro x hx y hy hxy
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, rfl⟩ := hy
  rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap] at hxy
  simp only [AffineMap.lineMap_apply_module, smul_eq_mul] at hxy
  have hd : g q - g p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hab : a = b := by
    rcases lt_or_gt_of_ne hd with hdneg | hdpos <;> nlinarith
  rw [hab]

theorem eq_endpoint_of_mem_segment_apply_zero_of_mul_nonneg
    {g : Plane →ᵃ[ℝ] ℝ} {p q x : Plane}
    (hprod : 0 ≤ g p * g q) (hnotboth : ¬ (g p = 0 ∧ g q = 0))
    (hx : x ∈ segment ℝ p q) (hzero : g x = 0) : x = p ∨ x = q := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [g.apply_lineMap, AffineMap.lineMap_apply_module] at hzero
  simp only [smul_eq_mul] at hzero
  by_cases hp : g p = 0
  · have hq : g q ≠ 0 := fun hq => hnotboth ⟨hp, hq⟩
    have ht0 : t = 0 := by
      rw [hp] at hzero
      apply (mul_eq_zero.mp (by linarith : t * g q = 0)).resolve_right hq
    left
    simp [ht0, AffineMap.lineMap_apply_module]
  · by_cases hq : g q = 0
    · have ht1 : t = 1 := by
        rw [hq] at hzero
        have : (1 - t) * g p = 0 := by linarith
        have := (mul_eq_zero.mp this).resolve_right hp
        linarith
      right
      simp [ht1, AffineMap.lineMap_apply_module]
    · have hpos : 0 < g p * g q := lt_of_le_of_ne hprod (mul_ne_zero hp hq).symm
      rcases mul_pos_iff.mp hpos with hsign | hsign
      · have ht0 := ht.1
        have ht1 := ht.2
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hsign.1.le,
          mul_nonneg ht0 hsign.2.le]
      · have ht0 := ht.1
        have ht1 := ht.2
        nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hsign.1.le),
          mul_nonneg ht0 (neg_nonneg.mpr hsign.2.le)]

theorem affineIndependent_subset_pair {p q : Plane} (hpq : p ≠ q)
    {s : Set Plane} (hs : s ⊆ {p, q}) :
    AffineIndependent ℝ ((↑) : s → Plane) := by
  have h := (affineIndependent_of_ne (k := ℝ) hpq).range
  apply h.mono
  simpa [Set.pair_comm] using hs

theorem old_vertex_mem_of_oppositeCoord_zero (t : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex} (hedge : M.oppositeEdgePoints t k = e.image M.position)
    {v : M.Vertex} (hvt : v ∈ t.1)
    (hzero : M.oppositeCoord t k (M.position v) = 0) : v ∈ e := by
  have hvrange : v ∈ Set.range (M.orderedVertex t) := by
    rw [M.range_orderedVertex t]
    exact hvt
  obtain ⟨i, rfl⟩ := hvrange
  have hik : k ≠ i := by
    intro hki
    subst i
    rw [M.oppositeCoord_vertex] at hzero
    norm_num at hzero
  have hp : M.position (M.orderedVertex t i) ∈ M.oppositeEdgePoints t k := by
    unfold oppositeEdgePoints
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ _⟩, rfl⟩
  rw [hedge] at hp
  obtain ⟨w, hwe, hw⟩ := Finset.mem_image.mp hp
  exact M.position_injective hw |>.symm ▸ hwe

theorem trace_vertex_old_edge_or_zero (t : M.Triangle) (k : Fin 3)
    {e : Finset M.Vertex} (hedge : M.oppositeEdgePoints t k = e.image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    (∃ v ∈ e, (x : Plane) = M.position v) ∨ f (x : Plane) = 0 := by
  have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
  have hxcoord : M.oppositeCoord t k (x : Plane) = 0 := (Finset.mem_filter.mp hx).2
  rcases M.local_child_vertex_old_or_zero f t hs hxs with hold | hzero
  · obtain ⟨v, hvt, hxv⟩ := hold
    left
    refine ⟨v, M.old_vertex_mem_of_oppositeCoord_zero t k hedge hvt ?_, hxv⟩
    rw [← hxv]
    exact hxcoord
  · exact Or.inr hzero

theorem trace_vertex_mem_oppositeEdgeHull (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    (x : Plane) ∈ convexHull ℝ ((M.oppositeEdgePoints t k : Finset Plane) : Set Plane) := by
  rw [← M.parent_inter_oppositeCoord_zero t k]
  exact ⟨M.child_vertex_mem_parent f t hs (Finset.mem_filter.mp hx).1,
    (Finset.mem_filter.mp hx).2⟩

theorem trace_vertex_eq_endpoint_or_cut (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (hab : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (ha : 0 < f (M.position a)) (hb : f (M.position b) < 0)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b ∨
      x = M.cutRefinedVertex f a b (mul_neg_of_pos_of_neg ha hb) := by
  rcases M.trace_vertex_old_edge_or_zero f t k hedge hs hx with hold | hzero
  · obtain ⟨v, hv, hxv⟩ := hold
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Or.inl (Subtype.ext hxv)
    · exact Or.inr (Or.inl (Subtype.ext hxv))
  · right; right
    apply Subtype.ext
    apply affineCutPoint.eq_of_mem_segment_of_apply_eq_zero f (M.position a) (M.position b)
      ha hb
    · have hxedge := M.trace_vertex_mem_oppositeEdgeHull f t k hs hx
      rw [hedge] at hxedge
      simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
        Set.image_insert_eq, Set.image_singleton] at hxedge
      rwa [convexHull_pair] at hxedge
    · exact hzero

theorem trace_vertex_eq_endpoint_of_mul_nonneg (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (hab : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hprod : 0 ≤ f (M.position a) * f (M.position b))
    (hnotboth : ¬ (f (M.position a) = 0 ∧ f (M.position b) = 0))
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b := by
  rcases M.trace_vertex_old_edge_or_zero f t k hedge hs hx with hold | hzero
  · obtain ⟨v, hv, hxv⟩ := hold
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Or.inl (Subtype.ext hxv)
    · exact Or.inr (Subtype.ext hxv)
  · have hxedge := M.trace_vertex_mem_oppositeEdgeHull f t k hs hx
    rw [hedge] at hxedge
    simp only [Finset.coe_image, Finset.coe_insert, Finset.coe_singleton,
      Set.image_insert_eq, Set.image_singleton] at hxedge
    rw [convexHull_pair] at hxedge
    rcases eq_endpoint_of_mem_segment_apply_zero_of_mul_nonneg hprod hnotboth hxedge hzero
      with hxa | hxb
    · exact Or.inl (Subtype.ext hxa)
    · exact Or.inr (Subtype.ext hxb)

theorem orderedVertex_eq_endpoint_of_ne_opposite (t : M.Triangle) (k j : Fin 3)
    {a b : M.Vertex}
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    (hjk : j ≠ k) : M.orderedVertex t j = a ∨ M.orderedVertex t j = b := by
  have hp : M.position (M.orderedVertex t j) ∈ M.oppositeEdgePoints t k := by
    unfold oppositeEdgePoints
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩, rfl⟩
  rw [hedge] at hp
  obtain ⟨v, hv, hpos⟩ := Finset.mem_image.mp hp
  have hvj : v = M.orderedVertex t j := M.position_injective hpos
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl hvj.symm
  · exact Or.inr hvj.symm

theorem trace_vertex_eq_endpoint_of_edge_in_line (t : M.Triangle) (k : Fin 3)
    {a b : M.Vertex} (_ : a ≠ b)
    (hedge : M.oppositeEdgePoints t k = ({a, b} : Finset M.Vertex).image M.position)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (ha : f (M.position a) = 0) (hb : f (M.position b) = 0)
    {x : M.RefinedVertex f} (hx : x ∈ M.childEdgeTrace f t k s) :
    x = M.oldRefinedVertex f a ∨ x = M.oldRefinedVertex f b := by
  classical
  have hzero (j : Fin 3) (hjk : j ≠ k) :
      f (M.position (M.orderedVertex t j)) = 0 := by
    rcases M.orderedVertex_eq_endpoint_of_ne_opposite t k j hedge hjk with hj | hj
    · simpa [hj] using ha
    · simpa [hj] using hb
  have hp : ¬ Nonempty (M.PositiveStrictOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.negative_one]
    · linarith [hzero (o.perm 0) h0k, o.positive]
  have hn : ¬ Nonempty (M.NegativeStrictOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.positive_one]
    · linarith [hzero (o.perm 0) h0k, o.negative]
  have hep : ¬ Nonempty (M.PositiveEdgeOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.negative]
    · linarith [hzero (o.perm 0) h0k, o.positive]
  have hen : ¬ Nonempty (M.NegativeEdgeOrdering f t) := by
    rintro ⟨o⟩
    have hne : o.perm 0 ≠ o.perm 1 := o.perm.injective.ne (by decide)
    by_cases h0k : o.perm 0 = k
    · have h1k : o.perm 1 ≠ k := fun h => hne (h0k.trans h.symm)
      linarith [hzero (o.perm 1) h1k, o.positive]
    · linarith [hzero (o.perm 0) h0k, o.negative]
  unfold localMeshTriangles at hs
  simp only [hp, hn, hep, hen, ↓reduceDIte] at hs
  unfold unchangedMeshFor at hs
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
  have hr : r = Finset.univ := Finset.mem_singleton.mp hr
  subst r
  have hxs := (Finset.mem_filter.mp hx).1
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hxs
  have hjk : j ≠ k := by
    intro hjk
    subst j
    have hz := (Finset.mem_filter.mp hx).2
    change M.oppositeCoord t k
        (M.oldRefinedVertex f (M.orderedVertex t k) : Plane) = 0 at hz
    change M.oppositeCoord t k (M.position (M.orderedVertex t k)) = 0 at hz
    rw [M.oppositeCoord_vertex] at hz
    norm_num at hz
  rcases M.orderedVertex_eq_endpoint_of_ne_opposite t k j hedge hjk with hj | hj
  · left
    change M.oldRefinedVertex f (M.orderedVertex t j) = M.oldRefinedVertex f a
    rw [hj]
  · right
    change M.oldRefinedVertex f (M.orderedVertex t j) = M.oldRefinedVertex f b
    rw [hj]

theorem childEdgeTrace_monochromatic (t : M.Triangle) (k : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t) :
    (∀ x ∈ M.childEdgeTrace f t k s, 0 ≤ f (x : Plane)) ∨
      (∀ x ∈ M.childEdgeTrace f t k s, f (x : Plane) ≤ 0) := by
  rcases M.localMeshTriangles_monochromatic f t s hs with h | h
  · exact Or.inl fun x hx => h x (Finset.mem_filter.mp hx).1
  · exact Or.inr fun x hx => h x (Finset.mem_filter.mp hx).1

private theorem convexHull_inter_of_opposite_three_point_subsets
    {a b z : M.RefinedVertex f}
    (ha : 0 < f (a : Plane)) (hb : f (b : Plane) < 0) (hz : f (z : Plane) = 0)
    {C D : Finset (M.RefinedVertex f)}
    (hCclass : ∀ x ∈ C, x = a ∨ x = b ∨ x = z)
    (hDclass : ∀ x ∈ D, x = a ∨ x = b ∨ x = z)
    (hC : ∀ x ∈ C, 0 ≤ f (x : Plane)) (hD : ∀ x ∈ D, f (x : Plane) ≤ 0) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (C : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (D : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((C ∩ D : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let val : M.RefinedVertex f → Plane := (↑)
  simp only [← Finset.coe_image]
  have hCsub : C ⊆ {a, z} := by
    intro x hx
    rcases hCclass x hx with rfl | rfl | rfl
    · simp
    · exfalso; linarith [hC _ hx]
    · simp
  have hDsub : D ⊆ {b, z} := by
    intro x hx
    rcases hDclass x hx with rfl | rfl | rfl
    · exfalso; linarith [hD _ hx]
    · simp
    · simp
  by_cases hzC : z ∈ C
  · by_cases hzD : z ∈ D
    · have hCzero : (C.image val).filter (fun p ↦ f p = 0) = {(z : Plane)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hxzero⟩
          rcases hCclass x hx with rfl | rfl | rfl
          · exfalso; linarith
          · exfalso; linarith
          · rfl
        · rintro rfl
          exact ⟨⟨z, hzC, rfl⟩, hz⟩
      have hDzero : (D.image val).filter (fun p ↦ f p = 0) = {(z : Plane)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨x, hx, rfl⟩, hxzero⟩
          rcases hDclass x hx with rfl | rfl | rfl
          · exfalso; linarith
          · exfalso; linarith
          · rfl
        · rintro rfl
          exact ⟨⟨z, hzD, rfl⟩, hz⟩
      have hinter := convexHull_inter_of_affine_separation
        (C.image val) (D.image val) ({(z : Plane)} : Finset Plane) f
        (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          exact hC x hx)
        (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          exact hD x hx)
        hCzero hDzero
      have hCD : C ∩ D = {z} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton]
        constructor
        · rintro ⟨hxC, hxD⟩
          have hxpair := hCsub hxC
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
          rcases hxpair with hxa | hxz
          · subst x
            exfalso
            linarith [hD a hxD]
          · exact hxz
        · rintro rfl
          exact ⟨hzC, hzD⟩
      rw [hCD]
      simpa [val] using hinter
    · have hDsingle : D ⊆ {b} := by
        intro x hx
        have hxpair := hDsub hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
        rcases hxpair with hxb | hxz
        · simp [hxb]
        · exact False.elim (hzD (hxz ▸ hx))
      have hDgeom : convexHull ℝ ((D.image val : Finset Plane) : Set Plane) ⊆ {(b : Plane)} :=
        convexHull_min (by
          intro p hp
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          simpa [val] using hDsingle hx) (convex_singleton _)
      have hCnonneg : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ⊆
          {p | 0 ≤ f p} := convexHull_min (by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        exact hC x hx) ((convex_Ici (0 : ℝ)).affine_preimage f)
      have hleft : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
          convexHull ℝ ((D.image val : Finset Plane) : Set Plane) = ∅ := by
        apply Set.Subset.antisymm
        · intro p hp
          have hpb := hDgeom hp.2
          simp only [Set.mem_singleton_iff] at hpb
          subst p
          exfalso
          have hbnonneg : 0 ≤ f (b : Plane) := hCnonneg hp.1
          linarith
        · exact Set.empty_subset _
      have hCD : C ∩ D = ∅ := by
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_inter.mp hx
          have hxb := hDsingle hx'.2
          simp only [Finset.mem_singleton] at hxb
          subst x
          exfalso
          linarith [hC b hx'.1]
        · intro hx
          simp at hx
      rw [hleft, hCD]
      simp
  · have hCsingle : C ⊆ {a} := by
      intro x hx
      have hxpair := hCsub hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
      rcases hxpair with hxa | hxz
      · simp [hxa]
      · exact False.elim (hzC (hxz ▸ hx))
    have hCgeom : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ⊆ {(a : Plane)} :=
      convexHull_min (by
        intro p hp
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
        simpa [val] using hCsingle hx) (convex_singleton _)
    have hDnonpos : convexHull ℝ ((D.image val : Finset Plane) : Set Plane) ⊆
        {p | f p ≤ 0} := convexHull_min (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact hD x hx) ((convex_Iic (0 : ℝ)).affine_preimage f)
    have hleft : convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
        convexHull ℝ ((D.image val : Finset Plane) : Set Plane) = ∅ := by
      apply Set.Subset.antisymm
      · intro p hp
        have hpa := hCgeom hp.1
        simp only [Set.mem_singleton_iff] at hpa
        subst p
        exfalso
        have hanonpos : f (a : Plane) ≤ 0 := hDnonpos hp.2
        linarith
      · exact Set.empty_subset _
    have hCD : C ∩ D = ∅ := by
      ext x
      constructor
      · intro hx
        have hx' := Finset.mem_inter.mp hx
        have hxa := hCsingle hx'.1
        simp only [Finset.mem_singleton] at hxa
        subst x
        exfalso
        linarith [hD a hx'.2]
      · intro hx
        simp at hx
    rw [hleft, hCD]
    simp

/-- The finite one-dimensional calculation behind compatibility on a cut edge. -/
theorem convexHull_inter_of_signed_three_point_subsets
    {a b z : M.RefinedVertex f}
    (ha : 0 < f (a : Plane)) (hb : f (b : Plane) < 0) (hz : f (z : Plane) = 0)
    {A B : Finset (M.RefinedVertex f)}
    (hAclass : ∀ x ∈ A, x = a ∨ x = b ∨ x = z)
    (hBclass : ∀ x ∈ B, x = a ∨ x = b ∨ x = z)
    (hAmono : (∀ x ∈ A, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ A, f (x : Plane) ≤ 0))
    (hBmono : (∀ x ∈ B, 0 ≤ f (x : Plane)) ∨ (∀ x ∈ B, f (x : Plane) ≤ 0)) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let val : M.RefinedVertex f → Plane := (↑)
  let AP : Finset Plane := A.image val
  let BP : Finset Plane := B.image val
  have ha_ne_z : (a : Plane) ≠ (z : Plane) := by
    intro h
    have := congrArg f h
    linarith
  have hb_ne_z : (b : Plane) ≠ (z : Plane) := by
    intro h
    have := congrArg f h
    linarith
  have sameSide
      (hA : ∀ x ∈ A, 0 ≤ f (x : Plane))
      (hB : ∀ x ∈ B, 0 ≤ f (x : Plane)) :
      convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
        convexHull ℝ ((AP ∩ BP : Finset Plane) : Set Plane) := by
    have hAsub : A ⊆ {a, z} := by
      intro x hx
      rcases hAclass x hx with rfl | rfl | rfl
      · simp
      · exfalso; linarith [hA _ hx]
      · simp
    have hBsub : B ⊆ {a, z} := by
      intro x hx
      rcases hBclass x hx with rfl | rfl | rfl
      · simp
      · exfalso; linarith [hB _ hx]
      · simp
    have hPsub : (AP ∪ BP : Finset Plane) ⊆ {(a : Plane), (z : Plane)} := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hAsub hv
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hBsub hv
    have hAI : AffineIndependent ℝ
        ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
      apply affineIndependent_subset_pair ha_ne_z
      intro x hx
      change x = (a : Plane) ∨ x = (z : Plane)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hPsub hx
    simpa only [Finset.coe_inter] using (hAI.convexHull_inter').symm
  have sameSideNeg
      (hA : ∀ x ∈ A, f (x : Plane) ≤ 0)
      (hB : ∀ x ∈ B, f (x : Plane) ≤ 0) :
      convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
        convexHull ℝ ((AP ∩ BP : Finset Plane) : Set Plane) := by
    have hAsub : A ⊆ {b, z} := by
      intro x hx
      rcases hAclass x hx with rfl | rfl | rfl
      · exfalso; linarith [hA _ hx]
      · simp
      · simp
    have hBsub : B ⊆ {b, z} := by
      intro x hx
      rcases hBclass x hx with rfl | rfl | rfl
      · exfalso; linarith [hB _ hx]
      · simp
      · simp
    have hPsub : (AP ∪ BP : Finset Plane) ⊆ {(b : Plane), (z : Plane)} := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hAsub hv
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        simpa [val] using hBsub hv
    have hAI : AffineIndependent ℝ
        ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
      apply affineIndependent_subset_pair hb_ne_z
      intro x hx
      change x = (b : Plane) ∨ x = (z : Plane)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hPsub hx
    simpa only [Finset.coe_inter] using (hAI.convexHull_inter').symm
  have oppositeSide {C D : Finset (M.RefinedVertex f)}
      (hCclass : ∀ x ∈ C, x = a ∨ x = b ∨ x = z)
      (hDclass : ∀ x ∈ D, x = a ∨ x = b ∨ x = z)
      (hC : ∀ x ∈ C, 0 ≤ f (x : Plane))
      (hD : ∀ x ∈ D, f (x : Plane) ≤ 0) :
      convexHull ℝ ((C.image val : Finset Plane) : Set Plane) ∩
          convexHull ℝ ((D.image val : Finset Plane) : Set Plane) =
        convexHull ℝ (((C ∩ D).image val : Finset Plane) : Set Plane) := by
    simpa only [← Finset.coe_image] using
      convexHull_inter_of_opposite_three_point_subsets (M := M) (f := f)
        ha hb hz hCclass hDclass hC hD
  simp only [← Finset.coe_image]
  change convexHull ℝ (AP : Set Plane) ∩ convexHull ℝ (BP : Set Plane) =
    convexHull ℝ (((A ∩ B).image val : Finset Plane) : Set Plane)
  have himageInter : (A ∩ B).image val = AP ∩ BP := by
    exact Finset.image_inter _ _ Subtype.val_injective
  rcases hAmono with hA | hA <;> rcases hBmono with hB | hB
  · exact (sameSide hA hB).trans (congrArg (fun S : Set Plane => convexHull ℝ S)
      (by simpa only [Finset.coe_inj] using himageInter.symm))
  · exact oppositeSide hAclass hBclass hA hB
  · rw [Set.inter_comm, Finset.inter_comm]
    exact oppositeSide hBclass hAclass hB hA
  · exact (sameSideNeg hA hB).trans (congrArg (fun S : Set Plane => convexHull ℝ S)
      (by simpa only [Finset.coe_inj] using himageInter.symm))

theorem convexHull_inter_of_two_point_subsets
    {a b : M.RefinedVertex f} (hab : (a : Plane) ≠ (b : Plane))
    {A B : Finset (M.RefinedVertex f)}
    (hA : ∀ x ∈ A, x = a ∨ x = b) (hB : ∀ x ∈ B, x = a ∨ x = b) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let AP := A.image ((↑) : M.RefinedVertex f → Plane)
  let BP := B.image ((↑) : M.RefinedVertex f → Plane)
  have hsub : (AP ∪ BP : Finset Plane) ⊆ {(a : Plane), (b : Plane)} := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      simpa using hA x hx
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      simpa using hB x hx
  have hAI : AffineIndependent ℝ ((↑) : (AP ∪ BP : Finset Plane) → Plane) := by
    apply affineIndependent_subset_pair hab
    intro p hp
    change p = (a : Plane) ∨ p = (b : Plane)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hsub hp
  have hinter := (hAI.convexHull_inter').symm
  simp only [← Finset.coe_image]
  have hi : (A ∩ B).image ((↑) : M.RefinedVertex f → Plane) = AP ∩ BP :=
    Finset.image_inter _ _ Subtype.val_injective
  exact hinter.trans (congrArg (fun S : Set Plane => convexHull ℝ S)
    (by simpa only [Finset.coe_inter] using
      congrArg ((↑) : Finset Plane → Set Plane) hi.symm))

/-- The cutting line contains no old edge of the mesh. -/
def TransverseToEdges : Prop :=
  ∀ (t : M.Triangle) (i j : Fin 3), i ≠ j →
    ¬ (f (M.position (M.orderedVertex t i)) = 0 ∧
      f (M.position (M.orderedVertex t j)) = 0)

theorem lineRefinementTriangles_inter_of_parent_inter_card_two
    (T U : M.Triangle)
    (hcard : (T.1 ∩ U.1).card = 2)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  let e : Finset M.Vertex := T.1 ∩ U.1
  have heT : e ⊆ T.1 := Finset.inter_subset_left
  have heU : e ⊆ U.1 := Finset.inter_subset_right
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hcard
  have he' : e = {a, b} := he
  obtain ⟨kT, hkT⟩ := M.exists_oppositeEdgePoints_eq T heT hcard
  obtain ⟨kU, hkU⟩ := M.exists_oppositeEdgePoints_eq U heU hcard
  have hkT' : M.oppositeEdgePoints T kT = ({a, b} : Finset M.Vertex).image M.position := by
    rw [hkT, ← he']
  have hkU' : M.oppositeEdgePoints U kU = ({a, b} : Finset M.Vertex).image M.position := by
    rw [hkU, ← he']
  let A := M.childEdgeTrace f T kT s
  let B := M.childEdgeTrace f U kU q
  let S := convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
    (s : Set (M.RefinedVertex f)))
  let Q := convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
    (q : Set (M.RefinedVertex f)))
  let PT := convexHull ℝ (M.position '' (T.1 : Set M.Vertex))
  let PU := convexHull ℝ (M.position '' (U.1 : Set M.Vertex))
  let F := convexHull ℝ (M.position '' (e : Set M.Vertex))
  have hparent : PT ∩ PU = F := M.triangle_inter T.1 T.2 U.1 U.2
  have hSsub : S ⊆ PT := M.convexHull_child_subset_parent f T hs
  have hQsub : Q ⊆ PU := M.convexHull_child_subset_parent f U hq
  have hrestrict : S ∩ Q = (S ∩ F) ∩ (Q ∩ F) := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ F := by
        rw [← hparent]
        exact ⟨hSsub hx.1, hQsub hx.2⟩
      exact ⟨⟨hx.1, hxF⟩, hx.2, hxF⟩
    · intro hx
      exact ⟨hx.1.1, hx.2.1⟩
  have hTF : convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) = F := by
    dsimp only [F]
    rw [hkT]
    simp only [Finset.coe_image]
  have hUF : convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) = F := by
    dsimp only [F]
    rw [hkU]
    simp only [Finset.coe_image]
  have hST := M.child_inter_oppositeEdge f T kT hs
  have hQU := M.child_inter_oppositeEdge f U kU hq
  rw [hTF] at hST
  rw [hUF] at hQU
  have htraceInter : s ∩ q = A ∩ B := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · intro hx
      have hxparent : (x : Plane) ∈ PT ∩ PU :=
        ⟨M.child_vertex_mem_parent f T hs hx.1,
          M.child_vertex_mem_parent f U hq hx.2⟩
      rw [hparent] at hxparent
      have hxTzero : M.oppositeCoord T kT (x : Plane) = 0 := by
        have hxedge : (x : Plane) ∈
            convexHull ℝ ((M.oppositeEdgePoints T kT : Finset Plane) : Set Plane) := by
          rw [hTF]
          exact hxparent
        rw [← M.parent_inter_oppositeCoord_zero T kT] at hxedge
        exact hxedge.2
      have hxUzero : M.oppositeCoord U kU (x : Plane) = 0 := by
        have hxedge : (x : Plane) ∈
            convexHull ℝ ((M.oppositeEdgePoints U kU : Finset Plane) : Set Plane) := by
          rw [hUF]
          exact hxparent
        rw [← M.parent_inter_oppositeCoord_zero U kU] at hxedge
        exact hxedge.2
      exact ⟨Finset.mem_filter.mpr ⟨hx.1, hxTzero⟩,
        Finset.mem_filter.mpr ⟨hx.2, hxUzero⟩⟩
    · intro hx
      exact ⟨(Finset.mem_filter.mp hx.1).1, (Finset.mem_filter.mp hx.2).1⟩
  have hAB :
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (A : Set (M.RefinedVertex f))) ∩
          convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (B : Set (M.RefinedVertex f))) =
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
          ((A ∩ B : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
    by_cases hcross : f (M.position a) * f (M.position b) < 0
    · rcases mul_neg_iff.mp hcross with hsign | hsign
      · let z := M.cutRefinedVertex f a b hcross
        apply M.convexHull_inter_of_signed_three_point_subsets f
          (a := M.oldRefinedVertex f a) (b := M.oldRefinedVertex f b) (z := z)
          hsign.1 hsign.2
          (by simpa [z] using M.pairCutPosition_apply_eq_zero f a b hcross)
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f T kT hab hkT' hs hsign.1 hsign.2 hx
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f U kU hab hkU' hq hsign.1 hsign.2 hx
        · exact M.childEdgeTrace_monochromatic f T kT hs
        · exact M.childEdgeTrace_monochromatic f U kU hq
      · have hcross' : f (M.position b) * f (M.position a) < 0 := by
          simpa [mul_comm] using hcross
        let z := M.cutRefinedVertex f b a hcross'
        apply M.convexHull_inter_of_signed_three_point_subsets f
          (a := M.oldRefinedVertex f b) (b := M.oldRefinedVertex f a) (z := z)
          hsign.2 hsign.1
          (by simpa [z] using M.pairCutPosition_apply_eq_zero f b a hcross')
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f T kT hab.symm
            (by simpa [Finset.pair_comm] using hkT') hs hsign.2 hsign.1 hx
        · intro x hx
          exact M.trace_vertex_eq_endpoint_or_cut f U kU hab.symm
            (by simpa [Finset.pair_comm] using hkU') hq hsign.2 hsign.1 hx
        · exact M.childEdgeTrace_monochromatic f T kT hs
        · exact M.childEdgeTrace_monochromatic f U kU hq
    · apply M.convexHull_inter_of_two_point_subsets f
          (a := M.oldRefinedVertex f a) (b := M.oldRefinedVertex f b)
          (fun h => hab (M.position_injective h))
      · intro x hx
        by_cases hboth : f (M.position a) = 0 ∧ f (M.position b) = 0
        · exact M.trace_vertex_eq_endpoint_of_edge_in_line f T kT hab hkT' hs
            hboth.1 hboth.2 hx
        · exact M.trace_vertex_eq_endpoint_of_mul_nonneg f T kT hab hkT' hs
            (not_lt.mp hcross) hboth hx
      · intro x hx
        by_cases hboth : f (M.position a) = 0 ∧ f (M.position b) = 0
        · exact M.trace_vertex_eq_endpoint_of_edge_in_line f U kU hab hkU' hq
            hboth.1 hboth.2 hx
        · exact M.trace_vertex_eq_endpoint_of_mul_nonneg f U kU hab hkU' hq
            (not_lt.mp hcross) hboth hx
  rw [hrestrict, hST, hQU, hAB, ← htraceInter]

/-- A nonnegative affine functional vanishing only at the `i`-th old vertex. -/
noncomputable def vertexSupportCoord (t : M.Triangle) (i : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Plane 1 - M.oppositeCoord t i

@[simp] theorem vertexSupportCoord_vertex (t : M.Triangle) (i j : Fin 3) :
    M.vertexSupportCoord t i (M.position (M.orderedVertex t j)) =
      if i = j then 0 else 1 := by
  change 1 - M.oppositeCoord t i (M.position (M.orderedVertex t j)) = _
  rw [M.oppositeCoord_vertex]
  split_ifs <;> ring

theorem vertexSupportCoord_nonneg_of_mem_parent (t : M.Triangle) (i : Fin 3)
    {x : Plane} (hx : x ∈ convexHull ℝ (M.position '' (t.1 : Set M.Vertex))) :
    0 ≤ M.vertexSupportCoord t i x := by
  have hrange : Set.range (M.position ∘ M.orderedVertex t) =
      M.position '' (t.1 : Set M.Vertex) := by
    rw [Set.range_comp, M.range_orderedVertex t]
  rw [← hrange] at hx
  apply convexHull_min ?_
    ((convex_Ici (0 : ℝ)).affine_preimage (M.vertexSupportCoord t i)) hx
  rintro x ⟨j, rfl⟩
  change 0 ≤ M.vertexSupportCoord t i (M.position (M.orderedVertex t j))
  rw [M.vertexSupportCoord_vertex]
  split_ifs <;> norm_num

theorem parent_inter_vertexSupportCoord_zero (t : M.Triangle) (i : Fin 3) :
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩
        {x | M.vertexSupportCoord t i x = 0} =
      {M.position (M.orderedVertex t i)} := by
  let p : Fin 3 → Plane := M.position ∘ M.orderedVertex t
  have hrange : M.position '' (t.1 : Set M.Vertex) =
      ((Finset.univ.image p : Finset Plane) : Set Plane) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.range_comp,
      M.range_orderedVertex t]
  rw [hrange]
  rw [convexHull_inter_affine_zero_of_nonneg]
  · have hfilter : (Finset.univ.image p).filter
        (fun x => M.vertexSupportCoord t i x = 0) = {p i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨j, hj⟩, hzero⟩
        have hij : i = j := by
          by_contra hij
          have : M.vertexSupportCoord t i (p j) = 1 := by
            change M.vertexSupportCoord t i (M.position (M.orderedVertex t j)) = 1
            rw [M.vertexSupportCoord_vertex, if_neg hij]
          have hzero' : M.vertexSupportCoord t i (p j) = 0 := by
            rw [hj]
            exact hzero
          rw [this] at hzero'
          norm_num at hzero'
        subst j
        exact hj.symm
      · rintro rfl
        refine ⟨⟨i, rfl⟩, ?_⟩
        change M.vertexSupportCoord t i (M.position (M.orderedVertex t i)) = 0
        simp
    rw [hfilter, Finset.coe_singleton, convexHull_singleton]
    simp [p]
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    change 0 ≤ M.vertexSupportCoord t i (M.position (M.orderedVertex t j))
    rw [M.vertexSupportCoord_vertex]
    split_ifs <;> norm_num

theorem old_vertex_mem_child_of_position_mem (t : M.Triangle) (i : Fin 3)
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f t)
    (hmem : M.position (M.orderedVertex t i) ∈
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (s : Set (M.RefinedVertex f)))) :
    M.oldRefinedVertex f (M.orderedVertex t i) ∈ s := by
  classical
  let g := M.vertexSupportCoord t i
  let points : Finset Plane := s.image ((↑) : M.RefinedVertex f → Plane)
  have hg : ∀ x ∈ points, 0 ≤ g x := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact M.vertexSupportCoord_nonneg_of_mem_parent t i
      (M.child_vertex_mem_parent f t hs hv)
  have hinter := convexHull_inter_affine_zero_of_nonneg points g hg
  have hcorner : M.position (M.orderedVertex t i) ∈
      convexHull ℝ (points.filter (fun x => g x = 0) : Set Plane) := by
    rw [← hinter]
    refine ⟨?_, ?_⟩
    · simpa [points, Finset.coe_image] using hmem
    · change M.vertexSupportCoord t i (M.position (M.orderedVertex t i)) = 0
      simp
  have hne : (points.filter fun x => g x = 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hcorner
    simp at hcorner
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp hp'.1
  have hvparent := M.child_vertex_mem_parent f t hs hv
  have hvcorner : (v : Plane) = M.position (M.orderedVertex t i) := by
    have : (v : Plane) ∈
        convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) ∩ {x | g x = 0} := by
      refine ⟨hvparent, ?_⟩
      change g (v : Plane) = 0
      have hpzero := hp'.2
      rw [← hvp] at hpzero
      exact hpzero
    rw [show g = M.vertexSupportCoord t i by rfl,
      M.parent_inter_vertexSupportCoord_zero t i] at this
    simpa using this
  have hvEq : v = M.oldRefinedVertex f (M.orderedVertex t i) := Subtype.ext hvcorner
  rwa [← hvEq]

theorem lineRefinementTriangles_inter_of_parent_inter_card_zero
    (T U : M.Triangle) (hcard : (T.1 ∩ U.1).card = 0)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  have he : T.1 ∩ U.1 = ∅ := Finset.card_eq_zero.mp hcard
  have hparents := M.triangle_inter T.1 T.2 U.1 U.2
  rw [he] at hparents
  have hinter : convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (s : Set (M.RefinedVertex f))) ∩
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        (q : Set (M.RefinedVertex f))) = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxparent : x ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
          convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
        ⟨M.convexHull_child_subset_parent f T hs hx.1,
          M.convexHull_child_subset_parent f U hq hx.2⟩
      rw [hparents] at hxparent
      simp at hxparent
    · exact Set.empty_subset _
  have hsq : s ∩ q = ∅ := by
    ext v
    constructor
    · intro hv
      have hv' := Finset.mem_inter.mp hv
      have hvparent : (v : Plane) ∈
          convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
            convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
        ⟨M.child_vertex_mem_parent f T hs hv'.1,
          M.child_vertex_mem_parent f U hq hv'.2⟩
      rw [hparents] at hvparent
      simp at hvparent
    · intro hv
      simp at hv
  rw [hinter, hsq]
  simp

theorem lineRefinementTriangles_inter_of_parent_inter_card_one
    (T U : M.Triangle) (hcard : (T.1 ∩ U.1).card = 1)
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.localMeshTriangles f T)
    (hq : q ∈ M.localMeshTriangles f U) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  classical
  obtain ⟨a, hea⟩ := Finset.card_eq_one.mp hcard
  have haT : a ∈ T.1 := Finset.mem_of_mem_inter_left (by rw [hea]; simp)
  have haU : a ∈ U.1 := Finset.mem_of_mem_inter_right (by rw [hea]; simp)
  have harangeT : a ∈ Set.range (M.orderedVertex T) := by
    rw [M.range_orderedVertex T]
    exact haT
  have harangeU : a ∈ Set.range (M.orderedVertex U) := by
    rw [M.range_orderedVertex U]
    exact haU
  obtain ⟨iT, hiT⟩ := harangeT
  obtain ⟨iU, hiU⟩ := harangeU
  have hparents := M.triangle_inter T.1 T.2 U.1 U.2
  rw [hea] at hparents
  simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton] at hparents
  apply Set.Subset.antisymm
  · intro x hx
    have hxparent : x ∈ convexHull ℝ (M.position '' (T.1 : Set M.Vertex)) ∩
        convexHull ℝ (M.position '' (U.1 : Set M.Vertex)) :=
      ⟨M.convexHull_child_subset_parent f T hs hx.1,
        M.convexHull_child_subset_parent f U hq hx.2⟩
    rw [hparents] at hxparent
    have hxa : x = M.position a := by simpa using hxparent
    have haS : M.oldRefinedVertex f a ∈ s := by
      rw [← hiT]
      apply M.old_vertex_mem_child_of_position_mem f T iT hs
      simpa [hiT, hxa] using hx.1
    have haQ : M.oldRefinedVertex f a ∈ q := by
      rw [← hiU]
      apply M.old_vertex_mem_child_of_position_mem f U iU hq
      simpa [hiU, hxa] using hx.2
    apply subset_convexHull ℝ
    exact ⟨M.oldRefinedVertex f a, Finset.mem_inter.mpr ⟨haS, haQ⟩,
      by simpa using hxa.symm⟩
  · intro x hx
    exact ⟨convexHull_mono (Set.image_mono Finset.inter_subset_left) hx,
      convexHull_mono (Set.image_mono Finset.inter_subset_right) hx⟩

/-- All maximal triangles of the coherent line refinement. -/
noncomputable def lineRefinementTriangles : Finset (Finset (M.RefinedVertex f)) :=
  Finset.univ.biUnion fun t : M.Triangle => M.localMeshTriangles f t

theorem mem_lineRefinementTriangles_iff {s : Finset (M.RefinedVertex f)} :
    s ∈ M.lineRefinementTriangles f ↔
      ∃ t : M.Triangle, s ∈ M.localMeshTriangles f t := by
  constructor
  · intro hs
    obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp hs
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ht⟩

theorem card_of_mem_lineRefinementTriangles {s : Finset (M.RefinedVertex f)}
    (hs : s ∈ M.lineRefinementTriangles f) : s.card = 3 := by
  obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.card_of_mem_localMeshTriangles f t ht

theorem affineIndependent_of_mem_lineRefinementTriangles
    {s : Finset (M.RefinedVertex f)} (hs : s ∈ M.lineRefinementTriangles f) :
    AffineIndependent ℝ fun v : s => (v.1 : Plane) := by
  obtain ⟨t, ht⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.affineIndependent_of_mem_localMeshTriangles f t ht

theorem lineRefinementTriangles_support :
    (⋃ s ∈ M.lineRefinementTriangles f,
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f)))) =
      M.toPlaneComplex.support := by
  rw [M.toPlaneComplex_support]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
    refine ⟨t.1, t.2, ?_⟩
    rw [← M.localMeshTriangles_support f t]
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hst, hxs⟩⟩
  · rintro ⟨t, ht, hxt⟩
    let T : M.Triangle := ⟨t, ht⟩
    rw [← M.localMeshTriangles_support f T] at hxt
    obtain ⟨s, hxt⟩ := Set.mem_iUnion.mp hxt
    obtain ⟨hs, hxs⟩ := Set.mem_iUnion.mp hxt
    exact ⟨s, M.mem_lineRefinementTriangles_iff f |>.mpr ⟨T, hs⟩, hxs⟩

theorem lineRefinementTriangles_inter
    {s q : Finset (M.RefinedVertex f)} (hs : s ∈ M.lineRefinementTriangles f)
    (hq : q ∈ M.lineRefinementTriangles f) :
    convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (s : Set (M.RefinedVertex f))) ∩
        convexHull ℝ (((↑) : M.RefinedVertex f → Plane) '' (q : Set (M.RefinedVertex f))) =
      convexHull ℝ (((↑) : M.RefinedVertex f → Plane) ''
        ((s ∩ q : Finset (M.RefinedVertex f)) : Set (M.RefinedVertex f))) := by
  obtain ⟨T, hsT⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  obtain ⟨U, hqU⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hq
  by_cases hTU : T = U
  · subst U
    exact M.localMeshTriangles_inter f T hsT hqU
  · have hle : (T.1 ∩ U.1).card ≤ 3 := by
      calc
        (T.1 ∩ U.1).card ≤ T.1.card := Finset.card_le_card Finset.inter_subset_left
        _ = 3 := M.card_triangle T.1 T.2
    have hne3 : (T.1 ∩ U.1).card ≠ 3 := by
      intro hc
      have hT : T.1 ∩ U.1 = T.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by rw [M.card_triangle T.1 T.2, hc])
      have hU : T.1 ∩ U.1 = U.1 := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_right (by rw [M.card_triangle U.1 U.2, hc])
      apply hTU
      apply Subtype.ext
      exact hT.symm.trans hU
    have hcases : (T.1 ∩ U.1).card = 0 ∨ (T.1 ∩ U.1).card = 1 ∨
        (T.1 ∩ U.1).card = 2 := by omega
    rcases hcases with hc | hc | hc
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_zero f T U hc hsT hqU
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_one f T U hc hsT hqU
    · exact M.lineRefinementTriangles_inter_of_parent_inter_card_two f T U hc hsT hqU

/-- Subdivision of a finite triangle mesh by one affine line transverse to its old edges. -/
noncomputable def lineRefinementMesh : TriangleMesh where
  Vertex := M.RefinedVertex f
  position := (↑)
  position_injective := Subtype.val_injective
  triangles := M.lineRefinementTriangles f
  card_triangle := fun _ hs => M.card_of_mem_lineRefinementTriangles f hs
  affineIndependent_triangle := fun _ hs =>
    M.affineIndependent_of_mem_lineRefinementTriangles f hs
  triangle_inter := fun _ hs _ hq => M.lineRefinementTriangles_inter f hs hq

theorem lineRefinementMesh_support :
    (M.lineRefinementMesh f).toPlaneComplex.support = M.toPlaneComplex.support := by
  rw [TriangleMesh.toPlaneComplex_support]
  exact M.lineRefinementTriangles_support f

/-- Cutting every triangle of a mesh by one affine line gives a subdivision of the original
plane complex. -/
theorem lineRefinementMesh_subdivides :
    (M.lineRefinementMesh f).toPlaneComplex.Subdivides M.toPlaneComplex := by
  constructor
  · exact M.lineRefinementMesh_support f
  · intro s hs
    obtain ⟨-, u, hu, hsu⟩ :=
      (M.lineRefinementMesh f).mem_faces_iff.mp hs
    obtain ⟨t, hut⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hu
    refine ⟨t.1, M.mem_faces_iff.mpr ⟨?_, t.1, t.2, subset_rfl⟩, ?_⟩
    · exact Finset.card_pos.mp (by rw [M.card_triangle t.1 t.2]; omega)
    · exact (convexHull_mono (Set.image_mono hsu)).trans
        (M.convexHull_child_subset_parent f t hut)

theorem lineRefinementMesh_isMonochromatic :
    (M.lineRefinementMesh f).IsMonochromatic f := by
  intro s hs
  obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  exact M.localMeshTriangles_monochromatic f t s hst

theorem lineRefinementMesh_preserves_monochromatic (g : Plane →ᵃ[ℝ] ℝ)
    (hM : M.IsMonochromatic g) : (M.lineRefinementMesh f).IsMonochromatic g := by
  intro s hs
  obtain ⟨t, hst⟩ := M.mem_lineRefinementTriangles_iff f |>.mp hs
  rcases hM t.1 t.2 with ht | ht
  · left
    intro v hv
    have hvparent := M.child_vertex_mem_parent f t hst hv
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage g) hvparent
    rintro x ⟨w, hw, rfl⟩
    exact ht w hw
  · right
    intro v hv
    have hvparent := M.child_vertex_mem_parent f t hst hv
    apply convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage g) hvparent
    rintro x ⟨w, hw, rfl⟩
    exact ht w hw

/-- Successively subdivide a mesh by a finite list of affine lines. -/
noncomputable def refineByLines : TriangleMesh → List (Plane →ᵃ[ℝ] ℝ) → TriangleMesh
  | M, [] => M
  | M, g :: gs => refineByLines (M.lineRefinementMesh g) gs

theorem refineByLines_support (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (M.refineByLines lines).toPlaneComplex.support = M.toPlaneComplex.support := by
  induction lines generalizing M with
  | nil => rfl
  | cons g gs ih =>
      rw [refineByLines, ih, lineRefinementMesh_support]

/-- Successive line cuts remain a subdivision of the original mesh. -/
theorem refineByLines_subdivides (lines : List (Plane →ᵃ[ℝ] ℝ)) :
    (M.refineByLines lines).toPlaneComplex.Subdivides M.toPlaneComplex := by
  induction lines generalizing M with
  | nil => exact PlaneComplex.Subdivides.refl M.toPlaneComplex
  | cons g gs ih =>
      change (M.lineRefinementMesh g).refineByLines gs |>.toPlaneComplex |>.Subdivides
        M.toPlaneComplex
      exact (ih (M := M.lineRefinementMesh g)).trans (M.lineRefinementMesh_subdivides g)

theorem refineByLines_preserves_monochromatic
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (g : Plane →ᵃ[ℝ] ℝ)
    (hM : M.IsMonochromatic g) : (M.refineByLines lines).IsMonochromatic g := by
  induction lines generalizing M with
  | nil => exact hM
  | cons f fs ih =>
      exact ih (M := M.lineRefinementMesh f)
        (M.lineRefinementMesh_preserves_monochromatic f g hM)

theorem refineByLines_isMonochromatic_of_mem
    (lines : List (Plane →ᵃ[ℝ] ℝ)) {g : Plane →ᵃ[ℝ] ℝ} (hg : g ∈ lines) :
    (M.refineByLines lines).IsMonochromatic g := by
  induction lines generalizing M with
  | nil => simp at hg
  | cons h hs ih =>
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact (M.lineRefinementMesh g).refineByLines_preserves_monochromatic hs g
          (M.lineRefinementMesh_isMonochromatic g)
      · exact ih (M := M.lineRefinementMesh h) hg

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
