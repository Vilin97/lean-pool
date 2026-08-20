/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ElementaryMove

/-!
# Transporting the elementary move to a thin kite

The fixed diamond used to prove the barycentric fan move is too large for the relative
Schoenflies induction.  This file transports it piecewise-affinely to a kite whose lower and
upper margins are an arbitrary positive `δ`.  The two halves of the outer kite form a
two-triangle mesh, so the transport is supplied by the canonical realization homeomorphism.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Left, right, top, and bottom vertices of an axis-aligned kite. -/
def axisKitePosition (lo hi : ℝ) : Fin 4 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 hi, planePoint 0 lo]

@[simp] theorem axisKitePosition_zero (lo hi : ℝ) :
    axisKitePosition lo hi 0 = planePoint (-1) 0 := rfl

@[simp] theorem axisKitePosition_one (lo hi : ℝ) :
    axisKitePosition lo hi 1 = planePoint 1 0 := rfl

@[simp] theorem axisKitePosition_two (lo hi : ℝ) :
    axisKitePosition lo hi 2 = planePoint 0 hi := rfl

@[simp] theorem axisKitePosition_three (lo hi : ℝ) :
    axisKitePosition lo hi 3 = planePoint 0 lo := rfl

/-- The `axisKiteTriangles` declaration. -/
def axisKiteTriangles : Finset (Finset (Fin 4)) :=
  {{0, 2, 3}, {1, 2, 3}}

/-- The `axisKitePatch` declaration. -/
def axisKitePatch (lo hi : ℝ) : Set Plane :=
  convexHull ℝ (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∪
    convexHull ℝ (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _))

private theorem affineIndependent_finset_of_range_kite {V : Type}
    (position : V → Plane) {t : Finset V} (p : Fin 3 → V)
    (hp : AffineIndependent ℝ (position ∘ p)) (hrange : Set.range p = (t : Set V)) :
    AffineIndependent ℝ fun v : t => position v := by
  classical
  let eFun : Fin 3 → t := fun i => ⟨p i, by
    change p i ∈ (t : Set V)
    rw [← hrange]
    exact Set.mem_range_self i⟩
  have heBijective : Function.Bijective eFun := by
    constructor
    · intro i j hij
      apply hp.injective
      exact congrArg (fun v : t => position v) hij
    · rintro ⟨v, hv⟩
      have : v ∈ Set.range p := by rwa [hrange]
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, rfl⟩
  let e : Fin 3 ≃ t := Equiv.ofBijective eFun heBijective
  apply (affineIndependent_equiv e).mp
  convert hp using 1
  funext i
  rfl

theorem axisKitePosition_injective {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi) :
    Function.Injective (axisKitePosition lo hi) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [axisKitePosition, planePoint] at hij ⊢
  all_goals linarith

theorem axisKite_affineIndependent {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi)
    {t : Finset (Fin 4)} (ht : t ∈ axisKiteTriangles) :
    AffineIndependent ℝ fun v : t => axisKitePosition lo hi v := by
  simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · apply affineIndependent_finset_of_range_kite (axisKitePosition lo hi) ![0, 2, 3]
    · have h : AffineIndependent ℝ ![axisKitePosition lo hi 0,
          axisKitePosition lo hi 2, axisKitePosition lo hi 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [axisKitePosition_zero, axisKitePosition_two, axisKitePosition_three,
          planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp
  · apply affineIndependent_finset_of_range_kite (axisKitePosition lo hi) ![1, 2, 3]
    · have h : AffineIndependent ℝ ![axisKitePosition lo hi 1,
          axisKitePosition lo hi 2, axisKitePosition lo hi 3] := by
        apply affineIndependent_plane_triple_of_det_ne_zero
        simp only [axisKitePosition_one, axisKitePosition_two, axisKitePosition_three,
          planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
        linarith
      convert h using 1; funext i; fin_cases i <;> rfl
    · ext v
      fin_cases v <;> simp

theorem axisKite_inter {lo hi : ℝ} (hlo : lo < 0) (hhi : 0 < hi) :
    convexHull ℝ (axisKitePosition lo hi '' (({0, 2, 3} : Finset (Fin 4)) : Set _)) ∩
        convexHull ℝ (axisKitePosition lo hi '' (({1, 2, 3} : Finset (Fin 4)) : Set _)) =
      convexHull ℝ (axisKitePosition lo hi ''
        ((({0, 2, 3} : Finset (Fin 4)) ∩ {1, 2, 3} : Finset (Fin 4)) : Set _)) := by
  apply convexHull_image_inter_of_affine_separation (axisKitePosition lo hi)
    (axisKitePosition_injective hlo hhi) {0, 2, 3} {1, 2, 3} (-diamondVerticalAffine)
  all_goals
    intro v hv
    fin_cases v <;> simp [axisKitePosition] at hv ⊢

/-- The `axisKiteMesh` declaration. -/
noncomputable def axisKiteMesh (lo hi : ℝ) (hlo : lo < 0) (hhi : 0 < hi) : TriangleMesh where
  Vertex := Fin 4
  position := axisKitePosition lo hi
  position_injective := axisKitePosition_injective hlo hhi
  triangles := axisKiteTriangles
  card_triangle := by
    intro t ht
    simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide
  affineIndependent_triangle := fun t ht => axisKite_affineIndependent hlo hhi ht
  triangle_inter := by
    intro s hs t ht
    simp only [axisKiteTriangles, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simp
    · exact axisKite_inter hlo hhi
    · simpa [Set.inter_comm, Finset.inter_comm] using axisKite_inter hlo hhi
    · simp

theorem axisKiteMesh_support (lo hi : ℝ) (hlo : lo < 0) (hhi : 0 < hi) :
    (axisKiteMesh lo hi hlo hhi).toPlaneComplex.support = axisKitePatch lo hi := by
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [axisKiteMesh]
  change (⋃ t ∈ axisKiteTriangles,
    convexHull ℝ (axisKitePosition lo hi '' (t : Set (Fin 4)))) = _
  ext p
  simp [axisKiteTriangles, axisKitePatch]

theorem axisKitePatch_negTwo_two : axisKitePatch (-2) 2 = diamondPatch := by
  unfold axisKitePatch diamondPatch diamondLeftRegion diamondRightRegion
  congr 1 <;> apply congrArg (convexHull ℝ) <;> ext p <;>
    simp [axisKitePosition] <;> tauto

/-- Vertical scale used to compress the fixed diamond to a kite with margins `δ`. -/
noncomputable def thinKiteScale (δ : ℝ) : ℝ := (1 + 2 * δ) / 4

/-- The global piecewise-affine transport.  Writing the two affine pieces with `|x|` makes
continuity across the vertical diagonal immediate. -/
noncomputable def thinKiteMap (δ : ℝ) (p : Plane) : Plane :=
  planePoint (p 0) (thinKiteScale δ * p 1 + (1 - |p 0|) / 2)

/-- The `thinKiteInv` declaration. -/
noncomputable def thinKiteInv (δ : ℝ) (p : Plane) : Plane :=
  planePoint (p 0) ((p 1 - (1 - |p 0|) / 2) / thinKiteScale δ)

theorem thinKiteScale_pos {δ : ℝ} (hδ : 0 < δ) : 0 < thinKiteScale δ := by
  unfold thinKiteScale
  positivity

/-- The `thinKiteGlobalHomeomorph` declaration. -/
noncomputable def thinKiteGlobalHomeomorph (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane := by
  have hs : thinKiteScale δ ≠ 0 := (thinKiteScale_pos hδ).ne'
  have hleft : Function.LeftInverse (thinKiteInv δ) (thinKiteMap δ) := by
    intro p
    ext i
    fin_cases i
    · simp [thinKiteMap, thinKiteInv]
    · simp [thinKiteMap, thinKiteInv]
      field_simp [hs]
  have hright : Function.RightInverse (thinKiteInv δ) (thinKiteMap δ) := by
    intro p
    ext i
    fin_cases i
    · simp [thinKiteMap, thinKiteInv]
    · simp [thinKiteMap, thinKiteInv]
      field_simp [hs]
      ring
  exact
    { toEquiv := Equiv.mk (thinKiteMap δ) (thinKiteInv δ) hleft hright
      continuous_toFun := by
        unfold thinKiteMap thinKiteScale planePoint
        fun_prop
      continuous_invFun := by
        unfold thinKiteInv thinKiteScale planePoint
        fun_prop }

/-- The thin kite is the image of the fixed diamond under the explicit transport. -/
noncomputable def thinKitePatch (δ : ℝ) : Set Plane := thinKiteMap δ '' diamondPatch

/-- Every point of the thin kite lies in the tangent cone at its left base vertex. -/
theorem thinKitePatch_subset_leftCone {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane}
    (hp : p ∈ thinKitePatch δ) :
    0 ≤ p 0 + 1 ∧ -δ * (p 0 + 1) ≤ p 1 ∧ p 1 ≤ (1 + δ) * (p 0 + 1) := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  have hs : thinKiteScale δ = (1 + 2 * δ) / 4 := rfl
  constructor
  · simp only [thinKiteMap, planePoint_apply_zero]
    linarith
  · constructor
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith

/-- Every point of the thin kite lies in the tangent cone at its right base vertex. -/
theorem thinKitePatch_subset_rightCone {δ : ℝ} (hδ : 0 ≤ δ) {p : Plane}
    (hp : p ∈ thinKitePatch δ) :
    0 ≤ 1 - p 0 ∧ -δ * (1 - p 0) ≤ p 1 ∧ p 1 ≤ (1 + δ) * (1 - p 0) := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  have hs : thinKiteScale δ = (1 + 2 * δ) / 4 := rfl
  constructor
  · simp only [thinKiteMap, planePoint_apply_zero]
    linarith
  · constructor
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith
    · simp only [thinKiteMap, planePoint_apply_zero, planePoint_apply_one]
      rw [hs]
      by_cases hx : q 0 ≤ 0
      · rw [abs_of_nonpos hx]
        nlinarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        rw [abs_of_nonneg hx']
        nlinarith

/-- The triangle onto which the thin kite collapses when `δ = 0`. -/
def kiteTrianglePosition : Fin 3 → Plane :=
  ![planePoint (-1) 0, planePoint 1 0, planePoint 0 1]

theorem kiteTrianglePosition_affineIndependent :
    AffineIndependent ℝ kiteTrianglePosition := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  norm_num [kiteTrianglePosition, planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]

/-- A ray from the left base vertex whose coordinate direction lies in the original triangle
cone enters the triangle immediately. -/
theorem exists_leftBase_openSegment_mem_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint (-1) 0) (hx : 0 < q 0 + 1)
    (hy0 : 0 ≤ q 1) (hyx : q 1 ≤ q 0 + 1) :
    ∃ p ∈ segment ℝ (planePoint (-1) 0) q \ {planePoint (-1) 0},
      p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  let dx := q 0 + 1
  let dy := q 1
  let t : ℝ := 1 / (1 + dx + dy)
  have hden : 0 < 1 + dx + dy := by dsimp [dx, dy]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hden]
    dsimp [dx, dy]
    linarith
  let p := AffineMap.lineMap (planePoint (-1) 0) q t
  have hpSegment : p ∈ segment ℝ (planePoint (-1) 0) q := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hpNe : p ≠ planePoint (-1) 0 := by
    intro hp
    have hinj := AffineMap.lineMap_injective ℝ hq.symm
    apply ht.ne'
    apply hinj
    dsimp [p] at hp
    simpa using hp
  let w : Fin 3 → ℝ :=
    ![1 - t * (dx + dy) / 2, t * (dx - dy) / 2, t * dy]
  have hpTriangle : p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition p w
    · intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sub_nonneg, w,
                        Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
      · have htd : t * (dx + dy) < 1 := by
          dsimp [t]
          field_simp
          nlinarith
        linarith
      · nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hyx)]
      · exact mul_nonneg ht.le hy0
    · simp [w]
      ring
    · ext i
      fin_cases i <;>
        simp [w, p, kiteTrianglePosition, AffineMap.lineMap_apply_module,
          planePoint, dx, dy]
      all_goals ring
  exact ⟨p, ⟨hpSegment, by simpa using hpNe⟩, hpTriangle⟩

/-- A ray from the right base vertex whose direction lies in the original triangle cone enters
the triangle immediately. -/
theorem exists_rightBase_openSegment_mem_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint 1 0) (hx : 0 < 1 - q 0)
    (hy0 : 0 ≤ q 1) (hyx : q 1 ≤ 1 - q 0) :
    ∃ p ∈ segment ℝ (planePoint 1 0) q \ {planePoint 1 0},
      p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  let dx := 1 - q 0
  let dy := q 1
  let t : ℝ := 1 / (1 + dx + dy)
  have hden : 0 < 1 + dx + dy := by dsimp [dx, dy]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one hden]
    dsimp [dx, dy]
    linarith
  let p := AffineMap.lineMap (planePoint 1 0) q t
  have hpSegment : p ∈ segment ℝ (planePoint 1 0) q := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  have hpNe : p ≠ planePoint 1 0 := by
    intro hp
    have hinj := AffineMap.lineMap_injective ℝ hq.symm
    apply ht.ne'
    apply hinj
    dsimp [p] at hp
    simpa using hp
  let w : Fin 3 → ℝ :=
    ![t * (dx - dy) / 2, 1 - t * (dx + dy) / 2, t * dy]
  have hpTriangle : p ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
    apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition p w
    · intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, w, Fin.mk_one,
                        Matrix.cons_val_one, sub_nonneg, Fin.reduceFinMk, Matrix.cons_val]
      · nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hyx)]
      · have htd : t * (dx + dy) < 1 := by
          dsimp [t]
          field_simp
          nlinarith
        linarith
      · exact mul_nonneg ht.le hy0
    · simp [w]
      ring
    · ext i
      fin_cases i <;>
        simp [w, p, kiteTrianglePosition, AffineMap.lineMap_apply_module,
          planePoint, dx, dy]
      all_goals ring
  exact ⟨p, ⟨hpSegment, by simpa using hpNe⟩, hpTriangle⟩

/-- If a segment leaves the left base vertex without entering the triangle, its direction is
strictly outside the triangle tangent cone. -/
theorem leftBase_direction_outside_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint (-1) 0)
    (havoid : segment ℝ (planePoint (-1) 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0}) :
    q 0 + 1 ≤ 0 ∨
      (0 < q 0 + 1 ∧ (q 1 < 0 ∨ q 0 + 1 < q 1)) := by
  by_cases hx : q 0 + 1 ≤ 0
  · exact Or.inl hx
  right
  have hxpos : 0 < q 0 + 1 := lt_of_not_ge hx
  refine ⟨hxpos, ?_⟩
  by_contra hdir
  push Not at hdir
  obtain ⟨p, hpSegment, hpTriangle⟩ :=
    exists_leftBase_openSegment_mem_kiteTriangle hq hxpos hdir.1 hdir.2
  have hpLeft := havoid ⟨hpSegment.1, hpTriangle⟩
  exact hpSegment.2 (by simpa using hpLeft)

theorem rightBase_direction_outside_kiteTriangle {q : Plane}
    (hq : q ≠ planePoint 1 0)
    (havoid : segment ℝ (planePoint 1 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0}) :
    1 - q 0 ≤ 0 ∨
      (0 < 1 - q 0 ∧ (q 1 < 0 ∨ 1 - q 0 < q 1)) := by
  by_cases hx : 1 - q 0 ≤ 0
  · exact Or.inl hx
  right
  have hxpos : 0 < 1 - q 0 := lt_of_not_ge hx
  refine ⟨hxpos, ?_⟩
  by_contra hdir
  push Not at hdir
  obtain ⟨p, hpSegment, hpTriangle⟩ :=
    exists_rightBase_openSegment_mem_kiteTriangle hq hxpos hdir.1 hdir.2
  have hpRight := havoid ⟨hpSegment.1, hpTriangle⟩
  exact hpSegment.2 (by simpa using hpRight)

/-- A segment leaving the left base vertex outside the triangle misses every sufficiently thin
kite except at that vertex. -/
theorem exists_thinKitePatch_inter_leftSegment_eq_singleton {q : Plane}
    (hq : q ≠ planePoint (-1) 0)
    (havoid : segment ℝ (planePoint (-1) 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ (planePoint (-1) 0) q = {planePoint (-1) 0} := by
  rcases leftBase_direction_outside_kiteTriangle hq havoid with hx | ⟨hx, hy | hy⟩
  · refine ⟨1, by norm_num, fun δ hδ _ => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hdx0 : q 0 + 1 = 0 := by
        rw [hcoord0] at hcone
        nlinarith
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hdx0, mul_zero] at hcone
      rw [hcoord1] at hcone
      have hdy0 : q 1 = 0 := by nlinarith
      exfalso
      apply hq
      apply plane_ext
      · simp only [planePoint_apply_zero]
        linarith
      · simpa [planePoint] using hdy0
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := -q 1 / (q 0 + 1)
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos (neg_pos.mpr hy) hx
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : δ * (q 0 + 1) < -q 1 := by
        dsimp [ε] at hδε
        exact (lt_div_iff₀ hx).mp hδε
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := q 1 / (q 0 + 1) - 1
    have hε : 0 < ε := by
      dsimp [ε]
      rw [sub_pos, one_lt_div hx]
      exact hy
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpLeft : p = planePoint (-1) 0
      · simp [hpLeft]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpLeft
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_leftCone hδ.le hpPatch
      have hcoord0 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 0 + 1 = t * (q 0 + 1) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint (-1) 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : (1 + δ) * (q 0 + 1) < q 1 := by
        dsimp [ε] at hδε
        rw [lt_sub_iff_add_lt] at hδε
        have := (lt_div_iff₀ hx).mp hδε
        nlinarith
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint (-1) 0, Or.inl <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩

/-- A segment leaving the right base vertex outside the triangle misses every sufficiently thin
kite except at that vertex. -/
theorem exists_thinKitePatch_inter_rightSegment_eq_singleton {q : Plane}
    (hq : q ≠ planePoint 1 0)
    (havoid : segment ℝ (planePoint 1 0) q ∩
      convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ (planePoint 1 0) q = {planePoint 1 0} := by
  rcases rightBase_direction_outside_kiteTriangle hq havoid with hx | ⟨hx, hy | hy⟩
  · refine ⟨1, by norm_num, fun δ hδ _ => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hdx0 : 1 - q 0 = 0 := by
        rw [hcoord0] at hcone
        nlinarith
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hdx0, mul_zero] at hcone
      rw [hcoord1] at hcone
      have hdy0 : q 1 = 0 := by nlinarith
      exfalso
      apply hq
      apply plane_ext
      · simp only [planePoint_apply_zero]
        linarith
      · simpa [planePoint] using hdy0
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := -q 1 / (1 - q 0)
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos (neg_pos.mpr hy) hx
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : δ * (1 - q 0) < -q 1 := by
        dsimp [ε] at hδε
        exact (lt_div_iff₀ hx).mp hδε
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩
  · let ε := q 1 / (1 - q 0) - 1
    have hε : 0 < ε := by
      dsimp [ε]
      rw [sub_pos, one_lt_div hx]
      exact hy
    refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
    apply Set.Subset.antisymm
    · rintro p ⟨hpPatch, hpSegment⟩
      by_cases hpRight : p = planePoint 1 0
      · simp [hpRight]
      rw [segment_eq_image_lineMap] at hpSegment
      obtain ⟨t, ht, rfl⟩ := hpSegment
      have htne : t ≠ 0 := by
        intro ht0
        apply hpRight
        rw [ht0, AffineMap.lineMap_apply_zero]
      have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
      have hcone := thinKitePatch_subset_rightCone hδ.le hpPatch
      have hcoord0 :
          1 - (AffineMap.lineMap (planePoint 1 0) q t) 0 = t * (1 - q 0) := by
        simp [AffineMap.lineMap_apply_module, planePoint]
        ring
      have hcoord1 :
          (AffineMap.lineMap (planePoint 1 0) q t) 1 = t * q 1 := by
        simp [AffineMap.lineMap_apply_module, planePoint]
      rw [hcoord0, hcoord1] at hcone
      have hmargin : (1 + δ) * (1 - q 0) < q 1 := by
        dsimp [ε] at hδε
        rw [lt_sub_iff_add_lt] at hδε
        have := (lt_div_iff₀ hx).mp hδε
        nlinarith
      exfalso
      nlinarith
    · intro p hp
      rw [Set.mem_singleton_iff] at hp
      subst p
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      exact ⟨planePoint 1 0, Or.inr <|
        subset_convexHull ℝ _ ⟨2, rfl⟩, by
          simp [thinKiteMap, planePoint]⟩

theorem thinKiteMap_zero_mem_triangle {q : Plane} (hq : q ∈ diamondPatch) :
    thinKiteMap 0 q ∈ convexHull ℝ (Set.range kiteTrianglePosition) := by
  rw [diamondPatch_eq_inDiamond] at hq
  rcases hq with ⟨hUR, hUL, hLR, hLL⟩
  rw [diamondSlackUR_eq] at hUR
  rw [diamondSlackUL_eq] at hUL
  rw [diamondSlackLR_eq] at hLR
  rw [diamondSlackLL_eq] at hLL
  let r := thinKiteMap 0 q
  let w : Fin 3 → ℝ := ![(1 - r 1 - r 0) / 2, (1 - r 1 + r 0) / 2, r 1]
  apply mem_convexHull_range_fin3_of_weights kiteTrianglePosition r w
  · intro i
    fin_cases i <;> simp [w]
    all_goals
      by_cases hx : q 0 ≤ 0
      · simp [r, thinKiteMap, thinKiteScale, planePoint, abs_of_nonpos hx]
        linarith
      · have hx' : 0 ≤ q 0 := le_of_not_ge hx
        simp [r, thinKiteMap, thinKiteScale, planePoint, abs_of_nonneg hx']
        linarith
  · simp [w]
    ring
  · ext i
    fin_cases i <;> simp [w, r, kiteTrianglePosition, thinKiteMap, planePoint]
    all_goals ring

/-- Every open neighborhood of the limiting triangle contains all sufficiently thin normalized
kites. -/
theorem exists_thinKitePatch_subset_open_normalized (U : Set Plane) (hU : IsOpen U)
    (htriangle : convexHull ℝ (Set.range kiteTrianglePosition) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε → thinKitePatch δ ⊆ U := by
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  have hcontinuous : Continuous fun z : ℝ × Plane => thinKiteMap z.1 z.2 := by
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop
  have heventually : ∀ᶠ δ in nhds (0 : ℝ), ∀ q ∈ diamondPatch, thinKiteMap δ q ∈ U := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro q hq
    apply hcontinuous.continuousAt.eventually
    exact hU.mem_nhds (htriangle (thinKiteMap_zero_mem_triangle hq))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδball : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [δ]
    rw [abs_of_nonneg (by positivity)]
    linarith
  refine ⟨δ, hδ, fun η _ hη p hp => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hp
  have hηball : η ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos]
    · dsimp [δ] at hη
      linarith
    · assumption
  exact hball hηball q hq

/-- A finite-mesh edge which meets the limiting triangle in at most one base endpoint is
avoided by every sufficiently thin kite, apart from that endpoint. -/
theorem exists_thinKitePatch_inter_segment_subset_baseEndpoints {a b : Plane}
    (hab : a ≠ b)
    (hinter : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
      {planePoint (-1) 0, planePoint 1 0})
    (hleftEndpoint : planePoint (-1) 0 ∈ segment ℝ a b →
      a = planePoint (-1) 0 ∨ b = planePoint (-1) 0)
    (hrightEndpoint : planePoint 1 0 ∈ segment ℝ a b →
      a = planePoint 1 0 ∨ b = planePoint 1 0)
    (hnotBoth : ¬(planePoint (-1) 0 ∈ segment ℝ a b ∧
      planePoint 1 0 ∈ segment ℝ a b)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      thinKitePatch δ ∩ segment ℝ a b ⊆
        {planePoint (-1) 0, planePoint 1 0} := by
  by_cases hleft : planePoint (-1) 0 ∈ segment ℝ a b
  · have hright : planePoint 1 0 ∉ segment ℝ a b :=
      fun h => hnotBoth ⟨hleft, h⟩
    have havoid : segment ℝ a b ∩ convexHull ℝ (Set.range kiteTrianglePosition) ⊆
        {planePoint (-1) 0} := by
      intro p hp
      have hpSegment := hp.1
      rcases hinter hp with hp | hp
      · simpa using hp
      · exact False.elim (hright (hp ▸ hpSegment))
    rcases hleftEndpoint hleft with ha | hb
    · subst a
      obtain ⟨ε, hε, hεavoid⟩ :=
        exists_thinKitePatch_inter_leftSegment_eq_singleton hab.symm havoid
      refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
      rw [hεavoid δ hδ hδε]
      simp
    · subst b
      have havoid' : segment ℝ (planePoint (-1) 0) a ∩
          convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint (-1) 0} := by
        rwa [segment_symm ℝ (planePoint (-1) 0) a]
      obtain ⟨ε, hε, hεavoid⟩ :=
        exists_thinKitePatch_inter_leftSegment_eq_singleton hab havoid'
      refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
      rw [segment_symm ℝ a (planePoint (-1) 0), hεavoid δ hδ hδε]
      simp
  · by_cases hright : planePoint 1 0 ∈ segment ℝ a b
    · have havoid : segment ℝ a b ∩
          convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0} := by
        intro p hp
        have hpSegment := hp.1
        rcases hinter hp with hp | hp
        · exact False.elim (hleft (hp ▸ hpSegment))
        · simpa using hp
      rcases hrightEndpoint hright with ha | hb
      · subst a
        obtain ⟨ε, hε, hεavoid⟩ :=
          exists_thinKitePatch_inter_rightSegment_eq_singleton hab.symm havoid
        refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
        rw [hεavoid δ hδ hδε]
        simp
      · subst b
        have havoid' : segment ℝ (planePoint 1 0) a ∩
            convexHull ℝ (Set.range kiteTrianglePosition) ⊆ {planePoint 1 0} := by
          rwa [segment_symm ℝ (planePoint 1 0) a]
        obtain ⟨ε, hε, hεavoid⟩ :=
          exists_thinKitePatch_inter_rightSegment_eq_singleton hab havoid'
        refine ⟨ε, hε, fun δ hδ hδε => ?_⟩
        rw [segment_symm ℝ a (planePoint 1 0), hεavoid δ hδ hδε]
        simp
    · have hdisjoint : Disjoint (segment ℝ a b)
          (convexHull ℝ (Set.range kiteTrianglePosition)) := by
        rw [Set.disjoint_left]
        intro p hpSegment hpTriangle
        rcases hinter ⟨hpSegment, hpTriangle⟩ with hp | hp
        · exact hleft (hp ▸ hpSegment)
        · exact hright (hp ▸ hpSegment)
      have hclosed : IsClosed (segment ℝ a b) := by
        rw [← convexHull_pair]
        exact (Set.Finite.isCompact_convexHull (𝕜 := ℝ) (by simp)).isClosed
      obtain ⟨ε, hε, hpatch⟩ := exists_thinKitePatch_subset_open_normalized
        (segment ℝ a b)ᶜ
        hclosed.isOpen_compl (by
          intro p hpTriangle hpSegment
          exact Set.disjoint_left.mp hdisjoint hpSegment hpTriangle)
      refine ⟨ε, hε, fun δ hδ hδε p hp => ?_⟩
      have hpCompl : p ∈ (segment ℝ a b)ᶜ := by
        exact hpatch δ hδ hδε hp.1
      exact False.elim (hpCompl hp.2)

/-- The `diamondOuterToThinKite` declaration. -/
noncomputable def diamondOuterToThinKite (δ : ℝ) (hδ : 0 < δ) :
    diamondPatch ≃ₜ thinKitePatch δ := by
  exact (thinKiteGlobalHomeomorph δ hδ).image diamondPatch

/-- The `thinKiteSource` declaration. -/
noncomputable def thinKiteSource (δ : ℝ) : ℝ := -2 / (1 + 2 * δ)

/-- The `thinKiteTarget` declaration. -/
noncomputable def thinKiteTarget (δ : ℝ) : ℝ := 2 / (1 + 2 * δ)

theorem thinKiteSource_lower {δ : ℝ} (hδ : 0 < δ) : -2 < thinKiteSource δ := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteSource, lt_div_iff₀ hd]
  nlinarith

theorem thinKiteSource_upper {δ : ℝ} (hδ : 0 < δ) : thinKiteSource δ < 2 := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteSource, div_lt_iff₀ hd]
  nlinarith

theorem thinKiteTarget_lower {δ : ℝ} (hδ : 0 < δ) : -2 < thinKiteTarget δ := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteTarget, lt_div_iff₀ hd]
  nlinarith

theorem thinKiteTarget_upper {δ : ℝ} (hδ : 0 < δ) : thinKiteTarget δ < 2 := by
  have hd : 0 < 1 + 2 * δ := by positivity
  rw [thinKiteTarget, div_lt_iff₀ hd]
  nlinarith

private noncomputable def diamondFanSpokeWeights (i : Fin 5) (c : ℝ) : Fin 5 → ℝ :=
  fun v => if v = i then 1 - c else if v = 4 then c else 0

private noncomputable def diamondFanLeftSpokeRealization (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x := diamondFanSpokeWeights 0 c
  refine ⟨x, ?_, {0, 4, 2}, ?_, ?_⟩
  · constructor
    · intro v
      fin_cases v <;> simp [x, diamondFanSpokeWeights] <;> linarith [hc.1, hc.2]
    · simp [x, diamondFanSpokeWeights, Fin.sum_univ_succ]
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    fin_cases v <;> simp [x, diamondFanSpokeWeights] at hv ⊢

private theorem diamondFanLeftSpokeRealization_baryEval (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanLeftSpokeRealization a ha0 ha1 c hc).1 =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c := by
  change (∑ v : Fin 5, diamondFanSpokeWeights 0 c v • diamondFanPosition a v) = _
  ext i
  fin_cases i <;>
    simp [diamondFanSpokeWeights, diamondFanPosition, AffineMap.lineMap_apply_module,
      Fin.sum_univ_succ, planePoint]

private noncomputable def diamondFanLeftSpokePoint (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    (diamondFanLeftSpokeRealization a ha0 ha1 c hc)

private theorem diamondFanLeftSpokePoint_val (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanLeftSpokePoint a ha0 ha1 c hc : Plane) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c :=
  diamondFanLeftSpokeRealization_baryEval a ha0 ha1 c hc

private theorem diamondFanAmbientHomeomorph_leftSpoke (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 b) c := by
  have hmem : AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c ∈
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support := by
    rw [← diamondFanLeftSpokePoint_val a ha0 ha1 c hc]
    exact (diamondFanLeftSpokePoint a ha0 ha1 c hc).property
  unfold diamondFanAmbientHomeomorph TriangleMesh.ambientRepositionHomeomorph
  apply Eq.trans (extendHomeomorphByIdentity_apply_mem _ _ _ hmem)
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c, hmem⟩ : Plane) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 b) c
  rw [diamondFanPatchHomeomorph_apply_val]
  have hz :
      (⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 a) c, hmem⟩ :
        (diamondFanMesh a ha0 ha1).toPlaneComplex.support) =
        diamondFanLeftSpokePoint a ha0 ha1 c hc := by
    apply Subtype.ext
    exact (diamondFanLeftSpokePoint_val a ha0 ha1 c hc).symm
  rw [hz]
  exact ((diamondFanMesh a ha0 ha1).coe_repositionHomeomorph_apply_realization
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanLeftSpokeRealization a ha0 ha1 c hc)).trans
      (diamondFanLeftSpokeRealization_baryEval b hb0 hb1 c hc)

private noncomputable def diamondFanRightSpokeRealization (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    GeometricRealization (Fin 5) (diamondFanMesh a ha0 ha1).toPlaneComplex.cells := by
  let x := diamondFanSpokeWeights 1 c
  refine ⟨x, ?_, {1, 2, 4}, ?_, ?_⟩
  · constructor
    · intro v
      fin_cases v <;> simp [x, diamondFanSpokeWeights] <;> linarith [hc.1, hc.2]
    · simp [x, diamondFanSpokeWeights, Fin.sum_univ_succ]
  · simp [PlaneComplex.cells, TriangleMesh.toPlaneComplex, TriangleMesh.faces,
      diamondFanMesh, diamondFanTriangles]
  · intro v hv
    fin_cases v <;> simp [x, diamondFanSpokeWeights] at hv ⊢

private theorem diamondFanRightSpokeRealization_baryEval (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.baryEval
        (diamondFanRightSpokeRealization a ha0 ha1 c hc).1 =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c := by
  change (∑ v : Fin 5, diamondFanSpokeWeights 1 c v • diamondFanPosition a v) = _
  ext i
  fin_cases i <;>
    simp [diamondFanSpokeWeights, diamondFanPosition, AffineMap.lineMap_apply_module,
      Fin.sum_univ_succ, planePoint]

private noncomputable def diamondFanRightSpokePoint (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanMesh a ha0 ha1).toPlaneComplex.support :=
  (diamondFanMesh a ha0 ha1).toPlaneComplex.realizationHomeomorph
    (diamondFanMesh a ha0 ha1).toPlaneComplex_isPure2
    (diamondFanRightSpokeRealization a ha0 ha1 c hc)

private theorem diamondFanRightSpokePoint_val (a : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (diamondFanRightSpokePoint a ha0 ha1 c hc : Plane) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c :=
  diamondFanRightSpokeRealization_baryEval a ha0 ha1 c hc

private theorem diamondFanAmbientHomeomorph_rightSpoke (a b : ℝ)
    (ha0 : -2 < a) (ha1 : a < 2) (hb0 : -2 < b) (hb1 : b < 2)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    diamondFanAmbientHomeomorph a b ha0 ha1 hb0 hb1
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 b) c := by
  have hmem : AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c ∈
      (diamondFanMesh a ha0 ha1).toPlaneComplex.support := by
    rw [← diamondFanRightSpokePoint_val a ha0 ha1 c hc]
    exact (diamondFanRightSpokePoint a ha0 ha1 c hc).property
  unfold diamondFanAmbientHomeomorph TriangleMesh.ambientRepositionHomeomorph
  apply Eq.trans (extendHomeomorphByIdentity_apply_mem _ _ _ hmem)
  change (diamondFanPatchHomeomorph a b ha0 ha1 hb0 hb1
    ⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c, hmem⟩ : Plane) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 b) c
  rw [diamondFanPatchHomeomorph_apply_val]
  have hz :
      (⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 a) c, hmem⟩ :
        (diamondFanMesh a ha0 ha1).toPlaneComplex.support) =
        diamondFanRightSpokePoint a ha0 ha1 c hc := by
    apply Subtype.ext
    exact (diamondFanRightSpokePoint_val a ha0 ha1 c hc).symm
  rw [hz]
  exact ((diamondFanMesh a ha0 ha1).coe_repositionHomeomorph_apply_realization
    (diamondFanPosition b) (diamondFanPosition_injective hb0 hb1)
    (diamondFanMesh b hb0 hb1).affineIndependent_triangle
    (diamondFanMesh b hb0 hb1).triangle_inter
    (diamondFanRightSpokeRealization a ha0 ha1 c hc)).trans
      (diamondFanRightSpokeRealization_baryEval b hb0 hb1 c hc)

@[simp] theorem thinKiteMap_source (δ : ℝ) (hδ : 0 < δ) :
    thinKiteMap δ (planePoint 0 (thinKiteSource δ)) = planePoint 0 0 := by
  ext i
  fin_cases i
  · simp [thinKiteMap]
  · simp only [thinKiteMap, thinKiteSource, Fin.isValue, planePoint_apply_zero, thinKiteScale,
      planePoint_apply_one, abs_zero, sub_zero, one_div, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

@[simp] theorem thinKiteMap_target (δ : ℝ) (hδ : 0 < δ) :
    thinKiteMap δ (planePoint 0 (thinKiteTarget δ)) = planePoint 0 1 := by
  ext i
  fin_cases i
  · simp [thinKiteMap]
  · simp only [thinKiteMap, thinKiteTarget, Fin.isValue, planePoint_apply_zero, thinKiteScale,
      planePoint_apply_one, abs_zero, sub_zero, one_div, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

theorem isClosed_thinKitePatch (δ : ℝ) : IsClosed (thinKitePatch δ) := by
  rw [thinKitePatch]
  have hcompact : IsCompact diamondPatch := by
    rw [← diamondFanMesh_support 0 (by norm_num) (by norm_num)]
    exact (diamondFanMesh 0 (by norm_num) (by norm_num)).toPlaneComplex.isCompact_support
  exact (hcompact.image (by
    unfold thinKiteMap thinKiteScale planePoint
    fun_prop)).isClosed

/-- The `thinKiteAmbientHomeomorph` declaration. -/
noncomputable def thinKiteAmbientHomeomorph (δ : ℝ) (hδ : 0 < δ) : Plane ≃ₜ Plane :=
  (thinKiteGlobalHomeomorph δ hδ).symm.trans
    ((diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
      (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
      (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)).trans
        (thinKiteGlobalHomeomorph δ hδ))

private theorem thinKiteInv_leftSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteInv δ (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 (thinKiteSource δ)) c := by
  have habs : |c - 1| = 1 - c := by
    rw [abs_of_nonpos]
    · ring
    · linarith [hc.2]
  ext i
  fin_cases i
  · simp [thinKiteInv, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteInv, planePoint, AffineMap.lineMap_apply_module, Fin.isValue,
      PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_neg,
      mul_one, neg_sub, mul_zero, add_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, habs, sub_sub_cancel, zero_sub, thinKiteScale,
      Fin.mk_one, thinKiteSource, zero_add]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteInv_rightSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteInv δ (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 (thinKiteSource δ)) c := by
  have habs : |1 - c| = 1 - c := abs_of_nonneg (by linarith [hc.2])
  ext i
  fin_cases i
  · simp [thinKiteInv, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteInv, planePoint, AffineMap.lineMap_apply_module, Fin.isValue,
      PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one,
      mul_zero, add_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, habs,
      sub_sub_cancel, zero_sub, thinKiteScale, Fin.mk_one, thinKiteSource, zero_add]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteMap_leftTargetSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteMap δ
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 (thinKiteTarget δ)) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 1) c := by
  have habs : |c - 1| = 1 - c := by
    rw [abs_of_nonpos]
    · ring
    · linarith [hc.2]
  ext i
  fin_cases i
  · simp [thinKiteMap, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteMap, planePoint, thinKiteTarget,
      AffineMap.lineMap_apply_module, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_neg, mul_one, neg_sub, mul_zero,
      add_zero, thinKiteScale, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_add, habs, sub_sub_cancel, Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

private theorem thinKiteMap_rightTargetSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteMap δ
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 (thinKiteTarget δ)) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 1) c := by
  have habs : |1 - c| = 1 - c := abs_of_nonneg (by linarith [hc.2])
  ext i
  fin_cases i
  · simp [thinKiteMap, AffineMap.lineMap_apply_module, planePoint]
  · simp only [thinKiteMap, planePoint, thinKiteTarget,
      AffineMap.lineMap_apply_module, Fin.isValue, PiLp.add_apply, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_one, mul_zero, add_zero, thinKiteScale,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_add, habs, sub_sub_cancel,
      Fin.mk_one]
    have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
    field_simp [hd]
    ring

theorem thinKiteAmbientHomeomorph_leftSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteAmbientHomeomorph δ hδ
        (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 1) c := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  change thinKiteMap δ
      (diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
        (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
        (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
        (thinKiteInv δ
          (AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c))) = _
  rw [thinKiteInv_leftSpoke δ hδ c hc,
    diamondFanAmbientHomeomorph_leftSpoke, thinKiteMap_leftTargetSpoke δ hδ c hc]
  exact hc

theorem thinKiteAmbientHomeomorph_rightSpoke (δ : ℝ) (hδ : 0 < δ)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    thinKiteAmbientHomeomorph δ hδ
        (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c) =
      AffineMap.lineMap (planePoint 1 0) (planePoint 0 1) c := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  change thinKiteMap δ
      (diamondFanAmbientHomeomorph (thinKiteSource δ) (thinKiteTarget δ)
        (thinKiteSource_lower hδ) (thinKiteSource_upper hδ)
        (thinKiteTarget_lower hδ) (thinKiteTarget_upper hδ)
        (thinKiteInv δ
          (AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c))) = _
  rw [thinKiteInv_rightSpoke δ hδ c hc,
    diamondFanAmbientHomeomorph_rightSpoke, thinKiteMap_rightTargetSpoke δ hδ c hc]
  exact hc

theorem thinKiteAmbientHomeomorph_image_leftSpoke (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint (-1) 0) (planePoint 0 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 1) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨-, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (thinKiteAmbientHomeomorph_leftSpoke δ hδ c hc).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨AffineMap.lineMap (planePoint (-1) 0) (planePoint 0 0) c,
      ⟨c, hc, rfl⟩, thinKiteAmbientHomeomorph_leftSpoke δ hδ c hc⟩

theorem thinKiteAmbientHomeomorph_image_rightSpoke (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint 1 0) (planePoint 0 0) =
      segment ℝ (planePoint 1 0) (planePoint 0 1) := by
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨-, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, (thinKiteAmbientHomeomorph_rightSpoke δ hδ c hc).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨AffineMap.lineMap (planePoint 1 0) (planePoint 0 0) c,
      ⟨c, hc, rfl⟩, thinKiteAmbientHomeomorph_rightSpoke δ hδ c hc⟩

/-- The thin-kite homeomorphism is affine on every subsegment of its left base half. -/
theorem thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_leftSpoke
    (δ : ℝ) (hδ : 0 < δ) {a b : Plane}
    (ha : a ∈ segment ℝ (planePoint (-1) 0) (planePoint 0 0))
    (hb : b ∈ segment ℝ (planePoint (-1) 0) (planePoint 0 0)) :
    thinKiteAmbientHomeomorph δ hδ '' segment ℝ a b =
      segment ℝ (thinKiteAmbientHomeomorph δ hδ a)
        (thinKiteAmbientHomeomorph δ hδ b) := by
  rw [segment_eq_image_lineMap] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  let L := planePoint (-1) 0
  let C := planePoint 0 0
  let A := planePoint 0 1
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      thinKiteAmbientHomeomorph δ hδ
          (AffineMap.lineMap (AffineMap.lineMap L C s)
            (AffineMap.lineMap L C r) t) =
        AffineMap.lineMap
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap L C s))
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap L C r)) t := by
    have hsr : (1 - t) * s + t * r ∈ Set.Icc (0 : ℝ) 1 := by
      have hmem := (convex_Icc (0 : ℝ) 1).segment_subset hs hr
        (lineMap_mem_segment ℝ s r ht)
      simpa [AffineMap.lineMap_apply_module] using hmem
    rw [show AffineMap.lineMap (AffineMap.lineMap L C s)
          (AffineMap.lineMap L C r) t =
        AffineMap.lineMap L C ((1 - t) * s + t * r) by
      ext i
      fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> ring]
    rw [thinKiteAmbientHomeomorph_leftSpoke δ hδ _ hsr,
      thinKiteAmbientHomeomorph_leftSpoke δ hδ s hs,
      thinKiteAmbientHomeomorph_leftSpoke δ hδ r hr]
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply_module] ; ring
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simpa [L, C] using (hline t ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨AffineMap.lineMap (AffineMap.lineMap L C s)
      (AffineMap.lineMap L C r) t, ⟨t, ht, rfl⟩,
        by simpa [L, C] using hline t ht⟩

/-- The thin-kite homeomorphism is affine on every subsegment of its right base half. -/
theorem thinKiteAmbientHomeomorph_image_segment_of_endpoints_mem_rightSpoke
    (δ : ℝ) (hδ : 0 < δ) {a b : Plane}
    (ha : a ∈ segment ℝ (planePoint 0 0) (planePoint 1 0))
    (hb : b ∈ segment ℝ (planePoint 0 0) (planePoint 1 0)) :
    thinKiteAmbientHomeomorph δ hδ '' segment ℝ a b =
      segment ℝ (thinKiteAmbientHomeomorph δ hδ a)
        (thinKiteAmbientHomeomorph δ hδ b) := by
  rw [segment_symm] at ha hb
  rw [segment_eq_image_lineMap] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  let R := planePoint 1 0
  let C := planePoint 0 0
  let A := planePoint 0 1
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      thinKiteAmbientHomeomorph δ hδ
          (AffineMap.lineMap (AffineMap.lineMap R C s)
            (AffineMap.lineMap R C r) t) =
        AffineMap.lineMap
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap R C s))
          (thinKiteAmbientHomeomorph δ hδ (AffineMap.lineMap R C r)) t := by
    have hsr : (1 - t) * s + t * r ∈ Set.Icc (0 : ℝ) 1 := by
      have hmem := (convex_Icc (0 : ℝ) 1).segment_subset hs hr
        (lineMap_mem_segment ℝ s r ht)
      simpa [AffineMap.lineMap_apply_module] using hmem
    rw [show AffineMap.lineMap (AffineMap.lineMap R C s)
          (AffineMap.lineMap R C r) t =
        AffineMap.lineMap R C ((1 - t) * s + t * r) by
      ext i
      fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> ring]
    rw [thinKiteAmbientHomeomorph_rightSpoke δ hδ _ hsr,
      thinKiteAmbientHomeomorph_rightSpoke δ hδ s hs,
      thinKiteAmbientHomeomorph_rightSpoke δ hδ r hr]
    ext i
    fin_cases i <;> simp [AffineMap.lineMap_apply_module] ; ring
  rw [segment_eq_image_lineMap, segment_eq_image_lineMap]
  ext p
  constructor
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simpa [R, C] using (hline t ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨AffineMap.lineMap (AffineMap.lineMap R C s)
      (AffineMap.lineMap R C r) t, ⟨t, ht, rfl⟩,
        by simpa [R, C] using hline t ht⟩

theorem baseSegment_eq_spokes :
    segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 0) ∪
        segment ℝ (planePoint 1 0) (planePoint 0 0) := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    by_cases hhalf : c ≤ (1 : ℝ) / 2
    · left
      rw [segment_eq_image_lineMap]
      refine ⟨2 * c, ⟨by linarith [hc.1], by linarith⟩, ?_⟩
      ext i
      fin_cases i <;>
        simp [AffineMap.lineMap_apply_module, planePoint]; ring
    · right
      rw [segment_eq_image_lineMap]
      refine ⟨2 - 2 * c, ⟨by linarith [hc.2], by linarith⟩, ?_⟩
      ext i
      fin_cases i <;>
        simp [AffineMap.lineMap_apply_module, planePoint]; ring
  · have hcenter : planePoint 0 0 ∈
        segment ℝ (planePoint (-1) 0) (planePoint 1 0) := by
      rw [show planePoint 0 0 = AffineMap.lineMap
          (planePoint (-1) 0) (planePoint 1 0) ((1 : ℝ) / 2) by
        ext i
        fin_cases i <;>
          simp [AffineMap.lineMap_apply_module, planePoint]; ring]
      exact lineMap_mem_segment ℝ _ _ (by constructor <;> norm_num)
    apply Set.union_subset
    · exact (convex_segment (𝕜 := ℝ) (planePoint (-1) 0) (planePoint 1 0)).segment_subset
        (left_mem_segment ℝ _ _) hcenter
    · exact (convex_segment (𝕜 := ℝ) (planePoint (-1) 0) (planePoint 1 0)).segment_subset
        (right_mem_segment ℝ _ _) hcenter

theorem thinKiteAmbientHomeomorph_image_baseSegment (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ ''
        segment ℝ (planePoint (-1) 0) (planePoint 1 0) =
      segment ℝ (planePoint (-1) 0) (planePoint 0 1) ∪
        segment ℝ (planePoint 1 0) (planePoint 0 1) := by
  rw [baseSegment_eq_spokes, Set.image_union,
    thinKiteAmbientHomeomorph_image_leftSpoke,
    thinKiteAmbientHomeomorph_image_rightSpoke]

theorem thinKiteAmbientHomeomorph_center (δ : ℝ) (hδ : 0 < δ) :
    thinKiteAmbientHomeomorph δ hδ (planePoint 0 0) = planePoint 0 1 := by
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [show (thinKiteGlobalHomeomorph δ hδ).symm (planePoint 0 0) =
      planePoint 0 (thinKiteSource δ) by
    change thinKiteInv δ (planePoint 0 0) = planePoint 0 (thinKiteSource δ)
    ext i
    fin_cases i
    · simp [thinKiteInv]
    · simp only [thinKiteInv, Fin.isValue, planePoint_apply_zero, planePoint_apply_one, abs_zero,
        sub_zero, one_div, zero_sub, thinKiteScale, Fin.mk_one, thinKiteSource]
      have hd : 1 + 2 * δ ≠ 0 := (by positivity : 0 < 1 + 2 * δ).ne'
      field_simp [hd]
      ring]
  rw [diamondFanAmbientHomeomorph_center]
  exact thinKiteMap_target δ hδ

theorem thinKiteAmbientHomeomorph_eqOn_compl (δ : ℝ) (hδ : 0 < δ) :
    Set.EqOn (thinKiteAmbientHomeomorph δ hδ) id (thinKitePatch δ)ᶜ := by
  intro p hp
  have hpre : (thinKiteGlobalHomeomorph δ hδ).symm p ∉ diamondPatch := by
    intro hmem
    apply hp
    rw [thinKitePatch]
    refine ⟨(thinKiteGlobalHomeomorph δ hδ).symm p, hmem, ?_⟩
    simpa [thinKiteGlobalHomeomorph] using
      (thinKiteGlobalHomeomorph δ hδ).apply_symm_apply p
  rw [thinKiteAmbientHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply]
  rw [diamondFanAmbientHomeomorph_eqOn_compl _ _ _ _ _ _ hpre]
  simp

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
