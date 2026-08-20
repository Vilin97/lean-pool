/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.Moise.ChartExtraction
import LeanPool.ClassificationOfSurfaces.Moise.PLApproximation

/-!
# Polygonal disks in a half-plane

The bordered Radó step approximates the one-skeleton inside the closed right half-plane.  This
file records the elementary but important consequence: once the replacement polygon stays in
that half-plane, its bounded Schoenflies filling stays there as well.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- The model closed half-plane is convex. -/
theorem convex_halfPlaneSet : Convex ℝ HalfPlaneSet := by
  have hlinear : IsLinearMap ℝ (fun v : Plane ↦ v 0) :=
    .mk (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  simpa [HalfPlaneSet] using convex_halfSpace_ge hlinear (0 : ℝ)

/-- A polygonal circle carried by the closed right half-plane bounds its disk there. -/
theorem PolygonalCircle.closedRegion_subset_halfPlane (J : PolygonalCircle)
    (hcarrier : J.carrier ⊆ HalfPlaneSet) :
    J.closedRegion ⊆ HalfPlaneSet := by
  have hinterior : J.interiorRegion ⊆ HalfPlaneSet := by
    intro x hx
    by_contra hnot
    have hxneg : x 0 < 0 := lt_of_not_ge hnot
    let line : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap 0 x
    let ray : Set Plane := line '' Set.Ici (1 : ℝ)
    have hxRay : x ∈ ray := by
      refine ⟨1, Set.mem_Ici.mpr le_rfl, ?_⟩
      simp [line]
    have hrayPreconnected : IsPreconnected ray := by
      exact (convex_Ici (1 : ℝ)).isPreconnected.image line
        line.continuous_of_finiteDimensional.continuousOn
    have hrayOff : ray ⊆ J.carrierᶜ := by
      rintro y ⟨t, ht, rfl⟩ hyCarrier
      have hyNonneg : 0 ≤ (AffineMap.lineMap 0 x t) 0 := hcarrier hyCarrier
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hyCoord : (AffineMap.lineMap 0 x t) 0 = t * x 0 := by
        simp [AffineMap.lineMap_apply]
      rw [hyCoord] at hyNonneg
      nlinarith
    have hraySplit : ray ⊆ J.interiorRegion ∪ J.exteriorRegion := by
      rw [J.interior_union_exterior]
      exact hrayOff
    have hrayInside : ray ⊆ J.interiorRegion :=
      hrayPreconnected.subset_left_of_subset_union
        J.isOpen_interiorRegion J.isOpen_exteriorRegion
        J.disjoint_interior_exterior hraySplit ⟨x, hxRay, hx⟩
    obtain ⟨R, hR⟩ := J.isBounded_interiorRegion.subset_closedBall (0 : Plane)
    let d := dist x 0
    have hd : 0 < d := dist_pos.mpr (by
      intro hxzero
      have hcoord : x 0 = (0 : Plane) 0 := congrArg (fun z : Plane ↦ z 0) hxzero
      simp only [PiLp.zero_apply] at hcoord
      linarith)
    let t : ℝ := (|R| + 1) / d + 1
    have ht : 1 ≤ t := by
      dsimp [t]
      have : 0 ≤ (|R| + 1) / d := div_nonneg (by positivity) hd.le
      linarith
    let y := AffineMap.lineMap (0 : Plane) x t
    have hyRay : y ∈ ray := ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hyBound := hR (hrayInside hyRay)
    rw [Metric.mem_closedBall] at hyBound
    have hydist : dist y 0 = t * d := by
      dsimp [y, d]
      rw [dist_lineMap_left, Real.norm_eq_abs,
        abs_of_nonneg (le_trans (by norm_num) ht), dist_comm 0 x]
    rw [hydist] at hyBound
    have hRabs : R ≤ |R| := le_abs_self R
    dsimp [t] at hyBound
    field_simp [hd.ne'] at hyBound
    nlinarith
  rw [J.closedRegion_eq_union]
  exact Set.union_subset hinterior hcarrier

/-- A plane-open subset of the closed half-plane cannot contain a point of its supporting
boundary line. -/
theorem coordZero_pos_of_mem_open_subset_halfPlane {O : Set Plane}
    (hO : IsOpen O) (hOH : O ⊆ HalfPlaneSet) {x : Plane} (hx : x ∈ O) :
    0 < x 0 := by
  have hxNonneg : 0 ≤ x 0 := hOH hx
  refine lt_of_le_of_ne hxNonneg ?_
  intro hxZero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO x hx
  let y : Plane := x - (ε / 2) • planePoint 1 0
  have hxy : dist y x < ε := by
    have hvertexNorm : ‖planePoint 1 0‖ = 1 := by
      simp [planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [dist_eq_norm]
    rw [show y - x = -(ε / 2) •
        planePoint 1 0 by
      simp [y, sub_eq_add_neg, add_assoc]]
    rw [norm_smul, norm_neg, hvertexNorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith
  have hyO : y ∈ O := hball (Metric.mem_ball.mpr hxy)
  have hyNonneg : 0 ≤ y 0 := hOH hyO
  have hyCoord : y 0 = x 0 - ε / 2 := by
    simp [y]
  rw [hyCoord, hxZero] at hyNonneg
  linarith

/-- The supporting line meets the filled polygonal disk only on its polygonal boundary. -/
theorem PolygonalCircle.mem_carrier_of_mem_closedRegion_coordZero
    (J : PolygonalCircle) (hcarrier : J.carrier ⊆ HalfPlaneSet)
    {x : Plane} (hx : x ∈ J.closedRegion) (hxZero : x 0 = 0) :
    x ∈ J.carrier := by
  rw [J.closedRegion_eq_union] at hx
  rcases hx with hxInterior | hxCarrier
  · have hxPos :=
      coordZero_pos_of_mem_open_subset_halfPlane J.isOpen_interiorRegion
        (by
          intro y hy
          exact J.closedRegion_subset_halfPlane hcarrier
            (by rw [J.closedRegion_eq_union]; exact Or.inl hy))
        hxInterior
    linarith
  · exact hxCarrier

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
