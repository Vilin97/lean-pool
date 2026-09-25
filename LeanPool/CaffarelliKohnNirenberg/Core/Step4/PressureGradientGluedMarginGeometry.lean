/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersShift
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Margin-safe parabolic cylinders and their closures

This file records the elementary geometry behind the "doubling with a margin"
step: a parabolic cylinder that meets the carrier region and whose radius is at
most one third of the margin separating the carrier from the outer ball has its
doubled-radius cylinder, and hence the closure of that cylinder, contained in
the outer region.  This is what lets a slice estimate proved at a single cell
radius be applied at twice that radius, at the price of a third of the gap
between the inner and outer regions.

The results are stated in the two settings used later: a one-sided cylinder
based at the origin of the unit parabolic cylinder, and a parabolic metric ball
about an arbitrary centre.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN.Core.Step4

/-- The triangle inequality for the Euclidean norm on `Vec3`. -/
private theorem vec3EuclideanNorm_sub_triangle (a b c : Vec3) :
    vec3EuclideanNorm (a - c) ≤ vec3EuclideanNorm (a - b) + vec3EuclideanNorm (b - c) := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
  simpa only [dist_eq_norm] using
    dist_triangle (WithLp.toLp 2 a) (WithLp.toLp 2 b) (WithLp.toLp 2 c)

/-- Two Euclidean balls that meet are closer than the sum of their radii: if some
point lies within radius `r` of `x` and within radius `a` of `c`, then the centres
themselves are less than `a + r` apart.  This is the quantitative form of the
separation between a cell that meets the carrier and the outer ball. -/
theorem vec3EuclideanNorm_lt_of_vec3Ball_inter_nonempty
    {x c : Vec3} {r a : ℝ}
    (h : (vec3Ball x r ∩ vec3Ball c a).Nonempty) :
    vec3EuclideanNorm (x - c) < a + r := by
  rcases h with ⟨w, hwx, hwc⟩
  simp only [mem_vec3Ball] at hwx hwc
  have htri := vec3EuclideanNorm_sub_triangle x w c
  rw [CKN.Foundation.Heat.vec3EuclideanNorm_sub_comm x w] at htri
  linarith only [htri, hwx, hwc]

/-- A parabolic cylinder that meets the carrier at a radius at most a third of the
margin between the carrier and the outer ball has its DOUBLED cylinder inside the
outer region.  Concretely, if `x` is within `R₁ + r` of the origin, `3 * r ≤ R₀ - R₁`
and `R₀ ≤ 1`, then every point of `parabolicCylinder x t (2 * r)` lies in the unit
cylinder `parabolicCylinder 0 0 1`, provided the base time `t` lies below zero and
the doubled time-depth stays at or above the unit depth.  The factor three is the
margin that absorbs the doubling of the radius. -/
theorem parabolicCylinder_double_subset_unit_of_margin
    {R₀ R₁ r t : ℝ} {x : Vec3}
    (hR₀ : R₀ ≤ 1) (hmargin : 3 * r ≤ R₀ - R₁)
    (hx : vec3EuclideanNorm (x - 0) < R₁ + r)
    (htop : t ≤ 0) (hbot : -1 ≤ t - (2 * r) ^ 2) :
    parabolicCylinder x t (2 * r) ⊆ parabolicCylinder (0 : Vec3) 0 1 := by
  intro p hp
  rcases p with ⟨y, s⟩
  change vec3EuclideanNorm (y - x) < 2 * r ∧
    t - (2 * r) ^ 2 < s ∧ s ≤ t at hp
  rcases hp with ⟨hy, hlo, hhi⟩
  change vec3EuclideanNorm (y - 0) < 1 ∧ (0 : ℝ) - 1 ^ 2 < s ∧ s ≤ 0
  refine ⟨?_, ?_, ?_⟩
  · have htri := vec3EuclideanNorm_sub_triangle y x 0
    linarith only [htri, hy, hx, hmargin, hR₀]
  · linarith only [hlo, hbot]
  · exact le_trans hhi htop

/-- The closure form of the margin-safe doubling: if the closure of the unit
parabolic cylinder lies in the space-time carrier `Ω × I`, then so does the closure
of every doubled cylinder whose radius is at most a third of the margin and whose
base point lies within `R₁ + r` of the origin, with the same time-side bounds.  The
closure is taken because the slice estimate is applied on closed one-sided
cylinders. -/
theorem closure_parabolicCylinder_double_subset_spaceTimeSet_of_origin_margin
    {Ω : Set Vec3} {I : Set ℝ} {R₀ R₁ r t : ℝ} {x : Vec3}
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ CKN.spaceTimeSet Ω I)
    (hR₀ : R₀ ≤ 1) (hmargin : 3 * r ≤ R₀ - R₁)
    (hx : vec3EuclideanNorm (x - 0) < R₁ + r)
    (htop : t ≤ 0) (hbot : -1 ≤ t - (2 * r) ^ 2) :
    closure (parabolicCylinder x t (2 * r)) ⊆ CKN.spaceTimeSet Ω I := by
  have hsub := parabolicCylinder_double_subset_unit_of_margin hR₀ hmargin hx htop hbot
  exact (closure_mono hsub).trans hdom

/-- The margin-safe doubling for a parabolic metric ball: a closed doubled cylinder
whose radius is at most a third of `R`, and whose base point is within `R/2 + r` of
the centre and whose base time lies in the one-sided window around the centre time,
is contained in the parabolic ball of radius `2 * R`.  This is the version applied
when the outer region is a parabolic ball rather than the unit cylinder. -/
theorem closure_parabolicCylinder_double_subset_metricBall_of_margin
    {z₀ : ParabolicPoint} {R r t : ℝ} {x : Vec3}
    (hR : 0 < R) (hr : 0 < r) (hmargin : 3 * r ≤ R)
    (hx : vec3EuclideanNorm (x - z₀.1) < R / 2 + r)
    (hlow : z₀.2 - R ^ 2 / 4 - r ^ 2 < t) (hhigh : t < z₀.2 + R ^ 2 / 4 + r ^ 2) :
    closure (parabolicCylinder x t (2 * r)) ⊆ Metric.ball z₀ (2 * R) := by
  rw [closure_parabolicCylinder (by linarith only [hr] : (0 : ℝ) < 2 * r),
    metricBall_eq_parabolicBall]
  intro p hp
  rcases p with ⟨y, s⟩
  change vec3EuclideanNorm (y - x) ≤ 2 * r ∧
    t - (2 * r) ^ 2 ≤ s ∧ s ≤ t at hp
  rcases hp with ⟨hy, hlo, hhi⟩
  constructor
  · change vec3EuclideanNorm (y - z₀.1) < 2 * R
    have htri := vec3EuclideanNorm_sub_triangle y x z₀.1
    linarith only [htri, hy, hx, hmargin, hR]
  · change z₀.2 - (2 * R) ^ 2 < s ∧ s < z₀.2 + (2 * R) ^ 2
    constructor
    · have hr2 : r ^ 2 ≤ R ^ 2 / 9 := by nlinarith only [hr, hR, hmargin]
      nlinarith only [hlo, hlow, hr2, hR]
    · have hr2 : r ^ 2 ≤ R ^ 2 / 9 := by nlinarith only [hr, hR, hmargin]
      nlinarith only [hhi, hhigh, hr2, hR]

/-- A margin-safe cell that meets the carrier ball has its own ball, and hence a
fortiori the region where its slice estimate is read, inside the outer ball. -/
theorem vec3Ball_subset_outer_of_margin
    {R₀ R₁ r : ℝ} {x : Vec3} (hr : 0 ≤ r) (hmargin : 3 * r ≤ R₀ - R₁)
    (hx : vec3EuclideanNorm (x - 0) < R₁ + r) :
    vec3Ball x r ⊆ vec3Ball (0 : Vec3) R₀ := by
  intro y hy
  simp only [mem_vec3Ball] at hy ⊢
  have htri := vec3EuclideanNorm_sub_triangle y x 0
  linarith only [htri, hy, hx, hmargin, hr]

/-- The three margin premises of the doubling step for a parabolic metric ball,
read off a cell that meets the inner ball: the spatial centres are close, and the
cell's top time lies in the one-sided window around the centre time. -/
theorem symmetric_margin_premises_of_meet
    {z₀ : ParabolicPoint} {R r t : ℝ} {x : Vec3} (hr : 0 < r)
    (hmeet : (parabolicCylinder x t r ∩ Metric.ball z₀ (R / 2)).Nonempty) :
    vec3EuclideanNorm (x - z₀.1) < R / 2 + r ∧
      z₀.2 - R ^ 2 / 4 - r ^ 2 < t ∧ t < z₀.2 + R ^ 2 / 4 + r ^ 2 := by
  obtain ⟨w, hwcell, hwball⟩ := hmeet
  rw [metricBall_eq_parabolicBall] at hwball
  obtain ⟨hwx, hwlo, hwhi⟩ := hwcell
  obtain ⟨hwz, hwt⟩ := hwball
  simp only [mem_vec3Ball] at hwx hwz
  obtain ⟨hwt1, hwt2⟩ := hwt
  have hquarter : (R / 2) ^ 2 = R ^ 2 / 4 := by ring
  rw [hquarter] at hwt1 hwt2
  have hr2 : 0 < r ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have htri := vec3EuclideanNorm_sub_triangle x w.1 z₀.1
    rw [CKN.Foundation.Heat.vec3EuclideanNorm_sub_comm x w.1] at htri
    linarith only [htri, hwx, hwz]
  · linarith only [hwt1, hwhi, hr2]
  · linarith only [hwt2, hwlo]

end CKN.Core.Step4
