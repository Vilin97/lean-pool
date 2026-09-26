/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingCubeGeometry

/-! # Global Parent Geometry -/

@[expose] public section

namespace Homogenization

open scoped Topology

noncomputable section

namespace CubeCalderonZygmund

open Set

/-!
# Global parent geometry for cube Calderón–Zygmund stopping balls

The local harmonic comparison is made on an axis cube which realizes a
sup-metric ball about a stopping point.  When that point belongs to the
centered cube at scale `m`, the conservative stopping cutoff keeps even the
closed comparison parent inside the open centered cube at scale `m + 1`.
-/

/-- A closed ball of radius at most one quarter of the scale-`m` side length
about a point of the centered scale-`m` cube lies in its open next parent.

The statement uses `cubeRadius / 2` so it composes directly with the
`10 * 3^n` stopping cutoff. -/
theorem closedBall_subset_openCubeSet_originCube_succ_of_mem
    {d : ℕ} {m : ℤ} {x : Vec d} {a : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (ha_nonneg : 0 ≤ a)
    (ha : a ≤ cubeRadius (originCube d m) / 2) :
    Metric.closedBall x a ⊆ openCubeSet (originCube d (m + 1)) := by
  intro y hy
  rw [mem_openCubeSet_originCube_iff]
  have hx' := mem_openCubeSet_originCube_iff.mp hx
  have hy' : y ∈ Set.pi Set.univ (fun i : Fin d => Metric.closedBall (x i) a) := by
    rw [← closedBall_pi x ha_nonneg]
    exact hy
  intro i
  have hyi := hy' i (by simp)
  change y i ∈ Metric.closedBall (x i) a at hyi
  rw [Real.closedBall_eq_Icc] at hyi
  have hscale_pos : 0 < (3 : ℝ) ^ m := by positivity
  have ha' : a ≤ (1 / 4 : ℝ) * (3 : ℝ) ^ m := by
    calc
      a ≤ cubeRadius (originCube d m) / 2 := ha
      _ = (1 / 4 : ℝ) * (3 : ℝ) ^ m := by
        simp only [cubeRadius, cubeScaleFactor, originCube]
        ring
  have hleft :
      (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (m + 1) =
        (-(3 / 2 : ℝ)) * (3 : ℝ) ^ m := by
    rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
    ring
  have hright :
      (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1) =
        (3 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
    ring
  constructor
  · rw [hleft]
    nlinarith [(hx' i).1, hyi.1]
  · rw [hright]
    nlinarith [(hx' i).2, hyi.2]

/-- The depth-`n` comparison-parent radius is at most half the radius of the
ambient centered cube under the standard stopping cutoff. -/
theorem stoppingComparisonParentRadius_le_half_cubeRadius_of_le
    {d : ℕ} {m : ℤ} {r : ℝ} (n : ℕ)
    (hr : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ n)) :
    stoppingComparisonParentMultiplier n * r ≤ cubeRadius (originCube d m) / 2 := by
  rw [le_div_iff₀ (by positivity : 0 < 10 * (3 : ℝ) ^ n)] at hr
  rw [stoppingComparisonParentMultiplier]
  nlinarith

/-- The closed comparison-parent ball remains in the next centered open cube
whenever the stopping point belongs to the present centered open cube and its
radius obeys the standard cutoff. -/
theorem stoppingComparisonParent_closedBall_subset_openCubeSet_originCube_succ
    {d : ℕ} {m : ℤ} {x : Vec d} {r : ℝ} (n : ℕ)
    (hx : x ∈ openCubeSet (originCube d m)) (hr_nonneg : 0 ≤ r)
    (hr : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ n)) :
    Metric.closedBall x (stoppingComparisonParentMultiplier n * r) ⊆
      openCubeSet (originCube d (m + 1)) := by
  apply closedBall_subset_openCubeSet_originCube_succ_of_mem hx
  · exact mul_nonneg (by simp [stoppingComparisonParentMultiplier]) hr_nonneg
  · exact stoppingComparisonParentRadius_le_half_cubeRadius_of_le n hr

/-- The open axis-cube comparison parent remains in the next centered open
cube under the standard stopping cutoff. -/
theorem stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
    {d : ℕ} {m : ℤ} {x : Vec d} {r : ℝ} (n : ℕ)
    (hx : x ∈ openCubeSet (originCube d m)) (hr_pos : 0 < r)
    (hr : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ n)) :
    axisCube (stoppingComparisonParentCorner x r n)
        (stoppingComparisonParentSide r n) ⊆
      openCubeSet (originCube d (m + 1)) := by
  rw [stoppingComparisonParent_axisCube_eq_ball x hr_pos n]
  exact (Metric.ball_subset_closedBall.trans
    (stoppingComparisonParent_closedBall_subset_openCubeSet_originCube_succ n hx hr_pos.le hr))

end CubeCalderonZygmund

end

end Homogenization
