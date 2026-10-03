/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalParentGeometry

/-! # Interior Parent Geometry -/

@[expose] public section

namespace Homogenization

open scoped Topology

noncomputable section

namespace CubeCalderonZygmund

open Set

/-!
# Stopping comparisons inside the half-radius reflected parent

The reflected parent construction produces its interior weak Hessian on the
half-scaled open cube at scale `m + 1`.  The standard stopping cutoff already
keeps the comparison-parent radius below half the radius at scale `m`; this
file records that the resulting closed ball, and hence its open axis-cube
realization, lies strictly inside that Hessian domain.
-/

/-- A closed ball of radius at most half the radius at scale `m`, centered at
a point strictly inside the scale-`m` cube, lies in the half-scaled open cube
at scale `m + 1`.  Strictness at the target boundary comes from the strict
source-cube membership, not from the closed-ball radius bound. -/
theorem closedBall_subset_scaledOpenCubeSet_originCube_succ_one_div_two_of_mem
    {d : ℕ} {m : ℤ} {x : Vec d} {a : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (ha_nonneg : 0 ≤ a)
    (ha : a ≤ cubeRadius (originCube d m) / 2) :
    Metric.closedBall x a ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) := by
  intro y hy
  have hx' := mem_openCubeSet_originCube_iff.mp hx
  have hy' : y ∈ Set.pi Set.univ (fun i : Fin d => Metric.closedBall (x i) a) := by
    rw [← closedBall_pi x ha_nonneg]
    exact hy
  have hscale_pos : 0 < (3 : ℝ) ^ m := by
    positivity
  have ha' : a ≤ (1 / 4 : ℝ) * (3 : ℝ) ^ m := by
    calc
      a ≤ cubeRadius (originCube d m) / 2 := ha
      _ = (1 / 4 : ℝ) * (3 : ℝ) ^ m := by
        simp only [cubeRadius, cubeScaleFactor, originCube]
        ring
  intro i
  have hyi := hy' i (by simp)
  change y i ∈ Metric.closedBall (x i) a at hyi
  rw [Real.closedBall_eq_Icc] at hyi
  change
    |y i - cubeCenter (originCube d (m + 1)) i| <
      (1 / 2 : ℝ) * cubeRadius (originCube d (m + 1))
  simp only [cubeCenter, originCube, Pi.zero_apply, Int.cast_zero, zero_mul,
    sub_zero, cubeRadius, cubeScaleFactor]
  rw [abs_lt]
  have hparent_scale : (3 : ℝ) ^ (m + 1) = (3 : ℝ) ^ m * 3 := by
    rw [zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num)]
    norm_num
  rw [hparent_scale]
  constructor <;> nlinarith [(hx' i).1, (hx' i).2, hyi.1, hyi.2]

/-- Under the standard cutoff, the closed stopping-comparison parent lies in
the half-scaled open cube on which the reflected solution's weak Hessian is
constructed. -/
theorem stoppingComparisonParent_closedBall_subset_scaledOpenCubeSet_originCube_succ_one_div_two
    {d : ℕ} {m : ℤ} {x : Vec d} {r : ℝ} (depth : ℕ)
    (hx : x ∈ openCubeSet (originCube d m)) (hr_nonneg : 0 ≤ r)
    (hcutoff : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth)) :
    Metric.closedBall x (stoppingComparisonParentMultiplier depth * r) ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) := by
  apply closedBall_subset_scaledOpenCubeSet_originCube_succ_one_div_two_of_mem hx
  · exact mul_nonneg (by simp [stoppingComparisonParentMultiplier]) hr_nonneg
  · exact stoppingComparisonParentRadius_le_half_cubeRadius_of_le depth hcutoff

/-- Under the standard cutoff, the open axis-cube realization of the stopping
comparison parent lies in the half-scaled reflected-parent Hessian domain. -/
theorem stoppingComparisonParent_axisCube_subset_scaledOpenCubeSet_originCube_succ_one_div_two
    {d : ℕ} {m : ℤ} {x : Vec d} {r : ℝ} (depth : ℕ)
    (hx : x ∈ openCubeSet (originCube d m)) (hr_pos : 0 < r)
    (hcutoff : r ≤ cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth)) :
    axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ) := by
  rw [stoppingComparisonParent_axisCube_eq_ball x hr_pos depth]
  exact Metric.ball_subset_closedBall.trans
    (stoppingComparisonParent_closedBall_subset_scaledOpenCubeSet_originCube_succ_one_div_two
      depth hx hr_pos.le hcutoff)

end CubeCalderonZygmund

end

end Homogenization
