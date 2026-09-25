/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorBasic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Kernel All Orders Smooth

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open CKN.Foundation.Parabolic


/-!
# Smoothness and scaling of the Newtonian kernel away from the origin

The kernel `newtonianKernel` of `cor:CZ-harmonic` is a constant multiple of a
negative real power of the quadratic form `q`, hence of every finite
differentiability order away from the origin, and it is homogeneous of degree
`-1` under dilations.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- The Newtonian kernel as a real power of the quadratic form `q`. -/
theorem newtonianKernel_eq_q_rpow (z : Vec3) :
    newtonianKernel z = (4 * Real.pi)⁻¹ * q z ^ (-(1 : ℝ) / 2) := by
  by_cases hz : z = 0
  · subst z
    simp only [newtonianKernel, q, vec3EuclideanNorm, Fin.sum_univ_three]
    norm_num [Real.zero_rpow (by norm_num : (-(1 : ℝ) / 2) ≠ 0)]
  · have hqnonneg : 0 ≤ q z := (q_pos hz).le
    have hnorm : vec3EuclideanNorm z = Real.sqrt (q z) := by
      rw [q_eq_vec3Norm_sq z, Real.sqrt_sq (vec3EuclideanNorm_nonneg z)]
    rw [newtonianKernel, hnorm, one_div, mul_inv, Real.sqrt_eq_rpow,
      show -(1 : ℝ) / 2 = -(1 / (2 : ℝ)) by ring,
      Real.rpow_neg hqnonneg (1 / (2 : ℝ))]

/-- The Newtonian kernel has every finite differentiability order away from the origin. -/
theorem contDiffAt_newtonianKernel (n : ℕ) {x : Vec3} (hx : x ≠ 0) :
    ContDiffAt ℝ n newtonianKernel x := by
  have hq : ContDiff ℝ n q := by
    unfold q
    apply ContDiff.sum
    intro i _
    exact (contDiff_apply ℝ ℝ i).pow 2
  have hpow : ContDiffAt ℝ n (fun z : Vec3 => q z ^ (-(1 : ℝ) / 2)) x :=
    hq.contDiffAt.rpow_const_of_ne (q_pos hx).ne'
  have hconst : ContDiffAt ℝ n (fun _ : Vec3 => (4 * Real.pi)⁻¹) x :=
    contDiffAt_const
  have hgoal : ContDiffAt ℝ n
      (fun z : Vec3 => (4 * Real.pi)⁻¹ * q z ^ (-(1 : ℝ) / 2)) x :=
    hconst.mul hpow
  rw [show newtonianKernel =
      (fun z : Vec3 => (4 * Real.pi)⁻¹ * q z ^ (-(1 : ℝ) / 2))
      from funext newtonianKernel_eq_q_rpow]
  exact hgoal

/-- Homogeneity of degree `-1` of the Newtonian kernel. -/
theorem newtonianKernel_smul_left {r : ℝ} (hr : 0 < r) (x : Vec3) :
    newtonianKernel (r • x) = r⁻¹ * newtonianKernel x := by
  unfold newtonianKernel
  rw [vec3EuclideanNorm_smul, abs_of_pos hr, one_div, one_div,
    show 4 * Real.pi * (r * vec3EuclideanNorm x) =
      r * (4 * Real.pi * vec3EuclideanNorm x) by ring,
    mul_inv]

end CKN.Foundation.Heat
