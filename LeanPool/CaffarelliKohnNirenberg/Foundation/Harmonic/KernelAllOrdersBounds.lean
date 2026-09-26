/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersOpen
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersSphere
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Kernel All Orders Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators Topology
open CKN.Foundation.Parabolic


/-!
# All-order derivative bounds for the Newtonian kernel

The Newtonian kernel `newtonianKernel` is homogeneous of degree `-1` and of
every finite differentiability order away from the origin, so its `k`-th
derivative is homogeneous of degree `-(1 + k)`.  Combining this with the
compactness of the Euclidean unit sphere gives, for each order `k`, a constant
`c` with

  `‖D^k newtonianKernel x‖ ≤ c ‖x‖₂^{-(1 + k)}`  for `x ≠ 0`,

and the same statement with exponent `-(2 + k)` for each first-order kernel
`∂_j newtonianKernel`.  These are the kernel estimates behind `cor:CZ-harmonic`
and the smoothness display `eq:har-Ck`.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- Space with the origin removed; the Newtonian kernel is smooth there. -/
theorem isOpen_vec3Punctured : IsOpen {z : Vec3 | z ≠ 0} := isOpen_ne

/-- The Newtonian kernel has every finite differentiability order off the origin. -/
theorem contDiffOn_newtonianKernel (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) newtonianKernel {z : Vec3 | z ≠ 0} := fun _z hz =>
  (contDiffAt_newtonianKernel n hz).contDiffWithinAt

/-- Every iterated derivative of the Newtonian kernel is differentiable off the origin. -/
theorem differentiableAt_iteratedFDeriv_newtonianKernel (k : ℕ) {x : Vec3} (hx : x ≠ 0) :
    DifferentiableAt ℝ (iteratedFDeriv ℝ k newtonianKernel) x :=
  differentiableAt_iteratedFDeriv_of_isOpen isOpen_vec3Punctured k
    (contDiffOn_newtonianKernel (k + 1)) hx

/-- Every iterated derivative of the Newtonian kernel is continuous off the origin. -/
theorem continuousOn_iteratedFDeriv_newtonianKernel (k : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ k newtonianKernel) {z : Vec3 | z ≠ 0} :=
  continuousOn_iteratedFDeriv_of_isOpen isOpen_vec3Punctured k (contDiffOn_newtonianKernel k)

/-- The `k`-th derivative of the Newtonian kernel is homogeneous of degree `-(1 + k)`. -/
theorem iteratedFDeriv_newtonianKernel_smul (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∀ {x : Vec3}, x ≠ 0 →
      iteratedFDeriv ℝ k newtonianKernel (r • x) =
        (r ^ (1 + k))⁻¹ • iteratedFDeriv ℝ k newtonianKernel x := by
  induction k with
  | zero =>
      intro x hx
      ext m
      simp only [iteratedFDeriv_zero_apply, smul_apply, smul_eq_mul, Nat.add_zero, pow_one]
      exact newtonianKernel_smul_left hr x
  | succ k ih =>
      intro x hx
      have hrne : r ≠ 0 := ne_of_gt hr
      have hsmulne : r • x ≠ 0 := smul_ne_zero hrne hx
      have hG : HasFDerivAt (fun y : Vec3 => iteratedFDeriv ℝ k newtonianKernel (r • y))
          ((fderiv ℝ (iteratedFDeriv ℝ k newtonianKernel) (r • x)).comp
            (r • (ContinuousLinearMap.id ℝ Vec3))) x :=
        (differentiableAt_iteratedFDeriv_newtonianKernel k hsmulne).hasFDerivAt.comp x
          ((hasFDerivAt_id x).const_smul r)
      have hH : HasFDerivAt
          (fun y : Vec3 => (r ^ (1 + k))⁻¹ • iteratedFDeriv ℝ k newtonianKernel y)
          ((r ^ (1 + k))⁻¹ • fderiv ℝ (iteratedFDeriv ℝ k newtonianKernel) x) x :=
        (differentiableAt_iteratedFDeriv_newtonianKernel k hx).hasFDerivAt.const_smul
          ((r ^ (1 + k))⁻¹)
      have heq : (fun y : Vec3 => iteratedFDeriv ℝ k newtonianKernel (r • y))
          =ᶠ[𝓝 x] fun y : Vec3 => (r ^ (1 + k))⁻¹ • iteratedFDeriv ℝ k newtonianKernel y := by
        filter_upwards [isOpen_vec3Punctured.mem_nhds hx] with y hy using ih hy
      have hunique := (hH.congr_of_eventuallyEq heq).unique hG
      have happly : ∀ v : Vec3,
          (fderiv ℝ (iteratedFDeriv ℝ k newtonianKernel) (r • x)) v =
            (r ^ (1 + (k + 1)))⁻¹ •
              (fderiv ℝ (iteratedFDeriv ℝ k newtonianKernel) x) v := by
        intro v
        have h := congrArg (fun L => L v) hunique
        simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.id_apply, map_smul] at h
        have hpow : (r ^ (1 + (k + 1)))⁻¹ = r⁻¹ * (r ^ (1 + k))⁻¹ := by
          rw [← mul_inv]
          congr 1
          ring
        rw [hpow, mul_smul, h, smul_smul, inv_mul_cancel₀ hrne, one_smul]
      ext m
      rw [iteratedFDeriv_succ_apply_left, happly (m 0)]
      simp only [smul_apply, iteratedFDeriv_succ_apply_left]

/-- The size of the `k`-th derivative of the Newtonian kernel away from the origin. -/
theorem exists_norm_iteratedFDeriv_newtonianKernel_le (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Vec3, x ≠ 0 →
      ‖iteratedFDeriv ℝ k newtonianKernel x‖ ≤ c * (vec3EuclideanNorm x ^ (1 + k))⁻¹ := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_bound_on_vec3Sphere (continuousOn_iteratedFDeriv_newtonianKernel k)
  refine ⟨c, hc0, fun x hx => ?_⟩
  have hR : 0 < vec3EuclideanNorm x := vec3EuclideanNorm_pos_of_ne_zero hx
  set R : ℝ := vec3EuclideanNorm x with hRdef
  have hunit : vec3EuclideanNorm (R⁻¹ • x) = 1 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR), ← hRdef,
      inv_mul_cancel₀ (ne_of_gt hR)]
  have hune : R⁻¹ • x ≠ 0 := ne_zero_of_vec3EuclideanNorm_pos (by rw [hunit]; norm_num)
  have hxeq : x = R • (R⁻¹ • x) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  calc
    ‖iteratedFDeriv ℝ k newtonianKernel x‖
        = ‖iteratedFDeriv ℝ k newtonianKernel (R • (R⁻¹ • x))‖ := by rw [← hxeq]
    _ = ‖(R ^ (1 + k))⁻¹ • iteratedFDeriv ℝ k newtonianKernel (R⁻¹ • x)‖ := by
        rw [iteratedFDeriv_newtonianKernel_smul k hR hune]
    _ = (R ^ (1 + k))⁻¹ * ‖iteratedFDeriv ℝ k newtonianKernel (R⁻¹ • x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ (R ^ (1 + k))⁻¹ * c := by
        exact mul_le_mul_of_nonneg_left (hc _ hunit) (by positivity)
    _ = c * (R ^ (1 + k))⁻¹ := by ring

/-- Each coordinate basis vector has sup norm at most one. -/
theorem norm_basisVec_le_one (j : Fin 3) : ‖CKN.basisVec j‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, CKN.basisVec_apply]
  by_cases h : i = j <;> simp [h]

/-- The size of the `k`-th derivative of a first-order Newtonian kernel `∂_j N`. -/
theorem exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le (j : Fin 3) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Vec3, x ≠ 0 →
      ‖iteratedFDeriv ℝ k (CKN.spatialDeriv newtonianKernel j) x‖ ≤
        c * (vec3EuclideanNorm x ^ (2 + k))⁻¹ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_iteratedFDeriv_newtonianKernel_le (k + 1)
  refine ⟨c, hc0, fun x hx => ?_⟩
  have hf : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fderiv ℝ newtonianKernel) x := by
    have h := contDiffAt_newtonianKernel (k + 1) hx
    have hcast : (((k + 1 : ℕ)) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by
      push_cast
      ring
    rw [hcast] at h
    exact h.fderiv_right_succ
  have hclm := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (n := k)
    (c := CKN.basisVec j) hf le_rfl
  have hsucc : ‖iteratedFDeriv ℝ k (fderiv ℝ newtonianKernel) x‖ =
      ‖iteratedFDeriv ℝ (k + 1) newtonianKernel x‖ := norm_iteratedFDeriv_fderiv
  have hpow : (1 : ℕ) + (k + 1) = 2 + k := by ring
  calc
    ‖iteratedFDeriv ℝ k (CKN.spatialDeriv newtonianKernel j) x‖
        = ‖iteratedFDeriv ℝ k (fun y : Vec3 => (fderiv ℝ newtonianKernel y)
            (CKN.basisVec j)) x‖ := rfl
    _ ≤ ‖CKN.basisVec j‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ newtonianKernel) x‖ := hclm
    _ ≤ 1 * ‖iteratedFDeriv ℝ (k + 1) newtonianKernel x‖ := by
        rw [hsucc]
        exact mul_le_mul_of_nonneg_right (norm_basisVec_le_one j) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (k + 1) newtonianKernel x‖ := one_mul _
    _ ≤ c * (vec3EuclideanNorm x ^ (1 + (k + 1)))⁻¹ := hc x hx
    _ = c * (vec3EuclideanNorm x ^ (2 + k))⁻¹ := by rw [hpow]

end CKN.Foundation.Heat
