/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersSphere
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Kernel All Orders Shift

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic


/-!
# Shifted kernels: measurability and separation

A kernel continuous away from the origin gives a measurable shifted integrand,
because the shifted singularity is a single point and hence a null set.  The
remaining lemmas record the reflection symmetry of the Euclidean length, the
fact that a small sup-norm displacement loses at most half of a Euclidean
separation, and the monotonicity of inverse powers.  These support the
potential estimates of `cor:CZ-harmonic`.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- The Euclidean length is symmetric under exchanging the two points.

This is the reflection symmetry used to convert the displacement `x - z`
appearing in the triangle inequality into the sup-norm difference `z - x` in
`half_le_vec3EuclideanNorm_sub`, part of the potential estimates of
`cor:CZ-harmonic`. -/
theorem vec3EuclideanNorm_sub_comm (a b : Vec3) :
    vec3EuclideanNorm (a - b) = vec3EuclideanNorm (b - a) := by
  have h : a - b = (-1 : ℝ) • (b - a) := by
    rw [neg_smul, one_smul, neg_sub]
  rw [h, vec3EuclideanNorm_smul, abs_neg, abs_one, one_mul]

/-- A sup-norm displacement below `δ / 6` loses at most half of a Euclidean separation `δ`.

Writing `x - y = (x - z) + (z - y)` and applying the triangle inequality shows
that `vec3EuclideanNorm (z - y)` can fall short of `δ` by at most
`vec3EuclideanNorm (x - z)`, and the latter is bounded by `3 ‖z - x‖ < δ / 2`.
This is the geometric input to the potential estimates of `cor:CZ-harmonic`. -/
theorem half_le_vec3EuclideanNorm_sub {x z y : Vec3} {δ : ℝ} (hδ : 0 < δ)
    (hz : ‖z - x‖ < δ / 6) (h : δ ≤ vec3EuclideanNorm (x - y)) :
    δ / 2 ≤ vec3EuclideanNorm (z - y) := by
  have hxy : vec3EuclideanNorm (x - y) ≤
      vec3EuclideanNorm (x - z) + vec3EuclideanNorm (z - y) := by
    have hdecomp : x - y = (x - z) + (z - y) := by abel
    rw [hdecomp]
    exact vec3EuclideanNorm_triangle (x - z) (z - y)
  have hxz : vec3EuclideanNorm (x - z) ≤ 3 * ‖z - x‖ := by
    rw [vec3EuclideanNorm_sub_comm x z]
    exact CKN.euclideanNorm_le_three_mul_space_norm (z - x)
  have hxzlt : vec3EuclideanNorm (x - z) < δ / 2 := by
    calc
      vec3EuclideanNorm (x - z) ≤ 3 * ‖z - x‖ := hxz
      _ < 3 * (δ / 6) := mul_lt_mul_of_pos_left hz (by norm_num)
      _ = δ / 2 := by ring
  have hsum : δ ≤ vec3EuclideanNorm (x - z) + vec3EuclideanNorm (z - y) := h.trans hxy
  have hδhalf : 0 < δ / 2 := div_pos hδ (by norm_num)
  linarith only [hδhalf, hsum, hxzlt]

/-- Inverse powers reverse the order.

For `0 < δ ≤ t` and any exponent `n`, the inverse power `(t ^ n)⁻¹` is at most
`(δ ^ n)⁻¹`; this is the elementary monotonicity behind the all-order kernel
bounds of `cor:CZ-harmonic`. -/
theorem inv_pow_le_inv_pow_of_le {δ t : ℝ} (hδ : 0 < δ) (h : δ ≤ t) (n : ℕ) :
    (t ^ n)⁻¹ ≤ (δ ^ n)⁻¹ := by
  have hpow : δ ^ n ≤ t ^ n := pow_le_pow_left₀ hδ.le h n
  exact (inv_le_inv₀ (pow_pos (hδ.trans_le h) n) (pow_pos hδ n)).mpr hpow

/-- A kernel continuous away from the origin has a measurable shifted integrand.

The set `S = {y | y ≠ x}` is open and its complement is the singleton `{x}`,
which is null.  Hence `fun y => K (x - y)` is continuous on `S`, so almost
everywhere strongly measurable against `volume`, and the product with the
scalar factor `g` is measurable as well.  This is the measurability input to
the potential estimates of `cor:CZ-harmonic`. -/
theorem aestronglyMeasurable_smul_kernel_shift {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Vec3 → F} (hK : ContinuousOn K {z : Vec3 | z ≠ 0})
    {g : Vec3 → ℝ} (hg : AEStronglyMeasurable g volume) (x : Vec3) :
    AEStronglyMeasurable (fun y : Vec3 => g y • K (x - y)) volume := by
  let S : Set Vec3 := {y | y ≠ x}
  have hSmeas : MeasurableSet S := isOpen_ne.measurableSet
  have hScompl : volume Sᶜ = 0 := by
    have hc : Sᶜ = {x} := by
      ext y
      simp [S]
    rw [hc]
    simp
  have hae : ∀ᵐ y ∂volume, y ∈ S := by
    rw [MeasureTheory.ae_iff]
    exact hScompl
  have hcont : ContinuousOn (fun y : Vec3 => K (x - y)) S :=
    hK.comp' ((continuous_const.sub continuous_id).continuousOn)
      fun y hy => sub_ne_zero.mpr (Ne.symm hy)
  have hmeasK : AEStronglyMeasurable (fun y : Vec3 => K (x - y)) volume := by
    have h := ContinuousOn.aestronglyMeasurable (μ := volume) hcont hSmeas
    rwa [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae] at h
  exact hg.smul hmeasK

end CKN.Foundation.Heat
