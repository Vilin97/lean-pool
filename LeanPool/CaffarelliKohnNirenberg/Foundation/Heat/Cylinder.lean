/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Bounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.TestFunction

/-!
# Cylinder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-- Spatial-gradient bound for the rescaled backward heat test function. -/
def backwardHeatTestGradientNorm (r : ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  r ^ 2 * heatKernelGradientNorm x (r ^ 2 - t)

private lemma rpow_three_halves_eq_sqrt_cube {y : ℝ} (hy : 0 ≤ y) :
    y ^ ((3 : ℝ) / 2) = (Real.sqrt y) ^ (3 : ℕ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

private lemma heatKernel_lower_on_scale {r τ : ℝ} {x : Vec3}
    (hr : 0 < r) (hτlow : r ^ 2 ≤ τ) (hτup : τ < 2 * r ^ 2)
    (hx : vec3EuclideanNorm x < r) :
    1 / (2000 * r ^ 3) ≤ heatKernel x τ := by
  have hτ : 0 < τ := lt_of_lt_of_le (sq_pos_of_pos hr) hτlow
  have hbase : 4 * Real.pi * τ ≤ 64 * r ^ 2 := by
    have hpi : 4 * Real.pi ≤ (16 : ℝ) := by nlinarith only [Real.pi_le_four]
    calc
      4 * Real.pi * τ ≤ 16 * τ := by gcongr
      _ ≤ 16 * (2 * r ^ 2) := by gcongr
      _ ≤ 64 * r ^ 2 := by nlinarith only [sq_nonneg r]
  have hpow : (4 * Real.pi * τ) ^ ((3 : ℝ) / 2) ≤
      (1000 : ℝ) * r ^ 3 := by
    have hpow' := Real.rpow_le_rpow (by positivity : 0 ≤ 4 * Real.pi * τ)
      hbase (by positivity : 0 ≤ (3 : ℝ) / 2)
    have hsqrt : Real.sqrt (64 * r ^ 2) = 8 * r := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
      have hsqrt64 : Real.sqrt (64 : ℝ) = 8 := by
        rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num
      rw [hsqrt64, Real.sqrt_sq_eq_abs, abs_of_pos hr]
    calc
      (4 * Real.pi * τ) ^ ((3 : ℝ) / 2) ≤
          (64 * r ^ 2) ^ ((3 : ℝ) / 2) := hpow'
      _ = (Real.sqrt (64 * r ^ 2)) ^ (3 : ℕ) :=
        rpow_three_halves_eq_sqrt_cube (by positivity)
      _ = (8 * r) ^ 3 := by rw [hsqrt]
      _ ≤ 1000 * r ^ 3 := by nlinarith only [hr, sq_nonneg r]
  have hpref : 1 / (1000 * r ^ 3) ≤ (4 * Real.pi * τ) ^ (-(3 : ℝ) / 2) := by
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
      Real.rpow_neg (by positivity)]
    simpa only [one_div] using
      (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hq : ∑ i, x i ^ 2 < r ^ 2 := by
    rw [← vec3EuclideanNorm_sq]
    exact sq_lt_sq₀ (vec3EuclideanNorm_nonneg x) (by positivity) |>.mpr hx
  have ha : (∑ i, x i ^ 2) / (4 * τ) ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < (4 * τ : ℝ))).2
    nlinarith only [hq, hτlow]
  have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(∑ i, x i ^ 2) / (4 * τ)) := by
    have hlin : 1 - (∑ i, x i ^ 2) / (4 * τ) ≤
        Real.exp (-((∑ i, x i ^ 2) / (4 * τ))) := by
      convert Real.add_one_le_exp (-((∑ i, x i ^ 2) / (4 * τ))) using 1
      · ring_nf
    convert (show (1 : ℝ) / 2 ≤
        Real.exp (-((∑ i, x i ^ 2) / (4 * τ))) by nlinarith only [ha, hlin]) using 1
    · ring_nf
  rw [heatKernel_eq_formula_sum hτ]
  calc
    1 / (2000 * r ^ 3) =
        (1 / (1000 * r ^ 3)) * (1 / 2 : ℝ) := by ring
    _ ≤ (4 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * τ)) := by
      gcongr

private lemma cylinder_time_data {r : ℝ} {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 r) :
    r ^ 2 ≤ r ^ 2 - p.2 ∧ r ^ 2 - p.2 < 2 * r ^ 2 := by
  rcases (mem_parabolicCylinder.mp hp) with ⟨_, hlow, hupp⟩
  constructor
  · nlinarith only [hupp]
  · nlinarith only [hlow]

lemma backwardHeatTestFunction_lower_on_cylinder {r : ℝ} (hr : 0 < r)
    {p : ParabolicPoint} (hp : p ∈ parabolicCylinder 0 0 r) :
    1 / (2000 * r) ≤ backwardHeatTestFunction r p.1 p.2 := by
  have hscale := cylinder_time_data hp
  have hkernel := heatKernel_lower_on_scale hr hscale.1 hscale.2
    (mem_parabolicCylinder.mp hp).1
  have hkernel' : 1 / (2000 * r ^ 3) ≤ heatKernel p.1 (r ^ 2 - p.2) := by
    simpa only [sub_zero] using hkernel
  rw [backwardHeatTestFunction]
  calc
    1 / (2000 * r) = r ^ 2 * (1 / (2000 * r ^ 3)) := by
      field_simp [hr.ne']
    _ ≤ r ^ 2 * heatKernel p.1 (r ^ 2 - p.2) := by
      gcongr

lemma backwardHeatTestFunction_upper_on_cylinder {r ρ : ℝ} (hr : 0 < r)
    (_ : 0 < ρ) {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 ρ) :
    backwardHeatTestFunction r p.1 p.2 ≤ 1000 / r := by
  rcases (mem_parabolicCylinder.mp hp) with ⟨_, hlow, hupp⟩
  have hτ : 0 < r ^ 2 - p.2 := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hsqrt : r ≤ Real.sqrt (r ^ 2 - p.2) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (r ^ 2 - p.2) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (r ^ 2 - p.2)) ^ 2 = r ^ 2 - p.2 :=
      Real.sq_sqrt hτ.le
    apply (sq_le_sq₀ hr.le hsqrt_nonneg).mp
    nlinarith only [hupp, hsqrt_sq]
  have hrho : r ≤ rhoTwo p.1 (r ^ 2 - p.2) := by
    unfold rhoTwo
    exact hsqrt.trans (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  have hG := heatKernel_le_rho_inv_cube (x := p.1) hτ
  have hdiv : 1000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 3 ≤ 1000 / r ^ 3 := by
    gcongr
  rw [backwardHeatTestFunction]
  calc
    r ^ 2 * heatKernel p.1 (r ^ 2 - p.2) ≤
        r ^ 2 * (1000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 3) := by gcongr
    _ ≤ r ^ 2 * (1000 / r ^ 3) := by gcongr
    _ = 1000 / r := by field_simp [hr.ne']

lemma backwardHeatTestGradient_upper_on_cylinder {r ρ : ℝ} (hr : 0 < r)
    (_ : 0 < ρ) {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 ρ) :
    backwardHeatTestGradientNorm r p.1 p.2 ≤ 300000 / r ^ 2 := by
  rcases (mem_parabolicCylinder.mp hp) with ⟨_, hlow, hupp⟩
  have hτ : 0 < r ^ 2 - p.2 := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hsqrt : r ≤ Real.sqrt (r ^ 2 - p.2) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (r ^ 2 - p.2) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (r ^ 2 - p.2)) ^ 2 = r ^ 2 - p.2 :=
      Real.sq_sqrt hτ.le
    apply (sq_le_sq₀ hr.le hsqrt_nonneg).mp
    nlinarith only [hupp, hsqrt_sq]
  have hrho : r ≤ rhoTwo p.1 (r ^ 2 - p.2) := by
    unfold rhoTwo
    exact hsqrt.trans (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  have hG := heatKernelGradientNorm_le_rho_inv_four (x := p.1) hτ
  have hdiv : 300000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 4 ≤ 300000 / r ^ 4 := by
    gcongr
  rw [backwardHeatTestGradientNorm]
  calc
    r ^ 2 * heatKernelGradientNorm p.1 (r ^ 2 - p.2) ≤
        r ^ 2 * (300000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 4) := by gcongr
    _ ≤ r ^ 2 * (300000 / r ^ 4) := by gcongr
    _ = 300000 / r ^ 2 := by field_simp [hr.ne']

private lemma rhoTwo_ge_half_on_annulus {r ρ : ℝ} (_ : 0 < r) (hρ : 0 < ρ)
    {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    ρ / 2 ≤ rhoTwo p.1 (r ^ 2 - p.2) := by
  rcases (mem_parabolicCylinder.mp hp.1) with ⟨hspace, hlow, hupp⟩
  have hnot : ¬ (vec3EuclideanNorm p.1 < ρ / 2 ∧
      -(ρ / 2) ^ 2 < p.2 ∧ p.2 ≤ 0) := by
    have hnot0 := hp.2
    change ¬ (vec3EuclideanNorm (p.1 - 0) < ρ / 2 ∧
      0 - (ρ / 2) ^ 2 < p.2 ∧ p.2 ≤ 0) at hnot0
    simpa only [sub_zero, zero_sub] using hnot0
  by_cases hsmall : vec3EuclideanNorm p.1 < ρ / 2
  · have htime : p.2 ≤ -(ρ / 2) ^ 2 := by
      exact le_of_not_gt fun hgt => hnot ⟨hsmall, hgt, hupp⟩
    have hτ : (ρ / 2) ^ 2 ≤ r ^ 2 - p.2 := by
      nlinarith only [sq_nonneg r, htime]
    have hsqrt : ρ / 2 ≤ Real.sqrt (r ^ 2 - p.2) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (r ^ 2 - p.2) := Real.sqrt_nonneg _
      have hsqrt_sq : (Real.sqrt (r ^ 2 - p.2)) ^ 2 = r ^ 2 - p.2 := by
        exact Real.sq_sqrt (by nlinarith only [hτ])
      apply (sq_le_sq₀ (by positivity) hsqrt_nonneg).mp
      simpa only [hsqrt_sq] using hτ
    unfold rhoTwo
    exact hsqrt.trans (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg _))
  · have hlarge : ρ / 2 ≤ vec3EuclideanNorm p.1 := le_of_not_gt hsmall
    unfold rhoTwo
    exact hlarge.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))

lemma backwardHeatTestFunction_upper_on_annulus {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (_ : r ≤ ρ / 2) {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    backwardHeatTestFunction r p.1 p.2 ≤ 8000000 * r ^ 2 / ρ ^ 3 := by
  rcases (mem_parabolicCylinder.mp hp.1) with ⟨_, hlow, hupp⟩
  have hτ : 0 < r ^ 2 - p.2 := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hrho := rhoTwo_ge_half_on_annulus hr hρ hp
  have hG := heatKernel_le_rho_inv_cube (x := p.1) hτ
  have hdiv : 1000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 3 ≤ 8000000 / ρ ^ 3 := by
    calc
      1000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 3 ≤
          1000 / (ρ / 2) ^ 3 := by gcongr
      _ = 8000 / ρ ^ 3 := by
        field_simp [hρ.ne']
        norm_num
      _ ≤ 8000000 / ρ ^ 3 := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rw [backwardHeatTestFunction]
  calc
    r ^ 2 * heatKernel p.1 (r ^ 2 - p.2) ≤
        r ^ 2 * (1000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 3) := by gcongr
    _ ≤ r ^ 2 * (8000000 / ρ ^ 3) := by gcongr
    _ = 8000000 * r ^ 2 / ρ ^ 3 := by ring

lemma backwardHeatTestGradient_upper_on_annulus {r ρ : ℝ} (hr : 0 < r)
    (hρ : 0 < ρ) (_ : r ≤ ρ / 2) {p : ParabolicPoint}
    (hp : p ∈ parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    backwardHeatTestGradientNorm r p.1 p.2 ≤ 5000000 * r ^ 2 / ρ ^ 4 := by
  rcases (mem_parabolicCylinder.mp hp.1) with ⟨_, hlow, hupp⟩
  have hτ : 0 < r ^ 2 - p.2 := by
    nlinarith only [sq_pos_of_pos hr, hupp]
  have hrho := rhoTwo_ge_half_on_annulus hr hρ hp
  have hG := heatKernelGradientNorm_le_rho_inv_four (x := p.1) hτ
  have hdiv : 300000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 4 ≤ 5000000 / ρ ^ 4 := by
    calc
      300000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 4 ≤
          300000 / (ρ / 2) ^ 4 := by gcongr
      _ = 4800000 / ρ ^ 4 := by
        field_simp [hρ.ne']
        norm_num
      _ ≤ 5000000 / ρ ^ 4 := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  rw [backwardHeatTestGradientNorm]
  calc
    r ^ 2 * heatKernelGradientNorm p.1 (r ^ 2 - p.2) ≤
        r ^ 2 * (300000 / rhoTwo p.1 (r ^ 2 - p.2) ^ 4) := by gcongr
    _ ≤ r ^ 2 * (5000000 / ρ ^ 4) := by gcongr
    _ = 5000000 * r ^ 2 / ρ ^ 4 := by ring

end CKN.Foundation.Heat
