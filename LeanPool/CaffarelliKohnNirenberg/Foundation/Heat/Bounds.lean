/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.PolyExpBounds

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Kernel

/-!
# Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

lemma abs_vec3_component_le_norm (x : Vec3) (i : Fin 3) :
    |x i| ≤ vec3EuclideanNorm x := by
  have hi : (x i) ^ 2 ≤ ∑ j, x j ^ 2 := by
    exact Finset.single_le_sum (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hs : 0 ≤ vec3EuclideanNorm x := vec3EuclideanNorm_nonneg x
  rw [← sq_le_sq₀ (abs_nonneg (x i)) hs, sq_abs, vec3EuclideanNorm_sq]
  exact hi

/-- Sum of absolute spatial derivatives of the heat kernel. -/
@[expose]
def heatKernelGradientNorm (x : Vec3) (t : ℝ) : ℝ :=
  ∑ i, |heatKernelSpaceDerivative x t i|

/-- Time derivative of a spatial heat-kernel derivative, extended by zero to nonpositive time. -/
@[expose]
def heatKernelTimeGradientDerivative (x : Vec3) (t : ℝ) (i : Fin 3) : ℝ :=
  if 0 < t then
    (x i) / (2 * t ^ 2) * heatKernel x t +
      (-(x i) / (2 * t)) *
        heatKernelTimeDerivative x t
  else 0

/-- Sum of absolute time derivatives of the spatial heat-kernel gradient. -/
@[expose]
def heatKernelTimeGradientNorm (x : Vec3) (t : ℝ) : ℝ :=
  ∑ i, |heatKernelTimeGradientDerivative x t i|

private lemma heatKernel_space_derivative_abs_le {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    |heatKernelSpaceDerivative x t i| ≤
      vec3EuclideanNorm x / (2 * t) * heatKernel x t := by
  rw [heatKernelSpaceDerivative, ite_eq_left ht, abs_mul, abs_div, abs_neg]
  rw [abs_of_pos (by positivity : 0 < (2 * t : ℝ)),
    abs_of_nonneg (heatKernel_nonneg x t)]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (abs_vec3_component_le_norm x i) (by positivity))
    (heatKernel_nonneg x t)

private lemma heatKernel_time_derivative_abs_le {x : Vec3} {t : ℝ}
    (ht : 0 < t) :
    |heatKernelTimeDerivative x t| ≤
      heatKernel x t *
        (((∑ i, x i ^ 2) / (4 * t) + (3 : ℝ) / 2) / t) := by
  rw [heatKernelTimeDerivative, ite_eq_left ht, abs_mul,
    abs_of_nonneg (heatKernel_nonneg x t)]
  have hq : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _hi => sq_nonneg (x i)
  have hcoef :
      |(∑ i, x i ^ 2) / (4 * t ^ 2) - (3 : ℝ) / (2 * t)| ≤
        ((∑ i, x i ^ 2) / (4 * t) + (3 : ℝ) / 2) / t := by
    calc
      |(∑ i, x i ^ 2) / (4 * t ^ 2) - (3 : ℝ) / (2 * t)| ≤
          |(∑ i, x i ^ 2) / (4 * t ^ 2)| + |(3 : ℝ) / (2 * t)| :=
        abs_sub _ _
      _ = ((∑ i, x i ^ 2) / (4 * t) + (3 : ℝ) / 2) / t := by
        rw [abs_of_nonneg, abs_of_nonneg]
        · field_simp
        · positivity
        · positivity
  exact mul_le_mul_of_nonneg_left hcoef (heatKernel_nonneg x t)

private lemma heatKernel_time_gradient_abs_le {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    |heatKernelTimeGradientDerivative x t i| ≤
        vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t *
        (((∑ j, x j ^ 2) / (4 * t) + (5 : ℝ) / 2)) := by
  have hfirst :
      |(x i) / (2 * t ^ 2) * heatKernel x t| ≤
        vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < (2 * t ^ 2 : ℝ)),
      abs_of_nonneg (heatKernel_nonneg x t)]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (abs_vec3_component_le_norm x i) (by positivity))
      (heatKernel_nonneg x t)
  have hsecond :
      |(-(x i) / (2 * t)) * heatKernelTimeDerivative x t| ≤
        vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t *
          (((∑ j, x j ^ 2) / (4 * t) + (3 : ℝ) / 2)) := by
    rw [abs_mul, abs_div, abs_neg,
      abs_of_pos (by positivity : 0 < (2 * t : ℝ))]
    have hxi : |x i| / (2 * t) ≤ vec3EuclideanNorm x / (2 * t) :=
      div_le_div_of_nonneg_right (abs_vec3_component_le_norm x i) (by positivity)
    have hleft : 0 ≤ vec3EuclideanNorm x / (2 * t) := by
      exact div_nonneg (vec3EuclideanNorm_nonneg x) (by positivity)
    calc
      |x i| / (2 * t) * |heatKernelTimeDerivative x t| ≤
          vec3EuclideanNorm x / (2 * t) * |heatKernelTimeDerivative x t| :=
        mul_le_mul_of_nonneg_right hxi (abs_nonneg _)
      _ ≤ vec3EuclideanNorm x / (2 * t) *
          (heatKernel x t * (((∑ j, x j ^ 2) / (4 * t) + (3 : ℝ) / 2) / t)) :=
        mul_le_mul_of_nonneg_left (heatKernel_time_derivative_abs_le ht) hleft
      _ = vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t *
          (((∑ j, x j ^ 2) / (4 * t) + (3 : ℝ) / 2)) := by
        field_simp
  calc
    |heatKernelTimeGradientDerivative x t i| =
        |(x i) / (2 * t ^ 2) * heatKernel x t +
          (-(x i) / (2 * t)) * heatKernelTimeDerivative x t| := by
      rw [heatKernelTimeGradientDerivative, ite_eq_left ht]
    _ ≤
        |(x i) / (2 * t ^ 2) * heatKernel x t| +
          |(-(x i) / (2 * t)) * heatKernelTimeDerivative x t| :=
      abs_add_le _ _
    _ ≤
        vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t +
          (vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t *
            (((∑ j, x j ^ 2) / (4 * t) + (3 : ℝ) / 2))) :=
      add_le_add hfirst hsecond
    _ = vec3EuclideanNorm x / (2 * t ^ 2) * heatKernel x t *
        (((∑ j, x j ^ 2) / (4 * t) + (5 : ℝ) / 2)) := by ring

lemma heatKernel_gradient_rho_four_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    rhoTwo x t ^ 4 * heatKernelGradientNorm x t ≤ 300000 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ i, x i ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ i, x i ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hgrad : heatKernelGradientNorm x t ≤
      3 * (s / (2 * t)) * heatKernel x t := by
    unfold heatKernelGradientNorm
    calc
      ∑ i, |heatKernelSpaceDerivative x t i| ≤
          ∑ i, s / (2 * t) * heatKernel x t :=
        Finset.sum_le_sum fun i _hi => heatKernel_space_derivative_abs_le ht i
      _ = 3 * (s / (2 * t)) * heatKernel x t := by
        simp only [Finset.sum_const, Finset.card_fin]
        ring
  have hscaled : rhoTwo x t ^ 4 * heatKernelGradientNorm x t ≤
      (3 / 2 : ℝ) * u * (1 + u) ^ 4 * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 4 * heatKernelGradientNorm x t ≤
          (z * (1 + u)) ^ 4 * (3 * (s / (2 * t)) * heatKernel x t) :=
        mul_le_mul_of_nonneg_left hgrad (by positivity)
      _ ≤ (z * (1 + u)) ^ 4 * (3 * (s / (2 * t)) *
          (z ^ (-(3 : ℝ)) * Real.exp (-a))) := by
        gcongr
      _ = (3 / 2 : ℝ) * u * (1 + u) ^ 4 * Real.exp (-a) := by
        rw [hsu, ← htz, heat_rpow_neg_three z hz]
        field_simp [hz.ne']
  calc
    rhoTwo x t ^ 4 * heatKernelGradientNorm x t ≤
        (3 / 2 : ℝ) * u * (3 * (1 + a)) ^ 4 * Real.exp (-a) :=
      hscaled.trans (by gcongr)
    _ = (3 / 2 : ℝ) * u * 81 * ((1 + a) ^ 4 * Real.exp (-a)) := by ring
    _ ≤ (3 / 2 : ℝ) * (1 + a) * 81 *
        ((1 + a) ^ 4 * Real.exp (-a)) := by
      gcongr
      have hpoly : 0 ≤ u ^ 2 - 4 * u + 4 := by
        nlinarith only [sq_nonneg (u - 2)]
      nlinarith only [hua, hpoly]
    _ = (3 / 2 : ℝ) * 81 * ((1 + a) ^ 5 * Real.exp (-a)) := by ring
    _ ≤ (3 / 2 : ℝ) * 81 *
        ((2 : ℝ) ^ (5 - 1) * (1 + (Nat.factorial 5 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (one_add_pow_exp_neg_le (n := 5) ha)
        (by positivity)
    _ ≤ 300000 := by norm_num

lemma heatKernel_time_derivative_rho_five_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    rhoTwo x t ^ 5 * |heatKernelTimeDerivative x t| ≤ 10000000 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ i, x i ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ i, x i ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hscaled : rhoTwo x t ^ 5 * |heatKernelTimeDerivative x t| ≤
      (3 / 2 : ℝ) * (1 + u) ^ 5 * (1 + a) * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 5 * |heatKernelTimeDerivative x t| ≤
      (z * (1 + u)) ^ 5 *
            (heatKernel x t * ((a + (3 : ℝ) / 2) / t)) := by
        gcongr
        simpa [a] using heatKernel_time_derivative_abs_le ht
      _ ≤ (z * (1 + u)) ^ 5 *
          ((z ^ (-(3 : ℝ)) * Real.exp (-a)) * ((a + (3 : ℝ) / 2) / t)) := by
        gcongr
      _ ≤ (3 / 2 : ℝ) * (1 + u) ^ 5 * (1 + a) * Real.exp (-a) := by
        have ha3 : a + (3 : ℝ) / 2 ≤ (3 / 2 : ℝ) * (1 + a) := by
          nlinarith only [ha]
        rw [← htz, heat_rpow_neg_three z hz]
        field_simp [hz.ne']
        nlinarith only [ha3]
  calc
    rhoTwo x t ^ 5 * |heatKernelTimeDerivative x t| ≤
        (3 / 2 : ℝ) * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := by
      exact hscaled.trans (by gcongr)
    _ = (3 / 2 : ℝ) * 243 * ((1 + a) ^ 6 * Real.exp (-a)) := by ring
    _ ≤ (3 / 2 : ℝ) * 243 *
        ((2 : ℝ) ^ (6 - 1) * (1 + (Nat.factorial 6 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (one_add_pow_exp_neg_le (n := 6) ha)
        (by positivity)
    _ ≤ 10000000 := by norm_num

lemma heatKernel_time_gradient_rho_six_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    rhoTwo x t ^ 6 * heatKernelTimeGradientNorm x t ≤ 30000000000 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ i, x i ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ i, x i ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hmix : heatKernelTimeGradientNorm x t ≤
      3 * (s / (2 * t ^ 2)) * heatKernel x t * (a + (5 : ℝ) / 2) := by
    unfold heatKernelTimeGradientNorm
    calc
      ∑ i, |heatKernelTimeGradientDerivative x t i| ≤
          ∑ i, s / (2 * t ^ 2) * heatKernel x t *
            (((∑ j, x j ^ 2) / (4 * t) + (5 : ℝ) / 2)) :=
        Finset.sum_le_sum fun i _hi => by
          simpa [a] using heatKernel_time_gradient_abs_le ht i
      _ = 3 * (s / (2 * t ^ 2)) * heatKernel x t * (a + (5 : ℝ) / 2) := by
        simp only [Finset.sum_const, Finset.card_fin]
        ring
  have hscaled : rhoTwo x t ^ 6 * heatKernelTimeGradientNorm x t ≤
      (3 / 2 : ℝ) * u * (1 + u) ^ 6 * (a + (5 : ℝ) / 2) * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 6 * heatKernelTimeGradientNorm x t ≤
          (z * (1 + u)) ^ 6 *
            (3 * (s / (2 * t ^ 2)) * heatKernel x t * (a + (5 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmix (by positivity)
      _ ≤ (z * (1 + u)) ^ 6 *
          (3 * (s / (2 * t ^ 2)) *
            (z ^ (-(3 : ℝ)) * Real.exp (-a)) * (a + (5 : ℝ) / 2)) := by
        gcongr
      _ = (3 / 2 : ℝ) * u * (1 + u) ^ 6 *
          (a + (5 : ℝ) / 2) * Real.exp (-a) := by
        rw [hsu, ← htz, heat_rpow_neg_three z hz]
        field_simp [hz.ne']
  calc
    rhoTwo x t ^ 6 * heatKernelTimeGradientNorm x t ≤
        (3 / 2 : ℝ) * (2 * (1 + a)) * (3 * (1 + a)) ^ 6 *
          ((5 / 2 : ℝ) * (1 + a)) * Real.exp (-a) := by
      have hu_le : u ≤ 2 * (1 + a) := by
        nlinarith only [hua, sq_nonneg (u - 2)]
      have ha5 : a + (5 : ℝ) / 2 ≤ (5 / 2 : ℝ) * (1 + a) := by
        nlinarith only [ha]
      exact hscaled.trans (by gcongr)
    _ = (15 / 2 : ℝ) * 729 * ((1 + a) ^ 8 * Real.exp (-a)) := by ring
    _ ≤ (15 / 2 : ℝ) * 729 *
        ((2 : ℝ) ^ (8 - 1) * (1 + (Nat.factorial 8 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (one_add_pow_exp_neg_le (n := 8) ha)
        (by positivity)
    _ ≤ 30000000000 := by norm_num

lemma heatKernel_rho_cube_le {x : Vec3} {t : ℝ} (ht : 0 < t) :
    rhoTwo x t ^ 3 * heatKernel x t ≤ 1000 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ i, x i ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := by exact vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq]
    rw [htz]
    field_simp [htz]
  have hu_le : u ≤ 2 * (1 + a) := by
    nlinarith only [hua, sq_nonneg (u - 1)]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ i, x i ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right (heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  rw [hrho]
  calc
    (z * (1 + u)) ^ 3 * heatKernel x t ≤
        (z * (1 + u)) ^ 3 * (z ^ (-(3 : ℝ)) * Real.exp (-a)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = (1 + u) ^ 3 * Real.exp (-a) := by
      rw [mul_pow, ← Real.rpow_natCast, Real.rpow_neg hz.le]
      field_simp
      norm_num
    _ ≤ (3 * (1 + a)) ^ 3 * Real.exp (-a) := by
      gcongr
    _ = 27 * ((1 + a) ^ 3 * Real.exp (-a)) := by ring
    _ ≤ 27 * ((2 : ℝ) ^ (3 - 1) * (1 + (Nat.factorial 3 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (one_add_pow_exp_neg_le (n := 3) ha)
        (by norm_num)
    _ ≤ 1000 := by norm_num

private lemma rhoTwo_pos {x : Vec3} {t : ℝ} (ht : 0 < t) : 0 < rhoTwo x t := by
  unfold rhoTwo
  exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg x) (Real.sqrt_pos.2 ht)

lemma heatKernel_le_rho_inv_cube {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel x t ≤ 1000 / rhoTwo x t ^ 3 := by
  apply (le_div_iff₀ (pow_pos (rhoTwo_pos ht) 3)).2
  calc
    heatKernel x t * rhoTwo x t ^ 3 = rhoTwo x t ^ 3 * heatKernel x t := by ring
    _ ≤ 1000 := heatKernel_rho_cube_le ht

lemma heatKernelGradientNorm_le_rho_inv_four {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernelGradientNorm x t ≤ 300000 / rhoTwo x t ^ 4 := by
  apply (le_div_iff₀ (pow_pos (rhoTwo_pos ht) 4)).2
  calc
    heatKernelGradientNorm x t * rhoTwo x t ^ 4 =
        rhoTwo x t ^ 4 * heatKernelGradientNorm x t := by ring
    _ ≤ 300000 := heatKernel_gradient_rho_four_le ht

lemma heatKernelTimeDerivative_le_rho_inv_five {x : Vec3} {t : ℝ} (ht : 0 < t) :
    |heatKernelTimeDerivative x t| ≤ 10000000 / rhoTwo x t ^ 5 := by
  apply (le_div_iff₀ (pow_pos (rhoTwo_pos ht) 5)).2
  calc
    |heatKernelTimeDerivative x t| * rhoTwo x t ^ 5 =
        rhoTwo x t ^ 5 * |heatKernelTimeDerivative x t| := by ring
    _ ≤ 10000000 := heatKernel_time_derivative_rho_five_le ht

lemma heatKernelTimeGradientNorm_le_rho_inv_six {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernelTimeGradientNorm x t ≤ 30000000000 / rhoTwo x t ^ 6 := by
  apply (le_div_iff₀ (pow_pos (rhoTwo_pos ht) 6)).2
  calc
    heatKernelTimeGradientNorm x t * rhoTwo x t ^ 6 =
        rhoTwo x t ^ 6 * heatKernelTimeGradientNorm x t := by ring
    _ ≤ 30000000000 := heatKernel_time_gradient_rho_six_le ht

lemma heatKernelSpaceDerivative_abs_le_rho_inv_four {x : Vec3} {t : ℝ}
    (ht : 0 < t) (i : Fin 3) :
    |heatKernelSpaceDerivative x t i| ≤ 300000 / rhoTwo x t ^ 4 := by
  have hcomponent : |heatKernelSpaceDerivative x t i| ≤ heatKernelGradientNorm x t := by
    unfold heatKernelGradientNorm
    exact Finset.single_le_sum
      (fun j _hj => abs_nonneg (heatKernelSpaceDerivative x t j))
      (Finset.mem_univ i)
  exact hcomponent.trans (heatKernelGradientNorm_le_rho_inv_four ht)

end CKN.Foundation.Heat
