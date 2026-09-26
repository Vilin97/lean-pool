/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The three-dimensional heat kernel

This file fixes the Gaussian normalization used by the parabolic estimates.
The spatial variable is the repository's `Fin 3 → ℝ` type, and the spatial
quadratic form is written as a finite sum so that it is independent of the
ambient sup norm on the function space.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! ### Definitions and elementary identities -/

/-- Three-dimensional Gaussian heat kernel, extended by zero to nonpositive time. -/
@[expose]
def heatKernel (x : Vec3) (t : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
      Real.exp (-(∑ i, x i ^ 2) / (4 * t))
  else 0

/-- Causal heat kernel on parabolic points. -/
@[expose]
def heatKernelPlus (p : ParabolicPoint) : ℝ :=
  if 0 < p.2 then heatKernel p.1 p.2 else 0

/-- Sum of spatial Euclidean length and the square root of time used in kernel estimates. -/
@[expose]
def rhoTwo (x : Vec3) (t : ℝ) : ℝ :=
  vec3EuclideanNorm x + Real.sqrt t

lemma vec3EuclideanNorm_sq (x : Vec3) :
    (vec3EuclideanNorm x) ^ 2 = ∑ i, x i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (x i))

lemma heatKernel_eq_zero_of_nonpos {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    heatKernel x t = 0 := by
  simp [heatKernel, not_lt.mpr ht]

lemma heatKernel_eq_formula {x : Vec3} {t : ℝ} (ht : 0 < t) :
  heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t)) := by
  rw [heatKernel, ite_eq_left ht, vec3EuclideanNorm_sq]

lemma heatKernel_eq_formula_sum {x : Vec3} {t : ℝ} (ht : 0 < t) :
    heatKernel x t =
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) := by
  rw [heatKernel_eq_formula ht, vec3EuclideanNorm_sq]

lemma heatKernel_nonneg (x : Vec3) (t : ℝ) : 0 ≤ heatKernel x t := by
  by_cases ht : 0 < t
  · rw [heatKernel_eq_formula ht]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.exp_pos _).le
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)]

lemma heatKernel_pos {x : Vec3} {t : ℝ} (ht : 0 < t) :
    0 < heatKernel x t := by
  rw [heatKernel_eq_formula ht]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

lemma heatKernelPlus_eq_heatKernel (p : ParabolicPoint) :
    heatKernelPlus p = heatKernel p.1 p.2 := by
  by_cases ht : 0 < p.2
  · simp [heatKernelPlus, ht]
  · rw [heatKernel_eq_zero_of_nonpos (le_of_not_gt ht)]
    simp [heatKernelPlus, ht]


lemma heatKernelPlus_eq_zero_of_nonpos {x : Vec3} {t : ℝ} (ht : t ≤ 0) :
    heatKernelPlus (x, t) = 0 := by
  simp [heatKernelPlus, not_lt.mpr ht]

private lemma gaussian_sum_exp_eq_prod (x : Vec3) (t : ℝ) :
    Real.exp (-(∑ i, x i ^ 2) / (4 * t)) =
      ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2) := by
  rw [show -(∑ i, x i ^ 2) / (4 * t) =
      ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) by
    calc
      -(∑ i, x i ^ 2) / (4 * t) =
          (-1 / (4 * t)) * (∑ i, x i ^ 2) := by
            field_simp
      _ = ∑ i, (-1 / (4 * t)) * (x i) ^ 2 := by rw [Finset.mul_sum]
      _ = ∑ i, (-(1 / (4 * t)) * (x i) ^ 2) := by ring_nf]
  exact Real.exp_sum Finset.univ (fun i => -(1 / (4 * t)) * (x i) ^ 2)

private lemma gaussian_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * t))) volume := by
  rw [show volume = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) by
    exact volume_pi]
  have hprod : Integrable
      (fun x : Vec3 => ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2))
      (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) := by
    exact Integrable.fintype_prod (ι := Fin 3) (E := ℝ)
      (μ := fun _ : Fin 3 => (volume : Measure ℝ)) (fun _hi => by
      convert integrable_exp_neg_mul_sq
        (by positivity : 0 < (1 / (4 * t) : ℝ)) using 1)
  exact hprod.congr (Filter.Eventually.of_forall fun x =>
    (gaussian_sum_exp_eq_prod x t).symm)

lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernel x t) volume := by
  rw [show (fun x : Vec3 => heatKernel x t) = fun x : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) by
    funext x
    exact heatKernel_eq_formula_sum ht]
  exact (gaussian_integrable t ht).const_mul _

lemma gaussian_integral (t : ℝ) (ht : 0 < t) :
    ∫ x : Vec3, Real.exp (-(∑ i, x i ^ 2) / (4 * t)) =
      (Real.sqrt (4 * Real.pi * t)) ^ (3 : ℕ) := by
  rw [show volume = Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)) by
    exact volume_pi]
  have hfun : (fun x : Vec3 => Real.exp (-(∑ i, x i ^ 2) / (4 * t))) =
      (fun x : Vec3 => ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2)) := by
    funext x
    exact gaussian_sum_exp_eq_prod x t
  have hprod := integral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (fun _ : Fin 3 => fun y : ℝ => Real.exp (-(1 / (4 * t)) * y ^ 2))
  rw [hfun]
  rw [show (∫ x : Vec3, ∏ i, Real.exp (-(1 / (4 * t)) * (x i) ^ 2)
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) =
      ∏ i : Fin 3, ∫ y : ℝ, Real.exp (-(1 / (4 * t)) * y ^ 2) by
    exact hprod]
  simp only [Finset.prod_const, Finset.card_fin]
  rw [integral_gaussian (1 / (4 * t))]
  congr 1
  field_simp [ht.ne']

lemma heatKernel_integral (t : ℝ) (ht : 0 < t) :
    ∫ x : Vec3, heatKernel x t = 1 := by
  rw [show (fun x : Vec3 => heatKernel x t) = fun x : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i, x i ^ 2) / (4 * t)) by
    funext x
    exact heatKernel_eq_formula_sum ht]
  rw [integral_const_mul, gaussian_integral t ht]
  have hbase : 0 < 4 * Real.pi * t := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hbase.le]
  have hexp : (1 / 2 : ℝ) * (↑(3 : ℕ) : ℝ) = (3 : ℝ) / 2 := by norm_num
  rw [hexp]
  rw [← Real.rpow_add hbase]
  simp only [show -(3 : ℝ) / 2 + (3 : ℝ) / 2 = 0 by ring, Real.rpow_zero]

lemma heatKernelPlus_nonneg (p : ParabolicPoint) : 0 ≤ heatKernelPlus p := by
  rw [heatKernelPlus_eq_heatKernel]
  exact heatKernel_nonneg _ _

end CKN.Foundation.Heat
