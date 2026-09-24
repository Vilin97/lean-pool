/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBridge
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantFinite
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareConstantPos
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallFaithfulL1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormTriangle
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallMemLp
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Finiteness

/-!
# The scale-explicit Sobolev–Poincaré inequalities on Euclidean balls

This file records the three clauses of the ball lemma together with one
constant chosen independently of the ball and the functions.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

private theorem euclideanBall_eq_vec3Ball_faithful {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- A single absolute constant for all three clauses of the ball lemma. -/
noncomputable def sobolevPoincareFaithfulC5 : ℝ :=
  1 + sobolevPoincareL6Constant.toReal +
    (2 * sobolevPoincareL6Constant +
      2 * sobolevPoincareBallFullConstant).toReal +
    Real.sqrt 3 * poincareSobolevL1Constant.toReal *
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ)

/-- The constant in the existing mean-zero L⁶ estimate is nonnegative. -/
theorem sobolevPoincareL6Constant_nonneg :
    0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg

/-- The chosen mean-zero Sobolev constant is nonzero, by the bump-function lower bound. -/
theorem sobolevPoincareL6Constant_pos_faithful : 0 < sobolevPoincareL6Constant :=
  sobolevPoincareL6Constant_pos

/-- `C₅` is positive. -/
theorem sobolevPoincareFaithfulC5_pos : 0 < sobolevPoincareFaithfulC5 := by
  dsimp [sobolevPoincareFaithfulC5]
  positivity

private theorem sobolevPoincareL6Constant_le_ofReal_C5 :
    sobolevPoincareL6Constant ≤ ENNReal.ofReal sobolevPoincareFaithfulC5 := by
  rw [← ofReal_toReal_sobolevPoincareL6Constant]
  apply ENNReal.ofReal_le_ofReal
  dsimp [sobolevPoincareFaithfulC5]
  calc
    sobolevPoincareL6Constant.toReal ≤
        1 + sobolevPoincareL6Constant.toReal :=
      le_add_of_nonneg_left (by norm_num)
    _ ≤ 1 + sobolevPoincareL6Constant.toReal +
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant).toReal :=
      le_add_of_nonneg_right ENNReal.toReal_nonneg
    _ ≤ 1 + sobolevPoincareL6Constant.toReal +
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant).toReal +
          Real.sqrt 3 * poincareSobolevL1Constant.toReal *
            (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) :=
      le_add_of_nonneg_right (by positivity)

private theorem sobolevPoincareFullConstant_le_ofReal_C5 :
    2 * sobolevPoincareL6Constant + 2 * sobolevPoincareBallFullConstant ≤
      ENNReal.ofReal sobolevPoincareFaithfulC5 := by
  have hfinite :
      2 * sobolevPoincareL6Constant + 2 * sobolevPoincareBallFullConstant ≠ ∞ := by
    have hfull : sobolevPoincareBallFullConstant ≠ ∞ := by
      rw [sobolevPoincareBallFullConstant]
      finiteness
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top (by norm_num) sobolevPoincareL6Constant_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) hfull
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  dsimp [sobolevPoincareFaithfulC5]
  have hnonneg : 0 ≤
      (2 * sobolevPoincareL6Constant +
        2 * sobolevPoincareBallFullConstant).toReal := ENNReal.toReal_nonneg
  calc
    (2 * sobolevPoincareL6Constant +
        2 * sobolevPoincareBallFullConstant).toReal ≤
        1 + sobolevPoincareL6Constant.toReal +
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant).toReal := by
      exact le_add_of_nonneg_left (by positivity)
    _ ≤ 1 + sobolevPoincareL6Constant.toReal +
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant).toReal +
          Real.sqrt 3 * poincareSobolevL1Constant.toReal *
            (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) :=
      le_add_of_nonneg_right (by positivity)

private theorem vec3GradientSum_le_euclidean_mul_sqrt_threeFaithful (v : Vec3) :
    (∑ i : Fin 3, |v i|) ≤ Real.sqrt 3 * vec3EuclideanNorm v :=
  sum_abs_le_sqrt_three_vec3EuclideanNormFaithful v

private theorem euclideanGradient_memLp_of_w1pFaithful
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : W1pFunction (euclideanBall x₀ r) 1) :
    MemLp (fun x => vec3EuclideanNorm (u.grad x)) 1
      (volume.restrict (euclideanBall x₀ r)) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let G : Vec3 → ℝ := w1pGradientNorm u
  have hBvol : volume B < ∞ := by
    change volume (euclideanBall x₀ r) < ∞
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply_univ] using hBvol
  have hGmem : MemLp G 1 (volume.restrict B) := by
    change MemLp (fun x => ∑ i : Fin 3, |u.grad x i|) 1 (volume.restrict B)
    exact memLp_finsetSum (p := (1 : ℝ≥0∞)) (μ := volume.restrict B)
      Finset.univ (fun i _ => (u.grad_memLp i).abs)
  have hGint : Integrable G (volume.restrict B) := memLp_one_iff_integrable.mp hGmem
  have hGradAEM (i : Fin 3) : AEMeasurable (fun x => u.grad x i)
      (volume.restrict B) := by
    exact (u.grad_memLp i).aestronglyMeasurable.aemeasurable
  have hNormAEM : AEMeasurable (fun x => vec3EuclideanNorm (u.grad x))
      (volume.restrict B) :=
    continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
      (aemeasurable_pi_iff.mpr hGradAEM)
  have hdom (x : Vec3) : vec3EuclideanNorm (u.grad x) ≤ G x := by
    exact vec3EuclideanNorm_le_sum_abs (u.grad x)
  have hNormInt : Integrable (fun x => vec3EuclideanNorm (u.grad x))
      (volume.restrict B) := by
    apply hGint.mono' hNormAEM.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact hdom x
  exact memLp_one_iff_integrable.mpr hNormInt

private theorem w1p_euclideanBall_gradient_integral_le_sqrt_three
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : W1pFunction (euclideanBall x₀ r) 1) :
    ∫ x in euclideanBall x₀ r, w1pGradientNorm u x ∂volume ≤
      Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
        vec3EuclideanNorm (u.grad x) ∂volume := by
  let B : Set Vec3 := euclideanBall x₀ r
  let G : Vec3 → ℝ := w1pGradientNorm u
  have hBvol : volume B < ∞ := by
    change volume (euclideanBall x₀ r) < ∞
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq]
    finiteness
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply_univ] using hBvol
  have hGmem : MemLp G 1 (volume.restrict B) := by
    change MemLp (fun x => ∑ i : Fin 3, |u.grad x i|) 1 (volume.restrict B)
    exact memLp_finsetSum (p := (1 : ℝ≥0∞)) (μ := volume.restrict B)
      Finset.univ (fun i _ => (u.grad_memLp i).abs)
  have hGint : Integrable G (volume.restrict B) := memLp_one_iff_integrable.mp hGmem
  have hNormMem := euclideanGradient_memLp_of_w1pFaithful x₀ hr u
  have hNormInt : Integrable (fun x => vec3EuclideanNorm (u.grad x))
      (volume.restrict B) := memLp_one_iff_integrable.mp hNormMem
  have hGbound (x : Vec3) : G x ≤ Real.sqrt 3 * vec3EuclideanNorm (u.grad x) := by
    exact sum_abs_le_sqrt_three_vec3EuclideanNormFaithful (u.grad x)
  calc
    ∫ x, G x ∂volume.restrict B ≤
        ∫ x, Real.sqrt 3 * vec3EuclideanNorm (u.grad x) ∂volume.restrict B :=
      integral_mono_ae hGint (hNormInt.const_mul (Real.sqrt 3))
        (ae_of_all (volume.restrict B) hGbound)
    _ = Real.sqrt 3 * ∫ x, vec3EuclideanNorm (u.grad x) ∂volume.restrict B :=
      integral_const_mul _ _
  
/-- The full scale-explicit (L^1) Poincaré clause on every Euclidean ball. -/
theorem sobolevPoincare_ball_L1_faithful
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : W1pFunction (euclideanBall x₀ r) 1) :
    ∫ x in euclideanBall x₀ r,
        |u.toFun x - average (volume.restrict (euclideanBall x₀ r)) u.toFun|
          ∂volume ≤
      sobolevPoincareFaithfulC5 * r *
        ∫ x in euclideanBall x₀ r, vec3EuclideanNorm (u.grad x) ∂volume := by
  let B : Set Vec3 := euclideanBall x₀ r
  let c : ℝ := Real.pi * 4 / 3
  have hvol : (volume B).toReal = r ^ 3 * c := by
    change (volume (euclideanBall x₀ r)).toReal = _
    rw [euclideanBall_eq_vec3Ball_faithful hr, volume_vec3Ball_eq,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal (by positivity)]
  have hvolroot : (volume B).toReal ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * r := by
    rw [hvol, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast r 3, ← Real.rpow_mul hr.le]
    norm_num
    ring
  have hgrad := w1p_euclideanBall_gradient_integral_le_sqrt_three x₀ hr u
  have hraw := w1p_euclideanBall_poincareL1_faithful x₀ hr u
  have hright_nonneg : 0 ≤ r * ∫ x in B, vec3EuclideanNorm (u.grad x) ∂volume :=
    mul_nonneg hr.le (integral_nonneg fun x => vec3EuclideanNorm_nonneg _)
  rw [hvolroot] at hraw
  have hcoef : poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) * Real.sqrt 3 ≤
      sobolevPoincareFaithfulC5 := by
    dsimp [sobolevPoincareFaithfulC5]
    calc
      poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) * Real.sqrt 3 =
          Real.sqrt 3 * poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) := by ring
      _ ≤ 1 + sobolevPoincareL6Constant.toReal +
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant).toReal +
          Real.sqrt 3 * poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) :=
        le_add_of_nonneg_left (by positivity)
  calc
    ∫ x in B, |u.toFun x - average (volume.restrict B) u.toFun| ∂volume ≤
        poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) * r *
          ∫ x in B, w1pGradientNorm u x ∂volume := by
            simpa [B, mul_assoc] using hraw
    _ ≤ poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) * r *
          (Real.sqrt 3 * ∫ x in B, vec3EuclideanNorm (u.grad x) ∂volume) :=
        mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = (poincareSobolevL1Constant.toReal * c ^ (1 / 3 : ℝ) * Real.sqrt 3) *
          (r * ∫ x in B, vec3EuclideanNorm (u.grad x) ∂volume) := by ring
    _ ≤ sobolevPoincareFaithfulC5 *
          (r * ∫ x in B, vec3EuclideanNorm (u.grad x) ∂volume) :=
        mul_le_mul_of_nonneg_right hcoef hright_nonneg
    _ = _ := by ring

/-- The mean-zero and full L⁶ clauses of Sobolev–Poincaré on every Euclidean ball. -/
theorem sobolevPoincare_ball_L6_faithful
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    (∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn 6 (vec3Ball x₀ r)
          (fun x => v.toFun x - average (volume.restrict (vec3Ball x₀ r)) v.toFun) ≤
        ENNReal.ofReal sobolevPoincareFaithfulC5 *
          weakGradientLpNormOn 2 (vec3Ball x₀ r) v.grad) ∧
    (∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn 6 (vec3Ball x₀ r) v.toFun ≤
        ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (weakGradientLpNormOn 2 (vec3Ball x₀ r) v.grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (vec3Ball x₀ r) v.toFun)) := by
  constructor
  · intro v
    have hball := euclideanBall_eq_vec3Ball_faithful (x₀ := x₀) hr
    have hweak := sobolevPoincare_L6_ball_weak x₀ hr v
    have hweak' :
        lpNormOn 6 (vec3Ball x₀ r)
            (fun x => v.toFun x - average (volume.restrict (vec3Ball x₀ r)) v.toFun) ≤
          sobolevPoincareL6Constant * weakGradientLpNormOn 2
            (vec3Ball x₀ r) v.grad := by
      simpa [hball] using hweak
    exact hweak'.trans (mul_le_mul_of_nonneg_right
      sobolevPoincareL6Constant_le_ofReal_C5 (by positivity))
  · intro v
    have hball := euclideanBall_eq_vec3Ball_faithful (x₀ := x₀) hr
    have hfull := h1SobolevBall_of_sobolevPoincare hr v
    have hfull' :
        lpNormOn 6 (vec3Ball x₀ r) v.toFun ≤
          (2 * sobolevPoincareL6Constant +
            2 * sobolevPoincareBallFullConstant) *
            (weakGradientLpNormOn 2 (vec3Ball x₀ r) v.grad +
              (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (vec3Ball x₀ r) v.toFun) := by
      simpa [hball] using hfull
    exact hfull'.trans (mul_le_mul_of_nonneg_right
      sobolevPoincareFullConstant_le_ofReal_C5 (by positivity))

/-- The three scale-explicit clauses of the paper's ball lemma, with one
constant chosen uniformly in the centre, radius, and function. -/
theorem sobolevPoincare_ball_faithful
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r) :
    (∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn 6 (vec3Ball x₀ r)
          (fun x => v.toFun x - average (volume.restrict (vec3Ball x₀ r)) v.toFun) ≤
        ENNReal.ofReal sobolevPoincareFaithfulC5 *
          weakGradientLpNormOn 2 (vec3Ball x₀ r) v.grad) ∧
    (∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn 6 (vec3Ball x₀ r) v.toFun ≤
        ENNReal.ofReal sobolevPoincareFaithfulC5 *
          (weakGradientLpNormOn 2 (vec3Ball x₀ r) v.grad +
            (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (vec3Ball x₀ r) v.toFun)) ∧
    (∀ u : W1pFunction (euclideanBall x₀ r) 1,
      ∫ x in euclideanBall x₀ r,
          |u.toFun x - average (volume.restrict (euclideanBall x₀ r)) u.toFun|
            ∂volume ≤
        sobolevPoincareFaithfulC5 * r *
          ∫ x in euclideanBall x₀ r, vec3EuclideanNorm (u.grad x) ∂volume) := by
  have hL6 := sobolevPoincare_ball_L6_faithful x₀ hr
  exact ⟨hL6.1, hL6.2,
    fun u => sobolevPoincare_ball_L1_faithful x₀ hr u⟩

end
end CKN
