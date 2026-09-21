/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernel1D
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Classical Euclidean heat evolution for tensor components

This module upgrades the coordinatewise integral estimates in `HeatKernel1D` to
actual second spatial derivatives of the `n`-dimensional heat semigroup.  It is
the analytic local model for the connection heat equation on symmetric
two-tensors: in a parallel frame the rough Laplacian acts componentwise.

The results here are deliberately stated first for scalar components.  Later in
the file they are assembled into finite matrix-valued fields and symmetry is
shown to be preserved by the constructed evolution.
-/

@[expose] public noncomputable section

open Real MeasureTheory Metric
open scoped Real ENNReal NNReal Topology

namespace RicciFlow
namespace AnalyticPDE

/-! ## Actual second coordinate derivatives -/

/-- The product Gaussian envelope needed to differentiate a coordinate of the
heat-semigroup gradient a second time is integrable. -/
lemma integrable_gaussianSecondEnvelope_erase_prod {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) (k : Fin n) :
    Integrable (fun y : Fin n → ℝ =>
      (((1 + |y k - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          * Real.exp (-(y k - x k) ^ 2 / (8 * t)))
        * ∏ j ∈ Finset.univ.erase k, heatKernel1D t (x j - y j)) := by
  classical
  have hb8 : 0 < (8 * t)⁻¹ := by positivity
  have h0 : Integrable (fun w : ℝ => Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
    integrable_exp_neg_mul_sq hb8
  have h1 : Integrable (fun w : ℝ => w ^ (1 : ℝ) * Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
  have h2 : Integrable (fun w : ℝ => w ^ (2 : ℝ) * Real.exp (-(8 * t)⁻¹ * w ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb8 (by norm_num)
  have hbase : Integrable (fun w : ℝ =>
      ((1 + |w|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
        * Real.exp (-w ^ 2 / (8 * t))) := by
    have hsum := (((h0.const_mul (1 / (4 * t ^ 2) + 1 / (2 * t))).add
      ((h1.abs).const_mul (1 / (2 * t ^ 2)))).add
      (h2.const_mul (1 / (4 * t ^ 2))))
    refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [Pi.add_apply, Real.rpow_one, Real.rpow_two]
    have hexp : -(8 * t)⁻¹ * w ^ 2 = -w ^ 2 / (8 * t) := by
      rw [neg_div, div_eq_inv_mul]
      ring
    rw [abs_mul, abs_of_pos (Real.exp_pos _), hexp, ← sq_abs w]
    ring
  have henv : Integrable (fun z : ℝ =>
      ((1 + |z - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
        * Real.exp (-(z - x k) ^ 2 / (8 * t))) :=
    hbase.comp_sub_right (x k)
  set F : Fin n → ℝ → ℝ := fun i z =>
    if i = k then
      ((1 + |z - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
        * Real.exp (-(z - x k) ^ 2 / (8 * t))
    else heatKernel1D t (x i - z) with hF
  have hprod : (fun y : Fin n → ℝ =>
      (((1 + |y k - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          * Real.exp (-(y k - x k) ^ 2 / (8 * t)))
        * ∏ j ∈ Finset.univ.erase k, heatKernel1D t (x j - y j))
      = fun y => ∏ i, F i (y i) := by
    funext y
    rw [(
      Finset.mul_prod_erase Finset.univ (fun i => F i (y i)) (Finset.mem_univ k)).symm]
    have hFk : F k (y k) =
        ((1 + |y k - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
          * Real.exp (-(y k - x k) ^ 2 / (8 * t)) := by
      simp only [hF, if_pos rfl]
    rw [hFk]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [hF, if_neg (Finset.ne_of_mem_erase hj)]
  have hvol : (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) := by
    rw [volume_pi]
  rw [hprod, hvol]
  refine Integrable.fin_nat_prod (f := F) (fun i => ?_)
  rcases eq_or_ne i k with hik | hik
  · subst hik
    simpa [hF] using henv
  · simp only [hF, if_neg hik]
    exact (integrable_heatKernel1D ht).comp_sub_left (x i)

/-- The coordinate derivative formula for `H_t f` is itself differentiable.
Its derivative is convolution with the second coordinate derivative of the
`n`-dimensional heat kernel. -/
theorem hasDerivAt_heatSemigroupND_coordGradient {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt
      (fun s => ∫ y : Fin n → ℝ,
        (heatKernelND t (Function.update x k s - y)
          * (-((Function.update x k s - y) k) / (2 * t))) * f y)
      (∫ y : Fin n → ℝ,
        (heatKernelND t (x - y)
          * (((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y)) (x k) := by
  classical
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    heatKernel1D t (s - y k) * (-(s - y k) / (2 * t))
      * (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) * f y with hF
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    heatKernel1D t (s - y k)
      * ((s - y k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))
      * (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) * f y with hF'
  set M : ℝ := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) * C with hM
  set bound : (Fin n → ℝ) → ℝ := fun y =>
    M * ((((1 + |y k - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
        * Real.exp (-(y k - x k) ^ 2 / (8 * t)))
      * ∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) with hbound
  have hFbase : F (x k) = fun y =>
      (heatKernelND t (x - y) * (-((x - y) k) / (2 * t))) * f y := by
    funext y
    simp only [hF]
    rw [heatKernelND_eq_update_mul n t (x - y) k]
    simp only [Pi.sub_apply]
    ring
  have hF'base : F' (x k) = fun y =>
      (heatKernelND t (x - y)
        * (((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) := by
    funext y
    simp only [hF']
    rw [heatKernelND_eq_update_mul n t (x - y) k]
    simp only [Pi.sub_apply]
    ring
  have hFmeas : ∀ᶠ s in nhds (x k),
      AEStronglyMeasurable (F s) (volume : Measure (Fin n → ℝ)) := by
    filter_upwards with s
    have hK : AEStronglyMeasurable (fun y : Fin n → ℝ => heatKernel1D t (s - y k)) := by
      exact ((continuous_heatKernel1D_space t).comp (by fun_prop)).aestronglyMeasurable
    have hlin : AEStronglyMeasurable (fun y : Fin n → ℝ => -(s - y k) / (2 * t)) := by
      exact (by fun_prop : Continuous (fun y : Fin n → ℝ => -(s - y k) / (2 * t))).aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun y : Fin n → ℝ =>
        ∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) := by
      apply Continuous.aestronglyMeasurable
      apply continuous_finsetProd
      intro j _
      exact (continuous_heatKernel1D_space t).comp (by fun_prop)
    refine (((hK.mul hlin).mul hprod).mul hfm).congr ?_
    filter_upwards with y
    simp only [hF, Pi.mul_apply]
  have hFint : Integrable (F (x k)) (volume : Measure (Fin n → ℝ)) := by
    rw [hFbase]
    exact integrable_deriv_coord_heatKernelND_sub_mul ht k x hfm hfb
  have hF'meas : AEStronglyMeasurable (F' (x k))
      (volume : Measure (Fin n → ℝ)) := by
    rw [hF'base]
    have hcoeff : AEStronglyMeasurable (fun y : Fin n → ℝ =>
        (x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
      fun_prop
    exact ((continuous_heatKernelND_sub t x).aestronglyMeasurable.mul hcoeff).mul hfm
  have hboundint : Integrable bound (volume : Measure (Fin n → ℝ)) := by
    simpa only [hbound, Pi.sub_apply] using
      (integrable_gaussianSecondEnvelope_erase_prod ht x k).const_mul M
  have hbnd : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ s ∈ Metric.ball (x k) 1, ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hzle : |s - x k| ≤ 1 := hs.le
    have hpre : (0 : ℝ) < (4 * π * t) ^ (-(1 : ℝ) / 2) :=
      heatKernel1D_prefactor_pos ht
    have hzx2 : (s - x k) ^ 2 ≤ 1 := by
      rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_one, Real.sqrt_sq_eq_abs]
      exact hzle
    set Eg := Real.exp (-(y k - x k) ^ 2 / (8 * t)) with hEg
    have hEgpos : 0 < Eg := Real.exp_pos _
    set P := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (1 / (4 * t)) with hP
    have hPpos : 0 < P := by positivity
    set Poly := (1 + |y k - x k|) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) with hPoly
    have hPolynn : 0 ≤ Poly := by rw [hPoly]; positivity
    have hK : heatKernel1D t (s - y k) ≤ P * Eg := by
      rw [hP, hEg, heatKernel1D_apply,
        mul_assoc ((4 * π * t) ^ (-(1 : ℝ) / 2)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hpre.le
      apply Real.exp_le_exp.mpr
      have hq : (s - y k) ^ 2 ≥ (y k - x k) ^ 2 / 2 - (s - x k) ^ 2 := by
        nlinarith [sq_nonneg ((y k - x k) - 2 * (s - x k))]
      rw [← sub_nonneg]
      have key : 1 / (4 * t) + -(y k - x k) ^ 2 / (8 * t)
          - -(s - y k) ^ 2 / (4 * t)
          = (2 - ((y k - x k) ^ 2 - 2 * (s - y k) ^ 2)) / (8 * t) := by
        field_simp
        ring
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hq, hzx2]
    have hzy : |s - y k| ≤ 1 + |y k - x k| := by
      have hsplit : s - y k = (s - x k) + (x k - y k) := by ring
      calc |s - y k| ≤ |s - x k| + |x k - y k| := by
            rw [hsplit]
            exact abs_add_le _ _
        _ ≤ 1 + |y k - x k| := by rw [abs_sub_comm (x k) (y k)]; linarith
    have hsqle : (s - y k) ^ 2 ≤ (1 + |y k - x k|) ^ 2 := by
      nlinarith [hzy, sq_abs (s - y k), abs_nonneg (s - y k), abs_nonneg (y k - x k)]
    have hpolybd :
        |(s - y k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤ Poly := by
      have hA : (0 : ℝ) ≤ (s - y k) ^ 2 / (4 * t ^ 2) := by positivity
      have hB : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
      have hstep1 : |(s - y k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
          ≤ (s - y k) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hstep2 : (s - y k) ^ 2 / (4 * t ^ 2)
          ≤ (1 + |y k - x k|) ^ 2 / (4 * t ^ 2) :=
        div_le_div_of_nonneg_right hsqle (by positivity)
      rw [hPoly]
      linarith
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hQnn : 0 ≤ ∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j) :=
      Finset.prod_nonneg (fun j _ => heatKernel1D_nonneg ht _)
    have hnorm : ‖F' s y‖ = heatKernel1D t (s - y k)
        * |(s - y k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
        * (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) * |f y| := by
      simp only [hF']
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (heatKernel1D_nonneg ht _), abs_of_nonneg hQnn]
    rw [hnorm]
    calc heatKernel1D t (s - y k)
            * |(s - y k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
            * (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) * |f y|
        ≤ (P * Eg) * Poly
            * (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j)) * C := by
          gcongr
      _ = bound y := by simp only [hbound, hM, hP, hEg, hPoly]; ring
  have hderiv : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ s ∈ Metric.ball (x k) 1, HasDerivAt (fun s' => F s' y) (F' s y) s := by
    filter_upwards with y s _
    have hin : HasDerivAt (fun s' : ℝ => s' - y k) 1 s := by
      simpa using (hasDerivAt_id s).sub_const (y k)
    have hbase := (hasDerivAt_heatKernel1D_space_second ht (s - y k)).comp s hin
    rw [mul_one] at hbase
    have hmul := (hbase.mul_const
      (∏ j ∈ Finset.univ.erase k, heatKernel1D t ((x - y) j))).mul_const (f y)
    simpa only [hF, hF', Function.comp_apply] using hmul
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Fin n → ℝ))) (F := F) (x₀ := x k) (bound := bound)
    (s := Metric.ball (x k) 1) (Metric.ball_mem_nhds (x k) one_pos)
    hFmeas hFint hF'meas hbnd hboundint hderiv
  have hfun : (fun s => ∫ y : Fin n → ℝ,
      (heatKernelND t (Function.update x k s - y)
        * (-((Function.update x k s - y) k) / (2 * t))) * f y)
      = fun s => ∫ y, F s y := by
    funext s
    apply integral_congr_ae
    filter_upwards with y
    simp only [hF]
    rw [heatKernelND_eq_update_mul n t (Function.update x k s - y) k]
    simp only [Function.update_self, Pi.sub_apply]
    have hp : (∏ j ∈ Finset.univ.erase k,
        heatKernel1D t (Function.update x k s j - y j))
        = ∏ j ∈ Finset.univ.erase k, heatKernel1D t (x j - y j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hp]
    ring
  rw [hfun, hF'base.symm]
  exact key.2

/-- The actual iterated coordinate derivative of the `n`-dimensional heat
semigroup is the convolution with the corresponding kernel second derivative. -/
theorem deriv2_heatSemigroupND_coord_eq_integral {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (deriv (fun s => heatSemigroupND t f (Function.update x k s))) (x k)
      = ∫ y : Fin n → ℝ,
        (heatKernelND t (x - y)
          * (((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) := by
  have hfirst : deriv (fun s => heatSemigroupND t f (Function.update x k s))
      = fun s => ∫ y : Fin n → ℝ,
        (heatKernelND t (Function.update x k s - y)
          * (-((Function.update x k s - y) k) / (2 * t))) * f y := by
    funext s
    exact (hasDerivAt_heatSemigroupND_coord_update ht x k hfm hfb s).deriv
  rw [hfirst]
  exact (hasDerivAt_heatSemigroupND_coordGradient ht x k hfm hfb).deriv

/-- The actual second coordinate derivative obeys the previously established
`C/t` smoothing estimate. -/
theorem abs_deriv2_heatSemigroupND_coord_le {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    |deriv (deriv (fun s => heatSemigroupND t f (Function.update x k s))) (x k)|
      ≤ C / t := by
  rw [deriv2_heatSemigroupND_coord_eq_integral ht x k hfm hfb]
  exact heatSemigroupND_coord_second_deriv_integral_bound ht x k hfm hfb

/-! ## Actual time derivative and the heat equation -/

/-- A translated all-coordinate Gaussian envelope with one quadratic factor is
integrable.  This is the common majorant for differentiating the
`n`-dimensional heat semigroup in time. -/
lemma integrable_gaussianTimeEnvelopeND {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ =>
      (∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t))
        * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t))) := by
  classical
  have hb6 : 0 < (6 * t)⁻¹ := by positivity
  have h0base : Integrable (fun z : ℝ => Real.exp (-(6 * t)⁻¹ * z ^ 2)) :=
    integrable_exp_neg_mul_sq hb6
  have h2base : Integrable (fun z : ℝ => z ^ (2 : ℝ) * Real.exp (-(6 * t)⁻¹ * z ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb6 (by norm_num)
  have h0 : ∀ j : Fin n,
      Integrable (fun z : ℝ => Real.exp (-(x j - z) ^ 2 / (6 * t))) := by
    intro j
    have h := h0base.comp_sub_left (x j)
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    have he : -(6 * t)⁻¹ * (x j - z) ^ 2 = -(x j - z) ^ 2 / (6 * t) := by
      rw [neg_div, div_eq_inv_mul]
      ring
    simp only [he]
  have h2 : ∀ j : Fin n, Integrable (fun z : ℝ =>
      ((x j - z) ^ 2 / t ^ 2 + 1 / t) * Real.exp (-(x j - z) ^ 2 / (6 * t))) := by
    intro j
    have hbase : Integrable (fun w : ℝ =>
        (w ^ 2 / t ^ 2 + 1 / t) * Real.exp (-w ^ 2 / (6 * t))) := by
      have hsum := (h2base.const_mul (1 / t ^ 2)).add (h0base.const_mul (1 / t))
      refine hsum.congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [Pi.add_apply, Real.rpow_two]
      have he : -(6 * t)⁻¹ * w ^ 2 = -w ^ 2 / (6 * t) := by
        rw [neg_div, div_eq_inv_mul]
        ring
      rw [he]
      ring
    exact hbase.comp_sub_left (x j)
  have hterm : ∀ i : Fin n, Integrable (fun y : Fin n → ℝ =>
      ((x i - y i) ^ 2 / t ^ 2 + 1 / t)
        * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t))) := by
    intro i
    set F : Fin n → ℝ → ℝ := fun j z =>
      if j = i then
        ((x j - z) ^ 2 / t ^ 2 + 1 / t) * Real.exp (-(x j - z) ^ 2 / (6 * t))
      else Real.exp (-(x j - z) ^ 2 / (6 * t)) with hF
    have hp : (fun y : Fin n → ℝ =>
        ((x i - y i) ^ 2 / t ^ 2 + 1 / t)
          * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)))
        = fun y => ∏ j, F j (y j) := by
      funext y
      have hG : Real.exp (-(x i - y i) ^ 2 / (6 * t))
          * ∏ j ∈ Finset.univ.erase i, Real.exp (-(x j - y j) ^ 2 / (6 * t))
          = ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)) :=
        Finset.mul_prod_erase Finset.univ
          (fun j => Real.exp (-(x j - y j) ^ 2 / (6 * t))) (Finset.mem_univ i)
      have hFp : F i (y i) * ∏ j ∈ Finset.univ.erase i, F j (y j)
          = ∏ j : Fin n, F j (y j) :=
        Finset.mul_prod_erase Finset.univ (fun j => F j (y j)) (Finset.mem_univ i)
      rw [← hG, ← hFp]
      simp only [hF, if_pos rfl]
      have heq : (∏ j ∈ Finset.univ.erase i, F j (y j))
          = ∏ j ∈ Finset.univ.erase i,
              Real.exp (-(x j - y j) ^ 2 / (6 * t)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [hF, if_neg (Finset.ne_of_mem_erase hj)]
      rw [heq]
      ring
    have hvol : (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) := by
      rw [volume_pi]
    rw [hp, hvol]
    refine Integrable.fin_nat_prod (f := F) (fun j => ?_)
    rcases eq_or_ne j i with hji | hji
    · subst j
      simpa [hF] using h2 i
    · simpa [hF, hji] using h0 j
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hterm i)
  refine hsum.congr (Filter.Eventually.of_forall (fun y => ?_))
  change (∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t)
      * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)))
    = (∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t))
      * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t))
  rw [Finset.sum_mul]

/-- The `n`-dimensional heat semigroup is differentiable at every positive
time.  The derivative is convolution with the kernel time derivative, written
in the equivalent Laplacian-coefficient form. -/
theorem hasDerivAt_heatSemigroupND_time {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    HasDerivAt (fun s => heatSemigroupND s f x)
      (∫ y : Fin n → ℝ, heatKernelND t (x - y)
        * (∑ i : Fin n, ((x - y) i ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) t := by
  classical
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hfb 0)
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y => heatKernelND s (x - y) * f y with hF
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    heatKernelND s (x - y)
      * (∑ i : Fin n, ((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))) * f y with hF'
  set P : ℝ := (2 * π * t) ^ (-(1 : ℝ) / 2) with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  set M : ℝ := P ^ n * C with hM
  set bound : (Fin n → ℝ) → ℝ := fun y =>
    M * ((∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t))
      * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t))) with hbound
  have hsNhd : Metric.ball t (t / 2) ∈ nhds t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have hFmeas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable (F s) (volume : Measure (Fin n → ℝ)) := by
    filter_upwards with s
    simp only [hF]
    exact (continuous_heatKernelND_sub s x).aestronglyMeasurable.mul hfm
  have hFint : Integrable (F t) (volume : Measure (Fin n → ℝ)) := by
    simp only [hF]
    exact integrable_heatKernelND_sub_mul ht x hfm hfb
  have hF'meas : AEStronglyMeasurable (F' t) (volume : Measure (Fin n → ℝ)) := by
    have hcoeff : AEStronglyMeasurable (fun y : Fin n → ℝ =>
        ∑ i : Fin n, ((x - y) i ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    change AEStronglyMeasurable
      (((fun y : Fin n → ℝ => heatKernelND t (x - y))
        * (fun y => ∑ i : Fin n, ((x - y) i ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))) * f)
        (volume : Measure (Fin n → ℝ))
    exact ((continuous_heatKernelND_sub t x).aestronglyMeasurable.mul hcoeff).mul hfm
  have hboundint : Integrable bound (volume : Measure (Fin n → ℝ)) := by
    simpa only [hbound] using (integrable_gaussianTimeEnvelopeND ht x).const_mul M
  have hbnd : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ s ∈ Metric.ball t (t / 2), ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hpair := abs_lt.1 hs
    have hslo : t / 2 < s := by linarith [hpair.1]
    have hshi : s < 3 * t / 2 := by linarith [hpair.2]
    have hspos : 0 < s := by linarith
    have h2πt : (0 : ℝ) < 2 * π * t := by positivity
    have hpref : (4 * π * s) ^ (-(1 : ℝ) / 2) ≤ P := by
      rw [hP]
      apply Real.rpow_le_rpow_of_nonpos h2πt (by nlinarith [Real.pi_pos, hslo])
      norm_num
    have h46 : 4 * s ≤ 6 * t := by linarith
    have hcoordK : ∀ i : Fin n, heatKernel1D s (x i - y i)
        ≤ P * Real.exp (-(x i - y i) ^ 2 / (6 * t)) := by
      intro i
      rw [heatKernel1D_apply]
      apply mul_le_mul hpref (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hPpos.le
      rw [neg_div, neg_div, neg_le_neg_iff]
      gcongr
    have hK : heatKernelND s (x - y) ≤
        P ^ n * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)) := by
      rw [heatKernelND_apply]
      have hp : (∏ i : Fin n, P * Real.exp (-(x i - y i) ^ 2 / (6 * t)))
          = P ^ n * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← hp]
      apply Finset.prod_le_prod
      · intro i _
        exact heatKernel1D_nonneg hspos ((x - y) i)
      · intro i _
        simpa only [Pi.sub_apply] using hcoordK i
    have hcoeff : |∑ i : Fin n, ((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))|
        ≤ ∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t) := by
      calc |∑ i : Fin n, ((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))|
          ≤ ∑ i : Fin n, |((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t) := by
          exact Finset.sum_le_sum (fun i _ => by
          have hA : 0 ≤ (x - y) i ^ 2 / (4 * s ^ 2) := by positivity
          have hB : 0 ≤ 1 / (2 * s) := by positivity
          have habs : |(x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s)|
              ≤ (x - y) i ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
            rw [abs_le]
            exact ⟨by linarith, by linarith⟩
          have hsq : (x - y) i ^ 2 / (4 * s ^ 2) ≤ (x i - y i) ^ 2 / t ^ 2 := by
            simp only [Pi.sub_apply]
            gcongr
            nlinarith [hslo, ht]
          have hinv : 1 / (2 * s) ≤ 1 / t := by
            gcongr
            linarith
          linarith)
    have hsum0 : 0 ≤ ∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hgauss0 : 0 ≤ ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)) :=
      Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le)
    have hfa : |f y| ≤ C := (Real.norm_eq_abs (f y) ▸ hfb y)
    have hnorm : ‖F' s y‖ = heatKernelND s (x - y)
        * |∑ i : Fin n, ((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| * |f y| := by
      simp only [hF']
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernelND_nonneg hspos _)]
    rw [hnorm]
    calc heatKernelND s (x - y)
          * |∑ i : Fin n, ((x - y) i ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| * |f y|
        ≤ (P ^ n * ∏ j : Fin n, Real.exp (-(x j - y j) ^ 2 / (6 * t)))
            * (∑ i : Fin n, ((x i - y i) ^ 2 / t ^ 2 + 1 / t)) * C := by
          gcongr
      _ = bound y := by simp only [hbound, hM]; ring
  have hderiv : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      ∀ s ∈ Metric.ball t (t / 2), HasDerivAt (fun r => F r y) (F' s y) s := by
    filter_upwards with y s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hspos : 0 < s := by
      have := (abs_lt.1 hs).1
      linarith
    simpa only [hF, hF'] using (hasDerivAt_heatKernelND_time n s hspos (x - y)).mul_const (f y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Fin n → ℝ))) (F := F) (x₀ := t) (bound := bound)
    (s := Metric.ball t (t / 2)) hsNhd hFmeas hFint hF'meas hbnd hboundint hderiv
  simpa only [hF, hF', heatSemigroupND] using key.2

/-- The classical `n`-dimensional heat semigroup solves the heat equation:
its actual time derivative is the sum of its actual second coordinate
derivatives. -/
theorem heatSemigroupND_solves_heatEquation_classical {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    deriv (fun s => heatSemigroupND s f x) t
      = ∑ k : Fin n,
        deriv (deriv (fun r => heatSemigroupND t f (Function.update x k r))) (x k) := by
  rw [(hasDerivAt_heatSemigroupND_time ht x hfm hfb).deriv]
  have hdist : (∫ y : Fin n → ℝ, heatKernelND t (x - y)
        * (∑ i : Fin n, ((x - y) i ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y)
      = ∑ k : Fin n, ∫ y : Fin n → ℝ,
          heatKernelND t (x - y)
            * ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * f y := by
    rw [← integral_finsetSum Finset.univ
      (fun k _ => integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x hfm hfb)]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hdist]
  apply Finset.sum_congr rfl
  intro k _
  exact (deriv2_heatSemigroupND_coord_eq_integral ht x k hfm hfb).symm

/-! ## Symmetric two-tensor components in a parallel Euclidean frame -/

/-- Componentwise heat evolution of a finite matrix field on Euclidean space. -/
def matrixHeatSemigroupND (n d : ℕ) (t : ℝ)
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => heatSemigroupND t (fun y => f y i j) x

/-- The componentwise Euclidean Laplacian of the constructed matrix heat
evolution, expressed through actual iterated coordinate derivatives. -/
def matrixHeatLaplacianND (n d : ℕ) (t : ℝ)
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ k : Fin n,
    deriv (deriv (fun r =>
      matrixHeatSemigroupND n d t f (Function.update x k r) i j)) (x k)

/-- The total evolution has the prescribed initial value at `t = 0` and uses
the heat-kernel construction at positive times. -/
def matrixHeatEvolutionND (n d : ℕ)
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  if t = 0 then f x else matrixHeatSemigroupND n d t f x

@[simp] theorem matrixHeatEvolutionND_zero (n d : ℕ)
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) :
    matrixHeatEvolutionND n d f 0 x = f x := by
  simp [matrixHeatEvolutionND]

theorem matrixHeatEvolutionND_eq_semigroup_of_pos {n d : ℕ} {t : ℝ} (ht : 0 < t)
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ) (x : Fin n → ℝ) :
    matrixHeatEvolutionND n d f t x = matrixHeatSemigroupND n d t f x := by
  simp [matrixHeatEvolutionND, ne_of_gt ht]

/-- Componentwise heat evolution preserves symmetry, so it really evolves
symmetric two-tensor coefficients rather than arbitrary matrices. -/
theorem matrixHeatSemigroupND_isSymm {n d : ℕ} {t : ℝ}
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (hf : ∀ x, (f x).IsSymm) (x : Fin n → ℝ) :
    (matrixHeatSemigroupND n d t f x).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [matrixHeatSemigroupND]
  apply integral_congr_ae
  filter_upwards with y
  rw [(hf y).apply i j]

/-- The total Euclidean tensor evolution preserves symmetry at every
nonnegative time, including the explicitly attached initial slice. -/
theorem matrixHeatEvolutionND_isSymm {n d : ℕ} {t : ℝ}
    (f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (hf : ∀ x, (f x).IsSymm) (x : Fin n → ℝ) :
    (matrixHeatEvolutionND n d f t x).IsSymm := by
  by_cases hzero : t = 0
  · simp [hzero, matrixHeatEvolutionND, hf x]
  · rw [matrixHeatEvolutionND, if_neg hzero]
    exact matrixHeatSemigroupND_isSymm f hf x

/-- The matrix-valued heat-kernel construction is an actual classical
solution of the componentwise tensor heat equation at every positive time. -/
theorem hasDerivAt_matrixHeatSemigroupND_time {n d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ} {C : ℝ} (x : Fin n → ℝ)
    (hfm : ∀ i j, AEStronglyMeasurable (fun y => f y i j))
    (hfb : ∀ y i j, ‖f y i j‖ ≤ C) :
    HasDerivAt (fun s => matrixHeatSemigroupND n d s f x)
      (matrixHeatLaplacianND n d t f x) t := by
  change HasDerivAt
    (fun s => fun i j => heatSemigroupND s (fun y => f y i j) x)
    (fun i j => ∑ k : Fin n,
      deriv (deriv (fun r => heatSemigroupND t (fun y => f y i j)
        (Function.update x k r))) (x k)) t
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have htime := hasDerivAt_heatSemigroupND_time ht x (hfm i j) (fun y => hfb y i j)
  exact htime.congr_deriv (htime.deriv.symm.trans
    (heatSemigroupND_solves_heatEquation_classical ht x (hfm i j) (fun y => hfb y i j)))

/-- Entrywise `C/t` second-derivative Schauder smoothing for the symmetric
matrix heat evolution. -/
theorem abs_deriv2_matrixHeatSemigroupND_coord_le {n d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ} {C : ℝ}
    (x : Fin n → ℝ) (k : Fin n) (i j : Fin d)
    (hfm : AEStronglyMeasurable (fun y => f y i j))
    (hfb : ∀ y, ‖f y i j‖ ≤ C) :
    |deriv (deriv (fun r => matrixHeatSemigroupND n d t f
        (Function.update x k r) i j)) (x k)| ≤ C / t := by
  simpa only [matrixHeatSemigroupND] using
    abs_deriv2_heatSemigroupND_coord_le ht x k hfm hfb

/-- Entrywise parabolic time-derivative bound for the constructed tensor heat
solution.  It follows from the heat equation and the sum of the coordinate
second-derivative bounds. -/
theorem abs_matrixHeatLaplacianND_apply_le {n d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℝ} {C : ℝ}
    (x : Fin n → ℝ) (i j : Fin d)
    (hfm : AEStronglyMeasurable (fun y => f y i j))
    (hfb : ∀ y, ‖f y i j‖ ≤ C) :
    |matrixHeatLaplacianND n d t f x i j| ≤ (n : ℝ) * C / t := by
  rw [matrixHeatLaplacianND]
  calc |∑ k : Fin n, deriv (deriv (fun r =>
          matrixHeatSemigroupND n d t f (Function.update x k r) i j)) (x k)|
      ≤ ∑ k : Fin n, |deriv (deriv (fun r =>
          matrixHeatSemigroupND n d t f (Function.update x k r) i j)) (x k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, C / t :=
      Finset.sum_le_sum (fun k _ =>
        abs_deriv2_matrixHeatSemigroupND_coord_le ht x k i j hfm hfb)
    _ = (n : ℝ) * C / t := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end AnalyticPDE
end RicciFlow
