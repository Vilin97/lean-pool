/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatEuclidean
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Fractional Gaussian moments and Schauder cancellation

This file begins the genuine Schauder upgrade of the Euclidean tensor heat
model.  Its two basic ingredients are:

* the exact `t^(r/2)` scaling of every integrable absolute Gaussian moment;
* the zero-mass identity for each coordinate Hessian of the heat kernel.

Together these turn convolution against a spatially `r`-Hölder datum into an
integrable `t^(-1+r/2)` Hessian bound, rather than the nonintegrable `t⁻¹`
bound available for merely bounded data.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The absolute `r`-moment of the time-one one-dimensional heat kernel. -/
def gaussianAbsMoment (r : ℝ) : ℝ :=
  ∫ x : ℝ, |x| ^ r * heatKernel1D 1 x

/-- Absolute Gaussian moments are integrable precisely on the range needed
below (`r > -1`). -/
lemma integrable_abs_rpow_mul_heatKernel1D_one {r : ℝ} (hr : -1 < r) :
    Integrable (fun x : ℝ => |x| ^ r * heatKernel1D 1 x) := by
  have hpos : IntegrableOn (fun x : ℝ => |x| ^ r * Real.exp (-(4 : ℝ)⁻¹ * x ^ 2))
      (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq (b := (4 : ℝ)⁻¹) (by norm_num) hr).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    simp only [abs_of_pos hx0]
  have hneg : IntegrableOn (fun x : ℝ => |x| ^ r * Real.exp (-(4 : ℝ)⁻¹ * x ^ 2))
      (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [neg_preimage, neg_Iio, neg_zero]
    change IntegrableOn
      (fun x : ℝ => |-x| ^ r * Real.exp (-(4 : ℝ)⁻¹ * (-x) ^ 2)) (Ioi 0)
    simpa only [abs_neg, neg_sq] using hpos
  have hgauss : Integrable (fun x : ℝ => |x| ^ r * Real.exp (-(4 : ℝ)⁻¹ * x ^ 2)) := by
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    have hpos' : IntegrableOn
        (fun x : ℝ => |x| ^ r * Real.exp (-(4 : ℝ)⁻¹ * x ^ 2)) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact hpos
    exact ⟨hneg, hpos'⟩
  have hscaled := hgauss.const_mul ((4 * π) ^ (-(1 : ℝ) / 2))
  refine hscaled.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [heatKernel1D_apply]
  have he : -(4 : ℝ)⁻¹ * x ^ 2 = -x ^ 2 / 4 := by ring
  rw [he]
  ring

lemma gaussianAbsMoment_nonneg (r : ℝ) : 0 ≤ gaussianAbsMoment r := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg x) r) (heatKernel1D_nonneg (by norm_num) x)

/-- Parabolic square-root scaling of the heat kernel. -/
lemma heatKernel1D_sqrt_scale {t z : ℝ} (ht : 0 < t) :
    heatKernel1D t (Real.sqrt t * z) = (Real.sqrt t)⁻¹ * heatKernel1D 1 z := by
  rw [heatKernel1D_apply, heatKernel1D_apply,
    prefactor_eq_inv_two_sqrt t ht, prefactor_eq_inv_two_sqrt 1 (by norm_num)]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hsqrtpi : Real.sqrt (π * t) = Real.sqrt π * Real.sqrt t := by
    rw [Real.sqrt_mul Real.pi_pos.le]
  rw [hsqrtpi]
  have hexp : -(Real.sqrt t * z) ^ 2 / (4 * t) = -z ^ 2 / 4 := by
    rw [mul_pow, hs2]
    field_simp
  rw [hexp]
  field_simp

/-- Exact scaling of an absolute Gaussian moment. -/
theorem integral_abs_rpow_mul_heatKernel1D_eq {t r : ℝ} (ht : 0 < t) (_hr : -1 < r) :
    (∫ x : ℝ, |x| ^ r * heatKernel1D t x)
      = (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hcv := Measure.integral_comp_mul_left
    (fun x : ℝ => |x| ^ r * heatKernel1D t x) (Real.sqrt t)
  rw [abs_of_pos (inv_pos.mpr hs)] at hcv
  have hscaled : (fun z : ℝ => |Real.sqrt t * z| ^ r * heatKernel1D t (Real.sqrt t * z))
      = fun z => (Real.sqrt t) ^ (r - 1) * (|z| ^ r * heatKernel1D 1 z) := by
    funext z
    rw [abs_mul, abs_of_pos hs, Real.mul_rpow hs.le (abs_nonneg z),
      heatKernel1D_sqrt_scale ht]
    have hp : (Real.sqrt t) ^ r * (Real.sqrt t) ^ (-1 : ℝ) =
        (Real.sqrt t) ^ (r - 1) := by
      rw [← Real.rpow_add hs]
      congr 1
    rw [← Real.rpow_neg_one, ← hp]
    ring
  rw [hscaled, integral_const_mul] at hcv
  rw [gaussianAbsMoment]
  have hmul := congrArg (fun z : ℝ => Real.sqrt t * z) hcv
  simp only [smul_eq_mul] at hmul
  simp only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hmul
  calc
    (∫ x : ℝ, |x| ^ r * heatKernel1D t x)
        = Real.sqrt t * ((Real.sqrt t) ^ (r - 1) *
            ∫ x : ℝ, |x| ^ r * heatKernel1D 1 x) := by
              simpa only [mul_assoc] using hmul.symm
    _ = (Real.sqrt t) ^ r * ∫ x : ℝ, |x| ^ r * heatKernel1D 1 x := by
      have hp : Real.sqrt t * (Real.sqrt t) ^ (r - 1) = (Real.sqrt t) ^ r := by
        calc
          Real.sqrt t * (Real.sqrt t) ^ (r - 1) =
              (Real.sqrt t) ^ (1 : ℝ) * (Real.sqrt t) ^ (r - 1) := by
                rw [Real.rpow_one]
          _ = (Real.sqrt t) ^ ((1 : ℝ) + (r - 1)) := (Real.rpow_add hs _ _).symm
          _ = (Real.sqrt t) ^ r := by congr 1 <;> ring
      rw [← mul_assoc, hp]

/-- Integrability of the absolute `r`-moment at every positive time. -/
lemma integrable_abs_rpow_mul_heatKernel1D {t r : ℝ} (ht : 0 < t) (hr : -1 < r) :
    Integrable (fun x : ℝ => |x| ^ r * heatKernel1D t x) := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have hpos : IntegrableOn
      (fun x : ℝ => |x| ^ r * Real.exp (-(4 * t)⁻¹ * x ^ 2)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq (b := (4 * t)⁻¹) hb hr).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    simp only [abs_of_pos hx0]
  have hneg : IntegrableOn
      (fun x : ℝ => |x| ^ r * Real.exp (-(4 * t)⁻¹ * x ^ 2)) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [neg_preimage, neg_Iio, neg_zero]
    change IntegrableOn
      (fun x : ℝ => |-x| ^ r * Real.exp (-(4 * t)⁻¹ * (-x) ^ 2)) (Ioi 0)
    simpa only [abs_neg, neg_sq] using hpos
  have hgauss : Integrable
      (fun x : ℝ => |x| ^ r * Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    have hpos' : IntegrableOn
        (fun x : ℝ => |x| ^ r * Real.exp (-(4 * t)⁻¹ * x ^ 2)) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact hpos
    exact ⟨hneg, hpos'⟩
  have hscaled := hgauss.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  refine hscaled.congr (Filter.Eventually.of_forall (fun x => ?_))
  change (4 * π * t) ^ (-(1 : ℝ) / 2) *
      (|x| ^ r * Real.exp (-(4 * t)⁻¹ * x ^ 2)) = |x| ^ r * heatKernel1D t x
  rw [heatKernel1D_apply]
  have he : -(4 * t)⁻¹ * x ^ 2 = -x ^ 2 / (4 * t) := by
    rw [neg_div, div_eq_inv_mul]
    ring
  rw [he]
  ring

private lemma abs_rpow_mul_sq {r x : ℝ} (hr : 0 ≤ r) :
    |x| ^ r * x ^ 2 = |x| ^ (r + 2) := by
  rw [← sq_abs]
  have hxpow : |x| ^ 2 = |x| ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  rw [hxpow]
  rw [← Real.rpow_add' (abs_nonneg x) (by linarith)]

/-- The fractional-moment majorant for a one-dimensional heat-kernel Hessian
is integrable. -/
lemma integrable_abs_rpow_secondDeriv_majorant {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    Integrable (fun x : ℝ =>
      |x| ^ r * heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) := by
  have h1 := (integrable_abs_rpow_mul_heatKernel1D ht
    (show -1 < r + 2 by linarith)).const_mul (1 / (4 * t ^ 2))
  have h2 := (integrable_abs_rpow_mul_heatKernel1D ht
    (show -1 < r by linarith)).const_mul (1 / (2 * t))
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
  change (1 / (4 * t ^ 2)) * (|x| ^ (r + 2) * heatKernel1D t x) +
      (1 / (2 * t)) * (|x| ^ r * heatKernel1D t x) =
      |x| ^ r * heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
  rw [← abs_rpow_mul_sq hr]
  ring

/-- Exact integral of the positive fractional Hessian majorant. -/
theorem integral_abs_rpow_secondDeriv_majorant_eq
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (∫ x : ℝ,
      |x| ^ r * heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) =
      (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
        + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r) := by
  have hpoint : (fun x : ℝ =>
      |x| ^ r * heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) =
      fun x => (1 / (4 * t ^ 2)) * (|x| ^ (r + 2) * heatKernel1D t x) +
        (1 / (2 * t)) * (|x| ^ r * heatKernel1D t x) := by
    funext x
    rw [← abs_rpow_mul_sq hr]
    ring
  rw [hpoint]
  rw [integral_add
    ((integrable_abs_rpow_mul_heatKernel1D ht
      (show -1 < r + 2 by linarith)).const_mul _)
    ((integrable_abs_rpow_mul_heatKernel1D ht
      (show -1 < r by linarith)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_abs_rpow_mul_heatKernel1D_eq ht (show -1 < r + 2 by linarith),
    integral_abs_rpow_mul_heatKernel1D_eq ht (show -1 < r by linarith)]

/-- **Fractional Hessian-moment estimate.**  The absolute coordinate Hessian
of the heat kernel, weighted by `|x|^r`, has the exact parabolic scale encoded
by the two moments on the right.  Each term is proportional to
`t^(-1+r/2)`; the unsimplified form avoids hiding any positivity condition in
power algebra and is the form used by the product-kernel argument. -/
theorem integral_abs_rpow_mul_abs_secondDeriv_heatKernel1D_le
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (∫ x : ℝ, |x| ^ r *
      |heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|)
      ≤ (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
        + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r) := by
  have hmaj := integrable_abs_rpow_secondDeriv_majorant ht hr
  have htarget : Integrable (fun x : ℝ => |x| ^ r *
      |heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|) := by
    have hrpow : Continuous (fun x : ℝ => |x| ^ r) :=
      continuous_abs.rpow_const (fun _ => Or.inr hr)
    have hinner : Continuous (fun x : ℝ =>
        heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) :=
      (continuous_heatKernel1D_space t).mul (by fun_prop)
    refine hmaj.mono' (hrpow.mul hinner.abs).aestronglyMeasurable ?_
    filter_upwards with x
    have hk := heatKernel1D_nonneg ht x
    have hp := Real.rpow_nonneg (abs_nonneg x) r
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (abs_nonneg _)), abs_mul,
      abs_of_nonneg hk]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (sq_sub_inv_le_add t ht x) hk) hp
  calc
    _ ≤ ∫ x : ℝ,
        |x| ^ r * heatKernel1D t x * (x ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by
      refine integral_mono htarget hmaj (fun x => ?_)
      have hk := heatKernel1D_nonneg ht x
      have hp := Real.rpow_nonneg (abs_nonneg x) r
      rw [abs_mul, abs_of_nonneg hk]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sq_sub_inv_le_add t ht x) hk) hp
    _ = _ := integral_abs_rpow_secondDeriv_majorant_eq ht hr

/-- Diagonal coordinate moment of the positive `n`-dimensional Hessian
majorant.  Product-Gaussian Fubini reduces it to the one-dimensional moment. -/
theorem integral_abs_coord_rpow_secondDeriv_majorantND_diag_eq
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (k : Fin n) :
    (∫ x : Fin n → ℝ, |x k| ^ r * heatKernelND t x *
      (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) =
      (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
        + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r) := by
  classical
  let F : Fin n → ℝ → ℝ := fun i z => if i = k then
    |z| ^ r * heatKernel1D t z * (z ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
    else heatKernel1D t z
  have hp : (fun x : Fin n → ℝ => |x k| ^ r * heatKernelND t x *
      (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) = fun x => ∏ i, F i (x i) := by
    funext x
    rw [heatKernelND_apply]
    rw [(
      Finset.mul_prod_erase Finset.univ (fun i => F i (x i)) (Finset.mem_univ k)).symm]
    simp only [F, if_pos]
    have heq : (∏ i ∈ Finset.univ.erase k, F i (x i)) =
        ∏ i ∈ Finset.univ.erase k, heatKernel1D t (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [F, if_neg (Finset.ne_of_mem_erase hi)]
    rw [heq]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => heatKernel1D t (x i))
      (Finset.mem_univ k)]
    ring
  rw [hp, integral_fin_nat_prod_volume_eq_prod]
  have hi : ∀ i, (∫ z : ℝ, F i z) = if i = k then
      (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
        + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r) else 1 := by
    intro i
    rcases eq_or_ne i k with rfl | hik
    · simp only [F, if_pos]
      exact integral_abs_rpow_secondDeriv_majorant_eq ht hr
    · simp only [F, if_neg hik, integral_heatKernel1D ht]
  rw [Finset.prod_congr rfl (fun i _ => hi i), Finset.prod_ite_eq']
  simp

/-- Transverse coordinate moment of the positive `n`-dimensional Hessian
majorant.  The weighted coordinate contributes its fractional Gaussian moment,
while the Hessian coordinate contributes total mass `1/t`. -/
theorem integral_abs_coord_rpow_secondDeriv_majorantND_offdiag_eq
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (j k : Fin n) (hjk : j ≠ k) :
    (∫ x : Fin n → ℝ, |x j| ^ r * heatKernelND t x *
      (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) =
      ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t) := by
  classical
  let F : Fin n → ℝ → ℝ := fun i z =>
    if i = j then |z| ^ r * heatKernel1D t z
    else if i = k then heatKernel1D t z * (z ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
    else heatKernel1D t z
  have hp : (fun x : Fin n → ℝ => |x j| ^ r * heatKernelND t x *
      (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) = fun x => ∏ i, F i (x i) := by
    funext x
    rw [heatKernelND_apply]
    have hfactor : (∏ i, F i (x i)) =
        |x j| ^ r * (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
          ∏ i, heatKernel1D t (x i) := by
      have hFi : ∀ i, F i (x i) =
          (if i = j then |x j| ^ r else 1) *
          (if i = k then (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) else 1) *
          heatKernel1D t (x i) := by
        intro i
        by_cases hij : i = j
        · subst i
          simp [F, hjk]
        · by_cases hik : i = k
          · subst i
            simp [F, hij]
            ring
          · simp [F, hij, hik]
      rw [Finset.prod_congr rfl (fun i _ => hFi i)]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_ite_eq', Finset.prod_ite_eq']
      simp
    rw [hfactor]
    ring
  rw [hp, integral_fin_nat_prod_volume_eq_prod]
  let A : ℝ := (Real.sqrt t) ^ r * gaussianAbsMoment r
  have hi : ∀ i, (∫ z : ℝ, F i z) =
      if i = j then A else if i = k then 1 / t else 1 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [F, if_pos, A]
      exact integral_abs_rpow_mul_heatKernel1D_eq ht (show -1 < r by linarith)
    · by_cases hik : i = k
      · subst i
        simp only [F, if_neg (Ne.symm hjk), if_pos]
        exact heatKernel1D_mul_sq_sub_inv_integral_eq ht
      · simp only [F, if_neg hij, if_neg hik, integral_heatKernel1D ht]
  rw [Finset.prod_congr rfl (fun i _ => hi i)]
  have hsplit : (∏ i : Fin n, if i = j then A else if i = k then 1 / t else 1) =
      (∏ i : Fin n, if i = j then A else 1) *
        (∏ i : Fin n, if i = k then 1 / t else 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs with hij hik <;> simp_all
  rw [hsplit, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [A]

/-- Integrability of every coordinate-weighted positive Hessian majorant. -/
lemma integrable_abs_coord_rpow_secondDeriv_majorantND
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (j k : Fin n) :
    Integrable (fun x : Fin n → ℝ => |x j| ^ r * heatKernelND t x *
      (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) := by
  classical
  rw [volume_pi]
  by_cases hjk : j = k
  · subst j
    let F : Fin n → ℝ → ℝ := fun i z => if i = k then
      |z| ^ r * heatKernel1D t z * (z ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
      else heatKernel1D t z
    have hp : (fun x : Fin n → ℝ => |x k| ^ r * heatKernelND t x *
        (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) = fun x => ∏ i, F i (x i) := by
      funext x
      rw [heatKernelND_apply]
      rw [(
        Finset.mul_prod_erase Finset.univ (fun i => F i (x i)) (Finset.mem_univ k)).symm]
      simp only [F, if_pos]
      have heq : (∏ i ∈ Finset.univ.erase k, F i (x i)) =
          ∏ i ∈ Finset.univ.erase k, heatKernel1D t (x i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [F, if_neg (Finset.ne_of_mem_erase hi)]
      rw [heq]
      rw [← Finset.mul_prod_erase Finset.univ (fun i => heatKernel1D t (x i))
        (Finset.mem_univ k)]
      ring
    rw [hp]
    refine Integrable.fin_nat_prod (f := F) (fun i => ?_)
    rcases eq_or_ne i k with rfl | hik
    · simpa only [F, if_pos] using integrable_abs_rpow_secondDeriv_majorant ht hr
    · simpa only [F, if_neg hik] using integrable_heatKernel1D ht
  · let F : Fin n → ℝ → ℝ := fun i z =>
      if i = j then |z| ^ r * heatKernel1D t z
      else if i = k then heatKernel1D t z * (z ^ 2 / (4 * t ^ 2) + 1 / (2 * t))
      else heatKernel1D t z
    have hp : (fun x : Fin n → ℝ => |x j| ^ r * heatKernelND t x *
        (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t))) = fun x => ∏ i, F i (x i) := by
      funext x
      rw [heatKernelND_apply]
      have hfactor : (∏ i, F i (x i)) =
          |x j| ^ r * (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
            ∏ i, heatKernel1D t (x i) := by
        have hFi : ∀ i, F i (x i) =
            (if i = j then |x j| ^ r else 1) *
            (if i = k then (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) else 1) *
            heatKernel1D t (x i) := by
          intro i
          by_cases hij : i = j
          · subst i
            simp [F, hjk]
          · by_cases hik : i = k
            · subst i
              simp [F, hij]
              ring
            · simp [F, hij, hik]
        rw [Finset.prod_congr rfl (fun i _ => hFi i)]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_ite_eq', Finset.prod_ite_eq']
        simp
      rw [hfactor]
      ring
    rw [hp]
    refine Integrable.fin_nat_prod (f := F) (fun i => ?_)
    by_cases hij : i = j
    · subst i
      simpa only [F, if_pos] using
        integrable_abs_rpow_mul_heatKernel1D ht (show -1 < r by linarith)
    · by_cases hik : i = k
      · subst i
        simpa [F, Ne.symm hjk] using
          integrable_abs_rpow_secondDeriv_majorant ht (show (0 : ℝ) ≤ 0 by norm_num)
      · simpa only [F, if_neg hij, if_neg hik] using integrable_heatKernel1D ht

/-- Integrability of the coordinate-weighted absolute Hessian kernel. -/
lemma integrable_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (j k : Fin n) :
    Integrable (fun x : Fin n → ℝ => |x j| ^ r *
      |heatKernelND t x * (x k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|) := by
  have hmaj := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr j k
  have hrpow : Continuous (fun x : Fin n → ℝ => |x j| ^ r) :=
    (continuous_abs.comp (continuous_apply j)).rpow_const (fun _ => Or.inr hr)
  have hinner : Continuous (fun x : Fin n → ℝ =>
      heatKernelND t x * (x k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) :=
    (continuous_heatKernelND t).mul (by fun_prop)
  refine hmaj.mono' (hrpow.mul hinner.abs).aestronglyMeasurable ?_
  filter_upwards with x
  have hk := heatKernelND_nonneg ht x
  have hp := Real.rpow_nonneg (abs_nonneg (x j)) r
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (abs_nonneg _)), abs_mul,
    abs_of_nonneg hk]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (sq_sub_inv_le_add t ht (x k)) hk) hp

/-- Coordinatewise fractional moment of the absolute `n`-dimensional Hessian
kernel.  The diagonal coordinate uses the `r+2` moment; every transverse
coordinate is its `r`-moment times the unweighted Hessian mass. -/
theorem integral_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND_le
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (j k : Fin n) :
    (∫ x : Fin n → ℝ, |x j| ^ r *
      |heatKernelND t x * (x k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|) ≤
      if j = k then
        (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
          + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r)
      else ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t) := by
  have hmaj := integrable_abs_coord_rpow_secondDeriv_majorantND ht hr j k
  have htarget := integrable_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND ht hr j k
  calc
    _ ≤ ∫ x : Fin n → ℝ, |x j| ^ r * heatKernelND t x *
        (x k ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by
      refine integral_mono htarget hmaj (fun x => ?_)
      have hk := heatKernelND_nonneg ht x
      have hp := Real.rpow_nonneg (abs_nonneg (x j)) r
      rw [abs_mul, abs_of_nonneg hk]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sq_sub_inv_le_add t ht (x k)) hk) hp
    _ ≤ _ := by
      by_cases hjk : j = k
      · subst j
        simp only [if_pos]
        exact le_of_eq (integral_abs_coord_rpow_secondDeriv_majorantND_diag_eq ht hr k)
      · simp only [if_neg hjk]
        exact le_of_eq
          (integral_abs_coord_rpow_secondDeriv_majorantND_offdiag_eq ht hr j k hjk)

/-- A coordinate Hessian of the Euclidean heat kernel has zero total mass.
This is the cancellation identity used to replace `f(y)` by `f(y) - f(x)`
inside the Hessian convolution. -/
theorem integral_secondDeriv_coord_heatKernelND_eq_zero
    {n : ℕ} {t : ℝ} (ht : 0 < t) (k : Fin n) :
    (∫ x : Fin n → ℝ,
      heatKernelND t x * ((x k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) = 0 := by
  have hint := integral_sub
    ((integrable_sq_coord_mul_heatKernelND ht k).const_mul (1 / (4 * t ^ 2)))
    ((integrable_heatKernelND ht).const_mul (1 / (2 * t)))
  have hrewrite : (∫ x : Fin n → ℝ,
      heatKernelND t x * ((x k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) =
      (∫ x : Fin n → ℝ,
        (1 / (4 * t ^ 2)) * ((x k) ^ 2 * heatKernelND t x)
          - (1 / (2 * t)) * heatKernelND t x) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hrewrite, hint, integral_const_mul, integral_const_mul,
    integral_sq_coord_mul_heatKernelND_eq ht k, integral_heatKernelND ht]
  field_simp
  ring

/-- Translation invariance of Hessian-kernel cancellation. -/
theorem integral_secondDeriv_coord_heatKernelND_sub_eq_zero
    {n : ℕ} {t : ℝ} (ht : 0 < t) (k : Fin n) (x : Fin n → ℝ) :
    (∫ y : Fin n → ℝ,
      heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) = 0 := by
  rw [integral_sub_left_eq_self
    (fun w : Fin n → ℝ =>
      heatKernelND t w * ((w k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) volume x]
  exact integral_secondDeriv_coord_heatKernelND_eq_zero ht k

/-- Cancellation rewrites the Hessian convolution against `f` as convolution
against the increment `f(y) - f(x)`.  Boundedness is used only to justify both
Bochner integrals; the equality itself is the zero-mass identity above. -/
theorem secondDeriv_heatKernelND_convolution_eq_increment
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C) :
    (∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y) =
    ∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) *
        (f y - f x) := by
  let K : (Fin n → ℝ) → ℝ := fun y =>
    heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))
  have hK : Integrable K := (integrable_secondDeriv_coord_heatKernelND ht k).comp_sub_left x
  have hKf : Integrable (fun y => K y * f y) := by
    simpa only [K] using integrable_secondDeriv_coord_heatKernelND_sub_mul ht k x hfm hfb
  have hKc : Integrable (fun y => K y * f x) := hK.mul_const (f x)
  have hpoint : (fun y => K y * (f y - f x)) = fun y => K y * f y - K y * f x := by
    funext y
    ring
  change (∫ y, K y * f y) = ∫ y, K y * (f y - f x)
  rw [hpoint, integral_sub hKf hKc]
  have hc : (∫ y, K y * f x) = f x * ∫ y, K y := by
    calc
      _ = ∫ y, f x * K y := by congr 1; funext y; ring
      _ = _ := by rw [integral_const_mul]
  rw [hc]
  have hzero : (∫ y, K y) = 0 := by
    simpa only [K] using integral_secondDeriv_coord_heatKernelND_sub_eq_zero ht k x
  rw [hzero]
  ring

/-- **Euclidean spatial Schauder gain, Hessian kernel form.**  If the increment
of `f` at `x` is bounded by a sum of coordinate `r`-Hölder increments, then
its coordinate heat-kernel Hessian is bounded by the corresponding finite sum
of explicit Gaussian moments.  Each summand has scale `t^(-1+r/2)`, so it is
integrable in Duhamel time exactly when `r > 0`.

This theorem is the quantitative cancellation step absent from the older
`C/t` smoothing estimate: boundedness justifies the original convolution,
while Hölder regularity removes its nonintegrable singularity. -/
theorem abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    {f : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ y, |f y - f x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r) :
    |∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y| ≤
      H * ∑ j : Fin n, if j = k then
        (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
          + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r)
      else ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t) := by
  classical
  let K : (Fin n → ℝ) → ℝ := fun y =>
    heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))
  let W : Fin n → (Fin n → ℝ) → ℝ := fun j y =>
    |(x - y) j| ^ r * |K y|
  have hWi : ∀ j, Integrable (W j) := by
    intro j
    have h :=
      (integrable_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND ht hr j k).comp_sub_left x
    simpa only [W, K] using h
  have hsum : Integrable (fun y => ∑ j : Fin n, W j y) := by
    exact integrable_finset_sum Finset.univ (fun j _ => hWi j)
  have hdom : Integrable (fun y => H * ∑ j : Fin n, W j y) := hsum.const_mul H
  have hcancel := secondDeriv_heatKernelND_convolution_eq_increment ht x k hfm hfb
  rw [hcancel]
  change |∫ y, K y * (f y - f x)| ≤ _
  calc
    _ ≤ ∫ y, H * ∑ j : Fin n, W j y := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall (fun y => ?_))
      have hh := hholder y
      rw [Real.norm_eq_abs, abs_mul]
      have hKnn : 0 ≤ |K y| := abs_nonneg _
      calc
        |K y| * |f y - f x| ≤ |K y| * (H * ∑ j : Fin n, |(x - y) j| ^ r) :=
          mul_le_mul_of_nonneg_left hh hKnn
        _ = H * ∑ j : Fin n, W j y := by
          simp only [W]
          calc
            |K y| * (H * ∑ j : Fin n, |(x - y) j| ^ r) =
                ∑ j : Fin n, |K y| * (H * |(x - y) j| ^ r) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
            _ = ∑ j : Fin n, H * (|(x - y) j| ^ r * |K y|) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = H * ∑ j : Fin n, |(x - y) j| ^ r * |K y| := by
              rw [Finset.mul_sum]
    _ = H * ∫ y, ∑ j : Fin n, W j y := by rw [integral_const_mul]
    _ = H * ∑ j : Fin n, ∫ y, W j y := by
      rw [integral_finset_sum Finset.univ (fun j _ => hWi j)]
    _ ≤ H * ∑ j : Fin n, if j = k then
        (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
          + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r)
      else ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t) := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply Finset.sum_le_sum
      intro j _
      have htrans : (∫ y, W j y) = ∫ w : Fin n → ℝ,
          |w j| ^ r * |heatKernelND t w * (w k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))| := by
        rw [integral_sub_left_eq_self
          (fun w : Fin n → ℝ => |w j| ^ r *
            |heatKernelND t w * (w k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))|) volume x]
      rw [htrans]
      exact integral_abs_coord_rpow_mul_abs_secondDeriv_heatKernelND_le ht hr j k

/-- The diagonal fractional Hessian moment has the parabolic homogeneity
`t^(-1+r/2)`. -/
theorem diagonal_hessianMoment_scale {t r : ℝ} (ht : 0 < t) :
    (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
        + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r) =
    t ^ (-1 + r / 2) * (gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2) := by
  have hs1 : (Real.sqrt t) ^ (r + 2) = t ^ ((r + 2) / 2) := by
    exact (Real.rpow_div_two_eq_sqrt (r + 2) ht.le).symm
  have hs0 : (Real.sqrt t) ^ r = t ^ (r / 2) := by
    exact (Real.rpow_div_two_eq_sqrt r ht.le).symm
  have hp2 : t ^ (2 : ℝ) = t ^ 2 := by norm_num [Real.rpow_two]
  have hd2 : t ^ ((r + 2) / 2) / t ^ (2 : ℝ) = t ^ (-1 + r / 2) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  have hd1 : t ^ (r / 2) / t = t ^ (-1 + r / 2) := by
    calc
      t ^ (r / 2) / t = t ^ (r / 2) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ (r / 2 - 1) := (Real.rpow_sub ht _ _).symm
      _ = t ^ (-1 + r / 2) := by congr 1 <;> ring
  rw [hs1, hs0, ← hp2]
  rw [show 1 / (4 * t ^ (2 : ℝ)) * (t ^ ((r + 2) / 2) * gaussianAbsMoment (r + 2)) =
      (t ^ ((r + 2) / 2) / t ^ (2 : ℝ)) * (gaussianAbsMoment (r + 2) / 4) by ring,
    show 1 / (2 * t) * (t ^ (r / 2) * gaussianAbsMoment r) =
      (t ^ (r / 2) / t) * (gaussianAbsMoment r / 2) by ring,
    hd2, hd1]
  ring

/-- A transverse fractional Hessian moment has the same parabolic homogeneity
`t^(-1+r/2)`. -/
theorem offdiagonal_hessianMoment_scale {t r : ℝ} (ht : 0 < t) :
    ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t) =
      t ^ (-1 + r / 2) * gaussianAbsMoment r := by
  rw [← Real.rpow_div_two_eq_sqrt r ht.le]
  have hd1 : t ^ (r / 2) / t = t ^ (-1 + r / 2) := by
    calc
      t ^ (r / 2) / t = t ^ (r / 2) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ (r / 2 - 1) := (Real.rpow_sub ht _ _).symm
      _ = t ^ (-1 + r / 2) := by congr 1 <;> ring
  rw [show (t ^ (r / 2) * gaussianAbsMoment r) * (1 / t) =
      (t ^ (r / 2) / t) * gaussianAbsMoment r by ring, hd1]

/-- The dimension-dependent, time-independent Gaussian moment sum appearing
in one coordinate Hessian estimate. -/
def heatHessianHolderMoment (n : ℕ) (r : ℝ) (k : Fin n) : ℝ :=
  ∑ j : Fin n, if j = k then
    gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
  else gaussianAbsMoment r

lemma heatHessianHolderMoment_nonneg (n : ℕ) (r : ℝ) (k : Fin n) :
    0 ≤ heatHessianHolderMoment n r k := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact add_nonneg (div_nonneg (gaussianAbsMoment_nonneg _) (by norm_num))
      (div_nonneg (gaussianAbsMoment_nonneg _) (by norm_num))
  · exact gaussianAbsMoment_nonneg _

/-- Homogeneous form of the Euclidean coordinate-Hessian Schauder estimate.
The singular factor is exactly `t^(-1+r/2)`, separated from a nonnegative,
time-independent Gaussian moment constant. -/
theorem abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    {f : (Fin n → ℝ) → ℝ} {C H : ℝ} (hH : 0 ≤ H)
    (x : Fin n → ℝ) (k : Fin n)
    (hfm : AEStronglyMeasurable f) (hfb : ∀ y, ‖f y‖ ≤ C)
    (hholder : ∀ y, |f y - f x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r) :
    |∫ y : Fin n → ℝ,
      (heatKernelND t (x - y) * (((x - y) k) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y| ≤
      H * t ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
  have h := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder
    ht hr hH x k hfm hfb hholder
  refine h.trans_eq ?_
  rw [heatHessianHolderMoment]
  have hsum : (∑ j : Fin n, if j = k then
        (1 / (4 * t ^ 2)) * ((Real.sqrt t) ^ (r + 2) * gaussianAbsMoment (r + 2))
          + (1 / (2 * t)) * ((Real.sqrt t) ^ r * gaussianAbsMoment r)
      else ((Real.sqrt t) ^ r * gaussianAbsMoment r) * (1 / t)) =
      t ^ (-1 + r / 2) * ∑ j : Fin n, if j = k then
        gaussianAbsMoment (r + 2) / 4 + gaussianAbsMoment r / 2
      else gaussianAbsMoment r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjk : j = k
    · simp only [if_pos hjk]
      exact diagonal_hessianMoment_scale ht
    · simp only [if_neg hjk]
      exact offdiagonal_hessianMoment_scale ht
  rw [hsum]
  ring

/-- **Time-integrated Euclidean Schauder Hessian bound.**  A uniformly
spatially `r`-Hölder forcing has an integrable Duhamel Hessian singularity:

`|∫ₜ₀ᵗ D²H_(t-s) q(s) ds| ≤ H · M(n,r,k) · (t-t₀)^(r/2)/(r/2)`.

The strict condition `r > 0` is exactly what makes
`(t-s)^(-1+r/2)` integrable at `s=t`.  The `IntervalIntegrable` input records
that the parameterized kernel convolution is a genuine Bochner integrand; it
will be discharged by the Duhamel differentiation construction. -/
theorem abs_intervalIntegral_secondDeriv_heatKernelND_convolution_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    (q : ℝ → (Fin n → ℝ) → ℝ) {C H : ℝ} (hH : 0 ≤ H)
    (hqm : ∀ s, AEStronglyMeasurable (q s)) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n)
    (_hGint : IntervalIntegrable (fun s =>
      ∫ y : Fin n → ℝ, (heatKernelND (t - s) (x - y) *
        (((x - y) k) ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y)
      volume t₀ t) :
    |∫ s in t₀..t, ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (x - y) *
        (((x - y) k) ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y| ≤
      H * heatHessianHolderMoment n r k * ((t - t₀) ^ (r / 2) / (r / 2)) := by
  let G : ℝ → ℝ := fun s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (x - y) *
      (((x - y) k) ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y
  let A : ℝ := H * heatHessianHolderMoment n r k
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  have hA : 0 ≤ A := mul_nonneg hH (heatHessianHolderMoment_nonneg n r k)
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc t₀ t → ‖G s‖ ≤ g s := by
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      rw [ae_iff, hset]
      exact measure_singleton t
    filter_upwards [htne] with s hs hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    rw [Real.norm_eq_abs]
    have h := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
      hst hr0.le hH x k (hqm s) (hqb s) (hqholder s x)
    change |G s| ≤ g s
    calc
      |G s| ≤ H * (t - s) ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
        simpa only [G] using h
      _ = g s := by simp only [g, A]; ring
  have hgint : IntervalIntegrable g volume t₀ t := by
    have hrexp : (-1 : ℝ) < -1 + r / 2 := by linarith
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' hrexp
    have hcomp := hbase.comp_sub_left t
    have hweight : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2)) volume t₀ t := by
      simpa using hcomp.symm
    exact hweight.const_mul A
  change |∫ s in t₀..t, G s| ≤ _
  have hmain := intervalIntegral.norm_integral_le_of_norm_le hT hae hgint
  rw [Real.norm_eq_abs] at hmain
  have hgval : (∫ s in t₀..t, g s) =
      A * ((t - t₀) ^ (r / 2) / (r / 2)) := by
    simp only [g]
    rw [intervalIntegral.integral_const_mul, integral_rpow_sub t₀ t
      (show (-1 : ℝ) < -1 + r / 2 by linarith)]
    congr 2 <;> ring
  rw [hgval] at hmain
  simpa only [A, mul_assoc] using hmain

/-! ## Actual differentiation of the Duhamel term -/

/-- Time measurability of a coordinate-gradient heat convolution for a
continuous bounded-function-valued source.  This is the Fubini measurability
input for differentiating a Duhamel integral in space. -/
lemma aestronglyMeasurable_gradient_heatKernelND_convolution_time
    {n : ℕ} {t : ℝ}
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (x : Fin n → ℝ) (k : Fin n) :
    AEStronglyMeasurable (fun s => ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y) := by
  have hK : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatKernelND (t - p.1) (x - p.2)) := by
    have hmap : Measurable (fun p : ℝ × (Fin n → ℝ) => (t - p.1, x - p.2)) :=
      (measurable_const.sub measurable_fst).prodMk (measurable_const.sub measurable_snd)
    have hkernel := (measurable_uncurry_heatKernelND (n := n)).comp hmap
    exact hkernel
  have hc : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (-(x - p.2) k / (2 * (t - p.1)))) := by
    have hcoord : Measurable (fun p : ℝ × (Fin n → ℝ) => (x - p.2) k) :=
      measurable_const.sub ((measurable_pi_apply k).comp measurable_snd)
    exact hcoord.neg.div (measurable_const.mul (measurable_const.sub measurable_fst))
  have hQ : Measurable (fun p : ℝ × (Fin n → ℝ) => q p.1 p.2) := by
    have heval : Continuous (fun p : ℝ × (Fin n → ℝ) => q p.1 p.2) :=
      (hq.comp continuous_fst).eval continuous_snd
    exact heval.measurable
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (heatKernelND (t - p.1) (x - p.2) * (-(x - p.2) k / (2 * (t - p.1)))) * q p.1 p.2) :=
    (hK.mul hc).mul hQ
  exact (hG.aestronglyMeasurable
    (μ := (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- Time measurability of a coordinate-Hessian heat convolution for a
continuous bounded-function-valued source. -/
lemma aestronglyMeasurable_hessian_heatKernelND_convolution_time
    {n : ℕ} {t : ℝ}
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (x : Fin n → ℝ) (k : Fin n) :
    AEStronglyMeasurable (fun s => ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (x - y) *
        ((x - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y) := by
  have hK : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatKernelND (t - p.1) (x - p.2)) := by
    have hmap : Measurable (fun p : ℝ × (Fin n → ℝ) => (t - p.1, x - p.2)) :=
      (measurable_const.sub measurable_fst).prodMk (measurable_const.sub measurable_snd)
    have hkernel := (measurable_uncurry_heatKernelND (n := n)).comp hmap
    exact hkernel
  have hc : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      ((x - p.2) k ^ 2 / (4 * (t - p.1) ^ 2) - 1 / (2 * (t - p.1)))) := by
    have hcoord : Measurable (fun p : ℝ × (Fin n → ℝ) => (x - p.2) k) :=
      measurable_const.sub ((measurable_pi_apply k).comp measurable_snd)
    have htime : Measurable (fun p : ℝ × (Fin n → ℝ) => t - p.1) :=
      measurable_const.sub measurable_fst
    exact ((hcoord.pow_const 2).div (measurable_const.mul (htime.pow_const 2))).sub
      (measurable_const.div (measurable_const.mul htime))
  have hQ : Measurable (fun p : ℝ × (Fin n → ℝ) => q p.1 p.2) := by
    have heval : Continuous (fun p : ℝ × (Fin n → ℝ) => q p.1 p.2) :=
      (hq.comp continuous_fst).eval continuous_snd
    exact heval.measurable
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (heatKernelND (t - p.1) (x - p.2) *
        ((x - p.2) k ^ 2 / (4 * (t - p.1) ^ 2) - 1 / (2 * (t - p.1)))) * q p.1 p.2) :=
    (hK.mul hc).mul hQ
  exact (hG.aestronglyMeasurable
    (μ := (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- The coordinate-gradient convolution is interval-integrable up to the
Duhamel endpoint.  Its `C / sqrt(π(t-s))` singularity is integrable. -/
lemma intervalIntegrable_gradient_heatKernelND_convolution
    {n : ℕ} {t₀ t : ℝ} (hT : t₀ ≤ t)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C : ℝ} (hqb : ∀ s y, ‖q s y‖ ≤ C) (x : Fin n → ℝ) (k : Fin n) :
    IntervalIntegrable (fun s => ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y)
      volume t₀ t := by
  let G : ℝ → ℝ := fun s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y
  let g : ℝ → ℝ := fun s =>
    (C / Real.sqrt π) * (t - s) ^ (-(1 / 2) : ℝ)
  have hGm : AEStronglyMeasurable G := by
    simpa only [G] using aestronglyMeasurable_gradient_heatKernelND_convolution_time hq x k
  have hgint : IntervalIntegrable g volume t₀ t := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-(1 / 2) : ℝ)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2) : ℝ)) volume t₀ t := by
      simpa using hcomp.symm
    simp only [g]
    exact hw.const_mul _
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr ?_
  have hgOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hgint
  refine hgOn.mono' hGm.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
  have htne : ∀ᵐ s : ℝ, s ≠ t := by rw [ae_iff, hset]; exact measure_singleton t
  filter_upwards [htne] with s hs hmem
  have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
  rw [Real.norm_eq_abs]
  have hb := heatSemigroupND_coord_deriv_integral_bound hst x k
    (q s).continuous.aestronglyMeasurable (hqb s)
  refine hb.trans_eq ?_
  simp only [g]
  rw [Real.sqrt_mul Real.pi_pos.le, Real.rpow_neg hst.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- The coordinate-Hessian convolution is interval-integrable for every
strictly positive Hölder exponent.  Cancellation improves the endpoint
singularity from `(t-s)⁻¹` to `(t-s)^(-1+r/2)`. -/
lemma intervalIntegrable_hessian_heatKernelND_convolution
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n) :
    IntervalIntegrable (fun s => ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (x - y) *
        ((x - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y)
      volume t₀ t := by
  let G : ℝ → ℝ := fun s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (x - y) *
      ((x - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y
  let A : ℝ := H * heatHessianHolderMoment n r k
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  have hGm : AEStronglyMeasurable G := by
    simpa only [G] using aestronglyMeasurable_hessian_heatKernelND_convolution_time hq x k
  have hgint : IntervalIntegrable g volume t₀ t := by
    have hrexp : (-1 : ℝ) < -1 + r / 2 := by linarith
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' hrexp
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2)) volume t₀ t := by
      simpa using hcomp.symm
    exact hw.const_mul A
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr ?_
  have hgOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hgint
  refine hgOn.mono' hGm.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
  have htne : ∀ᵐ s : ℝ, s ≠ t := by rw [ae_iff, hset]; exact measure_singleton t
  filter_upwards [htne] with s hs hmem
  have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
  rw [Real.norm_eq_abs]
  have hb := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
    hst hr0.le hH x k (q s).continuous.aestronglyMeasurable (hqb s) (hqholder s x)
  change |G s| ≤ g s
  calc
    |G s| ≤ H * (t - s) ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
      simpa only [G] using hb
    _ = g s := by simp only [g, A]; ring

/-- A Duhamel integral with a continuous bounded source is differentiable in
each coordinate.  Its derivative is the time integral of the corresponding
coordinate-gradient heat-kernel convolution. -/
theorem hasDerivAt_heatDuhamelND_coord
    {n : ℕ} {t₀ t : ℝ} (hT : t₀ ≤ t)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C : ℝ} (hqb : ∀ s y, ‖q s y‖ ≤ C) (x : Fin n → ℝ) (k : Fin n) :
    HasDerivAt (fun a => ∫ s in t₀..t,
      heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a))
      (∫ s in t₀..t, ∫ y : Fin n → ℝ,
        (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y)
      (x k) := by
  let F : ℝ → ℝ → ℝ := fun a s =>
    heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a)
  let F' : ℝ → ℝ → ℝ := fun a s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x k a - y) *
      (-(Function.update x k a - y) k / (2 * (t - s)))) * q s y
  let bound : ℝ → ℝ := fun s =>
    (C / Real.sqrt π) * (t - s) ^ (-(1 / 2) : ℝ)
  have hFmeas : ∀ᶠ a in 𝓝 (x k),
      AEStronglyMeasurable (F a) ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    filter_upwards with a
    exact (intervalIntegrable_heatSemigroupND_duhamel hT hq hqb
      (Function.update x k a)).def'.aestronglyMeasurable
  have hFint : IntervalIntegrable (F (x k)) volume t₀ t := by
    simpa only [F, Function.update_eq_self] using
      intervalIntegrable_heatSemigroupND_duhamel hT hq hqb x
  have hF'meas : AEStronglyMeasurable (F' (x k)) ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    have hm := aestronglyMeasurable_gradient_heatKernelND_convolution_time (t := t) hq x k
    simpa only [F', Function.update_eq_self] using
      (hm.restrict : AEStronglyMeasurable _ ((volume : Measure ℝ).restrict (Ι t₀ t)))
  have hbint : IntervalIntegrable bound volume t₀ t := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-(1 / 2) : ℝ)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2) : ℝ)) volume t₀ t := by
      simpa using hcomp.symm
    exact hw.const_mul _
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hset]
    exact measure_singleton t
  have hbnd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), ‖F' a s‖ ≤ bound s := by
    filter_upwards [htne] with s hs hmem a _
    rw [uIoc_of_le hT] at hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    rw [Real.norm_eq_abs]
    have hb := heatSemigroupND_coord_deriv_integral_bound hst (Function.update x k a) k
      (q s).continuous.aestronglyMeasurable (hqb s)
    refine hb.trans_eq ?_
    simp only [bound]
    rw [Real.sqrt_mul Real.pi_pos.le, Real.rpow_neg hst.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hdiff : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), HasDerivAt (fun a => F a s) (F' a s) a := by
    filter_upwards [htne] with s hs hmem a _
    rw [uIoc_of_le hT] at hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    simpa only [F, F'] using hasDerivAt_heatSemigroupND_coord_update hst x k
      (q s).continuous.aestronglyMeasurable (hqb s) a
  have hout := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := t₀) (b := t) (F := F) (F' := F') (x₀ := x k)
    (s := Set.univ) Filter.univ_mem hFmeas hFint hF'meas hbnd hbint hdiff
  simpa only [F, F', Function.update_eq_self] using hout.2

/-- Under a uniform spatial Hölder bound, the time integral of the
coordinate-gradient convolution is differentiable once more in that
coordinate.  Its derivative is the coordinate-Hessian convolution. -/
theorem hasDerivAt_heatDuhamelND_coordGradient
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n) :
    HasDerivAt (fun a => ∫ s in t₀..t, ∫ y : Fin n → ℝ,
      (heatKernelND (t - s) (Function.update x k a - y) *
        (-(Function.update x k a - y) k / (2 * (t - s)))) * q s y)
      (∫ s in t₀..t, ∫ y : Fin n → ℝ,
        (heatKernelND (t - s) (x - y) *
          ((x - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y)
      (x k) := by
  let F : ℝ → ℝ → ℝ := fun a s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x k a - y) *
      (-(Function.update x k a - y) k / (2 * (t - s)))) * q s y
  let F' : ℝ → ℝ → ℝ := fun a s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x k a - y) *
      ((Function.update x k a - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y
  let A : ℝ := H * heatHessianHolderMoment n r k
  let bound : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  have hFmeas : ∀ᶠ a in 𝓝 (x k),
      AEStronglyMeasurable (F a) ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    filter_upwards with a
    have hm := aestronglyMeasurable_gradient_heatKernelND_convolution_time
      (t := t) hq (Function.update x k a) k
    exact (by simpa only [F] using
      (hm.restrict : AEStronglyMeasurable _ ((volume : Measure ℝ).restrict (Ι t₀ t))))
  have hFint : IntervalIntegrable (F (x k)) volume t₀ t := by
    simpa only [F, Function.update_eq_self] using
      intervalIntegrable_gradient_heatKernelND_convolution hT hq hqb x k
  have hF'meas : AEStronglyMeasurable (F' (x k)) ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    have hm := aestronglyMeasurable_hessian_heatKernelND_convolution_time (t := t) hq x k
    simpa only [F', Function.update_eq_self] using
      (hm.restrict : AEStronglyMeasurable _ ((volume : Measure ℝ).restrict (Ι t₀ t)))
  have hbint : IntervalIntegrable bound volume t₀ t := by
    have hrexp : (-1 : ℝ) < -1 + r / 2 := by linarith
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2)) volume 0 (t - t₀) :=
      intervalIntegral.intervalIntegrable_rpow' hrexp
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2)) volume t₀ t := by
      simpa using hcomp.symm
    exact hw.const_mul A
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hset]
    exact measure_singleton t
  have hbnd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), ‖F' a s‖ ≤ bound s := by
    filter_upwards [htne] with s hs hmem a _
    rw [uIoc_of_le hT] at hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    rw [Real.norm_eq_abs]
    have hb := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
      hst hr0.le hH (Function.update x k a) k (q s).continuous.aestronglyMeasurable
      (hqb s) (hqholder s (Function.update x k a))
    change |F' a s| ≤ bound s
    calc
      |F' a s| ≤ H * (t - s) ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
        simpa only [F'] using hb
      _ = bound s := by simp only [bound, A]; ring
  have hdiff : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), HasDerivAt (fun a => F a s) (F' a s) a := by
    filter_upwards [htne] with s hs hmem a _
    rw [uIoc_of_le hT] at hmem
    have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hmem.2 hs)
    have hd := hasDerivAt_heatSemigroupND_coordGradient hst (Function.update x k a) k
      (q s).continuous.aestronglyMeasurable (hqb s)
    have hupd : ∀ b : ℝ, Function.update (Function.update x k a) k b =
        Function.update x k b := by
      intro b
      funext j
      rcases eq_or_ne j k with hjk | hjk
      · subst j; simp
      · simp [Function.update_of_ne hjk]
    simpa only [F, F', hupd, Function.update_self] using hd
  have hout := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := t₀) (b := t) (F := F) (F' := F') (x₀ := x k)
    (s := Set.univ) Filter.univ_mem hFmeas hFint hF'meas hbnd hbint hdiff
  simpa only [F, F', Function.update_eq_self] using hout.2

/-- The Hessian kernel integral is the actual iterated coordinate derivative
of the Euclidean Duhamel solution. -/
theorem hasDerivAt_deriv_heatDuhamelND_coord
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n) :
    HasDerivAt
      (deriv (fun a => ∫ s in t₀..t,
        heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a)))
      (∫ s in t₀..t, ∫ y : Fin n → ℝ,
        (heatKernelND (t - s) (x - y) *
          ((x - y) k ^ 2 / (4 * (t - s) ^ 2) - 1 / (2 * (t - s)))) * q s y)
      (x k) := by
  let U : ℝ → ℝ := fun a => ∫ s in t₀..t,
    heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a)
  let G : ℝ → ℝ := fun a => ∫ s in t₀..t, ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x k a - y) *
      (-(Function.update x k a - y) k / (2 * (t - s)))) * q s y
  have hUG : deriv U = G := by
    funext a
    have hd := hasDerivAt_heatDuhamelND_coord hT hq hqb
      (Function.update x k a) k
    have hupd : ∀ b : ℝ, Function.update (Function.update x k a) k b =
        Function.update x k b := by
      intro b
      funext j
      rcases eq_or_ne j k with hjk | hjk
      · subst j; simp
      · simp [Function.update_of_ne hjk]
    simpa only [U, G, hupd, Function.update_self] using hd.deriv
  rw [show (deriv (fun a => ∫ s in t₀..t,
      heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a))) = G by
        simpa only [U] using hUG]
  simpa only [G] using
    hasDerivAt_heatDuhamelND_coordGradient hT hr0 hq hH hqb hqholder x k

/-- **Actual coordinate-Hessian Schauder bound for the Duhamel solution.**
The iterated derivative, rather than only its representing kernel integral,
obeys the time-integrated `C^r → C^2` estimate. -/
theorem abs_secondDeriv_heatDuhamelND_coord_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤ H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n) :
    |deriv (deriv (fun a => ∫ s in t₀..t,
      heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a))) (x k)| ≤
      H * heatHessianHolderMoment n r k * ((t - t₀) ^ (r / 2) / (r / 2)) := by
  rw [(hasDerivAt_deriv_heatDuhamelND_coord hT hr0 hq hH hqb hqholder x k).deriv]
  exact abs_intervalIntegral_secondDeriv_heatKernelND_convolution_le
    hT hr0 (fun s => ⇑(q s)) hH
    (fun s => (q s).continuous.aestronglyMeasurable) hqb hqholder x k
    (intervalIntegrable_hessian_heatKernelND_convolution
      hT hr0 hq hH hqb hqholder x k)

end AnalyticPDE
end RicciFlow
