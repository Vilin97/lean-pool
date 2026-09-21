/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.HeatKernelSchauder

/-!
# Classical spatial regularity of the Euclidean Duhamel potential

This module packages the coordinate-Hessian kernel from the Schauder estimate
as a continuous bounded function.  In particular, the second derivatives
proved in `HeatKernelSchauder` are not merely pointwise expressions: at every
fixed final time they form continuous spatial fields, as required for the
domain of the heat generator.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Convolution with one diagonal coordinate Hessian of the Euclidean heat
kernel. -/
def heatHessianCoordConvolutionND {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ,
    (heatKernelND t (x - y) *
      ((x - y) k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * f y

/-- A diagonal heat-kernel Hessian convolution is spatially continuous for
bounded continuous data. -/
theorem continuous_heatHessianCoordConvolutionND
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (hf : Continuous f)
    (hfb : ∀ y, |f y| ≤ C) (k : Fin n) :
    Continuous (heatHessianCoordConvolutionND t f k) := by
  let K : (Fin n → ℝ) → ℝ := fun z =>
    heatKernelND t z * (z k ^ 2 / (4 * t ^ 2) - 1 / (2 * t))
  have hKi : Integrable K := by
    simpa only [K] using integrable_secondDeriv_coord_heatKernelND ht k
  have hCoV : heatHessianCoordConvolutionND t f k =
      fun x : Fin n → ℝ => ∫ z : Fin n → ℝ, K z * f (x - z) := by
    funext x
    rw [heatHessianCoordConvolutionND,
      ← integral_sub_left_eq_self (fun z => K z * f (x - z)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [K, sub_sub_cancel]
  rw [hCoV]
  apply continuous_of_dominated
      (bound := fun z : Fin n → ℝ => |K z| * C)
  · intro x
    exact (hKi.aestronglyMeasurable.mul
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · intro x
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfb (x - z)) (abs_nonneg (K z))
  · simpa only [Real.norm_eq_abs] using hKi.norm.mul_const C
  · filter_upwards with z
    exact continuous_const.mul (hf.comp (continuous_id.sub continuous_const))

/-- The continuous diagonal Hessian convolution, bundled in the global
sup-norm Banach space. -/
def heatHessianCoordNDbcf {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatHessianCoordConvolutionND t f k)
    (continuous_heatHessianCoordConvolutionND (C := ‖f‖) ht f.continuous
      (fun y => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y) k)
    (‖f‖ / t)
    (fun x => by
      rw [Real.norm_eq_abs]
      simpa only [heatHessianCoordConvolutionND] using
        heatSemigroupND_coord_second_deriv_integral_bound ht x k
          f.continuous.aestronglyMeasurable
          (fun y => f.norm_coe_le_norm y))

@[simp] theorem heatHessianCoordNDbcf_apply {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n)
    (x : Fin n → ℝ) :
    heatHessianCoordNDbcf ht f k x = heatHessianCoordConvolutionND t f k x :=
  rfl

/-- The time-integrated diagonal Hessian of a Duhamel potential. -/
def heatDuhamelHessianCoordND {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ s in t₀..t, heatHessianCoordConvolutionND (t - s) (q s) k x

/-- At a fixed final time, the Duhamel coordinate Hessian is a continuous
function of space.  The proof uses the cancellation-improved integrable
majorant `(t-s)^(-1+r/2)` uniformly in the spatial parameter. -/
theorem continuous_heatDuhamelHessianCoordND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) :
    Continuous (heatDuhamelHessianCoordND t₀ t q k) := by
  let A : ℝ := H * heatHessianHolderMoment n r k
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc t₀ t)
  have hgintI : IntervalIntegrable g volume t₀ t := by
    have hrexp : (-1 : ℝ) < -1 + r / 2 := by linarith
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2))
        volume 0 (t - t₀) := intervalIntegral.intervalIntegrable_rpow' hrexp
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2))
        volume t₀ t := by simpa using hcomp.symm
    exact hw.const_mul A
  have hgint : Integrable g μ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hgintI
  have hmeas : ∀ x : Fin n → ℝ,
      AEStronglyMeasurable
        (fun s => heatHessianCoordConvolutionND (t - s) (q s) k x) μ := by
    intro x
    have hm := aestronglyMeasurable_hessian_heatKernelND_convolution_time
      (t := t) hq x k
    simpa only [heatHessianCoordConvolutionND] using hm.restrict
  have hbnd : ∀ x : Fin n → ℝ, ∀ᵐ s ∂μ,
      ‖heatHessianCoordConvolutionND (t - s) (q s) k x‖ ≤ g s := by
    intro x
    rw [ae_restrict_iff' measurableSet_Ioc]
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
      rw [ae_iff, hset]
      exact measure_singleton t
    filter_upwards [htne] with s hst hs
    have hst' : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    rw [Real.norm_eq_abs]
    have hb := abs_secondDeriv_heatKernelND_convolution_le_of_coordHolder_scale
      hst' hr0.le hH x k (q s).continuous.aestronglyMeasurable
      (hqb s) (hqholder s x)
    change |heatHessianCoordConvolutionND (t - s) (q s) k x| ≤ g s
    calc
      |heatHessianCoordConvolutionND (t - s) (q s) k x| ≤
          H * (t - s) ^ (-1 + r / 2) * heatHessianHolderMoment n r k := by
        simpa only [heatHessianCoordConvolutionND] using hb
      _ = g s := by simp only [g, A]; ring
  have hcont : ∀ᵐ s ∂μ, Continuous
      (fun x : Fin n → ℝ => heatHessianCoordConvolutionND (t - s) (q s) k x) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext s; simp
      rw [ae_iff, hset]
      exact measure_singleton t
    filter_upwards [htne] with s hst hs
    exact continuous_heatHessianCoordConvolutionND
      (sub_pos.mpr (lt_of_le_of_ne hs.2 hst))
      (q s).continuous
      (fun y => by simpa only [Real.norm_eq_abs] using hqb s y) k
  have hc : Continuous (fun x : Fin n → ℝ =>
      ∫ s, heatHessianCoordConvolutionND (t - s) (q s) k x ∂μ) :=
    continuous_of_dominated hmeas hbnd hgint hcont
  have hfun : heatDuhamelHessianCoordND t₀ t q k =
      fun x : Fin n → ℝ =>
        ∫ s, heatHessianCoordConvolutionND (t - s) (q s) k x ∂μ := by
    funext x
    rw [heatDuhamelHessianCoordND, intervalIntegral.integral_of_le hT]
  rw [hfun]
  exact hc

/-- The Duhamel coordinate Hessian as an element of the bounded continuous
function space. -/
def heatDuhamelHessianCoordNDbcf
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatDuhamelHessianCoordND t₀ t q k)
    (continuous_heatDuhamelHessianCoordND hT hr0 hq hH hqb hqholder k)
    (H * heatHessianHolderMoment n r k *
      ((t - t₀) ^ (r / 2) / (r / 2)))
    (fun x => by
      rw [Real.norm_eq_abs]
      simpa only [heatDuhamelHessianCoordND, heatHessianCoordConvolutionND] using
        abs_intervalIntegral_secondDeriv_heatKernelND_convolution_le
          hT hr0 (fun s => ⇑(q s)) hH
          (fun s => (q s).continuous.aestronglyMeasurable) hqb hqholder x k
          (intervalIntegrable_hessian_heatKernelND_convolution
            hT hr0 hq hH hqb hqholder x k))

@[simp] theorem heatDuhamelHessianCoordNDbcf_apply
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianCoordNDbcf hT hr0 hq hH hqb hqholder k x =
      heatDuhamelHessianCoordND t₀ t q k x :=
  rfl

/-- The bundled Hessian field is the actual iterated coordinate derivative of
the Duhamel potential. -/
theorem deriv2_heatDuhamelND_coord_eq_bcf
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) (k : Fin n) :
    deriv (deriv (fun a => ∫ s in t₀..t,
      heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a))) (x k) =
      heatDuhamelHessianCoordNDbcf hT hr0 hq hH hqb hqholder k x := by
  rw [(hasDerivAt_deriv_heatDuhamelND_coord
    hT hr0 hq hH hqb hqholder x k).deriv]
  rfl

/-- The spatial Laplacian of the Euclidean Duhamel potential, defined as the
finite trace of its actual coordinate Hessians. -/
def heatDuhamelLaplacianND {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, heatDuhamelHessianCoordND t₀ t q k x

/-- The Duhamel Laplacian is spatially continuous. -/
theorem continuous_heatDuhamelLaplacianND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r) :
    Continuous (heatDuhamelLaplacianND t₀ t q) := by
  apply continuous_finsetSum
  intro k _
  exact continuous_heatDuhamelHessianCoordND hT hr0 hq hH hqb hqholder k

/-- The actual coordinate Laplacian of the Duhamel potential agrees with the
finite sum of its time-integrated Hessian kernels. -/
theorem sum_secondDeriv_heatDuhamelND_eq_laplacian
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    (∑ k : Fin n, deriv (deriv (fun a => ∫ s in t₀..t,
      heatSemigroupND (t - s) (⇑(q s)) (Function.update x k a))) (x k)) =
      heatDuhamelLaplacianND t₀ t q x := by
  rw [heatDuhamelLaplacianND]
  apply Finset.sum_congr rfl
  intro k _
  rw [(hasDerivAt_deriv_heatDuhamelND_coord
    hT hr0 hq hH hqb hqholder x k).deriv]
  rfl

/-- The Duhamel Laplacian as a bounded continuous function. -/
def heatDuhamelLaplacianNDbcf
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∑ k : Fin n,
    heatDuhamelHessianCoordNDbcf hT hr0 hq hH hqb hqholder k

@[simp] theorem heatDuhamelLaplacianNDbcf_apply
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r)
    (x : Fin n → ℝ) :
    heatDuhamelLaplacianNDbcf hT hr0 hq hH hqb hqholder x =
      heatDuhamelLaplacianND t₀ t q x := by
  simp [heatDuhamelLaplacianNDbcf, heatDuhamelLaplacianND,
    heatDuhamelHessianCoordNDbcf_apply]

/-- Quantitative global sup-norm bound for the Duhamel Laplacian. -/
theorem norm_heatDuhamelLaplacianNDbcf_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ j : Fin n, |(x - y) j| ^ r) :
    ‖heatDuhamelLaplacianNDbcf hT hr0 hq hH hqb hqholder‖ ≤
      ∑ k : Fin n, H * heatHessianHolderMoment n r k *
        ((t - t₀) ^ (r / 2) / (r / 2)) := by
  calc
    ‖heatDuhamelLaplacianNDbcf hT hr0 hq hH hqb hqholder‖ ≤
        ∑ k : Fin n,
          ‖heatDuhamelHessianCoordNDbcf hT hr0 hq hH hqb hqholder k‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ k : Fin n, H * heatHessianHolderMoment n r k *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [BoundedContinuousFunction.norm_le]
      · intro x
        rw [heatDuhamelHessianCoordNDbcf_apply, Real.norm_eq_abs]
        simpa only [heatDuhamelHessianCoordND, heatHessianCoordConvolutionND] using
          abs_intervalIntegral_secondDeriv_heatKernelND_convolution_le
            hT hr0 (fun s => ⇑(q s)) hH
            (fun s => (q s).continuous.aestronglyMeasurable) hqb hqholder x k
            (intervalIntegrable_hessian_heatKernelND_convolution
              hT hr0 hq hH hqb hqholder x k)
      · exact mul_nonneg
          (mul_nonneg hH (heatHessianHolderMoment_nonneg n r k))
          (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _) (by linarith))

/-! ### Fractional approximate identity in the global sup norm -/

/-- A coordinatewise fractional moment of the product heat kernel has the
same value as its one-dimensional factor. -/
theorem integral_abs_coord_rpow_mul_heatKernelND_eq
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : -1 < r) (j : Fin n) :
    (∫ z : Fin n → ℝ, |z j| ^ r * heatKernelND t z) =
      (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  classical
  let F : Fin n → ℝ → ℝ := fun i z =>
    if i = j then |z| ^ r * heatKernel1D t z else heatKernel1D t z
  have hp : (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z) =
      fun z => ∏ i, F i (z i) := by
    funext z
    rw [heatKernelND_apply]
    have hfactor : (∏ i, F i (z i)) =
        (∏ i, if i = j then |z i| ^ r else (1 : ℝ)) *
          ∏ i, heatKernel1D t (z i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      simp only [F]
      split_ifs <;> ring
    rw [hfactor, Finset.prod_ite_eq']
    simp
  rw [hp, integral_fin_nat_prod_volume_eq_prod]
  have hi : ∀ i, (∫ z : ℝ, F i z) = if i = j then
      (Real.sqrt t) ^ r * gaussianAbsMoment r else 1 := by
    intro i
    rcases eq_or_ne i j with rfl | hij
    · simp only [F, if_pos]
      exact integral_abs_rpow_mul_heatKernel1D_eq ht hr
    · simp only [F, if_neg hij, integral_heatKernel1D ht]
  rw [Finset.prod_congr rfl (fun i _ => hi i), Finset.prod_ite_eq']
  simp

/-- The coordinatewise fractional moment is integrable. -/
lemma integrable_abs_coord_rpow_mul_heatKernelND
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : -1 < r) (j : Fin n) :
    Integrable (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z) := by
  classical
  have hp : (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z) =
      fun z => ∏ i, if i = j then
        |z i| ^ r * heatKernel1D t (z i) else heatKernel1D t (z i) := by
    funext z
    rw [heatKernelND_apply]
    have hfactor :
        (∏ i, if i = j then |z i| ^ r * heatKernel1D t (z i)
          else heatKernel1D t (z i)) =
        (∏ i, if i = j then |z i| ^ r else (1 : ℝ)) *
          ∏ i, heatKernel1D t (z i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> ring
    rw [hfactor, Finset.prod_ite_eq']
    simp
  rw [hp, volume_pi]
  refine Integrable.fin_nat_prod
    (f := fun i z => if i = j then
      |z| ^ r * heatKernel1D t z else heatKernel1D t z) (fun i => ?_)
  rcases eq_or_ne i j with rfl | hij
  · simpa using integrable_abs_rpow_mul_heatKernel1D ht hr
  · simpa [hij] using integrable_heatKernel1D ht

/-- Quantitative approximate-identity estimate for a bounded function with a
global coordinatewise `r`-Hölder modulus.  Unlike the earlier Lipschitz-only
estimate, this has the exact `t^(r/2)` scale needed at a Schauder endpoint. -/
theorem abs_heatSemigroupND_sub_self_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    {w : (Fin n → ℝ) → ℝ} {C H : ℝ} (_hH : 0 ≤ H)
    (hwm : AEStronglyMeasurable w) (hwb : ∀ y, ‖w y‖ ≤ C)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r)
    (x : Fin n → ℝ) :
    |heatSemigroupND t w x - w x| ≤
      H * ∑ _j : Fin n, (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  have hker_w : Integrable (fun y => heatKernelND t (x - y) * w y) :=
    integrable_heatKernelND_sub_mul ht x hwm hwb
  have hker_c : Integrable (fun y => heatKernelND t (x - y) * w x) :=
    (integrable_heatKernelND_sub ht x).mul_const (w x)
  have hcoord_int : ∀ j : Fin n,
      Integrable (fun y => heatKernelND t (x - y) * |(x - y) j| ^ r) := by
    intro j
    have h := (integrable_abs_coord_rpow_mul_heatKernelND ht
      (show -1 < r by linarith) j).comp_sub_left x
    exact h.congr (Filter.Eventually.of_forall (fun y => by ring))
  have key : heatSemigroupND t w x - w x =
      ∫ y, heatKernelND t (x - y) * (w y - w x) := by
    have hsub : (∫ y, heatKernelND t (x - y) * (w y - w x)) =
        (∫ y, heatKernelND t (x - y) * w y) -
          ∫ y, heatKernelND t (x - y) * w x := by
      rw [← integral_sub hker_w hker_c]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
    rw [hsub, integral_mul_const, integral_heatKernelND_sub ht, one_mul,
      heatSemigroupND]
  have hpoint : ∀ y, ‖heatKernelND t (x - y) * (w y - w x)‖ ≤
      H * ∑ j : Fin n, heatKernelND t (x - y) * |(x - y) j| ^ r := by
    intro y
    have hK : 0 ≤ heatKernelND t (x - y) := heatKernelND_nonneg ht _
    calc
      ‖heatKernelND t (x - y) * (w y - w x)‖ =
          heatKernelND t (x - y) * |w y - w x| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
      _ ≤ heatKernelND t (x - y) *
          (H * ∑ j : Fin n, |(x - y) j| ^ r) := by
            apply mul_le_mul_of_nonneg_left _ hK
            have hh := hholder y x
            simpa only [Pi.sub_apply, abs_sub_comm] using hh
      _ = H * ∑ j : Fin n,
          heatKernelND t (x - y) * |(x - y) j| ^ r := by
            simp only [Finset.mul_sum]
            ring
  have hRHS : Integrable (fun y => H * ∑ j : Fin n,
      heatKernelND t (x - y) * |(x - y) j| ^ r) :=
    (integrable_finsetSum _ (fun j _ => hcoord_int j)).const_mul H
  rw [key, ← Real.norm_eq_abs]
  calc
    ‖∫ y, heatKernelND t (x - y) * (w y - w x)‖ ≤
        ∫ y, ‖heatKernelND t (x - y) * (w y - w x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, H * ∑ j : Fin n,
        heatKernelND t (x - y) * |(x - y) j| ^ r :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hRHS
        (Filter.Eventually.of_forall hpoint)
    _ = H * ∑ j : Fin n,
        ∫ y, heatKernelND t (x - y) * |(x - y) j| ^ r := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hcoord_int j)]
    _ = H * ∑ _j : Fin n,
        (Real.sqrt t) ^ r * gaussianAbsMoment r := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hshift : (∫ y, heatKernelND t (x - y) * |(x - y) j| ^ r) =
          ∫ z, |z j| ^ r * heatKernelND t z := by
        rw [show (fun y => heatKernelND t (x - y) * |(x - y) j| ^ r) =
            fun y => |(x - y) j| ^ r * heatKernelND t (x - y) by
              funext y; ring]
        exact integral_sub_left_eq_self
          (fun z : Fin n → ℝ => |z j| ^ r * heatKernelND t z) volume x
      rw [hshift, integral_abs_coord_rpow_mul_heatKernelND_eq ht
        (show -1 < r by linarith) j]

/-- Sup-norm form of the fractional approximate-identity estimate. -/
theorem norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r) :
    ‖heatSemigroupNDbcf ht w - w‖ ≤
      H * ∑ _j : Fin n, (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  have hb := fun x => abs_heatSemigroupND_sub_self_le_of_coordHolder
    ht hr hH w.continuous.aestronglyMeasurable
      (fun y => w.norm_coe_le_norm y) hholder x
  have hnonneg : 0 ≤ H * ∑ _j : Fin n,
      (Real.sqrt t) ^ r * gaussianAbsMoment r := by
    apply mul_nonneg hH
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg t) r)
      (gaussianAbsMoment_nonneg r)
  rw [BoundedContinuousFunction.norm_le hnonneg]
  intro x
  rw [BoundedContinuousFunction.sub_apply, heatSemigroupNDbcf_apply,
    Real.norm_eq_abs]
  exact hb x

/-- Strong right-continuity at heat-time zero for globally coordinatewise
Hölder bounded data. -/
theorem continuousWithinAt_heatFlowPathBcf_zero_of_coordHolder
    {n : ℕ} {r : ℝ} (hr : 0 < r)
    (w : BoundedContinuousFunction (Fin n → ℝ) ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ a b, |w a - w b| ≤
      H * ∑ j : Fin n, |(a - b) j| ^ r) :
    ContinuousWithinAt (heatFlowPathBcf w) (Set.Ici 0) 0 := by
  have hzero : heatFlowPathBcf w 0 = w := dif_neg (lt_irrefl 0)
  let g : ℝ → ℝ := fun s =>
    H * ∑ _j : Fin n, (Real.sqrt s) ^ r * gaussianAbsMoment r
  have hbound : ∀ s : ℝ, 0 ≤ s → dist (heatFlowPathBcf w s) w ≤ g s := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hspos
    · rw [hzero, dist_self]
      simp only [g, Real.sqrt_zero, Real.zero_rpow hr.ne', zero_mul,
        Finset.sum_const_zero, mul_zero]
      exact le_rfl
    · rw [heatFlowPathBcf_of_pos w hspos, dist_eq_norm]
      exact norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder
        hspos hr.le w hH hholder
  have hg : Filter.Tendsto g (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    have hpow : Continuous (fun s : ℝ => (Real.sqrt s) ^ r) :=
      Real.continuous_sqrt.rpow_const (fun _ => Or.inr hr.le)
    have hcont : ContinuousAt g 0 :=
      (continuous_const.mul
        (continuous_finsetSum Finset.univ
          (fun _j _ => hpow.mul continuous_const))).continuousAt
    have hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ici 0)) (nhds (g 0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [g, Real.sqrt_zero, Real.zero_rpow hr.ne', zero_mul,
      Finset.sum_const_zero, mul_zero] using hlim
  show Filter.Tendsto (heatFlowPathBcf w) (nhdsWithin 0 (Set.Ici 0))
    (nhds (heatFlowPathBcf w 0))
  rw [hzero, tendsto_iff_dist_tendsto_zero]
  have hev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ici 0),
      dist (heatFlowPathBcf w s) w ≤ g s := by
    filter_upwards [self_mem_nhdsWithin] with s hs using hbound s hs
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) hev hg

end AnalyticPDE
end RicciFlow
