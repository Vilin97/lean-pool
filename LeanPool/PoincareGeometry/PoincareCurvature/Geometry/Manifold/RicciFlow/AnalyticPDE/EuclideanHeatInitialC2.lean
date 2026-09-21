/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatFrechet

/-!
# Heat flow of bounded C2 initial data

The kernel-derivative formula is useful for positive-time smoothing, but its
raw estimate is singular as time tends to zero.  For genuinely C2 initial
data the derivatives instead commute through the Euclidean heat semigroup.
This file proves that fact from the translated heat-kernel integral and
packages the resulting uniform Hessian estimate.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The heat convolution in fixed-kernel coordinates. -/
theorem heatSemigroupND_eq_integral_kernel_mul_sub
    {n : ℕ} {t : ℝ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    heatSemigroupND t f x =
      ∫ z : Fin n → ℝ, heatKernelND t z * f (x - z) := by
  rw [heatSemigroupND,
    ← integral_sub_left_eq_self
      (fun z : Fin n → ℝ => heatKernelND t z * f (x - z)) volume x]
  congr 1
  funext y
  rw [sub_sub_cancel]

/-- Re-anchor an everywhere coordinate-derivative witness at an arbitrary
value of that coordinate. -/
lemma hasDerivAt_coord_update_of_everywhere
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {k : Fin n}
    (hfg : ∀ x, HasDerivAt (fun a ↦ f (Function.update x k a)) (g x) (x k))
    (x : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun b ↦ f (Function.update x k b))
      (g (Function.update x k a)) a := by
  have h := hfg (Function.update x k a)
  simpa only [Function.update_self, Function.update_idem] using h

/-- A bounded coordinate derivative commutes through the Euclidean heat
semigroup.  The proof uses fixed-kernel coordinates, so differentiation falls
on the datum rather than on the Gaussian. -/
theorem hasDerivAt_heatSemigroupND_coord_of_bounded_deriv
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f g : BoundedContinuousFunction (Fin n → ℝ) ℝ) (k : Fin n)
    (hfg : ∀ x, HasDerivAt (fun a ↦ f (Function.update x k a)) (g x) (x k))
    (x : Fin n → ℝ) :
    HasDerivAt (fun a ↦ heatSemigroupND t f (Function.update x k a))
      (heatSemigroupND t g x) (x k) := by
  classical
  let F : ℝ → (Fin n → ℝ) → ℝ := fun a z ↦
    heatKernelND t z * f (Function.update x k a - z)
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun a z ↦
    heatKernelND t z * g (Function.update x k a - z)
  let bound : (Fin n → ℝ) → ℝ := fun z ↦
    heatKernelND t z * ‖g‖
  have hFmeas : ∀ᶠ a in nhds (x k),
      AEStronglyMeasurable (F a) (volume : Measure (Fin n → ℝ)) := by
    filter_upwards with a
    exact ((continuous_heatKernelND t).mul
      (f.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hFint : Integrable (F (x k)) (volume : Measure (Fin n → ℝ)) := by
    exact (integrable_heatKernelND ht).mul_bdd
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z ↦ f.norm_coe_le_norm _))
  have hF'meas : AEStronglyMeasurable (F' (x k))
      (volume : Measure (Fin n → ℝ)) := by
    exact ((continuous_heatKernelND t).mul
      (g.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hboundint : Integrable bound (volume : Measure (Fin n → ℝ)) :=
    (integrable_heatKernelND ht).mul_const ‖g‖
  have hbnd : ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)),
      ∀ a ∈ Metric.ball (x k) 1, ‖F' a z‖ ≤ bound z := by
    filter_upwards with z a ha
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (heatKernelND_nonneg ht z)]
    exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (heatKernelND_nonneg ht z)
  have hderiv : ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)),
      ∀ a ∈ Metric.ball (x k) 1,
        HasDerivAt (fun b ↦ F b z) (F' a z) a := by
    filter_upwards with z a ha
    have hsub : ∀ b : ℝ,
        Function.update x k b - z =
          Function.update (x - z) k (b - z k) := by
      intro b
      funext i
      by_cases hik : i = k
      · subst i
        simp
      · simp [Function.update_of_ne hik]
    have hd := hasDerivAt_coord_update_of_everywhere hfg (x - z) (a - z k)
    have hlin : HasDerivAt (fun b : ℝ ↦ b - z k) 1 a := by
      simpa using (hasDerivAt_id a).sub_const (z k)
    have hc := hd.comp a hlin
    rw [mul_one] at hc
    have hfun : (fun b ↦ F b z) = fun b ↦
        heatKernelND t z * f (Function.update (x - z) k (b - z k)) := by
      funext b
      simp only [F]
      rw [hsub b]
    rw [hfun]
    have hF' : F' a z = heatKernelND t z *
        g (Function.update (x - z) k (a - z k)) := by
      simp only [F']
      rw [hsub a]
    rw [hF']
    simpa only [Function.comp_apply] using hc.const_mul (heatKernelND t z)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Fin n → ℝ))) (F := F) (x₀ := x k)
    (bound := bound) (s := Metric.ball (x k) 1)
    (Metric.ball_mem_nhds (x k) one_pos) hFmeas hFint hF'meas hbnd
      hboundint hderiv
  have hfun : (fun a ↦ heatSemigroupND t f (Function.update x k a)) =
      fun a ↦ ∫ z : Fin n → ℝ, F a z := by
    funext a
    simpa only [F] using
      heatSemigroupND_eq_integral_kernel_mul_sub (t := t) f
        (Function.update x k a)
  have hval : (∫ z : Fin n → ℝ, F' (x k) z) = heatSemigroupND t g x := by
    rw [heatSemigroupND_eq_integral_kernel_mul_sub]
    congr 1
    funext z
    simp only [F', Function.update_eq_self]
  rw [hfun, ← hval]
  exact key.2

/-- Heat convolution preserves a coordinatewise spatial Holder modulus. -/
theorem abs_heatSemigroupND_sub_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    |heatSemigroupND t f x - heatSemigroupND t f y| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r := by
  let B : ℝ := H * ∑ ell : Fin n, |(x - y) ell| ^ r
  have hB : 0 ≤ B := mul_nonneg hH (Finset.sum_nonneg fun _ _ ↦
    Real.rpow_nonneg (abs_nonneg _) r)
  let Fx : (Fin n → ℝ) → ℝ := fun z ↦ heatKernelND t z * f (x - z)
  let Fy : (Fin n → ℝ) → ℝ := fun z ↦ heatKernelND t z * f (y - z)
  have hFxi : Integrable Fx := (integrable_heatKernelND ht).mul_bdd
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z ↦ f.norm_coe_le_norm _))
  have hFyi : Integrable Fy := (integrable_heatKernelND ht).mul_bdd
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z ↦ f.norm_coe_le_norm _))
  have hdom : Integrable (fun z : Fin n → ℝ ↦ heatKernelND t z * B) :=
    (integrable_heatKernelND ht).mul_const B
  have hpoint : ∀ z : Fin n → ℝ, ‖Fx z - Fy z‖ ≤ heatKernelND t z * B := by
    intro z
    rw [Real.norm_eq_abs]
    have hdiff : |f (x - z) - f (y - z)| ≤ B := by
      have hh := hholder (x - z) (y - z)
      simpa only [B, Pi.sub_apply, sub_sub_sub_cancel_right] using hh
    simp only [Fx, Fy]
    rw [← mul_sub, abs_mul, abs_of_nonneg (heatKernelND_nonneg ht z)]
    exact mul_le_mul_of_nonneg_left hdiff (heatKernelND_nonneg ht z)
  rw [heatSemigroupND_eq_integral_kernel_mul_sub,
    heatSemigroupND_eq_integral_kernel_mul_sub]
  have hmain : |(∫ z, Fx z) - ∫ z, Fy z| ≤ B := by
    rw [← integral_sub hFxi hFyi, ← Real.norm_eq_abs]
    calc
      ‖∫ z, Fx z - Fy z‖ ≤ ∫ z, heatKernelND t z * B :=
        norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
      _ = B := by rw [integral_mul_const, integral_heatKernelND ht, one_mul]
  simpa only [Fx, Fy, B] using hmain

/-- Bundled Chapman--Kolmogorov law on bounded continuous functions. -/
theorem heatSemigroupNDbcf_comp {n : ℕ} (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    heatSemigroupNDbcf ht (heatSemigroupNDbcf hs f) =
      heatSemigroupNDbcf (add_pos ht hs) f := by
  ext x
  exact heatSemigroupND_comp t s ht hs x f.continuous.aestronglyMeasurable
    (fun y ↦ f.norm_coe_le_norm y)

/-- Bounded scalar C2 data on Euclidean space, recorded by bounded continuous
coordinate derivatives and their actual derivative witnesses. -/
structure EuclideanBoundedC2Data (n : ℕ) where
  value : BoundedContinuousFunction (Fin n → ℝ) ℝ
  first : Fin n → BoundedContinuousFunction (Fin n → ℝ) ℝ
  second : Fin n → Fin n → BoundedContinuousFunction (Fin n → ℝ) ℝ
  hasDeriv_value : ∀ k x,
    HasDerivAt (fun a ↦ value (Function.update x k a)) (first k x) (x k)
  hasDeriv_first : ∀ j k x,
    HasDerivAt (fun a ↦ first k (Function.update x j a)) (second j k x) (x j)

namespace EuclideanBoundedC2Data

/-- The kernel gradient of the heat evolution of C1 data is the heat
evolution of the actual first derivative. -/
theorem heatSemigroupGradientCoordND_eq
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (k : Fin n) (x : Fin n → ℝ) :
    heatSemigroupGradientCoordND t D.value k x =
      heatSemigroupND t (D.first k) x := by
  have hkernel : HasDerivAt
      (fun a ↦ heatSemigroupND t D.value (Function.update x k a))
      (heatSemigroupGradientCoordND t D.value k x) (x k) := by
    simpa only [heatSemigroupGradientCoordND] using
      hasDerivAt_heatSemigroupND_coord ht x k
        D.value.continuous.aestronglyMeasurable
        (fun y ↦ D.value.norm_coe_le_norm y)
  have htransfer := hasDerivAt_heatSemigroupND_coord_of_bounded_deriv
    ht D.value (D.first k) k (D.hasDeriv_value k) x
  exact hkernel.unique htransfer

/-- Every full Hessian-kernel entry of the heat evolution of bounded C2 data
is the heat evolution of the corresponding actual second derivative. -/
theorem heatHessianEntryConvolutionND_eq
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatHessianEntryConvolutionND t D.value j k x =
      heatSemigroupND t (D.second j k) x := by
  have hkernel : HasDerivAt
      (fun a ↦ heatSemigroupGradientCoordND t D.value k
        (Function.update x j a))
      (heatHessianEntryConvolutionND t D.value j k x) (x j) := by
    simpa only [heatSemigroupGradientCoordND,
      heatHessianEntryConvolutionND] using
      hasDerivAt_heatSemigroupND_coordGradient_entry ht x j k
        D.value.continuous.aestronglyMeasurable
        (fun y ↦ D.value.norm_coe_le_norm y)
  have htransfer := hasDerivAt_heatSemigroupND_coord_of_bounded_deriv
    ht (D.first k) (D.second j k) j (D.hasDeriv_first j k) x
  have hfun :
      (fun a ↦ heatSemigroupGradientCoordND t D.value k
        (Function.update x j a)) =
      (fun a ↦ heatSemigroupND t (D.first k)
        (Function.update x j a)) := by
    funext a
    exact D.heatSemigroupGradientCoordND_eq ht k (Function.update x j a)
  rw [hfun] at hkernel
  exact hkernel.unique htransfer

/-- The homogeneous heat Hessian has a time-uniform entrywise bound supplied
by the bounded initial Hessian, with no positive-time singularity. -/
theorem abs_heatHessianEntryConvolutionND_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t D.value j k x| ≤ ‖D.second j k‖ := by
  rw [D.heatHessianEntryConvolutionND_eq ht j k x]
  exact abs_heatSemigroupND_le ht x (fun y ↦ by
    simpa only [Real.norm_eq_abs] using D.second j k |>.norm_coe_le_norm y)

/-- Operator-norm form of the time-uniform homogeneous Hessian estimate. -/
theorem norm_heatSemigroupHessianCLM_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t D.value x‖ ≤
      ∑ j : Fin n, ∑ k : Fin n, ‖D.second j k‖ := by
  unfold heatSemigroupHessianCLM
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact D.abs_heatHessianEntryConvolutionND_le ht j k x

/-- The homogeneous heat Hessian preserves the spatial Holder modulus of the
initial Hessian, entry by entry and uniformly down to time zero. -/
theorem abs_heatHessianEntryConvolutionND_sub_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t r : ℝ} (ht : 0 < t)
    {H₂ : ℝ} (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t D.value j k x -
        heatHessianEntryConvolutionND t D.value j k y| ≤
      H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r := by
  rw [D.heatHessianEntryConvolutionND_eq ht j k x,
    D.heatHessianEntryConvolutionND_eq ht j k y]
  exact abs_heatSemigroupND_sub_le_of_coordHolder ht (D.second j k) hH₂
    (hsecondHolder j k) x y

/-- Quantitative convergence of the homogeneous heat Hessian to the actual
initial Hessian at the C2,alpha endpoint. -/
theorem abs_heatHessianEntryConvolutionND_sub_initial_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t r : ℝ} (ht : 0 < t)
    (hr : 0 ≤ r) {H₂ : ℝ} (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t D.value j k x - D.second j k x| ≤
      H₂ * ∑ _ell : Fin n,
        (Real.sqrt t) ^ r * gaussianAbsMoment r := by
  rw [D.heatHessianEntryConvolutionND_eq ht j k x]
  exact abs_heatSemigroupND_sub_self_le_of_coordHolder ht hr hH₂
    (D.second j k).continuous.aestronglyMeasurable
    (fun y ↦ (D.second j k).norm_coe_le_norm y)
    (hsecondHolder j k) x

/-- Time Holder estimate for one actual homogeneous heat-Hessian entry.  It
is obtained by factoring the later heat flow through the earlier one and
applying the approximate-identity estimate to the initial Hessian. -/
theorem abs_heatHessianEntryConvolutionND_time_sub_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {s t r : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hr : 0 ≤ r)
    {H₂ : ℝ} (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatHessianEntryConvolutionND t D.value j k x -
        heatHessianEntryConvolutionND s D.value j k x| ≤
      H₂ * ∑ _ell : Fin n,
        (Real.sqrt (t - s)) ^ r * gaussianAbsMoment r := by
  by_cases heq : s = t
  · subst t
    simp only [sub_self, abs_zero]
    apply mul_nonneg hH₂
    apply Finset.sum_nonneg
    intro ell hell
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg 0) r)
      (gaussianAbsMoment_nonneg r)
  · have hst' : s < t := lt_of_le_of_ne hst heq
    have ht : 0 < t := hs.trans hst'
    have hd : 0 < t - s := sub_pos.mpr hst'
    let w := D.second j k
    have hcomp : heatSemigroupNDbcf hs (heatSemigroupNDbcf hd w) =
        heatSemigroupNDbcf ht w := by
      have hc := heatSemigroupNDbcf_comp s (t - s) hs hd w
      have htime : s + (t - s) = t := by ring
      simpa only [htime] using hc
    have hcontract :
        ‖heatSemigroupNDbcf ht w - heatSemigroupNDbcf hs w‖ ≤
          ‖heatSemigroupNDbcf hd w - w‖ := by
      rw [← hcomp]
      exact norm_heatSemigroupNDbcf_sub_le hs (heatSemigroupNDbcf hd w) w
    have happ := norm_heatSemigroupNDbcf_sub_self_le_of_coordHolder
      hd hr w hH₂ (hsecondHolder j k)
    rw [D.heatHessianEntryConvolutionND_eq ht j k x,
      D.heatHessianEntryConvolutionND_eq hs j k x]
    calc
      |heatSemigroupND t w x - heatSemigroupND s w x| =
          ‖(heatSemigroupNDbcf ht w - heatSemigroupNDbcf hs w) x‖ := by
        simp only [BoundedContinuousFunction.sub_apply,
          heatSemigroupNDbcf_apply, Real.norm_eq_abs]
      _ ≤ ‖heatSemigroupNDbcf ht w - heatSemigroupNDbcf hs w‖ :=
        (heatSemigroupNDbcf ht w - heatSemigroupNDbcf hs w).norm_coe_le_norm x
      _ ≤ ‖heatSemigroupNDbcf hd w - w‖ := hcontract
      _ ≤ H₂ * ∑ _ell : Fin n,
          (Real.sqrt (t - s)) ^ r * gaussianAbsMoment r := happ

/-- Full operator-norm spatial Holder estimate for the homogeneous heat
Hessian of bounded C2,alpha data. -/
theorem norm_heatSemigroupHessianCLM_sub_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {t r : ℝ} (ht : 0 < t)
    {H₂ : ℝ} (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t D.value x -
        heatSemigroupHessianCLM t D.value y‖ ≤
      ∑ _j : Fin n, ∑ _k : Fin n,
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r := by
  have heq : heatSemigroupHessianCLM t D.value x -
      heatSemigroupHessianCLM t D.value y =
      coordinateHessianCLM (fun j k ↦
        heatHessianEntryConvolutionND t D.value j k x -
          heatHessianEntryConvolutionND t D.value j k y) := by
    ext v w
    simp only [heatSemigroupHessianCLM_apply, coordinateHessianCLM_apply,
      sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact D.abs_heatHessianEntryConvolutionND_sub_le ht hH₂ hsecondHolder j k x y

/-- Full operator-norm time Holder estimate for the homogeneous heat Hessian. -/
theorem norm_heatSemigroupHessianCLM_time_sub_le
    {n : ℕ} (D : EuclideanBoundedC2Data n) {s t r : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hr : 0 ≤ r)
    {H₂ : ℝ} (hH₂ : 0 ≤ H₂)
    (hsecondHolder : ∀ j k x y,
      |D.second j k x - D.second j k y| ≤
        H₂ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t D.value x -
        heatSemigroupHessianCLM s D.value x‖ ≤
      ∑ _j : Fin n, ∑ _k : Fin n,
        H₂ * ∑ _ell : Fin n,
          (Real.sqrt (t - s)) ^ r * gaussianAbsMoment r := by
  have heq : heatSemigroupHessianCLM t D.value x -
      heatSemigroupHessianCLM s D.value x =
      coordinateHessianCLM (fun j k ↦
        heatHessianEntryConvolutionND t D.value j k x -
          heatHessianEntryConvolutionND s D.value j k x) := by
    ext v w
    simp only [heatSemigroupHessianCLM_apply, coordinateHessianCLM_apply,
      sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact D.abs_heatHessianEntryConvolutionND_time_sub_le
    hs hst hr hH₂ hsecondHolder j k x

end EuclideanBoundedC2Data

end AnalyticPDE
end RicciFlow
