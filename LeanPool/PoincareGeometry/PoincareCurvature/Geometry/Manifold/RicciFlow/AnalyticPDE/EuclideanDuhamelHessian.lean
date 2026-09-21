/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatHessian

/-!
# Full spatial Hessian of the Euclidean Duhamel potential

This file integrates the full heat Hessian in time.  Each mixed entry is a
continuous bounded spatial field, is the actual derivative of the appropriate
coordinate-gradient field, and satisfies the time-integrated Schauder bound.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Convolution with one entry of the Euclidean heat Hessian. -/
def heatHessianEntryConvolutionND {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (j k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, heatHessianKernelEntryND t (x - y) j k * f y

/-- A full heat-Hessian convolution is spatially continuous for bounded
continuous data. -/
theorem continuous_heatHessianEntryConvolutionND
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ} {C : ℝ} (hf : Continuous f)
    (hfb : ∀ y, |f y| ≤ C) (j k : Fin n) :
    Continuous (heatHessianEntryConvolutionND t f j k) := by
  let K : (Fin n → ℝ) → ℝ := fun z => heatHessianKernelEntryND t z j k
  have hKi : Integrable K := by
    simpa only [K] using integrable_heatHessianKernelEntryND ht j k
  have hconv : heatHessianEntryConvolutionND t f j k =
      fun x : Fin n → ℝ => ∫ z : Fin n → ℝ, K z * f (x - z) := by
    funext x
    rw [heatHessianEntryConvolutionND,
      ← integral_sub_left_eq_self (fun z => K z * f (x - z)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [K, sub_sub_cancel]
  rw [hconv]
  apply continuous_of_dominated (bound := fun z : Fin n → ℝ => |K z| * C)
  · intro x
    exact hKi.aestronglyMeasurable.mul
      (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfb (x - z)) (abs_nonneg (K z))
  · simpa only [Real.norm_eq_abs] using hKi.norm.mul_const C
  · filter_upwards with z
    exact continuous_const.mul (hf.comp (continuous_id.sub continuous_const))

/-- Time measurability of a full heat-Hessian convolution. -/
lemma aestronglyMeasurable_heatHessianEntryConvolution_time
    {n : ℕ} {t : ℝ}
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    (x : Fin n → ℝ) (j k : Fin n) :
    AEStronglyMeasurable (fun s =>
      heatHessianEntryConvolutionND (t - s) (q s) j k x) := by
  have hK : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatKernelND (t - p.1) (x - p.2)) := by
    have hmap : Measurable (fun p : ℝ × (Fin n → ℝ) => (t - p.1, x - p.2)) :=
      (measurable_const.sub measurable_fst).prodMk
        (measurable_const.sub measurable_snd)
    have hkernel := (measurable_uncurry_heatKernelND (n := n)).comp hmap
    exact hkernel
  have hc : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (x - p.2) j * (x - p.2) k / (4 * (t - p.1) ^ 2) -
        if j = k then 1 / (2 * (t - p.1)) else 0) := by
    by_cases hjk : j = k
    · subst j
      simp only [if_pos]
      fun_prop
    · simp only [if_neg hjk]
      fun_prop
  have hQ : Measurable (fun p : ℝ × (Fin n → ℝ) => q p.1 p.2) :=
    (ContinuousEval.continuous_eval.comp
      ((hq.comp continuous_fst).prodMk continuous_snd)).measurable
  have hG : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatHessianKernelEntryND (t - p.1) (x - p.2) j k * q p.1 p.2) := by
    change Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (heatKernelND (t - p.1) (x - p.2) *
        ((x - p.2) j * (x - p.2) k / (4 * (t - p.1) ^ 2) -
          if j = k then 1 / (2 * (t - p.1)) else 0)) * q p.1 p.2)
    exact (hK.mul hc).mul hQ
  simpa only [heatHessianEntryConvolutionND] using
    (hG.aestronglyMeasurable
      (μ := (volume : Measure ℝ).prod
        (volume : Measure (Fin n → ℝ)))).integral_prod_right'

/-- Cancellation makes the full Hessian convolution integrable up to the
Duhamel endpoint for every positive spatial Holder exponent. -/
lemma intervalIntegrable_heatHessianEntryConvolution
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (j k : Fin n) :
    IntervalIntegrable (fun s =>
      heatHessianEntryConvolutionND (t - s) (q s) j k x) volume t₀ t := by
  let G : ℝ → ℝ := fun s =>
    heatHessianEntryConvolutionND (t - s) (q s) j k x
  let A := H * heatHessianEntryHolderMoment n r j k
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  have hGm : AEStronglyMeasurable G := by
    simpa only [G] using aestronglyMeasurable_heatHessianEntryConvolution_time hq x j k
  have hgint : IntervalIntegrable g volume t₀ t := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2))
        volume 0 (t - t₀) := intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2))
        volume t₀ t := by simpa using hcomp.symm
    exact hw.const_mul A
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr ?_
  have hgOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hgint
  refine hgOn.mono' hGm.restrict ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hs]
    exact measure_singleton t
  filter_upwards [htne] with s hst hs
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  rw [Real.norm_eq_abs]
  have hb := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    hpos hr0.le hH x j k (q s).continuous.aestronglyMeasurable
    (hqb s) (hqholder s x)
  change |G s| ≤ g s
  change |G s| ≤ A * (t - s) ^ (-1 + r / 2)
  change |G s| ≤ H * heatHessianEntryHolderMoment n r j k *
    (t - s) ^ (-1 + r / 2)
  exact hb.trans_eq (by ring)

/-- One time-integrated entry of the full Duhamel Hessian. -/
def heatDuhamelHessianEntryND {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (j k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ s in t₀..t, heatHessianEntryConvolutionND (t - s) (q s) j k x

/-- Every Duhamel Hessian entry is spatially continuous. -/
theorem continuous_heatDuhamelHessianEntryND
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) : Continuous (heatDuhamelHessianEntryND t₀ t q j k) := by
  let A := H * heatHessianEntryHolderMoment n r j k
  let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc t₀ t)
  have hgintI : IntervalIntegrable g volume t₀ t := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2))
        volume 0 (t - t₀) := intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2))
        volume t₀ t := by simpa using hcomp.symm
    exact hw.const_mul A
  have hgint : Integrable g μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hgintI
  have hmeas : ∀ x : Fin n → ℝ, AEStronglyMeasurable
      (fun s => heatHessianEntryConvolutionND (t - s) (q s) j k x) μ := by
    intro x
    exact (aestronglyMeasurable_heatHessianEntryConvolution_time
      (t := t) hq x j k).restrict
  have hbnd : ∀ x : Fin n → ℝ, ∀ᵐ s ∂μ,
      ‖heatHessianEntryConvolutionND (t - s) (q s) j k x‖ ≤ g s := by
    intro x
    rw [ae_restrict_iff' measurableSet_Ioc]
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
      rw [ae_iff, hs]
      exact measure_singleton t
    filter_upwards [htne] with s hst hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    rw [Real.norm_eq_abs]
    have hb := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
      hpos hr0.le hH x j k (q s).continuous.aestronglyMeasurable
      (hqb s) (hqholder s x)
    change |heatHessianEntryConvolutionND (t - s) (q s) j k x| ≤
      H * heatHessianEntryHolderMoment n r j k * (t - s) ^ (-1 + r / 2)
    exact hb.trans_eq (by ring)
  have hcont : ∀ᵐ s ∂μ, Continuous (fun x : Fin n → ℝ =>
      heatHessianEntryConvolutionND (t - s) (q s) j k x) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have htne : ∀ᵐ s : ℝ, s ≠ t := by
      have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
      rw [ae_iff, hs]
      exact measure_singleton t
    filter_upwards [htne] with s hst hs
    exact continuous_heatHessianEntryConvolutionND
      (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (q s).continuous
      (fun y => by simpa only [Real.norm_eq_abs] using hqb s y) j k
  have hc : Continuous (fun x : Fin n → ℝ =>
      ∫ s, heatHessianEntryConvolutionND (t - s) (q s) j k x ∂μ) :=
    continuous_of_dominated hmeas hbnd hgint hcont
  have heq : heatDuhamelHessianEntryND t₀ t q j k = fun x : Fin n → ℝ =>
      ∫ s, heatHessianEntryConvolutionND (t - s) (q s) j k x ∂μ := by
    funext x
    rw [heatDuhamelHessianEntryND, intervalIntegral.integral_of_le hT]
  rw [heq]
  exact hc

/-- The full Hessian entry bundled as a bounded continuous function. -/
def heatDuhamelHessianEntryNDbcf
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) : BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (heatDuhamelHessianEntryND t₀ t q j k)
    (continuous_heatDuhamelHessianEntryND hT hr0 hq hH hqb hqholder j k)
    (H * heatHessianEntryHolderMoment n r j k *
      ((t - t₀) ^ (r / 2) / (r / 2)))
    (fun x => by
      rw [Real.norm_eq_abs, heatDuhamelHessianEntryND]
      let G : ℝ → ℝ := fun s =>
        heatHessianEntryConvolutionND (t - s) (q s) j k x
      let A := H * heatHessianEntryHolderMoment n r j k
      let g : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
      have hGi := intervalIntegrable_heatHessianEntryConvolution
        hT hr0 hq hH hqb hqholder x j k
      have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc t₀ t → ‖G s‖ ≤ g s := by
        have htne : ∀ᵐ s : ℝ, s ≠ t := by
          have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
          rw [ae_iff, hs]
          exact measure_singleton t
        filter_upwards [htne] with s hst hs
        have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
        rw [Real.norm_eq_abs]
        have hb := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
          hpos hr0.le hH x j k (q s).continuous.aestronglyMeasurable
          (hqb s) (hqholder s x)
        change |G s| ≤ A * (t - s) ^ (-1 + r / 2)
        exact hb.trans_eq (by simp only [G, A, heatHessianEntryConvolutionND]; ring)
      have hgint : IntervalIntegrable g volume t₀ t := by
        have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2))
            volume 0 (t - t₀) := intervalIntegral.intervalIntegrable_rpow' (by linarith)
        have hcomp := hbase.comp_sub_left t
        have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2))
            volume t₀ t := by simpa using hcomp.symm
        exact hw.const_mul A
      have hm := intervalIntegral.norm_integral_le_of_norm_le hT hae hgint
      rw [Real.norm_eq_abs] at hm
      have hgval : (∫ s in t₀..t, g s) =
          A * ((t - t₀) ^ (r / 2) / (r / 2)) := by
        simp only [g]
        rw [intervalIntegral.integral_const_mul,
          integral_rpow_sub t₀ t (show (-1 : ℝ) < -1 + r / 2 by linarith)]
        congr 2 <;> ring
      rw [hgval] at hm
      simpa only [G, A] using hm)

@[simp] theorem heatDuhamelHessianEntryNDbcf_apply
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k x =
      heatDuhamelHessianEntryND t₀ t q j k x := rfl

/-- The Duhamel coordinate-gradient field. -/
def heatDuhamelGradientCoordND {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ s in t₀..t, ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (x - y) * (-(x - y) k / (2 * (t - s)))) * q s y

/-- Differentiating a Duhamel gradient coordinate produces the corresponding
full Hessian entry. -/
theorem hasDerivAt_heatDuhamelGradientCoordND_entry
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (j k : Fin n) :
    HasDerivAt (fun a => heatDuhamelGradientCoordND t₀ t q k
      (Function.update x j a))
      (heatDuhamelHessianEntryND t₀ t q j k x) (x j) := by
  let F : ℝ → ℝ → ℝ := fun a s => ∫ y : Fin n → ℝ,
    (heatKernelND (t - s) (Function.update x j a - y) *
      (-(Function.update x j a - y) k / (2 * (t - s)))) * q s y
  let F' : ℝ → ℝ → ℝ := fun a s =>
    heatHessianEntryConvolutionND (t - s) (q s) j k (Function.update x j a)
  let A := H * heatHessianEntryHolderMoment n r j k
  let bound : ℝ → ℝ := fun s => A * (t - s) ^ (-1 + r / 2)
  have hFmeas : ∀ᶠ a in 𝓝 (x j), AEStronglyMeasurable (F a)
      ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    filter_upwards with a
    exact (aestronglyMeasurable_gradient_heatKernelND_convolution_time
      (t := t) hq (Function.update x j a) k).restrict
  have hFint : IntervalIntegrable (F (x j)) volume t₀ t := by
    simpa only [F, Function.update_eq_self] using
      intervalIntegrable_gradient_heatKernelND_convolution hT hq hqb x k
  have hF'meas : AEStronglyMeasurable (F' (x j))
      ((volume : Measure ℝ).restrict (Ι t₀ t)) := by
    simpa only [F', Function.update_eq_self] using
      (aestronglyMeasurable_heatHessianEntryConvolution_time
        (t := t) hq x j k).restrict
  have hbint : IntervalIntegrable bound volume t₀ t := by
    have hbase : IntervalIntegrable (fun z : ℝ => z ^ (-1 + r / 2))
        volume 0 (t - t₀) := intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hcomp := hbase.comp_sub_left t
    have hw : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-1 + r / 2))
        volume t₀ t := by simpa using hcomp.symm
    exact hw.const_mul A
  have htne : ∀ᵐ s : ℝ, s ≠ t := by
    have hs : {a : ℝ | ¬a ≠ t} = {t} := by ext s; simp
    rw [ae_iff, hs]
    exact measure_singleton t
  have hbnd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), ‖F' a s‖ ≤ bound s := by
    filter_upwards [htne] with s hst hs a _
    rw [uIoc_of_le hT] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    rw [Real.norm_eq_abs]
    have hb := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
      hpos hr0.le hH (Function.update x j a) j k
      (q s).continuous.aestronglyMeasurable (hqb s)
      (hqholder s (Function.update x j a))
    change |F' a s| ≤ A * (t - s) ^ (-1 + r / 2)
    exact hb.trans_eq (by simp only [F', A, heatHessianEntryConvolutionND]; ring)
  have hdiff : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι t₀ t →
      ∀ a ∈ (Set.univ : Set ℝ), HasDerivAt (fun a => F a s) (F' a s) a := by
    filter_upwards [htne] with s hst hs a _
    rw [uIoc_of_le hT] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    have hupd : ∀ b : ℝ, Function.update (Function.update x j a) j b =
        Function.update x j b := by
      intro b
      funext i
      by_cases hij : i = j
      · subst i
        simp
      · simp [Function.update_of_ne hij]
    simpa only [F, F', heatHessianEntryConvolutionND, hupd,
      Function.update_self] using
        hasDerivAt_heatSemigroupND_coordGradient_entry hpos
          (Function.update x j a) j k (q s).continuous.aestronglyMeasurable (hqb s)
  have hout := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := t₀) (b := t) (F := F) (F' := F') (x₀ := x j)
    (s := Set.univ) Filter.univ_mem hFmeas hFint hF'meas hbnd hbint hdiff
  simpa only [heatDuhamelGradientCoordND, heatDuhamelHessianEntryND, F, F',
    Function.update_eq_self] using hout.2

/-- For distinct coordinates, the bundled mixed entry is the actual iterated
coordinate derivative of the Duhamel potential. -/
theorem hasDerivAt_partial_heatDuhamelND_coord_offdiag
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) {j k : Fin n} (hjk : j ≠ k) :
    HasDerivAt
      (fun a => deriv (fun b => ∫ s in t₀..t,
        heatSemigroupND (t - s) (q s)
          (Function.update (Function.update x j a) k b))
        ((Function.update x j a) k))
      (heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k x)
      (x j) := by
  let P : (Fin n → ℝ) → ℝ := fun z => deriv (fun b => ∫ s in t₀..t,
    heatSemigroupND (t - s) (q s) (Function.update z k b)) (z k)
  have hP : P = heatDuhamelGradientCoordND t₀ t q k := by
    funext z
    have hd := hasDerivAt_heatDuhamelND_coord hT hq hqb z k
    simpa only [P, heatDuhamelGradientCoordND] using hd.deriv
  change HasDerivAt (fun a => P (Function.update x j a)) _ (x j)
  rw [hP]
  simpa only [heatDuhamelHessianEntryNDbcf_apply] using
    hasDerivAt_heatDuhamelGradientCoordND_entry
      hT hr0 hq hH hqb hqholder x j k

end AnalyticPDE
end RicciFlow
