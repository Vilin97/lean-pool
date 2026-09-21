/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatHessianSemigroup

/-!
# Spatial Holder control of the Euclidean Duhamel Hessian

This module moves the recent-time cancellation and old-time factorization
bounds under the Duhamel integral.  The integral is first reflected to heat
time `u = t-s`, where the standard split at a positive scale is transparent.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Reflection of a full Duhamel Hessian entry to heat time `u = t-s`. -/
theorem heatDuhamelHessianEntryND_eq_comp_sub
    {n : ℕ} (t₀ t : ℝ)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (j k : Fin n) (x : Fin n → ℝ) :
    heatDuhamelHessianEntryND t₀ t q j k x =
      ∫ u in (0 : ℝ)..(t - t₀),
        heatHessianEntryConvolutionND u (q (t - u)) j k x := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := t₀) (b := t)
    (fun u ↦ heatHessianEntryConvolutionND u (q (t - u)) j k x) t
  simpa only [heatDuhamelHessianEntryND, sub_sub_cancel, sub_self] using h

/-- The cancellation envelope used on the recent part of the heat-time
integral. -/
def heatDuhamelHessianRecentEnvelope
    (n : ℕ) (r H : ℝ) (j k : Fin n) (u : ℝ) : ℝ :=
  2 * (H * u ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k)

/-- The factorized Lipschitz envelope used on the old part of the heat-time
integral. -/
def heatDuhamelHessianOldEnvelope
    (n : ℕ) (r H d : ℝ) (j k : Fin n) (u : ℝ) : ℝ :=
  (n : ℝ) *
    ((H * (u / 2) ^ (-1 + r / 2) *
      heatHessianEntryHolderMoment n r j k) /
        Real.sqrt (π * (u / 2))) * d

/-- Time-independent coefficient in the normalized old-time envelope. -/
def heatDuhamelHessianOldConstant
    (n : ℕ) (r H : ℝ) (j k : Fin n) : ℝ :=
  (n : ℝ) *
    (H * (1 / 2 : ℝ) ^ (-1 + r / 2) *
      heatHessianEntryHolderMoment n r j k) /
        Real.sqrt (π / 2)

lemma heatDuhamelHessianOldConstant_nonneg
    (n : ℕ) (r : ℝ) {H : ℝ} (hH : 0 ≤ H) (j k : Fin n) :
    0 ≤ heatDuhamelHessianOldConstant n r H j k := by
  unfold heatDuhamelHessianOldConstant
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg
        (mul_nonneg hH (Real.rpow_nonneg (by norm_num) _))
        (heatHessianEntryHolderMoment_nonneg n r j k))
  · exact Real.sqrt_nonneg _

lemma sq_rpow_half_eq_rpow {d r : ℝ} (hd : 0 ≤ d) :
    (d ^ 2) ^ (r / 2) = d ^ r := by
  calc
    (d ^ 2) ^ (r / 2) = (d ^ (2 : ℝ)) ^ (r / 2) := by
      exact congrArg (fun z : ℝ ↦ z ^ (r / 2))
        (Real.rpow_natCast d 2).symm
    _ = d ^ ((2 : ℝ) * (r / 2)) :=
      (Real.rpow_mul hd 2 (r / 2)).symm
    _ = d ^ r := by congr 1; ring

lemma mul_sq_rpow_eq_rpow {d r : ℝ} (hd : 0 < d) :
    d * (d ^ 2) ^ (-1 / 2 + r / 2) = d ^ r := by
  calc
    d * (d ^ 2) ^ (-1 / 2 + r / 2) =
        d ^ (1 : ℝ) * (d ^ (2 : ℝ)) ^ (-1 / 2 + r / 2) := by
      rw [Real.rpow_one]
      exact congrArg (fun z : ℝ ↦ d * z ^ (-1 / 2 + r / 2))
        (Real.rpow_natCast d 2).symm
    _ = d ^ (1 : ℝ) * d ^ ((2 : ℝ) * (-1 / 2 + r / 2)) := by
      rw [Real.rpow_mul hd.le]
    _ = d ^ ((1 : ℝ) + (2 : ℝ) * (-1 / 2 + r / 2)) :=
      (Real.rpow_add hd 1 (2 * (-1 / 2 + r / 2))).symm
    _ = d ^ r := by congr 1; ring

/-- On positive heat times, the old-time envelope has the homogeneous form
`K u^(-3/2+r/2) d`. -/
theorem heatDuhamelHessianOldEnvelope_eq
    {n : ℕ} {r H d u : ℝ} (hu : 0 < u) (j k : Fin n) :
    heatDuhamelHessianOldEnvelope n r H d j k u =
      heatDuhamelHessianOldConstant n r H j k *
        u ^ (-3 / 2 + r / 2) * d := by
  unfold heatDuhamelHessianOldEnvelope heatDuhamelHessianOldConstant
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hpi2 : (0 : ℝ) ≤ π / 2 := by positivity
  rw [show u / 2 = u * (1 / 2 : ℝ) by ring,
    Real.mul_rpow hu.le hhalf,
    show π * (u * (1 / 2 : ℝ)) = (π / 2) * u by ring,
    Real.sqrt_mul hpi2, Real.sqrt_eq_rpow]
  have hs : Real.sqrt (π / 2) ≠ 0 := by positivity
  have huPow : u ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hu _).ne'
  field_simp
  rw [Real.sqrt_eq_rpow]
  have hpow : u ^ ((-2 + r) / 2) =
      u ^ (1 / 2 : ℝ) * u ^ ((-3 + r) / 2) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  rw [hpow]
  ring

lemma intervalIntegrable_heatDuhamelHessianRecentEnvelope
    {n : ℕ} {r H δ : ℝ} (hr0 : 0 < r)
    (j k : Fin n) :
    IntervalIntegrable
      (heatDuhamelHessianRecentEnvelope n r H j k) volume 0 δ := by
  have hbase : IntervalIntegrable (fun u : ℝ ↦ u ^ (-1 + r / 2))
      volume 0 δ :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hi := (hbase.const_mul H).mul_const
    (2 * heatHessianEntryHolderMoment n r j k)
  have heq : heatDuhamelHessianRecentEnvelope n r H j k =
      fun u ↦ H * u ^ (-1 + r / 2) *
        (2 * heatHessianEntryHolderMoment n r j k) := by
    funext u
    unfold heatDuhamelHessianRecentEnvelope
    ring
  rw [heq]
  exact hi

/-- Exact value of the recent cancellation envelope. -/
theorem integral_heatDuhamelHessianRecentEnvelope
    {n : ℕ} {r H δ : ℝ} (hr0 : 0 < r)
    (j k : Fin n) :
    (∫ u in (0 : ℝ)..δ,
      heatDuhamelHessianRecentEnvelope n r H j k u) =
      2 * (H * heatHessianEntryHolderMoment n r j k *
        (δ ^ (r / 2) / (r / 2))) := by
  have heq : heatDuhamelHessianRecentEnvelope n r H j k =
      fun u ↦ (2 * H * heatHessianEntryHolderMoment n r j k) *
        u ^ (-1 + r / 2) := by
    funext u
    unfold heatDuhamelHessianRecentEnvelope
    ring
  rw [heq, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (show (-1 : ℝ) < -1 + r / 2 by linarith)),
    Real.zero_rpow (show -1 + r / 2 + 1 ≠ 0 by linarith)]
  ring_nf

/-- On an interval bounded away from heat time zero, the old-time envelope
is interval-integrable. -/
lemma intervalIntegrable_heatDuhamelHessianOldEnvelope
    {n : ℕ} {r H d δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T)
    (j k : Fin n) :
    IntervalIntegrable
      (heatDuhamelHessianOldEnvelope n r H d j k) volume δ T := by
  apply ContinuousOn.intervalIntegrable
  unfold heatDuhamelHessianOldEnvelope
  have hbase : ContinuousOn (fun u : ℝ ↦ u / 2) (Set.uIcc δ T) :=
    (continuous_id.div_const 2).continuousOn
  have hpow : ContinuousOn (fun u : ℝ ↦ (u / 2) ^ (-1 + r / 2))
      (Set.uIcc δ T) := by
    apply hbase.rpow_const
    intro u hu
    left
    have hu : δ ≤ u := by
      rw [uIcc_of_le hδT] at hu
      exact hu.1
    exact ne_of_gt (div_pos (hδ.trans_le hu) (by norm_num))
  have hsqrt : ContinuousOn (fun u : ℝ ↦ Real.sqrt (π * (u / 2)))
      (Set.uIcc δ T) :=
    Real.continuous_sqrt.comp_continuousOn
      (continuous_const.continuousOn.mul hbase)
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact continuous_const.continuousOn
    · apply ContinuousOn.div
      · exact (continuous_const.continuousOn.mul hpow).mul
          continuous_const.continuousOn
      · exact hsqrt
      · intro u hu
        have hu' : δ ≤ u := by
          rw [uIcc_of_le hδT] at hu
          exact hu.1
        have hu0 : 0 < u := hδ.trans_le hu'
        have : 0 < π * (u / 2) :=
          mul_pos Real.pi_pos (div_pos hu0 (by norm_num))
        exact (Real.sqrt_pos.mpr this).ne'
  · exact continuous_const.continuousOn

/-- Exact integral of the normalized old-time envelope on an interval away
from zero. -/
theorem integral_heatDuhamelHessianOldEnvelope
    {n : ℕ} {r H d δ T : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T)
    (hr1 : r ≠ 1) (j k : Fin n) :
    (∫ u in δ..T, heatDuhamelHessianOldEnvelope n r H d j k u) =
      heatDuhamelHessianOldConstant n r H j k * d *
        ((T ^ (-1 / 2 + r / 2) - δ ^ (-1 / 2 + r / 2)) /
          (-1 / 2 + r / 2)) := by
  have hpoint : (∫ u in δ..T,
      heatDuhamelHessianOldEnvelope n r H d j k u) =
      ∫ u in δ..T, heatDuhamelHessianOldConstant n r H j k *
        u ^ (-3 / 2 + r / 2) * d := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hδT] at hu
    have hu0 : 0 < u := hδ.trans_le hu.1
    exact heatDuhamelHessianOldEnvelope_eq hu0 j k
  rw [hpoint]
  have hzero : (0 : ℝ) ∉ Set.uIcc δ T := by
    rw [uIcc_of_le hδT]
    intro h
    exact (not_lt_of_ge h.1) hδ
  rw [show (fun u : ℝ ↦ heatDuhamelHessianOldConstant n r H j k *
        u ^ (-3 / 2 + r / 2) * d) =
      fun u ↦ (heatDuhamelHessianOldConstant n r H j k * d) *
        u ^ (-3 / 2 + r / 2) by
      funext u; ring,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by
      intro he
      apply hr1
      linarith, hzero⟩)]
  congr 1
  ring_nf

/-- **Duhamel Hessian split estimate.**  For every positive split scale
`δ ≤ t-t₀`, the spatial difference of one full Hessian entry is bounded by
the recent cancellation envelope on `[0,δ]` plus the factorized old-time
Lipschitz envelope on `[δ,t-t₀]`. -/
theorem abs_heatDuhamelHessianEntryND_sub_le_split
    {n : ℕ} {t₀ t r δ : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    (hδ : 0 < δ) (hδT : δ ≤ t - t₀)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
      (∫ u in (0 : ℝ)..δ,
        heatDuhamelHessianRecentEnvelope n r H j k u) +
      ∫ u in δ..(t - t₀),
        heatDuhamelHessianOldEnvelope n r H ‖x - y‖ j k u := by
  let F : ℝ → ℝ := fun u ↦
    heatHessianEntryConvolutionND u (q (t - u)) j k x -
      heatHessianEntryConvolutionND u (q (t - u)) j k y
  have hx := intervalIntegrable_heatHessianEntryConvolution
    hT hr0 hq hH hqb hqholder x j k
  have hy := intervalIntegrable_heatHessianEntryConvolution
    hT hr0 hq hH hqb hqholder y j k
  have hxi : IntervalIntegrable (fun u ↦
      heatHessianEntryConvolutionND u (q (t - u)) j k x)
      volume 0 (t - t₀) := by
    have hcomp := hx.comp_sub_left t
    simpa only [sub_sub_cancel, sub_self] using hcomp.symm
  have hyi : IntervalIntegrable (fun u ↦
      heatHessianEntryConvolutionND u (q (t - u)) j k y)
      volume 0 (t - t₀) := by
    have hcomp := hy.comp_sub_left t
    simpa only [sub_sub_cancel, sub_self] using hcomp.symm
  have hFi : IntervalIntegrable F volume 0 (t - t₀) := by
    exact hxi.sub hyi
  have hsub0δ : Set.uIcc (0 : ℝ) δ ⊆ Set.uIcc (0 : ℝ) (t - t₀) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ t - t₀)]; exact ⟨by linarith, hδT⟩)
  have hsubδT : Set.uIcc δ (t - t₀) ⊆ Set.uIcc (0 : ℝ) (t - t₀) :=
    Set.uIcc_subset_uIcc
      (by rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ t - t₀)]; exact ⟨hδ.le, hδT⟩)
      Set.right_mem_uIcc
  have hFi0δ := hFi.mono_set hsub0δ
  have hFiδT := hFi.mono_set hsubδT
  have hreI := intervalIntegrable_heatDuhamelHessianRecentEnvelope
    (H := H) (δ := δ) hr0 j k
  have holdI := intervalIntegrable_heatDuhamelHessianOldEnvelope
    (r := r) (H := H) (d := ‖x - y‖) hδ hδT j k
  rw [heatDuhamelHessianEntryND_eq_comp_sub,
    heatDuhamelHessianEntryND_eq_comp_sub,
    ← intervalIntegral.integral_sub hxi hyi]
  change |∫ u in (0 : ℝ)..(t - t₀), F u| ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hFi0δ hFiδT]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hδ.le
    · filter_upwards with u hmem
      rw [Real.norm_eq_abs]
      have hu0 : 0 < u := hmem.1
      exact abs_heatHessianEntryConvolutionND_sub_le_recent
        hu0 hr0.le (q (t - u)) hH (hqholder (t - u)) j k x y
    · exact hreI
  · rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hδT
    · filter_upwards with u hmem
      rw [Real.norm_eq_abs]
      have hu0 : 0 < u := hδ.trans hmem.1
      exact abs_heatHessianEntryConvolutionND_sub_le_old
        hu0 hr0.le (q (t - u)) hH (hqholder (t - u)) j k x y
    · exact holdI

/-- Evaluated form of the Duhamel Hessian split estimate. -/
theorem abs_heatDuhamelHessianEntryND_sub_le_split_explicit
    {n : ℕ} {t₀ t r δ : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    (hr1 : r ≠ 1) (hδ : 0 < δ) (hδT : δ ≤ t - t₀)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
      2 * (H * heatHessianEntryHolderMoment n r j k *
        (δ ^ (r / 2) / (r / 2))) +
      heatDuhamelHessianOldConstant n r H j k * ‖x - y‖ *
        (((t - t₀) ^ (-1 / 2 + r / 2) -
            δ ^ (-1 / 2 + r / 2)) / (-1 / 2 + r / 2)) := by
  have hmain := abs_heatDuhamelHessianEntryND_sub_le_split
    hT hr0 hδ hδT hq hH hqb hqholder j k x y
  rw [integral_heatDuhamelHessianRecentEnvelope hr0 j k,
    integral_heatDuhamelHessianOldEnvelope hδ hδT hr1 j k] at hmain
  exact hmain

/-- Entrywise spatial Holder constant produced by the heat-time split. -/
def heatDuhamelHessianSpatialHolderEntryConstant
    (n : ℕ) (r H : ℝ) (j k : Fin n) : ℝ :=
  2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) +
    heatDuhamelHessianOldConstant n r H j k / ((1 - r) / 2)

lemma heatDuhamelHessianSpatialHolderEntryConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH : 0 ≤ H) (j k : Fin n) :
    0 ≤ heatDuhamelHessianSpatialHolderEntryConstant n r H j k := by
  unfold heatDuhamelHessianSpatialHolderEntryConstant
  exact add_nonneg
    (mul_nonneg (by norm_num) (div_nonneg
      (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
      (by linarith)))
    (div_nonneg (heatDuhamelHessianOldConstant_nonneg n r hH j k)
      (by linarith))

/-- In the small-distance regime `‖x-y‖² ≤ t-t₀`, the evaluated split
already gives the desired `r`-Holder modulus. -/
theorem abs_heatDuhamelHessianEntryND_sub_le_holder_of_sq_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ)
    (hd : 0 < ‖x - y‖) (hsmall : ‖x - y‖ ^ 2 ≤ t - t₀) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
      heatDuhamelHessianSpatialHolderEntryConstant n r H j k *
        ‖x - y‖ ^ r := by
  let d : ℝ := ‖x - y‖
  let e : ℝ := -1 / 2 + r / 2
  have hmain := abs_heatDuhamelHessianEntryND_sub_le_split_explicit
    hT hr0 (ne_of_lt hr1) (sq_pos_of_pos hd) hsmall
      hq hH hqb hqholder j k x y
  change _ ≤ heatDuhamelHessianSpatialHolderEntryConstant n r H j k * d ^ r
  have hmain' :
      |heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ t q j k y| ≤
        2 * (H * heatHessianEntryHolderMoment n r j k *
          ((d ^ 2) ^ (r / 2) / (r / 2))) +
        heatDuhamelHessianOldConstant n r H j k * d *
          (((t - t₀) ^ e - (d ^ 2) ^ e) / e) := by
    simpa only [d, e] using hmain
  have he : e < 0 := by dsimp only [e]; linarith
  have hQ :
      (((t - t₀) ^ e - (d ^ 2) ^ e) / e) ≤
        (d ^ 2) ^ e / (-e) := by
    rw [show ((t - t₀) ^ e - (d ^ 2) ^ e) / e =
        ((d ^ 2) ^ e - (t - t₀) ^ e) / (-e) by ring_nf]
    apply div_le_div_of_nonneg_right
    · exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr hT) e)
    · exact (neg_pos.mpr he).le
  have hre :
      2 * (H * heatHessianEntryHolderMoment n r j k *
        ((d ^ 2) ^ (r / 2) / (r / 2))) =
      (2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2))) *
        d ^ r := by
    rw [sq_rpow_half_eq_rpow hd.le]
    ring
  have hold :
      heatDuhamelHessianOldConstant n r H j k * d *
          (((t - t₀) ^ e - (d ^ 2) ^ e) / e) ≤
        (heatDuhamelHessianOldConstant n r H j k / ((1 - r) / 2)) *
          d ^ r := by
    calc
      _ ≤ heatDuhamelHessianOldConstant n r H j k * d *
          ((d ^ 2) ^ e / (-e)) := by
        gcongr
        exact mul_nonneg
          (heatDuhamelHessianOldConstant_nonneg n r hH j k) hd.le
      _ = heatDuhamelHessianOldConstant n r H j k *
          (d * (d ^ 2) ^ e) / (-e) := by ring
      _ = heatDuhamelHessianOldConstant n r H j k * d ^ r / (-e) := by
        rw [show e = -1 / 2 + r / 2 by rfl,
          mul_sq_rpow_eq_rpow hd]
      _ = (heatDuhamelHessianOldConstant n r H j k / ((1 - r) / 2)) *
          d ^ r := by
        dsimp only [e]
        ring
  refine hmain'.trans ?_
  rw [hre]
  change _ ≤
    (2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) +
      heatDuhamelHessianOldConstant n r H j k / ((1 - r) / 2)) * d ^ r
  calc
    _ ≤ (2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2))) *
        d ^ r +
      (heatDuhamelHessianOldConstant n r H j k / ((1 - r) / 2)) *
        d ^ r := add_le_add le_rfl hold
    _ = _ := by ring

/-- In the complementary large-distance regime, the global Duhamel Hessian
bound is already controlled by the same Holder constant. -/
theorem abs_heatDuhamelHessianEntryND_sub_le_holder_of_le_sq
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ)
    (hlarge : t - t₀ ≤ ‖x - y‖ ^ 2) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
      heatDuhamelHessianSpatialHolderEntryConstant n r H j k *
        ‖x - y‖ ^ r := by
  let E := heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k
  let A := H * heatHessianEntryHolderMoment n r j k *
    ((t - t₀) ^ (r / 2) / (r / 2))
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
      (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _)
        (by linarith))
  have hEnorm : ‖E‖ ≤ A := by
    dsimp only [E, A]
    unfold heatDuhamelHessianEntryNDbcf
    apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    exact hA
  have hx : |heatDuhamelHessianEntryND t₀ t q j k x| ≤ A := by
    rw [← Real.norm_eq_abs,
      ← heatDuhamelHessianEntryNDbcf_apply hT hr0 hq hH hqb hqholder]
    exact (E.norm_coe_le_norm x).trans hEnorm
  have hy : |heatDuhamelHessianEntryND t₀ t q j k y| ≤ A := by
    rw [← Real.norm_eq_abs,
      ← heatDuhamelHessianEntryNDbcf_apply hT hr0 hq hH hqb hqholder]
    exact (E.norm_coe_le_norm y).trans hEnorm
  have hp : (t - t₀) ^ (r / 2) ≤ ‖x - y‖ ^ r := by
    refine (Real.rpow_le_rpow (sub_nonneg.mpr hT) hlarge (by linarith)).trans_eq ?_
    exact sq_rpow_half_eq_rpow (norm_nonneg (x - y))
  have hrecentCoeff : 0 ≤
      2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) := by
    exact mul_nonneg (by norm_num)
      (div_nonneg
        (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
        (by linarith))
  calc
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
        |heatDuhamelHessianEntryND t₀ t q j k x| +
          |heatDuhamelHessianEntryND t₀ t q j k y| := abs_sub _ _
    _ ≤ A + A := add_le_add hx hy
    _ = 2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) *
        (t - t₀) ^ (r / 2) := by dsimp only [A]; ring
    _ ≤ 2 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) *
        ‖x - y‖ ^ r := mul_le_mul_of_nonneg_left hp hrecentCoeff
    _ ≤ heatDuhamelHessianSpatialHolderEntryConstant n r H j k *
        ‖x - y‖ ^ r := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      unfold heatDuhamelHessianSpatialHolderEntryConstant
      exact le_add_of_nonneg_right
        (div_nonneg (heatDuhamelHessianOldConstant_nonneg n r hH j k)
          (by linarith))

/-- **Spatial Holder estimate for every Duhamel Hessian entry.** -/
theorem abs_heatDuhamelHessianEntryND_sub_le_holder
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x y : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ t q j k y| ≤
      heatDuhamelHessianSpatialHolderEntryConstant n r H j k *
        ‖x - y‖ ^ r := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero, norm_zero]
    exact mul_nonneg
      (heatDuhamelHessianSpatialHolderEntryConstant_nonneg n hr0 hr1 hH j k)
      (Real.rpow_nonneg le_rfl r)
  · have hd : 0 < ‖x - y‖ := (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
    rcases le_total (‖x - y‖ ^ 2) (t - t₀) with hsmall | hlarge
    · exact abs_heatDuhamelHessianEntryND_sub_le_holder_of_sq_le
        hT hr0 hr1 hq hH hqb hqholder j k x y hd hsmall
    · exact abs_heatDuhamelHessianEntryND_sub_le_holder_of_le_sq
        hT hr0 hr1 hq hH hqb hqholder j k x y hlarge

/-- Full operator-norm spatial Holder constant for the Duhamel Hessian. -/
def heatDuhamelHessianSpatialHolderConstant
    (n : ℕ) (r H : ℝ) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n,
    heatDuhamelHessianSpatialHolderEntryConstant n r H j k

lemma heatDuhamelHessianSpatialHolderConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH : 0 ≤ H) :
    0 ≤ heatDuhamelHessianSpatialHolderConstant n r H := by
  unfold heatDuhamelHessianSpatialHolderConstant
  exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
    heatDuhamelHessianSpatialHolderEntryConstant_nonneg n hr0 hr1 hH j k

section DuhamelOperatorHolder

local instance duhamelHolderCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance duhamelHolderCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- **The genuine full Frechet Hessian of the Duhamel potential is spatially
`r`-Holder, uniformly in the final time.** -/
theorem norm_heatDuhamelHessianCLM_sub_le_holder
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x y : Fin n → ℝ) :
    ‖heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x -
        heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder y‖ ≤
      heatDuhamelHessianSpatialHolderConstant n r H * ‖x - y‖ ^ r := by
  have heq : heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder x -
      heatDuhamelHessianCLM hT hr0 hq hH hqb hqholder y =
      coordinateHessianCLM (fun j k ↦
        heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ t q j k y) := by
    ext v w
    simp only [heatDuhamelHessianCLM_apply, coordinateHessianCLM_apply,
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
  calc
    (∑ j : Fin n, ∑ k : Fin n,
        |heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ t q j k y|) ≤
        ∑ j : Fin n, ∑ k : Fin n,
          heatDuhamelHessianSpatialHolderEntryConstant n r H j k *
            ‖x - y‖ ^ r := by
      gcongr with j k
      exact abs_heatDuhamelHessianEntryND_sub_le_holder
        hT hr0 hr1 hq hH hqb hqholder j k x y
    _ = heatDuhamelHessianSpatialHolderConstant n r H * ‖x - y‖ ^ r := by
      unfold heatDuhamelHessianSpatialHolderConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]

end DuhamelOperatorHolder

end AnalyticPDE
end RicciFlow
