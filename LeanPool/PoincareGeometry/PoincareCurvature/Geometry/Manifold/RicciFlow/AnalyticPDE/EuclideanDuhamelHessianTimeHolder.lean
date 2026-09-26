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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessianHolder
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatParabolicHolder

/-!
# Temporal Holder control of the Euclidean Duhamel Hessian

The final-time increment is split at the parabolic scale `t-s`.  Close to
the moving endpoint, heat-kernel cancellation is integrable.  Away from the
endpoint, the Hessian semigroup factorization turns the time increment into
the approximate-identity modulus of an already Lipschitz Hessian entry.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- The exact first-moment modulus in the heat approximate identity. -/
def heatHessianTimeShiftModulus (δ : ℝ) : ℝ :=
  (4 * π * δ) ^ (-(1 : ℝ) / 2) * (4 * δ)

lemma heatHessianTimeShiftModulus_nonneg {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ heatHessianTimeShiftModulus δ := by
  unfold heatHessianTimeShiftModulus
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)

/-- On a heat-time interval comparable with the final-time increment, the
difference of two Hessian kernels is bounded by the cancellation envelope. -/
theorem abs_heatHessianEntryConvolutionND_time_shift_sub_le_recent
    {n : ℕ} {δ u r : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatHessianEntryConvolutionND (δ + u) f j k x -
        heatHessianEntryConvolutionND u f j k x| ≤
      heatDuhamelHessianRecentEnvelope n r H j k u := by
  have hdu : 0 < δ + u := add_pos_of_nonneg_of_pos hδ hu
  have hleft := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    hdu hr0 hH x j k f.continuous.aestronglyMeasurable
      (fun y ↦ f.norm_coe_le_norm y) (hholder x)
  have hright := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    hu hr0 hH x j k f.continuous.aestronglyMeasurable
      (fun y ↦ f.norm_coe_le_norm y) (hholder x)
  have he : -1 + r / 2 ≤ 0 := by linarith
  have hpow : (δ + u) ^ (-1 + r / 2) ≤ u ^ (-1 + r / 2) :=
    Real.rpow_le_rpow_of_nonpos hu (le_add_of_nonneg_left hδ) he
  calc
    |heatHessianEntryConvolutionND (δ + u) f j k x -
        heatHessianEntryConvolutionND u f j k x| ≤
        |heatHessianEntryConvolutionND (δ + u) f j k x| +
          |heatHessianEntryConvolutionND u f j k x| := abs_sub _ _
    _ ≤ (H * (δ + u) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) +
        (H * u ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) := add_le_add hleft hright
    _ ≤ 2 * (H * u ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) := by
      have hc : 0 ≤ H * heatHessianEntryHolderMoment n r j k :=
        mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k)
      nlinarith [mul_le_mul_of_nonneg_left hpow hc]
    _ = heatDuhamelHessianRecentEnvelope n r H j k u := by
      unfold heatDuhamelHessianRecentEnvelope
      ring

/-- Away from heat time zero, semigroup factorization turns a final-time
shift into the heat approximate-identity modulus of a Lipschitz Hessian. -/
theorem abs_heatHessianEntryConvolutionND_time_shift_sub_le_old
    {n : ℕ} {δ u r : ℝ} (hδ : 0 < δ) (hu : 0 < u)
    (hr0 : 0 ≤ r)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hholder : ∀ x y, |f y - f x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatHessianEntryConvolutionND (δ + u) f j k x -
        heatHessianEntryConvolutionND u f j k x| ≤
      heatDuhamelHessianOldEnvelope n r H
        ((n : ℝ) * heatHessianTimeShiftModulus δ) j k u := by
  let w := heatHessianEntryConvolutionNDbcf_of_coordHolder
    hu hr0 f hH hholder j k
  let L := heatDuhamelHessianOldConstant n r H j k *
    u ^ (-3 / 2 + r / 2)
  have hL : 0 ≤ L := mul_nonneg
    (heatDuhamelHessianOldConstant_nonneg n r hH j k)
    (Real.rpow_nonneg hu.le _)
  have hfactor : heatHessianEntryConvolutionND (δ + u) f j k x =
      heatSemigroupND δ w x := by
    simpa only [w] using
      heatHessianEntryConvolutionND_add_eq_heatSemigroupND
        hδ hu hr0 f hH hholder j k x
  have hwbound : ∀ y, ‖w y‖ ≤
      H * u ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
    intro y
    exact (w.norm_coe_le_norm y).trans
      (norm_heatHessianEntryConvolutionNDbcf_of_coordHolder_le
        hu hr0 f hH hholder j k)
  have hwlip : ∀ a b : Fin n → ℝ, |w a - w b| ≤ L * ‖a - b‖ := by
    intro a b
    have hmain := abs_heatHessianEntryConvolutionND_sub_le_old
      hu hr0 f hH hholder j k a b
    change |heatHessianEntryConvolutionND u f j k a -
      heatHessianEntryConvolutionND u f j k b| ≤ _
    change _ ≤ heatDuhamelHessianOldEnvelope n r H ‖a - b‖ j k u at hmain
    rw [heatDuhamelHessianOldEnvelope_eq hu j k] at hmain
    simpa only [L] using hmain
  rw [hfactor, ← heatHessianEntryConvolutionNDbcf_of_coordHolder_apply
    hu hr0 f hH hholder]
  have hmain := abs_heatSemigroupND_sub_self_le_of_lipschitz
    hδ hL w.continuous.aestronglyMeasurable hwbound hwlip x
  refine hmain.trans_eq ?_
  rw [heatDuhamelHessianOldEnvelope_eq hu j k]
  simp only [L, heatHessianTimeShiftModulus]
  ring

/-- The defining cancellation majorant is also a norm bound for a bundled
Duhamel Hessian entry. -/
theorem norm_heatDuhamelHessianEntryNDbcf_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) :
    ‖heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k‖ ≤
      H * heatHessianEntryHolderMoment n r j k *
        ((t - t₀) ^ (r / 2) / (r / 2)) := by
  unfold heatDuhamelHessianEntryNDbcf
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  exact mul_nonneg
    (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
    (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _)
      (by linarith))

/-- Pointwise form of the global cancellation bound for a Duhamel Hessian
entry. -/
theorem abs_heatDuhamelHessianEntryND_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x| ≤
      H * heatHessianEntryHolderMoment n r j k *
        ((t - t₀) ^ (r / 2) / (r / 2)) := by
  rw [← Real.norm_eq_abs,
    ← heatDuhamelHessianEntryNDbcf_apply hT hr0 hq hH hqb hqholder]
  exact
    (BoundedContinuousFunction.norm_coe_le_norm
      (heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k) x).trans
      (norm_heatDuhamelHessianEntryNDbcf_le
        hT hr0 hq hH hqb hqholder j k)

/-- Raw small-increment split.  The two endpoint pieces use cancellation;
the old piece uses semigroup factorization and a heat first moment. -/
theorem abs_heatDuhamelHessianEntryND_time_sub_le_split
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (hst : s < t)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hsmall : t - s ≤ s - t₀)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      2 * (∫ u in (0 : ℝ)..(t - s),
        heatDuhamelHessianRecentEnvelope n r H j k u) +
      ∫ u in (t - s)..(s - t₀),
        heatDuhamelHessianOldEnvelope n r H
          ((n : ℝ) * heatHessianTimeShiftModulus (t - s)) j k u := by
  let δ : ℝ := t - s
  let c : ℝ := s - δ
  let Ft : ℝ → ℝ := fun a ↦
    heatHessianEntryConvolutionND (t - a) (q a) j k x
  let Fs : ℝ → ℝ := fun a ↦
    heatHessianEntryConvolutionND (s - a) (q a) j k x
  let R : ℝ → ℝ := heatDuhamelHessianRecentEnvelope n r H j k
  let O : ℝ → ℝ := heatDuhamelHessianOldEnvelope n r H
    ((n : ℝ) * heatHessianTimeShiftModulus δ) j k
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hc0 : t₀ ≤ c := by dsimp only [c, δ]; linarith
  have hcs : c ≤ s := by dsimp only [c]; linarith
  have hstle : s ≤ t := hst.le
  have hFt : IntervalIntegrable Ft volume t₀ t := by
    simpa only [Ft] using intervalIntegrable_heatHessianEntryConvolution
      (hs0.trans hstle) hr0 hq hH hqb hqholder x j k
  have hFs : IntervalIntegrable Fs volume t₀ s := by
    simpa only [Fs] using intervalIntegrable_heatHessianEntryConvolution
      hs0 hr0 hq hH hqb hqholder x j k
  have hFt0s : IntervalIntegrable Ft volume t₀ s :=
    hFt.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by
      rw [uIcc_of_le (hs0.trans hstle)]
      exact ⟨hs0, hstle⟩))
  have hFst : IntervalIntegrable Ft volume s t :=
    hFt.mono_set (Set.uIcc_subset_uIcc (by
      rw [uIcc_of_le (hs0.trans hstle)]
      exact ⟨hs0, hstle⟩) Set.right_mem_uIcc)
  have hD : IntervalIntegrable (fun a ↦ Ft a - Fs a) volume t₀ s :=
    hFt0s.sub hFs
  have hD0c : IntervalIntegrable (fun a ↦ Ft a - Fs a) volume t₀ c :=
    hD.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc (by
      rw [uIcc_of_le hs0]
      exact ⟨hc0, hcs⟩))
  have hDcs : IntervalIntegrable (fun a ↦ Ft a - Fs a) volume c s :=
    hD.mono_set (Set.uIcc_subset_uIcc (by
      rw [uIcc_of_le hs0]
      exact ⟨hc0, hcs⟩) Set.right_mem_uIcc)
  have hRint : IntervalIntegrable R volume 0 δ := by
    simpa only [R] using intervalIntegrable_heatDuhamelHessianRecentEnvelope
      (H := H) (δ := δ) hr0 j k
  have hRcompT : IntervalIntegrable (fun a ↦ R (t - a)) volume s t := by
    have h := hRint.comp_sub_left t
    simpa only [sub_self, sub_zero, δ, sub_sub_cancel] using h.symm
  have hRcompS : IntervalIntegrable (fun a ↦ R (s - a)) volume c s := by
    have h := hRint.comp_sub_left s
    simpa only [sub_self, sub_zero, c, δ, sub_sub_cancel] using h.symm
  have hOint : IntervalIntegrable O volume δ (s - t₀) := by
    simpa only [O] using intervalIntegrable_heatDuhamelHessianOldEnvelope
      (r := r) (H := H)
      (d := (n : ℝ) * heatHessianTimeShiftModulus δ)
      hδ (by simpa only [δ] using hsmall) j k
  have hOcomp : IntervalIntegrable (fun a ↦ O (s - a)) volume t₀ c := by
    have h := hOint.comp_sub_left s
    simpa only [c, δ, sub_sub_cancel] using h.symm
  have hre : |∫ a in s..t, Ft a| ≤ ∫ a in s..t, R (t - a) := by
    have htne : ∀ᵐ a : ℝ, a ≠ t := by
      have hs : {a : ℝ | ¬ a ≠ t} = {t} := by ext a; simp
      rw [MeasureTheory.ae_iff, hs]
      exact MeasureTheory.measure_singleton t
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hstle
    · filter_upwards [htne] with a hat ha
      rw [Real.norm_eq_abs]
      have hua : 0 < t - a := sub_pos.mpr (lt_of_le_of_ne ha.2 hat)
      have hb := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
        hua hr0.le hH x j k (q a).continuous.aestronglyMeasurable
          (hqb a) (hqholder a x)
      change |Ft a| ≤ H * (t - a) ^ (-1 + r / 2) *
        heatHessianEntryHolderMoment n r j k at hb
      change |Ft a| ≤ R (t - a)
      change |Ft a| ≤ 2 * (H * (t - a) ^ (-1 + r / 2) *
        heatHessianEntryHolderMoment n r j k)
      have hbase : 0 ≤ H * (t - a) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k :=
        mul_nonneg
          (mul_nonneg hH (Real.rpow_nonneg hua.le (-1 + r / 2)))
          (heatHessianEntryHolderMoment_nonneg n r j k)
      exact hb.trans (by nlinarith)
    · exact hRcompT
  have hnear : |∫ a in c..s, (Ft a - Fs a)| ≤
      ∫ a in c..s, R (s - a) := by
    have hsne : ∀ᵐ a : ℝ, a ≠ s := by
      have ht : {a : ℝ | ¬ a ≠ s} = {s} := by ext a; simp
      rw [MeasureTheory.ae_iff, ht]
      exact MeasureTheory.measure_singleton s
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hcs
    · filter_upwards [hsne] with a has ha
      rw [Real.norm_eq_abs]
      have hu : 0 < s - a := sub_pos.mpr (lt_of_le_of_ne ha.2 has)
      have heq : t - a = δ + (s - a) := by dsimp only [δ]; ring
      change |heatHessianEntryConvolutionND (t - a) (q a) j k x -
        heatHessianEntryConvolutionND (s - a) (q a) j k x| ≤ R (s - a)
      rw [heq]
      exact abs_heatHessianEntryConvolutionND_time_shift_sub_le_recent
        hδ.le hu hr0.le hr1 (q a) hH (hqholder a) j k x
    · exact hRcompS
  have hfar : |∫ a in t₀..c, (Ft a - Fs a)| ≤
      ∫ a in t₀..c, O (s - a) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hc0
    · filter_upwards with a ha
      rw [Real.norm_eq_abs]
      have hu : 0 < s - a := by
        have : a ≤ c := ha.2
        dsimp only [c] at this
        linarith
      have heq : t - a = δ + (s - a) := by dsimp only [δ]; ring
      change |heatHessianEntryConvolutionND (t - a) (q a) j k x -
        heatHessianEntryConvolutionND (s - a) (q a) j k x| ≤ O (s - a)
      rw [heq]
      exact abs_heatHessianEntryConvolutionND_time_shift_sub_le_old
        hδ hu hr0.le (q a) hH (hqholder a) j k x
    · exact hOcomp
  have hdecomp :
      heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ s q j k x =
        (∫ a in s..t, Ft a) +
          (∫ a in t₀..c, (Ft a - Fs a)) +
          (∫ a in c..s, (Ft a - Fs a)) := by
    rw [heatDuhamelHessianEntryND, heatDuhamelHessianEntryND]
    change (∫ a in t₀..t, Ft a) - (∫ a in t₀..s, Fs a) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hFt0s hFst]
    have hsub := intervalIntegral.integral_sub hFt0s hFs
    have hadd := intervalIntegral.integral_add_adjacent_intervals hD0c hDcs
    calc
      ((∫ a in t₀..s, Ft a) + ∫ a in s..t, Ft a) -
          ∫ a in t₀..s, Fs a =
        (∫ a in s..t, Ft a) +
          ((∫ a in t₀..s, Ft a) - ∫ a in t₀..s, Fs a) := by ring
      _ = (∫ a in s..t, Ft a) +
          ∫ a in t₀..s, (Ft a - Fs a) := by rw [hsub]
      _ = (∫ a in s..t, Ft a) +
          ((∫ a in t₀..c, (Ft a - Fs a)) +
            ∫ a in c..s, (Ft a - Fs a)) := by rw [hadd]
      _ = _ := by ring
  rw [hdecomp]
  calc
    |(∫ a in s..t, Ft a) + (∫ a in t₀..c, (Ft a - Fs a)) +
        (∫ a in c..s, (Ft a - Fs a))| ≤
        |∫ a in s..t, Ft a| + |∫ a in t₀..c, (Ft a - Fs a)| +
          |∫ a in c..s, (Ft a - Fs a)| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (∫ a in s..t, R (t - a)) + (∫ a in t₀..c, O (s - a)) +
        (∫ a in c..s, R (s - a)) := add_le_add (add_le_add hre hfar) hnear
    _ = 2 * (∫ u in (0 : ℝ)..δ, R u) +
        ∫ u in δ..(s - t₀), O u := by
      have hRT := intervalIntegral.integral_comp_sub_left
        (a := s) (b := t) R t
      have hRS := intervalIntegral.integral_comp_sub_left
        (a := c) (b := s) R s
      have hOS := intervalIntegral.integral_comp_sub_left
        (a := t₀) (b := c) O s
      simp only [sub_self, c, δ, sub_sub_cancel] at hRT hRS hOS
      simp only [c, δ]
      rw [hRT, hRS, hOS]
      ring
    _ = 2 * (∫ u in (0 : ℝ)..(t - s),
        heatDuhamelHessianRecentEnvelope n r H j k u) +
      ∫ u in (t - s)..(s - t₀),
        heatDuhamelHessianOldEnvelope n r H
          ((n : ℝ) * heatHessianTimeShiftModulus (t - s)) j k u := by
      rfl

theorem heatHessianTimeShiftModulus_eq_sqrt {δ : ℝ} (hδ : 0 ≤ δ) :
    heatHessianTimeShiftModulus δ = 2 / Real.sqrt π * Real.sqrt δ := by
  unfold heatHessianTimeShiftModulus
  exact heatSemigroupND_timeModulus_eq_sqrt hδ

lemma sqrt_mul_rpow_time_eq_rpow {δ r : ℝ} (hδ : 0 < δ) :
    Real.sqrt δ * δ ^ (-1 / 2 + r / 2) = δ ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hδ]
  congr 1
  ring

/-- Coefficient supplied by the endpoint/old-time split for a small positive
time increment. -/
def heatDuhamelHessianTimeSmallEntryConstant
    (n : ℕ) (r H : ℝ) (j k : Fin n) : ℝ :=
  4 * (H * heatHessianEntryHolderMoment n r j k / (r / 2)) +
    heatDuhamelHessianOldConstant n r H j k * (n : ℝ) *
      (2 / Real.sqrt π) / ((1 - r) / 2)

lemma heatDuhamelHessianTimeSmallEntryConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH : 0 ≤ H) (j k : Fin n) :
    0 ≤ heatDuhamelHessianTimeSmallEntryConstant n r H j k := by
  unfold heatDuhamelHessianTimeSmallEntryConstant
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (div_nonneg
      (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
      (by linarith))
  · exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (heatDuhamelHessianOldConstant_nonneg n r hH j k)
          (Nat.cast_nonneg n))
        (div_nonneg (by norm_num) (Real.sqrt_nonneg π)))
      (by linarith)

/-- Evaluation and normalization of the small-increment split. -/
theorem abs_heatDuhamelHessianEntryND_time_sub_le_small
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (hst : s < t)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hsmall : t - s ≤ s - t₀)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      heatDuhamelHessianTimeSmallEntryConstant n r H j k *
        (t - s) ^ (r / 2) := by
  let δ : ℝ := t - s
  let e : ℝ := -1 / 2 + r / 2
  let K : ℝ := heatDuhamelHessianOldConstant n r H j k
  let d : ℝ := (n : ℝ) * heatHessianTimeShiftModulus δ
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hmain := abs_heatDuhamelHessianEntryND_time_sub_le_split
    hs0 hst hr0 hr1 hsmall hq hH hqb hqholder j k x
  rw [integral_heatDuhamelHessianRecentEnvelope hr0 j k,
    integral_heatDuhamelHessianOldEnvelope hδ
      (by simpa only [δ] using hsmall) (ne_of_lt hr1) j k] at hmain
  change _ ≤ heatDuhamelHessianTimeSmallEntryConstant n r H j k *
    δ ^ (r / 2)
  have hmain' :
      |heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ s q j k x| ≤
        4 * (H * heatHessianEntryHolderMoment n r j k *
          (δ ^ (r / 2) / (r / 2))) +
        K * d * (((s - t₀) ^ e - δ ^ e) / e) := by
    simp only [δ, e, K, d] at hmain ⊢
    convert hmain using 1
    all_goals ring
  have he : e < 0 := by dsimp only [e]; linarith
  have hQ : (((s - t₀) ^ e - δ ^ e) / e) ≤ δ ^ e / (-e) := by
    rw [show ((s - t₀) ^ e - δ ^ e) / e =
      (δ ^ e - (s - t₀) ^ e) / (-e) by ring_nf]
    apply div_le_div_of_nonneg_right
    · exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.mpr hs0) e)
    · exact (neg_pos.mpr he).le
  have hKd : 0 ≤ K * d := by
    exact mul_nonneg
      (heatDuhamelHessianOldConstant_nonneg n r hH j k)
      (mul_nonneg (Nat.cast_nonneg n)
        (heatHessianTimeShiftModulus_nonneg hδ.le))
  have hold : K * d * (((s - t₀) ^ e - δ ^ e) / e) ≤
      (K * (n : ℝ) * (2 / Real.sqrt π) / ((1 - r) / 2)) *
        δ ^ (r / 2) := by
    calc
      _ ≤ K * d * (δ ^ e / (-e)) :=
        mul_le_mul_of_nonneg_left hQ hKd
      _ = K * ((n : ℝ) * (2 / Real.sqrt π) * Real.sqrt δ) *
          (δ ^ e / (-e)) := by
        dsimp only [d]
        rw [heatHessianTimeShiftModulus_eq_sqrt hδ.le]
        ring_nf
      _ = (K * (n : ℝ) * (2 / Real.sqrt π) / ((1 - r) / 2)) *
          δ ^ (r / 2) := by
        calc
          K * ((n : ℝ) * (2 / Real.sqrt π) * Real.sqrt δ) *
              (δ ^ e / (-e)) =
            K * (n : ℝ) * (2 / Real.sqrt π) *
              (Real.sqrt δ * δ ^ (-1 / 2 + r / 2)) / (-e) := by
                dsimp only [e]
                ring
          _ = K * (n : ℝ) * (2 / Real.sqrt π) *
              δ ^ (r / 2) / (-e) := by
                rw [sqrt_mul_rpow_time_eq_rpow hδ]
          _ = _ := by dsimp only [e]; ring
  refine hmain'.trans ?_
  calc
    4 * (H * heatHessianEntryHolderMoment n r j k *
        (δ ^ (r / 2) / (r / 2))) +
        K * d * (((s - t₀) ^ e - δ ^ e) / e) ≤
      (4 * (H * heatHessianEntryHolderMoment n r j k / (r / 2))) *
          δ ^ (r / 2) +
        (K * (n : ℝ) * (2 / Real.sqrt π) / ((1 - r) / 2)) *
          δ ^ (r / 2) := by
      apply add_le_add
      · ring_nf
        exact le_rfl
      · exact hold
    _ = heatDuhamelHessianTimeSmallEntryConstant n r H j k *
        δ ^ (r / 2) := by
      unfold heatDuhamelHessianTimeSmallEntryConstant
      dsimp only [K]
      ring

/-- A coarse coefficient for increments longer than the elapsed old time. -/
def heatDuhamelHessianTimeLargeEntryConstant
    (n : ℕ) (r H : ℝ) (j k : Fin n) : ℝ :=
  H * heatHessianEntryHolderMoment n r j k *
    (((2 : ℝ) ^ (r / 2) + 1) / (r / 2))

lemma heatDuhamelHessianTimeLargeEntryConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hH : 0 ≤ H)
    (j k : Fin n) :
    0 ≤ heatDuhamelHessianTimeLargeEntryConstant n r H j k := by
  unfold heatDuhamelHessianTimeLargeEntryConstant
  exact mul_nonneg
    (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
    (div_nonneg (add_nonneg (Real.rpow_nonneg (by norm_num) _) zero_le_one)
      (by linarith))

/-- If the increment dominates all earlier elapsed time, the two global
cancellation bounds already have the desired temporal Holder scale. -/
theorem abs_heatDuhamelHessianEntryND_time_sub_le_large
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (hst : s < t)
    (hr0 : 0 < r) (hlarge : s - t₀ ≤ t - s)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      heatDuhamelHessianTimeLargeEntryConstant n r H j k *
        (t - s) ^ (r / 2) := by
  let δ : ℝ := t - s
  let A : ℝ := H * heatHessianEntryHolderMoment n r j k
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have ht0 : t₀ ≤ t := hs0.trans hst.le
  have htbound : t - t₀ ≤ 2 * δ := by dsimp only [δ]; linarith
  have hspow : (s - t₀) ^ (r / 2) ≤ δ ^ (r / 2) :=
    Real.rpow_le_rpow (sub_nonneg.mpr hs0) (by simpa only [δ] using hlarge)
      (by linarith)
  have htpow : (t - t₀) ^ (r / 2) ≤
      (2 : ℝ) ^ (r / 2) * δ ^ (r / 2) := by
    calc
      (t - t₀) ^ (r / 2) ≤ (2 * δ) ^ (r / 2) :=
        Real.rpow_le_rpow (sub_nonneg.mpr ht0) htbound (by linarith)
      _ = (2 : ℝ) ^ (r / 2) * δ ^ (r / 2) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
  have htH := abs_heatDuhamelHessianEntryND_le
    ht0 hr0 hq hH hqb hqholder j k x
  have hsH := abs_heatDuhamelHessianEntryND_le
    hs0 hr0 hq hH hqb hqholder j k x
  have hA : 0 ≤ A := mul_nonneg hH
    (heatHessianEntryHolderMoment_nonneg n r j k)
  have hp : 0 < r / 2 := by linarith
  calc
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      |heatDuhamelHessianEntryND t₀ t q j k x| +
        |heatDuhamelHessianEntryND t₀ s q j k x| := abs_sub _ _
    _ ≤ A * ((t - t₀) ^ (r / 2) / (r / 2)) +
        A * ((s - t₀) ^ (r / 2) / (r / 2)) := add_le_add htH hsH
    _ ≤ A * (((2 : ℝ) ^ (r / 2) * δ ^ (r / 2)) / (r / 2)) +
        A * (δ ^ (r / 2) / (r / 2)) := by
      gcongr
    _ = heatDuhamelHessianTimeLargeEntryConstant n r H j k *
        δ ^ (r / 2) := by
      unfold heatDuhamelHessianTimeLargeEntryConstant
      dsimp only [A]
      ring

/-- Uniform temporal Holder coefficient, covering both time-separation
regimes. -/
def heatDuhamelHessianTimeHolderEntryConstant
    (n : ℕ) (r H : ℝ) (j k : Fin n) : ℝ :=
  heatDuhamelHessianTimeSmallEntryConstant n r H j k +
    heatDuhamelHessianTimeLargeEntryConstant n r H j k

lemma heatDuhamelHessianTimeHolderEntryConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH : 0 ≤ H) (j k : Fin n) :
    0 ≤ heatDuhamelHessianTimeHolderEntryConstant n r H j k :=
  add_nonneg
    (heatDuhamelHessianTimeSmallEntryConstant_nonneg n hr0 hr1 hH j k)
    (heatDuhamelHessianTimeLargeEntryConstant_nonneg n hr0 hH j k)

theorem abs_heatDuhamelHessianEntryND_time_sub_le_holder_of_lt
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (hst : s < t)
    (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      heatDuhamelHessianTimeHolderEntryConstant n r H j k *
        (t - s) ^ (r / 2) := by
  rcases le_total (t - s) (s - t₀) with hsmall | hlarge
  · have hmain := abs_heatDuhamelHessianEntryND_time_sub_le_small
      hs0 hst hr0 hr1 hsmall hq hH hqb hqholder j k x
    refine hmain.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
    unfold heatDuhamelHessianTimeHolderEntryConstant
    exact le_add_of_nonneg_right
      (heatDuhamelHessianTimeLargeEntryConstant_nonneg n hr0 hH j k)
  · have hmain := abs_heatDuhamelHessianEntryND_time_sub_le_large
      hs0 hst hr0 hlarge hq hH hqb hqholder j k x
    refine hmain.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
    unfold heatDuhamelHessianTimeHolderEntryConstant
    exact le_add_of_nonneg_left
      (heatDuhamelHessianTimeSmallEntryConstant_nonneg n hr0 hr1 hH j k)

/-- **Temporal Holder estimate for every Duhamel Hessian entry.**  Only the
uniform spatial Holder modulus of the source is needed. -/
theorem abs_heatDuhamelHessianEntryND_time_sub_le_holder
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (ht0 : t₀ ≤ t)
    (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) (x : Fin n → ℝ) :
    |heatDuhamelHessianEntryND t₀ t q j k x -
        heatDuhamelHessianEntryND t₀ s q j k x| ≤
      heatDuhamelHessianTimeHolderEntryConstant n r H j k *
        |t - s| ^ (r / 2) := by
  rcases lt_trichotomy s t with hst | hst | hts
  · have habs : |t - s| = t - s := abs_of_pos (sub_pos.mpr hst)
    rw [habs]
    exact abs_heatDuhamelHessianEntryND_time_sub_le_holder_of_lt
      hs0 hst hr0 hr1 hq hH hqb hqholder j k x
  · subst t
    simp only [sub_self, abs_zero]
    exact mul_nonneg
      (heatDuhamelHessianTimeHolderEntryConstant_nonneg n hr0 hr1 hH j k)
      (Real.rpow_nonneg le_rfl _)
  · have hmain := abs_heatDuhamelHessianEntryND_time_sub_le_holder_of_lt
      ht0 hts hr0 hr1 hq hH hqb hqholder j k x
    rw [abs_sub_comm (heatDuhamelHessianEntryND t₀ t q j k x)
      (heatDuhamelHessianEntryND t₀ s q j k x), abs_sub_comm t s]
    rw [abs_of_pos (sub_pos.mpr hts)]
    exact hmain

/-- Full operator-norm temporal Holder coefficient. -/
def heatDuhamelHessianTimeHolderConstant (n : ℕ) (r H : ℝ) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n,
    heatDuhamelHessianTimeHolderEntryConstant n r H j k

lemma heatDuhamelHessianTimeHolderConstant_nonneg
    (n : ℕ) {r H : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hH : 0 ≤ H) :
    0 ≤ heatDuhamelHessianTimeHolderConstant n r H := by
  unfold heatDuhamelHessianTimeHolderConstant
  exact Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
    heatDuhamelHessianTimeHolderEntryConstant_nonneg n hr0 hr1 hH j k

section DuhamelTimeOperatorHolder

local instance duhamelTimeCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance duhamelTimeCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- **The genuine full Frechet Hessian of the Duhamel potential is temporally
`r/2`-Holder in operator norm.** -/
theorem norm_heatDuhamelHessianCLM_time_sub_le_holder
    {n : ℕ} {t₀ s t r : ℝ} (hs0 : t₀ ≤ s) (ht0 : t₀ ≤ t)
    (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatDuhamelHessianCLM ht0 hr0 hq hH hqb hqholder x -
        heatDuhamelHessianCLM hs0 hr0 hq hH hqb hqholder x‖ ≤
      heatDuhamelHessianTimeHolderConstant n r H * |t - s| ^ (r / 2) := by
  have heq : heatDuhamelHessianCLM ht0 hr0 hq hH hqb hqholder x -
      heatDuhamelHessianCLM hs0 hr0 hq hH hqb hqholder x =
      coordinateHessianCLM (fun j k ↦
        heatDuhamelHessianEntryND t₀ t q j k x -
          heatDuhamelHessianEntryND t₀ s q j k x) := by
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
          heatDuhamelHessianEntryND t₀ s q j k x|) ≤
      ∑ j : Fin n, ∑ k : Fin n,
        heatDuhamelHessianTimeHolderEntryConstant n r H j k *
          |t - s| ^ (r / 2) := by
      gcongr with j k
      exact abs_heatDuhamelHessianEntryND_time_sub_le_holder
        hs0 ht0 hr0 hr1 hq hH hqb hqholder j k x
    _ = heatDuhamelHessianTimeHolderConstant n r H *
        |t - s| ^ (r / 2) := by
      unfold heatDuhamelHessianTimeHolderConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]

end DuhamelTimeOperatorHolder

section DuhamelParabolicHolder

local instance duhamelParabolicCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance duhamelParabolicCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Totalized full Hessian field of the Duhamel potential. -/
def heatDuhamelHessianFieldND
    {n : ℕ} {r : ℝ} (t₀ : ℝ) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ℝ × (Fin n → ℝ) →
      (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  fun z ↦ if hz : t₀ ≤ z.1 then
    heatDuhamelHessianCLM hz hr0 hq hH hqb hqholder z.2
  else 0

/-- **The full Duhamel Hessian is parabolically `r`-Holder on the closed
forward cylinder.** -/
theorem parabolicHolderWith_heatDuhamelHessianFieldND
    {n : ℕ} {r : ℝ} (t₀ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ a y, ‖q a y‖ ≤ C)
    (hqholder : ∀ a x y, |q a y - q a x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r) :
    ParabolicHolderWith
      (heatDuhamelHessianSpatialHolderConstant n r H +
        heatDuhamelHessianTimeHolderConstant n r H) r
      (heatDuhamelHessianFieldND t₀ hr0 hq hH hqb hqholder)
      {p : ℝ × (Fin n → ℝ) | t₀ ≤ p.1} := by
  apply parabolicHolderWith_of_forall_same_time_same_space hr0.le
    (heatDuhamelHessianSpatialHolderConstant_nonneg n hr0 hr1 hH)
    (heatDuhamelHessianTimeHolderConstant_nonneg n hr0 hr1 hH)
  · rintro ⟨t, x⟩ ht ⟨s, y⟩ hs
    exact ht
  · intro t x y htx hty
    have ht : t₀ ≤ t := htx
    change ‖heatDuhamelHessianFieldND t₀ hr0 hq hH hqb hqholder (t, x) -
      heatDuhamelHessianFieldND t₀ hr0 hq hH hqb hqholder (t, y)‖ ≤ _
    simp only [heatDuhamelHessianFieldND, dif_pos ht]
    rw [dist_eq_norm]
    exact norm_heatDuhamelHessianCLM_sub_le_holder
      ht hr0 hr1 hq hH hqb hqholder x y
  · intro x t s htx hsx
    have ht : t₀ ≤ t := htx
    have hs : t₀ ≤ s := hsx
    change ‖heatDuhamelHessianFieldND t₀ hr0 hq hH hqb hqholder (t, x) -
      heatDuhamelHessianFieldND t₀ hr0 hq hH hqb hqholder (s, x)‖ ≤ _
    simp only [heatDuhamelHessianFieldND, dif_pos ht, dif_pos hs]
    exact norm_heatDuhamelHessianCLM_time_sub_le_holder
      hs ht hr0 hr1 hq hH hqb hqholder x

end DuhamelParabolicHolder

end AnalyticPDE
end RicciFlow
