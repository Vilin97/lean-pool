/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.AnalyticSeries
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.ExactOrder
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedSeries
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.WeightedCoefficientMap

/-!
# Normalized weighted coefficient sequences

Exact order in the distinguished variable lets us choose a small positive
weight so that the normalized coefficient sequence is strictly close to the
degree-`d` monomial in the ordinary complex `ℓ¹` norm.  This is the
Archimedean tail-scaling estimate needed by the Banach-algebra proof.
-/

open Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace ClassicalComplexWPT

/-- Absolutely summable one-variable coefficient sequences at the origin. -/
abbrev OriginSeq := L1Coeff ℕ

lemma norm_lastDirection_local (n : ℕ) : ‖lastDirection n‖ = 1 := by
  simp [lastDirection]

/-- The monomial coefficient vector supported at degree `d`. -/
noncomputable def monomialSeq (d : ℕ) : OriginSeq := lp.single 1 d 1

@[simp] lemma monomialSeq_apply_same (d : ℕ) : monomialSeq d d = 1 := by
  simp [monomialSeq, lp.single_apply]

@[simp] lemma monomialSeq_apply_ne {d k : ℕ} (h : k ≠ d) : monomialSeq d k = 0 := by
  simp [monomialSeq, lp.single_apply, h]

/-- Diagonal rescaling of an `ℓ¹` sequence by powers of `t ≤ 1`. -/
noncomputable def scaleSeq (t : ℝ≥0) (ht : t ≤ 1) (f : OriginSeq) : OriginSeq :=
  ⟨fun k ↦ (t : ℂ) ^ k * f k, by
    apply memℓp_gen
    have hs : Summable (fun k ↦ ‖(t : ℂ) ^ k * f k‖) :=
      (L1Coeff.summable_norm f).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg t.coe_nonneg]
        simpa using mul_le_of_le_one_left (norm_nonneg (f k))
          (pow_le_one₀ t.coe_nonneg (by exact_mod_cast ht)))
    simpa using hs⟩

@[simp] lemma scaleSeq_apply (t : ℝ≥0) (ht : t ≤ 1) (f : OriginSeq) (k : ℕ) :
    scaleSeq t ht f k = (t : ℂ) ^ k * f k := rfl

/-- Rescale a sequence and normalize its coefficient in degree `d` to one. -/
noncomputable def normalizedScale (t : ℝ≥0) (ht : t ≤ 1)
    (f : OriginSeq) (d : ℕ) : OriginSeq :=
  ((scaleSeq t ht f d)⁻¹) • scaleSeq t ht f

@[simp] lemma normalizedScale_apply (t : ℝ≥0) (ht : t ≤ 1)
    (f : OriginSeq) (d k : ℕ) :
    normalizedScale t ht f d k =
      (((t : ℂ) ^ d * f d)⁻¹) * ((t : ℂ) ^ k * f k) := rfl

lemma normalizedScale_sub_monomial_apply_lt {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d k : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖(normalizedScale t ht f d - monomialSeq d) k‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f k‖ := by
  change ‖normalizedScale t ht f d k - monomialSeq d k‖ ≤
    ((t : ℝ) / ‖f d‖) * ‖f k‖
  by_cases hkd : k < d
  · have hne : k ≠ d := ne_of_lt hkd
    simp [normalizedScale_apply, monomialSeq_apply_ne hne, hlow k hkd]
  by_cases hdk : k = d
  · subst k
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hprod : (t : ℂ) ^ d * f d ≠ 0 := mul_ne_zero (pow_ne_zero _ htC) hfd
    have heq : normalizedScale t ht f d d = 1 := by
      rw [normalizedScale_apply, inv_mul_cancel₀ hprod]
    rw [heq, monomialSeq_apply_same, sub_self, norm_zero]
    positivity
  have hdkle : d ≤ k := Nat.le_of_not_gt hkd
  have hdklt : d < k := lt_of_le_of_ne hdkle (Ne.symm hdk)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have htpowd : (t : ℂ) ^ d ≠ 0 := pow_ne_zero _ htC
  rw [normalizedScale_apply, monomialSeq_apply_ne hdk, sub_zero]
  rw [norm_mul, norm_inv, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg t.coe_nonneg]
  have htRpos : 0 < (t : ℝ) := by exact_mod_cast ht0
  have htRne : (t : ℝ) ≠ 0 := htRpos.ne'
  have hfdnorm : ‖f d‖ ≠ 0 := norm_ne_zero_iff.mpr hfd
  have hpow : (t : ℝ) ^ k = (t : ℝ) ^ (k - d) * (t : ℝ) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hdkle]
  have heq :
      (((t : ℝ) ^ d * ‖f d‖)⁻¹ * ((t : ℝ) ^ k * ‖f k‖)) =
        (((t : ℝ) ^ (k - d)) / ‖f d‖) * ‖f k‖ := by
    rw [hpow]
    field_simp
  rw [heq]
  gcongr
  apply pow_le_of_le_one t.coe_nonneg (by exact_mod_cast ht)
  omega

theorem norm_normalizedScale_sub_monomial_le {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖normalizedScale t ht f d - monomialSeq d‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f‖ := by
  rw [L1Coeff.norm_eq_tsum_norm, L1Coeff.norm_eq_tsum_norm]
  have hsright : Summable (fun k ↦ ((t : ℝ) / ‖f d‖) * ‖f k‖) :=
    (L1Coeff.summable_norm f).mul_left _
  calc
    (∑' k, ‖(normalizedScale t ht f d - monomialSeq d) k‖) ≤
        ∑' k, ((t : ℝ) / ‖f d‖) * ‖f k‖ := by
      apply Summable.tsum_le_tsum
      · intro k
        exact normalizedScale_sub_monomial_apply_lt ht ht0 f d k hlow hfd
      · exact L1Coeff.summable_norm _
      · exact hsright
    _ = ((t : ℝ) / ‖f d‖) * ∑' k, ‖f k‖ := by rw [tsum_mul_left]

theorem exists_scale_normalized_close_half (f : OriginSeq) (d : ℕ)
    (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ∃ (t : ℝ≥0) (ht : t ≤ 1), 0 < t ∧ t < 1 ∧
      ‖normalizedScale t ht f d - monomialSeq d‖ < (1 : ℝ) / 2 := by
  let a : ℝ := ‖f d‖
  let b : ℝ := ‖f‖
  have ha : 0 < a := by exact norm_pos_iff.mpr hfd
  have hb : 0 ≤ b := norm_nonneg _
  have hden : 0 < 4 * (b + a) := by positivity
  let tr : ℝ := a / (4 * (b + a))
  have htr0 : 0 < tr := div_pos ha hden
  have htr1 : tr < 1 := by
    rw [div_lt_one hden]
    nlinarith
  let t : ℝ≥0 := ⟨tr, htr0.le⟩
  have ht0 : 0 < t := by exact_mod_cast htr0
  have ht1 : t < 1 := by exact_mod_cast htr1
  refine ⟨t, ht1.le, ht0, ht1, ?_⟩
  calc
    ‖normalizedScale t ht1.le f d - monomialSeq d‖ ≤
        ((t : ℝ) / ‖f d‖) * ‖f‖ :=
      norm_normalizedScale_sub_monomial_le ht1.le ht0 f d hlow hfd
    _ = b / (4 * (b + a)) := by
      change (tr / a) * b = b / (4 * (b + a))
      dsimp only [tr]
      field_simp
    _ < (1 : ℝ) / 2 := by
      rw [div_lt_iff₀ hden]
      nlinarith

/-- Distinguished-variable coefficients at the base origin, weighted by `R^k`. -/
noncomputable def originWeightedCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) : OriginSeq :=
  ⟨fun k ↦ (R : ℂ) ^ k * lastTaylorCoefficient p k 0, by
    apply memℓp_gen
    have hs : Summable (fun k ↦ ‖(R : ℂ) ^ k * lastTaylorCoefficient p k 0‖) :=
      (p.summable_norm_mul_pow hR).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ by
        rw [lastTaylorCoefficient_zero, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg]
        have hc : ‖p k (fun _ ↦ lastDirection n)‖ ≤ ‖p k‖ := by
          simpa [norm_lastDirection_local] using (p k).le_opNorm (fun _ ↦ lastDirection n)
        calc
          (R : ℝ) ^ k * ‖p k (fun _ ↦ lastDirection n)‖ ≤
              (R : ℝ) ^ k * ‖p k‖ :=
            mul_le_mul_of_nonneg_left hc (pow_nonneg R.coe_nonneg k)
          _ = ‖p k‖ * (R : ℝ) ^ k := mul_comm _ _)
    simpa using hs⟩

@[simp] lemma originWeightedCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (k : ℕ) :
    originWeightedCoeffs p R hR k =
      (R : ℂ) ^ k * lastTaylorCoefficient p k 0 := rfl

lemma originWeightedCoeffs_low_eq_zero {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (R : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) {k : ℕ} (hk : k < d) :
    originWeightedCoeffs p R hR k = 0 := by
  rw [originWeightedCoeffs_apply,
    ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).1 k hk,
    mul_zero]

lemma originWeightedCoeffs_top_ne_zero {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (R : ℝ≥0) (hR0 : 0 < R)
    (hR : (R : ℝ≥0∞) < p.radius) :
    originWeightedCoeffs p R hR d ≠ 0 := by
  rw [originWeightedCoeffs_apply]
  have hRC : (R : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]
    exact hR0.ne'
  exact mul_ne_zero (pow_ne_zero _ hRC)
    ((exactOrderInLastVariable_iff_lastTaylorCoefficients p hp).mp horder).2

lemma mul_radius_lt_of_le_one {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R t : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (ht : t ≤ 1) :
    ((t * R : ℝ≥0) : ℝ≥0∞) < p.radius := by
  apply lt_of_le_of_lt _ hR
  exact_mod_cast mul_le_of_le_one_left (show 0 ≤ R from bot_le) ht

lemma scaleSeq_originWeightedCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (R t : ℝ≥0)
    (hR : (R : ℝ≥0∞) < p.radius) (ht : t ≤ 1) :
    scaleSeq t ht (originWeightedCoeffs p R hR) =
      originWeightedCoeffs p (t * R) (mul_radius_lt_of_le_one p R t hR ht) := by
  apply lp.ext
  funext k
  simp only [scaleSeq_apply, originWeightedCoeffs_apply]
  push_cast
  rw [mul_pow]
  ring

/-- Normalize the radially weighted Taylor coefficients at the origin. -/
noncomputable def normalizedOriginCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : OriginSeq :=
  ((originWeightedCoeffs p r hr d)⁻¹) • originWeightedCoeffs p r hr

@[simp] lemma normalizedOriginCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d k : ℕ) :
    normalizedOriginCoeffs p r hr d k =
      (((r : ℂ) ^ d * lastTaylorCoefficient p d 0)⁻¹) *
        ((r : ℂ) ^ k * lastTaylorCoefficient p k 0) := rfl

theorem exists_radius_normalizedOrigin_close_half {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
        ‖normalizedOriginCoeffs p r hr d - monomialSeq d‖ < (1 : ℝ) / 2 := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨R, hR0E, hR⟩
  have hR0 : 0 < R := by exact_mod_cast hR0E
  let B : OriginSeq := originWeightedCoeffs p R hR
  have hBlow : ∀ j < d, B j = 0 := by
    intro j hj
    exact originWeightedCoeffs_low_eq_zero p hp horder R hR hj
  have hBd : B d ≠ 0 := originWeightedCoeffs_top_ne_zero p hp horder R hR0 hR
  obtain ⟨t, ht, ht0, ht1, hclose⟩ :=
    exists_scale_normalized_close_half B d hBlow hBd
  let r : ℝ≥0 := t * R
  have hr : (r : ℝ≥0∞) < p.radius := mul_radius_lt_of_le_one p R t hR ht
  have hr0 : 0 < r := mul_pos ht0 hR0
  have hscale : scaleSeq t ht B = originWeightedCoeffs p r hr := by
    dsimp only [B, r, hr]
    exact scaleSeq_originWeightedCoeffs p R t hR ht
  have hnorm : normalizedScale t ht B d = normalizedOriginCoeffs p r hr d := by
    unfold normalizedScale normalizedOriginCoeffs
    rw [hscale]
  refine ⟨r, hr, hr0,
    originWeightedCoeffs_top_ne_zero p hp horder r hr0 hr, ?_⟩
  rw [← hnorm]
  exact hclose

/-- Normalize any analytic coefficient map by a fixed scalar. -/
noncomputable def normalizedCoefficientMap {n : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) : Base n → OriginSeq :=
  fun z ↦ denom⁻¹ • C z

theorem analyticAt_normalizedCoefficientMap {n : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0) :
    AnalyticAt ℂ (normalizedCoefficientMap C denom) 0 := by
  change AnalyticAt ℂ (denom⁻¹ • C) 0
  exact hC.const_smul

theorem eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one {n d : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0)
    (hclose : ‖normalizedCoefficientMap C denom 0 - monomialSeq d‖ < (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      ‖normalizedCoefficientMap C denom z - monomialSeq d‖ < 1 := by
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hmem : normalizedCoefficientMap C denom 0 ∈
      Metric.ball (monomialSeq d) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hclose.trans hhalf
  have hopen : Metric.ball (monomialSeq d) 1 ∈
      𝓝 (normalizedCoefficientMap C denom 0) :=
    Metric.isOpen_ball.mem_nhds hmem
  filter_upwards [(analyticAt_normalizedCoefficientMap C denom hC).continuousAt.eventually hopen]
    with z hz
  simpa [Metric.mem_ball, dist_eq_norm] using hz

/-- The analytic weighted coefficient map normalized by its degree-`d`
coefficient at the base origin. -/
noncomputable def analyticNormalizedCoefficientMap {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) : Base n → OriginSeq :=
  normalizedCoefficientMap (weightedCoefficientSeries p r).sum
    (originWeightedCoeffs p r hr d)

theorem analyticNormalizedCoefficientMap_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    analyticNormalizedCoefficientMap p r hr d 0 = normalizedOriginCoeffs p r hr d := by
  have hzq : (0 : Base n) ∈
      Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius := by
    simpa only [Metric.mem_eball, edist_self] using
      radius_weightedCoefficientSeries_pos p r hr
  have hzp : ((0 : Base n), (0 : ℂ)) ∈
      Metric.eball (0 : Ambient n) p.radius := by
    rw [← ambient_zero_eq n]
    have hp0 : (0 : ℝ≥0∞) < p.radius :=
      (show (0 : ℝ≥0∞) ≤ r by simp).trans_lt hr
    simpa only [Metric.mem_eball, edist_self] using hp0
  have hC0 : (weightedCoefficientSeries p r).sum (0 : Base n) =
      originWeightedCoeffs p r hr := by
    apply lp.ext
    funext k
    exact weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
      p r 0 k hr hzq hzp
  unfold analyticNormalizedCoefficientMap normalizedCoefficientMap normalizedOriginCoeffs
  rw [hC0]

theorem analyticAt_analyticNormalizedCoefficientMap {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 := by
  exact analyticAt_normalizedCoefficientMap _ _
    (analyticAt_weightedCoefficientSeries_sum p r hr)

/-- Exact distinguished order supplies a normalized analytic coefficient map
that is within `1/2` of the monomial at the origin and remains within `1` on
a neighborhood of the base origin. -/
theorem exists_normalizedAnalyticCoefficientMap {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 ∧
      ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ < (1 : ℝ) / 2 ∧
      ∀ᶠ z in 𝓝 (0 : Base n),
        ‖analyticNormalizedCoefficientMap p r hr d z - monomialSeq d‖ < 1 := by
  obtain ⟨r, hr, hr0, htop, hclose⟩ :=
    exists_radius_normalizedOrigin_close_half p hp horder
  have hzero : analyticNormalizedCoefficientMap p r hr d 0 =
      normalizedOriginCoeffs p r hr d :=
    analyticNormalizedCoefficientMap_zero p r hr d
  have hclose' :
      ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ < (1 : ℝ) / 2 := by
    rw [hzero]
    exact hclose
  have han := analyticAt_analyticNormalizedCoefficientMap p r hr d
  refine ⟨r, hr, hr0, htop, han, hclose', ?_⟩
  exact eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
    (weightedCoefficientSeries p r).sum (originWeightedCoeffs p r hr d)
    (analyticAt_weightedCoefficientSeries_sum p r hr) hclose'

end ClassicalComplexWPT
