/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Conversions
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.AELocalEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Upper semicontinuity of the time-slice energy

The product-cutoff argument below uses the almost-every-time local energy
inequality and the compactly supported smooth cutoffs from the setting layer.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

lemma product_test_function
    {Ω : Set Vec3} {I : Set ℝ} {η : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθI : tsupport θ ⊆ I) :
    (fun z : Vec3 × ℝ => η z.1 * θ z.2) ∈
      spaceTimeTestFunction (V := ℝ) Ω I := by
  have hts : tsupport (fun z : Vec3 × ℝ => η z.1 * θ z.2) =
      tsupport η ×ˢ tsupport θ := by
    have hsupp : Function.support (fun z : Vec3 × ℝ => η z.1 * θ z.2) =
        Function.support η ×ˢ Function.support θ := by
      ext z
      simp only [Function.mem_support, Set.mem_prod, mul_ne_zero_iff]
    rw [tsupport, tsupport, tsupport, hsupp, closure_prod_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact (hη.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp contDiff_snd)
  · change IsCompact (tsupport (fun z : Vec3 × ℝ => η z.1 * θ z.2))
    rw [hts]
    exact IsCompact.prod hηc hθc
  · rw [hts]
    exact Set.prod_mono hηΩ hθI

lemma smooth_time_envelope {a b : ℝ} (hab : a < b) {I : Set ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hI : IsOpen I) (hconn : I.OrdConnected) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ I ∧ (∀ t, 0 ≤ θ t) ∧ ∀ t ∈ Icc a b, θ t = 1 := by
  obtain ⟨εa, hεa, hεasub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ha)
  obtain ⟨εb, hεb, hεbsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hb)
  let ε := min εa εb
  have hε : 0 < ε := lt_min hεa hεb
  let c := (a + b) / 2
  let d := (b - a) / 2
  let rIn := d + ε / 4
  let rOut := d + ε / 2
  have hd : 0 < d := by dsimp [d]; linarith only [hab]
  have hrIn : 0 < rIn := by dsimp [rIn]; positivity
  have hrOut : rIn < rOut := by dsimp [rIn, rOut]; linarith only [hε]
  let B : ContDiffBump c := ⟨rIn, rOut, hrIn, hrOut⟩
  refine ⟨fun t => B t, B.contDiff, B.hasCompactSupport, ?_, ?_, ?_⟩
  · rw [show tsupport (fun t => B t) = closedBall c rOut from B.tsupport_eq]
    intro t ht
    by_cases hta : t ≤ a
    · apply hεasub
      rw [Metric.mem_ball]
      change dist t c ≤ rOut at ht
      rw [Real.dist_eq] at ht ⊢
      have htlow : -rOut ≤ t - c := (abs_le.mp ht).1
      have hmin : ε ≤ εa := min_le_left _ _
      dsimp [c, d, rOut] at htlow ⊢
      rw [abs_of_nonpos (by linarith only [hta])]
      linarith only [htlow, hmin, hε]
    · by_cases htb : b ≤ t
      · apply hεbsub
        rw [Metric.mem_ball]
        change dist t c ≤ rOut at ht
        rw [Real.dist_eq] at ht ⊢
        have hthigh : t - c ≤ rOut := (abs_le.mp ht).2
        have hmin : ε ≤ εb := min_le_right _ _
        dsimp [c, d, rOut] at hthigh
        rw [abs_lt]
        constructor
        · have htpos : 0 ≤ t - b := by linarith only [htb]
          linarith only [hεb, htpos]
        · linarith only [hthigh, hmin, hε]
      · exact hconn.out ha hb ⟨le_of_not_ge hta, le_of_not_ge htb⟩
  · intro t
    exact B.nonneg
  · intro t ht
    exact B.one_of_mem_closedBall (by
      change dist t c ≤ rIn
      rw [Real.dist_eq]
      have hdist : |t - c| ≤ d := by
        rw [abs_le]
        constructor
        · dsimp [c, d]
          linarith only [ht.1]
        · dsimp [c, d]
          linarith only [ht.2]
      have hle : d ≤ rIn := by
        dsimp [rIn]
        linarith only [hε]
      exact hdist.trans hle)

lemma vec3Ball_subset_euclideanBall {x : Vec3} {r : ℝ} (hr : 0 < r) :
    vec3Ball x r ⊆ euclideanBall x r := by
  intro y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
  have heq : vecEuclideanNorm (y - x) = vec3EuclideanNorm (y - x) := by
    simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot]
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  exact hy


lemma weighted_kernel_le
    {A : ℝ → ℝ} {b h S : ℝ} (hh : 0 < h)
    (hA : ∀ᵐ s ∂volume.restrict (Ioc (b - h) b), A s ≤ S)
    (hAint : Integrable A volume) (_ : 0 ≤ S) :
    ∫ s, A s * (-deriv (backwardTimeCutoff b h) s) ≤ S := by
  have hA' := (ae_restrict_iff' measurableSet_Ioc).mp hA
  have hk : Integrable (fun s => -deriv (backwardTimeCutoff b h) s) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (backwardTimeCutoff_smooth (t := b) (h := h)).continuous_deriv
        (by simp) |>.neg
    · apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      exact backwardTimeCutoff_kernel_support hh
  have hleft : Integrable (fun s => A s * (-deriv (backwardTimeCutoff b h) s)) volume :=
    hAint.mul_bdd hk.aestronglyMeasurable (by
      filter_upwards [] with s
      simpa only [Real.norm_eq_abs, abs_neg] using
        (backwardTimeCutoff_abs_deriv_le (t := b) (h := h) (s := s) hh))
  have hright : Integrable (fun s => S * (-deriv (backwardTimeCutoff b h) s)) volume :=
    hk.const_mul S
  calc
    ∫ s, A s * (-deriv (backwardTimeCutoff b h) s) ≤
        ∫ s, S * (-deriv (backwardTimeCutoff b h) s) := by
      apply integral_mono_ae hleft hright
      filter_upwards [hA', Measure.ae_ne (volume : Measure ℝ) (b - h)] with s hs hne
      by_cases hs' : s ∈ Icc (b - h) b
      · exact mul_le_mul_of_nonneg_right (hs (by
            exact ⟨lt_of_le_of_ne hs'.1 hne.symm, hs'.2⟩))
          (neg_nonneg.mpr (backwardTimeCutoff_deriv_nonpos hh))
      · have hz : -deriv (backwardTimeCutoff b h) s = 0 := by
          apply neg_eq_zero.mpr
          by_contra hne
          exact hs' (backwardTimeCutoff_kernel_support hh
            (Function.mem_support.mpr (neg_ne_zero.mpr hne)))
        rw [hz, mul_zero, mul_zero]
    _ = S := by
      rw [integral_const_mul, backwardTimeCutoff_kernel_integral hh]
      ring

lemma strip_error_tendsto
    {g : Vec3 × ℝ → ℝ} {K : Set Vec3} {b : ℝ}
    (hK : IsCompact K) (hg : Integrable g volume) :
    Tendsto
      (fun h : ℝ => ∫ z in K ×ˢ Icc (b - h) (b + h), |g z|)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeasure : Tendsto
      (fun h : ℝ => volume (K ×ˢ Icc (b - h) (b + h)))
      (𝓝[>] 0) (𝓝 0) := by
    have htime := tendsto_measure_Icc_nhdsWithin_right' (volume : Measure ℝ) b
    have hKmeas : MeasurableSet K := hK.measurableSet
    have hKtop : volume K ≠ ⊤ := hK.measure_ne_top
    have hprod : ∀ h : ℝ,
        volume (K ×ˢ Icc (b - h) (b + h)) =
          volume K * volume (Icc (b - h) (b + h)) := by
      intro h
      rw [show (volume : Measure (Vec3 × ℝ)) =
          (volume : Measure Vec3).prod (volume : Measure ℝ) from
            Measure.volume_eq_prod _ _]
      rw [Measure.prod_prod K (Icc (b - h) (b + h))]
    rw [show (fun h : ℝ => volume (K ×ˢ Icc (b - h) (b + h))) =
      (fun h => volume K * volume (Icc (b - h) (b + h))) from by
        funext h; rw [hprod h]]
    have hmul := ENNReal.Tendsto.const_mul htime (Or.inr hKtop)
    simpa [measure_singleton] using hmul
  exact hg.norm.tendsto_setIntegral_nhds_zero hmeasure

lemma setIntegral_univ_Iio_probe
    {g : Vec3 × ℝ → ℝ} {t : ℝ}
    (hg : IntegrableOn g (Set.univ ×ˢ Iio t) volume) :
    ∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z =
      ∫ s in Iio t, ∫ x, g (x, s) := by
  have hgs : IntegrableOn (fun z : ℝ × Vec3 => g z.swap)
      (Iio t ×ˢ Set.univ) ((volume : Measure ℝ).prod (volume : Measure Vec3)) :=
    hg.swap
  calc
    ∫ z : Vec3 × ℝ in (Set.univ ×ˢ Iio t), g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) =
        ∫ z : ℝ × Vec3 in (Iio t ×ˢ Set.univ), g z.swap ∂
          (volume : Measure ℝ).prod (volume : Measure Vec3) := by
      exact (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) Set.univ (Iio t) g).symm
    _ = ∫ s in Iio t, ∫ x, g (x, s) := by
      rw [setIntegral_prod _ hgs]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [setIntegral_univ]
      rfl

lemma cutoff_slice_le
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3}
    {η : Vec3 → ℝ} {θ : ℝ → ℝ} {x₀ : Vec3} {r R a b : ℝ}
    (hr : 0 < r) (hrr : r < R)
    (hη_nonneg : ∀ x, 0 ≤ η x) (hη_le : ∀ x, η x ≤ 1)
    (_ : ∀ x, x ∈ vec3Ball x₀ r → η x = 1)
    (hη_support : tsupport η ⊆ euclideanBall x₀ R)
    (hηΩ : tsupport η ⊆ Ω)
    (hθ_one : ∀ s, s ∈ Icc a b → θ s = 1)
    {S : ℝ≥0∞}
    (hSdef : S = essSup
      (timeSliceBallEnergy x₀ R · (fun w => vec3EuclideanNorm (u w)))
      (volume.restrict (Ioc a b))) (hS : S ≠ ⊤)
    (hE : Integrable
      (fun z : Vec3 × ℝ =>
        (vec3EuclideanNorm (u z)) ^ 2 * (η z.1 * θ z.2)) volume) :
    ∀ᵐ s ∂volume.restrict (Ioc a b),
      ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x ≤ S.toReal := by
  have hslice := hE.prod_left_ae
  have houter := ENNReal.ae_le_essSup
    (f := fun s => timeSliceBallEnergy x₀ R s
      (fun w => vec3EuclideanNorm (u w)))
    (μ := volume.restrict (Ioc a b))
  rw [← hSdef] at houter
  filter_upwards [ae_restrict_of_ae hslice, houter,
    ae_restrict_mem measurableSet_Ioc] with s hs houter hsab'
  have hsab : s ∈ Icc a b := ⟨le_of_lt hsab'.1, hsab'.2⟩
  have hθs : θ s = 1 := hθ_one s hsab
  have hsη : Integrable
      (fun x : Vec3 => (vec3EuclideanNorm (u (x, s))) ^ 2 * η x) volume := by
    simpa [hθs, mul_assoc] using hs
  have hnon : ∀ x : Vec3, 0 ≤
      (vec3EuclideanNorm (u (x, s))) ^ 2 * η x := by
    intro x
    exact mul_nonneg (sq_nonneg _) (hη_nonneg x)
  have hreal : ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x =
      (∫⁻ x, ENNReal.ofReal
        ((vec3EuclideanNorm (u (x, s))) ^ 2 * η x)).toReal := by
    rw [← setIntegral_univ]
    rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hsη.integrableOn]
    · simp only [Measure.restrict_univ]
    · exact Filter.Eventually.of_forall hnon
  have hpoint : ∀ x : Vec3,
      ENNReal.ofReal ((vec3EuclideanNorm (u (x, s))) ^ 2 * η x) ≤
        (vec3Ball x₀ R).indicator
          (fun y => ENNReal.ofReal ((vec3EuclideanNorm (u (y, s))) ^ 2)) x := by
    intro x
    by_cases hx : x ∈ vec3Ball x₀ R
    · simp only [Set.indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_right (sq_nonneg _) (hη_le x)
    · have hηzero : η x = 0 := by
        apply le_antisymm
        · by_contra hne
          have hmem : x ∈ tsupport η :=
            subset_tsupport (f := η) (Function.mem_support.mpr
              (ne_of_gt (lt_of_not_ge hne)))
          have heu := (mem_euclideanBall_iff_vecEuclideanNorm_lt
            (lt_trans hr hrr)).mp (hη_support hmem)
          have heq : vecEuclideanNorm (x - x₀) = vec3EuclideanNorm (x - x₀) := by
            simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot]
            apply congrArg Real.sqrt
            apply Finset.sum_congr rfl
            intro i hi
            ring
          apply hx
          rw [mem_vec3Ball, ← heq]
          exact heu
        · exact hη_nonneg x
      simp [hηzero, hx]
  have hlin := (lintegral_mono (μ := (volume : Measure Vec3)) hpoint)
  rw [lintegral_indicator (vec3Ball_measurable x₀ R)] at hlin
  have htime : (∫⁻ x in vec3Ball x₀ R,
        ENNReal.ofReal ((vec3EuclideanNorm (u (x, s))) ^ 2)) =
      timeSliceBallEnergy x₀ R s (fun w => vec3EuclideanNorm (u w)) := by
    unfold timeSliceBallEnergy
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    rw [← Real.rpow_natCast]
    rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)]
    all_goals norm_num
  rw [htime] at hlin
  have hto := ENNReal.toReal_mono hS (hlin.trans houter)
  have hΩ : ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x =
      ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hne
    apply hx
    have hηne : η x ≠ 0 := by
      intro hzero
      exact hne (by simp [hzero])
    have hmem : x ∈ tsupport η :=
      subset_tsupport (f := η) (Function.mem_support.mpr hηne)
    exact hηΩ hmem
  calc
    ∫ x in Ω, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x =
        ∫ x, (vec3EuclideanNorm (u (x, s))) ^ 2 * η x := hΩ
    _ = (∫⁻ x, ENNReal.ofReal
        ((vec3EuclideanNorm (u (x, s))) ^ 2 * η x)).toReal := hreal
    _ ≤ S.toReal := hto

end CKN
