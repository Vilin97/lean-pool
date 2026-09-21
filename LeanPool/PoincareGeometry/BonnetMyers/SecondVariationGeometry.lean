/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Second Variation Geometry -/

noncomputable section

open Filter Set
open MeasureTheory
open scoped Topology ContDiff

namespace BonnetMyersEntry

/-- Cauchy--Schwarz for a nonnegative continuous speed on an interval. -/
theorem intervalIntegral_sq_le_length_mul_integral_sq
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Icc 0 L))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) L, 0 ≤ f t) :
    (∫ t in (0 : ℝ)..L, f t) ^ 2 ≤
      L * ∫ t in (0 : ℝ)..L, (f t) ^ 2 := by
  have hJ : (⨍ t in (0 : ℝ)..L, f t) ^ 2 ≤
      ⨍ t in (0 : ℝ)..L, (f t) ^ 2 := by
    have hu : uIoc (0 : ℝ) L = Ioc 0 L := uIoc_of_le hL.le
    letI : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) L)) :=
      hu.symm ▸ inferInstance
    letI : NeZero (volume.restrict (uIoc (0 : ℝ) L)) :=
      ⟨by
        rw [hu, ne_eq, Measure.restrict_eq_zero]
        simp only [Real.volume_Ioc, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
        exact hL⟩
    refine (convexOn_pow 2).map_average_le (continuousOn_pow 2)
      isClosed_Ici ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [hu] at ht
      exact hf0 t ⟨ht.1.le, ht.2⟩
    · rw [hu]
      change IntegrableOn f (Ioc 0 L) volume
      exact hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · rw [hu]
      change IntegrableOn ((fun x : ℝ ↦ x ^ 2) ∘ f) (Ioc 0 L) volume
      exact ((continuous_pow 2).comp_continuousOn hf).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  rw [interval_average_eq, interval_average_eq] at hJ
  have hL0 : L ≠ 0 := ne_of_gt hL
  simp only [smul_eq_mul, sub_zero] at hJ
  field_simp [hL0] at hJ
  exact hJ

/-- A path whose scalar speed integrates to at least the interval length has
at least unit-speed energy. -/
theorem length_le_intervalIntegral_sq_of_length_le_integral
    {speed : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hspeed : ContinuousOn speed (Icc 0 L))
    (hspeed0 : ∀ t ∈ Icc (0 : ℝ) L, 0 ≤ speed t)
    (hlength : L ≤ ∫ t in (0 : ℝ)..L, speed t) :
    L ≤ ∫ t in (0 : ℝ)..L, (speed t) ^ 2 := by
  have hcs := intervalIntegral_sq_le_length_mul_integral_sq
    hL hspeed hspeed0
  have hsq : L ^ 2 ≤ (∫ t in (0 : ℝ)..L, speed t) ^ 2 := by
    nlinarith
  nlinarith

/-! ### Broken-path energy estimates

A chartwise variation of a long geodesic is naturally only piecewise smooth
in the time variable.  The following finite Cauchy--Schwarz estimate is the
precise replacement for applying the integral inequality to one globally
continuous speed. -/

/-- If the total length of finitely many path pieces is at least their total
time and each piece satisfies the usual length--energy Cauchy--Schwarz
estimate, then the total energy is at least the total time. -/
theorem sum_duration_le_sum_energy_of_sum_duration_le_sum_length
    {ι : Type*} {S : Finset ι}
    {duration length energy : ι → ℝ}
    (hduration : ∀ i ∈ S, 0 < duration i)
    (hlength : ∀ i ∈ S, 0 ≤ length i)
    (hpiece : ∀ i ∈ S,
      (length i) ^ 2 ≤ duration i * energy i)
    (htotal : (∑ i ∈ S, duration i) ≤ ∑ i ∈ S, length i) :
    (∑ i ∈ S, duration i) ≤ ∑ i ∈ S, energy i := by
  have henergy : ∀ i ∈ S, 0 ≤ energy i := by
    intro i hi
    have hsquare : 0 ≤ (length i) ^ 2 := sq_nonneg _
    have hproduct : 0 ≤ duration i * energy i := hsquare.trans (hpiece i hi)
    exact nonneg_of_mul_nonneg_right hproduct (hduration i hi)
  have hcs : (∑ i ∈ S, length i) ^ 2 ≤
      (∑ i ∈ S, duration i) * ∑ i ∈ S, energy i :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun i hi ↦ (hduration i hi).le) henergy hpiece
  have hduration_sum : 0 ≤ ∑ i ∈ S, duration i :=
    Finset.sum_nonneg (fun i hi ↦ (hduration i hi).le)
  have hlength_sum : 0 ≤ ∑ i ∈ S, length i :=
    Finset.sum_nonneg hlength
  have henergy_sum : 0 ≤ ∑ i ∈ S, energy i :=
    Finset.sum_nonneg henergy
  by_cases hzero : (∑ i ∈ S, duration i) = 0
  · rw [hzero]
    exact henergy_sum
  · have hpositive : 0 < ∑ i ∈ S, duration i :=
      lt_of_le_of_ne hduration_sum (Ne.symm hzero)
    have hsquare : (∑ i ∈ S, duration i) ^ 2 ≤
        (∑ i ∈ S, length i) ^ 2 := by
      nlinarith
    nlinarith

/-- Finite-piece form of the length--energy estimate.  Each piece may have
its own continuous speed and its own parameter interval; no continuity is
required where adjacent pieces meet. -/
theorem sum_duration_le_sum_intervalIntegral_sq_of_broken_length_lower_bound
    {ι : Type*} {S : Finset ι}
    {a b : ι → ℝ} {speed : ι → ℝ → ℝ}
    (hab : ∀ i ∈ S, a i < b i)
    (hspeed : ∀ i ∈ S, ContinuousOn (speed i) (Icc (a i) (b i)))
    (hspeed0 : ∀ i ∈ S, ∀ t ∈ Icc (a i) (b i), 0 ≤ speed i t)
    (hlength : (∑ i ∈ S, (b i - a i)) ≤
      ∑ i ∈ S, ∫ t in a i..b i, speed i t) :
    (∑ i ∈ S, (b i - a i)) ≤
      ∑ i ∈ S, ∫ t in a i..b i, (speed i t) ^ 2 := by
  apply sum_duration_le_sum_energy_of_sum_duration_le_sum_length
    (ι := ι) (S := S) (duration := fun i ↦ b i - a i)
    (length := fun i ↦ ∫ t in a i..b i, speed i t)
    (energy := fun i ↦ ∫ t in a i..b i, (speed i t) ^ 2)
  · intro i hi
    exact sub_pos.mpr (hab i hi)
  · intro i hi
    exact intervalIntegral.integral_nonneg (hab i hi).le
      (fun t ht ↦ hspeed0 i hi t ht)
  · intro i hi
    have h := intervalIntegral_sq_le_length_mul_integral_sq
      (f := fun t ↦ speed i (t + a i)) (sub_pos.mpr (hab i hi))
      ((hspeed i hi).comp (continuous_id.add continuous_const).continuousOn
        (fun t ht ↦ by constructor <;> linarith [ht.1, ht.2]))
      (fun t ht ↦ hspeed0 i hi (t + a i) (by
        constructor <;> linarith [ht.1, ht.2]))
    calc
      (∫ t in a i..b i, speed i t) ^ 2 =
          (∫ t in (0 : ℝ)..b i - a i, speed i (t + a i)) ^ 2 := by
        rw [intervalIntegral.integral_comp_add_right]
        simp only [zero_add, sub_add_cancel]
      _ ≤ (b i - a i) *
          ∫ t in (0 : ℝ)..b i - a i, (speed i (t + a i)) ^ 2 := h
      _ = (b i - a i) * ∫ t in a i..b i, (speed i t) ^ 2 := by
        congr 1
        have hshift := intervalIntegral.integral_comp_add_right
          (fun x : ℝ ↦ (speed i x) ^ 2) (a i)
          (a := (0 : ℝ)) (b := b i - a i)
        simpa only [zero_add, sub_add_cancel] using hshift
  · exact hlength

/-- At a twice continuously differentiable local minimum, the second
iterated derivative is nonnegative.  Only local `C²` regularity at the
minimum is needed. -/
theorem iteratedDeriv_two_nonneg_of_isLocalMin
    {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hmin : IsLocalMin f 0) :
    0 ≤ iteratedDeriv 2 f 0 := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (2 : ℕ∞ω)) le_rfl (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.mp hu
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let s : Set ℝ := Icc (-δ) δ
  have hsconv : Convex ℝ s := convex_Icc _ _
  have hzeros : (0 : ℝ) ∈ s := by simp [s, hδ.le]
  have hsu : s ⊆ u := by
    intro x hx
    apply hεu
    rw [Metric.mem_ball, Real.dist_0_eq_abs]
    rw [abs_lt]
    constructor <;> dsimp [s, δ] at hx ⊢ <;> linarith [hx.1, hx.2]
  have hfs : ContDiffOn ℝ 2 f s := hfu.mono hsu
  have hsnhds : s ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Metric.ball_mem_nhds 0 hδ)
    intro x hx
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_lt] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hfirst : deriv f 0 = 0 := hmin.deriv_eq_zero
  have ht := taylor_tendsto (f := f) (x₀ := (0 : ℝ)) (n := 2)
    hsconv hzeros hfs
  rw [nhdsWithin_eq_nhds.2 hsnhds] at ht
  have hunique : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by linarith)
  have hformula : ∀ x : ℝ,
      taylorWithinEval f 2 s 0 x =
        f 0 + x * deriv f 0 + (x ^ 2 / 2) * iteratedDeriv 2 f 0 := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      inv_one, pow_zero, pow_one, one_mul, sub_zero,
      iteratedDeriv_zero, iteratedDeriv_one,
      smul_eq_mul, zero_add]
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (hf.of_le (by norm_num)) hzeros]
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (hf.of_le (by norm_num)) hzeros]
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique hf hzeros]
    simp only [iteratedDeriv_zero, iteratedDeriv_one]
    ring
  have hlim : Tendsto
      (fun x : ℝ ↦ (x ^ 2)⁻¹ * (f x - f 0))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((2 : ℝ)⁻¹ * iteratedDeriv 2 f 0)) := by
    have ht' : Tendsto
        (fun x : ℝ ↦ (x ^ 2)⁻¹ *
          (f x - taylorWithinEval f 2 s 0 x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [sub_zero, smul_eq_mul] using
        ht.mono_left nhdsWithin_le_nhds
    have heq : (fun x : ℝ ↦ (x ^ 2)⁻¹ * (f x - f 0)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun x : ℝ ↦ (x ^ 2)⁻¹ *
          (f x - taylorWithinEval f 2 s 0 x) +
            (2 : ℝ)⁻¹ * iteratedDeriv 2 f 0) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [hformula, hfirst]
      have hx0 : x ≠ 0 := ne_of_gt hx
      field_simp
      ring
    have hc : Tendsto (fun _ : ℝ ↦ (2 : ℝ)⁻¹ * iteratedDeriv 2 f 0)
        (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ)⁻¹ * iteratedDeriv 2 f 0)) :=
      tendsto_const_nhds
    simpa only [zero_add] using (ht'.add hc).congr' heq.symm
  have hnonneg : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      0 ≤ (x ^ 2)⁻¹ * (f x - f 0) := by
    have hmin' : ∀ᶠ x in 𝓝 (0 : ℝ), f 0 ≤ f x := hmin
    filter_upwards [hmin'.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x hfx hx
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg x)) (sub_nonneg.mpr hfx)
  have hhalf : 0 ≤ (2 : ℝ)⁻¹ * iteratedDeriv 2 f 0 :=
    ge_of_tendsto hlim hnonneg
  nlinarith

/-- Analytic variational backbone: endpoint minimization forces the second
derivative of a smooth energy family to be nonnegative. -/
theorem energy_secondVariation_nonnegative_of_length_lower_bound
    {speed : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hspeed : ∀ e, ContinuousOn (speed e) (Icc 0 L))
    (hspeed_nonneg : ∀ e t, t ∈ Icc (0 : ℝ) L → 0 ≤ speed e t)
    (hspeed_zero : ∀ t ∈ Icc (0 : ℝ) L, speed 0 t = 1)
    (hlength : ∀ e, L ≤ ∫ t in (0 : ℝ)..L, speed e t)
    (henergy : ContDiff ℝ 2
      (fun e ↦ (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..L, (speed e t) ^ 2)) :
    0 ≤ iteratedDeriv 2
      (fun e ↦ (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..L, (speed e t) ^ 2) 0 := by
  let energy : ℝ → ℝ := fun e ↦
    (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..L, (speed e t) ^ 2
  have henergy_zero : energy 0 = L / 2 := by
    have hInt : (∫ t in (0 : ℝ)..L, (speed 0 t) ^ 2) = L := by
      calc
        (∫ t in (0 : ℝ)..L, (speed 0 t) ^ 2) =
            ∫ _t in (0 : ℝ)..L, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Icc (0 : ℝ) L := by
            simpa [uIcc_of_le hL.le] using ht
          change speed 0 t ^ 2 = (1 : ℝ)
          rw [hspeed_zero t ht', one_pow]
        _ = L := by simp
    change (2 : ℝ)⁻¹ * (∫ t in (0 : ℝ)..L, (speed 0 t) ^ 2) = L / 2
    rw [hInt]
    ring
  have hminimum : IsLocalMin energy 0 := by
    apply Filter.Eventually.of_forall
    intro e
    have hlower : L ≤ ∫ t in (0 : ℝ)..L, (speed e t) ^ 2 :=
      length_le_intervalIntegral_sq_of_length_le_integral hL
        (hspeed e) (hspeed_nonneg e) (hlength e)
    rw [henergy_zero]
    change L / 2 ≤ (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..L, (speed e t) ^ 2
    nlinarith
  change 0 ≤ iteratedDeriv 2 energy 0
  exact iteratedDeriv_two_nonneg_of_isLocalMin
    (show ContDiffAt ℝ 2 energy 0 from henergy.contDiffAt) hminimum

/-- Analytic second-variation backbone for a finite broken path.  The path
pieces need only have continuous speed separately.  If their endpoints splice
to an endpoint-fixed competitor, its minimizing length lower bound implies a
nonnegative second derivative of the sum of the piece energies. -/
theorem brokenEnergy_secondVariation_nonnegative_of_length_lower_bound
    {ι : Type*} {S : Finset ι} {a b : ι → ℝ}
    {speed : ℝ → ι → ℝ → ℝ} {L : ℝ}
    (hab : ∀ i ∈ S, a i < b i)
    (hduration : (∑ i ∈ S, (b i - a i)) = L)
    (hspeed : ∀ e i, i ∈ S →
      ContinuousOn (speed e i) (Icc (a i) (b i)))
    (hspeed_nonneg : ∀ e i, i ∈ S → ∀ t ∈ Icc (a i) (b i),
      0 ≤ speed e i t)
    (hspeed_zero : ∀ i, i ∈ S → ∀ t ∈ Icc (a i) (b i),
      speed 0 i t = 1)
    (hlength : ∀ e, L ≤
      ∑ i ∈ S, ∫ t in a i..b i, speed e i t)
    (henergy : ContDiff ℝ 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2)) :
    0 ≤ iteratedDeriv 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2) 0 := by
  let energy : ℝ → ℝ := fun e ↦ (2 : ℝ)⁻¹ *
    ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2
  have henergy_zero : energy 0 = L / 2 := by
    have hpiece : ∀ i ∈ S,
        (∫ t in a i..b i, (speed 0 i t) ^ 2) = b i - a i := by
      intro i hi
      calc
        (∫ t in a i..b i, (speed 0 i t) ^ 2) =
            ∫ _t in a i..b i, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Icc (a i) (b i) := by
            simpa [uIcc_of_le (hab i hi).le] using ht
          change speed 0 i t ^ 2 = (1 : ℝ)
          rw [hspeed_zero i hi t ht', one_pow]
        _ = b i - a i := by simp
    have hsum :
        (∑ i ∈ S, ∫ t in a i..b i, (speed 0 i t) ^ 2) =
          ∑ i ∈ S, (b i - a i) := by
      exact Finset.sum_congr rfl hpiece
    change (2 : ℝ)⁻¹ *
      (∑ i ∈ S, ∫ t in a i..b i, (speed 0 i t) ^ 2) = L / 2
    rw [hsum, hduration]
    ring
  have hminimum : IsLocalMin energy 0 := by
    apply Filter.Eventually.of_forall
    intro e
    have hlower : L ≤
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2 := by
      rw [← hduration]
      exact sum_duration_le_sum_intervalIntegral_sq_of_broken_length_lower_bound
        (S := S) hab (fun i hi ↦ hspeed e i hi)
          (fun i hi ↦ hspeed_nonneg e i hi) (by simpa [hduration] using hlength e)
    rw [henergy_zero]
    change L / 2 ≤ (2 : ℝ)⁻¹ *
      ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2
    nlinarith
  change 0 ≤ iteratedDeriv 2 energy 0
  exact iteratedDeriv_two_nonneg_of_isLocalMin
    (show ContDiffAt ℝ 2 energy 0 from henergy.contDiffAt) hminimum

/-- Local-in-the-variation-parameter form of the broken-path argument.  A
chart variation only has to remain inside its chart for sufficiently small
parameters, so continuity, nonnegativity of speed, and endpoint minimality
are naturally neighbourhood assumptions rather than global ones. -/
theorem brokenEnergy_secondVariation_nonnegative_of_eventually_length_lower_bound
    {ι : Type*} {S : Finset ι} {a b : ι → ℝ}
    {speed : ℝ → ι → ℝ → ℝ} {L : ℝ}
    (hab : ∀ i ∈ S, a i < b i)
    (hduration : (∑ i ∈ S, (b i - a i)) = L)
    (hspeed : ∀ᶠ e in nhds (0 : ℝ), ∀ i, i ∈ S →
      ContinuousOn (speed e i) (Icc (a i) (b i)))
    (hspeed_nonneg : ∀ᶠ e in nhds (0 : ℝ), ∀ i, i ∈ S →
      ∀ t ∈ Icc (a i) (b i), 0 ≤ speed e i t)
    (hspeed_zero : ∀ i, i ∈ S → ∀ t ∈ Icc (a i) (b i),
      speed 0 i t = 1)
    (hlength : ∀ᶠ e in nhds (0 : ℝ), L ≤
      ∑ i ∈ S, ∫ t in a i..b i, speed e i t)
    (henergy : ContDiffAt ℝ 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2) 0) :
    0 ≤ iteratedDeriv 2
      (fun e ↦ (2 : ℝ)⁻¹ *
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2) 0 := by
  let energy : ℝ → ℝ := fun e ↦ (2 : ℝ)⁻¹ *
    ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2
  have henergy_zero : energy 0 = L / 2 := by
    have hpiece : ∀ i ∈ S,
        (∫ t in a i..b i, (speed 0 i t) ^ 2) = b i - a i := by
      intro i hi
      calc
        (∫ t in a i..b i, (speed 0 i t) ^ 2) =
            ∫ _t in a i..b i, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Icc (a i) (b i) := by
            simpa [uIcc_of_le (hab i hi).le] using ht
          change speed 0 i t ^ 2 = (1 : ℝ)
          rw [hspeed_zero i hi t ht', one_pow]
        _ = b i - a i := by simp
    have hsum :
        (∑ i ∈ S, ∫ t in a i..b i, (speed 0 i t) ^ 2) =
          ∑ i ∈ S, (b i - a i) :=
      Finset.sum_congr rfl hpiece
    change (2 : ℝ)⁻¹ *
      (∑ i ∈ S, ∫ t in a i..b i, (speed 0 i t) ^ 2) = L / 2
    rw [hsum, hduration]
    ring
  have hminimum : IsLocalMin energy 0 := by
    filter_upwards [hspeed, hspeed_nonneg, hlength] with e hspeed_e hnonneg_e hlength_e
    have hlower : L ≤
        ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2 := by
      rw [← hduration]
      exact sum_duration_le_sum_intervalIntegral_sq_of_broken_length_lower_bound
        (S := S) hab (fun i hi ↦ hspeed_e i hi)
          (fun i hi ↦ hnonneg_e i hi)
          (by simpa [hduration] using hlength_e)
    rw [henergy_zero]
    change L / 2 ≤ (2 : ℝ)⁻¹ *
      ∑ i ∈ S, ∫ t in a i..b i, (speed e i t) ^ 2
    nlinarith
  change 0 ≤ iteratedDeriv 2 energy 0
  exact iteratedDeriv_two_nonneg_of_isLocalMin
    (show ContDiffAt ℝ 2 energy 0 from henergy) hminimum

end BonnetMyersEntry
