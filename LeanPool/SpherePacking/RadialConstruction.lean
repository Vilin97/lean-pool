/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.HarmonicAnalysis
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# RadialConstruction

Construction of radial admissible witnesses and sharp asymptotics.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def SaddleSourceSchwartzRealization : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (ε ^ 3) ≤ (10 * Real.log (1 / ε)) →
      ∀ d : ℕ, 0 < d →
        ∃ fminus fplus : TestFunction d,
          (∀ x : Euclidean d,
            fminus x = minusSaddleFunction ε d x) ∧
          (∀ x : Euclidean d,
            fplus x = plusSaddleFunction ε d x)

private noncomputable def SaddleSourceEventualSigns : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop,
      (∀ x : Euclidean d,
        0 ≤ (plusSaddleFunction ε d x).re) ∧
      (∀ x : Euclidean d,
        saddleSourceRadius ε d ≤ ‖x‖ →
          (minusSaddleFunction ε d x).re ≤ 0)

private noncomputable def saddleOrderedUpperConstruction
    (hschwartz : SaddleSourceSchwartzRealization)
    (hsigns : SaddleSourceEventualSigns) :
    OrderedEpsilonUpperConstruction := by
  have heventually :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        (ε ^ 3) ≤ (10 * Real.log (1 / ε)) ∧
          (∀ᶠ d : ℕ in atTop,
            (∀ x : Euclidean d,
              0 ≤ (plusSaddleFunction ε d x).re) ∧
            (∀ x : Euclidean d,
              saddleSourceRadius ε d ≤ ‖x‖ →
                (minusSaddleFunction ε d x).re ≤ 0)) :=
    eventually_upper_shortCutoff_le_shortEndpoint.and hsigns
  have hmembership :
      {ε : ℝ |
        (ε ^ 3) ≤ (10 * Real.log (1 / ε)) ∧
          (∀ᶠ d : ℕ in atTop,
            (∀ x : Euclidean d,
              0 ≤ (plusSaddleFunction ε d x).re) ∧
            (∀ x : Euclidean d,
              saddleSourceRadius ε d ≤ ‖x‖ →
                (minusSaddleFunction ε d x).re ≤ 0))} ∈
        𝓝[>] (0 : ℝ) := heventually
  have hexists :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hmembership
  let ε₀ : ℝ := Classical.choose hexists
  have hchosen := Classical.choose_spec hexists
  have hε₀ : 0 < ε₀ := hchosen.1
  have hinterval := hchosen.2
  refine
    { epsilonBound := ε₀
      epsilonBound_pos := hε₀
      normalizedRadius := fun ε d =>
        saddleSourceRadius ε d / Real.sqrt (d : ℝ)
      limitingRadius := limitingSaddleRadius
      limitingRadius_tendsto := tendsto_limitingSaddleRadius
      normalizedRadius_tendsto := ?_
      admissibleWitness := ?_ }
  · intro ε hε _hsmall
    exact tendsto_saddleSourceRadius_normalized hε
  · intro ε hε hsmall
    have hproperties := hinterval
      (show ε ∈ Ioo (0 : ℝ) ε₀ from ⟨hε, hsmall⟩)
    obtain ⟨horder, hsignε⟩ := hproperties
    filter_upwards [hsignε, eventually_gt_atTop (0 : ℕ)]
      with d hsign hd
    obtain ⟨fminus, fplus, hminus, hplus⟩ :=
      hschwartz ε hε horder d hd
    let f : Admissible d :=
      saddleSourceAdmissible hε hd horder
        (saddleSourceRadius_pos ε d)
        fminus fplus hminus hplus hsign.1 hsign.2
    refine ⟨f, ?_⟩
    exact le_of_eq (saddleSourceAdmissible_normalizedCost
      hε hd horder (saddleSourceRadius_pos ε d)
      fminus fplus hminus hplus hsign.1 hsign.2)

end

section

open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def lowerGammaBoundaryCapped (ℓ R D y : ℝ) : ℝ :=
  if y = 0 then D else min (lowerGammaBoundaryLog ℓ R y) D

private theorem lowerGammaBoundaryLog_pole_decomposition
    (ℓ R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ℓ R y =
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ -
        Real.log (|y| / 2) := by
  let s : ℂ := -Complex.I * (y : ℂ) / 2
  have hs : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    try dsimp [s] at him
    norm_num at him
    exact hy (by linarith)
  have hgammas : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have him := congrArg Complex.im hm
    try dsimp [s] at him
    norm_num at him
    exact hy (by linarith)
  have hnorm :
      ‖Complex.Gamma (s + 1)‖ =
        ‖s‖ * ‖Complex.Gamma s‖ := by
    rw [Complex.Gamma_add_one s hs, norm_mul]
  have hs_norm : ‖s‖ = |y| / 2 := by
    simp only [neg_mul, Complex.norm_div, norm_neg, Complex.norm_mul, Complex.norm_I,
      Complex.norm_real,
      Real.norm_eq_abs, one_mul, Complex.norm_ofNat, s]
  have hlog :
      Real.log ‖Complex.Gamma s‖ =
        Real.log ‖Complex.Gamma (s + 1)‖ -
          Real.log (|y| / 2) := by
    rw [hnorm, Real.log_mul
      (norm_ne_zero_iff.mpr hs)
      (norm_ne_zero_iff.mpr hgammas), hs_norm]
    ring
  have harg : s + 1 = 1 - Complex.I * (y : ℂ) / 2 := by
    try dsimp [s]
    ring
  unfold lowerGammaBoundaryLog
  change
    ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma s‖ -
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖ = _
  rw [hlog, harg]
  ring

private theorem lowerGammaBoundaryLog_tendsto_atTop_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Tendsto (lowerGammaBoundaryLog ℓ R)
      (𝓝[≠] (0 : ℝ)) atTop := by
  have hlogbot :
      Tendsto (fun y : ℝ => Real.log (|y| / 2))
        (𝓝[≠] (0 : ℝ)) atBot := by
    have hshift :=
      Real.tendsto_log_nhdsNE_zero.atBot_add
        (tendsto_const_nhds (x := -(Real.log (2 : ℝ))))
    apply hshift.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyzero : y ≠ 0 := by
      simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! hy
    rw [Real.log_div
      (abs_ne_zero.mpr hyzero) (by norm_num), Real.log_abs]
    ring
  have hnumPole :
      ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hdenPole :
      ∀ m : ℕ, (ℓ : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnumGamma :
      ContinuousAt (fun y : ℝ =>
        Complex.Gamma (1 - Complex.I * (y : ℂ) / 2)) 0 := by
    apply (Complex.continuousAt_Gamma (1 : ℂ)
      hnumPole).comp_of_eq
    · fun_prop
    · norm_num
  have hdenGamma :
      ContinuousAt (fun y : ℝ =>
        Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) 0 := by
    apply (Complex.continuousAt_Gamma (ℓ : ℂ)
      hdenPole).comp_of_eq
    · fun_prop
    · norm_num
  have hnumLog :
      ContinuousAt (fun y : ℝ =>
        Real.log ‖Complex.Gamma
          (1 - Complex.I * (y : ℂ) / 2)‖) 0 := by
    apply hnumGamma.norm.log
    simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero, Complex.Gamma_one, norm_one,
      ne_eq, one_ne_zero,
      not_false_eq_true]
  have hdenLog :
      ContinuousAt (fun y : ℝ =>
        Real.log ‖Complex.Gamma
          ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) 0 := by
    apply hdenGamma.norm.log
    simpa only [Complex.ofReal_zero, mul_zero, zero_div, add_zero, ne_eq,
      norm_eq_zero] using! norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero hdenPole)
  have hregular :
      ContinuousAt (fun y : ℝ =>
        ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma
            (1 - Complex.I * (y : ℂ) / 2)‖ -
          Real.log ‖Complex.Gamma
            ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) 0 :=
    (continuousAt_const.add hnumLog).sub hdenLog
  have hreglimit :
      Tendsto (fun y : ℝ =>
        ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma
            (1 - Complex.I * (y : ℂ) / 2)‖ -
          Real.log ‖Complex.Gamma
            ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (ℓ * Real.log (Real.pi * R ^ 2) +
          Real.log ‖Complex.Gamma (1 : ℂ)‖ -
          Real.log ‖Complex.Gamma (ℓ : ℂ)‖)) := by
    convert! hregular.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ)) using 1;
        norm_num
  have hnegative :
      Tendsto (fun y : ℝ => -Real.log (|y| / 2))
        (𝓝[≠] (0 : ℝ)) atTop :=
    tendsto_neg_atTop_iff.mpr hlogbot
  have hsum := hnegative.atTop_add hreglimit
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyzero : y ≠ 0 := by
    simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! hy
  rw [lowerGammaBoundaryLog_pole_decomposition ℓ R hyzero]
  ring

private theorem lowerGammaBoundaryCapped_continuous
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R D : ℝ) :
    Continuous (lowerGammaBoundaryCapped ℓ R D) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst y
    have htail :
        ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
          D ≤ lowerGammaBoundaryLog ℓ R x :=
      (lowerGammaBoundaryLog_tendsto_atTop_zero
        hℓ R).eventually_ge_atTop D
    have hnear :
        ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
          x ≠ 0 → D ≤ lowerGammaBoundaryLog ℓ R x := by
      have h := (eventually_nhdsWithin_iff.mp htail)
      filter_upwards [h] with x hx
      intro hxzero
      apply hx
      simpa only [mem_compl_iff, mem_singleton_iff, ne_eq] using! hxzero
    have hconstant :
        ContinuousAt (fun _ : ℝ => D) (0 : ℝ) :=
      continuousAt_const
    apply hconstant.congr_of_eventuallyEq
    filter_upwards [hnear] with x hx
    unfold lowerGammaBoundaryCapped
    split_ifs with hzero
    · rfl
    · exact min_eq_right (hx hzero)
  · have hopen : IsOpen ({(0 : ℝ)}ᶜ) :=
      isClosed_singleton.isOpen_compl
    have hmem : y ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := by
      simpa only [mem_compl_iff, mem_singleton_iff] using! hy
    have hregular :
        ContinuousAt (lowerGammaBoundaryLog ℓ R) y := by
      apply (lowerGammaBoundaryLog_continuousOn hℓ R
        (S := {(0 : ℝ)}ᶜ)
        (by
          intro x hx
          simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! hx)).continuousAt
      exact hopen.mem_nhds hmem
    have hmin :
        ContinuousAt (fun x : ℝ =>
          min (lowerGammaBoundaryLog ℓ R x) D) y :=
      hregular.min continuousAt_const
    apply hmin.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hy] with x hx
    simp only [lowerGammaBoundaryCapped, hx, ↓reduceIte]

private theorem lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
    {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (R D : ℝ)
    (hgamma : Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) * lowerGammaBoundaryLog ℓ R y)) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped ℓ R D y) := by
  have hgammaabs : Integrable
      (fun y : ℝ =>
        Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y|) := by
    simpa only [neg_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using! hgamma.norm
  have hbase := strip_exp_abs_integrable ha
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y| +
        |D| * Real.exp ((-a) * |y|)) :=
    hgammaabs.add (hbase.const_mul |D|)
  have hweight : Continuous
      (fun y : ℝ => Real.exp ((-a) * |y|)) := by
    fun_prop
  apply hmajor.mono'
    ((hweight.mul
      (lowerGammaBoundaryCapped_continuous
        hℓ R D)).aestronglyMeasurable)
  filter_upwards [Measure.ae_ne
    (volume : Measure ℝ) 0] with y hy
  have hcap :
      |lowerGammaBoundaryCapped ℓ R D y| ≤
        |lowerGammaBoundaryLog ℓ R y| + |D| := by
    unfold lowerGammaBoundaryCapped
    rw [ite_eq_right hy]
    rcases le_total (lowerGammaBoundaryLog ℓ R y) D
      with hleft | hright
    · rw [min_eq_left hleft]
      exact le_add_of_nonneg_right (abs_nonneg D)
    · rw [min_eq_right hright]
      exact le_add_of_nonneg_left
        (abs_nonneg (lowerGammaBoundaryLog ℓ R y))
  change
    |Real.exp ((-a) * |y|) *
      lowerGammaBoundaryCapped ℓ R D y| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * |y|) *
        |lowerGammaBoundaryCapped ℓ R D y| ≤
      Real.exp ((-a) * |y|) *
        (|lowerGammaBoundaryLog ℓ R y| + |D|) :=
      mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
    _ = Real.exp ((-a) * |y|) *
          |lowerGammaBoundaryLog ℓ R y| +
        |D| * Real.exp ((-a) * |y|) := by
      ring

private theorem stripRegularizedOuter_integrable_of_exp_integrable
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) * b y)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ z y *
          (b y : ℂ)) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  let a : ℝ := Real.pi / (2 * ℓ)
  let D : ℝ :=
    2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))
  let Cpos : ℝ := Real.exp (a * z.re) / D
  let Cneg : ℝ := Real.exp (-a * z.re) / D
  have ha : 0 < a := by
    try dsimp [a]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  change Integrable
    (fun y : ℝ =>
      Real.exp ((-a) * |y|) * b y)
    at hboundary
  have hboundaryabs :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) * |b y|) := by
    simpa only [neg_mul, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using! hboundary.norm
  have hposfactor (y : ℝ) :
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D =
        Cpos * Real.exp ((-a) * y) := by
    have hsplit :
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) =
          Real.exp (a * z.re) * Real.exp ((-a) * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cpos]
    ring
  have hnegfactor (y : ℝ) :
      Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D =
        Cneg * Real.exp (a * y) := by
    have hsplit :
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) =
          Real.exp (-a * z.re) * Real.exp (a * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cneg]
    ring
  have hboundaryRight :
      ContinuousOn b (Ioi (0 : ℝ)) :=
    hb.continuousOn
  have hcastRight :
      ContinuousOn
        (fun y : ℝ => (b y : ℂ))
        (Ioi (0 : ℝ)) := by
    simpa only [comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hboundaryRight
  have hcontinuousRight :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Ioi (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
      hℓ hz).mul hcastRight
  have hrightmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cpos *
            (Real.exp ((-a) * |y|) *
              |b y|))
        (Ioi (0 : ℝ)) :=
    hboundaryabs.integrableOn.const_mul Cpos
  have hright :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Ioi (0 : ℝ)) := by
    apply hrightmajorant.mono'
      (hcontinuousRight.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (b y : ℂ)‖ ≤
        Cpos *
          (Real.exp ((-a) * |y|) *
            |b y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
        hℓ hz (mem_Ioi.mp hy).le
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |b y| ≤
        (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D) *
          |b y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cpos *
          (Real.exp ((-a) * |y|) *
            |b y|) := by
        rw [abs_of_pos (mem_Ioi.mp hy), hposfactor]
        ring
  have hboundaryLeft :
      ContinuousOn b (Iio (0 : ℝ)) :=
    hb.continuousOn
  have hcastLeft :
      ContinuousOn
        (fun y : ℝ => (b y : ℂ))
        (Iio (0 : ℝ)) := by
    simpa only [comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hboundaryLeft
  have hcontinuousLeft :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Iio (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
      hℓ hz).mul hcastLeft
  have hleftmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cneg *
            (Real.exp ((-a) * |y|) *
              |b y|))
        (Iio (0 : ℝ)) :=
    hboundaryabs.integrableOn.const_mul Cneg
  have hleft :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ))
        (Iio (0 : ℝ)) := by
    apply hleftmajorant.mono'
      (hcontinuousLeft.aestronglyMeasurable measurableSet_Iio)
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (b y : ℂ)‖ ≤
        Cneg *
          (Real.exp ((-a) * |y|) *
            |b y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_neg
        hℓ hz (mem_Iio.mp hy)
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |b y| ≤
        (Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D) *
          |b y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cneg *
          (Real.exp ((-a) * |y|) *
            |b y|) := by
        rw [abs_of_neg (mem_Iio.mp hy), hnegfactor]
        simp only [mul_neg, neg_mul, neg_neg]
        ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private noncomputable def stripRegularizedOuter (ℓ : ℝ) (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ,
    stripRegularizedHolomorphicPoissonKernel ℓ z y *
      (b y : ℂ)

private theorem stripRegularizedOuter_differentiableAt_of_exp_integrable
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) * b y)) :
    DifferentiableAt ℂ (stripRegularizedOuter ℓ b) z := by
  obtain ⟨S, hS, C, hC, hderivbound⟩ :=
    stripRegularizedHolomorphicPoissonKernelDeriv_local_bound hℓ hz
  have hstrip :
      Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z := by
    have him : Continuous (fun w : ℂ => w.im) := by
      fun_prop
    exact (isOpen_Ioo.preimage him).mem_nhds hz
  have hneighborhood :
      S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ) ∈ 𝓝 z :=
    inter_mem hS hstrip
  have hboundaryabs :
      Integrable
        (fun y : ℝ =>
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|) := by
    simpa only [neg_mul, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] using! hboundary.norm
  have hboundintegrable :
      Integrable
        (fun y : ℝ =>
          C * (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|)) :=
    hboundaryabs.const_mul C
  have hFmeas :
      ∀ᶠ w : ℂ in 𝓝 z,
        AEStronglyMeasurable
          (fun y : ℝ =>
            stripRegularizedHolomorphicPoissonKernel ℓ w y *
              (b y : ℂ)) := by
    filter_upwards [hstrip] with w hw
    exact
      (stripRegularizedOuter_integrable_of_exp_integrable
        hℓ hw b hb hboundary).aestronglyMeasurable
  have hFint :
      Integrable
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (b y : ℂ)) :=
    stripRegularizedOuter_integrable_of_exp_integrable hℓ hz b hb hboundary
  have hGmeas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y *
            (b y : ℂ)) := by
    have hreal := hb.measurable
    have hcast :
        Measurable (fun y : ℝ => (b y : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp hreal
    exact
      ((stripRegularizedHolomorphicPoissonKernelDeriv_continuous
        hℓ hz).measurable.mul hcast).aestronglyMeasurable
  have hdominated :
      ∀ᵐ y : ℝ, ∀ w ∈ S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ),
        ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
          (b y : ℂ)‖ ≤
            C *
              (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
                |b y|) := by
    filter_upwards [] with y
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ *
          |b y| ≤
        (C * Real.exp (-(Real.pi / (2 * ℓ)) * |y|)) *
          |b y| :=
        mul_le_mul_of_nonneg_right
          (hderivbound w hw.1 y) (abs_nonneg _)
      _ = C *
          (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
            |b y|) := by
        ring
  have hdiff :
      ∀ᵐ y : ℝ, ∀ w ∈ S ∩ (Complex.im ⁻¹' Ioo (-ℓ) ℓ),
        HasDerivAt
          (fun v : ℂ =>
            stripRegularizedHolomorphicPoissonKernel ℓ v y *
              (b y : ℂ))
          (stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
            (b y : ℂ)) w := by
    filter_upwards [] with y
    intro w hw
    exact
      (stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
        hℓ hw.2 y).mul_const (b y : ℂ)
  have hresult :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w : ℂ => fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ w y *
          (b y : ℂ))
      (F' := fun w : ℂ => fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y *
          (b y : ℂ))
      (bound := fun y : ℝ =>
        C * (Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
          |b y|))
      hneighborhood hFmeas hFint hGmeas
      hdominated hboundintegrable hdiff
  unfold stripRegularizedOuter
  exact hresult.2.differentiableAt

private noncomputable def lowerStripCappedGammaOuter
    (ℓ R D : ℝ) (z : ℂ) : ℂ :=
  stripRegularizedOuter ℓ
    (lowerGammaBoundaryCapped ℓ R D) z

private theorem lowerGammaBoundaryCapped_exp_integrable_dimension
    {d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 < a) (R D : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  apply lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
    hℓ ha R D
  exact lowerGammaBoundaryLog_dimension_exp_integrable
    hd ha R

private theorem lowerStripCappedGammaOuter_integrable_dimension
    {d : ℕ} (hd : 0 < d) {R D : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹'
      Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2) z y *
          (lowerGammaBoundaryCapped
            ((d : ℝ) / 2) R D y : ℂ)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < Real.pi / (2 * ((d : ℝ) / 2)) :=
    div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  apply stripRegularizedOuter_integrable_of_exp_integrable
    hℓ hz (lowerGammaBoundaryCapped
      ((d : ℝ) / 2) R D)
    (lowerGammaBoundaryCapped_continuous hℓ R D)
  exact lowerGammaBoundaryCapped_exp_integrable_dimension
    hd ha R D

private theorem lowerStripCappedGammaOuter_differentiableOn_dimension
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    DifferentiableOn ℂ
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < Real.pi / (2 * ((d : ℝ) / 2)) :=
    div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  intro z hz
  unfold lowerStripCappedGammaOuter
  exact (stripRegularizedOuter_differentiableAt_of_exp_integrable
    hℓ hz
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (lowerGammaBoundaryCapped_continuous hℓ R D)
    (lowerGammaBoundaryCapped_exp_integrable_dimension
      hd ha R D)).differentiableWithinAt

private theorem stripRegularizedOuter_re
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (s : ℝ) (b : ℝ → ℝ)
    (houter : Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ))) :
    (stripRegularizedOuter ℓ b
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) := by
  unfold stripRegularizedOuter
  calc
    (∫ y : ℝ,
        stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re =
      ∫ y : ℝ,
        (stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re := by
      exact (integral_re houter).symm
    _ =
      ∫ y : ℝ,
        stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      change
        (stripRegularizedHolomorphicPoissonKernel ℓ
            ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y *
          (b y : ℂ)).re =
          stripPoissonKernel σ ((s - y) / ℓ) / ℓ * b y
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero,
        stripRegularizedHolomorphicPoissonKernel_re
          hℓ hσbelow hσabove]
    _ = ∫ T : ℝ, stripPoissonKernel σ T * b (s - ℓ * T) :=
      stripPoisson_integral_changeVariables hℓ σ s b

private theorem lowerStripCappedGammaOuter_re_dimension
    {d : ℕ} (hd : 0 < d) {σ R D : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D
          (s - ((d : ℝ) / 2) * T) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hz :
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ)) ∈
        Complex.im ⁻¹'
          Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, one_mul, zero_add]
    constructor
    · linarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · linarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  unfold lowerStripCappedGammaOuter
  exact stripRegularizedOuter_re hℓ hσbelow hσabove s
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (lowerStripCappedGammaOuter_integrable_dimension
      hd (R := R) (D := D) hz)

private theorem stripPoissonKernel_tendsto_zero_bottom_of_ne
    {T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun σ : ℝ => stripPoissonKernel σ T)
      (𝓝 (-1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hu : Real.pi * T / 2 ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero Real.pi_ne_zero hT) (by norm_num)
  have hcosh : 1 < Real.cosh (Real.pi * T / 2) :=
    Real.one_lt_cosh.mpr hu
  have hangle : Continuous (fun σ : ℝ => stripAngle σ) := by
    unfold stripAngle
    fun_prop
  have hden :
      4 * (Real.cosh (Real.pi * T / 2) -
        Real.cos (stripAngle (-1))) ≠ 0 := by
    simp only [stripAngle]
    norm_num
    linarith
  have hcontinuous :
      ContinuousAt (fun σ : ℝ => stripPoissonKernel σ T)
        (-1 : ℝ) := by
    unfold stripPoissonKernel
    exact ((Real.continuous_sin.comp hangle).continuousAt.div
      (continuousAt_const.mul
        (continuousAt_const.sub
          (Real.continuous_cos.comp hangle).continuousAt)) hden)
  convert! hcontinuous.tendsto using 1
  all_goals simp only [stripPoissonKernel, stripAngle, add_neg_cancel, mul_zero, zero_div,
    Real.sin_zero, Real.cos_zero]

private theorem stripPoissonKernel_le_center_of_lower_of_abs_ge
    {σ δ T : ℝ}
    (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (hδ : 0 < δ) (hT : δ ≤ |T|) :
    stripPoissonKernel σ T ≤
      (1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)) *
        stripPoissonKernel 0 T := by
  let A : ℝ := Real.cosh (Real.pi * T / 2)
  let C : ℝ := Real.cosh (Real.pi * δ / 2)
  let c : ℝ := 1 - C⁻¹
  have hδarg : Real.pi * δ / 2 ≠ 0 := by
    exact (div_pos (mul_pos Real.pi_pos hδ)
      (by norm_num)).ne'
  have hC : 1 < C := by
    exact Real.one_lt_cosh.mpr hδarg
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have hc : 0 < c := by
    try dsimp [c]
    have hrecip : C⁻¹ < 1 := (inv_lt_one₀ hCpos).mpr hC
    linarith
  have hA : 0 < A := Real.cosh_pos _
  have hCA : C ≤ A := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_div, abs_mul, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos hδ]
    norm_num
    gcongr
  have hratio : 1 ≤ A / C := by
    apply (le_div_iff₀ hCpos).2
    simpa only [one_mul] using! hCA
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hcoslt : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa only [gt_iff_lt, Real.cos_zero] using! h
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have hden : 0 < A - Real.cos (stripAngle σ) := by
    try dsimp [A]
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  have hcompare : c * A ≤ A - Real.cos (stripAngle σ) := by
    have hcos := Real.cos_le_one (stripAngle σ)
    try dsimp [c]
    rw [sub_mul, one_mul, inv_mul_eq_div]
    linarith
  have hcA : 0 < 4 * (c * A) := by positivity
  calc
    stripPoissonKernel σ T =
        Real.sin (stripAngle σ) /
          (4 * (A - Real.cos (stripAngle σ))) := rfl
    _ ≤ Real.sin (stripAngle σ) / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_left hsin.le hcA
      exact mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ ≤ 1 / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_right
        (Real.sin_le_one (stripAngle σ)) hcA.le
    _ = (1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)) *
          stripPoissonKernel 0 T := by
      simp only [stripPoissonKernel, stripAngle]
      norm_num
      try dsimp [A, C, c]
      field_simp [hc.ne', hA.ne']

private theorem stripPoissonKernel_le_center_of_lower
    {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      (1 / (1 - Real.cos (stripAngle σ))) *
        stripPoissonKernel 0 T := by
  let A : ℝ := Real.cosh (Real.pi * T / 2)
  let q : ℝ := Real.cos (stripAngle σ)
  let c : ℝ := 1 - q
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hhalf : stripAngle σ ≤ Real.pi / 2 := by
    unfold stripAngle
    linarith [mul_nonpos_of_nonneg_of_nonpos
      Real.pi_pos.le hnonpos]
  have hq : 0 ≤ q := by
    try dsimp [q]
    apply Real.cos_nonneg_of_mem_Icc
    exact ⟨by linarith [Real.pi_pos], hhalf⟩
  have hqlt : q < 1 := by
    try dsimp [q]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa only [gt_iff_lt, Real.cos_zero] using! h
  have hc : 0 < c := by
    try dsimp [c]
    linarith
  have hA : 0 < A := Real.cosh_pos _
  have hAone : 1 ≤ A := Real.one_le_cosh _
  have hcompare : c * A ≤ A - q := by
    try dsimp [c]
    linarith [mul_nonneg hq (sub_nonneg.mpr hAone)]
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have hcA : 0 < 4 * (c * A) := by positivity
  calc
    stripPoissonKernel σ T =
        Real.sin (stripAngle σ) / (4 * (A - q)) := rfl
    _ ≤ Real.sin (stripAngle σ) / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_left hsin.le hcA
      exact mul_le_mul_of_nonneg_left hcompare (by norm_num)
    _ ≤ 1 / (4 * (c * A)) := by
      apply div_le_div_of_nonneg_right
        (Real.sin_le_one (stripAngle σ)) hcA.le
    _ = (1 / (1 - Real.cos (stripAngle σ))) *
          stripPoissonKernel 0 T := by
      have hcenter : stripPoissonKernel 0 T =
          1 / (4 * A) := by
        simp only [stripPoissonKernel, stripAngle, add_zero, mul_one, Real.sin_pi_div_two,
          Real.cos_pi_div_two,
          sub_zero, one_div, mul_inv_rev, A]
      rw [hcenter]
      change 1 / (4 * (c * A)) =
        (1 / c) * (1 / (4 * A))
      field_simp [hc.ne', hA.ne']

private theorem stripPoissonKernel_lower_product_integrable
    {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hbase : Integrable (fun T : ℝ =>
      stripPoissonKernel 0 T * g T)) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * g T) := by
  let C : ℝ := 1 / (1 - Real.cos (stripAngle σ))
  have hangle := stripAngle_mem_Ioo hbelow
    (show σ < 1 by linarith)
  have hqlt : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle.2.le hangle.1
    simpa only [gt_iff_lt, Real.cos_zero] using! h
  have hC : 0 < C := by
    try dsimp [C]
    exact one_div_pos.mpr (by linarith)
  have hmajor : Integrable
      (fun T : ℝ => C *
        ‖stripPoissonKernel 0 T * g T‖) :=
    hbase.norm.const_mul C
  have hmeas : Measurable
      (fun T : ℝ => stripPoissonKernel σ T * g T) := by
    have hk : Measurable
        (fun T : ℝ => stripPoissonKernel σ T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    exact hk.mul hg.measurable
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with T
  have hσpositive := stripPoissonKernel_pos
    hbelow (show σ < 1 by linarith) T
  have hzero := stripPoissonKernel_pos
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1) T
  have hkernel := stripPoissonKernel_le_center_of_lower
    hbelow hnonpos T
  calc
    ‖stripPoissonKernel σ T * g T‖ =
        stripPoissonKernel σ T * ‖g T‖ := by
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos hσpositive]
    _ ≤ (C * stripPoissonKernel 0 T) * ‖g T‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact hkernel
    _ = C * ‖stripPoissonKernel 0 T * g T‖ := by
      rw [norm_mul, Real.norm_of_nonneg hzero.le]
      ring

private theorem lowerGammaBoundaryCapped_central_poisson_shift_integrable
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel 0 T *
        lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
          (s - ((d : ℝ) / 2) * T)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  let z : ℂ := (s : ℂ) +
    Complex.I * ((0 * ℓ : ℝ) : ℂ)
  have hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ := by
    try dsimp [z]
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re,
      zero_mul, one_mul, zero_add]
    constructor <;> linarith
  have houter := lowerStripCappedGammaOuter_integrable_dimension
    hd (R := R) (D := D) hz
  have hreal := houter.re
  have htranslated := hreal.comp_sub_left s
  have hscaled := htranslated.comp_mul_left' hℓ.ne'
  have hproduct := hscaled.const_mul ℓ
  convert! hproduct using 1
  ext T
  change
    stripPoissonKernel 0 T *
      lowerGammaBoundaryCapped ℓ R D (s - ℓ * T) =
      ℓ *
        (stripRegularizedHolomorphicPoissonKernel ℓ z
          (s - ℓ * T) *
            (lowerGammaBoundaryCapped ℓ R D
              (s - ℓ * T) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  try dsimp [z]
  rw [stripRegularizedHolomorphicPoissonKernel_re
    hℓ (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)]
  have harg : (s - (s - ℓ * T)) / ℓ = T := by
    field_simp [hℓ.ne']
    ring
  rw [harg]
  field_simp [hℓ.ne']

end

section

open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

private theorem norm_extension_le_of_frontier
    {U : Set ℂ}
    (hopen : IsOpen U)
    (hconnected : IsPreconnected U)
    (hbounded : Bornology.IsBounded U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {N : ℂ → ℝ}
    (hN : ContinuousOn N (closure U))
    (hinterior : ∀ z ∈ U, N z = ‖f z‖)
    {C : ℝ}
    (hfrontier : ∀ z ∈ frontier U, N z ≤ C)
    {z : ℂ} (hz : z ∈ closure U) :
    N z ≤ C := by
  classical
  by_cases hnonempty : U.Nonempty
  · have hproper : U ≠ (Set.univ : Set ℂ) := by
      intro hu
      rw [hu] at hbounded
      exact NormedSpace.unbounded_univ ℂ ℂ hbounded
    have hcompact : IsCompact (closure U) :=
      hbounded.isCompact_closure
    obtain ⟨w, hwclosure, hwmax⟩ :=
      hcompact.exists_isMaxOn hnonempty.closure hN
    have hwcases : w ∈ U ∨ w ∈ frontier U := by
      rw [closure_eq_interior_union_frontier,
        hopen.interior_eq, Set.mem_union] at hwclosure
      exact hwclosure
    have hwbound : N w ≤ C := by
      rcases hwcases with hWinterior | hWfrontier
      · have hmaxnorm :
            IsMaxOn (norm ∘ f) U w := by
          intro x hx
          change ‖f x‖ ≤ ‖f w‖
          rw [← hinterior x hx,
            ← hinterior w hWinterior]
          exact hwmax (subset_closure hx)
        have hconstant :=
          Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
            hconnected hopen hf hWinterior hmaxnorm
        have hrealconstant :
            Set.EqOn N (Function.const ℂ (N w)) U := by
          intro x hx
          calc
            N x = ‖f x‖ := hinterior x hx
            _ = ‖f w‖ := by
              simpa only [comp_apply, const] using!
                hconstant hx
            _ = N w := (hinterior w hWinterior).symm
        have hclosedconstant :=
          hrealconstant.of_subset_closure hN
            continuousOn_const subset_closure Subset.rfl
        obtain ⟨t, ht⟩ :=
          nonempty_frontier_iff.mpr
            ⟨hnonempty, hproper⟩
        have htclosure : t ∈ closure U :=
          frontier_subset_closure ht
        calc
          N w = N t := by
            symm
            simpa only [const] using!
              hclosedconstant htclosure
          _ ≤ C := hfrontier t ht
      · exact hfrontier w hWfrontier
    exact le_trans (hwmax hz) hwbound
  · have hempty : U = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [hempty, finite_empty, Finite.isClosed, IsClosed.closure_eq,
      mem_empty_iff_false] at hz

private theorem exists_vertical_cutoff
    {m r c q B δ C : ℝ} {f g : ℂ → ℂ} {z : ℂ}
    (hδ : δ < 0) (hcq : c < q) (hq : 0 < q) (hC : 0 < C)
    (hg : ∀ ⦃w : ℂ⦄, w.im ∈ Icc (m - r) (m + r) →
      ‖g w‖ ≤ Real.exp (δ * Real.exp (q * |w.re|)))
    (hf : Asymptotics.IsBigO
      (Filter.comap (fun w : ℂ => |w.re|) Filter.atTop ⊓
        Filter.principal (Complex.im ⁻¹' Ioo (m - r) (m + r)))
      f (fun w : ℂ => Real.exp (B * Real.exp (c * |w.re|)))) :
    ∃ R : ℝ, |z.re| < R ∧ ∀ w : ℂ, |w.re| = R →
      w.im ∈ Ioo (m - r) (m + r) → ‖g w • f w‖ ≤ C := by
  refine ((eventually_gt_atTop |z.re|).and ?_).exists
  rcases hf.exists_pos with ⟨A, hA, hAmajor⟩
  simp only [isBigOWith_iff, eventually_inf_principal, eventually_comap,
    Set.mem_Ioo, Set.mem_preimage, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hAmajor
  suffices hlimit : Tendsto
      (fun R : ℝ => Real.exp
        (δ * Real.exp (q * R) + B * Real.exp (c * R) + Real.log A))
      Filter.atTop (𝓝 (0 : ℝ)) by
    filter_upwards [hlimit.eventually (ge_mem_nhds hC), hAmajor]
      with R hRC hbound w hwre hwim
    calc
      ‖g w • f w‖ ≤ Real.exp
          (δ * Real.exp (q * R) + B * Real.exp (c * R) + Real.log A) := by
        rw [norm_smul, Real.exp_add, ← hwre, Real.exp_add, Real.exp_log hA,
          mul_assoc, mul_comm _ A]
        gcongr
        · exact hg (Set.Ioo_subset_Icc_self hwim)
        · exact hbound w hwre hwim
      _ ≤ C := hRC
  apply Real.tendsto_exp_atBot.comp
  suffices haux : Tendsto
      (fun R : ℝ => δ + B * (Real.exp ((q - c) * R))⁻¹)
      Filter.atTop (𝓝 (δ + B * 0)) by
    rw [mul_zero, add_zero] at haux
    refine Filter.Tendsto.atBot_add ?_ tendsto_const_nhds
    simpa only [id, Function.comp_apply, add_mul, mul_assoc,
      ← div_eq_inv_mul, ← Real.exp_sub, ← sub_mul, sub_sub_cancel] using!
        haux.neg_mul_atTop hδ
          (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hq))
  exact tendsto_const_nhds.add
    (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_exp_atTop.comp
          (tendsto_id.const_mul_atTop (sub_pos.mpr hcq)))))

private theorem horizontalStrip_norm_extension_majorization
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (f : ℂ → ℂ) (N : ℂ → ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.im ⁻¹' Ioo a b))
    (hN : ContinuousOn N
      (Complex.im ⁻¹' Icc a b))
    (hNnonneg : ∀ w : ℂ,
      w.im ∈ Icc a b → 0 ≤ N w)
    (hinterior : ∀ w : ℂ,
      w.im ∈ Ioo a b → N w = ‖f w‖)
    (hbottom : ∀ w : ℂ, w.im = a → N w ≤ C)
    (htop : ∀ w : ℂ, w.im = b → N w ≤ C)
    (hgrowth :
      ∃ c < Real.pi / (b - a), ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap (fun w : ℂ => |w.re|)
              Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹' Ioo a b))
          f
          (fun w : ℂ =>
            Real.exp (B * Real.exp (c * |w.re|))))
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    N z ≤ C := by
  rw [le_iff_eq_or_lt] at hza hzb
  rcases hza with hza | hza
  · exact hbottom z hza.symm
  rcases hzb with hzb | hzb
  · exact htop z hzb
  obtain ⟨m, r, rfl, rfl⟩ :
      ∃ m r : ℝ, a = m - r ∧ b = m + r :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hr : 0 < r := by linarith
  have hwidth : m - r < m + r := by linarith
  rw [add_sub_sub_cancel, ← two_mul,
    div_mul_eq_div_div] at hgrowth
  have hπr : 0 < Real.pi / 2 / r :=
    div_pos Real.pi_div_two_pos hr
  rcases hgrowth with ⟨c, hc, B, hO⟩
  obtain ⟨q, ⟨hcq, hq⟩, hqr⟩ :
      ∃ q : ℝ,
        (c < q ∧ 0 < q) ∧
          q < Real.pi / 2 / r := by
    simpa only [max_lt_iff] using!
      exists_between (max_lt hc hπr)
  have hqr' : q * r < Real.pi / 2 :=
    (lt_div_iff₀ hr).mp hqr
  let aff : ℂ → ℂ :=
    fun w => q * (w - m * Complex.I)
  let damp : ℝ → ℂ → ℂ :=
    fun ε w =>
      Complex.exp (ε *
        (Complex.exp (aff w) +
          Complex.exp (-aff w)))
  suffices hevent :
      ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ),
        ‖damp ε z • f z‖ ≤ C by
    rw [hinterior z ⟨hza, hzb⟩]
    refine le_of_tendsto
      (Filter.Tendsto.mono_left ?_
        nhdsWithin_le_nhds) hevent
    apply
      ((Complex.continuous_ofReal.mul
        continuous_const).cexp.smul
          continuous_const).norm.tendsto'
    simp only [Pi.mul_apply, Pi.smul_apply', ofReal_zero, zero_mul, exp_zero, smul_eq_mul, one_mul]
  filter_upwards [self_mem_nhdsWithin]
    with ε hε
  change ε < 0 at hε
  obtain ⟨δ, hδ, hδbound⟩ :
      ∃ δ : ℝ,
        δ < 0 ∧
          ∀ ⦃w : ℂ⦄,
            w.im ∈ Icc (m - r) (m + r) →
              ‖damp ε w‖ ≤
                Real.exp
                  (δ * Real.exp (q * |w.re|)) := by
    refine ⟨ε * Real.cos (q * r),
      mul_neg_of_neg_of_pos hε
        (Real.cos_pos_of_mem_Ioo
          (abs_lt.mp
            ((abs_of_pos (mul_pos hq hr)).symm ▸ hqr'))),
      ?_⟩
    intro w hw
    have hwaff : |(aff w).im| ≤ q * r := by
      rw [← Real.closedBall_eq_Icc,
        Metric.mem_closedBall, Real.dist_eq] at hw
      try dsimp [aff]
      rw [Complex.im_ofReal_mul, Complex.sub_im,
        Complex.mul_I_im, Complex.ofReal_re,
        abs_mul, abs_of_pos hq]
      gcongr
    simpa only [aff, Complex.re_ofReal_mul,
      abs_mul, abs_of_pos hq, Complex.sub_re,
      Complex.mul_I_re, Complex.ofReal_im,
      zero_mul, neg_zero, sub_zero, damp] using!
        norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le
          hε.le hwaff hqr'.le
  have hdampedge :
      ∀ w : ℂ,
        w.im = m - r ∨ w.im = m + r →
          ‖damp ε w‖ ≤ 1 := by
    intro w hw
    apply le_trans (hδbound
      (hw.by_cases
        (fun h => h.symm ▸ left_mem_Icc.mpr hwidth.le)
        (fun h => h.symm ▸ right_mem_Icc.mpr hwidth.le)))
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      hδ.le (Real.exp_pos _).le
  obtain ⟨R, hzR, hR⟩ :=
    exists_vertical_cutoff hδ hcq hq hC hδbound hO
  have hRpos : 0 < R :=
    (abs_nonneg z.re).trans_lt hzR
  let U : Set ℂ :=
    Set.Ioo (-R) R ×ℂ Set.Ioo (m - r) (m + r)
  have hUopen : IsOpen U :=
    IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  have hUbounded : Bornology.IsBounded U :=
    Bornology.IsBounded.reProdIm
      (isBounded_Ioo _ _) (isBounded_Ioo _ _)
  have hUconvex : Convex ℝ U := by
    have hset : U =
        ({w : ℂ | -R < w.re} ∩
          {w : ℂ | w.re < R}) ∩
        ({w : ℂ | m - r < w.im} ∩
          {w : ℂ | w.im < m + r}) := by
      ext w
      simp only [mem_reProdIm, mem_Ioo, mem_inter_iff, mem_ofPred_eq, U]
    rw [hset]
    exact
      ((convex_halfSpace_re_gt (-R)).inter
        (convex_halfSpace_re_lt R)).inter
      ((convex_halfSpace_im_gt (m - r)).inter
        (convex_halfSpace_im_lt (m + r)))
  have hdamp : Differentiable ℂ (damp ε) := by
    exact
      ((((differentiable_id.sub_const _).const_mul _).cexp.add
        ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul
          _).cexp
  have hweighted :
      DifferentiableOn ℂ
        (fun w : ℂ => damp ε w • f w) U := by
    exact (hdamp.differentiableOn.smul hf).mono
      Set.inter_subset_right
  have hclosure :
      closure U ⊆
        Complex.im ⁻¹' Icc (m - r) (m + r) := by
    intro w hw
    try dsimp [U] at hw
    rw [Complex.closure_reProdIm,
      closure_Ioo (neg_lt_self hRpos).ne,
      closure_Ioo hwidth.ne] at hw
    exact hw.2
  let Next : ℂ → ℝ :=
    fun w => ‖damp ε w‖ * N w
  have hNext : ContinuousOn Next (closure U) := by
    try dsimp [Next]
    exact hdamp.continuous.norm.continuousOn.mul
      (hN.mono hclosure)
  have hNextinterior :
      ∀ w ∈ U,
        Next w = ‖damp ε w • f w‖ := by
    intro w hw
    try dsimp [Next]
    rw [hinterior w hw.2]
    exact (norm_mul _ _).symm
  have hNextfrontier :
      ∀ w ∈ frontier U, Next w ≤ C := by
    intro w hw
    try dsimp [U] at hw
    rw [Complex.frontier_reProdIm,
      closure_Ioo (neg_lt_self hRpos).ne,
      frontier_Ioo hwidth,
      closure_Ioo hwidth.ne,
      frontier_Ioo (neg_lt_self hRpos)] at hw
    by_cases him : w.im = m - r ∨ w.im = m + r
    · dsimp [Next]
      calc
        ‖damp ε w‖ * N w ≤ 1 * N w := by
          apply mul_le_mul_of_nonneg_right
            (hdampedge w him)
          apply hNnonneg w
          exact him.by_cases
            (fun h => h.symm ▸ left_mem_Icc.mpr hwidth.le)
            (fun h => h.symm ▸ right_mem_Icc.mpr hwidth.le)
        _ = N w := one_mul _
        _ ≤ C := him.by_cases
          (hbottom w) (htop w)
    · have hvert :
          w ∈ ({-R, R} : Set ℝ) ×ℂ
            Icc (m - r) (m + r) := by
        exact hw.resolve_left
          (fun h => him h.2)
      have him' :=
        eq_endpoints_or_mem_Ioo_of_mem_Icc hvert.2
      rw [← or_assoc] at him'
      have himinterior := him'.resolve_left him
      try dsimp [Next]
      rw [hinterior w himinterior]
      simpa only [ge_iff_le, smul_eq_mul, Complex.norm_mul] using!
        hR w
          ((abs_eq hRpos.le).mpr hvert.1.symm)
          himinterior
  have hzU : z ∈ U := by
    exact ⟨(abs_lt.mp hzR), ⟨hza, hzb⟩⟩
  have hmax := norm_extension_le_of_frontier
    hUopen hUconvex.isPreconnected hUbounded
    hweighted hNext hNextinterior
    hNextfrontier (subset_closure hzU)
  calc
    ‖damp ε z • f z‖ = Next z := by
      symm
      exact hNextinterior z hzU
    _ ≤ C := hmax

private theorem harmonic_abs_log_half_le_half
    {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (x / 2)| ≤ x / 2 := by
  have hhalf : 1 ≤ x / 2 := by linarith
  rw [abs_of_nonneg (Real.log_nonneg hhalf)]
  have hlog :=
    Real.log_le_sub_one_of_pos
      (show 0 < x / 2 by linarith)
  linarith

private theorem harmonic_abs_log_sqrtFactor_le_linear
    {c x : ℝ} (hc : 0 ≤ c) (hx : 2 ≤ x) :
    |Real.log
      (Real.sqrt (c ^ 2 + (x / 2) ^ 2))| ≤ c + x := by
  have hfactor := lower_abs_log_sqrtFactor_le
    hc (show 0 < x by linarith)
  have hlog := harmonic_abs_log_half_le_half hx
  linarith

private theorem harmonic_abs_log_coth_div_le_linear
    {x : ℝ} (hx : 2 ≤ x) :
    |Real.log
      (lowerCoth (Real.pi * (x / 2)) / (x / 2))| ≤
      Real.pi * x + |Real.log Real.pi| + x := by
  have hcorr := lower_abs_log_coth_div_le
    (show 0 < x / 2 by linarith)
  have hlog := harmonic_abs_log_half_le_half hx
  linarith

private theorem harmonic_integerGammaBoundary_abs_le_linear
    (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ x : ℝ, 2 ≤ x →
        |lowerGammaBoundaryLog (k : ℝ) R x| ≤
          A * (1 + x) := by
  let S : ℝ :=
    ∑ j ∈ Finset.range k, (j : ℝ)
  let L : ℝ :=
    |(k : ℝ) * Real.log (Real.pi * R ^ 2)|
  let A : ℝ := L + S + (k : ℝ) + 1
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hL : 0 ≤ L := abs_nonneg _
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro x hx
  have hxzero : x ≠ 0 := by linarith
  have hsum :
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))| ≤
        S + (k : ℝ) * x := by
    calc
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))| ≤
          ∑ j ∈ Finset.range k,
            |Real.log
              (Real.sqrt
                ((j : ℝ) ^ 2 + (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k,
            ((j : ℝ) + x) := by
        apply Finset.sum_le_sum
        intro j hj
        exact harmonic_abs_log_sqrtFactor_le_linear
          (Nat.cast_nonneg j) hx
      _ = S + (k : ℝ) * x := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, S]
  rw [lowerGammaBoundaryLog_integer k R hxzero]
  have habs := abs_sub
    ((k : ℝ) * Real.log (Real.pi * R ^ 2))
    (∑ j ∈ Finset.range k,
      Real.log (Real.sqrt
        ((j : ℝ) ^ 2 + (x / 2) ^ 2)))
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hxpos : 0 ≤ x := by linarith
  try dsimp [A, L]
  try dsimp [L] at hL
  linarith [mul_nonneg hL hxpos,
    mul_nonneg hS hxpos, mul_nonneg hk hxpos]

private theorem harmonic_halfIntegerGammaBoundary_abs_le_linear
    (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ x : ℝ, 2 ≤ x →
        |lowerGammaBoundaryLog
          ((k : ℝ) + 1 / 2) R x| ≤
          A * (1 + x) := by
  let S : ℝ :=
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)
  let L : ℝ :=
    |((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2)|
  let Q : ℝ := |Real.log Real.pi|
  let A : ℝ :=
    L + S + (k : ℝ) + Real.pi + Q + 2
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hL : 0 ≤ L := abs_nonneg _
  have hQ : 0 ≤ Q := abs_nonneg _
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hsum :
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 +
              (x / 2) ^ 2))| ≤
        S + (k : ℝ) * x := by
    calc
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 +
              (x / 2) ^ 2))| ≤
          ∑ j ∈ Finset.range k,
            |Real.log
              (Real.sqrt
                (((j : ℝ) + 1 / 2) ^ 2 +
                  (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k,
            ((j : ℝ) + 1 / 2 + x) := by
        apply Finset.sum_le_sum
        intro j hj
        apply harmonic_abs_log_sqrtFactor_le_linear
          (by positivity) hx
      _ = S + (k : ℝ) * x := by
        simp only [one_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, S]
  have hcorr :=
    harmonic_abs_log_coth_div_le_linear hx
  have hcorrhalf :
      |(1 / 2 : ℝ) *
        Real.log
          (lowerCoth (Real.pi * (x / 2)) /
            (x / 2))| ≤
        (1 / 2 : ℝ) *
          (Real.pi * x + Q + x) := by
    rw [abs_mul, abs_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Q] using! hcorr)
      (by norm_num)
  rw [lowerGammaBoundaryLog_halfInteger
    k R hxpos.ne']
  simp only [abs_of_pos hxpos]
  rw [show Real.pi * x / 2 =
    Real.pi * (x / 2) by ring]
  have hmain := abs_sub
    (((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2))
    (∑ j ∈ Finset.range k,
      Real.log
        (Real.sqrt
          (((j : ℝ) + 1 / 2) ^ 2 +
            (x / 2) ^ 2)))
  have htotal := abs_add_le
    (((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 +
                (x / 2) ^ 2)))
    ((1 / 2 : ℝ) *
      Real.log
        (lowerCoth (Real.pi * (x / 2)) /
          (x / 2)))
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hxn : 0 ≤ x := hxpos.le
  try dsimp [A, L, Q]
  try dsimp [L] at hL
  try dsimp [Q] at hQ
  linarith [mul_nonneg hL hxn,
    mul_nonneg hS hxn,
    mul_nonneg hk hxn,
    mul_nonneg hπ hxn,
    mul_nonneg hQ hxn]

private theorem harmonic_dimensionGammaBoundary_eq_abs
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R |y| := by
  by_cases hnonneg : 0 ≤ y
  · rw [abs_of_nonneg hnonneg]
  · have hneg : y < 0 := lt_of_not_ge hnonneg
    rw [abs_of_neg hneg]
    exact
      (lowerGammaBoundaryLog_dimension_neg
        (d := d) R hy).symm

private theorem harmonic_dimensionGammaBoundary_abs_le_linear
    (d : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ, 2 ≤ |y| →
        |lowerGammaBoundaryLog
          ((d : ℝ) / 2) R y| ≤
          A * (1 + |y|) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hcast :
        ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    obtain ⟨A, hA, htail⟩ :=
      harmonic_integerGammaBoundary_abs_le_linear k R
    refine ⟨A, hA, ?_⟩
    intro y hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hy
    rw [harmonic_dimensionGammaBoundary_eq_abs R hyzero,
      hcast]
    exact htail |y| hy
  · have hcast :
        ((↑(2 * k + 1) : ℝ) / 2) =
          (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    obtain ⟨A, hA, htail⟩ :=
      harmonic_halfIntegerGammaBoundary_abs_le_linear k R
    refine ⟨A, hA, ?_⟩
    intro y hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hy
    rw [harmonic_dimensionGammaBoundary_eq_abs R hyzero,
      hcast]
    exact htail |y| hy

private theorem lowerGammaBoundaryCapped_dimension_abs_le_linear
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : ℝ,
        |lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y| ≤
            A * (1 + |y|) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A₀, hA₀, htail⟩ :=
    harmonic_dimensionGammaBoundary_abs_le_linear d R
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc : IsCompact
      (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
        (lowerGammaBoundaryCapped_continuous
          hℓ R D).continuousOn
  let A : ℝ :=
    max 0 (max K (max |D| A₀))
  have hA : 0 ≤ A := le_max_left _ _
  have hKA : K ≤ A :=
    le_trans (le_max_left _ _)
      (le_max_right _ _)
  have hDA : |D| ≤ A :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_max_right _ _))
  have hA₀A : A₀ ≤ A :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_max_right _ _))
  refine ⟨A, hA, ?_⟩
  intro y
  have hfactor : 1 ≤ 1 + |y| := by
    linarith [abs_nonneg y]
  by_cases hy : |y| < 2
  · have hymem : y ∈ Icc (-2 : ℝ) 2 := by
      have hbounds := abs_lt.mp hy
      exact ⟨hbounds.1.le, hbounds.2.le⟩
    have hcompact := hK y hymem
    rw [Real.norm_eq_abs] at hcompact
    calc
      |lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y| ≤ K := hcompact
      _ ≤ A := hKA
      _ ≤ A * (1 + |y|) := by
        linarith [mul_nonneg hA (abs_nonneg y)]
  · have hylarge : 2 ≤ |y| := le_of_not_gt hy
    have hyzero : y ≠ 0 := by
      intro heq
      subst y
      norm_num at hylarge
    unfold lowerGammaBoundaryCapped
    rw [ite_eq_right hyzero]
    by_cases hmin :
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤ D
    · rw [min_eq_left hmin]
      calc
        |lowerGammaBoundaryLog
          ((d : ℝ) / 2) R y| ≤
            A₀ * (1 + |y|) := htail y hylarge
        _ ≤ A * (1 + |y|) :=
          mul_le_mul_of_nonneg_right hA₀A
            (by positivity)
    · rw [min_eq_right (le_of_not_ge hmin)]
      calc
        |D| ≤ A := hDA
        _ ≤ A * (1 + |y|) := by
          linarith [mul_nonneg hA (abs_nonneg y)]

private theorem stripPoissonKernel_le_exponentialMajorant_of_nonneg
    {σ : ℝ} (hσ : 0 ≤ σ) (hσone : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripPoissonExponentialMajorant T := by
  have hbelow : -1 < σ := by linarith
  have hmass := stripBottomMass_pos hσone
  have hmassone :=
    (stripBottomMass_lt_one hbelow).le
  have hext :=
    stripNormalizedPoissonExtension_le_majorant
      hσ hσone.le T
  have hreconstruct :
      stripPoissonKernel σ T =
        stripBottomMass σ *
          stripNormalizedPoissonExtension σ T := by
    rw [← stripNormalizedPoissonKernel_eq_extension
      hbelow hσone T]
    unfold stripNormalizedPoissonKernel
    field_simp [hmass.ne']
  rw [hreconstruct]
  calc
    stripBottomMass σ *
        stripNormalizedPoissonExtension σ T ≤
      1 * stripNormalizedPoissonExtension σ T :=
        mul_le_mul_of_nonneg_right hmassone hext.1
    _ = stripNormalizedPoissonExtension σ T := one_mul _
    _ ≤ stripPoissonExponentialMajorant T := hext.2

private theorem harmonic_stripPoissonExponentialMajorant_abs_integrable :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T * |T|) := by
  have hbase :=
    integrable_abs_pow_mul_exp_neg_mul_abs 1
      (half_pos Real.pi_pos)
  have hconstant := hbase.const_mul (Real.pi / 2)
  convert! hconstant using 1
  ext T
  unfold stripPoissonExponentialMajorant
  norm_num
  ring

private theorem harmonic_stripPoissonKernel_zero_abs_integrable :
    Integrable
      (fun T : ℝ => stripPoissonKernel 0 T * |T|) := by
  have hmajor :=
    harmonic_stripPoissonExponentialMajorant_abs_integrable
  have hmeas : Measurable
      (fun T : ℝ => stripPoissonKernel 0 T * |T|) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with T
  have hkernel :=
    stripPoissonKernel_le_exponentialMajorant_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1) T
  have hpos := stripPoissonKernel_pos
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1) T
  have hmajorpos : 0 ≤ stripPoissonExponentialMajorant T := by
    unfold stripPoissonExponentialMajorant
    positivity
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hpos.le (abs_nonneg T))]
  exact mul_le_mul_of_nonneg_right
    hkernel (abs_nonneg T)

private theorem harmonic_stripPoissonKernel_abs_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable
      (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
  by_cases hσ : σ ≤ 0
  · exact stripPoissonKernel_lower_product_integrable
      hbelow hσ continuous_abs
      harmonic_stripPoissonKernel_zero_abs_integrable
  · have hpositive : 0 ≤ σ := (le_of_not_ge hσ)
    have hmajor :=
      harmonic_stripPoissonExponentialMajorant_abs_integrable
    have hmeas : Measurable
        (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with T
    have hkernel :=
      stripPoissonKernel_le_exponentialMajorant_of_nonneg
        hpositive habove T
    have hkpos := stripPoissonKernel_pos
      hbelow habove T
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg hkpos.le (abs_nonneg T))]
    exact mul_le_mul_of_nonneg_right
      hkernel (abs_nonneg T)

private theorem exists_stripPoissonKernel_uniform_abs_moment :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ σ : ℝ, -1 < σ → σ < 1 →
        (∫ T : ℝ,
          stripPoissonKernel σ T * |T|) ≤ M := by
  let C : ℝ :=
    1 / (1 - (Real.cosh (Real.pi / 2))⁻¹)
  let J : ℝ :=
    ∫ T : ℝ, stripPoissonKernel 0 T * |T|
  let E : ℝ :=
    ∫ T : ℝ,
      stripPoissonExponentialMajorant T * |T|
  let M : ℝ := 1 + C * J + E
  have harg : Real.pi / 2 ≠ 0 :=
    (half_pos Real.pi_pos).ne'
  have hcosh : 1 < Real.cosh (Real.pi / 2) :=
    Real.one_lt_cosh.mpr harg
  have hC : 0 < C := by
    try dsimp [C]
    have hpositive := Real.cosh_pos (Real.pi / 2)
    have hinv := (inv_lt_one₀ hpositive).mpr hcosh
    exact one_div_pos.mpr (by linarith)
  have hJ : 0 ≤ J := by
    try dsimp [J]
    apply integral_nonneg
    intro T
    exact mul_nonneg
      (stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T).le
      (abs_nonneg T)
  have hE : 0 ≤ E := by
    try dsimp [E]
    apply integral_nonneg
    intro T
    unfold stripPoissonExponentialMajorant
    positivity
  have hM : 0 ≤ M := by
    try dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro σ hbelow habove
  have hmoment :=
    harmonic_stripPoissonKernel_abs_integrable
      hbelow habove
  by_cases hσ : σ ≤ 0
  · let S : Set ℝ := {T : ℝ | 1 ≤ |T|}
    have hS : MeasurableSet S :=
      (isClosed_le continuous_const
        continuous_abs).measurableSet
    have hk := stripPoissonKernel_integrable
      hbelow habove
    have hcenter :=
      harmonic_stripPoissonKernel_zero_abs_integrable
    have hscaled : Integrable
        (fun T : ℝ =>
          C * (stripPoissonKernel 0 T * |T|)) :=
      hcenter.const_mul C
    have hfar :
        (∫ T in S,
          stripPoissonKernel σ T * |T|) ≤
          C * J := by
      calc
        (∫ T in S,
            stripPoissonKernel σ T * |T|) ≤
          ∫ T in S,
            C * (stripPoissonKernel 0 T * |T|) := by
          apply setIntegral_mono_on
            hmoment.integrableOn
            hscaled.integrableOn hS
          intro T hT
          have hcompare :=
            stripPoissonKernel_le_center_of_lower_of_abs_ge
              hbelow hσ
              (by norm_num : (0 : ℝ) < 1)
              (show (1 : ℝ) ≤ |T| from hT)
          have hCeq :
              1 / (1 -
                (Real.cosh (Real.pi * (1 : ℝ) / 2))⁻¹) =
                C := by
            try dsimp [C]
            congr 2
            ring_nf
          rw [hCeq] at hcompare
          linarith [mul_nonneg
            (sub_nonneg.mpr hcompare)
            (abs_nonneg T)]
        _ ≤ ∫ T : ℝ,
            C * (stripPoissonKernel 0 T * |T|) := by
          apply setIntegral_le_integral hscaled
          filter_upwards [] with T
          exact mul_nonneg hC.le
            (mul_nonneg
              (stripPoissonKernel_pos
                (by norm_num : (-1 : ℝ) < 0)
                (by norm_num : (0 : ℝ) < 1) T).le
              (abs_nonneg T))
        _ = C * J := by
          rw [integral_const_mul]
    have hnear :
        (∫ T in Sᶜ,
          stripPoissonKernel σ T * |T|) ≤ 1 := by
      calc
        (∫ T in Sᶜ,
            stripPoissonKernel σ T * |T|) ≤
          ∫ T in Sᶜ,
            stripPoissonKernel σ T := by
          apply setIntegral_mono_on
            hmoment.integrableOn
            hk.integrableOn hS.compl
          intro T hT
          have hTabs : |T| ≤ 1 := by
            have hnot : ¬ (1 : ℝ) ≤ |T| := by
              intro hge
              exact hT (show T ∈ S from hge)
            exact (lt_of_not_ge hnot).le
          have hkpos :=
            stripPoissonKernel_pos
              hbelow habove T
          linarith [mul_nonneg hkpos.le
            (sub_nonneg.mpr hTabs)]
        _ ≤ ∫ T : ℝ,
            stripPoissonKernel σ T := by
          apply setIntegral_le_integral hk
          filter_upwards [] with T
          exact (stripPoissonKernel_pos
            hbelow habove T).le
        _ = stripBottomMass σ :=
          integral_stripPoissonKernel hbelow habove
        _ ≤ 1 := (stripBottomMass_lt_one hbelow).le
    have hsplit := integral_add_compl hS hmoment
    try dsimp [M]
    linarith
  · have hσnonneg : 0 ≤ σ := le_of_not_ge hσ
    have hmajor :=
      harmonic_stripPoissonExponentialMajorant_abs_integrable
    have hineq :
        (∫ T : ℝ,
          stripPoissonKernel σ T * |T|) ≤ E := by
      try dsimp [E]
      apply integral_mono hmoment hmajor
      intro T
      apply mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_exponentialMajorant_of_nonneg
          hσnonneg habove T)
        (abs_nonneg T)
    try dsimp [M]
    linarith [mul_nonneg hC.le hJ]

private theorem lowerGammaBoundaryCapped_poisson_abs_le_linear
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ σ : ℝ, -1 < σ → σ < 1 →
        ∀ s : ℝ,
          |∫ T : ℝ,
            stripPoissonKernel σ T *
              lowerGammaBoundaryCapped
                ((d : ℝ) / 2) R D
                (s - ((d : ℝ) / 2) * T)| ≤
              B * (1 + |s|) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hdatum⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear
      hd R D
  obtain ⟨M, hM, hmomentbound⟩ :=
    exists_stripPoissonKernel_uniform_abs_moment
  let B : ℝ := A * (1 + ℓ * M)
  have hB : 0 ≤ B := by
    try dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro σ hbelow habove s
  have hk := stripPoissonKernel_integrable
    hbelow habove
  have hmoment :=
    harmonic_stripPoissonKernel_abs_integrable
      hbelow habove
  have hconstant := hk.const_mul
    (A * (1 + |s|))
  have hlinear := hmoment.const_mul (A * ℓ)
  have hmajor : Integrable
      (fun T : ℝ =>
        (A * (1 + |s|)) *
            stripPoissonKernel σ T +
          (A * ℓ) *
            (stripPoissonKernel σ T * |T|)) := by
    exact hconstant.add hlinear
  have hpoint :
      ∀ᵐ T : ℝ,
        ‖stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ℓ R D
              (s - ℓ * T)‖ ≤
          (A * (1 + |s|)) *
              stripPoissonKernel σ T +
            (A * ℓ) *
              (stripPoissonKernel σ T * |T|) := by
    filter_upwards [] with T
    have hkpos :=
      stripPoissonKernel_pos hbelow habove T
    have hb := hdatum (s - ℓ * T)
    have htriangle := abs_sub s (ℓ * T)
    have hmulabs : |ℓ * T| = ℓ * |T| := by
      rw [abs_mul, abs_of_pos hℓ]
    rw [hmulabs] at htriangle
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos hkpos, Real.norm_eq_abs]
    have hbig :
        |lowerGammaBoundaryCapped ℓ R D
          (s - ℓ * T)| ≤
          A * (1 + |s| + ℓ * |T|) := by
      calc
        |lowerGammaBoundaryCapped ℓ R D
          (s - ℓ * T)| ≤
            A * (1 + |s - ℓ * T|) := hb
        _ ≤ A * (1 + |s| + ℓ * |T|) := by
          apply mul_le_mul_of_nonneg_left _ hA
          linarith
    linarith [mul_nonneg hkpos.le
      (sub_nonneg.mpr hbig)]
  have hmass :=
    (stripBottomMass_lt_one hbelow).le
  have hmasspos :=
    (stripBottomMass_pos habove).le
  have hmomentle :=
    hmomentbound σ hbelow habove
  calc
    |∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D
            (s - ℓ * T)| =
      ‖∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D
            (s - ℓ * T)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ T : ℝ,
        ((A * (1 + |s|)) *
            stripPoissonKernel σ T +
          (A * ℓ) *
            (stripPoissonKernel σ T * |T|)) :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = (A * (1 + |s|)) * stripBottomMass σ +
        (A * ℓ) *
          (∫ T : ℝ,
            stripPoissonKernel σ T * |T|) := by
      rw [integral_add hconstant hlinear,
        integral_const_mul, integral_const_mul,
        integral_stripPoissonKernel hbelow habove]
    _ ≤ A * (1 + |s|) + (A * ℓ) * M := by
      have hfirst := mul_le_mul_of_nonneg_left
        hmass (by positivity : 0 ≤ A * (1 + |s|))
      have hsecond := mul_le_mul_of_nonneg_left
        hmomentle (by positivity : 0 ≤ A * ℓ)
      linarith
    _ ≤ B * (1 + |s|) := by
      try dsimp [B]
      linarith [mul_nonneg
        (show 0 ≤ A * ℓ * M by positivity)
        (abs_nonneg s)]

private theorem lowerStripCappedGammaOuter_abs_re_le_linear
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z : ℂ,
        z ∈ Complex.im ⁻¹'
          Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        |(lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re| ≤
          B * (1 + |z.re|) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨B, hB, hbound⟩ :=
    lowerGammaBoundaryCapped_poisson_abs_le_linear
      hd R D
  refine ⟨B, hB, ?_⟩
  intro z hz
  have hzbelow : -ℓ < z.im := hz.1
  have hzabove : z.im < ℓ := hz.2
  let σ : ℝ := z.im / ℓ
  have hσbelow : -1 < σ := by
    try dsimp [σ]
    apply (lt_div_iff₀ hℓ).2
    simpa only [neg_mul, one_mul] using! hzbelow
  have hσabove : σ < 1 := by
    try dsimp [σ]
    apply (div_lt_iff₀ hℓ).2
    simpa only [one_mul] using! hzabove
  have hzrep :
      (z.re : ℂ) +
        Complex.I * ((σ * ℓ : ℝ) : ℂ) = z := by
    apply Complex.ext
    · simp only [ofReal_mul, add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero, sub_zero,
      zero_mul, I_im, mul_im,
        add_zero, sub_self]
    · simp only [isUnit_iff_ne_zero, ne_eq, hℓ.ne', not_false_eq_true, IsUnit.div_mul_cancel,
      add_im, ofReal_im,
        mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul, zero_add, σ]
  have hreal := lowerStripCappedGammaOuter_re_dimension
    hd hσbelow hσabove z.re (R := R) (D := D)
  rw [hzrep] at hreal
  rw [hreal]
  exact hbound σ hσbelow hσabove z.re

private theorem antiFourierWitness_cappedWeightedMellinStrip_growth
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ) :
    ∃ c < Real.pi /
        (((d : ℝ) / 2) - (-((d : ℝ) / 2))),
      ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap
              (fun z : ℂ => |z.re|) Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹'
                Ioo (-((d : ℝ) / 2))
                    ((d : ℝ) / 2)))
          (fun z : ℂ =>
            Complex.exp
                (-(lowerStripCappedGammaOuter
                  ((d : ℝ) / 2) R D z)) *
              normalizedRadialMellinStrip
                hd w.function R z)
          (fun z : ℂ =>
            Real.exp
              (B * Real.exp (c * |z.re|))) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ :=
    half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨G, hG, houter⟩ :=
    lowerStripCappedGammaOuter_abs_re_le_linear
      hd R D
  obtain ⟨K, hK, hwitness⟩ :=
    antiFourierWitness_normalizedMellinStrip_uniform_bound
      hd w
  let c : ℝ := Real.pi / (4 * ℓ)
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hclt : c < Real.pi / (ℓ - (-ℓ)) := by
    try dsimp [c]
    apply (div_lt_div_iff₀
      (by positivity : 0 < 4 * ℓ)
      (by linarith : 0 < ℓ - (-ℓ))).2
    nlinarith [Real.pi_pos, hℓ]
  let B : ℝ := G * (1 + 1 / c)
  refine ⟨c, hclt, B, ?_⟩
  apply Asymptotics.IsBigO.of_bound (K + 1)
  apply Filter.eventually_inf_principal.mpr
  refine Filter.Eventually.of_forall ?_
  intro z hz
  have hzbelow : -ℓ < z.im := hz.1
  have hzabove : z.im < ℓ := hz.2
  have hZ := hwitness z hzbelow.le hzabove.le
  have hW := houter z hz
  have hre :
      -(lowerStripCappedGammaOuter ℓ R D z).re ≤
        G * (1 + |z.re|) := by
    exact le_trans
      (neg_le_abs _) hW
  have hexpcomparison :
      G * (1 + |z.re|) ≤
        B * Real.exp (c * |z.re|) := by
    have hx : 0 ≤ |z.re| := abs_nonneg _
    have hcinv : 0 ≤ 1 / c := by positivity
    have hsmall :
        1 + |z.re| ≤
          (1 + 1 / c) *
            Real.exp (c * |z.re|) := by
      calc
        1 + |z.re| ≤
            (1 + 1 / c) *
              (1 + c * |z.re|) := by
          have hcx : 0 ≤ c * |z.re| :=
            mul_nonneg hc.le hx
          have hrecip : (1 / c) * c = 1 := by
            field_simp [hc.ne']
          nlinarith [mul_nonneg hcinv hcx]
        _ ≤ (1 + 1 / c) *
              Real.exp (c * |z.re|) := by
          apply mul_le_mul_of_nonneg_left
            (show 1 + c * |z.re| ≤
              Real.exp (c * |z.re|) by
              simpa only [add_comm] using!
                Real.add_one_le_exp (c * |z.re|))
            (by positivity)
    try dsimp [B]
    calc
      G * (1 + |z.re|) ≤
          G * ((1 + 1 / c) *
            Real.exp (c * |z.re|)) :=
        mul_le_mul_of_nonneg_left hsmall hG
      _ = G * (1 + 1 / c) *
          Real.exp (c * |z.re|) := by ring
  rw [norm_mul, Complex.norm_exp,
    Complex.neg_re, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp
        (-(lowerStripCappedGammaOuter ℓ R D z).re) *
        ‖normalizedRadialMellinStrip
          hd w.function R z‖ ≤
      Real.exp
        (G * (1 + |z.re|)) * K := by
      apply mul_le_mul
        (Real.exp_le_exp.mpr hre) hZ
        (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp
        (B * Real.exp (c * |z.re|)) * K := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hexpcomparison) hK
    _ ≤ (K + 1) *
        Real.exp
          (B * Real.exp (c * |z.re|)) := by
      linarith [Real.exp_pos
        (B * Real.exp (c * |z.re|))]

private theorem harmonic_bottom_normalized_height_tendsto
    {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    Tendsto
      (fun z : ℂ => z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (-1 : ℝ)) := by
  have hcontinuous : Continuous
      (fun z : ℂ => z.im / ℓ) := by
    fun_prop
  convert! hcontinuous.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds using 1;
      simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul, zero_add,
        zero_sub, ne_eq,
        hℓ.ne', not_false_eq_true, neg_div_self]

private theorem harmonic_bottom_real_tendsto
    {ℓ : ℝ} (s : ℝ) :
    Tendsto Complex.re
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 s) := by
  convert! Complex.continuous_re.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds using 1;
      simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        sub_zero]

private theorem harmonic_bottom_far_joint_tendsto_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T in {T : ℝ | δ ≤ |T|},
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) - Complex.I * (ℓ : ℂ)
  let S : Set ℝ :=
    {T : ℝ | δ ≤ |T|}
  let C : ℝ :=
    1 / (1 - (Real.cosh (Real.pi * δ / 2))⁻¹)
  let integrand : ℂ → ℝ → ℝ := fun z T =>
    S.indicator
      (fun T : ℝ => stripPoissonKernel (z.im / ℓ) T * b (z.re - ℓ * T)) T
  let majorant : ℝ → ℝ := fun T =>
    C * ((A * (2 + |s|)) * stripPoissonKernel 0 T +
      (A * ℓ) * (stripPoissonKernel 0 T * |T|))
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const
      continuous_abs).measurableSet
  have hδarg : Real.pi * δ / 2 ≠ 0 := by
    exact (div_pos (mul_pos Real.pi_pos hδ)
      (by norm_num)).ne'
  have hcosh : 1 < Real.cosh (Real.pi * δ / 2) :=
    Real.one_lt_cosh.mpr hδarg
  have hC : 0 < C := by
    try dsimp [C]
    have hpositive := Real.cosh_pos (Real.pi * δ / 2)
    have hinv := (inv_lt_one₀ hpositive).mpr hcosh
    exact one_div_pos.mpr (by linarith)
  have hσ :
      Tendsto (fun z : ℂ => z.im / ℓ)
        (𝓝[U] z₀) (𝓝 (-1 : ℝ)) := by
    exact harmonic_bottom_normalized_height_tendsto
      hℓ s
  have hsreal :
      Tendsto Complex.re
        (𝓝[U] z₀) (𝓝 s) :=
    harmonic_bottom_real_tendsto s
  have hlower :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        -1 < z.im / ℓ := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    have hzbelow : -ℓ < z.im := hz.1
    apply (lt_div_iff₀ hℓ).2
    simpa only [neg_mul, one_mul] using! hzbelow
  have hupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        z.im / ℓ ≤ 0 := by
    have hneg := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact hneg.mono (fun z hz => hz.le)
  have hrealbound :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        |z.re| ≤ |s| + 1 := by
    have hball := hsreal.eventually
      (Metric.ball_mem_nhds s
        (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hball]
      with z hz
    have hsmall : |z.re - s| < 1 := by
      simpa only [Real.dist_eq] using! hz
    have htriangle := abs_add_le
      (z.re - s) s
    have heq : z.re - s + s = z.re := by ring
    rw [heq] at htriangle
    linarith
  have hkzero := stripPoissonKernel_integrable
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)
  have hmoment :=
    harmonic_stripPoissonKernel_zero_abs_integrable
  have hmajor : Integrable majorant := by
    dsimp only [majorant]
    exact
      ((hkzero.const_mul
        (A * (2 + |s|))).add
        (hmoment.const_mul (A * ℓ))).const_mul C
  have hmeas :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        AEStronglyMeasurable (integrand z) := by
    filter_upwards [] with z
    dsimp only [integrand]
    have hk : Measurable
        (fun T : ℝ =>
          stripPoissonKernel (z.im / ℓ) T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    have hbT : Measurable
        (fun T : ℝ => b (z.re - ℓ * T)) := by
      exact hb.measurable.comp (by fun_prop)
    exact ((hk.mul hbT).aestronglyMeasurable).indicator hS
  have hdom :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        ∀ᵐ T : ℝ,
          ‖integrand z T‖ ≤ majorant T := by
    filter_upwards [hlower, hupper, hrealbound]
      with z hzbelow hzupper hzreal
    filter_upwards [] with T
    dsimp only [integrand, majorant]
    by_cases hT : T ∈ S
    · rw [Set.indicator_of_mem hT]
      have hkernel :=
        stripPoissonKernel_le_center_of_lower_of_abs_ge
          hzbelow hzupper hδ
          (show δ ≤ |T| from hT)
      have hkpos := stripPoissonKernel_pos
        hzbelow (by linarith) T
      have hzero := stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T
      have htri := abs_sub z.re (ℓ * T)
      have hmul : |ℓ * T| = ℓ * |T| := by
        rw [abs_mul, abs_of_pos hℓ]
      rw [hmul] at htri
      have hdata :
          |b (z.re - ℓ * T)| ≤
            A * (2 + |s| + ℓ * |T|) := by
        calc
          |b (z.re - ℓ * T)| ≤
              A * (1 + |z.re - ℓ * T|) :=
            hbound _
          _ ≤ A * (2 + |s| + ℓ * |T|) := by
            apply mul_le_mul_of_nonneg_left _ hA
            linarith
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos hkpos, Real.norm_eq_abs]
      change
        stripPoissonKernel (z.im / ℓ) T *
          |b (z.re - ℓ * T)| ≤ _
      calc
        stripPoissonKernel (z.im / ℓ) T *
            |b (z.re - ℓ * T)| ≤
          (C * stripPoissonKernel 0 T) *
            (A * (2 + |s| + ℓ * |T|)) := by
          exact mul_le_mul hkernel hdata
            (abs_nonneg _)
            (mul_nonneg hC.le hzero.le)
        _ = C *
              ((A * (2 + |s|)) *
                  stripPoissonKernel 0 T +
                (A * ℓ) *
                  (stripPoissonKernel 0 T * |T|)) := by
          ring
    · rw [Set.indicator_of_notMem hT, norm_zero]
      have hzero := stripPoissonKernel_pos
        (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1) T
      exact mul_nonneg hC.le
        (add_nonneg
          (mul_nonneg (by positivity) hzero.le)
          (mul_nonneg (by positivity)
            (mul_nonneg hzero.le (abs_nonneg T))))
  have hpoint :
      ∀ᵐ T : ℝ,
        Tendsto
          (fun z : ℂ => integrand z T)
          (𝓝[U] z₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with T
    dsimp only [integrand]
    by_cases hT : T ∈ S
    · have hTne : T ≠ 0 := by
        intro hzero
        subst T
        have hbad : δ ≤ (0 : ℝ) := by
          simpa [S] using! hT
        linarith
      simp_rw [Set.indicator_of_mem hT]
      have hkernel :=
        (stripPoissonKernel_tendsto_zero_bottom_of_ne
          hTne).comp hσ
      have hcont : Continuous
          (fun z : ℂ => b (z.re - ℓ * T)) := by
        exact hb.comp (by fun_prop)
      have hdatum :
          Tendsto
            (fun z : ℂ => b (z.re - ℓ * T))
            (𝓝[U] z₀)
            (𝓝 (b (s - ℓ * T))) := by
        convert! hcont.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds using 1;
            simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
              sub_self, sub_zero, z₀]
      simpa only [comp_apply, zero_mul] using! hkernel.mul hdatum
    · simpa only [Set.indicator_of_notMem hT] using!
        (tendsto_const_nhds :
          Tendsto (fun _ : ℂ => (0 : ℝ))
            (𝓝[U] z₀) (𝓝 (0 : ℝ)))
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ))
      majorant
      hmeas hdom hmajor hpoint
  simpa only [integrand, integral_indicator hS, integral_zero] using! hDCT

private theorem harmonic_bottom_joint_tendsto_zero_of_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hcentral : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b (t - ℓ * T)))
    (s : ℝ) (hszero : b s = 0) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) - Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) - Complex.I * (ℓ : ℂ)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨η, hη, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp hb.continuousAt)
      (ε / 2) hhalf
  let δ : ℝ := η / (2 * ℓ)
  have hδ : 0 < δ := by
    try dsimp [δ]
    positivity
  let S : Set ℝ := {T : ℝ | δ ≤ |T|}
  have hS : MeasurableSet S :=
    (isClosed_le continuous_const
      continuous_abs).measurableSet
  have hfar :=
    harmonic_bottom_far_joint_tendsto_zero
      hℓ hb hA hbound s hδ
  have hfarevent :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        ‖∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ < ε / 2 := by
    have hmetric :=
      (Metric.tendsto_nhds.mp hfar)
        (ε / 2) hhalf
    filter_upwards [hmetric] with z hz
    simpa only [Real.norm_eq_abs, dist_zero_right] using! hz
  have hlower :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        -1 < z.im / ℓ := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    apply (lt_div_iff₀ hℓ).2
    simpa only [neg_mul, one_mul] using! hz.1
  have hσ := harmonic_bottom_normalized_height_tendsto
    hℓ s
  have hupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        z.im / ℓ ≤ 0 := by
    have h := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact h.mono (fun z hz => hz.le)
  have hreal := harmonic_bottom_real_tendsto
    (ℓ := ℓ) s
  have hrealclose :
      ∀ᶠ z : ℂ in 𝓝[U] z₀,
        |z.re - s| < η / 2 := by
    have hball := hreal.eventually
      (Metric.ball_mem_nhds s (half_pos hη))
    filter_upwards [hball]
      with z hz
    simpa only [Real.dist_eq] using! hz
  filter_upwards [hlower, hupper,
    hfarevent, hrealclose]
    with z hzbelow hzupper hzfar hzreal
  have hzabove : z.im / ℓ < 1 := by linarith
  have hg : Continuous
      (fun T : ℝ => b (z.re - ℓ * T)) :=
    hb.comp (by fun_prop)
  have hproduct :=
    stripPoissonKernel_lower_product_integrable
      hzbelow hzupper hg (hcentral z.re)
  have hk := stripPoissonKernel_integrable
    hzbelow hzabove
  have hmajor : Integrable
      (fun T : ℝ =>
        (ε / 2) * stripPoissonKernel
          (z.im / ℓ) T) :=
    hk.const_mul (ε / 2)
  have hpositive :
      0 ≤ᵐ[(volume : Measure ℝ)]
        (fun T : ℝ =>
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T) := by
    filter_upwards [] with T
    exact mul_nonneg hhalf.le
      (stripPoissonKernel_pos
        hzbelow hzabove T).le
  have hnear :
      ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤ ε / 2 := by
    calc
      ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤
        ∫ T in Sᶜ,
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T := by
        apply norm_integral_le_of_norm_le
          hmajor.integrableOn
        filter_upwards [ae_restrict_mem hS.compl]
          with T hT
        have hTsmall : |T| < δ := by
          have hnot : ¬ δ ≤ |T| := by
            intro hge
            exact hT (show T ∈ S from hge)
          exact lt_of_not_ge hnot
        have hscaled : ℓ * |T| < η / 2 := by
          try dsimp [δ] at hTsmall
          have hm := mul_lt_mul_of_pos_left
            hTsmall hℓ
          have heq : ℓ * (η / (2 * ℓ)) =
              η / 2 := by
            field_simp [hℓ.ne']
          rw [heq] at hm
          exact hm
        have htriangle := abs_sub
          (z.re - s) (ℓ * T)
        have hmul : |ℓ * T| = ℓ * |T| := by
          rw [abs_mul, abs_of_pos hℓ]
        rw [hmul] at htriangle
        have harg :
            |(z.re - ℓ * T) - s| < η := by
          have hring :
              (z.re - ℓ * T) - s =
                (z.re - s) - ℓ * T := by ring
          rw [hring]
          linarith
        have hbdist :
            dist (z.re - ℓ * T) s < η := by
          rw [Real.dist_eq]
          exact harg
        have hbsmall := hcontrol hbdist
        have hbabs :
            |b (z.re - ℓ * T)| < ε / 2 := by
          simpa only [hszero, dist_zero_right, Real.norm_eq_abs] using! hbsmall
        have hkpos := stripPoissonKernel_pos
          hzbelow hzabove T
        rw [norm_mul, Real.norm_eq_abs,
          abs_of_pos hkpos, Real.norm_eq_abs]
        linarith [mul_nonneg hkpos.le
          (sub_nonneg.mpr hbabs.le)]
      _ ≤ ∫ T : ℝ,
          (ε / 2) *
            stripPoissonKernel (z.im / ℓ) T :=
        setIntegral_le_integral
          hmajor hpositive
      _ = (ε / 2) *
          stripBottomMass (z.im / ℓ) := by
        rw [integral_const_mul,
          integral_stripPoissonKernel
            hzbelow hzabove]
      _ ≤ ε / 2 := by
        have hmass :=
          (stripBottomMass_lt_one hzbelow).le
        linarith [mul_nonneg hhalf.le
          (sub_nonneg.mpr hmass)]
  have hsplit := integral_add_compl hS hproduct
  rw [dist_zero_right]
  calc
    ‖∫ T : ℝ,
        stripPoissonKernel (z.im / ℓ) T *
          b (z.re - ℓ * T)‖ =
      ‖(∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) +
        (∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))‖ := by
      rw [hsplit]
    _ ≤ ‖∫ T in S,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ +
        ‖∫ T in Sᶜ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ :=
      norm_add_le _ _
    _ < ε := by linarith

private theorem lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ((d : ℝ) / 2)) T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
              (z.re - ((d : ℝ) / 2) * T))
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) -
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (lowerGammaBoundaryCapped
        ((d : ℝ) / 2) R D s)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let b : ℝ → ℝ := lowerGammaBoundaryCapped ℓ R D
  let b₀ : ℝ → ℝ := fun y => b y - b s
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ := (s : ℂ) - Complex.I * (ℓ : ℂ)
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  have hb : Continuous b :=
    lowerGammaBoundaryCapped_continuous hℓ R D
  have hb₀ : Continuous b₀ := by
    try dsimp [b₀]
    fun_prop
  obtain ⟨A, hA, hbound⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear hd R D
  let A₀ : ℝ := A + |b s|
  have hA₀ : 0 ≤ A₀ := by
    try dsimp [A₀]
    positivity
  have hbound₀ : ∀ y : ℝ,
      |b₀ y| ≤ A₀ * (1 + |y|) := by
    intro y
    have htriangle := abs_sub (b y) (b s)
    have hbmain : |b y| ≤ A * (1 + |y|) := by
      exact hbound y
    have hy : 0 ≤ |y| := abs_nonneg y
    have hbs : 0 ≤ |b s| := abs_nonneg _
    try dsimp [b₀, A₀]
    linarith [mul_nonneg hbs hy]
  have hcentral : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b (t - ℓ * T)) := by
    intro t
    exact lowerGammaBoundaryCapped_central_poisson_shift_integrable
      hd R D t
  have hkcentral := stripPoissonKernel_integrable
    (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)
  have hcentral₀ : ∀ t : ℝ,
      Integrable (fun T : ℝ =>
        stripPoissonKernel 0 T * b₀ (t - ℓ * T)) := by
    intro t
    have hsub := (hcentral t).sub
      (hkcentral.mul_const (b s))
    convert! hsub using 1
    ext T
    try dsimp [b₀]
    ring
  have hzero := harmonic_bottom_joint_tendsto_zero_of_zero
    hℓ hb₀ hA₀ hbound₀ hcentral₀ s
      (show b₀ s = 0 by simp only [sub_self, b₀])
  have hσ := harmonic_bottom_normalized_height_tendsto
    hℓ s
  have hmasscontinuous : Continuous stripBottomMass := by
    unfold stripBottomMass
    fun_prop
  have hmass : Tendsto
      (fun z : ℂ => stripBottomMass (z.im / ℓ))
      (𝓝[U] z₀) (𝓝 (1 : ℝ)) := by
    convert! hmasscontinuous.continuousAt.tendsto.comp hσ
      using 1; norm_num [stripBottomMass]
  have hsum := hzero.add (hmass.mul_const (b s))
  have hσupper :
      ∀ᶠ z : ℂ in 𝓝[U] z₀, z.im / ℓ ≤ 0 := by
    have hevent := hσ.eventually
      (eventually_lt_nhds
        (show (-1 : ℝ) < 0 by norm_num))
    exact hevent.mono fun z hz => hz.le
  have heq :
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) =ᶠ[𝓝[U] z₀]
      (fun z : ℂ =>
        (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          stripBottomMass (z.im / ℓ) * b s) := by
    filter_upwards [self_mem_nhdsWithin, hσupper]
      with z hz hzupper
    have hzlower : -1 < z.im / ℓ := by
      apply (lt_div_iff₀ hℓ).2
      simpa only [neg_mul, one_mul] using! hz.1
    have hzabove : z.im / ℓ < 1 := by linarith
    have hg₀ : Continuous
        (fun T : ℝ => b₀ (z.re - ℓ * T)) := by
      exact hb₀.comp (by fun_prop)
    have hprod₀ :=
      stripPoissonKernel_lower_product_integrable
        hzlower hzupper hg₀ (hcentral₀ z.re)
    have hk := stripPoissonKernel_integrable
      hzlower hzabove
    have hconst := hk.mul_const (b s)
    calc
      (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) =
        ∫ T : ℝ,
          (stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T) +
           stripPoissonKernel (z.im / ℓ) T * b s) := by
          congr 1
          funext T
          try dsimp [b₀]
          ring
      _ = (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          ∫ T : ℝ,
            stripPoissonKernel (z.im / ℓ) T * b s :=
        integral_add hprod₀ hconst
      _ = (∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b₀ (z.re - ℓ * T)) +
          stripBottomMass (z.im / ℓ) * b s := by
        rw [integral_mul_const,
          integral_stripPoissonKernel hzlower hzabove]
  have hresult := hsum.congr' heq.symm
  simpa [ℓ, b, U, z₀] using! hresult

private theorem stripPoissonKernel_tendsto_zero_top
    (T : ℝ) :
    Tendsto (fun σ : ℝ => stripPoissonKernel σ T)
      (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hangle : stripAngle (1 : ℝ) = Real.pi := by
    unfold stripAngle
    ring
  have hden :
      4 * (Real.cosh (Real.pi * T / 2) -
        Real.cos (stripAngle (1 : ℝ))) ≠ 0 := by
    rw [hangle, Real.cos_pi]
    have hcosh := Real.one_le_cosh (Real.pi * T / 2)
    linarith
  have hnum : ContinuousAt
      (fun σ : ℝ => Real.sin (stripAngle σ)) 1 := by
    unfold stripAngle
    fun_prop
  have hdencont : ContinuousAt
      (fun σ : ℝ =>
        4 * (Real.cosh (Real.pi * T / 2) -
          Real.cos (stripAngle σ))) 1 := by
    unfold stripAngle
    fun_prop
  have h := (hnum.div hdencont hden).tendsto
  simpa only [stripPoissonKernel, Pi.div_apply, hangle, Real.sin_pi, Real.cos_pi, sub_neg_eq_add,
    zero_div] using! h

private theorem harmonic_top_normalized_height_tendsto
    {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    Tendsto
      (fun z : ℂ => z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) + Complex.I * (ℓ : ℂ)))
      (𝓝 (1 : ℝ)) := by
  have hcontinuous : Continuous
      (fun z : ℂ => z.im / ℓ) := by
    fun_prop
  convert! hcontinuous.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds using 1;
      simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul, zero_add,
        ne_eq, hℓ.ne',
        not_false_eq_true, div_self]

private theorem harmonic_upper_joint_tendsto_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ]
        ((s : ℂ) + Complex.I * (ℓ : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let U : Set ℂ :=
    Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ :=
    (s : ℂ) + Complex.I * (ℓ : ℂ)
  have hσ : Tendsto
      (fun z : ℂ => z.im / ℓ)
        (𝓝[U] z₀) (𝓝 (1 : ℝ)) :=
    harmonic_top_normalized_height_tendsto hℓ s
  have hreal : Tendsto Complex.re
      (𝓝[U] z₀) (𝓝 s) := by
    convert! Complex.continuous_re.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds using 1;
      simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        add_zero, z₀]
  have hnonneg : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      0 ≤ z.im / ℓ := by
    have h := hσ.eventually
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    exact h.mono (fun z hz => hz.le)
  have habove : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      z.im / ℓ < 1 := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    apply (div_lt_iff₀ hℓ).2
    simpa only [one_mul] using! hz.2
  have hrealbound : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      |z.re| ≤ |s| + 1 := by
    have hball := hreal.eventually
      (Metric.ball_mem_nhds s
        (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hball] with z hz
    have hsmall : |z.re - s| < 1 := by
      simpa only [Real.dist_eq] using! hz
    have htri := abs_add_le (z.re - s) s
    have heq : z.re - s + s = z.re := by ring
    rw [heq] at htri
    linarith
  have hmajor : Integrable
      (fun T : ℝ =>
        (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|)) :=
    (stripPoissonExponentialMajorant_integrable.const_mul
      (A * (2 + |s|))).add
      (harmonic_stripPoissonExponentialMajorant_abs_integrable.const_mul
        (A * ℓ))
  have hmeas : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      AEStronglyMeasurable
        (fun T : ℝ =>
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)) := by
    filter_upwards [] with z
    have hk : Measurable
        (fun T : ℝ => stripPoissonKernel (z.im / ℓ) T) := by
      unfold stripPoissonKernel stripAngle
      fun_prop
    have hdatum : Measurable
        (fun T : ℝ => b (z.re - ℓ * T)) :=
      hb.measurable.comp (by fun_prop)
    exact (hk.mul hdatum).aestronglyMeasurable
  have hdom : ∀ᶠ z : ℂ in 𝓝[U] z₀,
      ∀ᵐ T : ℝ,
        ‖stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T)‖ ≤
          (A * (2 + |s|)) *
              stripPoissonExponentialMajorant T +
            (A * ℓ) *
              (stripPoissonExponentialMajorant T * |T|) := by
    filter_upwards [hnonneg, habove, hrealbound]
      with z hznonneg hzabove hzreal
    filter_upwards [] with T
    have hzbelow : -1 < z.im / ℓ := by linarith
    have hkpos := stripPoissonKernel_pos hzbelow hzabove T
    have hkbound :=
      stripPoissonKernel_le_exponentialMajorant_of_nonneg
        hznonneg hzabove T
    have hmajorpos : 0 ≤ stripPoissonExponentialMajorant T := by
      unfold stripPoissonExponentialMajorant
      positivity
    have htri := abs_sub z.re (ℓ * T)
    have hmul : |ℓ * T| = ℓ * |T| := by
      rw [abs_mul, abs_of_pos hℓ]
    rw [hmul] at htri
    have hdata :
        |b (z.re - ℓ * T)| ≤
          A * (2 + |s| + ℓ * |T|) := by
      calc
        |b (z.re - ℓ * T)| ≤
          A * (1 + |z.re - ℓ * T|) := hbound _
        _ ≤ A * (2 + |s| + ℓ * |T|) := by
          apply mul_le_mul_of_nonneg_left _ hA
          linarith
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos hkpos, Real.norm_eq_abs]
    calc
      stripPoissonKernel (z.im / ℓ) T *
          |b (z.re - ℓ * T)| ≤
        stripPoissonExponentialMajorant T *
          (A * (2 + |s| + ℓ * |T|)) :=
            mul_le_mul hkbound hdata
              (abs_nonneg _) hmajorpos
      _ = (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|) := by
            ring
  have hpoint : ∀ᵐ T : ℝ,
      Tendsto
        (fun z : ℂ =>
          stripPoissonKernel (z.im / ℓ) T *
            b (z.re - ℓ * T))
        (𝓝[U] z₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with T
    have hk :=
      (stripPoissonKernel_tendsto_zero_top T).comp hσ
    have hcont : Continuous
        (fun z : ℂ => b (z.re - ℓ * T)) :=
      hb.comp (by fun_prop)
    have hdatum : Tendsto
        (fun z : ℂ => b (z.re - ℓ * T))
        (𝓝[U] z₀) (𝓝 (b (s - ℓ * T))) := by
      convert! hcont.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds using 1;
          simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
            sub_self, add_zero, z₀]
    simpa only [comp_apply, zero_mul] using! hk.mul hdatum
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (f := fun _ : ℝ => (0 : ℝ))
      (fun T : ℝ =>
        (A * (2 + |s|)) *
            stripPoissonExponentialMajorant T +
          (A * ℓ) *
            (stripPoissonExponentialMajorant T * |T|))
      hmeas hdom hmajor hpoint
  simpa only [integral_zero] using! h

private theorem exists_antiFourierWitness_eventually_capped_bottom_majorant
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ y : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp (lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y) := by
  obtain ⟨C, hC, hglobal⟩ :=
    antiFourierWitness_normalizedMellinStrip_uniform_bound hd w
  let D₀ : ℝ := Real.log (C + 1)
  have hD₀ : Real.exp D₀ = C + 1 := by
    try dsimp [D₀]
    apply Real.exp_log
    linarith
  refine ⟨D₀, ?_⟩
  intro D hD y
  have hbounded :
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ C := by
    apply hglobal
    · simp only [ofReal_div, ofReal_natCast, ofReal_ofNat, sub_im, ofReal_im, mul_im, I_re,
      div_ofNat_im,
        natCast_im, zero_div, mul_zero, I_im, div_ofNat_re, natCast_re, one_mul, zero_add,
          zero_sub, Std.le_refl]
    · simp only [ofReal_div, ofReal_natCast, ofReal_ofNat, sub_im, ofReal_im, mul_im, I_re,
      div_ofNat_im,
        natCast_im, zero_div, mul_zero, I_im, div_ofNat_re, natCast_re, one_mul, zero_add,
          zero_sub, neg_le_self_iff]
      have hdim : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
  have hcapped :
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp D := by
    calc
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ C :=
        hbounded
      _ ≤ C + 1 := by linarith
      _ = Real.exp D₀ := hD₀.symm
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hD
  by_cases hy : y = 0
  · subst y
    simpa only [ofReal_zero, ofReal_div, ofReal_natCast, ofReal_ofNat, zero_sub,
      lowerGammaBoundaryCapped,
      ↓reduceIte, ge_iff_le] using! hcapped
  · unfold lowerGammaBoundaryCapped
    rw [ite_eq_right hy]
    by_cases hmin :
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤ D
    · rw [min_eq_left hmin]
      exact
        antiFourierWitness_normalizedMellinStrip_bottom_norm_le_gamma
          hd hR w y hy
    · rw [min_eq_right (le_of_not_ge hmin)]
      exact hcapped

private theorem lowerStripCappedGammaOuter_bottom_re_joint_tendsto
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) -
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (lowerGammaBoundaryCapped
        ((d : ℝ) / 2) R D s)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ := (s : ℂ) - Complex.I * (ℓ : ℂ)
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  have hpoisson :=
    lowerGammaBoundaryCapped_bottom_poisson_joint_tendsto
      hd R D s
  have heq :
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter ℓ R D z).re) =ᶠ[𝓝[U] z₀]
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            lowerGammaBoundaryCapped ℓ R D
              (z.re - ℓ * T)) := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    have hbelow : -1 < z.im / ℓ := by
      apply (lt_div_iff₀ hℓ).2
      simpa only [neg_mul, one_mul] using! hz.1
    have habove : z.im / ℓ < 1 := by
      apply (div_lt_iff₀ hℓ).2
      simpa only [one_mul] using! hz.2
    have hrepr :
        (z.re : ℂ) + Complex.I *
          (((z.im / ℓ * ℓ : ℝ) : ℂ)) = z := by
      apply Complex.ext
      · simp only [ofReal_mul, ofReal_div, add_re, ofReal_re, mul_re, I_re, div_ofReal_re,
        div_ofReal_im, ofReal_im,
          zero_div, mul_zero, sub_zero, zero_mul, I_im, mul_im, add_zero, sub_self]
      · simp only [isUnit_iff_ne_zero, ne_eq, hℓ.ne', not_false_eq_true, IsUnit.div_mul_cancel,
        add_im, ofReal_im,
          mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul, zero_add]
    rw [← hrepr]
    simpa [ℓ, hℓ.ne'] using!
      (lowerStripCappedGammaOuter_re_dimension
        (R := R) (D := D) hd hbelow habove z.re)
  have hresult := hpoisson.congr' heq.symm
  simpa [ℓ, U, z₀] using! hresult

private theorem lowerStripCappedGammaOuter_top_re_joint_tendsto
    {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
      (𝓝[Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
          ((s : ℂ) +
            Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)))
      (𝓝 (0 : ℝ)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let z₀ : ℂ := (s : ℂ) + Complex.I * (ℓ : ℂ)
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hbound⟩ :=
    lowerGammaBoundaryCapped_dimension_abs_le_linear hd R D
  have hcontinuous :=
    lowerGammaBoundaryCapped_continuous hℓ R D
  have hpoisson := harmonic_upper_joint_tendsto_zero
    hℓ hcontinuous hA hbound s
  have heq :
      (fun z : ℂ =>
        (lowerStripCappedGammaOuter ℓ R D z).re) =ᶠ[𝓝[U] z₀]
      (fun z : ℂ =>
        ∫ T : ℝ,
          stripPoissonKernel (z.im / ℓ) T *
            lowerGammaBoundaryCapped ℓ R D
              (z.re - ℓ * T)) := by
    filter_upwards [self_mem_nhdsWithin]
      with z hz
    have hbelow : -1 < z.im / ℓ := by
      apply (lt_div_iff₀ hℓ).2
      simpa only [neg_mul, one_mul] using! hz.1
    have habove : z.im / ℓ < 1 := by
      apply (div_lt_iff₀ hℓ).2
      simpa only [one_mul] using! hz.2
    have hrepr :
        (z.re : ℂ) + Complex.I *
          (((z.im / ℓ * ℓ : ℝ) : ℂ)) = z := by
      apply Complex.ext
      · simp only [ofReal_mul, ofReal_div, add_re, ofReal_re, mul_re, I_re, div_ofReal_re,
        div_ofReal_im, ofReal_im,
          zero_div, mul_zero, sub_zero, zero_mul, I_im, mul_im, add_zero, sub_self]
      · simp only [isUnit_iff_ne_zero, ne_eq, hℓ.ne', not_false_eq_true, IsUnit.div_mul_cancel,
        add_im, ofReal_im,
          mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul, zero_add]
    rw [← hrepr]
    simpa [ℓ, hℓ.ne'] using!
      (lowerStripCappedGammaOuter_re_dimension
        (R := R) (D := D) hd hbelow habove z.re)
  have hresult := hpoisson.congr' heq.symm
  simpa [ℓ, U, z₀] using! hresult

private noncomputable def horizontalStripRealTraceExtension
    (a b : ℝ) (H : ℂ → ℝ)
    (bottom top : ℝ → ℝ) (z : ℂ) : ℝ :=
  if z.im = a then bottom z.re
  else if z.im = b then top z.re
  else H z

private theorem horizontalStrip_closed_eq_open_union_edges
    {a b : ℝ} (hab : a < b) :
    (Complex.im ⁻¹' Icc a b) =
      ((Complex.im ⁻¹' Ioo a b) ∪
        (Complex.im ⁻¹' {a})) ∪
        (Complex.im ⁻¹' {b}) := by
  ext z
  change
    (a ≤ z.im ∧ z.im ≤ b) ↔
      (((a < z.im ∧ z.im < b) ∨ z.im = a) ∨
        z.im = b)
  constructor
  · intro hz
    by_cases hbottom : z.im = a
    · exact Or.inl (Or.inr hbottom)
    by_cases htop : z.im = b
    · exact Or.inr htop
    exact Or.inl (Or.inl
      ⟨lt_of_le_of_ne hz.1 (Ne.symm hbottom),
        lt_of_le_of_ne hz.2 htop⟩)
  · intro hz
    rcases hz with (hinterior | hbottom) | htop
    · exact ⟨hinterior.1.le, hinterior.2.le⟩
    · rw [hbottom]
      exact ⟨le_rfl, hab.le⟩
    · rw [htop]
      exact ⟨hab.le, le_rfl⟩

private theorem horizontalStripRealTraceExtension_continuousOn
    {a b : ℝ} (hab : a < b)
    (H : ℂ → ℝ) (bottom top : ℝ → ℝ)
    (hH : ContinuousOn H (Complex.im ⁻¹' Ioo a b))
    (hbottom : Continuous bottom)
    (htop : Continuous top)
    (hbottomtrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (a : ℂ)))
        (𝓝 (bottom s)))
    (htoptrace : ∀ s : ℝ,
      Tendsto H
        (𝓝[Complex.im ⁻¹' Ioo a b]
          ((s : ℂ) + Complex.I * (b : ℂ)))
        (𝓝 (top s))) :
    ContinuousOn
      (horizontalStripRealTraceExtension a b H bottom top)
      (Complex.im ⁻¹' Icc a b) := by
  let E : ℂ → ℝ :=
    horizontalStripRealTraceExtension a b H bottom top
  let O : Set ℂ := Complex.im ⁻¹' Ioo a b
  let L : Set ℂ := Complex.im ⁻¹' {a}
  let T : Set ℂ := Complex.im ⁻¹' {b}
  have hclosedL : IsClosed L := by
    exact isClosed_singleton.preimage Complex.continuous_im
  have hclosedT : IsClosed T := by
    exact isClosed_singleton.preimage Complex.continuous_im
  have hinterior : ∀ z ∈ O, E z = H z := by
    intro z hz
    have hza : z.im ≠ a := ne_of_gt hz.1
    have hzb : z.im ≠ b := ne_of_lt hz.2
    simp only [horizontalStripRealTraceExtension, hza, ↓reduceIte, hzb, E]
  intro z hz
  have hU : ContinuousWithinAt E O z := by
    by_cases hza : z.im = a
    · have hrepr :
          (z.re : ℂ) + Complex.I * (a : ℂ) = z := by
        apply Complex.ext
        · simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
          sub_self, add_zero]
        · simpa only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
          zero_add] using! hza.symm
      have htrace := hbottomtrace z.re
      rw [hrepr] at htrace
      have hevent : E =ᶠ[𝓝[O] z] H :=
        mem_of_superset self_mem_nhdsWithin hinterior
      change Tendsto E (𝓝[O] z) (𝓝 (E z))
      have hvalue : E z = bottom z.re := by
        simp only [horizontalStripRealTraceExtension, hza, ↓reduceIte, E]
      rw [hvalue]
      exact htrace.congr' hevent.symm
    · by_cases hzb : z.im = b
      · have hrepr :
            (z.re : ℂ) + Complex.I * (b : ℂ) = z := by
          apply Complex.ext
          · simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
            sub_self, add_zero]
          · simpa only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
            zero_add] using! hzb.symm
        have htrace := htoptrace z.re
        rw [hrepr] at htrace
        have hevent : E =ᶠ[𝓝[O] z] H :=
          mem_of_superset self_mem_nhdsWithin hinterior
        change Tendsto E (𝓝[O] z) (𝓝 (E z))
        have hvalue : E z = top z.re := by
          simp only [horizontalStripRealTraceExtension, hzb, (ne_of_gt hab : b ≠ a), ↓reduceIte, E]
        rw [hvalue]
        exact htrace.congr' hevent.symm
      · have hzO : z ∈ O := by
          exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hza),
            lt_of_le_of_ne hz.2 hzb⟩
        exact (hH z hzO).congr hinterior
          (hinterior z hzO)
  have hL : ContinuousWithinAt E L z := by
    by_cases hza : z ∈ L
    · have hreal : z.im = a := hza
      have hc : Continuous
          (fun w : ℂ => bottom w.re) :=
        hbottom.comp Complex.continuous_re
      apply hc.continuousAt.continuousWithinAt.congr
      · intro w hw
        have hwa : w.im = a := hw
        simp only [horizontalStripRealTraceExtension, hwa, ↓reduceIte, E]
      · simp only [horizontalStripRealTraceExtension, hreal, ↓reduceIte, E]
    · apply continuousWithinAt_of_notMem_closure
      rw [hclosedL.closure_eq]
      exact hza
  have hT : ContinuousWithinAt E T z := by
    by_cases hzb : z ∈ T
    · have hreal : z.im = b := hzb
      have hc : Continuous
          (fun w : ℂ => top w.re) :=
        htop.comp Complex.continuous_re
      apply hc.continuousAt.continuousWithinAt.congr
      · intro w hw
        have hwb : w.im = b := hw
        have hwa : w.im ≠ a := by
          rw [hwb]
          exact ne_of_gt hab
        simp only [horizontalStripRealTraceExtension, hwb, (ne_of_gt hab : b ≠ a), ↓reduceIte, E]
      · have hza : z.im ≠ a := by
          rw [hreal]
          exact ne_of_gt hab
        simp only [horizontalStripRealTraceExtension, hreal, (ne_of_gt hab : b ≠ a), ↓reduceIte, E]
    · apply continuousWithinAt_of_notMem_closure
      rw [hclosedT.closure_eq]
      exact hzb
  change ContinuousWithinAt E
    (Complex.im ⁻¹' Icc a b) z
  rw [horizontalStrip_closed_eq_open_union_edges hab]
  exact (hU.union hL).union hT

private noncomputable def lowerStripCappedGammaHarmonic
    (d : ℕ) (R D : ℝ) (z : ℂ) : ℝ :=
  horizontalStripRealTraceExtension
    (-((d : ℝ) / 2)) ((d : ℝ) / 2)
    (fun w : ℂ =>
      (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D w).re)
    (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
    (fun _ : ℝ => 0) z

private theorem lowerStripCappedGammaHarmonic_continuousOn
    {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ContinuousOn (lowerStripCappedGammaHarmonic d R D)
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  unfold lowerStripCappedGammaHarmonic
  apply horizontalStripRealTraceExtension_continuousOn
    (show -((d : ℝ) / 2) < (d : ℝ) / 2 by linarith)
  · exact Complex.continuous_re.comp_continuousOn
      (lowerStripCappedGammaOuter_differentiableOn_dimension
        hd R D).continuousOn
  · exact lowerGammaBoundaryCapped_continuous hℓ R D
  · fun_prop
  · intro s
    simpa only [ofReal_neg, ofReal_div, ofReal_natCast, ofReal_ofNat, mul_neg,
      sub_eq_add_neg] using!
      lowerStripCappedGammaOuter_bottom_re_joint_tendsto
        hd R D s
  · intro s
    simpa only [ofReal_div, ofReal_natCast, ofReal_ofNat] using!
      lowerStripCappedGammaOuter_top_re_joint_tendsto
        hd R D s

private theorem antiFourierWitness_capped_poisson_majorization_of_real_extension
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ)
    (E : ℂ → ℝ)
    (hE : ContinuousOn E
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)))
    (hEinterior : ∀ z : ℂ,
      z.im ∈ Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        E z = (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
    (hEbottom : ∀ z : ℂ,
      z.im = -((d : ℝ) / 2) →
        E z = lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D z.re)
    (hEtop : ∀ z : ℂ,
      z.im = (d : ℝ) / 2 → E z = 0)
    (hcap : ∀ y : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp (lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s : ℝ) :
    ‖normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))‖ ≤
      Real.exp
        (∫ T : ℝ, stripPoissonKernel σ T *
          lowerGammaBoundaryCapped
            ((d : ℝ) / 2) R D
            (s - ((d : ℝ) / 2) * T)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  let U : Set ℂ := Complex.im ⁻¹' Ioo (-ℓ) ℓ
  let S : Set ℂ := Complex.im ⁻¹' Icc (-ℓ) ℓ
  let Z : ℂ → ℂ :=
    normalizedRadialMellinStrip hd w.function R
  let W : ℂ → ℂ := lowerStripCappedGammaOuter ℓ R D
  let f : ℂ → ℂ := fun z => Complex.exp (-(W z)) * Z z
  let N : ℂ → ℝ := fun z => Real.exp (-(E z)) * ‖Z z‖
  have hℓ : 0 < ℓ := half_pos (Nat.cast_pos.mpr hd)
  have hwidth : -ℓ < ℓ := by linarith
  have houter : DifferentiableOn ℂ W U := by
    exact lowerStripCappedGammaOuter_differentiableOn_dimension
      hd R D
  have hZdifferentiable : DifferentiableOn ℂ Z U := by
    exact (antiFourierWitness_normalizedMellinStrip_diffContOnCl
      hd w).differentiableOn
  have hf : DifferentiableOn ℂ f U := by
    exact houter.neg.cexp.mul hZdifferentiable
  have hclosure : closure U = S := by
    try dsimp [U, S]
    rw [Complex.closure_preimage_im,
      closure_Ioo (ne_of_lt hwidth)]
  have hZcontinuous : ContinuousOn Z S := by
    have hcont :=
      (antiFourierWitness_normalizedMellinStrip_diffContOnCl
        hd w).continuousOn
    simpa [Z, U, hclosure, ℓ] using! hcont
  have hN : ContinuousOn N S := by
    try dsimp [N]
    exact hE.neg.rexp.mul hZcontinuous.norm
  have hnonnegative : ∀ z : ℂ,
      z.im ∈ Icc (-ℓ) ℓ → 0 ≤ N z := by
    intro z hz
    exact mul_nonneg (Real.exp_pos _).le
      (norm_nonneg _)
  have hinterior : ∀ z : ℂ,
      z.im ∈ Ioo (-ℓ) ℓ → N z = ‖f z‖ := by
    intro z hz
    have hreal := hEinterior z hz
    try dsimp [N, f, W, Z]
    rw [hreal, norm_mul, Complex.norm_exp,
      Complex.neg_re]
  have hbottom : ∀ z : ℂ,
      z.im = -ℓ → N z ≤ (1 : ℝ) := by
    intro z hz
    have hrepr :
        (z.re : ℂ) - Complex.I * (ℓ : ℂ) = z := by
      apply Complex.ext
      · simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, sub_zero]
      · simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
        zero_add, zero_sub, hz]
    have hzbound : ‖Z z‖ ≤
        Real.exp (lowerGammaBoundaryCapped ℓ R D z.re) := by
      rw [← hrepr]
      simpa [Z, ℓ] using! hcap z.re
    have hboundary := hEbottom z hz
    try dsimp [N]
    rw [hboundary]
    calc
      Real.exp
          (-(lowerGammaBoundaryCapped ℓ R D z.re)) *
          ‖Z z‖ ≤
        Real.exp
          (-(lowerGammaBoundaryCapped ℓ R D z.re)) *
          Real.exp
            (lowerGammaBoundaryCapped ℓ R D z.re) :=
          mul_le_mul_of_nonneg_left hzbound
            (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        simp only [neg_add_cancel, Real.exp_zero]
  have htop : ∀ z : ℂ,
      z.im = ℓ → N z ≤ (1 : ℝ) := by
    intro z hz
    have hrepr :
        (z.re : ℂ) + Complex.I * (ℓ : ℂ) = z := by
      apply Complex.ext
      · simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero]
      · simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, ofReal_re, one_mul,
        zero_add, hz]
    have hzbound : ‖Z z‖ ≤ (1 : ℝ) := by
      rw [← hrepr]
      exact antiFourierWitness_normalizedMellinStrip_top_norm_le_one
        hd w z.re
    try dsimp [N]
    rw [hEtop z hz]
    simpa only [neg_zero, Real.exp_zero, one_mul, ge_iff_le] using! hzbound
  let z : ℂ := (s : ℂ) +
    Complex.I * (((σ * ℓ : ℝ) : ℂ))
  have hzbelow : -ℓ ≤ z.im := by
    try dsimp [z]
    simp only [Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im, one_mul, zero_add]
    linarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
  have hzabove : z.im ≤ ℓ := by
    try dsimp [z]
    simp only [Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.ofReal_re,
      zero_mul, Complex.I_im, one_mul, zero_add]
    linarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have hmax : N z ≤ (1 : ℝ) :=
    horizontalStrip_norm_extension_majorization
      hwidth (by norm_num) f N hf hN
      hnonnegative hinterior hbottom htop
      (antiFourierWitness_cappedWeightedMellinStrip_growth
        hd w D)
      hzbelow hzabove
  have hzinterior : z.im ∈ Ioo (-ℓ) ℓ := by
    try dsimp [z]
    simp only [Set.mem_Ioo,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im,
      one_mul, zero_add]
    constructor
    · linarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · linarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have hreal := hEinterior z hzinterior
  have hpoisson := lowerStripCappedGammaOuter_re_dimension
    (R := R) (D := D) hd hbelow habove s
  have hEz : E z =
      ∫ T : ℝ,
        stripPoissonKernel σ T *
          lowerGammaBoundaryCapped ℓ R D (s - ℓ * T) := by
    calc
      E z = (lowerStripCappedGammaOuter ℓ R D z).re := hreal
      _ = _ := by
        simpa only [ofReal_mul, ofReal_div, ofReal_natCast, ofReal_ofNat, ℓ, z] using! hpoisson
  have hweighted :
      Real.exp (-(E z)) * ‖Z z‖ ≤ (1 : ℝ) := hmax
  have hscale :=
    mul_le_mul_of_nonneg_left hweighted
      (Real.exp_pos (E z)).le
  have hfinal : ‖Z z‖ ≤ Real.exp (E z) := by
    convert! hscale using 1
    · rw [← mul_assoc, ← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero, one_mul]
    · simp only [mul_one]
  rw [hEz] at hfinal
  simpa [z, Z, ℓ] using! hfinal

private theorem exists_antiFourierWitness_capped_poisson_majorization
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    ∃ D₀ : ℝ,
      ∀ D : ℝ, D₀ ≤ D →
        ∀ {σ : ℝ}, -1 < σ → σ < 1 →
          ∀ s : ℝ,
            ‖normalizedRadialMellinStrip hd w.function R
              ((s : ℂ) + Complex.I *
                (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
              Real.exp
                (∫ T : ℝ,
                  stripPoissonKernel σ T *
                    lowerGammaBoundaryCapped
                      ((d : ℝ) / 2) R D
                      (s - ((d : ℝ) / 2) * T)) := by
  obtain ⟨D₀, hbottom⟩ :=
    exists_antiFourierWitness_eventually_capped_bottom_majorant
      hd hR w
  refine ⟨D₀, ?_⟩
  intro D hD σ hbelow habove s
  apply antiFourierWitness_capped_poisson_majorization_of_real_extension
    hd w D (lowerStripCappedGammaHarmonic d R D)
    (lowerStripCappedGammaHarmonic_continuousOn hd R D)
  · intro z hz
    have hza : z.im ≠ -((d : ℝ) / 2) :=
      ne_of_gt hz.1
    have hzb : z.im ≠ (d : ℝ) / 2 :=
      ne_of_lt hz.2
    simp only [lowerStripCappedGammaHarmonic, horizontalStripRealTraceExtension, hza,
      ↓reduceIte, hzb]
  · intro z hz
    simp only [lowerStripCappedGammaHarmonic, horizontalStripRealTraceExtension, hz, ↓reduceIte]
  · intro z hz
    have hℓ : 0 < (d : ℝ) / 2 :=
      half_pos (Nat.cast_pos.mpr hd)
    have hne : (d : ℝ) / 2 ≠ -((d : ℝ) / 2) := by
      linarith
    simp only [lowerStripCappedGammaHarmonic, horizontalStripRealTraceExtension, hz, hne,
      ↓reduceIte]
  · exact hbottom D hD
  · exact hbelow
  · exact habove

end

section

open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

private theorem stripPoissonKernel_shifted_centered_interval_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (-r) r,
      stripPoissonKernel σ (s - x)) ≤
      ∫ x in Icc (-r) r,
        stripPoissonKernel σ (0 - x) := by
  have hleft :
      (∫ x in Icc (-r) r,
        stripPoissonKernel σ (s - x)) =
        ∫ x in Icc (s - r) (s + r),
          stripPoissonKernel σ x := by
    rw [integral_Icc_eq_integral_Ioc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← intervalIntegral.integral_of_le
        (by linarith : s - r ≤ s + r),
      intervalIntegral.integral_comp_sub_left]
    congr 1; ring
  have hright :
      (∫ x in Icc (-r) r,
        stripPoissonKernel σ (0 - x)) =
        ∫ x in Icc (-r) r,
          stripPoissonKernel σ x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    simpa only [zero_sub] using! stripPoissonKernel_neg σ x
  rw [hleft, hright]
  exact stripPoissonKernel_centered_interval_max
    hbelow habove hr s

private noncomputable def stripPoissonWeightedMeasure
    (σ s : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun x : ℝ =>
      ENNReal.ofReal (stripPoissonKernel σ (s - x)))

private theorem stripPoissonWeightedMeasure_apply_Icc
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s a b : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc a b) =
      ENNReal.ofReal
        (∫ x in Icc a b,
          stripPoissonKernel σ (s - x)) := by
  unfold stripPoissonWeightedMeasure
  rw [MeasureTheory.withDensity_apply _ measurableSet_Icc]
  have hint :
      IntegrableOn
        (fun x : ℝ => stripPoissonKernel σ (s - x))
        (Icc a b) :=
    ((stripPoissonKernel_integrable hbelow habove).comp_sub_left s).integrableOn
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc a b)]
        (fun x : ℝ => stripPoissonKernel σ (s - x)) :=
    Filter.Eventually.of_forall
      (fun x => (stripPoissonKernel_pos hbelow habove (s - x)).le)
  exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm

private theorem stripPoissonWeightedMeasure_centered_interval_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc (-r) r) ≤
      stripPoissonWeightedMeasure σ 0 (Icc (-r) r) := by
  rw [stripPoissonWeightedMeasure_apply_Icc hbelow habove,
    stripPoissonWeightedMeasure_apply_Icc hbelow habove]
  exact ENNReal.ofReal_le_ofReal
    (stripPoissonKernel_shifted_centered_interval_max
      hbelow habove hr s)

private theorem stripPoissonWeightedMeasure_superlevel_le
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) (s : ℝ) :
    stripPoissonWeightedMeasure σ s
        {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ 0
        {x : ℝ | t < f x} := by
  obtain ⟨r, hr, hinner, houter⟩ :=
    even_antitone_superlevel_interval heven hanti hsupport ht
  have hinterval :
      stripPoissonWeightedMeasure σ 0 (Ioo (-r) r) =
        stripPoissonWeightedMeasure σ 0 (Icc (-r) r) := by
    unfold stripPoissonWeightedMeasure
    exact measure_congr Ioo_ae_eq_Icc
  calc
    stripPoissonWeightedMeasure σ s
        {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ s
        (Icc (-r) r) :=
      measure_mono houter
    _ ≤ stripPoissonWeightedMeasure σ 0
        (Icc (-r) r) :=
      stripPoissonWeightedMeasure_centered_interval_max
        hbelow habove hr s
    _ = stripPoissonWeightedMeasure σ 0
        (Ioo (-r) r) :=
      hinterval.symm
    _ ≤ stripPoissonWeightedMeasure σ 0
        {x : ℝ | t < f x} :=
      measure_mono hinner

private theorem even_antitone_poisson_lintegral_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫⁻ x : ℝ,
      ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ s) ≤
      ∫⁻ x : ℝ,
        ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ 0 := by
  rw [lintegral_eq_lintegral_meas_lt
    (stripPoissonWeightedMeasure σ s)
      (Filter.Eventually.of_forall hfnonneg)
      hfmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt
      (stripPoissonWeightedMeasure σ 0)
      (Filter.Eventually.of_forall hfnonneg)
      hfmeas.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with t ht
  exact stripPoissonWeightedMeasure_superlevel_le
    hbelow habove heven hanti hsupport ht s

private theorem stripPoissonKernel_weighted_product_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable (fun x : ℝ =>
      stripPoissonKernel σ (s - x) * f x) := by
  have hkmeas : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hmajor : Integrable (fun x : ℝ =>
      stripPoissonKernel σ 0 * ‖f x‖) :=
    hf.norm.const_mul (stripPoissonKernel σ 0)
  apply hmajor.mono'
  · exact hkmeas.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos (stripPoissonKernel_pos
        hbelow habove (s - x))]
    exact mul_le_mul_of_nonneg_right
      (stripPoissonKernel_antitone_abs hbelow habove
        (x := 0) (y := s - x) (by simp only [abs_zero, abs_nonneg]))
      (norm_nonneg _)

private theorem stripPoissonWeightedMeasure_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable f (stripPoissonWeightedMeasure σ s) := by
  have hkreal : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hknn : Measurable
      (fun x : ℝ =>
        Real.toNNReal (stripPoissonKernel σ (s - x))) :=
    hkreal.real_toNNReal
  unfold stripPoissonWeightedMeasure
  change Integrable f
    ((volume : Measure ℝ).withDensity
      (fun x : ℝ =>
        (Real.toNNReal (stripPoissonKernel σ (s - x)) : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_smul hknn).2
  have hproduct :=
    stripPoissonKernel_weighted_product_integrable
      hbelow habove hf s
  convert! hproduct using 1
  ext x
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (stripPoissonKernel_pos hbelow habove (s - x)).le,
    smul_eq_mul]

private theorem stripPoissonWeightedMeasure_integral
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (f : ℝ → ℝ) (s : ℝ) :
    (∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ s) =
      ∫ x : ℝ, stripPoissonKernel σ (s - x) * f x := by
  have hkreal : Measurable
      (fun x : ℝ => stripPoissonKernel σ (s - x)) := by
    unfold stripPoissonKernel stripAngle
    fun_prop
  have hk : Measurable
      (fun x : ℝ =>
        ENNReal.ofReal (stripPoissonKernel σ (s - x))) :=
    hkreal.ennreal_ofReal
  have hfinite :
      ∀ᵐ x : ℝ ∂volume,
        ENNReal.ofReal (stripPoissonKernel σ (s - x)) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  unfold stripPoissonWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hk hfinite]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal
    (stripPoissonKernel_pos hbelow habove (s - x)).le]
  rfl

private theorem even_antitone_poisson_convolution_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f)
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫ x : ℝ, stripPoissonKernel σ (s - x) * f x) ≤
      ∫ x : ℝ, stripPoissonKernel σ (0 - x) * f x := by
  have hsint := stripPoissonWeightedMeasure_integrable
    hbelow habove hf s
  have hzero := stripPoissonWeightedMeasure_integrable
    hbelow habove hf 0
  have hsnonneg :
      0 ≤ᵐ[stripPoissonWeightedMeasure σ s] f :=
    Filter.Eventually.of_forall hfnonneg
  have hzerononneg :
      0 ≤ᵐ[stripPoissonWeightedMeasure σ 0] f :=
    Filter.Eventually.of_forall hfnonneg
  have hlin := even_antitone_poisson_lintegral_max
    hbelow habove hfmeas hfnonneg heven hanti hsupport s
  rw [← ofReal_integral_eq_lintegral_ofReal hsint hsnonneg,
    ← ofReal_integral_eq_lintegral_ofReal hzero hzerononneg] at hlin
  have hcenter :
      0 ≤ ∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ 0 :=
    integral_nonneg hfnonneg
  have hreal := (ENNReal.ofReal_le_ofReal_iff hcenter).mp hlin
  rw [stripPoissonWeightedMeasure_integral hbelow habove,
    stripPoissonWeightedMeasure_integral hbelow habove] at hreal
  exact hreal

private theorem lowerGammaBoundaryCapped_dimension_neg
    {d : ℕ} (R D y : ℝ) :
    lowerGammaBoundaryCapped ((d : ℝ) / 2) R D (-y) =
      lowerGammaBoundaryCapped ((d : ℝ) / 2) R D y := by
  by_cases hy : y = 0
  · simp only [lowerGammaBoundaryCapped, hy, neg_zero, ↓reduceIte]
  · simp only [lowerGammaBoundaryCapped, neg_eq_zero, hy, ↓reduceIte,
    lowerGammaBoundaryLog_dimension_neg R hy]

private theorem lowerGammaBoundaryCapped_dimension_antitoneOn
    {d : ℕ} (R D : ℝ) :
    AntitoneOn
      (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_cases hxzero : x = 0
  · subst x
    unfold lowerGammaBoundaryCapped
    simp only [ite_true]
    split_ifs with hyzero
    · exact le_rfl
    · exact min_le_right _ _
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
    have hgamma := lowerGammaBoundaryLog_dimension_antitoneOn
      (d := d) R (show x ∈ Ioi (0 : ℝ) from hxpos)
        (show y ∈ Ioi (0 : ℝ) from hypos) hxy
    simp only [lowerGammaBoundaryCapped,
      ite_eq_right hxpos.ne', ite_eq_right hypos.ne']
    exact min_le_min hgamma (le_refl D)

private theorem lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large
    {d : ℕ} (hd : 2 ≤ d) {c Y n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hlarge : max 1 (8 * Real.pi * c ^ 2 * Real.exp n) ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤ -n := by
  have hyone : 1 ≤ |Y| :=
    le_trans (le_max_left 1 _) hlarge
  have hY : Y ≠ 0 := by
    intro h
    norm_num [h] at hyone
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hden : 0 < |Y| := abs_pos.mpr hY
  have hradius : 8 * Real.pi * c ^ 2 * Real.exp n ≤ |Y| :=
    le_trans (le_max_right 1 _) hlarge
  have hexpcancel : Real.exp n * Real.exp (-n) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero n)]
  have hscaled := mul_le_mul_of_nonneg_right
    hradius (Real.exp_pos (-n)).le
  have hratio :
      4 * Real.pi * c ^ 2 / |Y| ≤
        (1 / 2 : ℝ) * Real.exp (-n) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hratio_pos : 0 < 4 * Real.pi * c ^ 2 / |Y| :=
    div_pos hA hden
  have hlogratio :
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        -(Real.log (2 : ℝ)) - n := by
    calc
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          Real.log ((1 / 2 : ℝ) * Real.exp (-n)) :=
        Real.log_le_log hratio_pos hratio
      _ = -(Real.log (2 : ℝ)) - n := by
        rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
          (Real.exp_ne_zero _), Real.log_exp,
          one_div, Real.log_inv]
        ring
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hpiabs : 3 ≤ Real.pi * |Y| := by
    linarith [Real.pi_gt_three,
      mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
        (sub_nonneg.mpr hyone)]
  have harg : 1 ≤ Real.pi * |Y| / 2 := by
    linarith
  have hexpthree : 4 ≤ Real.exp (3 : ℝ) := by
    linarith [Real.add_one_le_exp (3 : ℝ)]
  have hexpsmall :
      Real.exp ((-Real.pi) * |Y|) ≤ (1 / 4 : ℝ) := by
    calc
      Real.exp ((-Real.pi) * |Y|) ≤ Real.exp (-3 : ℝ) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (Real.exp (3 : ℝ))⁻¹ := Real.exp_neg 3
      _ ≤ (1 / 4 : ℝ) := by
        simpa only [one_div] using!
          (one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 4) hexpthree)
  have hcoth := lowerCoth_log_le_four_exp_neg_two harg
  have hexp :
      Real.exp (-2 * (Real.pi * |Y| / 2)) =
        Real.exp ((-Real.pi) * |Y|) := by
    congr 1
    ring
  rw [hexp] at hcoth
  have hcorrection :
      (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
    linarith
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast hd
  have hlognonneg : 0 ≤ Real.log (2 : ℝ) + n := by
    linarith
  have hmain :
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          -(Real.log (2 : ℝ)) - n := by
    calc
      ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        ((d : ℝ) / 2) * (-(Real.log (2 : ℝ)) - n) :=
        mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ ≤ -(Real.log (2 : ℝ)) - n := by
        linarith [mul_nonneg
          (sub_nonneg.mpr hℓ) hlognonneg]
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hY
  linarith

private noncomputable def lowerGammaScaledCappedClipped
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y) + n)
    0

private theorem lowerGammaScaledCappedClipped_continuous
    {d : ℕ} (hd : 0 < d) (c D n : ℝ) :
    Continuous (lowerGammaScaledCappedClipped d c D n) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hcap := lowerGammaBoundaryCapped_continuous
    hℓ (c * Real.sqrt d) D
  have hscale : Continuous (fun Y : ℝ => ((d : ℝ) / 2) * Y) := by
    fun_prop
  exact ((hcap.comp hscale).add continuous_const).max
    continuous_const

private theorem lowerGammaScaledCappedClipped_neg
    (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n (-Y) =
      lowerGammaScaledCappedClipped d c D n Y := by
  unfold lowerGammaScaledCappedClipped
  have hmul : ((d : ℝ) / 2) * (-Y) =
      -(((d : ℝ) / 2) * Y) := by ring
  rw [hmul,
    lowerGammaBoundaryCapped_dimension_neg
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)]

private theorem lowerGammaScaledCappedClipped_antitoneOn
    (d : ℕ) (c D n : ℝ) :
    AntitoneOn (lowerGammaScaledCappedClipped d c D n)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have hℓ : 0 ≤ (d : ℝ) / 2 := by positivity
  have hgamma :=
    lowerGammaBoundaryCapped_dimension_antitoneOn
      (d := d) (c * Real.sqrt d) D
      (show ((d : ℝ) / 2) * x ∈ Ici (0 : ℝ) from
        mul_nonneg hℓ hx)
      (show ((d : ℝ) / 2) * y ∈ Ici (0 : ℝ) from
        mul_nonneg hℓ hy)
      (mul_le_mul_of_nonneg_left hxy hℓ)
  unfold lowerGammaScaledCappedClipped
  exact max_le_max (by linarith) (le_refl (0 : ℝ))

private theorem lowerGammaScaledCappedClipped_support
    {d : ℕ} (hd : 2 ≤ d) {c D n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) :
    Function.support (lowerGammaScaledCappedClipped d c D n) ⊆
      Icc (-(max 1 (8 * Real.pi * c ^ 2 * Real.exp n)))
        (max 1 (8 * Real.pi * c ^ 2 * Real.exp n)) := by
  intro Y hY
  change lowerGammaScaledCappedClipped d c D n Y ≠ 0 at hY
  have hsmall : |Y| < max 1 (8 * Real.pi * c ^ 2 * Real.exp n) := by
    by_contra hnot
    have hlarge : max 1
        (8 * Real.pi * c ^ 2 * Real.exp n) ≤ |Y| :=
      le_of_not_gt hnot
    have hnonpos :=
      lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large
        hd hc hn hlarge
    have hyone : 1 ≤ |Y| :=
      le_trans (le_max_left 1 _) hlarge
    have hyzero : Y ≠ 0 := by
      intro hzero
      norm_num [hzero] at hyone
    have hℓ : 0 < (d : ℝ) / 2 := by
      positivity
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hyzero
    apply hY
    unfold lowerGammaScaledCappedClipped
    rw [lowerGammaBoundaryCapped, ite_eq_right harg]
    apply max_eq_right
    have hmin := min_le_left
      (lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) D
    linarith
  exact ⟨(neg_lt_of_abs_lt hsmall).le,
    (lt_of_abs_lt hsmall).le⟩

private theorem lowerGammaScaledCappedClipped_integrable
    {d : ℕ} (hd : 2 ≤ d) {c D n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) :
    Integrable (lowerGammaScaledCappedClipped d c D n) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  apply (lowerGammaScaledCappedClipped_continuous
    hdpos c D n).integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc
      (lowerGammaScaledCappedClipped_support hd hc hn)

private theorem lowerGammaScaledCappedClipped_poisson_convolution_max
    {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaScaledCappedClipped d c D n Y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact even_antitone_poisson_convolution_max
    hbelow habove
    (lowerGammaScaledCappedClipped_integrable hd hc hn)
    (lowerGammaScaledCappedClipped_continuous
      hdpos c D n).measurable
    (fun Y => le_max_right _ _)
    (lowerGammaScaledCappedClipped_neg d c D n)
    (lowerGammaScaledCappedClipped_antitoneOn d c D n)
    (lowerGammaScaledCappedClipped_support hd hc hn)
    s

private theorem lowerGammaScaledCapped_poisson_product_integrable
    {d : ℕ} (hd : 0 < d) {R D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
          (((d : ℝ) / 2) * Y)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hz :
      ((((d : ℝ) / 2) * s : ℝ) : ℂ) +
          Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ) ∈
        Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, one_mul, zero_add]
    constructor
    · linarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · linarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have houter := lowerStripCappedGammaOuter_integrable_dimension
    hd (R := R) (D := D) hz
  have hreal := houter.re
  have hscaled := hreal.comp_mul_left' hℓ.ne'
  have hproduct := hscaled.const_mul ((d : ℝ) / 2)
  convert! hproduct using 1
  ext Y
  change
    stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
          (((d : ℝ) / 2) * Y) =
      ((d : ℝ) / 2) *
        (stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2)
          (((((d : ℝ) / 2) * s : ℝ) : ℂ) +
            Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))
          (((d : ℝ) / 2) * Y) *
            (lowerGammaBoundaryCapped ((d : ℝ) / 2) R D
              (((d : ℝ) / 2) * Y) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [stripRegularizedHolomorphicPoissonKernel_re
    hℓ hbelow habove]
  have harg :
      (((d : ℝ) / 2) * s - ((d : ℝ) / 2) * Y) /
          ((d : ℝ) / 2) = s - Y := by
    field_simp [hℓ.ne']
  rw [harg]
  field_simp [hℓ.ne']

private theorem lowerGammaScaled_poisson_product_integrable
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (((d : ℝ) / 2) * Y)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have hz :
      ((((d : ℝ) / 2) * s : ℝ) : ℂ) +
          Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ) ∈
        Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [Set.mem_preimage, Set.mem_Ioo,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, one_mul, zero_add]
    constructor
    · linarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · linarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have houter := lowerStripGammaOuter_integrable_dimension
    hd (R := R) hz
  have hreal := houter.re
  have hscaled := hreal.comp_mul_left' hℓ.ne'
  have hproduct := hscaled.const_mul ((d : ℝ) / 2)
  convert! hproduct using 1
  ext Y
  change
    stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (((d : ℝ) / 2) * Y) =
      ((d : ℝ) / 2) *
        (stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2)
          (((((d : ℝ) / 2) * s : ℝ) : ℂ) +
            Complex.I * ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))
          (((d : ℝ) / 2) * Y) *
            (lowerGammaBoundaryLog ((d : ℝ) / 2) R
              (((d : ℝ) / 2) * Y) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [stripRegularizedHolomorphicPoissonKernel_re
    hℓ hbelow habove]
  have harg :
      (((d : ℝ) / 2) * s - ((d : ℝ) / 2) * Y) /
          ((d : ℝ) / 2) = s - Y := by
    field_simp [hℓ.ne']
  rw [harg]
  field_simp [hℓ.ne']

private noncomputable def lowerGammaScaledCappedLowerClip
    (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
    (-n)

private theorem lowerGammaScaledCappedClipped_eq_lowerClip_add
    (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n Y =
      lowerGammaScaledCappedLowerClip d c D n Y + n := by
  unfold lowerGammaScaledCappedClipped
    lowerGammaScaledCappedLowerClip
  have h := max_add_add_right
    (lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
    (-n) n
  simpa only [neg_add_cancel] using! h

private theorem lowerGammaScaledCappedLowerClip_poisson_integrable
    {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y) := by
  have hbase := lowerGammaScaledCapped_poisson_product_integrable
    hd (R := c * Real.sqrt d) (D := D) hbelow habove s
  have hk := (stripPoissonKernel_integrable hbelow habove).comp_sub_left s
  have hconstant := hk.const_mul (-n)
  have hmax := hbase.sup hconstant
  convert! hmax using 1
  ext Y
  change
    stripPoissonKernel σ (s - Y) *
        max
          (lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
          (-n) =
      max
        (stripPoissonKernel σ (s - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
        (-n * stripPoissonKernel σ (s - Y))
  rw [mul_max_of_nonneg _ _
    (stripPoissonKernel_pos hbelow habove (s - Y)).le]
  ring_nf

private theorem lowerGammaScaledCappedClipped_integral_eq
    {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) =
      (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y) +
          n * stripBottomMass σ := by
  have hclip :=
    lowerGammaScaledCappedLowerClip_poisson_integrable
      hd (c := c) (D := D) (n := n)
      hbelow habove s
  have hk := (stripPoissonKernel_integrable
    hbelow habove).comp_sub_left s
  have hnkernel := hk.const_mul n
  calc
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) =
        ∫ Y : ℝ,
          (stripPoissonKernel σ (s - Y) *
            lowerGammaScaledCappedLowerClip d c D n Y) +
          n * stripPoissonKernel σ (s - Y) := by
      apply integral_congr_ae
      filter_upwards [] with Y
      rw [lowerGammaScaledCappedClipped_eq_lowerClip_add]
      ring
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        ∫ Y : ℝ, n * stripPoissonKernel σ (s - Y) :=
      integral_add hclip hnkernel
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        n * ∫ Y : ℝ, stripPoissonKernel σ (s - Y) := by
      rw [integral_const_mul]
    _ =
        (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip d c D n Y) +
        n * stripBottomMass σ := by
      rw [integral_sub_left_eq_self
        (stripPoissonKernel σ) volume s,
        integral_stripPoissonKernel hbelow habove]

private theorem lowerGammaScaledCappedLowerClip_poisson_convolution_max
    {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedLowerClip d c D n Y) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hplus := lowerGammaScaledCappedClipped_poisson_convolution_max
    (D := D) hd hc hn hbelow habove s
  rw [lowerGammaScaledCappedClipped_integral_eq
    hdpos hbelow habove s,
    lowerGammaScaledCappedClipped_integral_eq
      hdpos hbelow habove 0] at hplus
  linarith

private theorem lowerGammaScaledCappedLowerClip_poisson_tendsto
    {d : ℕ} (hd : 0 < d) {c D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip
            d c D (n : ℝ) Y)
      atTop
      (𝓝 (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))) := by
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)
  let K : ℝ → ℝ := fun Y => stripPoissonKernel σ (s - Y)
  have hbase : Integrable (fun Y : ℝ => K Y * b Y) :=
    lowerGammaScaledCapped_poisson_product_integrable
      hd (R := c * Real.sqrt d) (D := D)
      hbelow habove s
  apply tendsto_integral_of_dominated_convergence
    (fun Y : ℝ => |K Y * b Y|)
  · intro n
    exact
      (lowerGammaScaledCappedLowerClip_poisson_integrable
        hd (c := c) (D := D) (n := (n : ℝ))
        hbelow habove s).aestronglyMeasurable
  · exact hbase.abs
  · intro n
    filter_upwards [] with Y
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hclip :
        |max (b Y) (-(n : ℝ))| ≤ |b Y| := by
      rcases le_total (b Y) (-(n : ℝ))
        with hle | hle
      · rw [max_eq_right hle,
          abs_of_nonpos (neg_nonpos.mpr hn),
          abs_of_nonpos (le_trans hle (neg_nonpos.mpr hn))]
        linarith
      · rw [max_eq_left hle]
    change
      ‖K Y * max (b Y) (-(n : ℝ))‖ ≤ |K Y * b Y|
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hclip (abs_nonneg (K Y))
  · filter_upwards [] with Y
    have ht : Tendsto (fun n : ℕ => -(n : ℝ))
        atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hevent : ∀ᶠ n : ℕ in atTop, -(n : ℝ) ≤ b Y :=
      ht.eventually (Iic_mem_atBot (b Y))
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    change
      K Y * b Y = K Y * max (b Y) (-(n : ℝ))
    rw [max_eq_left hn]

private theorem lowerGammaScaledCapped_poisson_convolution_max
    {d : ℕ} (hd : 2 ≤ d) {c D σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaBoundaryCapped ((d : ℝ) / 2)
        (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) D (((d : ℝ) / 2) * Y) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact le_of_tendsto_of_tendsto
    (lowerGammaScaledCappedLowerClip_poisson_tendsto
      hdpos hbelow habove s)
    (lowerGammaScaledCappedLowerClip_poisson_tendsto
      hdpos hbelow habove 0)
    (Filter.Eventually.of_forall (fun n : ℕ =>
      lowerGammaScaledCappedLowerClip_poisson_convolution_max
        hd hc (Nat.cast_nonneg n) hbelow habove s))

private theorem lowerGammaScaledCapped_poisson_tendsto
    {d : ℕ} (hd : 0 < d) {c σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) (n : ℝ) (((d : ℝ) / 2) * Y))
      atTop
      (𝓝 (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y))) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y)
  let K : ℝ → ℝ := fun Y => stripPoissonKernel σ (s - Y)
  have hbase : Integrable (fun Y : ℝ => K Y * b Y) :=
    lowerGammaScaled_poisson_product_integrable
      hd (R := c * Real.sqrt d) hbelow habove s
  apply tendsto_integral_of_dominated_convergence
    (fun Y : ℝ => |K Y * b Y|)
  · intro n
    exact
      (lowerGammaScaledCapped_poisson_product_integrable
        hd (R := c * Real.sqrt d) (D := (n : ℝ))
        hbelow habove s).aestronglyMeasurable
  · exact hbase.abs
  · intro n
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hY
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hclip : |min (b Y) (n : ℝ)| ≤ |b Y| := by
      rcases le_total (b Y) (n : ℝ) with hle | hle
      · rw [min_eq_left hle]
      · rw [min_eq_right hle,
          abs_of_nonneg hn,
          abs_of_nonneg (le_trans hn hle)]
        exact hle
    change
      ‖K Y *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)‖ ≤
        |K Y * b Y|
    rw [lowerGammaBoundaryCapped, ite_eq_right harg,
      Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hclip (abs_nonneg (K Y))
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hY
    have ht : Tendsto (fun n : ℕ => (n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    have hevent : ∀ᶠ n : ℕ in atTop, b Y ≤ (n : ℝ) :=
      ht.eventually (Ici_mem_atTop (b Y))
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    change
      K Y * b Y =
        K Y * lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)
    rw [lowerGammaBoundaryCapped, ite_eq_right harg, min_eq_left hn]

private theorem lowerGammaScaled_poisson_convolution_max
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact le_of_tendsto_of_tendsto
    (lowerGammaScaledCapped_poisson_tendsto
      (c := c) hdpos hbelow habove s)
    (lowerGammaScaledCapped_poisson_tendsto
      (c := c) hdpos hbelow habove 0)
    (Filter.Eventually.of_forall (fun n : ℕ =>
      lowerGammaScaledCapped_poisson_convolution_max
        (D := (n : ℝ)) hd hc hbelow habove s))

private theorem lowerStripPoissonMajorant_scaled_convolution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R σ s : ℝ) :
    lowerStripPoissonMajorant ℓ R σ s =
      ∫ Y : ℝ,
        stripPoissonKernel σ (s / ℓ - Y) *
          lowerGammaBoundaryLog ℓ R (ℓ * Y) := by
  let f : ℝ → ℝ := fun Y =>
    stripPoissonKernel σ (s / ℓ - Y) *
      lowerGammaBoundaryLog ℓ R (ℓ * Y)
  calc
    lowerStripPoissonMajorant ℓ R σ s =
        ∫ T : ℝ, f (s / ℓ - T) := by
      unfold lowerStripPoissonMajorant
      apply integral_congr_ae
      filter_upwards [] with T
      try dsimp [f]
      have harg : s / ℓ - (s / ℓ - T) = T := by
        ring
      rw [harg]
      congr 1
      field_simp [hℓ.ne']
    _ = ∫ Y : ℝ, f Y :=
      integral_sub_left_eq_self f volume (s / ℓ)

private theorem lowerStripPoissonMajorant_dimension_centered_max
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ s ≤
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ s,
    lowerStripPoissonMajorant_scaled_convolution
      hℓ (c * Real.sqrt d) σ 0]
  simp only [zero_div]
  exact lowerGammaScaled_poisson_convolution_max
    hd hc hbelow habove (s / ((d : ℝ) / 2))

private theorem lowerRiemannLog_zero (T : ℝ) :
    lowerRiemannLog T 0 = Real.log (|T| / 2) := by
  unfold lowerRiemannLog
  have hsqrt : Real.sqrt (T ^ 2 / 4) = |T| / 2 := by
    rw [show T ^ 2 / 4 = (T / 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_div]
    norm_num
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, hsqrt]

private theorem lowerRiemannLog_scaled_factor
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (j : ℝ) :
    Real.sqrt (j ^ 2 + (ℓ * T / 2) ^ 2) =
      ℓ * Real.sqrt ((j / ℓ) ^ 2 + T ^ 2 / 4) := by
  have hinside :
      j ^ 2 + (ℓ * T / 2) ^ 2 =
        ℓ ^ 2 * ((j / ℓ) ^ 2 + T ^ 2 / 4) := by
    field_simp [hℓ.ne']
    ring
  rw [hinside, Real.sqrt_mul (sq_nonneg ℓ),
    Real.sqrt_sq_eq_abs, abs_of_pos hℓ]

private theorem lowerGammaBoundaryLog_integer_scaled
    {k : ℕ} (hk : 0 < k) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R ((k : ℝ) * T) =
      (k : ℝ) * Real.log (Real.pi * R ^ 2 / (k : ℝ)) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T ((j : ℝ) / (k : ℝ)) := by
  have hkreal : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hy : (k : ℝ) * T ≠ 0 :=
    mul_ne_zero hkreal.ne' hT
  rw [lowerGammaBoundaryLog_integer k R hy]
  have hterm (j : ℕ) :
      Real.log
        (Real.sqrt
          ((j : ℝ) ^ 2 + (((k : ℝ) * T) / 2) ^ 2)) =
        Real.log (k : ℝ) +
          lowerRiemannLog T ((j : ℝ) / (k : ℝ)) := by
    rw [lowerRiemannLog_scaled_factor hkreal]
    have hrad :
        0 < ((j : ℝ) / (k : ℝ)) ^ 2 + T ^ 2 / 4 := by
      linarith [sq_nonneg ((j : ℝ) / (k : ℝ)),
        sq_pos_of_ne_zero hT]
    rw [Real.log_mul hkreal.ne'
      (Real.sqrt_pos.mpr hrad).ne']
    rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ _j ∈ Finset.range k, Real.log (k : ℝ)) =
        (k : ℝ) * Real.log (k : ℝ) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  rw [Real.log_div
    (show Real.pi * R ^ 2 ≠ 0 by positivity) hkreal.ne']
  simp only [div_eq_mul_inv]
  ring

private theorem lowerGammaBoundaryLog_halfInteger_scaled
    (k : ℕ) {ℓ R T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ℓ R (ℓ * T) =
      ℓ * Real.log (Real.pi * R ^ 2 / ℓ) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * ℓ * |T| / 2)) -
        (1 / 2 : ℝ) * Real.log (|T| / 2) := by
  have hℓ : 0 < ℓ := by
    rw [hℓeq]
    positivity
  have hy : ℓ * T ≠ 0 :=
    mul_ne_zero hℓ.ne' hT
  have hraw := lowerGammaBoundaryLog_halfInteger
    k R hy
  rw [← hℓeq] at hraw
  rw [hraw]
  have hterm (j : ℕ) :
      Real.log
        (Real.sqrt
          (((j : ℝ) + 1 / 2) ^ 2 + (ℓ * T / 2) ^ 2)) =
        Real.log ℓ +
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ) := by
    rw [lowerRiemannLog_scaled_factor hℓ]
    have hrad :
        0 < (((j : ℝ) + 1 / 2) / ℓ) ^ 2 + T ^ 2 / 4 := by
      linarith [sq_nonneg (((j : ℝ) + 1 / 2) / ℓ),
        sq_pos_of_ne_zero hT]
    rw [Real.log_mul hℓ.ne'
      (Real.sqrt_pos.mpr hrad).ne']
    rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ _j ∈ Finset.range k, Real.log ℓ) =
        (k : ℝ) * Real.log ℓ := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  have habs : |ℓ * T| = ℓ * |T| := by
    rw [abs_mul, abs_of_pos hℓ]
  rw [habs]
  have harg :
      Real.pi * (ℓ * |T|) / 2 =
        Real.pi * ℓ * |T| / 2 := by ring
  rw [harg]
  have ht : 0 < |T| / 2 := by positivity
  have hcoth :
      0 < lowerCoth (Real.pi * ℓ * |T| / 2) := by
    apply lowerCoth_pos
    positivity
  have hden : ℓ * |T| / 2 = ℓ * (|T| / 2) := by ring
  rw [hden, Real.log_div hcoth.ne'
    (mul_ne_zero hℓ.ne' ht.ne'),
    Real.log_mul hℓ.ne' ht.ne']
  rw [Real.log_div
    (show Real.pi * R ^ 2 ≠ 0 by positivity) hℓ.ne']
  rw [hℓeq]
  ring

private theorem lowerRiemannLog_continuous
    {T : ℝ} (hT : T ≠ 0) :
    Continuous (lowerRiemannLog T) := by
  have hrad (x : ℝ) : 0 < x ^ 2 + T ^ 2 / 4 := by
    linarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have hsqrt :
      Continuous (fun x : ℝ =>
        Real.sqrt (x ^ 2 + T ^ 2 / 4)) := by
    fun_prop
  unfold lowerRiemannLog
  exact hsqrt.log (fun x =>
    (Real.sqrt_pos.mpr (hrad x)).ne')

private noncomputable def lowerRiemannErrorMajorant (T : ℝ) : ℝ :=
  3 * |lowerRiemannLog T 0| +
    2 * |lowerRiemannLog T 1| +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |T| / 2))

private theorem lowerGammaBoundaryLog_integer_riemann_le
    {k : ℕ} (hk : 0 < k) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R ((k : ℝ) * T) ≤
      (k : ℝ) *
        (Real.log (Real.pi * R ^ 2 / (k : ℝ)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rw [lowerGammaBoundaryLog_integer_scaled hk hR hT]
  have hriemann := (lower_integer_leftRiemann_error hT hk).2
  have hphase := integral_lowerRiemannLog hT
  have hcoth := lowerCoth_log_nonneg
    (show 0 < Real.pi * |T| / 2 by positivity)
  unfold lowerRiemannErrorMajorant
  nlinarith [le_abs_self (lowerRiemannLog T 1),
    neg_le_abs (lowerRiemannLog T 0),
    abs_nonneg (lowerRiemannLog T 0),
    abs_nonneg (lowerRiemannLog T 1)]

private theorem lowerRiemannLog_halfInteger_tail_integral_le
    (k : ℕ) {ℓ T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hT : T ≠ 0) :
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1,
      lowerRiemannLog T x) ≤
        (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
  have hℓ : 0 < ℓ := by
    rw [hℓeq]
    positivity
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    apply (div_le_one hℓ).2
    rw [hℓeq]
    linarith
  have hcont := lowerRiemannLog_continuous hT
  have hint : IntervalIntegrable
      (lowerRiemannLog T) volume ((k : ℝ) / ℓ) 1 :=
    hcont.intervalIntegrable _ _
  have hconst : IntervalIntegrable
      (fun _ : ℝ => lowerRiemannLog T 1)
      volume ((k : ℝ) / ℓ) 1 :=
    intervalIntegrable_const
  have hmono :
      (∫ x in ((k : ℝ) / ℓ)..1,
        lowerRiemannLog T x) ≤
        ∫ _x in ((k : ℝ) / ℓ)..1,
          lowerRiemannLog T 1 := by
    apply intervalIntegral.integral_mono_on
      hratio_le hint hconst
    intro x hx
    apply lowerRiemannLog_monotoneOn hT
    · exact (show x ∈ Ici (0 : ℝ) from
        le_trans hratio_nonneg hx.1)
    · exact (show (1 : ℝ) ∈ Ici (0 : ℝ) by norm_num)
    · exact hx.2
  rw [intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hscaled := mul_le_mul_of_nonneg_left hmono hℓ.le
  have hfactor : ℓ * (1 - (k : ℝ) / ℓ) = (1 / 2 : ℝ) := by
    field_simp [hℓ.ne']
    rw [hℓeq]
    ring
  calc
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1,
      lowerRiemannLog T x) ≤
        ℓ * ((1 - (k : ℝ) / ℓ) *
          lowerRiemannLog T 1) := hscaled
    _ = (1 / 2 : ℝ) * lowerRiemannLog T 1 := by
      rw [← mul_assoc, hfactor]

private theorem lowerGammaBoundaryLog_halfInteger_riemann_le
    (k : ℕ) {ℓ R T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hℓone : 1 ≤ ℓ)
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ℓ R (ℓ * T) ≤
      ℓ * (Real.log (Real.pi * R ^ 2 / ℓ) +
        1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  have hℓ : 0 < ℓ := by linarith
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    apply (div_le_one hℓ).2
    rw [hℓeq]
    linarith
  let q : ℝ → ℝ := lowerRiemannLog T
  have hcont := lowerRiemannLog_continuous hT
  have hfirst : IntervalIntegrable q volume
      (0 : ℝ) ((k : ℝ) / ℓ) :=
    hcont.intervalIntegrable _ _
  have hlast : IntervalIntegrable q volume
      ((k : ℝ) / ℓ) 1 :=
    hcont.intervalIntegrable _ _
  have hsplit :
      (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), q x) +
          (∫ x in ((k : ℝ) / ℓ)..1, q x) =
        ∫ x in (0 : ℝ)..1, q x :=
    intervalIntegral.integral_add_adjacent_intervals
      hfirst hlast
  have hmid := lower_halfInteger_midpointRiemann_error
    hT hℓ k
  have hmidupper :
      ℓ * (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), q x) -
          ∑ j ∈ Finset.range k,
            q (((j : ℝ) + 1 / 2) / ℓ) ≤
        q ((k : ℝ) / ℓ) - q 0 := by
    exact le_trans (le_abs_self _) hmid
  have htail :=
    lowerRiemannLog_halfInteger_tail_integral_le
      k hℓeq hT
  have hsumupper :
      -(∑ j ∈ Finset.range k,
        q (((j : ℝ) + 1 / 2) / ℓ)) ≤
        -ℓ * (∫ x in (0 : ℝ)..1, q x) +
          (q ((k : ℝ) / ℓ) - q 0) +
            (1 / 2 : ℝ) * q 1 := by
    nlinarith
  have hqk : q ((k : ℝ) / ℓ) ≤ q 1 := by
    apply lowerRiemannLog_monotoneOn hT
    · exact (show (k : ℝ) / ℓ ∈ Ici (0 : ℝ) from
        hratio_nonneg)
    · exact (show (1 : ℝ) ∈ Ici (0 : ℝ) by norm_num)
    · exact hratio_le
  have harg : 0 < Real.pi * |T| / 2 := by positivity
  have hargℓ : 0 < Real.pi * ℓ * |T| / 2 := by positivity
  have hargorder :
      Real.pi * |T| / 2 ≤ Real.pi * ℓ * |T| / 2 := by
    linarith [mul_nonneg (sub_nonneg.mpr hℓone)
      (mul_nonneg Real.pi_pos.le (abs_nonneg T))]
  have hcoth := lowerCoth_log_antitoneOn
    harg hargℓ hargorder
  have hphase := integral_lowerRiemannLog hT
  rw [lowerGammaBoundaryLog_halfInteger_scaled
    k hℓeq hR hT,
    ← lowerRiemannLog_zero T]
  unfold lowerRiemannErrorMajorant
  change
    ℓ * Real.log (Real.pi * R ^ 2 / ℓ) -
        ∑ j ∈ Finset.range k,
          q (((j : ℝ) + 1 / 2) / ℓ) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * ℓ * |T| / 2)) -
        (1 / 2 : ℝ) * q 0 ≤
      ℓ * (Real.log (Real.pi * R ^ 2 / ℓ) +
        1 + lowerEndpointPhase T) +
        (3 * |q 0| + 2 * |q 1| +
          (1 / 2 : ℝ) *
            Real.log (lowerCoth (Real.pi * |T| / 2)))
  change -(∫ x in (0 : ℝ)..1, q x) =
    1 + lowerEndpointPhase T at hphase
  nlinarith [le_abs_self (q 1), neg_le_abs (q 0),
    abs_nonneg (q 0), abs_nonneg (q 1)]

private theorem lowerGammaBoundaryLog_dimension_riemann_le
    {d : ℕ} (hd : 2 ≤ d) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R
        (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (Real.pi * R ^ 2 / ((d : ℝ) / 2)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 0 < k := by omega
    have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_riemann_le
      hk hR hT
  · have hk : 0 < k := by omega
    have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    apply lowerGammaBoundaryLog_halfInteger_riemann_le
      k rfl
    · have hkre : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    · exact hR
    · exact hT

private theorem lowerGammaBoundaryLog_dimension_scaled_riemann_le
    {d : ℕ} (hd : 2 ≤ d) {c T : ℝ}
    (hc : 0 < c) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hR : 0 < c * Real.sqrt d :=
    mul_pos hc (Real.sqrt_pos.mpr hdreal)
  have hratio :
      Real.pi * (c * Real.sqrt d) ^ 2 /
          ((d : ℝ) / 2) = 2 * Real.pi * c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hdreal.le]
    field_simp [hdreal.ne']
  have hconstant :
      Real.log (2 * Real.pi * c ^ 2) + 1 =
        Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) := by
    have hfactor :
        2 * Real.pi * Real.exp 1 * c ^ 2 =
          (2 * Real.pi * c ^ 2) * Real.exp 1 := by
      ring
    rw [hfactor,
      Real.log_mul (show 2 * Real.pi * c ^ 2 ≠ 0 by positivity)
        (Real.exp_ne_zero _), Real.log_exp]
  have h := lowerGammaBoundaryLog_dimension_riemann_le
    hd hR hT
  rw [hratio] at h
  calc
    lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * c ^ 2) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := h
    _ = ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
      rw [← hconstant]

private theorem stripPoissonKernel_le_mass_mul_exponential
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripBottomMass σ * stripPoissonExponentialMajorant T := by
  have hbelow : -1 < σ := by linarith
  have hmass := stripBottomMass_pos habove
  have hnormalize := stripNormalizedPoissonKernel_eq_extension
    hbelow habove T
  have hbound := stripNormalizedPoissonExtension_le_majorant
    hzero habove.le T
  have hquotient :
      stripPoissonKernel σ T / stripBottomMass σ ≤
        stripPoissonExponentialMajorant T := by
    change stripNormalizedPoissonKernel σ T ≤
      stripPoissonExponentialMajorant T
    rw [hnormalize]
    exact hbound.2
  have h := (div_le_iff₀ hmass).mp hquotient
  linarith

private theorem stripPoissonExponentialMajorant_abs_moment_integrable :
    Integrable (fun T : ℝ =>
      stripPoissonExponentialMajorant T * |T|) := by
  have hmoment := integrable_abs_pow_mul_exp_neg_mul_abs
    1 (half_pos Real.pi_pos)
  have hscaled := hmoment.const_mul (Real.pi / 2)
  convert! hscaled using 1
  ext T
  simp only [stripPoissonExponentialMajorant, neg_mul, pow_one]
  ring

private theorem stripPoissonKernel_abs_moment_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ => stripPoissonKernel σ T * |T|) := by
  have hbelow : -1 < σ := by linarith
  have hmajor :=
    stripPoissonExponentialMajorant_abs_moment_integrable.const_mul
      (stripBottomMass σ)
  have habsmeas : Measurable (fun T : ℝ => |T|) := by
    fun_prop
  apply hmajor.mono'
    ((stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      habsmeas.aestronglyMeasurable)
  filter_upwards [] with T
  change
    ‖stripPoissonKernel σ T * |T|‖ ≤
      stripBottomMass σ *
        (stripPoissonExponentialMajorant T * |T|)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T),
    abs_abs]
  calc
    stripPoissonKernel σ T * |T| ≤
      (stripBottomMass σ *
        stripPoissonExponentialMajorant T) * |T| :=
      mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_mass_mul_exponential
          hzero habove T) (abs_nonneg T)
    _ = stripBottomMass σ *
        (stripPoissonExponentialMajorant T * |T|) := by
      ring

private theorem stripPoissonKernel_mul_lowerRiemannLog_zero_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerRiemannLog T 0) := by
  have hgamma0 := lowerGammaScaled_poisson_product_integrable
    (d := 2) (by norm_num : 0 < (2 : ℕ))
    (R := (1 : ℝ)) hbelow habove 0
  have hgamma : Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerGammaBoundaryLog 1 1 T) := by
    apply hgamma0.congr
    filter_upwards [] with T
    norm_num [stripPoissonKernel_neg]
  have hk := stripPoissonKernel_integrable hbelow habove
  have hconst := hk.const_mul (Real.log Real.pi)
  have hdifference := hconst.sub hgamma
  apply hdifference.congr
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
    with T hT
  have hidentity :
      lowerGammaBoundaryLog 1 1 T =
        Real.log Real.pi - lowerRiemannLog T 0 := by
    simpa only [Nat.cast_one, one_mul, one_pow, mul_one, div_one, Finset.range_one,
      Finset.sum_singleton,
      CharP.cast_eq_zero] using!
      (lowerGammaBoundaryLog_integer_scaled
        (k := 1) (by norm_num) (R := (1 : ℝ))
        (by norm_num) hT)
  change
    Real.log Real.pi * stripPoissonKernel σ T -
        stripPoissonKernel σ T * lowerGammaBoundaryLog 1 1 T =
      stripPoissonKernel σ T * lowerRiemannLog T 0
  rw [hidentity]
  ring

private theorem lowerRiemannLog_one_nonneg_le (T : ℝ) :
    0 ≤ lowerRiemannLog T 1 ∧
      lowerRiemannLog T 1 ≤ |T| / 2 := by
  have hrad : 0 < (1 : ℝ) + T ^ 2 / 4 := by
    linarith [sq_nonneg T]
  have hsqrtone :
      1 ≤ Real.sqrt ((1 : ℝ) + T ^ 2 / 4) := by
    apply (Real.le_sqrt (by norm_num) hrad.le).2
    linarith [sq_nonneg T]
  have hsqrtupper :
      Real.sqrt ((1 : ℝ) + T ^ 2 / 4) ≤
        1 + |T| / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · linarith [abs_nonneg T, sq_abs T]
  unfold lowerRiemannLog
  simp only [one_pow]
  constructor
  · exact Real.log_nonneg hsqrtone
  · have hlog := Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.mpr hrad)
    linarith

private theorem lowerRiemannLog_one_continuous :
    Continuous (fun T : ℝ => lowerRiemannLog T 1) := by
  have hrad (T : ℝ) : 0 < (1 : ℝ) + T ^ 2 / 4 := by
    linarith [sq_nonneg T]
  have hsqrt :
      Continuous (fun T : ℝ =>
        Real.sqrt ((1 : ℝ) + T ^ 2 / 4)) := by
    fun_prop
  have h := hsqrt.log
    (fun T => (Real.sqrt_pos.mpr (hrad T)).ne')
  simpa only [lowerRiemannLog, one_pow] using! h

private theorem stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * |lowerRiemannLog T 1|) := by
  have hbelow : -1 < σ := by linarith
  have hmoment := stripPoissonKernel_abs_moment_integrable
    hzero habove
  have hmajor := hmoment.const_mul (1 / 2 : ℝ)
  have hmeas :=
    (stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      lowerRiemannLog_one_continuous.abs.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with T
  have hq := lowerRiemannLog_one_nonneg_le T
  change
    ‖stripPoissonKernel σ T * |lowerRiemannLog T 1|‖ ≤
      (1 / 2 : ℝ) * (stripPoissonKernel σ T * |T|)
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T),
    abs_abs, abs_of_nonneg hq.1]
  linarith [mul_nonneg
    (stripPoissonKernel_pos hbelow habove T).le
      (sub_nonneg.mpr hq.2)]

private theorem stripPoissonKernel_mul_abs_lowerRiemannLog_zero_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * |lowerRiemannLog T 0|) := by
  have h :=
    (stripPoissonKernel_mul_lowerRiemannLog_zero_integrable
      hbelow habove).abs
  apply h.congr
  filter_upwards [] with T
  rw [abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T)]

private theorem stripPoissonKernel_mul_coth_log_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T *
        Real.log (lowerCoth (Real.pi * |T| / 2))) := by
  have h := stripPoissonKernel_weighted_product_integrable
    hbelow habove lowerCoth_log_abs_integrable 0
  apply h.congr
  filter_upwards [] with T
  rw [zero_sub, stripPoissonKernel_neg]

private theorem lowerRiemannErrorMajorant_poisson_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T *
        lowerRiemannErrorMajorant T) := by
  have hbelow : -1 < σ := by linarith
  have hqzero :=
    (stripPoissonKernel_mul_abs_lowerRiemannLog_zero_integrable
      hbelow habove).const_mul (3 : ℝ)
  have hone :=
    (stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
      hzero habove).const_mul (2 : ℝ)
  have hcoth :=
    (stripPoissonKernel_mul_coth_log_integrable
      hbelow habove).const_mul (1 / 2 : ℝ)
  have hsum := hqzero.add (hone.add hcoth)
  convert! hsum using 1
  ext T
  change
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T =
      3 * (stripPoissonKernel σ T * |lowerRiemannLog T 0|) +
        (2 * (stripPoissonKernel σ T * |lowerRiemannLog T 1|) +
          (1 / 2 : ℝ) *
            (stripPoissonKernel σ T *
              Real.log (lowerCoth (Real.pi * |T| / 2))))
  unfold lowerRiemannErrorMajorant
  ring

private theorem stripPoissonKernel_mul_lowerEndpointPhase_integrable
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * lowerEndpointPhase T) := by
  have hbelow : -1 < σ := by linarith
  have hmajor :=
    stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable.const_mul
      (stripBottomMass σ)
  have hmeas :=
    (stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      lowerEndpointPhase_continuous.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with T
  change
    ‖stripPoissonKernel σ T * lowerEndpointPhase T‖ ≤
      stripBottomMass σ *
        (stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T)]
  calc
    stripPoissonKernel σ T * ‖lowerEndpointPhase T‖ ≤
      (stripBottomMass σ *
        stripPoissonExponentialMajorant T) *
          ‖lowerEndpointPhase T‖ :=
      mul_le_mul_of_nonneg_right
        (stripPoissonKernel_le_mass_mul_exponential
          hzero habove T) (norm_nonneg _)
    _ = stripBottomMass σ *
        (stripPoissonExponentialMajorant T *
          ‖lowerEndpointPhase T‖) := by ring

private theorem integral_stripPoissonKernel_mul_lowerEndpointPhase
    {σ : ℝ} (habove : σ < 1) :
    (∫ T : ℝ, stripPoissonKernel σ T * lowerEndpointPhase T) =
      stripBottomMass σ * lowerPoissonEndpointExpectation σ := by
  have hmass : stripBottomMass σ ≠ 0 :=
    (stripBottomMass_pos habove).ne'
  unfold lowerPoissonEndpointExpectation
    stripNormalizedPoissonKernel
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with T
  field_simp [hmass]

private noncomputable def lowerRiemannPoissonError (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T

private theorem lowerStripPoissonMajorant_dimension_central_bound
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hzero : 0 ≤ σ) (habove : σ < 1) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 ≤
      ((d : ℝ) / 2) * stripBottomMass σ *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ) +
        lowerRiemannPoissonError σ := by
  have hbelow : -1 < σ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hdpos)
  let ℓ : ℝ := (d : ℝ) / 2
  let A : ℝ := Real.log
    (2 * Real.pi * Real.exp 1 * c ^ 2)
  let K : ℝ → ℝ := stripPoissonKernel σ
  let q : ℝ → ℝ := lowerEndpointPhase
  let E : ℝ → ℝ := lowerRiemannErrorMajorant
  have hleft0 := lowerGammaScaled_poisson_product_integrable
    hdpos (R := c * Real.sqrt d) hbelow habove 0
  have hleft : Integrable (fun T : ℝ =>
      K T * lowerGammaBoundaryLog ℓ
        (c * Real.sqrt d) (ℓ * T)) := by
    simpa only [zero_sub, stripPoissonKernel_neg] using! hleft0
  have hk : Integrable K :=
    stripPoissonKernel_integrable hbelow habove
  have hq : Integrable (fun T : ℝ => K T * q T) :=
    stripPoissonKernel_mul_lowerEndpointPhase_integrable
      hzero habove
  have hE : Integrable (fun T : ℝ => K T * E T) :=
    lowerRiemannErrorMajorant_poisson_integrable
      hzero habove
  have hconstant := hk.const_mul (ℓ * A)
  have hphaseterm := hq.const_mul ℓ
  have hsum := hconstant.add (hphaseterm.add hE)
  have hright : Integrable (fun T : ℝ =>
      K T * (ℓ * (A + q T) + E T)) := by
    convert! hsum using 1
    ext T
    change
      K T * (ℓ * (A + q T) + E T) =
        (ℓ * A) * K T +
          (ℓ * (K T * q T) + K T * E T)
    ring
  have hmono :
      (∫ T : ℝ, K T *
        lowerGammaBoundaryLog ℓ
          (c * Real.sqrt d) (ℓ * T)) ≤
        ∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T) := by
    apply integral_mono_ae hleft hright
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with T hT
    apply mul_le_mul_of_nonneg_left
      (lowerGammaBoundaryLog_dimension_scaled_riemann_le
        hd hc hT)
      (stripPoissonKernel_pos hbelow habove T).le
  have heval :
      (∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T)) =
        ℓ * stripBottomMass σ *
          (A + lowerPoissonEndpointExpectation σ) +
            lowerRiemannPoissonError σ := by
    calc
      (∫ T : ℝ, K T *
          (ℓ * (A + q T) + E T)) =
        ∫ T : ℝ,
          (ℓ * A) * K T +
            (ℓ * (K T * q T) + K T * E T) := by
          apply integral_congr_ae
          filter_upwards [] with T
          ring
      _ =
        (∫ T : ℝ, (ℓ * A) * K T) +
          ((∫ T : ℝ, ℓ * (K T * q T)) +
            ∫ T : ℝ, K T * E T) := by
          have hfirst :=
            integral_add hconstant (hphaseterm.add hE)
          have hsecond := integral_add hphaseterm hE
          simpa only [Pi.add_apply] using!
            hfirst.trans
              (congrArg
                (fun x : ℝ =>
                  (∫ T : ℝ, (ℓ * A) * K T) + x)
                hsecond)
      _ =
        ℓ * stripBottomMass σ *
          (A + lowerPoissonEndpointExpectation σ) +
            lowerRiemannPoissonError σ := by
          rw [integral_const_mul, integral_const_mul,
            integral_stripPoissonKernel hbelow habove,
            integral_stripPoissonKernel_mul_lowerEndpointPhase
              habove]
          change
            (ℓ * A) * stripBottomMass σ +
              (ℓ * (stripBottomMass σ *
                lowerPoissonEndpointExpectation σ) +
                lowerRiemannPoissonError σ) = _
          ring
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ 0]
  simp only [zero_div, zero_sub, stripPoissonKernel_neg]
  exact hmono.trans_eq heval

private theorem exists_lowerStripPoissonMajorant_uniform_negative
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ s : ℝ,
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ s ≤
              -γ * ((d : ℝ) / 2) := by
  have hnegative :=
    eventually_lowerPoissonEndpointSharpCoefficient_neg
      hc hsharp
  have hpositive : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hless : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 :=
    self_mem_nhdsWithin
  obtain ⟨σ, hσpos, hσless, hσnegative⟩ :=
    (hpositive.and (hless.and hnegative)).exists
  have hmass := stripBottomMass_pos hσless
  let A : ℝ :=
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
      lowerPoissonEndpointExpectation σ
  have hA : A < 0 := hσnegative
  let γ : ℝ := -(stripBottomMass σ * A) / 2
  have hγ : 0 < γ := by
    try dsimp [γ]
    linarith [mul_neg_of_pos_of_neg hmass hA]
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hγscale : Tendsto
      (fun d : ℕ => γ * ((d : ℝ) / 2)) atTop atTop := by
    have hmul := hscale.atTop_mul_const hγ
    convert! hmul using 1
    ext d
    ring
  have herror : ∀ᶠ d : ℕ in atTop,
      lowerRiemannPoissonError σ ≤
        γ * ((d : ℝ) / 2) :=
    hγscale.eventually
      (Ici_mem_atTop (lowerRiemannPoissonError σ))
  refine ⟨σ, γ, hσpos, hσless, hγ, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ), herror]
    with d hd hderr
  intro s
  have hcenter := lowerStripPoissonMajorant_dimension_centered_max
    hd hc (by linarith) hσless s
  have hbound :=
    lowerStripPoissonMajorant_dimension_central_bound
      hd hc hσpos.le hσless
  calc
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ s ≤
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 := hcenter
    _ ≤ ((d : ℝ) / 2) * stripBottomMass σ * A +
      lowerRiemannPoissonError σ := hbound
    _ ≤ -γ * ((d : ℝ) / 2) := by
      try dsimp [γ] at hderr ⊢
      linarith

private theorem lowerCoth_log_half_le_of_one_le_abs
    {Y : ℝ} (hY : 1 ≤ |Y|) :
    (1 / 2 : ℝ) *
      Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
  have hpiabs : 3 ≤ Real.pi * |Y| := by
    linarith [Real.pi_gt_three,
      mul_nonneg
        (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
        (sub_nonneg.mpr hY)]
  have harg : 1 ≤ Real.pi * |Y| / 2 := by
    linarith
  have hexpthree : 4 ≤ Real.exp (3 : ℝ) := by
    linarith [Real.add_one_le_exp (3 : ℝ)]
  have hexpsmall :
      Real.exp ((-Real.pi) * |Y|) ≤ (1 / 4 : ℝ) := by
    calc
      Real.exp ((-Real.pi) * |Y|) ≤ Real.exp (-3 : ℝ) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (Real.exp (3 : ℝ))⁻¹ := Real.exp_neg 3
      _ ≤ (1 / 4 : ℝ) := by
        simpa only [one_div] using!
          (one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 4) hexpthree)
  have hcoth := lowerCoth_log_le_four_exp_neg_two harg
  have hexp :
      Real.exp (-2 * (Real.pi * |Y| / 2)) =
        Real.exp ((-Real.pi) * |Y|) := by
    congr 1
    ring
  rw [hexp] at hcoth
  linarith

private theorem lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : 1 ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
        ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * Real.exp 1 * c ^ 2 / |Y|) := by
  have hyzero : Y ≠ 0 := by
    intro hzero
    norm_num [hzero] at hY
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hyzero
  have hcorr := lowerCoth_log_half_le_of_one_le_abs hY
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast hd
  have hlog :
      Real.log (4 * Real.pi * Real.exp 1 * c ^ 2 / |Y|) =
        Real.log (4 * Real.pi * c ^ 2 / |Y|) + 1 := by
    have hfactor :
        4 * Real.pi * Real.exp 1 * c ^ 2 / |Y| =
          (4 * Real.pi * c ^ 2 / |Y|) * Real.exp 1 := by
      field_simp [abs_ne_zero.mpr hyzero]
    rw [hfactor,
      Real.log_mul
        (show 4 * Real.pi * c ^ 2 / |Y| ≠ 0 by positivity)
        (Real.exp_ne_zero _), Real.log_exp]
  rw [hlog]
  linarith

private noncomputable def stripPoissonCoreMass (σ : ℝ) : ℝ :=
  ∫ T in Icc (-1 : ℝ) 1, stripPoissonKernel σ T

private theorem stripPoissonCoreMass_pos
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripPoissonCoreMass σ := by
  have hk := stripPoissonKernel_integrable hbelow habove
  have hkone := stripPoissonKernel_pos hbelow habove 1
  have hconstant : IntegrableOn
      (fun _T : ℝ => stripPoissonKernel σ 1)
      (Icc (-1 : ℝ) 1) :=
    (continuous_const : Continuous
      (fun _T : ℝ => stripPoissonKernel σ 1)).integrableOn_Icc
  have hcompare :
      (∫ _T in Icc (-1 : ℝ) 1,
        stripPoissonKernel σ 1) ≤
        ∫ T in Icc (-1 : ℝ) 1,
          stripPoissonKernel σ T := by
    apply setIntegral_mono_on hconstant hk.integrableOn
      measurableSet_Icc
    intro T hT
    apply stripPoissonKernel_antitone_abs
      hbelow habove
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    exact (abs_le).mpr hT
  have hvalue :
      (∫ _T in Icc (-1 : ℝ) 1,
        stripPoissonKernel σ 1) =
        2 * stripPoissonKernel σ 1 := by
    norm_num
  rw [hvalue] at hcompare
  unfold stripPoissonCoreMass
  linarith

private theorem lowerGammaScaledPositivePart_poisson_exponential_tail
    {d : ℕ} (hd : 2 ≤ d) {c σ C S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hC : 0 < C)
    (hsupport :
      Function.support (lowerGammaScaledPositivePart d c) ⊆
        Icc (-C) C)
    (hmass :
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        C * ((d : ℝ) / 2))
    (hS : C ≤ S) :
    (∫ Y : ℝ,
      stripPoissonKernel σ (S - Y) *
        lowerGammaScaledPositivePart d c Y) ≤
      (stripBottomMass σ * (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * (S - C))) *
          (C * ((d : ℝ) / 2)) := by
  have hbelow : -1 < σ := by linarith
  let E : ℝ :=
    stripBottomMass σ * (Real.pi / 2) *
      Real.exp (-(Real.pi / 2) * (S - C))
  have hE : 0 ≤ E := by
    apply (mul_nonneg_iff_of_pos_right hC).mp
    try dsimp [E]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (stripBottomMass_pos hσone).le
          (by positivity))
        (Real.exp_pos _).le)
      hC.le
  have hp := lowerGammaScaledPositivePart_integrable hd hc
  have hweighted := stripPoissonKernel_weighted_product_integrable
    hbelow hσone hp S
  have hmajor : Integrable
      (fun Y : ℝ => E * lowerGammaScaledPositivePart d c Y) :=
    hp.const_mul E
  calc
    (∫ Y : ℝ,
      stripPoissonKernel σ (S - Y) *
        lowerGammaScaledPositivePart d c Y) ≤
      ∫ Y : ℝ,
        E * lowerGammaScaledPositivePart d c Y := by
      apply integral_mono_ae hweighted hmajor
      filter_upwards [] with Y
      by_cases hzero : lowerGammaScaledPositivePart d c Y = 0
      · simp only [hzero, mul_zero, Std.le_refl]
      · have hY := hsupport hzero
        have hdist : S - C ≤ |S - Y| := by
          rw [abs_of_nonneg (by linarith [hY.2] : 0 ≤ S - Y)]
          linarith [hY.2]
        have hexp :
            Real.exp (-(Real.pi / 2) * |S - Y|) ≤
              Real.exp (-(Real.pi / 2) * (S - C)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos]
        have hkernel : stripPoissonKernel σ (S - Y) ≤ E := by
          calc
            stripPoissonKernel σ (S - Y) ≤
              stripBottomMass σ *
                stripPoissonExponentialMajorant (S - Y) :=
                stripPoissonKernel_le_mass_mul_exponential
                  hσ hσone (S - Y)
            _ = stripBottomMass σ *
                ((Real.pi / 2) *
                  Real.exp (-(Real.pi / 2) * |S - Y|)) := by
                rfl
            _ ≤ stripBottomMass σ *
                ((Real.pi / 2) *
                  Real.exp (-(Real.pi / 2) * (S - C))) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_left hexp
                    (by positivity)
                · exact (stripBottomMass_pos hσone).le
            _ = E := by
              try dsimp [E]
              ring
        exact mul_le_mul_of_nonneg_right hkernel
          (le_max_right _ _)
    _ = E *
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) := by
      rw [integral_const_mul]
    _ ≤ E * (C * ((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hmass hE
    _ = (stripBottomMass σ * (Real.pi / 2) *
        Real.exp (-(Real.pi / 2) * (S - C))) *
          (C * ((d : ℝ) / 2)) := by
      rfl

private theorem lowerStripPoissonMajorant_core_tail_split
    {d : ℕ} (hd : 2 ≤ d) {c σ S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hS : 2 ≤ S) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
      (((d : ℝ) / 2) *
        Real.log ((8 * Real.pi * Real.exp 1 * c ^ 2) / S)) *
          stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
  have hbelow : -1 < σ := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hSpos : 0 < S := by linarith
  let ℓ : ℝ := (d : ℝ) / 2
  let P : ℝ := 4 * Real.pi * Real.exp 1 * c ^ 2
  let A : ℝ := 8 * Real.pi * Real.exp 1 * c ^ 2
  let L : ℝ := ℓ * Real.log (A / S)
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryLog ℓ (c * Real.sqrt d) (ℓ * Y)
  let p : ℝ → ℝ := lowerGammaScaledPositivePart d c
  have hP : 0 < P := by
    try dsimp [P]
    positivity
  have hA : A = 2 * P := by
    try dsimp [A, P]
    ring
  have hb_integrable : Integrable
      (fun T : ℝ => stripPoissonKernel σ T * b (S - T)) := by
    have hbase := lowerGammaScaled_poisson_product_integrable
      hdpos (R := c * Real.sqrt d) hbelow hσone S
    have hcomp := hbase.comp_sub_left S
    convert! hcomp using 1
    ext T
    try dsimp [b, ℓ]
    congr 1; ring_nf
  have hp_integrable : Integrable
      (fun T : ℝ => stripPoissonKernel σ T * p (S - T)) := by
    have hbase := stripPoissonKernel_weighted_product_integrable
      hbelow hσone
      (lowerGammaScaledPositivePart_integrable hd hc) S
    have hcomp := hbase.comp_sub_left S
    convert! hcomp using 1
    ext T
    try dsimp [p]
    congr 1; ring_nf
  have hcore_integrable : Integrable
      (fun T : ℝ =>
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) := by
    have hbase :=
      ((stripPoissonKernel_integrable hbelow hσone).const_mul L).indicator
        (s := Icc (-1 : ℝ) 1) measurableSet_Icc
    convert! hbase using 1
    ext T
    by_cases hT : T ∈ Icc (-1 : ℝ) 1
    · simp only [hT, indicator_of_mem]
      ring
    · simp only [hT, not_false_eq_true, indicator_of_notMem, mul_zero]
  have hnear : ∀ T ∈ Icc (-1 : ℝ) 1, b (S - T) ≤ L := by
    intro T hT
    have hdiff : 0 < S - T := by linarith [hT.2]
    have hlarge : 1 ≤ |S - T| := by
      rw [abs_of_pos hdiff]
      linarith [hT.2]
    have hratio : P / |S - T| ≤ A / S := by
      apply (div_le_div_iff₀ (abs_pos.mpr hdiff.ne') hSpos).2
      rw [abs_of_pos hdiff, hA]
      linarith [mul_nonneg hP.le
        (show 0 ≤ S - 2 * T by linarith [hT.2])]
    have hlog : Real.log (P / |S - T|) ≤
        Real.log (A / S) := by
      apply Real.log_le_log (by positivity)
      exact hratio
    have htail :=
      lowerGammaBoundaryLog_dimension_scaled_log_tail_simple
        hd hc hlarge
    change b (S - T) ≤ ℓ * Real.log (P / |S - T|) at htail
    change b (S - T) ≤ ℓ * Real.log (A / S)
    exact htail.trans
      (mul_le_mul_of_nonneg_left hlog hℓ.le)
  have hpointwise : ∀ T : ℝ,
      stripPoissonKernel σ T * b (S - T) ≤
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T +
          stripPoissonKernel σ T * p (S - T) := by
    intro T
    have hkernel := (stripPoissonKernel_pos hbelow hσone T).le
    have hpnonneg : 0 ≤ p (S - T) := by
      try dsimp [p, lowerGammaScaledPositivePart]
      exact le_max_right _ _
    have hb_le_p : b (S - T) ≤ p (S - T) := by
      try dsimp [b, p, ℓ, lowerGammaScaledPositivePart]
      exact le_max_left _ _
    by_cases hT : T ∈ Icc (-1 : ℝ) 1
    · simp only [Set.indicator_of_mem hT]
      have h := hnear T hT
      linarith [mul_nonneg hkernel hpnonneg,
        mul_nonneg hkernel (sub_nonneg.mpr h)]
    · simp only [Set.indicator_of_notMem hT, mul_zero,
        zero_add]
      exact mul_le_mul_of_nonneg_left hb_le_p hkernel
  have hcore_integral :
      (∫ T : ℝ,
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) =
        L * stripPoissonCoreMass σ := by
    calc
      (∫ T : ℝ,
        stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T) =
        ∫ T : ℝ,
          (Icc (-1 : ℝ) 1).indicator
            (fun T => L * stripPoissonKernel σ T) T := by
          apply integral_congr_ae
          filter_upwards [] with T
          by_cases hT : T ∈ Icc (-1 : ℝ) 1
          · simp only [hT, indicator_of_mem]
            ring
          · simp only [hT, not_false_eq_true, indicator_of_notMem, mul_zero]
      _ = ∫ T in Icc (-1 : ℝ) 1,
        L * stripPoissonKernel σ T := by
        rw [integral_indicator measurableSet_Icc]
      _ = L * stripPoissonCoreMass σ := by
        rw [integral_const_mul]
        rfl
  have hpositive_integral :
      (∫ T : ℝ, stripPoissonKernel σ T * p (S - T)) =
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
    let f : ℝ → ℝ := fun T =>
      stripPoissonKernel σ T * p (S - T)
    calc
      (∫ T : ℝ, stripPoissonKernel σ T * p (S - T)) =
        ∫ T : ℝ, f T := by rfl
      _ = ∫ Y : ℝ, f (S - Y) :=
        (integral_sub_left_eq_self f volume S).symm
      _ = ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
        apply integral_congr_ae
        filter_upwards [] with Y
        try dsimp [f, p]
        congr 1
        ring_nf
  have hrepresentation :
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) =
        ∫ T : ℝ, stripPoissonKernel σ T * b (S - T) := by
    rw [lowerStripPoissonMajorant_scaled_convolution
      hℓ (c * Real.sqrt d) σ]
    have hscale : (((d : ℝ) / 2) * S / ((d : ℝ) / 2)) = S := by
      field_simp [hℓ.ne']
    rw [hscale]
    let f : ℝ → ℝ := fun T =>
      stripPoissonKernel σ T * b (S - T)
    calc
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaBoundaryLog ((d : ℝ) / 2)
            (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) =
        ∫ Y : ℝ, f (S - Y) := by
          apply integral_congr_ae
          filter_upwards [] with Y
          try dsimp [f, b, ℓ]
          congr 1
          ring_nf
      _ = ∫ T : ℝ, f T :=
        integral_sub_left_eq_self f volume S
      _ = ∫ T : ℝ, stripPoissonKernel σ T * b (S - T) := by
        rfl
  rw [hrepresentation]
  calc
    (∫ T : ℝ, stripPoissonKernel σ T * b (S - T)) ≤
      ∫ T : ℝ,
        (stripPoissonKernel σ T *
          (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => L) T +
          stripPoissonKernel σ T * p (S - T)) := by
        apply integral_mono_ae hb_integrable
          (hcore_integrable.add hp_integrable)
        exact Filter.Eventually.of_forall hpointwise
    _ = L * stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
      rw [integral_add hcore_integrable hp_integrable,
        hcore_integral, hpositive_integral]
    _ = (((d : ℝ) / 2) *
        Real.log ((8 * Real.pi * Real.exp 1 * c ^ 2) / S)) *
          stripPoissonCoreMass σ +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
      rfl

private theorem lowerStripPoissonMajorant_dimension_neg
    {d : ℕ} (hd : 0 < d) (R σ s : ℝ) :
    lowerStripPoissonMajorant ((d : ℝ) / 2) R σ (-s) =
      lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  let f : ℝ → ℝ := fun T =>
    stripPoissonKernel σ T *
      lowerGammaBoundaryLog ((d : ℝ) / 2) R
        (s - ((d : ℝ) / 2) * T)
  unfold lowerStripPoissonMajorant
  calc
    (∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (-s - ((d : ℝ) / 2) * T)) =
      ∫ T : ℝ, f (-T) := by
        apply integral_congr_ae
        filter_upwards
          [Measure.ae_ne (volume : Measure ℝ)
            (-s / ((d : ℝ) / 2))]
          with T hT
        have hy : s + ((d : ℝ) / 2) * T ≠ 0 := by
          intro hzero
          apply hT
          apply (eq_div_iff hℓ.ne').2
          linarith
        try dsimp [f]
        rw [stripPoissonKernel_neg]
        have harg :
            -s - ((d : ℝ) / 2) * T =
              -(s + ((d : ℝ) / 2) * T) := by
          ring
        rw [harg, lowerGammaBoundaryLog_dimension_neg R hy]
        congr 1
        ring_nf
    _ = ∫ T : ℝ, f T :=
      integral_neg_eq_self f volume
    _ = ∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (s - ((d : ℝ) / 2) * T) := by
      rfl

private theorem exists_lowerStripPoissonMajorant_positive_logarithmic_tail
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ S →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (S / A) := by
  have hbelow : -1 < σ := by linarith
  obtain ⟨C, hC, huniform⟩ :=
    exists_lowerGammaScaledPositivePart_uniform_bound hc
  let A : ℝ := 8 * Real.pi * Real.exp 1 * c ^ 2
  let m : ℝ := stripPoissonCoreMass σ
  let κ : ℝ := m / 2
  let a : ℝ := Real.pi / 2
  let β : ℝ := stripBottomMass σ * a * C
  have hA : 0 < A := by
    try dsimp [A]
    positivity
  have hm : 0 < m :=
    stripPoissonCoreMass_pos hbelow hσone
  have hκ : 0 < κ := by
    try dsimp [κ]
    positivity
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hβ : 0 < β := by
    try dsimp [β]
    exact mul_pos
      (mul_pos (stripBottomMass_pos hσone) ha) hC
  have hscale : Tendsto
      (fun S : ℝ => S * a) atTop atTop :=
    tendsto_id.atTop_mul_const ha
  have hnegative : Tendsto
      (fun S : ℝ => -(S * a)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hscale
  have hexponential : Tendsto
      (fun S : ℝ => Real.exp (-(S * a))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hdecay : Tendsto
      (fun S : ℝ => β * Real.exp (-a * (S - C)))
        atTop (𝓝 0) := by
    have hmul :=
      hexponential.const_mul (β * Real.exp (a * C))
    convert! hmul using 1
    · ext S
      calc
        β * Real.exp (-a * (S - C)) =
            β * Real.exp (a * C + -(S * a)) := by
              congr 1
              ring_nf
        _ = β * (Real.exp (a * C) *
              Real.exp (-(S * a))) := by
              rw [Real.exp_add]
        _ = β * Real.exp (a * C) *
              Real.exp (-(S * a)) := by
              ring
    · simp only [mul_zero]
  have hsmall : ∀ᶠ S : ℝ in atTop,
      β * Real.exp (-a * (S - C)) < m / 4 :=
    hdecay.eventually
      (Iio_mem_nhds (by positivity : 0 < m / 4))
  have hbounded : ∀ᶠ S : ℝ in atTop,
      max 2 (max C (2 * A)) ≤ S :=
    eventually_ge_atTop _
  obtain ⟨B₀, hB₀⟩ :=
    Filter.eventually_atTop.1 (hsmall.and hbounded)
  let B : ℝ := max 1 B₀
  have hB : 0 < B := by
    try dsimp [B]
    linarith [le_max_left (1 : ℝ) B₀]
  refine ⟨A, B, κ, hA, hB, hκ, ?_⟩
  intro d hd S hSB
  have hBzero : B₀ ≤ S :=
    le_trans (le_max_right 1 B₀) hSB
  obtain ⟨hsmallS, hlargeS⟩ := hB₀ S hBzero
  have hStwo : 2 ≤ S :=
    le_trans (le_max_left 2 _) hlargeS
  have hSC : C ≤ S :=
    le_trans (le_trans (le_max_left C (2 * A))
      (le_max_right 2 _)) hlargeS
  have hSratio : 2 * A ≤ S :=
    le_trans (le_trans (le_max_right C (2 * A))
      (le_max_right 2 _)) hlargeS
  have hSpos : 0 < S := by linarith
  obtain ⟨hsupport, hpositive⟩ := huniform d hd
  have htail := lowerStripPoissonMajorant_core_tail_split
    hd hc hσ hσone hStwo
  have hpositive_tail := lowerGammaScaledPositivePart_poisson_exponential_tail
    hd hc hσ hσone hC hsupport hpositive hSC
  have hpositive_bound :
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaScaledPositivePart d c Y) ≤
        (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
    calc
      (∫ Y : ℝ,
        stripPoissonKernel σ (S - Y) *
          lowerGammaScaledPositivePart d c Y) ≤
        (stripBottomMass σ * (Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * (S - C))) *
            (C * ((d : ℝ) / 2)) := hpositive_tail
      _ = (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
        try dsimp [β, a]
        ring
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hratio : (2 : ℝ) ≤ S / A :=
    (le_div_iff₀ hA).2 hSratio
  have hlogratio : (1 / 2 : ℝ) ≤ Real.log (S / A) :=
    hlogtwo.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio)
  have hflip : Real.log (A / S) = -Real.log (S / A) := by
    rw [Real.log_div hA.ne' hSpos.ne',
      Real.log_div hSpos.ne' hA.ne']
    ring
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  calc
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
      (((d : ℝ) / 2) * Real.log (A / S)) * m +
        ∫ Y : ℝ,
          stripPoissonKernel σ (S - Y) *
            lowerGammaScaledPositivePart d c Y := by
        exact htail
    _ ≤ (((d : ℝ) / 2) * Real.log (A / S)) * m +
        (β * Real.exp (-a * (S - C))) *
          ((d : ℝ) / 2) := by
      linarith [hpositive_bound]
    _ ≤ -κ * ((d : ℝ) / 2) * Real.log (S / A) := by
      rw [hflip]
      try dsimp [κ]
      linarith [mul_nonneg
        (show 0 ≤ (d : ℝ) / 2 by positivity)
        (show 0 ≤ m * Real.log (S / A) / 2 -
          β * Real.exp (-a * (S - C)) by
          linarith [mul_nonneg hm.le
            (show 0 ≤ Real.log (S / A) - 1 / 2 by linarith)])]

private theorem exists_lowerStripPoissonMajorant_logarithmic_tail
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ |S| →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (|S| / A) := by
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_positive_logarithmic_tail
      hc hσ hσone
  refine ⟨A, B, κ, hA, hB, hκ, ?_⟩
  intro d hd S hS
  by_cases hnonneg : 0 ≤ S
  · rw [abs_of_nonneg hnonneg] at hS ⊢
    exact htail d hd S hS
  · have hnegative : S < 0 := lt_of_not_ge hnonneg
    have habs : |S| = -S := abs_of_neg hnegative
    have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hnegS : B ≤ -S := by simpa only [habs] using! hS
    have htailneg := htail d hd (-S) hnegS
    have harg :
        ((d : ℝ) / 2) * S =
          -(((d : ℝ) / 2) * (-S)) := by
      ring
    calc
      lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) =
        lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ
            (-(((d : ℝ) / 2) * (-S))) := by
          rw [harg]
      _ = lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ
            (((d : ℝ) / 2) * (-S)) :=
          lowerStripPoissonMajorant_dimension_neg
            hdpos (c * Real.sqrt d) σ
              (((d : ℝ) / 2) * (-S))
      _ ≤ -κ * ((d : ℝ) / 2) *
          Real.log ((-S) / A) := htailneg
      _ = -κ * ((d : ℝ) / 2) *
          Real.log (|S| / A) := by
          rw [habs]

private theorem inverseQuadraticAbs_integrable :
    Integrable (fun S : ℝ => 1 / (1 + |S|) ^ 2) := by
  have hbase := integrable_one_add_norm
    (E := ℝ) (μ := volume) (r := (2 : ℝ))
      (by norm_num)
  convert! hbase using 1
  ext S
  rw [Real.norm_eq_abs,
    Real.rpow_neg (by positivity)]
  simp only [one_div, Real.rpow_ofNat]

private theorem exists_lowerStripPoissonMajorant_integrable_majorant
    {c : ℝ} (hc : 0 < c) (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ S : ℝ,
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2)
              (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
            C * Real.exp (-γ * ((d : ℝ) / 2)) /
              (1 + |S|) ^ 2 := by
  obtain ⟨σ, γ₀, hσpos, hσone, hγ₀, hcentral⟩ :=
    exists_lowerStripPoissonMajorant_uniform_negative hc hsharp
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_logarithmic_tail
      hc hσpos.le hσone
  let T : ℝ := max B (max A 1)
  let C : ℝ := max ((1 + T) ^ 2) (4 * A ^ 2)
  let γ : ℝ := γ₀ / 2
  have hT : 1 ≤ T := by
    try dsimp [T]
    exact le_trans (le_max_right A 1)
      (le_max_right B (max A 1))
  have hTA : A ≤ T := by
    try dsimp [T]
    exact le_trans (le_max_left A 1)
      (le_max_right B (max A 1))
  have hTB : B ≤ T := by
    try dsimp [T]
    exact le_max_left B (max A 1)
  have hC : 0 < C := by
    try dsimp [C]
    have hsq : 0 < (1 + T) ^ 2 := sq_pos_of_pos (by linarith)
    exact lt_of_lt_of_le hsq (le_max_left _ _)
  have hγ : 0 < γ := by
    try dsimp [γ]
    positivity
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hdimension : ∀ᶠ d : ℕ in atTop,
      4 / κ ≤ (d : ℝ) / 2 :=
    hscale.eventually (Ici_mem_atTop (4 / κ))
  refine ⟨σ, γ, C, hσpos, hσone, hγ, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hdimension, hcentral] with d hd hdim hcen
  intro S
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  by_cases hfar : T ≤ |S|
  · have hBS : B ≤ |S| := le_trans hTB hfar
    have hAS : A ≤ |S| := le_trans hTA hfar
    have habspos : 0 < |S| := lt_of_lt_of_le hA hAS
    have hratio : (1 : ℝ) ≤ |S| / A :=
      (le_div_iff₀ hA).2 (by simpa only [one_mul] using! hAS)
    have hlog : 0 ≤ Real.log (|S| / A) :=
      Real.log_nonneg hratio
    have hκscale : 4 ≤ κ * ((d : ℝ) / 2) := by
      have h := (div_le_iff₀ hκ).1 hdim
      linarith
    have hnegative := hcen (((d : ℝ) / 2) * S)
    have hfrequency := htail d hd S hBS
    have haverage :
        lowerStripPoissonMajorant ((d : ℝ) / 2)
          (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
            -γ * ((d : ℝ) / 2) -
              2 * Real.log (|S| / A) := by
      try dsimp [γ]
      linarith [mul_nonneg
        (sub_nonneg.mpr hκscale) hlog]
    have hpow :
        Real.exp (-(2 : ℝ) * Real.log (|S| / A)) =
          (A / |S|) ^ 2 := by
      calc
        Real.exp (-(2 : ℝ) * Real.log (|S| / A)) =
            Real.exp
              (-Real.log (|S| / A) +
                -Real.log (|S| / A)) := by
              congr 1
              ring
        _ = Real.exp (-Real.log (|S| / A)) *
              Real.exp (-Real.log (|S| / A)) := by
              rw [Real.exp_add]
        _ = (A / |S|) ^ 2 := by
              rw [Real.exp_neg, Real.exp_log
                (div_pos habspos hA)]
              field_simp [habspos.ne', hA.ne']
    have hu : 1 ≤ |S| := le_trans hT hfar
    have hquad :
        (1 + |S|) ^ 2 ≤ 4 * |S| ^ 2 := by
      linarith [sq_nonneg (|S| - 1)]
    have hquadmajor :
        (A / |S|) ^ 2 * (1 + |S|) ^ 2 ≤
          4 * A ^ 2 := by
      calc
        (A / |S|) ^ 2 * (1 + |S|) ^ 2 ≤
            (A / |S|) ^ 2 * (4 * |S| ^ 2) :=
              mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
        _ = 4 * A ^ 2 := by
              field_simp [habspos.ne']
    have hden : 0 < (1 + |S|) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hprofile :
        (A / |S|) ^ 2 ≤ C / (1 + |S|) ^ 2 := by
      apply (le_div_iff₀ hden).2
      exact hquadmajor.trans
        (show 4 * A ^ 2 ≤ C from le_max_right _ _)
    calc
      Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
        Real.exp
          (-γ * ((d : ℝ) / 2) -
            2 * Real.log (|S| / A)) :=
          Real.exp_le_exp.mpr haverage
      _ = Real.exp (-γ * ((d : ℝ) / 2)) *
          (A / |S|) ^ 2 := by
        rw [show -γ * ((d : ℝ) / 2) -
          2 * Real.log (|S| / A) =
            -γ * ((d : ℝ) / 2) +
              (-(2 : ℝ) * Real.log (|S| / A)) by ring,
            Real.exp_add, hpow]
      _ ≤ Real.exp (-γ * ((d : ℝ) / 2)) *
          (C / (1 + |S|) ^ 2) :=
        mul_le_mul_of_nonneg_left hprofile
          (Real.exp_pos _).le
      _ = C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2 := by
        ring
  · have hnear : |S| ≤ T := le_of_lt (lt_of_not_ge hfar)
    have hden : 0 < (1 + |S|) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hnearquad : (1 + |S|) ^ 2 ≤ (1 + T) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hdenmajor : (1 + |S|) ^ 2 ≤ C :=
      hnearquad.trans (le_max_left _ _)
    have hexpcentral :
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
          Real.exp (-γ * ((d : ℝ) / 2)) := by
      apply Real.exp_le_exp.mpr
      have h := hcen (((d : ℝ) / 2) * S)
      try dsimp [γ]
      linarith [mul_nonneg hγ₀.le hℓ.le]
    calc
      Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
        Real.exp (-γ * ((d : ℝ) / 2)) := hexpcentral
      _ ≤ C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2 := by
        apply (le_div_iff₀ hden).2
        calc
          Real.exp (-γ * ((d : ℝ) / 2)) *
              (1 + |S|) ^ 2 ≤
            Real.exp (-γ * ((d : ℝ) / 2)) * C :=
              mul_le_mul_of_nonneg_left hdenmajor
                (Real.exp_pos _).le
          _ = C * Real.exp (-γ * ((d : ℝ) / 2)) := by
            ring

private noncomputable def lowerInverseQuadraticMass : ℝ :=
  ∫ S : ℝ, 1 / (1 + |S|) ^ 2

private theorem antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
    {d : ℕ} (hd : 0 < d) {R σ γ C : ℝ}
    (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s))
    (hmajor : ∀ S : ℝ,
      Real.exp
        (lowerStripPoissonMajorant ((d : ℝ) / 2)
          R σ (((d : ℝ) / 2) * S)) ≤
        C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2) :
    (∫ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) ≤
      (C * lowerInverseQuadraticMass) *
        ((d : ℝ) / 2) * Real.exp (-γ * ((d : ℝ) / 2)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  let Z : ℝ → ℂ := fun s =>
    normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I * (((σ * ℓ : ℝ) : ℂ)))
  have ha : (1 - σ) * ℓ < (d : ℝ) := by
    have hplus : 0 < (1 + σ) * ℓ :=
      mul_pos (by linarith) hℓ
    have hinner : 0 < (1 - σ) * ℓ :=
      mul_pos (sub_pos.mpr hσabove) hℓ
    apply (mul_lt_mul_iff_right₀ hinner).mp
    try dsimp [ℓ] at hplus hinner ⊢
    linarith [mul_pos hplus hinner]
  have hheight : ℓ - (1 - σ) * ℓ = σ * ℓ := by
    ring
  have hZ : Integrable Z := by
    have h :=
      antiFourierWitness_normalizedMellinStrip_shifted_integrable
        hd hR w ha
    convert! h using 1
    ext s
    try dsimp [Z, ℓ] at *
    congr 2
    push_cast
    ring
  let E : ℝ := C * Real.exp (-γ * ℓ)
  have hprofile : Integrable
      (fun S : ℝ => E / (1 + |S|) ^ 2) := by
    have h := inverseQuadraticAbs_integrable.const_mul E
    convert! h using 1
    ext S
    ring
  have hscaled : Integrable (fun S : ℝ => ‖Z (ℓ * S)‖) := by
    have h := hZ.norm.comp_mul_left' hℓ.ne'
    convert! h using 1
  have hbound :
      (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
        E * lowerInverseQuadraticMass := by
    calc
      (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
          ∫ S : ℝ, E / (1 + |S|) ^ 2 := by
        apply integral_mono_ae hscaled hprofile
        filter_upwards [] with S
        calc
          ‖Z (ℓ * S)‖ ≤
            Real.exp
              (lowerStripPoissonMajorant ℓ R σ (ℓ * S)) := by
                exact hpoint (ℓ * S)
          _ ≤ E / (1 + |S|) ^ 2 := by
                exact hmajor S
      _ = E * lowerInverseQuadraticMass := by
        unfold lowerInverseQuadraticMass
        calc
          (∫ S : ℝ, E / (1 + |S|) ^ 2) =
              ∫ S : ℝ, E * (1 / (1 + |S|) ^ 2) := by
                apply integral_congr_ae
                filter_upwards [] with S
                ring
          _ = E * (∫ S : ℝ, 1 / (1 + |S|) ^ 2) := by
                rw [integral_const_mul]
  have hchange :
      (∫ s : ℝ, ‖Z s‖) =
        ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) := by
    have h := Measure.integral_comp_mul_left
      (fun s : ℝ => ‖Z s‖) ℓ
    rw [abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul] at h
    calc
      (∫ s : ℝ, ‖Z s‖) =
          ℓ * (ℓ⁻¹ * (∫ s : ℝ, ‖Z s‖)) := by
            field_simp [hℓ.ne']
      _ = ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) := by
            rw [← h]
  change (∫ s : ℝ, ‖Z s‖) ≤
    (C * lowerInverseQuadraticMass) * ℓ *
      Real.exp (-γ * ℓ)
  rw [hchange]
  calc
    ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
      ℓ * (E * lowerInverseQuadraticMass) :=
        mul_le_mul_of_nonneg_left hbound hℓ.le
    _ = (C * lowerInverseQuadraticMass) * ℓ *
        Real.exp (-γ * ℓ) := by
      try dsimp [E]
      ring

private theorem lowerStripCappedPoisson_tendsto
    {d : ℕ} (hd : 0 < d) {c σ : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              (c * Real.sqrt d) (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ s)) := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ s]
  have h := lowerGammaScaledCapped_poisson_tendsto
    (c := c) hd hσbelow hσabove
      (s / ((d : ℝ) / 2))
  convert! h using 1
  ext n
  let f : ℝ → ℝ := fun Y =>
    stripPoissonKernel σ (s / ((d : ℝ) / 2) - Y) *
      lowerGammaBoundaryCapped ((d : ℝ) / 2)
        (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)
  calc
    (∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
            (s - ((d : ℝ) / 2) * T)) =
        ∫ T : ℝ, f (s / ((d : ℝ) / 2) - T) := by
          apply integral_congr_ae
          filter_upwards [] with T
          try dsimp [f]
          have hkernel :
              s / ((d : ℝ) / 2) -
                (s / ((d : ℝ) / 2) - T) = T := by
            ring
          have harg :
              ((d : ℝ) / 2) *
                (s / ((d : ℝ) / 2) - T) =
                  s - ((d : ℝ) / 2) * T := by
            field_simp [hℓ.ne']
          rw [hkernel, harg]
    _ = ∫ Y : ℝ, f Y :=
      integral_sub_left_eq_self f volume
        (s / ((d : ℝ) / 2))
    _ = ∫ Y : ℝ,
      stripPoissonKernel σ
        (s / ((d : ℝ) / 2) - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) (n : ℝ)
              (((d : ℝ) / 2) * Y) := by
      rfl

private theorem uniformAntiFourierSignRadius_of_poisson_majorization
    (hpoisson :
      ∀ {d : ℕ} (hd : 0 < d) {R : ℝ} (_hR : 0 < R)
        (w : AntiFourierWitness d R)
        {σ : ℝ} (_hσbelow : -1 < σ) (_hσabove : σ < 1)
        (s : ℝ),
        ‖normalizedRadialMellinStrip hd w.function R
          ((s : ℂ) + Complex.I *
            (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s)) :
    UniformAntiFourierSignRadius := by
  intro c hc hcritical
  have hsharp : c < Real.pi⁻¹ := hcritical
  obtain ⟨σ, γ, C, hσpos, hσone, hγ, hC, hmajor⟩ :=
    exists_lowerStripPoissonMajorant_integrable_majorant hc hsharp
  let J : ℝ := lowerInverseQuadraticMass
  let Q : ℝ := C * J
  let K : ℝ := (2 * Real.pi)⁻¹ * Q / (1 - σ)
  have hσbelow : -1 < σ := by linarith
  have hsigmapos : 0 < 1 - σ := sub_pos.mpr hσone
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hγscale : Tendsto
      (fun d : ℕ => γ * ((d : ℝ) / 2)) atTop atTop := by
    have h := hscale.atTop_mul_const hγ
    convert! h using 1
    ext d
    ring
  have hnegative : Tendsto
      (fun d : ℕ => -(γ * ((d : ℝ) / 2))) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hγscale
  have hexp : Tendsto
      (fun d : ℕ => Real.exp (-(γ * ((d : ℝ) / 2))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hlimit : Tendsto
      (fun d : ℕ => K *
        Real.exp (-γ * ((d : ℝ) / 2))) atTop (𝓝 0) := by
    have h := hexp.const_mul K
    convert! h using 1
    · ext d
      congr 1
      ring_nf
    · simp only [mul_zero]
  have hsmall : ∀ᶠ d : ℕ in atTop,
      K * Real.exp (-γ * ((d : ℝ) / 2)) < (1 / 2 : ℝ) :=
    hlimit.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hmajor, hsmall] with d hd hmaj hsmall_d
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hR : 0 < c * Real.sqrt (d : ℝ) :=
    mul_pos hc (Real.sqrt_pos.mpr hdreal)
  refine ⟨?_⟩
  intro w
  have hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hdpos w.function
        (c * Real.sqrt (d : ℝ))
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt (d : ℝ)) σ s) := by
    intro s
    exact hpoisson hdpos hR w hσbelow hσone s
  have hL1 :=
    antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
      hdpos hR hσbelow hσone w hpoint hmaj
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hden : 0 < (1 - σ) * ((d : ℝ) / 2) :=
    mul_pos hsigmapos hℓ
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hbound :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hdpos w.function
            (c * Real.sqrt (d : ℝ))
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) ≤
        K * Real.exp (-γ * ((d : ℝ) / 2)) := by
    calc
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hdpos w.function
            (c * Real.sqrt (d : ℝ))
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) ≤
        ((2 * Real.pi)⁻¹ *
          ((C * lowerInverseQuadraticMass) *
            ((d : ℝ) / 2) *
              Real.exp (-γ * ((d : ℝ) / 2)))) /
          ((1 - σ) * ((d : ℝ) / 2)) := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact mul_le_mul_of_nonneg_left hL1 hpi
      _ = K * Real.exp (-γ * ((d : ℝ) / 2)) := by
        try dsimp [K, Q, J]
        field_simp [hsigmapos.ne', hℓ.ne']
  exact no_antiFourierWitness_of_interiorMellinL1_lt_half
    hdpos hR hσbelow hσone w
      (lt_of_le_of_lt hbound hsmall_d)

private theorem lowerStripCappedPoisson_tendsto_radius
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              R (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        R σ s)) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr hdreal
  let c : ℝ := R / Real.sqrt (d : ℝ)
  have hrad : c * Real.sqrt (d : ℝ) = R := by
    try dsimp [c]
    exact div_mul_cancel₀ R hsqrt.ne'
  have h := lowerStripCappedPoisson_tendsto
    (c := c) hd hσbelow hσabove s
  simpa only [hrad] using! h

private theorem antiFourierWitness_norm_le_poisson_of_eventually_capped_radius
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (w : AntiFourierWitness d R)
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ)
    (hcapped : ∀ᶠ n : ℕ in atTop,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (∫ T : ℝ,
            stripPoissonKernel σ T *
              lowerGammaBoundaryCapped ((d : ℝ) / 2)
                R (n : ℝ)
                  (s - ((d : ℝ) / 2) * T))) :
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            R σ s) := by
  have hlimit := lowerStripCappedPoisson_tendsto_radius
    (R := R) hd hσbelow hσabove s
  have hexp :=
    Real.continuous_exp.continuousAt.tendsto.comp hlimit
  exact le_of_tendsto_of_tendsto
    tendsto_const_nhds hexp hcapped

private theorem uniformAntiFourierSignRadius_of_capped_poisson_majorization
    (hcap :
      ∀ {d : ℕ} (hd : 0 < d) {R : ℝ} (_hR : 0 < R)
        (w : AntiFourierWitness d R),
        ∃ D₀ : ℝ,
          ∀ D : ℝ, D₀ ≤ D →
            ∀ {σ : ℝ}, -1 < σ → σ < 1 →
              ∀ s : ℝ,
                ‖normalizedRadialMellinStrip hd w.function R
                  ((s : ℂ) + Complex.I *
                    (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
                  Real.exp
                    (∫ T : ℝ,
                      stripPoissonKernel σ T *
                        lowerGammaBoundaryCapped
                          ((d : ℝ) / 2) R D
                          (s - ((d : ℝ) / 2) * T))) :
    UniformAntiFourierSignRadius := by
  apply uniformAntiFourierSignRadius_of_poisson_majorization
  intro d hd R hR w σ hσbelow hσabove s
  obtain ⟨D₀, hD⟩ := hcap hd hR w
  apply antiFourierWitness_norm_le_poisson_of_eventually_capped_radius
    hd w hσbelow hσabove s
  have hevent : ∀ᶠ n : ℕ in atTop, D₀ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Ici_mem_atTop D₀)
  filter_upwards [hevent] with n hn
  exact hD (n : ℝ) hn hσbelow hσabove s

end

section

open Filter MeasureTheory Set
open scoped ENNReal Interval Topology

private theorem uniformAntiFourierSignRadius :
    UniformAntiFourierSignRadius := by
  apply uniformAntiFourierSignRadius_of_capped_poisson_majorization
  intro d hd R hR w
  exact exists_antiFourierWitness_capped_poisson_majorization
    hd hR w

end

section

open Set

private noncomputable def quotientRootMap (d : ℕ) (x : ℝ) : ℝ :=
  x ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private theorem continuous_quotientRootMap (d : ℕ) :
    Continuous (quotientRootMap d) := by
  unfold quotientRootMap
  exact (Real.continuous_rpow_const (by positivity)).div_const _

private theorem monotoneOn_quotientRootMap (d : ℕ) :
    MonotoneOn (quotientRootMap d) (quotientSet d) := by
  intro x hx y _ hxy
  rcases hx with ⟨f, rfl⟩
  unfold quotientRootMap
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (quotient_pos f).le hxy (by positivity))
    (Real.sqrt_nonneg _)

private theorem normalizedCostRange_eq_quotientRootImage (d : ℕ) :
    Set.range (normalizedCost (d := d)) =
      quotientRootMap d '' quotientSet d := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotient f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩

private theorem normalizedProgram_eq_quotientInf_root
    (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    normalizedProgram d =
      quotientRootMap d (sInf (quotientSet d)) := by
  obtain ⟨f⟩ := hadmissible
  have hnonempty : (quotientSet d).Nonempty :=
    ⟨quotient f, ⟨f, rfl⟩⟩
  unfold normalizedProgram
  rw [normalizedCostRange_eq_quotientRootImage]
  exact
    (MonotoneOn.map_csInf_of_continuousWithinAt
      (continuous_quotientRootMap d).continuousWithinAt
      (monotoneOn_quotientRootMap d) hnonempty
      (quotientSet_bddBelow d)).symm

private theorem quotientInf_nonneg
    (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    0 ≤ sInf (quotientSet d) := by
  obtain ⟨f⟩ := hadmissible
  refine le_csInf ⟨quotient f, f, rfl⟩ ?_
  rintro _ ⟨g, rfl⟩
  exact (quotient_pos g).le

private noncomputable def packingGeometricRoot (d : ℕ) : ℝ :=
  (unitBallVolume d / (2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) *
    Real.sqrt (d : ℝ)

private theorem linearProgram_root_eq_geometric_mul_normalizedProgram
    {d : ℕ} (hd : 0 < d) (hadmissible : Nonempty (Admissible d)) :
    (linearProgram d) ^ ((d : ℝ)⁻¹) =
      packingGeometricRoot d * normalizedProgram d := by
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  rw [normalizedProgram_eq_quotientInf_root d hadmissible]
  unfold linearProgram packingGeometricRoot quotientRootMap
  rw [Real.mul_rpow (geometricFactor_pos d).le
    (quotientInf_nonneg d hadmissible)]
  field_simp

end

section

open Filter
open scoped Nat Topology

private theorem unitBallVolume_odd (k : ℕ) :
    unitBallVolume (2 * k + 1) =
      Real.pi ^ k * 2 ^ (k + 1) / ((2 * k + 1)‼ : ℝ) := by
  have hhalf :
      ((↑(2 * k + 1) : ℝ) / 2) = (k : ℝ) + 1 / 2 := by
    push_cast
    ring
  have hgamma :
      Real.Gamma (((↑(2 * k + 1) : ℝ) / 2) + 1) =
        ((2 * k + 1)‼ : ℝ) * Real.sqrt Real.pi /
          (2 : ℝ) ^ (k + 1) := by
    rw [hhalf]
    convert! Real.Gamma_nat_add_one_add_half k using 1; ring_nf
  have hpi :
      Real.pi ^ (((2 * k + 1 : ℕ) : ℝ) / 2) =
        Real.pi ^ k * Real.sqrt Real.pi := by
    rw [hhalf, Real.rpow_add Real.pi_pos,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hdouble : (0 : ℝ) < ((2 * k + 1)‼ : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * k + 1)
  unfold unitBallVolume
  rw [hpi, hgamma]
  field_simp

private theorem oddDoubleFactorial_mul_two_pow_factorial (k : ℕ) :
    ((2 * k + 1)‼ : ℝ) * (2 : ℝ) ^ k * (k.factorial : ℝ) =
      ((2 * k + 1).factorial : ℝ) := by
  exact_mod_cast
    (by
      rw [mul_assoc, ← Nat.doubleFactorial_two_mul,
        ← Nat.factorial_eq_mul_doubleFactorial]
      : (2 * k + 1)‼ * 2 ^ k * k.factorial =
          (2 * k + 1).factorial)

private theorem unitBallVolume_odd_factorial (k : ℕ) :
    unitBallVolume (2 * k + 1) =
      Real.pi ^ k * (2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) /
        ((2 * k + 1).factorial : ℝ) := by
  rw [unitBallVolume_odd]
  have hdouble : ((2 * k + 1)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos (2 * k + 1)))
  have hfactorial : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (2 * k + 1)))
  have hidentity := oddDoubleFactorial_mul_two_pow_factorial k
  have hpower :
      (2 : ℝ) ^ (2 * k + 1) =
        (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpower]
  field_simp
  linarith [hidentity]

private theorem tendsto_factorialStirlingSequence :
    Tendsto Stirling.stirlingSeq atTop
      (nhds (Real.sqrt Real.pi)) :=
  Stirling.tendsto_stirlingSeq_sqrt_pi

private theorem tendsto_log_factorialStirlingSequence :
    Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k))
      atTop (nhds (Real.log (Real.sqrt Real.pi))) := by
  exact (Real.continuousAt_log (by positivity)).tendsto.comp
    tendsto_factorialStirlingSequence

private theorem tendsto_log_nat_div_nat :
    Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (nhds 0) := by
  simpa only [pow_one, one_mul, add_zero] using!
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem tendsto_log_factorialStirlingSequence_div_nat :
    Tendsto
      (fun k : ℕ => Real.log (Stirling.stirlingSeq k) / (k : ℝ))
      atTop (nhds 0) := by
  convert! tendsto_log_factorialStirlingSequence.mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1;
    simp only [mul_zero]

private theorem tendsto_log_two_mul_nat_div_nat :
    Tendsto (fun k : ℕ =>
      Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ))
      atTop (nhds 0) := by
  have hsum :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log (2 : ℝ))).add
      tendsto_log_nat_div_nat
  have hsum' :
      Tendsto
        (fun k : ℕ =>
          Real.log (2 : ℝ) / (k : ℝ) +
            Real.log (k : ℝ) / (k : ℝ))
        atTop (nhds 0) := by
    simpa only [add_zero] using! hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  rw [← add_div, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by exact_mod_cast (Nat.ne_of_gt hk))]

private theorem tendsto_log_factorial_div_nat_sub_log_nat :
    Tendsto
      (fun k : ℕ =>
        Real.log (k.factorial : ℝ) / (k : ℝ) - Real.log (k : ℝ))
      atTop (nhds (-1)) := by
  have hlimit :=
    (tendsto_log_factorialStirlingSequence_div_nat.add
      (tendsto_log_two_mul_nat_div_nat.const_mul (1 / 2 : ℝ))).sub
        (tendsto_const_nhds (x := (1 : ℝ)))
  have htarget :
      Tendsto
        (fun k : ℕ =>
          Real.log (Stirling.stirlingSeq k) / (k : ℝ) +
            (1 / 2 : ℝ) *
              (Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ)) - 1)
        atTop (nhds (-1)) := by
    convert! hlimit using 1; norm_num
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hformula := Stirling.log_stirlingSeq_formula k
  rw [Real.log_div hkreal (Real.exp_ne_zero 1), Real.log_exp]
    at hformula
  have hcomm :
      Real.log ((k : ℝ) * 2) = Real.log (2 * (k : ℝ)) := by
    rw [mul_comm]
  field_simp
  linarith [hformula, hcomm]

private theorem tendsto_oddDimension_atTop :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  exact tendsto_atTop_mono
    (fun k => by change k ≤ 2 * k + 1; omega) tendsto_id

private theorem tendsto_log_nat_div_oddDimension :
    Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (2 * (k : ℝ) + 1))
      atTop (nhds 0) := by
  have hproduct := tendsto_log_nat_div_nat.mul
    Stirling.tendsto_self_div_two_mul_self_add_one
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (Real.log (k : ℝ) / (k : ℝ)) *
            ((k : ℝ) / (2 * (k : ℝ) + 1)))
        atTop (nhds 0) := by
    convert! hproduct using 1; norm_num
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

private theorem tendsto_log_nat_sub_log_oddDimension :
    Tendsto
      (fun k : ℕ =>
        Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1))
      atTop (nhds (Real.log (1 / 2 : ℝ))) := by
  have hratio :=
    Stirling.tendsto_self_div_two_mul_self_add_one.log
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hodd : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  exact Real.log_div hkreal hodd

private noncomputable def normalizedVolumeLog (d : ℕ) : ℝ :=
  Real.log (unitBallVolume d) / (d : ℝ) +
    Real.log (d : ℝ) / 2

private theorem normalizedVolumeLog_odd_eq (k : ℕ) (hk : 0 < k) :
    normalizedVolumeLog (2 * k + 1) =
      (k : ℝ) / (2 * (k : ℝ) + 1) * Real.log Real.pi +
      Real.log 2 +
      ((k : ℝ) / (2 * (k : ℝ) + 1)) *
        (Real.log (k.factorial : ℝ) / (k : ℝ) -
          Real.log (k : ℝ)) -
      (Real.log ((2 * k + 1).factorial : ℝ) /
          (2 * (k : ℝ) + 1) -
        Real.log (2 * (k : ℝ) + 1)) +
      ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
        Real.log (k : ℝ) +
      (1 / 2 : ℝ) *
        (Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1)) := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hodd : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hkfactorial : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos k))
  have hoddfactorial : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (2 * k + 1)))
  have hpipow : Real.pi ^ k ≠ (0 : ℝ) :=
    pow_ne_zero k Real.pi_ne_zero
  have htwopow : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
  unfold normalizedVolumeLog
  rw [unitBallVolume_odd_factorial,
    Real.log_div
      (mul_ne_zero (mul_ne_zero hpipow htwopow) hkfactorial)
      hoddfactorial,
    Real.log_mul (mul_ne_zero hpipow htwopow) hkfactorial,
    Real.log_mul hpipow htwopow,
    Real.log_pow, Real.log_pow]
  push_cast
  field_simp
  ring

private theorem tendsto_normalizedVolumeLog_even :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hcore :=
    (tendsto_const_nhds
      (x := Real.log (2 * Real.pi) / 2)).sub
      (tendsto_log_factorial_div_nat_sub_log_nat.const_mul
        (1 / 2 : ℝ))
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          Real.log (2 * Real.pi) / 2 -
            (1 / 2 : ℝ) *
              (Real.log (k.factorial : ℝ) / (k : ℝ) -
                Real.log (k : ℝ)))
        atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
    convert! hcore using 1; norm_num; ring
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hkfactorial : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos k))
  have hpipow : Real.pi ^ k ≠ (0 : ℝ) :=
    pow_ne_zero k Real.pi_ne_zero
  unfold normalizedVolumeLog
  rw [unitBallVolume_even,
    Real.log_div hpipow hkfactorial,
    Real.log_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  push_cast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkreal]
  field_simp
  ring

private theorem tendsto_odd_halfDimension_log_correction :
    Tendsto
      (fun k : ℕ =>
        ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
          Real.log (k : ℝ))
      atTop (nhds 0) := by
  have hscaled :=
    tendsto_log_nat_div_oddDimension.const_mul (-1 / 2 : ℝ)
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (-1 / 2 : ℝ) *
            (Real.log (k : ℝ) / (2 * (k : ℝ) + 1)))
        atTop (nhds 0) := by
    convert! hscaled using 1; norm_num
  refine hlimit.congr' (Filter.Eventually.of_forall ?_)
  intro k
  have hodd : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem tendsto_log_oddFactorial_div_oddDimension_sub_log :
    Tendsto
      (fun k : ℕ =>
        Real.log ((2 * k + 1).factorial : ℝ) /
            (2 * (k : ℝ) + 1) -
          Real.log (2 * (k : ℝ) + 1))
      atTop (nhds (-1)) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using!
    tendsto_log_factorial_div_nat_sub_log_nat.comp
      tendsto_oddDimension_atTop

private theorem tendsto_normalizedVolumeLog_odd :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k + 1))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hq := Stirling.tendsto_self_div_two_mul_self_add_one
  have hparts :=
    (((((hq.mul_const (Real.log Real.pi)).add
      (tendsto_const_nhds (x := Real.log (2 : ℝ)))).add
      (hq.mul tendsto_log_factorial_div_nat_sub_log_nat)).sub
      tendsto_log_oddFactorial_div_oddDimension_sub_log).add
      tendsto_odd_halfDimension_log_correction).add
      (tendsto_log_nat_sub_log_oddDimension.const_mul (1 / 2 : ℝ))
  have hconstant :
      (1 / 2 : ℝ) * Real.log Real.pi + Real.log 2 +
        (1 / 2 : ℝ) * (-1) - (-1) + 0 +
        (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) =
          (Real.log (2 * Real.pi) + 1) / 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    norm_num
    ring
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (k : ℝ) / (2 * (k : ℝ) + 1) * Real.log Real.pi +
          Real.log 2 +
          ((k : ℝ) / (2 * (k : ℝ) + 1)) *
            (Real.log (k.factorial : ℝ) / (k : ℝ) -
              Real.log (k : ℝ)) -
          (Real.log ((2 * k + 1).factorial : ℝ) /
              (2 * (k : ℝ) + 1) -
            Real.log (2 * (k : ℝ) + 1)) +
          ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
            Real.log (k : ℝ) +
          (1 / 2 : ℝ) *
            (Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1)))
        atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
    simpa only [hconstant] using! hparts
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  exact (normalizedVolumeLog_odd_eq k hk).symm

/-- A sequence converges when its even and odd subsequences have the same limit. -/
public
theorem tendsto_of_even_and_odd {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X}
    (heven : Tendsto (fun k : ℕ => f (2 * k)) atTop (nhds x))
    (hodd : Tendsto (fun k : ℕ => f (2 * k + 1)) atTop (nhds x)) :
    Tendsto f atTop (nhds x) := by
  refine Filter.tendsto_iff_forall_eventually_mem.2 ?_
  intro s hs
  obtain ⟨Ne, hNe⟩ :=
    Filter.eventually_atTop.1 (heven.eventually hs)
  obtain ⟨No, hNo⟩ :=
    Filter.eventually_atTop.1 (hodd.eventually hs)
  refine Filter.eventually_atTop.2
    ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    apply hNe
    omega
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    apply hNo
    omega

private theorem tendsto_normalizedVolumeLog :
    Tendsto normalizedVolumeLog atTop
      (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  exact tendsto_of_even_and_odd tendsto_normalizedVolumeLog_even
    tendsto_normalizedVolumeLog_odd

private noncomputable def normalizedVolumeRoot (d : ℕ) : ℝ :=
  unitBallVolume d ^ ((d : ℝ)⁻¹) * Real.sqrt (d : ℝ)

private theorem normalizedVolumeRoot_pos {d : ℕ} (hd : 0 < d) :
    0 < normalizedVolumeRoot d := by
  unfold normalizedVolumeRoot
  exact mul_pos (Real.rpow_pos_of_pos (unitBallVolume_pos d) _)
    (Real.sqrt_pos.2 (by exact_mod_cast hd))

private theorem log_normalizedVolumeRoot {d : ℕ} (hd : 0 < d) :
    Real.log (normalizedVolumeRoot d) = normalizedVolumeLog d := by
  unfold normalizedVolumeRoot normalizedVolumeLog
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (unitBallVolume_pos d) _).ne'
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne',
    Real.log_rpow (unitBallVolume_pos d),
    Real.log_sqrt (by exact_mod_cast (Nat.zero_le d))]
  ring

private theorem exp_normalizedVolumeLog_limit :
    Real.exp ((Real.log (2 * Real.pi) + 1) / 2) =
      Real.sqrt (2 * Real.pi * Real.exp 1) := by
  have hbase : 0 < (2 : ℝ) * Real.pi := by positivity
  have htarget : 0 ≤ (2 : ℝ) * Real.pi * Real.exp 1 := by positivity
  have hsq :
      (Real.exp ((Real.log (2 * Real.pi) + 1) / 2)) ^ 2 =
        2 * Real.pi * Real.exp 1 := by
    calc
      (Real.exp ((Real.log (2 * Real.pi) + 1) / 2)) ^ 2 =
          Real.exp
            (((Real.log (2 * Real.pi) + 1) / 2) +
              ((Real.log (2 * Real.pi) + 1) / 2)) := by
            rw [Real.exp_add]
            ring
      _ = Real.exp (Real.log (2 * Real.pi) + 1) := by
            congr 1
            ring
      _ = 2 * Real.pi * Real.exp 1 := by
            rw [Real.exp_add, Real.exp_log hbase]
  have hroot := Real.sq_sqrt htarget
  nlinarith [Real.exp_pos ((Real.log (2 * Real.pi) + 1) / 2),
    Real.sqrt_nonneg (2 * Real.pi * Real.exp 1)]

private theorem tendsto_normalizedVolumeRoot :
    Tendsto normalizedVolumeRoot atTop
      (nhds (Real.sqrt (2 * Real.pi * Real.exp 1))) := by
  have hexp :
      Tendsto (fun d : ℕ => Real.exp (normalizedVolumeLog d)) atTop
        (nhds (Real.exp ((Real.log (2 * Real.pi) + 1) / 2))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      tendsto_normalizedVolumeLog
  rw [exp_normalizedVolumeLog_limit] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  rw [← log_normalizedVolumeRoot hd,
    Real.exp_log (normalizedVolumeRoot_pos hd)]

private theorem rpow_two_pow_inv_dimension {d : ℕ} (hd : 0 < d) :
    ((2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) = 2 := by
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  calc
    ((2 : ℝ) ^ d) ^ ((d : ℝ)⁻¹) =
        ((2 : ℝ) ^ (d : ℝ)) ^ ((d : ℝ)⁻¹) := by
          rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((d : ℝ) * (d : ℝ)⁻¹) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = 2 := by rw [mul_inv_cancel₀ hdreal, Real.rpow_one]

private theorem packingGeometricRoot_eq_normalizedVolumeRoot_div_two
    {d : ℕ} (hd : 0 < d) :
    packingGeometricRoot d = normalizedVolumeRoot d / 2 := by
  unfold packingGeometricRoot normalizedVolumeRoot
  rw [Real.div_rpow (unitBallVolume_pos d).le (by positivity),
    rpow_two_pow_inv_dimension hd]
  ring

private theorem tendsto_packingGeometricRoot :
    Tendsto packingGeometricRoot atTop
      (nhds (Real.sqrt (2 * Real.pi * Real.exp 1) / 2)) := by
  have hlimit := tendsto_normalizedVolumeRoot.div_const (2 : ℝ)
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (packingGeometricRoot_eq_normalizedVolumeRoot_div_two hd).symm

end

section

open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace Pointwise ContDiff

private noncomputable def radialFlatBumpReal (d : ℕ) (x : Euclidean d) : ℝ :=
  expNegInvGlue (1 - 4 * ‖x‖ ^ 2)

private noncomputable def radialFlatBumpFun (d : ℕ) (x : Euclidean d) : ℂ :=
  (radialFlatBumpReal d x : ℂ)

private theorem radialFlatBumpReal_nonneg (d : ℕ) (x : Euclidean d) :
    0 ≤ radialFlatBumpReal d x :=
  expNegInvGlue.nonneg _

private theorem radialFlatBumpReal_zero_pos (d : ℕ) :
    0 < radialFlatBumpReal d (0 : Euclidean d) := by
  unfold radialFlatBumpReal
  simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] using! expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1)

private theorem support_radialFlatBumpReal (d : ℕ) :
    Function.support (radialFlatBumpReal d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  ext x
  simp only [Function.mem_support, radialFlatBumpReal,
    Metric.mem_ball, dist_zero_right]
  constructor
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      exact lt_of_not_ge (fun h => hx (expNegInvGlue.zero_of_nonpos h))
    nlinarith [norm_nonneg x]
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := by
      nlinarith [norm_nonneg x]
    exact (expNegInvGlue.pos_of_pos hpos).ne'

private theorem support_radialFlatBumpFun (d : ℕ) :
    Function.support (radialFlatBumpFun d) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) := by
  rw [← support_radialFlatBumpReal d]
  ext x
  simp only [mem_support, radialFlatBumpFun, ne_eq, Complex.ofReal_eq_zero]

private theorem radialFlatBumpFun_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (radialFlatBumpFun d) := by
  change ContDiff ℝ ∞
    (fun x : Euclidean d =>
      Complex.ofRealCLM (expNegInvGlue (1 - 4 * ‖x‖ ^ 2)))
  exact Complex.ofRealCLM.contDiff.comp
    (expNegInvGlue.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

private theorem radialFlatBumpFun_hasCompactSupport (d : ℕ) :
    HasCompactSupport (radialFlatBumpFun d) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (1 / 2 : ℝ))
  rw [support_radialFlatBumpFun]
  exact Metric.ball_subset_closedBall

private noncomputable def radialFlatBump (d : ℕ) : TestFunction d :=
  (radialFlatBumpFun_hasCompactSupport d).toSchwartzMap
    (radialFlatBumpFun_contDiff d)

@[simp] private theorem radialFlatBump_apply (d : ℕ) (x : Euclidean d) :
    radialFlatBump d x = (radialFlatBumpReal d x : ℂ) := by
  rfl

private theorem radialFlatBump_real (d : ℕ) : IsRealValued (radialFlatBump d) := by
  intro x
  simp only [radialFlatBump_apply, Complex.ofReal_im]

private theorem radialFlatBump_radial (d : ℕ) : IsRadial (radialFlatBump d) := by
  intro x y hxy
  simp only [radialFlatBump_apply, radialFlatBumpReal, hxy]

private theorem integral_radialFlatBumpReal_pos (d : ℕ) :
    0 < ∫ x : Euclidean d, radialFlatBumpReal d x := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (show Continuous (radialFlatBumpReal d) by
      unfold radialFlatBumpReal
      fun_prop)
  · have hcomplex :
        Integrable (radialFlatBump d : Euclidean d → ℂ) :=
      (radialFlatBump d).integrable
    simpa only [radialFlatBump_apply, RCLike.re_to_complex, Complex.ofReal_re] using! hcomplex.re
  · exact radialFlatBumpReal_nonneg d
  · exact (radialFlatBumpReal_zero_pos d).ne'

private theorem IsRadial.fourier {d : ℕ} {f : TestFunction d}
    (hf : IsRadial f) : IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
    Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := by
    funext z
    exact hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x =
    (𝓕 (f : Euclidean d → ℂ)) y
  calc
    (𝓕 (f : Euclidean d → ℂ)) x =
        (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) :=
      Real.fourier_comp_linearIsometry A (f : Euclidean d → ℂ) x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hA]

private theorem fourier_conj_apply_of_real {d : ℕ} (f : TestFunction d)
    (hf : IsRealValued f) (ξ : Euclidean d) :
    starRingEnd ℂ ((𝓕 f : TestFunction d) ξ) =
      ((𝓕 f : TestFunction d) (-ξ)) := by
  change starRingEnd ℂ ((𝓕 (f : Euclidean d → ℂ)) ξ) =
    (𝓕 (f : Euclidean d → ℂ)) (-ξ)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  have hreal : starRingEnd ℂ (f x) = f x :=
    Complex.conj_eq_iff_im.mpr (hf x)
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofNat 2
  simp only [neg_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul,
    map_mul,
    ← Complex.exp_conj, map_neg, htwo, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg,
      hreal, inner_neg_right]

private theorem IsRealValued.fourier_of_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (hrad : IsRadial f) :
    IsRealValued (𝓕 f : TestFunction d) := by
  intro ξ
  apply Complex.conj_eq_iff_im.mp
  rw [fourier_conj_apply_of_real f hf]
  exact hrad.fourier (-ξ) ξ (by simp only [norm_neg])

private noncomputable def radialAutocorrelation (d : ℕ) : TestFunction d :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (radialFlatBump d) (radialFlatBump d)

private theorem fourier_radialAutocorrelation_apply (d : ℕ) (ξ : Euclidean d) :
    ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ) =
      ((𝓕 (radialFlatBump d) : TestFunction d) ξ) ^ 2 := by
  unfold radialAutocorrelation
  rw [SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply', pow_two]

private theorem fourier_radialFlatBump_real (d : ℕ) :
    IsRealValued (𝓕 (radialFlatBump d) : TestFunction d) :=
  (radialFlatBump_real d).fourier_of_radial (radialFlatBump_radial d)

private theorem fourier_radialAutocorrelation_real (d : ℕ) :
    IsRealValued (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro ξ
  rw [fourier_radialAutocorrelation_apply]
  simp only [pow_two, Complex.mul_im, fourier_radialFlatBump_real d ξ, mul_zero, zero_mul, add_zero]

private theorem fourier_radialAutocorrelation_nonneg (d : ℕ) (ξ : Euclidean d) :
    0 ≤ ((𝓕 (radialAutocorrelation d) : TestFunction d) ξ).re := by
  rw [fourier_radialAutocorrelation_apply]
  simp only [pow_two, Complex.mul_re, fourier_radialFlatBump_real d ξ,
    mul_zero, sub_zero]
  exact mul_self_nonneg _

private theorem fourier_radialFlatBump_zero (d : ℕ) :
    ((𝓕 (radialFlatBump d) : TestFunction d) (0 : Euclidean d)) =
      (↑(∫ x : Euclidean d, radialFlatBumpReal d x) : ℂ) := by
  change (𝓕 (radialFlatBump d : Euclidean d → ℂ)) 0 = _
  rw [Real.fourier_eq']
  simpa only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    radialFlatBump_apply, smul_eq_mul, one_mul, Complex.coe_algebraMap] using!
    (integral_ofReal (𝕜 := ℂ)
      (f := radialFlatBumpReal d)
      (μ := (volume : Measure (Euclidean d))))

private theorem fourier_radialAutocorrelation_zero_pos (d : ℕ) :
    0 < ((𝓕 (radialAutocorrelation d) : TestFunction d)
      (0 : Euclidean d)).re := by
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialFlatBump_zero]
  simpa only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    mul_self_pos,
    ne_eq] using!
    mul_pos (integral_radialFlatBumpReal_pos d)
      (integral_radialFlatBumpReal_pos d)

private theorem support_radialFlatBump (d : ℕ) :
    Function.support (radialFlatBump d : Euclidean d → ℂ) =
      Metric.ball (0 : Euclidean d) (1 / 2 : ℝ) :=
  support_radialFlatBumpFun d

private theorem support_radialAutocorrelation_subset (d : ℕ) :
    Function.support (radialAutocorrelation d : Euclidean d → ℂ) ⊆
      Metric.ball (0 : Euclidean d) (1 : ℝ) := by
  have hconv :
      (radialAutocorrelation d : Euclidean d → ℂ) =
        MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x
    exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ)
      (radialFlatBump d) (radialFlatBump d) x
  rw [hconv]
  calc
    Function.support
        (MeasureTheory.convolution
          (radialFlatBump d : Euclidean d → ℂ)
          (radialFlatBump d : Euclidean d → ℂ)
          (ContinuousLinearMap.mul ℂ ℂ) volume) ⊆
        Function.support (radialFlatBump d : Euclidean d → ℂ) +
          Function.support (radialFlatBump d : Euclidean d → ℂ) :=
      MeasureTheory.support_convolution_subset
        (ContinuousLinearMap.mul ℂ ℂ)
    _ = Metric.ball (0 : Euclidean d) (1 : ℝ) := by
      rw [support_radialFlatBump]
      rw [ball_add_ball (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num

private theorem radialAutocorrelation_outside_eq_zero (d : ℕ)
    (x : Euclidean d) (hx : 1 ≤ ‖x‖) :
    radialAutocorrelation d x = 0 := by
  by_contra hne
  have hsupport : x ∈ Function.support
      (radialAutocorrelation d : Euclidean d → ℂ) := hne
  have hball := support_radialAutocorrelation_subset d hsupport
  have hnorm : ‖x‖ < (1 : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using! hball
  linarith

private theorem radialAutocorrelation_real (d : ℕ) :
    IsRealValued (radialAutocorrelation d) := by
  intro x
  rw [radialAutocorrelation, SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def]
  change
    (∫ t : Euclidean d,
      (radialFlatBumpReal d t : ℂ) *
        (radialFlatBumpReal d (x - t) : ℂ)).im = 0
  simp_rw [← Complex.ofReal_mul]
  have hreal :
      (∫ t : Euclidean d,
        (↑(radialFlatBumpReal d t *
          radialFlatBumpReal d (x - t)) : ℂ)) =
        (↑(∫ t : Euclidean d,
          radialFlatBumpReal d t * radialFlatBumpReal d (x - t)) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hreal]
  simp only [Complex.ofReal_im]

private theorem fourier_radialAutocorrelation_radial (d : ℕ) :
    IsRadial (𝓕 (radialAutocorrelation d) : TestFunction d) := by
  intro x y hxy
  rw [fourier_radialAutocorrelation_apply,
    fourier_radialAutocorrelation_apply]
  rw [(radialFlatBump_radial d).fourier x y hxy]

private theorem radialAutocorrelation_radial (d : ℕ) :
    IsRadial (radialAutocorrelation d) := by
  intro x y hxy
  have h := (fourier_radialAutocorrelation_radial d).fourier
    (-x) (-y) (by simpa only [norm_neg] using! hxy)
  simpa only [fourier_sq_apply, neg_neg] using! h

private noncomputable def autocorrelationAdmissible (d : ℕ) : Admissible d where
  function := radialAutocorrelation d
  real := radialAutocorrelation_real d
  radial := radialAutocorrelation_radial d
  fourier_real := fourier_radialAutocorrelation_real d
  fourier_nonneg := fourier_radialAutocorrelation_nonneg d
  fourier_zero_pos := fourier_radialAutocorrelation_zero_pos d
  outside_nonpos := by
    intro x hx
    rw [radialAutocorrelation_outside_eq_zero d x hx]
    simp only [Complex.zero_re, Std.le_refl]

private theorem admissible_nonempty (d : ℕ) : Nonempty (Admissible d) :=
  ⟨autocorrelationAdmissible d⟩

private theorem quotientSet_nonempty (d : ℕ) : (quotientSet d).Nonempty :=
  ⟨quotient (autocorrelationAdmissible d),
    ⟨autocorrelationAdmissible d, rfl⟩⟩

end

section

private theorem log_criticalPackingBase :
    Real.log criticalPackingBase =
      (1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi)) := by
  unfold criticalPackingBase
  rw [Real.log_sqrt (by positivity)]
  ring

private theorem logb_criticalPackingBase :
    Real.logb 2 criticalPackingBase = -criticalBinaryExponent := by
  rw [Real.logb, log_criticalPackingBase]
  unfold criticalBinaryExponent
  rw [Real.logb]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_exp]
  ring

private theorem criticalPackingBase_lt_one : criticalPackingBase < 1 := by
  unfold criticalPackingBase
  have hratio : Real.exp 1 / (2 * Real.pi) < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith [Real.exp_one_lt_three, Real.pi_gt_three]
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    (by simpa only [one_pow] using! hratio)

private theorem criticalBinaryExponent_pos : 0 < criticalBinaryExponent := by
  have hlog : Real.logb 2 criticalPackingBase < 0 := by
    exact (Real.logb_neg (by norm_num) criticalPackingBase_pos
      criticalPackingBase_lt_one)
  rw [logb_criticalPackingBase] at hlog
  linarith

end

section

open Filter
open scoped Topology

private theorem uniformAdmissibleLowerBound_of_signRadius
    (hsign : UniformAntiFourierSignRadius) :
    UniformAdmissibleLowerBound := by
  intro c hc
  by_cases hpositive : 0 < c
  · filter_upwards [hsign c hpositive hc,
      eventually_gt_atTop (0 : ℕ)] with d hno hd
    intro f
    exact normalizedCost_ge_of_no_antiFourierWitness f hd c hno
  · exact Filter.Eventually.of_forall fun d f =>
      (le_of_not_gt hpositive).trans (normalizedCost_nonneg f)

private theorem normalizedProgram_eq_quotientInf_root_unconditional (d : ℕ) :
    normalizedProgram d =
      quotientRootMap d (sInf (quotientSet d)) :=
  normalizedProgram_eq_quotientInf_root d (admissible_nonempty d)

private theorem quotientInf_nonneg_unconditional (d : ℕ) :
    0 ≤ sInf (quotientSet d) :=
  quotientInf_nonneg d (admissible_nonempty d)

private theorem linearProgram_nonneg (d : ℕ) : 0 ≤ linearProgram d := by
  unfold linearProgram
  exact mul_nonneg (geometricFactor_pos d).le
    (quotientInf_nonneg_unconditional d)

private theorem linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
    {d : ℕ} (hd : 0 < d) :
    (linearProgram d) ^ ((d : ℝ)⁻¹) =
      packingGeometricRoot d * normalizedProgram d :=
  linearProgram_root_eq_geometric_mul_normalizedProgram hd
    (admissible_nonempty d)

private theorem geometricLimit_mul_criticalRadius :
    (Real.sqrt (2 * Real.pi * Real.exp 1) / 2) *
        Real.pi⁻¹ = criticalPackingBase := by
  have hleft :
      (Real.sqrt (2 * Real.pi * Real.exp 1)) ^ 2 =
        2 * Real.pi * Real.exp 1 :=
    Real.sq_sqrt (by positivity)
  have hright :
      (2 * Real.pi * Real.sqrt (Real.exp 1 / (2 * Real.pi))) ^ 2 =
        2 * Real.pi * Real.exp 1 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have heq :
      Real.sqrt (2 * Real.pi * Real.exp 1) =
        2 * Real.pi * Real.sqrt (Real.exp 1 / (2 * Real.pi)) := by
    have hleft_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * Real.exp 1) :=
      Real.sqrt_nonneg _
    have hright_nonneg :
        0 ≤ 2 * Real.pi * Real.sqrt (Real.exp 1 / (2 * Real.pi)) := by
      positivity
    nlinarith
  unfold criticalPackingBase
  rw [heq]
  field_simp

private theorem sharpPackingRoot_of_sharpQuotient
    (hquotient : SharpQuotientAsymptotic) :
    SharpPackingRootAsymptotic := by
  unfold SharpQuotientAsymptotic at hquotient
  unfold SharpPackingRootAsymptotic
  have hproduct := tendsto_packingGeometricRoot.mul hquotient
  rw [geometricLimit_mul_criticalRadius] at hproduct
  refine hproduct.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact
    (linearProgram_root_eq_geometric_mul_normalizedProgram_unconditional
      hd).symm

private theorem eventually_linearProgram_pos_of_sharpQuotient
    (hquotient : SharpQuotientAsymptotic) :
    ∀ᶠ d : ℕ in atTop, 0 < linearProgram d := by
  have hnorm : ∀ᶠ d : ℕ in atTop, 0 < normalizedProgram d :=
    hquotient.eventually (Ioi_mem_nhds (inv_pos.mpr Real.pi_pos))
  filter_upwards [hnorm, eventually_gt_atTop (0 : ℕ)] with d hpositive hd
  have hnonneg := quotientInf_nonneg_unconditional d
  have hinf : 0 < sInf (quotientSet d) := by
    by_contra hnot
    have hzero : sInf (quotientSet d) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    rw [normalizedProgram_eq_quotientInf_root_unconditional d,
      hzero] at hpositive
    have hdreal : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hd)
    simp only [quotientRootMap, ne_eq, inv_eq_zero, hdreal, not_false_eq_true, Real.zero_rpow,
      zero_div,
      lt_self_iff_false] at hpositive
  unfold linearProgram
  exact mul_pos (geometricFactor_pos d) hinf

private theorem sharpLog_of_sharpQuotient
    (hquotient : SharpQuotientAsymptotic) :
    SharpLogAsymptotic := by
  have hroot := sharpPackingRoot_of_sharpQuotient hquotient
  unfold SharpPackingRootAsymptotic at hroot
  have hlogs := hroot.log criticalPackingBase_pos.ne'
  rw [log_criticalPackingBase] at hlogs
  unfold SharpLogAsymptotic
  refine hlogs.congr' ?_
  filter_upwards [eventually_linearProgram_pos_of_sharpQuotient hquotient]
    with d hd
  rw [Real.log_rpow hd]
  ring

private noncomputable def SharpBinaryLogAsymptotic : Prop :=
  Tendsto
    (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ))
    atTop (nhds (-criticalBinaryExponent))

private theorem sharpBinaryLog_of_sharpQuotient
    (hquotient : SharpQuotientAsymptotic) :
    SharpBinaryLogAsymptotic := by
  have hnatural := sharpLog_of_sharpQuotient hquotient
  unfold SharpLogAsymptotic at hnatural
  have hscaled := hnatural.div_const (Real.log 2)
  have hconstant :
      ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * Real.pi))) /
          Real.log 2 = -criticalBinaryExponent := by
    calc
      _ = Real.log criticalPackingBase / Real.log 2 := by
        rw [log_criticalPackingBase]
      _ = Real.logb 2 criticalPackingBase := by
        rfl
      _ = -criticalBinaryExponent := logb_criticalPackingBase
  rw [hconstant] at hscaled
  unfold SharpBinaryLogAsymptotic
  refine hscaled.congr' (Filter.Eventually.of_forall ?_)
  intro d
  change
    (Real.log (linearProgram d) / (d : ℝ)) / Real.log 2 =
      (Real.log (linearProgram d) / Real.log 2) / (d : ℝ)
  ring

private theorem sharpAsymptotics_of_uniform_lower_and_ordered_upper
    (hlower : UniformAdmissibleLowerBound)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  have hquotient :=
    sharpQuotient_of_uniform_lower_and_ordered_upper hlower construction
  exact ⟨hquotient, sharpPackingRoot_of_sharpQuotient hquotient,
    sharpLog_of_sharpQuotient hquotient,
    sharpBinaryLog_of_sharpQuotient hquotient⟩

private theorem sharpAsymptotics_of_signRadius_and_ordered_upper
    (hsign : UniformAntiFourierSignRadius)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_uniform_lower_and_ordered_upper
    (uniformAdmissibleLowerBound_of_signRadius hsign) construction

private theorem saddleSourceSchwartzRealization :
    SaddleSourceSchwartzRealization := by
  intro ε hε horder d hd
  refine ⟨minusSaddleSchwartz hε hd horder,
    plusSaddleSchwartz hε hd horder, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl

private noncomputable def saddleOrderedUpperConstruction_of_sourceSigns
    (hsigns : SaddleSourceEventualSigns) :
    OrderedEpsilonUpperConstruction :=
  saddleOrderedUpperConstruction
    saddleSourceSchwartzRealization hsigns

private theorem sharpAsymptotics_of_saddleSourceEventualSigns
    (hsigns : SaddleSourceEventualSigns) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_signRadius_and_ordered_upper
    uniformAntiFourierSignRadius
    (saddleOrderedUpperConstruction_of_sourceSigns hsigns)

end

section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

private theorem eventually_plusSaddleProfile_nonneg_on_star :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_plusSaddleProfile_re_pos_on_star]
    with ε hε
  filter_upwards [hε] with d hd
  intro r hr hstar
  exact (hd r hr hstar).le

private theorem plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
    {ε : ℝ} {d : ℕ} {u : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hV : 0 < saddleSourceGaussianVariance ε ((d : ℝ) / 2) u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T).re) :
    0 < (plusSaddleProfile ε ((d : ℝ) / 2)
      (Real.exp (saddleLogRadius ε d u))).re := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  exact plusSaddleProfile_exp_re_pos_of_gaussian_error
    hε hℓ hu horder hV herror

private theorem minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
    {ε : ℝ} {d : ℕ} {u : ℝ}
    (hε : 0 < ε) (hd : 0 < d) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hV : 0 < saddleSourceGaussianVariance ε ((d : ℝ) / 2) u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T).re) :
    (minusSaddleProfile ε ((d : ℝ) / 2)
      (Real.exp (saddleLogRadius ε d u))).re < 0 := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  exact minusSaddleProfile_exp_re_neg_of_gaussian_error
    hε hℓ hu horder hV herror

private theorem saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hu : -1 < u) :
    (∫ T : ℝ, saddleSourceGaussianPlusIntegrand ε ℓ u T).re =
      ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hvalue : 0 < (ε / 4) + (1 - u) ^ 2 * (1 + u) := by
    have h := plusPolynomial_imaginary_re_pos hε hu
    rw [plusPolynomial_imaginary, Complex.ofReal_re] at h
    exact h
  rw [saddleSourceGaussianPlusIntegrand_integral,
    saddleSourceGaussianKernel_integral,
    plusPolynomial_imaginary]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hvalue]
  ring

private theorem saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    -(∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T).re =
      ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
        (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  have hvalue : (ε / 4) + (1 - u) * (1 + u) ^ 2 < 0 := by
    have h := minusPolynomial_imaginary_re_neg hε hu
    rw [minusPolynomial_imaginary, Complex.ofReal_re] at h
    exact h
  rw [saddleSourceGaussianMinusIntegrand_integral,
    saddleSourceGaussianKernel_integral,
    minusPolynomial_imaginary]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg hvalue]
  ring

private theorem saddleSmallRadiusStarOrdinate_sourceScale
    {d : ℕ} (hd : 0 < d) (ε : ℝ)
    {u : ℝ}
    (hu : saddleSmallRadiusStarOrdinate ε d ≤ u) :
    Real.log ((d : ℝ) / 2) / 4 ≤
      ((d : ℝ) / 2) * (1 + u) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  have hstar :
      ℓ * (1 + saddleSmallRadiusStarOrdinate ε d) =
        Real.log ℓ / 4 := by
    unfold saddleSmallRadiusStarOrdinate
    try dsimp [ℓ]
    field_simp [hℓ.ne']
    ring
  change Real.log ℓ / 4 ≤ ℓ * (1 + u)
  rw [← hstar]
  apply mul_le_mul_of_nonneg_left _ hℓ.le
  linarith

private theorem saddleSource_positiveOrdinate_sourceScale
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 1 ≤ u) :
    Real.log ℓ / 4 ≤ ℓ * (1 + u) := by
  have hlog := Real.log_le_sub_one_of_pos hℓ
  have hproduct :=
    mul_nonneg hℓ.le (sub_nonneg.mpr hu)
  linarith

private theorem eventually_plusSaddleProfile_re_pos_at_firstBranchSaddles :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ u : ℝ,
          saddleSmallRadiusStarOrdinate ε d ≤ u →
            u ≤ 1 + ε / 2 →
              0 < (plusSaddleProfile ε ((d : ℝ) / 2)
                (Real.exp (saddleLogRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε,
    eventually_gt_atTop (0 : ℕ)]
    with d hdimen hstar hd
  intro u hu hupper
  have hulower : -1 < u := hstar.trans_le hu
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hscale := saddleSmallRadiusStarOrdinate_sourceScale hd ε hu
  have herr := (hdimen u hulower hupper hscale).1
  have hV := hvariance ((d : ℝ) / 2) hℓ u hulower hupper
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
      hε hulower]
    simpa only [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
    hε hd hulower horder hV herror

private theorem eventually_minusSaddleProfile_re_neg_at_firstBranchSaddles :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ u : ℝ,
          1 + ε / 4 ≤ u →
            u ≤ 1 + ε / 2 →
              (minusSaddleProfile ε ((d : ℝ) / 2)
                (Real.exp (saddleLogRadius ε d u))).re < 0 := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_gt_atTop (0 : ℕ)] with d hdimen hd
  intro u hulower hupper
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hu : -1 < u := by linarith
  have huone : 1 ≤ u := by linarith
  have hscale := saddleSource_positiveOrdinate_sourceScale hℓ huone
  have herr := (hdimen u hu hupper hscale).2 hulower
  have hV := hvariance ((d : ℝ) / 2) hℓ u hu hupper
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
      hε hulower]
    simpa only [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
    hε hd hu horder hV herror

private theorem eventually_plusSaddleProfile_re_pos_at_secondBranchSaddles :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ u : ℝ, 1 + ε / 2 ≤ u →
          0 < (plusSaddleProfile ε ((d : ℝ) / 2)
            (Real.exp (saddleLogRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_gt_atTop (0 : ℕ)] with d hdimen hd
  intro u hu
  let δ : ℝ := u - 1
  have hδ : ε / 2 ≤ δ := by
    try dsimp [δ]
    linarith
  have hidentity : 1 + δ = u := by
    try dsimp [δ]
    ring
  have hulower : -1 < u := by linarith
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hV : 0 <
      saddleSourceGaussianVariance ε ((d : ℝ) / 2) u := by
    simpa only [hidentity] using!
      hvariance ((d : ℝ) / 2) hℓ δ hδ
  have herr := (hdimen δ hδ).1
  rw [hidentity] at herr
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianPlusIntegrand_integral_re_eq_norm
      hε hulower]
    simpa only [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact plusSaddleProfile_re_pos_at_sourceSaddle_of_gaussian_error
    hε hd hulower horder hV herror

private theorem eventually_minusSaddleProfile_re_neg_at_secondBranchSaddles :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ u : ℝ, 1 + ε / 2 ≤ u →
          (minusSaddleProfile ε ((d : ℝ) / 2)
            (Real.exp (saddleLogRadius ε d u))).re < 0 := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_fullGaussianErrors]
    with ε hε horder hvariance hfull
  change 0 < ε at hε
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hfull
  filter_upwards [hdimension,
    eventually_gt_atTop (0 : ℕ)] with d hdimen hd
  intro u hu
  let δ : ℝ := u - 1
  have hδ : ε / 2 ≤ δ := by
    try dsimp [δ]
    linarith
  have hidentity : 1 + δ = u := by
    try dsimp [δ]
    ring
  have hulower : -1 < u := by linarith
  have huminus : 1 + ε / 4 ≤ u := by linarith
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hV : 0 <
      saddleSourceGaussianVariance ε ((d : ℝ) / 2) u := by
    simpa only [hidentity] using!
      hvariance ((d : ℝ) / 2) hℓ δ hδ
  have herr := (hdimen δ hδ).2
  rw [hidentity] at herr
  have herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ((d : ℝ) / 2) u
            (saddleLogRadius ε d u) T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ((d : ℝ) / 2) u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand
            ε ((d : ℝ) / 2) u T).re := by
    rw [saddleSourceGaussianMinusIntegrand_neg_integral_re_eq_norm
      hε huminus]
    simpa only [saddleSourceStationaryLogRadius_eq_saddleLogRadius] using! herr
  exact minusSaddleProfile_re_neg_at_sourceSaddle_of_gaussian_error
    hε hd hulower horder hV herror

private theorem eventually_plusSaddleProfile_nonneg_of_star :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSmallRadiusStar ε d ≤ r →
            0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_saddleSmallRadiusStar_log_coverage,
    eventually_plusSaddleProfile_re_pos_at_firstBranchSaddles,
    eventually_plusSaddleProfile_re_pos_at_secondBranchSaddles]
    with ε hcoverage hfirst hsecond
  filter_upwards [hcoverage, hfirst, hsecond]
    with d hcoverage_d hfirst_d hsecond_d
  intro r hr
  obtain ⟨u, hu, hlog⟩ := hcoverage_d r hr
  have hrpos : 0 < r :=
    (saddleSmallRadiusStar_pos ε d).trans_le hr
  have hexp : Real.exp (saddleLogRadius ε d u) = r := by
    rw [hlog, Real.exp_log hrpos]
  by_cases hbranch : u ≤ 1 + ε / 2
  · have h := hfirst_d u hu hbranch
    rw [hexp] at h
    exact h.le
  · have hupper : 1 + ε / 2 ≤ u :=
      (lt_of_not_ge hbranch).le
    have h := hsecond_d u hupper
    rw [hexp] at h
    exact h.le

private theorem eventually_minusSaddleProfile_nonpos_of_sourceRadius :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSourceRadius ε d ≤ r →
            (minusSaddleProfile ε ((d : ℝ) / 2) r).re ≤ 0 := by
  filter_upwards [eventually_saddleSourceRadius_log_coverage,
    eventually_minusSaddleProfile_re_neg_at_firstBranchSaddles,
    eventually_minusSaddleProfile_re_neg_at_secondBranchSaddles]
    with ε hcoverage hfirst hsecond
  filter_upwards [hfirst, hsecond,
    eventually_gt_atTop (0 : ℕ)] with d hfirst_d hsecond_d hd
  intro r hr
  obtain ⟨u, hu, hlog⟩ := hcoverage d hd r hr
  have hrpos : 0 < r :=
    (saddleSourceRadius_pos ε d).trans_le hr
  have hexp : Real.exp (saddleLogRadius ε d u) = r := by
    rw [hlog, Real.exp_log hrpos]
  by_cases hbranch : u ≤ 1 + ε / 2
  · have h := hfirst_d u hu hbranch
    rw [hexp] at h
    exact h.le
  · have hupper : 1 + ε / 2 ≤ u :=
      (lt_of_not_ge hbranch).le
    have h := hsecond_d u hupper
    rw [hexp] at h
    exact h.le

private theorem saddleSourceEventualSigns : SaddleSourceEventualSigns := by
  unfold SaddleSourceEventualSigns
  filter_upwards [eventually_plusSaddleProfile_nonneg_on_star,
    eventually_plusSaddleProfile_nonneg_of_star,
    eventually_minusSaddleProfile_nonpos_of_sourceRadius]
    with ε hsmall hlarge hminus
  filter_upwards [hsmall, hlarge, hminus]
    with d hsmall_d hlarge_d hminus_d
  constructor
  · intro x
    change 0 ≤ (plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖).re
    rcases le_total ‖x‖ (saddleSmallRadiusStar ε d) with hx | hx
    · exact hsmall_d ‖x‖ (norm_nonneg x) hx
    · exact hlarge_d ‖x‖ hx
  · intro x hx
    change (minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖).re ≤ 0
    exact hminus_d ‖x‖ hx

private theorem sharpAsymptotics :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_saddleSourceEventualSigns saddleSourceEventualSigns

private theorem sharpQuotientAsymptotic : SharpQuotientAsymptotic :=
  sharpAsymptotics.1

private theorem sharpPackingRootAsymptotic : SharpPackingRootAsymptotic :=
  sharpAsymptotics.2.1

private theorem sharpLogAsymptotic : SharpLogAsymptotic :=
  sharpAsymptotics.2.2.1

private theorem sharpBinaryLogAsymptotic : SharpBinaryLogAsymptotic :=
  sharpAsymptotics.2.2.2

end

section

open Filter
open scoped Topology

private noncomputable def manuscriptQuotientRootSet (d : ℕ) : Set ℝ :=
  Set.range fun f : Admissible d => quotient f ^ ((d : ℝ)⁻¹)

private theorem manuscriptQuotientRootSet_eq_image (d : ℕ) :
    manuscriptQuotientRootSet d =
      (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) '' quotientSet d := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotient f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩

private theorem manuscriptQuotientRootInf_eq (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) =
      (sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) := by
  have hcontinuous :
      Continuous (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) :=
    Real.continuous_rpow_const (by positivity)
  have hmono :
      MonotoneOn (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) (quotientSet d) := by
    intro x hx y _ hxy
    obtain ⟨f, rfl⟩ := hx
    exact Real.rpow_le_rpow (quotient_pos f).le hxy (by positivity)
  obtain ⟨f⟩ := admissible_nonempty d
  have hnonempty : (quotientSet d).Nonempty :=
    ⟨quotient f, ⟨f, rfl⟩⟩
  rw [manuscriptQuotientRootSet_eq_image]
  exact
    (MonotoneOn.map_csInf_of_continuousWithinAt
      hcontinuous.continuousWithinAt hmono hnonempty
      (quotientSet_bddBelow d)).symm

private noncomputable def manuscriptNormalizedQuotientInfRoot (d : ℕ) : ℝ :=
  (sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) / Real.sqrt (d : ℝ)

private theorem manuscriptNormalizedQuotientInfRoot_eq (d : ℕ) :
    manuscriptNormalizedQuotientInfRoot d = normalizedProgram d := by
  rw [normalizedProgram_eq_quotientInf_root_unconditional]
  rfl

private theorem manuscriptQuotientRootInf_div_sqrt_eq (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ) =
      normalizedProgram d := by
  rw [manuscriptQuotientRootInf_eq]
  exact manuscriptNormalizedQuotientInfRoot_eq d

private theorem manuscriptQuotientRootInf_div_sqrt_tendsto
    (hquotient : SharpQuotientAsymptotic) :
    Tendsto
      (fun d : ℕ =>
        sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ))
      atTop (nhds ((Real.pi)⁻¹)) := by
  unfold SharpQuotientAsymptotic at hquotient
  exact hquotient.congr'
    (Filter.Eventually.of_forall fun d =>
      (manuscriptQuotientRootInf_div_sqrt_eq d).symm)

private noncomputable def manuscriptPackingDeficit (d : ℕ) : ℝ :=
  max 0 (criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))

private theorem manuscriptPackingDeficit_nonneg (d : ℕ) :
    0 ≤ manuscriptPackingDeficit d := by
  exact le_max_left _ _

private theorem manuscriptPackingDeficit_le_criticalPackingBase (d : ℕ) :
    manuscriptPackingDeficit d ≤ criticalPackingBase := by
  unfold manuscriptPackingDeficit
  refine max_le criticalPackingBase_pos.le ?_
  have hroot : 0 ≤ (linearProgram d) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_nonneg (linearProgram_nonneg d) _
  linarith

private theorem tendsto_manuscriptPackingDeficit
    (hpacking : SharpPackingRootAsymptotic) :
    Tendsto manuscriptPackingDeficit atTop (nhds (0 : ℝ)) := by
  unfold SharpPackingRootAsymptotic at hpacking
  have hconstant :
      Tendsto (fun _ : ℕ => criticalPackingBase) atTop
        (nhds criticalPackingBase) := tendsto_const_nhds
  have hsub :
      Tendsto
        (fun d : ℕ =>
          criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))
        atTop (nhds (0 : ℝ)) := by
    simpa only [sub_self] using! hconstant.sub hpacking
  have hmax :=
    (tendsto_const_nhds (f := atTop) (x := (0 : ℝ))).max hsub
  simpa only [max_self] using! hmax

private theorem manuscriptPackingRoot_sub_deficit_le (d : ℕ) :
    criticalPackingBase - manuscriptPackingDeficit d ≤
      (linearProgram d) ^ ((d : ℝ)⁻¹) := by
  have hdeficit :
      criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹) ≤
        manuscriptPackingDeficit d := by
    exact le_max_right _ _
  linarith

private theorem manuscriptPackingRoot_sub_deficit_pow_le
    {d : ℕ} (hd : 0 < d) :
    (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      linearProgram d := by
  have hbase : 0 ≤ criticalPackingBase - manuscriptPackingDeficit d :=
    sub_nonneg.mpr (manuscriptPackingDeficit_le_criticalPackingBase d)
  have hpower :=
    pow_le_pow_left₀ hbase (manuscriptPackingRoot_sub_deficit_le d) d
  rw [Real.rpow_inv_natCast_pow (linearProgram_nonneg d)
    (Nat.ne_of_gt hd)] at hpower
  exact hpower

private theorem linearProgram_le_geometric_mul_quotient
    {d : ℕ} (f : Admissible d) :
    linearProgram d ≤
      (unitBallVolume d / (2 : ℝ) ^ d) * quotient f := by
  unfold linearProgram
  exact mul_le_mul_of_nonneg_left
    (csInf_le (quotientSet_bddBelow d) ⟨f, rfl⟩)
    (geometricFactor_pos d).le

private theorem manuscriptUniversalQuotientBound
    {d : ℕ} (hd : 0 < d) (f : Admissible d) :
    (2 : ℝ) ^ d / unitBallVolume d *
        (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      quotient f := by
  have hprogram :=
    (manuscriptPackingRoot_sub_deficit_pow_le hd).trans
      (linearProgram_le_geometric_mul_quotient f)
  calc
    (2 : ℝ) ^ d / unitBallVolume d *
        (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      (2 : ℝ) ^ d / unitBallVolume d *
        ((unitBallVolume d / (2 : ℝ) ^ d) * quotient f) := by
          exact mul_le_mul_of_nonneg_left hprogram
            (div_pos (pow_pos (by norm_num : (0 : ℝ) < 2) d)
              (unitBallVolume_pos d)).le
    _ = quotient f := by
      have hv := (unitBallVolume_pos d).ne'
      field_simp

private noncomputable def manuscriptPackingRootError (d : ℕ) : ℝ :=
  (linearProgram d) ^ ((d : ℝ)⁻¹) - criticalPackingBase

private theorem tendsto_manuscriptPackingRootError
    (hpacking : SharpPackingRootAsymptotic) :
    Tendsto manuscriptPackingRootError atTop (nhds (0 : ℝ)) := by
  unfold SharpPackingRootAsymptotic at hpacking
  have hconstant :
      Tendsto (fun _ : ℕ => criticalPackingBase) atTop
        (nhds criticalPackingBase) := tendsto_const_nhds
  simpa only [sub_self] using! hpacking.sub hconstant

private theorem manuscriptLinearProgram_eq_packing_error_pow
    {d : ℕ} (hd : 0 < d) :
    linearProgram d =
      (criticalPackingBase + manuscriptPackingRootError d) ^ d := by
  have hroot :
      criticalPackingBase + manuscriptPackingRootError d =
        (linearProgram d) ^ ((d : ℝ)⁻¹) := by
    unfold manuscriptPackingRootError
    ring
  rw [hroot]
  exact (Real.rpow_inv_natCast_pow (linearProgram_nonneg d)
    (Nat.ne_of_gt hd)).symm

private noncomputable def manuscriptBinaryExponentError (d : ℕ) : ℝ :=
  -(Real.logb 2 (linearProgram d) / (d : ℝ)) -
    criticalBinaryExponent

private theorem tendsto_manuscriptBinaryExponentError
    (hbinary : SharpBinaryLogAsymptotic) :
    Tendsto manuscriptBinaryExponentError atTop (nhds (0 : ℝ)) := by
  unfold SharpBinaryLogAsymptotic at hbinary
  have hconstant :
      Tendsto (fun _ : ℕ => criticalBinaryExponent) atTop
        (nhds criticalBinaryExponent) := tendsto_const_nhds
  simpa only [neg_neg, sub_self] using! hbinary.neg.sub hconstant

private theorem manuscriptLinearProgram_eq_binary_error_rpow
    {d : ℕ} (hd : 0 < d) (hpositive : 0 < linearProgram d) :
    linearProgram d =
      (2 : ℝ) ^
        (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
          (d : ℝ)) := by
  have hdreal : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hexponent :
      -(criticalBinaryExponent + manuscriptBinaryExponentError d) *
        (d : ℝ) = Real.logb 2 (linearProgram d) := by
    unfold manuscriptBinaryExponentError
    field_simp
    ring
  rw [hexponent]
  exact (Real.rpow_logb (by norm_num) (by norm_num) hpositive).symm

private noncomputable def manuscriptQuotientRootError (d : ℕ) : ℝ :=
  normalizedProgram d - Real.pi⁻¹

private theorem tendsto_manuscriptQuotientRootError :
    Tendsto manuscriptQuotientRootError atTop (nhds (0 : ℝ)) := by
  have hquotient :
      Tendsto normalizedProgram atTop (nhds Real.pi⁻¹) :=
    sharpQuotientAsymptotic
  have hconstant :
      Tendsto (fun _ : ℕ => Real.pi⁻¹) atTop
        (nhds Real.pi⁻¹) := tendsto_const_nhds
  simpa only [sub_self] using!
    hquotient.sub hconstant

private theorem manuscriptQuotientRootError_isLittleO :
    Asymptotics.IsLittleO atTop
      manuscriptQuotientRootError (fun _ : ℕ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2
    tendsto_manuscriptQuotientRootError

private theorem manuscriptQuotientRootInf_eq_critical_add_error
    {d : ℕ} (hd : 0 < d) :
    sInf (manuscriptQuotientRootSet d) =
      ((Real.pi)⁻¹ + manuscriptQuotientRootError d) *
        Real.sqrt (d : ℝ) := by
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by
    positivity
  have hroot :=
    (div_eq_iff hsqrt.ne').mp
      (manuscriptQuotientRootInf_div_sqrt_eq d)
  calc
    sInf (manuscriptQuotientRootSet d) =
        normalizedProgram d * Real.sqrt (d : ℝ) := hroot
    _ = ((Real.pi)⁻¹ + manuscriptQuotientRootError d) *
        Real.sqrt (d : ℝ) := by
          unfold manuscriptQuotientRootError
          ring

private theorem exists_manuscriptQuotientRootIsLittleO :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d →
        sInf (manuscriptQuotientRootSet d) =
          ((Real.pi)⁻¹ + e d) * Real.sqrt (d : ℝ) := by
  refine ⟨manuscriptQuotientRootError,
    manuscriptQuotientRootError_isLittleO, ?_⟩
  intro d hd
  exact manuscriptQuotientRootInf_eq_critical_add_error hd

private theorem manuscriptPackingRootError_tendsto :
    Tendsto manuscriptPackingRootError atTop (nhds (0 : ℝ)) :=
  tendsto_manuscriptPackingRootError sharpPackingRootAsymptotic

private theorem manuscriptPackingRootError_isLittleO :
    Asymptotics.IsLittleO atTop
      manuscriptPackingRootError (fun _ : ℕ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2
    manuscriptPackingRootError_tendsto

private theorem manuscriptLinearProgram_eq_canonicalPackingPow
    {d : ℕ} (hd : 0 < d) :
    linearProgram d =
      (criticalPackingBase + manuscriptPackingRootError d) ^ d :=
  manuscriptLinearProgram_eq_packing_error_pow hd

private theorem exists_manuscriptPackingIsLittleO :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d →
        linearProgram d = (criticalPackingBase + e d) ^ d := by
  exact ⟨manuscriptPackingRootError,
    manuscriptPackingRootError_isLittleO,
    fun _ hd => manuscriptLinearProgram_eq_canonicalPackingPow hd⟩

private theorem manuscriptPackingDeficit_isLittleO :
    Asymptotics.IsLittleO atTop
      manuscriptPackingDeficit (fun _ : ℕ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2
    (tendsto_manuscriptPackingDeficit sharpPackingRootAsymptotic)

private theorem exists_manuscriptUniversalPackingIsLittleO :
    ∃ δ : ℕ → ℝ,
      Asymptotics.IsLittleO atTop δ (fun _ : ℕ => (1 : ℝ)) ∧
      (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ d : ℕ, 0 < d → ∀ f : Admissible d,
        (2 : ℝ) ^ d / unitBallVolume d *
          (criticalPackingBase - δ d) ^ d ≤ quotient f) := by
  exact ⟨manuscriptPackingDeficit,
    manuscriptPackingDeficit_isLittleO,
    manuscriptPackingDeficit_nonneg,
    fun _ hd f => manuscriptUniversalQuotientBound hd f⟩

private theorem manuscriptBinaryExponentError_tendsto :
    Tendsto manuscriptBinaryExponentError atTop (nhds (0 : ℝ)) :=
  tendsto_manuscriptBinaryExponentError sharpBinaryLogAsymptotic

private theorem manuscriptBinaryExponentError_isLittleO :
    Asymptotics.IsLittleO atTop
      manuscriptBinaryExponentError (fun _ : ℕ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2
    manuscriptBinaryExponentError_tendsto

private theorem eventually_manuscriptLinearProgram_pos :
    ∀ᶠ d : ℕ in atTop, 0 < linearProgram d :=
  eventually_linearProgram_pos_of_sharpQuotient
    sharpQuotientAsymptotic

private theorem manuscriptLinearProgram_eq_canonicalBinaryRpow
    {d : ℕ} (hd : 0 < d) (hpositive : 0 < linearProgram d) :
    linearProgram d =
      (2 : ℝ) ^
        (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
          (d : ℝ)) :=
  manuscriptLinearProgram_eq_binary_error_rpow hd hpositive

private theorem eventually_manuscriptLinearProgram_eq_canonicalBinaryRpow :
    ∀ᶠ d : ℕ in atTop,
      linearProgram d =
        (2 : ℝ) ^
          (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
            (d : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_manuscriptLinearProgram_pos]
    with d hd hpositive
  exact manuscriptLinearProgram_eq_canonicalBinaryRpow hd hpositive

private theorem exists_manuscriptBinaryIsLittleO :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ d : ℕ in atTop,
        linearProgram d =
          (2 : ℝ) ^
            (-(criticalBinaryExponent + e d) * (d : ℝ)) := by
  exact ⟨manuscriptBinaryExponentError,
    manuscriptBinaryExponentError_isLittleO,
    eventually_manuscriptLinearProgram_eq_canonicalBinaryRpow⟩

end

end CohnElkies
