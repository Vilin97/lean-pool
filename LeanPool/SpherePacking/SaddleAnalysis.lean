/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.GammaAnalysis
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# SaddleAnalysis

Saddle contours, Gaussian profiles, and source estimates.
-/

namespace CohnElkies

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def saddleSourceMellinContour (ℓ u T : ℝ) : ℂ :=
  ((ℓ * (1 + u) : ℝ) : ℂ) -
    Complex.I * ((ℓ * T : ℝ) : ℂ)

private theorem saddleSourceMellinContour_shellArgument
    {ℓ : ℝ} (hℓ : 0 < ℓ) (u T : ℝ) :
    Complex.I *
        (saddleSourceMellinContour ℓ u T - (ℓ : ℂ)) /
          (ℓ : ℂ) =
      (T : ℂ) + Complex.I * (u : ℂ) := by
  have hℓcomplex : (ℓ : ℂ) ≠ 0 := by
    exact_mod_cast hℓ.ne'
  unfold saddleSourceMellinContour
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul, sub_neg_eq_add]

private theorem saddleSourceMellinContour_gammaArgument
    (ℓ u T : ℝ) :
    saddleSourceMellinContour ℓ u T / 2 =
      ((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) := by
  unfold saddleSourceMellinContour
  push_cast
  ring

private theorem norm_saddleShellExponential_eq_exp_neg_damping
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ℓ T u : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hphase := saddleShellPhase_damping_identity
    hε horder ℓ T u
  rw [← Real.exp_add]
  congr 1
  linarith

private noncomputable def saddleSourceShellDerivative (ε u : ℝ) : ℝ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellDensity ε a * a * Real.sinh (u * a)) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    positiveShellDensity ε a * a * Real.sinh (u * a))

private theorem saddleSourceShellDerivative_one (ε : ℝ) :
    saddleSourceShellDerivative ε 1 =
      saddleShellDerivativeOne ε := by
  simp only [saddleSourceShellDerivative, one_mul, saddleShellDerivativeOne]

private theorem saddleSourceShellDerivative_neg
    (ε u : ℝ) :
    saddleSourceShellDerivative ε (-u) =
      -saddleSourceShellDerivative ε u := by
  unfold saddleSourceShellDerivative
  have hshort :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * a *
          Real.sinh (-u * a)) =
        -(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          shortShellDensity ε a * a *
            Real.sinh (u * a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      shortShellDensity ε a * a * Real.sinh (-u * a) =
        -(shortShellDensity ε a * a * Real.sinh (u * a))
    rw [neg_mul, Real.sinh_neg]
    ring
  have hpositive :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * a *
          Real.sinh (-u * a)) =
        -(∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          positiveShellDensity ε a * a *
            Real.sinh (u * a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      positiveShellDensity ε a * a * Real.sinh (-u * a) =
        -(positiveShellDensity ε a * a * Real.sinh (u * a))
    rw [neg_mul, Real.sinh_neg]
    ring
  rw [hshort, hpositive]
  ring

private theorem saddleLogRadius_eq_digamma_add_shellDerivative
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleLogRadius ε d u =
      -(Real.log Real.pi) / 2 +
        saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
          saddleSourceShellDerivative ε u := by
  unfold saddleLogRadius saddleSourceShellDerivative
  ring

private noncomputable def saddleSmallRadiusStarOrdinate (ε : ℝ) (d : ℕ) : ℝ :=
  let _sourceParameter : ℝ := ε
  show ℝ from
    -1 + Real.log ((d : ℝ) / 2) /
      (4 * ((d : ℝ) / 2))

private noncomputable def saddleSmallRadiusStar (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp
    (saddleLogRadius ε d
      (saddleSmallRadiusStarOrdinate ε d))

private theorem saddleSmallRadiusStar_pos (ε : ℝ) (d : ℕ) :
    0 < saddleSmallRadiusStar ε d := by
  unfold saddleSmallRadiusStar
  exact Real.exp_pos _

private theorem saddleSmallRadiusStar_gammaArgument
    {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    ((d : ℝ) / 2) *
        (1 + saddleSmallRadiusStarOrdinate ε d) / 2 =
      Real.log ((d : ℝ) / 2) / 8 := by
  have hdreal : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  unfold saddleSmallRadiusStarOrdinate
  field_simp
  ring

private theorem saddleSourceShellDerivative_eq_deriv
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (u : ℝ) :
    saddleSourceShellDerivative ε u =
      deriv (realHyperbolicShellPhase ε) u := by
  have h :=
    (realHyperbolicShellPhase_hasDerivAt
      hε horder u).deriv
  unfold saddleSourceShellDerivative
  simpa only [mul_comm] using! h.symm

private theorem saddleSourceShellDerivative_contDiff_one
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ (1 : WithTop ℕ∞)
      (saddleSourceShellDerivative ε) := by
  have hphase :
      ContDiff ℝ ((1 : WithTop ℕ∞) + 1)
        (realHyperbolicShellPhase ε) := by
    convert! realHyperbolicShellPhase_contDiff
      hε horder (2 : WithTop ℕ∞) using 1
  have hderiv :
      ContDiff ℝ (1 : WithTop ℕ∞)
        (deriv (realHyperbolicShellPhase ε)) :=
    (contDiff_succ_iff_deriv.mp hphase).2.2
  have heq :
      saddleSourceShellDerivative ε =
        deriv (realHyperbolicShellPhase ε) := by
    funext u
    exact saddleSourceShellDerivative_eq_deriv hε horder u
  rw [heq]
  exact hderiv

private theorem saddleSmallRadiusVariable_star_eq
    {ε : ℝ} {d : ℕ} (hd : 0 < d) :
    saddleSmallRadiusVariable ε (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma
            (Real.log ((d : ℝ) / 2) / 8) +
          2 *
            (saddleShellDerivativeOne ε +
              saddleSourceShellDerivative ε
                (saddleSmallRadiusStarOrdinate ε d))) := by
  have hpi : Real.pi = Real.exp (Real.log Real.pi) :=
    (Real.exp_log Real.pi_pos).symm
  unfold saddleSmallRadiusVariable saddleSmallRadiusStar
  rw [saddleLogRadius_eq_digamma_add_shellDerivative,
    saddleSmallRadiusStar_gammaArgument hd ε]
  nth_rw 1 [hpi]
  rw [show (Real.exp
      (-(Real.log Real.pi) / 2 +
        saddleDigamma (Real.log ((d : ℝ) / 2) / 8) / 2 +
        saddleSourceShellDerivative ε
          (saddleSmallRadiusStarOrdinate ε d))) ^ 2 =
      Real.exp
        (2 * (-(Real.log Real.pi) / 2 +
          saddleDigamma (Real.log ((d : ℝ) / 2) / 8) / 2 +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d))) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem saddleSourceShellDerivative_neg_one
    (ε : ℝ) :
    saddleSourceShellDerivative ε (-1) =
      -saddleShellDerivativeOne ε := by
  simpa only [saddleSourceShellDerivative_one] using!
    saddleSourceShellDerivative_neg ε 1

private theorem exists_saddleSourceShellDerivative_endpoint_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Icc (-1 : ℝ) 0,
        |saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε u| ≤
            C * (u + 1) := by
  have hcont :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
        (saddleSourceShellDerivative ε)
        (Icc (-1 : ℝ) 0) := by
    convert! (saddleSourceShellDerivative_contDiff_one
      hε horder).contDiffOn using 1
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound
      (f := saddleSourceShellDerivative ε)
      (n := 0) (by norm_num : (-1 : ℝ) ≤ 0) hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro u hu
  have hbound := hC u hu
  simp only [taylor_within_zero_eval,
    Real.norm_eq_abs, Nat.zero_add, pow_one] at hbound
  rw [saddleSourceShellDerivative_neg_one] at hbound
  have hidentity :
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε u =
        saddleSourceShellDerivative ε u -
          -saddleShellDerivativeOne ε := by
    ring
  rw [hidentity]
  calc
    |saddleSourceShellDerivative ε u -
        -saddleShellDerivativeOne ε| ≤
      C * (u - -1) := hbound
    _ ≤ max C 0 * (u + 1) := by
      have hnonneg : 0 ≤ u + 1 := by
        linarith [hu.1]
      calc
        C * (u - -1) = C * (u + 1) := by ring
        _ ≤ max C 0 * (u + 1) :=
          mul_le_mul_of_nonneg_right
            (le_max_left _ _) hnonneg

private theorem saddle_log_sq_le_four_mul
    {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hxpos : 0 < x := by linarith
  have hspos : 0 < Real.sqrt x :=
    Real.sqrt_pos.2 hxpos
  have hsquare := Real.sq_sqrt hxpos.le
  have hlogsplit :
      Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← hsquare, Real.log_pow]
    norm_num
  have hslog := Real.log_le_sub_one_of_pos hspos
  have hlognonnegative : 0 ≤ Real.log x :=
    Real.log_nonneg hx
  have hupper : Real.log x ≤ 2 * Real.sqrt x := by
    rw [hlogsplit]
    linarith
  have hfactor := mul_nonneg
    (sub_nonneg.mpr hupper)
    (add_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Real.sqrt_nonneg x))
      hlognonnegative)
  linarith

private theorem exists_saddleSmallRadiusStar_coordinate_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : ℕ,
        8 < Real.log ((d : ℝ) / 2) →
          saddleSmallRadiusVariable ε
            (saddleSmallRadiusStar ε d) ≤
              Real.log ((d : ℝ) / 2) / 8 + C := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_saddleSourceShellDerivative_endpoint_bound
      hε horder
  let C : ℝ := K / 4 * Real.exp (K / 2)
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro d hloglarge
  let ℓ : ℝ := (d : ℝ) / 2
  let m : ℝ := Real.log ℓ / 8
  let q : ℝ := Real.log ℓ / (4 * ℓ)
  let z : ℝ := 2 * K * q
  have hℓnonnegative : 0 ≤ ℓ := by
    try dsimp [ℓ]
    positivity
  have hlogpositive : 0 < Real.log ℓ := by
    try dsimp [ℓ]
    linarith
  have hℓone : 1 < ℓ :=
    (Real.log_pos_iff hℓnonnegative).mp hlogpositive
  have hℓ : 0 < ℓ := by linarith
  have hdreal : 0 < (d : ℝ) := by
    try dsimp [ℓ] at hℓ
    linarith
  have hd : 0 < d := by
    exact_mod_cast hdreal
  have hm : 1 < m := by
    try dsimp [m, ℓ]
    linarith
  have hmpositive : 0 < m := by linarith
  have hqnonnegative : 0 ≤ q := by
    try dsimp [q]
    positivity
  have hlogupper : Real.log ℓ ≤ ℓ := by
    linarith [Real.log_le_sub_one_of_pos hℓ]
  have hqbound : q ≤ 1 / 4 := by
    try dsimp [q]
    apply (div_le_iff₀ (show 0 < 4 * ℓ by positivity)).mpr
    linarith
  have hstar :
      saddleSmallRadiusStarOrdinate ε d = -1 + q := by
    rfl
  have huinterval :
      saddleSmallRadiusStarOrdinate ε d ∈
        Icc (-1 : ℝ) 0 := by
    rw [hstar]
    constructor <;> linarith
  have hshell :
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d) ≤
        K * q := by
    calc
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d) ≤
        |saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d)| :=
          le_abs_self _
      _ ≤ K *
          (saddleSmallRadiusStarOrdinate ε d + 1) :=
        hKbound _ huinterval
      _ = K * q := by
        rw [hstar]
        ring
  have hznonnegative : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hzupper : z ≤ K / 2 := by
    try dsimp [z]
    calc
      2 * K * q ≤ 2 * K * (1 / 4 : ℝ) := by
        gcongr
      _ = K / 2 := by ring
  have hlogquad := saddle_log_sq_le_four_mul hℓone.le
  have hmz : m * z ≤ K / 4 := by
    have hid :
        m * z =
          K * (Real.log ℓ) ^ 2 / (16 * ℓ) := by
      try dsimp [m, z, q]
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀
      (show 0 < 16 * ℓ by positivity)).mpr
    linarith [mul_nonneg hK
      (sub_nonneg.mpr hlogquad)]
  have hexpdifference :
      Real.exp z - 1 ≤ z * Real.exp z := by
    have hsource :=
      abs_exp_sub_one_le_abs_mul_exp_abs z
    rw [abs_of_nonneg
      (sub_nonneg.mpr (by
        simpa only [Real.one_le_exp_iff, Real.exp_zero] using! Real.exp_le_exp.mpr hznonnegative)),
      abs_of_nonneg hznonnegative] at hsource
    exact hsource
  have hproduct :
      m * Real.exp z ≤
        m + K / 4 * Real.exp (K / 2) := by
    have hdifference :=
      mul_le_mul_of_nonneg_left hexpdifference
        hmpositive.le
    have hexpbound :=
      Real.exp_le_exp.mpr hzupper
    have hscaled :
        m * z * Real.exp z ≤
          (K / 4) * Real.exp (K / 2) := by
      exact mul_le_mul hmz hexpbound
        (Real.exp_pos z).le (by positivity)
    linarith
  calc
    saddleSmallRadiusVariable ε
        (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma m +
          2 * (saddleShellDerivativeOne ε +
            saddleSourceShellDerivative ε
              (saddleSmallRadiusStarOrdinate ε d))) := by
        simpa only [m, ℓ] using!
          saddleSmallRadiusVariable_star_eq
            (ε := ε) hd
    _ ≤ Real.exp (Real.log m + z) := by
      apply Real.exp_le_exp.mpr
      have hdigamma := (saddleDigamma_bounds hm).2
      try dsimp [z]
      linarith
    _ = m * Real.exp z := by
      rw [Real.exp_add, Real.exp_log hmpositive]
    _ ≤ m + K / 4 * Real.exp (K / 2) := hproduct
    _ = Real.log ((d : ℝ) / 2) / 8 + C := by
      rfl

private theorem exists_eventually_y_star_le_log_eighth_add
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r →
          r ≤ saddleSmallRadiusStar ε d →
            saddleSmallRadiusVariable ε r ≤
              Real.log ((d : ℝ) / 2) / 8 + C := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_saddleSmallRadiusStar_coordinate_bound
      hε horder
  refine ⟨C, hC, ?_⟩
  have hcast :
      Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge :
      ∀ᶠ d : ℕ in atTop,
        2 * Real.exp 8 < (d : ℝ) :=
    hcast.eventually
      (eventually_gt_atTop (2 * Real.exp 8))
  filter_upwards [hlarge] with d hd
  intro r hr hrstar
  have hℓ : 0 < (d : ℝ) / 2 := by
    have he := Real.exp_pos (8 : ℝ)
    linarith
  have hlog : 8 < Real.log ((d : ℝ) / 2) := by
    apply (Real.lt_log_iff_exp_lt hℓ).mpr
    linarith
  have hstarpositive : 0 < saddleSmallRadiusStar ε d :=
    saddleSmallRadiusStar_pos ε d
  have hsquare :
      r ^ 2 ≤ (saddleSmallRadiusStar ε d) ^ 2 := by
    linarith [mul_nonneg
      (sub_nonneg.mpr hrstar)
      (add_nonneg hstarpositive.le hr)]
  calc
    saddleSmallRadiusVariable ε r ≤
        saddleSmallRadiusVariable ε
          (saddleSmallRadiusStar ε d) := by
      unfold saddleSmallRadiusVariable
      gcongr
    _ ≤ Real.log ((d : ℝ) / 2) / 8 + C :=
      hstar d hlog

private noncomputable def saddleSmallResidueTruncation (ℓ : ℝ) : ℕ :=
  Nat.ceil (20 * Real.log ℓ)

private theorem saddleSmallResidueTruncation_lower
    (ℓ : ℝ) :
    20 * Real.log ℓ ≤
      (saddleSmallResidueTruncation ℓ : ℝ) := by
  exact Nat.le_ceil (20 * Real.log ℓ)

private theorem saddleSmallResidueTruncation_upper
    {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    (saddleSmallResidueTruncation ℓ : ℝ) ≤
      20 * Real.log ℓ + 1 := by
  exact (Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num)
      (Real.log_nonneg hℓ))).le

private theorem tendsto_logLinear_div_atTop :
    Tendsto
      (fun ℓ : ℝ => (20 * Real.log ℓ + 1) / ℓ)
      atTop (𝓝 0) := by
  have hlog : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / ℓ)
      atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hinv : Tendsto
      (fun ℓ : ℝ => (1 : ℝ) / ℓ)
      atTop (𝓝 0) := by
    simpa only [one_div] using!
      (tendsto_inv_atTop_zero :
        Tendsto (fun ℓ : ℝ => ℓ⁻¹)
          atTop (𝓝 0))
  convert! (hlog.const_mul 20).add hinv using 1
  · funext ℓ
    ring
  · norm_num

private theorem tendsto_logLinear_sq_div_atTop :
    Tendsto
      (fun ℓ : ℝ => (20 * Real.log ℓ + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have hlog1 : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / ℓ)
      atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hlog2 : Tendsto
      (fun ℓ : ℝ => Real.log ℓ ^ 2 / ℓ)
      atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 2 (by norm_num : (1 : ℝ) ≠ 0)
  have hinv : Tendsto
      (fun ℓ : ℝ => (1 : ℝ) / ℓ)
      atTop (𝓝 0) := by
    simpa only [one_div] using!
      (tendsto_inv_atTop_zero :
        Tendsto (fun ℓ : ℝ => ℓ⁻¹)
          atTop (𝓝 0))
  convert! ((hlog2.const_mul 400).add
    (hlog1.const_mul 40)).add hinv using 1
  · funext ℓ
    ring
  · norm_num

private theorem tendsto_saddleSmallResidueTruncation_div :
    Tendsto
      (fun ℓ : ℝ =>
        (saddleSmallResidueTruncation ℓ : ℝ) / ℓ)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (f := fun ℓ : ℝ =>
      (saddleSmallResidueTruncation ℓ : ℝ) / ℓ)
    (g := fun ℓ : ℝ => (20 * Real.log ℓ + 1) / ℓ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)]
      with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)]
      with ℓ hℓ
    exact div_le_div_of_nonneg_right
      (saddleSmallResidueTruncation_upper hℓ)
      (by linarith)
  · exact tendsto_logLinear_div_atTop

private theorem tendsto_saddleSmallResidueTruncation_sq_div :
    Tendsto
      (fun ℓ : ℝ =>
        (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (f := fun ℓ : ℝ =>
      (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
    (g := fun ℓ : ℝ =>
      (20 * Real.log ℓ + 1) ^ 2 / ℓ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)]
      with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)]
      with ℓ hℓ
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact (sq_le_sq₀
      (by exact_mod_cast (Nat.zero_le
        (saddleSmallResidueTruncation ℓ)))
      (by linarith [Real.log_nonneg hℓ])).mpr
      (saddleSmallResidueTruncation_upper hℓ)
  · exact tendsto_logLinear_sq_div_atTop

private theorem eventually_saddleSmallResidueTruncation_double_le :
    ∀ᶠ ℓ : ℝ in atTop,
      2 * (saddleSmallResidueTruncation ℓ : ℝ) ≤ ℓ := by
  have hsmall :=
    tendsto_saddleSmallResidueTruncation_div.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall,
    eventually_gt_atTop (0 : ℝ)]
    with ℓ hratio hℓ
  have h := (div_lt_iff₀ hℓ).mp hratio
  linarith

private theorem eventually_saddleSmallResidueTruncation_succ_double_le :
    ∀ᶠ ℓ : ℝ in atTop,
      2 * ((saddleSmallResidueTruncation ℓ + 1 : ℕ) : ℝ) ≤ ℓ := by
  have hsmall :=
    tendsto_saddleSmallResidueTruncation_div.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall,
    eventually_ge_atTop (4 : ℝ)]
    with ℓ hratio hℓ
  have hℓpos : 0 < ℓ := by linarith
  have h := (div_lt_iff₀ hℓpos).mp hratio
  push_cast
  linarith

private theorem eventually_saddleSmallResidueTruncation_dominates_window
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          2 * y ≤
            (saddleSmallResidueTruncation ℓ : ℝ) + 2 := by
  filter_upwards
    [Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max C 0))] with ℓ hlog
  intro y hy hyupper
  have hlogC : C ≤ Real.log ℓ := by
    simpa only [max_eq_left hC] using! hlog
  have hN := saddleSmallResidueTruncation_lower ℓ
  linarith [hlogC]

private theorem saddleExpSeries_term_le_exp_mul_half_pow
    {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    y ^ m / (m.factorial : ℝ) ≤
      Real.exp (2 * y) * (1 / 2 : ℝ) ^ m := by
  have hterm :
      (2 * y) ^ m / (m.factorial : ℝ) ≤
        Real.exp (2 * y) := by
    simpa only [Finset.sum_singleton] using!
      (sum_le_hasSum ({m} : Finset ℕ)
        (fun n hn => by positivity)
        (saddleExpSeries_hasSum (2 * y)))
  have hpower :
      (2 * y) ^ m * (1 / 2 : ℝ) ^ m = y ^ m := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    y ^ m / (m.factorial : ℝ) =
        ((2 * y) ^ m / (m.factorial : ℝ)) *
          (1 / 2 : ℝ) ^ m := by
      rw [div_mul_eq_mul_div, hpower]
    _ ≤ Real.exp (2 * y) * (1 / 2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right hterm (by positivity)

private theorem saddleSmallResidue_half_log_le :
    Real.log (1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 1 / 2)
  linarith

private theorem saddleSmallResidueTruncation_half_pow_le
    (ℓ : ℝ) :
    (1 / 2 : ℝ) ^
        (saddleSmallResidueTruncation ℓ + 1) ≤
      Real.exp (-10 * Real.log ℓ) := by
  let m : ℕ := saddleSmallResidueTruncation ℓ + 1
  have hmlower :
      20 * Real.log ℓ ≤ (m : ℝ) := by
    try dsimp [m]
    push_cast
    linarith [saddleSmallResidueTruncation_lower ℓ]
  have hhalf := saddleSmallResidue_half_log_le
  have hproduct :=
    mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ (m : ℝ) by positivity)
  have hexponent :
      (m : ℝ) * Real.log (1 / 2 : ℝ) ≤
        -10 * Real.log ℓ := by
    linarith
  change (1 / 2 : ℝ) ^ m ≤ _
  calc
    (1 / 2 : ℝ) ^ m =
        Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) := by
      rw [Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ Real.exp (-10 * Real.log ℓ) :=
      Real.exp_le_exp.mpr hexponent

private noncomputable def saddleSmallResidueTailMajorant (C ℓ : ℝ) : ℝ :=
  Real.exp (3 * C - (77 / 8 : ℝ) * Real.log ℓ)

private theorem saddleSmallResidue_tail_le_majorant
    {C ℓ y : ℝ}
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
        (y ^ (saddleSmallResidueTruncation ℓ + 1) /
          ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) ≤
      saddleSmallResidueTailMajorant C ℓ := by
  let m : ℕ := saddleSmallResidueTruncation ℓ + 1
  have hterm := saddleExpSeries_term_le_exp_mul_half_pow
    hy m
  have hgeo := saddleSmallResidueTruncation_half_pow_le ℓ
  change Real.exp y *
      (y ^ m / (m.factorial : ℝ)) ≤ _
  calc
    Real.exp y * (y ^ m / (m.factorial : ℝ)) ≤
        Real.exp y *
          (Real.exp (2 * y) * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
    _ = Real.exp (3 * y) * (1 / 2 : ℝ) ^ m := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp
          (3 * (Real.log ℓ / 8 + C)) *
        Real.exp (-10 * Real.log ℓ) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact hgeo
      · positivity
      · positivity
    _ = saddleSmallResidueTailMajorant C ℓ := by
      rw [← Real.exp_add]
      unfold saddleSmallResidueTailMajorant
      congr 1
      ring

private theorem tendsto_saddleSmallResidueTailMajorant
    (C : ℝ) :
    Tendsto (saddleSmallResidueTailMajorant C)
      atTop (𝓝 0) := by
  have hneg :
      Tendsto
        (fun ℓ : ℝ =>
          (-(77 / 8 : ℝ)) * Real.log ℓ)
        atTop atBot :=
    Real.tendsto_log_atTop.const_mul_atTop_of_neg
      (by norm_num : (-(77 / 8 : ℝ)) < 0)
  have hsmall :=
    (Real.tendsto_exp_atBot.comp hneg).const_mul
      (Real.exp (3 * C))
  convert! hsmall using 1
  · funext ℓ
    unfold saddleSmallResidueTailMajorant
    rw [show
      3 * C - (77 / 8 : ℝ) * Real.log ℓ =
        3 * C + (-(77 / 8 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    rfl
  · simp only [mul_zero]

private noncomputable def saddleSmallResidueCoefficientMajorant
    (K C ℓ : ℝ) : ℝ :=
  K *
    Real.exp
      (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
    (2 * (Real.log ℓ / 8 + C) +
      (Real.log ℓ / 8 + C) ^ 2) *
    Real.exp
      (2 * C - (3 / 4 : ℝ) * Real.log ℓ)

private theorem saddleSmallResidue_coefficient_le_majorant
    {K C ℓ y : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * y + y ^ 2) * Real.exp (2 * y) ≤
      saddleSmallResidueCoefficientMajorant K C ℓ := by
  let Y : ℝ := Real.log ℓ / 8 + C
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hY : 0 ≤ Y := by
    try dsimp [Y]
    exact add_nonneg
      (div_nonneg (Real.log_nonneg hℓ)
        (by norm_num)) hC
  have hpoly : 2 * y + y ^ 2 ≤ 2 * Y + Y ^ 2 := by
    have hproduct : 0 ≤ (Y - y) * (Y + y) :=
      mul_nonneg (sub_nonneg.mpr hyupper)
        (add_nonneg hY hy)
    nlinarith
  have hrat :
      Real.exp (2 * Y) / ℓ =
        Real.exp (2 * C - (3 / 4 : ℝ) * Real.log ℓ) := by
    calc
      Real.exp (2 * Y) / ℓ =
          Real.exp (2 * Y) / Real.exp (Real.log ℓ) := by
        rw [Real.exp_log hℓpos]
      _ = Real.exp (2 * Y - Real.log ℓ) := by
        rw [Real.exp_sub]
      _ = Real.exp
          (2 * C - (3 / 4 : ℝ) * Real.log ℓ) := by
        congr 1
        try dsimp [Y]
        ring
  calc
    (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * y + y ^ 2) * Real.exp (2 * y) ≤
      (K / ℓ) *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * Y + Y ^ 2) * Real.exp (2 * Y) := by
      gcongr
    _ = K *
        Real.exp
          (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
        (2 * Y + Y ^ 2) *
          (Real.exp (2 * Y) / ℓ) := by
      ring
    _ = saddleSmallResidueCoefficientMajorant K C ℓ := by
      rw [hrat]
      rfl

private theorem tendsto_saddleLogWindowPolynomial_exp_neg
    (C : ℝ) :
    Tendsto
      (fun t : ℝ =>
        (2 * (t / 8 + C) + (t / 8 + C) ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * t))
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun t : ℝ => (3 / 4 : ℝ) * t)
        atTop atTop :=
    tendsto_id.const_mul_atTop
      (by norm_num : (0 : ℝ) < 3 / 4)
  have h2base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      hscale
  have h2 :
      Tendsto
        (fun t : ℝ =>
          t ^ 2 * Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h2base.const_mul ((4 / 3 : ℝ) ^ 2)
      using 1
    · funext t
      try dsimp
      have ha :
          -((3 / 4 : ℝ) * t) =
            (-(3 / 4 : ℝ)) * t := by ring
      rw [ha]
      ring
    · norm_num
  have h1base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      hscale
  have h1 :
      Tendsto
        (fun t : ℝ =>
          t * Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h1base.const_mul (4 / 3 : ℝ)
      using 1
    · funext t
      try dsimp
      have ha :
          -((3 / 4 : ℝ) * t) =
            (-(3 / 4 : ℝ)) * t := by ring
      rw [ha]
      ring
    · norm_num
  have h0 :
      Tendsto
        (fun t : ℝ =>
          Real.exp (-(3 / 4 : ℝ) * t))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using!
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg
          (by norm_num : (-(3 / 4 : ℝ)) < 0)))
  have hpoly :=
    ((h2.const_mul (1 / 64 : ℝ)).add
      (h1.const_mul (C / 4 + 1 / 4))).add
        (h0.const_mul (C ^ 2 + 2 * C))
  convert! hpoly using 1
  · funext t
    ring
  · norm_num

private theorem tendsto_saddleSmallResidueCoefficientMajorant
    (K C : ℝ) :
    Tendsto (saddleSmallResidueCoefficientMajorant K C)
      atTop (𝓝 0) := by
  have hscaled :
      Tendsto
        (fun ℓ : ℝ =>
          K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
        atTop (𝓝 0) := by
    convert! tendsto_saddleSmallResidueTruncation_sq_div.const_mul K
      using 1
    · funext ℓ
      ring
    · norm_num
  have hfactor :
      Tendsto
        (fun ℓ : ℝ =>
          Real.exp
            (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ))
        atTop (𝓝 1) := by
    simpa only [Real.exp_zero] using! hscaled.rexp
  have hwindow :=
    (tendsto_saddleLogWindowPolynomial_exp_neg C).comp
      Real.tendsto_log_atTop
  have hwindowScaled := hwindow.const_mul
    (Real.exp (2 * C))
  have htotal :=
    (hfactor.const_mul K).mul hwindowScaled
  convert! htotal using 1
  · funext ℓ
    unfold saddleSmallResidueCoefficientMajorant
    rw [show
      2 * C - (3 / 4 : ℝ) * Real.log ℓ =
        2 * C + (-(3 / 4 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    simp only [Function.comp_apply]
    ring
  · norm_num

private noncomputable def saddleSmallResidueRelativeErrorMajorant
    (K C ℓ : ℝ) : ℝ :=
  saddleSmallResidueCoefficientMajorant K C ℓ +
    2 * saddleSmallResidueTailMajorant C ℓ

private theorem tendsto_saddleSmallResidueRelativeErrorMajorant
    (K C : ℝ) :
    Tendsto (saddleSmallResidueRelativeErrorMajorant K C)
      atTop (𝓝 0) := by
  have h :=
    (tendsto_saddleSmallResidueCoefficientMajorant K C).add
      ((tendsto_saddleSmallResidueTailMajorant C).const_mul 2)
  simpa only [mul_zero, add_zero] using! h

private theorem eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by
  obtain ⟨K, hK, hfinite⟩ :=
    exists_plusSaddleSmallRadius_relativeFiniteResidue_error
      hε horder
  have hmajor :=
    (tendsto_saddleSmallResidueRelativeErrorMajorant K C).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards
    [hmajor,
      eventually_saddleSmallResidueTruncation_double_le,
      eventually_saddleSmallResidueTruncation_dominates_window hC,
      eventually_ge_atTop (1 : ℝ)]
    with ℓ hsmall hN hwindow hℓ
  intro y hy hyupper
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hratio := hwindow y hy hyupper
  have hbound := hfinite ℓ hℓpos
    (saddleSmallResidueTruncation ℓ) hN y hy hratio
  have hcoeff := saddleSmallResidue_coefficient_le_majorant
    hK hC hℓ hy hyupper
  have htail := saddleSmallResidue_tail_le_majorant
    hy hyupper
  have htailtwo :
      2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) ≤
        2 * saddleSmallResidueTailMajorant C ℓ := by
    calc
      2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) =
        2 * (Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ))) := by
        ring
      _ ≤ 2 * saddleSmallResidueTailMajorant C ℓ :=
        mul_le_mul_of_nonneg_left htail
          (by norm_num : (0 : ℝ) ≤ 2)
  calc
    Real.exp y *
        |(∑ n ∈ Finset.range
            (saddleSmallResidueTruncation ℓ + 1),
          ((-y) ^ n / (n.factorial : ℝ)) *
            plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-y)| ≤
      (K / ℓ) *
          Real.exp
            (K * (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ) *
          (2 * y + y ^ 2) * Real.exp (2 * y) +
        2 * Real.exp y *
          (y ^ (saddleSmallResidueTruncation ℓ + 1) /
            ((saddleSmallResidueTruncation ℓ + 1).factorial : ℝ)) :=
      hbound
    _ ≤ saddleSmallResidueCoefficientMajorant K C ℓ +
          2 * saddleSmallResidueTailMajorant C ℓ := by
      exact add_le_add hcoeff htailtwo
    _ < 1 / 2 := by
      exact hsmall

/-- The saddle residue dimension is asymptotic to half the ambient dimension. -/
public
theorem tendsto_saddleResidue_dimension_half :
    Tendsto
      (fun d : ℕ => (d : ℝ) / 2)
      atTop atTop := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hmul := hcast.atTop_mul_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  convert! hmul using 1
  funext d
  ring

private theorem eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ,
        0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          let ℓ : ℝ := (d : ℝ) / 2
          let y : ℝ := saddleSmallRadiusVariable ε r
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_eventually_y_star_le_log_eighth_add hε horder
  have hrelative :=
    eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
      hε horder hC
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hrelative
  filter_upwards [hdimension, hstar]
    with d hres hcut
  intro r hr hrstar
  try dsimp
  exact hres (saddleSmallRadiusVariable ε r)
    (saddleSmallRadiusVariable_nonneg ε r)
    (hcut r hr hrstar)

end

section

open Filter Set MeasureTheory
open scoped Topology BigOperators

private theorem gamma_half_factorial_lower (N : ℕ) :
    Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ) ≤
      Real.Gamma ((N : ℝ) + 3 / 2) := by
  induction N with
  | zero => simp only [Nat.factorial_zero, Nat.cast_one, mul_one, CharP.cast_eq_zero, zero_add,
    Std.le_refl]
  | succ N ih =>
    have hq : 0 < (N : ℝ) + 3 / 2 := by positivity
    have hrec :
        Real.Gamma (((N + 1 : ℕ) : ℝ) + 3 / 2) =
          ((N : ℝ) + 3 / 2) *
            Real.Gamma ((N : ℝ) + 3 / 2) := by
      convert! Real.Gamma_add_one hq.ne' using 1
      all_goals
        push_cast
        ring_nf
    calc
      Real.Gamma (3 / 2 : ℝ) *
          (((N + 1).factorial : ℕ) : ℝ) =
        ((N : ℝ) + 1) *
          (Real.Gamma (3 / 2 : ℝ) *
            (N.factorial : ℝ)) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ((N : ℝ) + 1) *
          Real.Gamma ((N : ℝ) + 3 / 2) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((N : ℝ) + 3 / 2) *
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        apply mul_le_mul_of_nonneg_right
          (by norm_num : (N : ℝ) + 1 ≤ (N : ℝ) + 3 / 2)
          (Real.Gamma_pos_of_pos hq).le
      _ = Real.Gamma (((N + 1 : ℕ) : ℝ) + 3 / 2) :=
        hrec.symm

private theorem saddleNegativeTruncation_half_pow_le (ℓ : ℝ) :
    (1 / 2 : ℝ) ^ saddleSmallResidueTruncation ℓ ≤
      2 * Real.exp (-10 * Real.log ℓ) := by
  have hnext := saddleSmallResidueTruncation_half_pow_le ℓ
  calc
    (1 / 2 : ℝ) ^ saddleSmallResidueTruncation ℓ =
      2 * (1 / 2 : ℝ) ^
        (saddleSmallResidueTruncation ℓ + 1) := by
          rw [pow_succ]
          ring
    _ ≤ 2 * Real.exp (-10 * Real.log ℓ) :=
      mul_le_mul_of_nonneg_left hnext (by norm_num)

private theorem saddleNegative_factorialTail_le_majorant
    {C ℓ y : ℝ}
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
      (y ^ saddleSmallResidueTruncation ℓ /
        ((saddleSmallResidueTruncation ℓ).factorial : ℝ)) ≤
      2 * saddleSmallResidueTailMajorant C ℓ := by
  let N : ℕ := saddleSmallResidueTruncation ℓ
  have hterm := saddleExpSeries_term_le_exp_mul_half_pow hy N
  have hgeo := saddleNegativeTruncation_half_pow_le ℓ
  change Real.exp y * (y ^ N / (N.factorial : ℝ)) ≤ _
  calc
    Real.exp y * (y ^ N / (N.factorial : ℝ)) ≤
      Real.exp y *
        (Real.exp (2 * y) * (1 / 2 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
    _ = Real.exp (3 * y) * (1 / 2 : ℝ) ^ N := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ Real.exp (3 * (Real.log ℓ / 8 + C)) *
        (2 * Real.exp (-10 * Real.log ℓ)) := by
      apply mul_le_mul
      · exact Real.exp_le_exp.mpr (by linarith)
      · exact hgeo
      · positivity
      · positivity
    _ = 2 * saddleSmallResidueTailMajorant C ℓ := by
      unfold saddleSmallResidueTailMajorant
      calc
        Real.exp (3 * (Real.log ℓ / 8 + C)) *
            (2 * Real.exp (-10 * Real.log ℓ)) =
          2 *
            (Real.exp (3 * (Real.log ℓ / 8 + C)) *
              Real.exp (-10 * Real.log ℓ)) := by ring
        _ = 2 *
            Real.exp
              (3 * (Real.log ℓ / 8 + C) +
                (-10 * Real.log ℓ)) := by
          rw [← Real.exp_add]
        _ = 2 *
            Real.exp
              (3 * C - (77 / 8 : ℝ) * Real.log ℓ) := by
          congr 2
          ring

private theorem saddleNegative_sqrt_le_one_add
    {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y ≤ 1 + y := by
  have hs := Real.sqrt_nonneg y
  have hsq := Real.sq_sqrt hy
  linarith [sq_nonneg (Real.sqrt y - 1)]

private noncomputable def saddleNegativeRelativeGammaTailMajorant
    (C K Kε ℓ : ℝ) : ℝ :=
  (2 * Kε / Real.Gamma (3 / 2 : ℝ)) *
    (1 + (Real.log ℓ / 8 + C)) *
      saddleSmallResidueTailMajorant C ℓ *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)

private theorem saddleNegative_relativeGammaTail_le_majorant
    {C K Kε ℓ y : ℝ}
    (hKε : 0 ≤ Kε)
    (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y)
    (hyupper : y ≤ Real.log ℓ / 8 + C) :
    Real.exp y *
      (Kε * Real.sqrt y *
          y ^ saddleSmallResidueTruncation ℓ /
            Real.Gamma
              ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
        Real.exp
          (K *
            (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
              ℓ)) ≤
      saddleNegativeRelativeGammaTailMajorant C K Kε ℓ := by
  let N : ℕ := saddleSmallResidueTruncation ℓ
  let Y : ℝ := Real.log ℓ / 8 + C
  have hY : 0 ≤ Y := by
    try dsimp [Y]
    exact add_nonneg
      (div_nonneg (Real.log_nonneg hℓ) (by norm_num)) hC
  have hΓ : 0 < Real.Gamma (3 / 2 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have hfactorial : 0 < (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hq : 0 < Real.Gamma ((N : ℝ) + 3 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hfrac :
      y ^ N / Real.Gamma ((N : ℝ) + 3 / 2) ≤
        (y ^ N / (N.factorial : ℝ)) /
          Real.Gamma (3 / 2 : ℝ) := by
    calc
      y ^ N / Real.Gamma ((N : ℝ) + 3 / 2) ≤
          y ^ N /
            (Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg hy N)
          (mul_pos hΓ hfactorial)
          (gamma_half_factorial_lower N)
      _ = (y ^ N / (N.factorial : ℝ)) /
          Real.Gamma (3 / 2 : ℝ) := by
        field_simp [hΓ.ne', hfactorial.ne']
  have hsqrt := saddleNegative_sqrt_le_one_add hy
  have hsqrtY : Real.sqrt y ≤ 1 + Y := by
    calc
      Real.sqrt y ≤ 1 + y := hsqrt
      _ ≤ 1 + Y := by dsimp [Y]; linarith
  have htail :=
    saddleNegative_factorialTail_le_majorant hy hyupper
  have hbase : 0 ≤ y ^ N / (N.factorial : ℝ) := by
    positivity
  have hmajor : 0 ≤ saddleSmallResidueTailMajorant C ℓ := by
    unfold saddleSmallResidueTailMajorant
    positivity
  let E : ℝ := Real.exp
    (K * (2 * (N : ℝ) + 1) ^ 2 / ℓ)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  change Real.exp y *
    (Kε * Real.sqrt y * y ^ N /
      Real.Gamma ((N : ℝ) + 3 / 2) * E) ≤ _
  calc
    Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) * E) =
      Kε * Real.sqrt y *
        (Real.exp y *
          (y ^ N / Real.Gamma ((N : ℝ) + 3 / 2))) * E := by
      ring
    _ ≤ Kε * Real.sqrt y *
        (Real.exp y *
          ((y ^ N / (N.factorial : ℝ)) /
            Real.Gamma (3 / 2 : ℝ))) * E := by
      gcongr
    _ = (Kε / Real.Gamma (3 / 2 : ℝ)) *
        Real.sqrt y *
          (Real.exp y * (y ^ N / (N.factorial : ℝ))) * E := by
      ring
    _ ≤ (Kε / Real.Gamma (3 / 2 : ℝ)) *
        (1 + Y) *
          (2 * saddleSmallResidueTailMajorant C ℓ) * E := by
      gcongr
    _ = saddleNegativeRelativeGammaTailMajorant C K Kε ℓ := by
      unfold saddleNegativeRelativeGammaTailMajorant
      try dsimp [N, Y, E]
      ring

private theorem tendsto_saddleNegativeTruncation_odd_sq_div :
    Tendsto
      (fun ℓ : ℝ =>
        (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  have hinv : Tendsto
      (fun ℓ : ℝ => (1 : ℝ) / ℓ)
      atTop (𝓝 0) := by
    simpa only [one_div] using!
      (tendsto_inv_atTop_zero :
        Tendsto (fun ℓ : ℝ => ℓ⁻¹) atTop (𝓝 0))
  have h :=
    ((tendsto_saddleSmallResidueTruncation_sq_div.const_mul 4).add
      (tendsto_saddleSmallResidueTruncation_div.const_mul 4)).add
        hinv
  convert! h using 1
  · funext ℓ
    ring
  · norm_num

private theorem tendsto_saddleNegativeLogWindowTailMajorant
    (C : ℝ) :
    Tendsto
      (fun ℓ : ℝ =>
        (1 + (Real.log ℓ / 8 + C)) *
          saddleSmallResidueTailMajorant C ℓ)
      atTop (𝓝 0) := by
  have hscale :
      Tendsto
        (fun t : ℝ => (77 / 8 : ℝ) * t)
        atTop atTop :=
    tendsto_id.const_mul_atTop
      (by norm_num : (0 : ℝ) < 77 / 8)
  have h1base :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      hscale
  have h1 :
      Tendsto
        (fun t : ℝ =>
          t * Real.exp (-(77 / 8 : ℝ) * t))
        atTop (𝓝 0) := by
    convert! h1base.const_mul (8 / 77 : ℝ) using 1
    · funext t
      try dsimp
      ring_nf
    · norm_num
  have h0 :
      Tendsto
        (fun t : ℝ => Real.exp (-(77 / 8 : ℝ) * t))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply] using!
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg
          (by norm_num : (-(77 / 8 : ℝ)) < 0)))
  have hpoly :=
    (h1.const_mul (1 / 8 : ℝ)).add
      (h0.const_mul (1 + C))
  have hlog := hpoly.comp Real.tendsto_log_atTop
  have hscaled := hlog.const_mul (Real.exp (3 * C))
  convert! hscaled using 1
  · funext ℓ
    unfold saddleSmallResidueTailMajorant
    rw [show
      3 * C - (77 / 8 : ℝ) * Real.log ℓ =
        3 * C + (-(77 / 8 : ℝ)) * Real.log ℓ by ring,
      Real.exp_add]
    simp only [Function.comp_apply]
    ring
  · norm_num

private theorem tendsto_saddleNegativeRelativeGammaTailMajorant
    (C K Kε : ℝ) :
    Tendsto (saddleNegativeRelativeGammaTailMajorant C K Kε)
      atTop (𝓝 0) := by
  have hsmall :=
    tendsto_saddleNegativeLogWindowTailMajorant C
  have herror :=
    (tendsto_saddleNegativeTruncation_odd_sq_div.const_mul K).rexp
  have htotal :=
    (hsmall.const_mul
      (2 * Kε / Real.Gamma (3 / 2 : ℝ))).mul herror
  convert! htotal using 1
  · funext ℓ
    unfold saddleNegativeRelativeGammaTailMajorant
    ring_nf
  · norm_num

private theorem eventually_saddleNegative_relativeGammaTail_lt_half
    {ε : ℝ} (hε : 0 < ε)
    (C K Kε : ℝ)
    (hC : 0 ≤ C)
    (hK : 0 ≤ K)
    (hKε : 0 ≤ Kε) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            (Kε * Real.sqrt y *
              y ^ saddleSmallResidueTruncation ℓ /
                Real.Gamma
                  ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
              Real.exp
                (K *
                  (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
                    ℓ)) < 1 / 2 := by
  have _hε : 0 < ε := hε
  have _hK : 0 ≤ K := hK
  have hmajor :=
    (tendsto_saddleNegativeRelativeGammaTailMajorant C K Kε).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hmajor, eventually_ge_atTop (1 : ℝ)]
    with ℓ hsmall hℓ
  intro y hy hyupper
  exact (saddleNegative_relativeGammaTail_le_majorant
    hKε hC hℓ hy hyupper).trans_lt hsmall

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private noncomputable def upperCosLaplaceKernel (c T a : ℝ) : ℝ :=
  (1 - Real.cos (a * T)) * Real.exp (-c * a) / a

private theorem upperCosLaplaceKernel_eq_frullani_re
    (c T a : ℝ) :
    upperCosLaplaceKernel c T a =
      (complexFrullaniKernel (c : ℂ)
        ((c : ℂ) + Complex.I * (T : ℂ)) a).re := by
  simp only [upperCosLaplaceKernel, neg_mul, complexFrullaniKernel, neg_add_rev,
    Complex.div_ofReal_re,
    Complex.sub_re, Complex.exp_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero,
    sub_zero, Complex.neg_im, Complex.mul_im, zero_mul, add_zero, neg_zero, Real.cos_zero,
      mul_one, Complex.add_re,
    Complex.I_re, Complex.I_im, sub_self, zero_add, Complex.add_im, one_mul, Real.cos_neg]
  ring_nf

private theorem upperCosLaplaceKernel_integrable
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCosLaplaceKernel c T) (Ioi 0) := by
  have hw : 0 < ((c : ℂ) + Complex.I * (T : ℂ)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, add_zero] using! hc
  have h := complexFrullaniKernel_integrable (z := (c : ℂ))
    (w := (c : ℂ) + Complex.I * (T : ℂ)) (by simpa only [Complex.ofReal_re] using! hc) hw
  have hr := h.re
  exact hr.congr (Filter.Eventually.of_forall
    (fun a => (upperCosLaplaceKernel_eq_frullani_re c T a).symm))

private theorem integral_upperCosLaplaceKernel
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) =
      Real.log
        (‖((c : ℂ) + Complex.I * (T : ℂ))‖ / c) := by
  let z : ℂ := (c : ℂ)
  let w : ℂ := (c : ℂ) + Complex.I * (T : ℂ)
  have hz : 0 < z.re := by simpa only [Complex.ofReal_re] using! hc
  have hw : 0 < w.re := by simpa [w] using! hc
  have hi := complexFrullaniKernel_integrable hz hw
  calc
    (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) =
        ∫ a : ℝ in Ioi 0, (complexFrullaniKernel z w a).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperCosLaplaceKernel_eq_frullani_re c T a
    _ = (∫ a : ℝ in Ioi 0, complexFrullaniKernel z w a).re :=
      integral_re hi
    _ = (Complex.log w - Complex.log z).re := by
      rw [integral_complexFrullaniKernel hz hw]
    _ = Real.log (‖((c : ℂ) + Complex.I * (T : ℂ))‖ / c) := by
      rw [Complex.sub_re, Complex.log_re, Complex.log_re,
        Real.log_div]
      · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, w, z]
      · exact (norm_pos_iff.mpr (ne_of_apply_ne Complex.re
          (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            zero_mul, Complex.I_im,
                Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.zero_re,
                  ne_eq] using! hc.ne'))).ne'
      · exact hc.ne'

private noncomputable def upperGammaTruncatedDampingIntegrand
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  upperCosLaplaceKernel η T a *
    ∑ k ∈ Finset.range (n + 1),
      Real.exp (-(2 * a / ℓ)) ^ k

private theorem upperGammaTruncatedDampingIntegrand_eq_sum
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaTruncatedDampingIntegrand ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCosLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  classical
  unfold upperGammaTruncatedDampingIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he :
      Real.exp (-η * a) *
          Real.exp (-(2 * a / ℓ)) ^ k =
        Real.exp (-(η + 2 * (k : ℝ) / ℓ) * a) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  unfold upperCosLaplaceKernel
  calc
    ((1 - Real.cos (a * T)) * Real.exp (-η * a) / a) *
        Real.exp (-(2 * a / ℓ)) ^ k =
      (1 - Real.cos (a * T)) *
        (Real.exp (-η * a) *
          Real.exp (-(2 * a / ℓ)) ^ k) / a := by
          ring
    _ = (1 - Real.cos (a * T)) *
        Real.exp (-(η + 2 * (k : ℝ) / ℓ) * a) / a := by
          rw [he]

private theorem upperGammaGeometricLimit_eq_integrand
    (ℓ η T a : ℝ) :
    upperCosLaplaceKernel η T a *
        (1 - Real.exp (-(2 * a / ℓ)))⁻¹ =
      upperGammaDampingIntegrand ℓ η T a := by
  simp only [upperCosLaplaceKernel, mul_comm, mul_neg, div_eq_mul_inv, mul_left_comm, mul_assoc,
    upperGammaDampingIntegrand, upperGammaMeasureDensity, mul_inv_rev]

private theorem tendsto_integral_upperGammaTruncatedDampingIntegrand
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a)
      atTop (𝓝 (upperGammaDamping ℓ η T)) := by
  unfold upperGammaDamping
  refine tendsto_integral_of_dominated_convergence
    (upperGammaDampingIntegrand ℓ η T) ?_
    (upperGammaDampingIntegrand_integrable hℓ hη T) ?_ ?_
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold upperGammaTruncatedDampingIntegrand
      upperCosLaplaceKernel
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hbase : 0 ≤ upperCosLaplaceKernel η T a := by
      unfold upperCosLaplaceKernel
      exact div_nonneg
        (mul_nonneg
          (sub_nonneg.mpr (Real.cos_le_one _))
          (Real.exp_pos _).le) ha.le
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          Real.exp (-(2 * a / ℓ)) ^ k) ≤
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ := by
      exact sum_le_hasSum (Finset.range (n + 1))
        (fun k hk => pow_nonneg hq0 k)
        (hasSum_geometric_of_lt_one hq0 hq1)
    have hpartial : 0 ≤
        upperGammaTruncatedDampingIntegrand ℓ η T n a := by
      unfold upperGammaTruncatedDampingIntegrand
      exact mul_nonneg hbase
        (Finset.sum_nonneg (fun k hk => pow_nonneg hq0 k))
    rw [Real.norm_eq_abs, abs_of_nonneg hpartial]
    calc
      upperGammaTruncatedDampingIntegrand ℓ η T n a =
          upperCosLaplaceKernel η T a *
            ∑ k ∈ Finset.range (n + 1),
              Real.exp (-(2 * a / ℓ)) ^ k := rfl
      _ ≤ upperCosLaplaceKernel η T a *
          (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hbase
      _ = upperGammaDampingIntegrand ℓ η T a :=
        upperGammaGeometricLimit_eq_integrand ℓ η T a
  · filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    have hq0 : 0 ≤ Real.exp (-(2 * a / ℓ)) :=
      (Real.exp_pos _).le
    have hq1 : Real.exp (-(2 * a / ℓ)) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have : 0 < 2 * a / ℓ :=
        div_pos (mul_pos (by norm_num) ha) hℓ
      linarith
    have hgeo :=
      (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
    have hshift := hgeo.comp (tendsto_add_atTop_nat 1)
    have hlimit :=
      Filter.Tendsto.mul
        (tendsto_const_nhds
          (x := upperCosLaplaceKernel η T a)) hshift
    simpa only [upperGammaTruncatedDampingIntegrand, Function.comp_apply,
      upperGammaGeometricLimit_eq_integrand] using! hlimit

private theorem upperGammaLaplaceRate_pos
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (k : ℕ) :
    0 < η + 2 * (k : ℝ) / ℓ := by
  exact add_pos_of_pos_of_nonneg hη
    (div_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hℓ.le)

private theorem integral_upperGammaTruncatedDampingIntegrand
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaTruncatedDampingIntegrand ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                Complex.I * (T : ℂ)‖ /
            (η + 2 * (k : ℝ) / ℓ)) := by
  classical
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaTruncatedDampingIntegrand ℓ η T n a) =
        ∫ a : ℝ in Ioi 0,
          ∑ k ∈ Finset.range (n + 1),
            upperCosLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperGammaTruncatedDampingIntegrand_eq_sum
        ℓ η T n a
    _ = ∑ k ∈ Finset.range (n + 1),
          ∫ a : ℝ in Ioi 0,
            upperCosLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply integral_finsetSum
      intro k hk
      exact upperCosLaplaceKernel_integrable
        (upperGammaLaplaceRate_pos hℓ hη k) T
    _ = ∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                Complex.I * (T : ℂ)‖ /
            (η + 2 * (k : ℝ) / ℓ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_upperCosLaplaceKernel
        (upperGammaLaplaceRate_pos hℓ hη k) T

private theorem upperComplex_norm_ratio_scale
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (T : ℝ) :
    ‖((s * c : ℝ) : ℂ) +
        Complex.I * ((s * T : ℝ) : ℂ)‖ / (s * c) =
      ‖(c : ℂ) + Complex.I * (T : ℂ)‖ / c := by
  have he :
      ((s * c : ℝ) : ℂ) +
          Complex.I * ((s * T : ℝ) : ℂ) =
        (s : ℂ) * ((c : ℂ) + Complex.I * (T : ℂ)) := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_of_nonneg hs.le]
  field_simp [hs.ne', hc.ne']

private theorem upperGammaLaplaceRate_log_ratio
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (k : ℕ) :
    Real.log
        (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
            Complex.I * (T : ℂ)‖ /
          (η + 2 * (k : ℝ) / ℓ)) =
      Real.log
        (‖((ℓ * η / 2 : ℝ) : ℂ) +
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
              (k : ℂ)‖ /
          (ℓ * η / 2 + (k : ℝ))) := by
  have hs : 0 < ℓ / 2 := by positivity
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hreal :
      ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) =
        ℓ * η / 2 + (k : ℝ) := by
    field_simp [hℓ.ne']
  have himag : ℓ / 2 * T = ℓ * T / 2 := by
    ring
  have harg :
      (((ℓ * η / 2 + (k : ℝ) : ℝ) : ℂ) +
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) =
        ((ℓ * η / 2 : ℝ) : ℂ) +
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) +
            (k : ℂ) := by
    push_cast
    ring
  have hscale := upperComplex_norm_ratio_scale
    (s := ℓ / 2)
    (c := η + 2 * (k : ℝ) / ℓ) hs hc T
  rw [hreal, himag, harg] at hscale
  exact congrArg Real.log hscale.symm

private theorem upperGammaEuler_real_factor_norm
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    ‖(m : ℂ) + (k : ℂ)‖ = m + (k : ℝ) := by
  have hp : 0 ≤ m + (k : ℝ) := by positivity
  convert! Complex.norm_of_nonneg hp using 1;
    push_cast; ring

private theorem upperGammaEuler_complex_factor_pos
    {m : ℝ} (hm : 0 < m) (b : ℝ) (k : ℕ) :
    0 < ‖(m : ℂ) + Complex.I * (b : ℂ) + (k : ℂ)‖ := by
  apply norm_pos_iff.mpr
  apply ne_of_apply_ne Complex.re
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
    Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.natCast_re, Complex.zero_re, ne_eq]
  exact (add_pos_of_pos_of_nonneg hm (Nat.cast_nonneg k)).ne'

private theorem upperGammaEuler_log_norm_ratio
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Real.log
      (‖Complex.GammaSeq
          ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
        ‖Complex.GammaSeq (m : ℂ) n‖) =
      -(∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖(m : ℂ) + Complex.I * (b : ℂ) + (k : ℂ)‖ /
            (m + (k : ℝ)))) := by
  classical
  let z : ℂ := (m : ℂ) + Complex.I * (b : ℂ)
  have hpow : ‖(n : ℂ) ^ z‖ = ‖(n : ℂ) ^ (m : ℂ)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast_cpow_of_pos hn]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, z]
  have hpown : ‖(n : ℂ) ^ (m : ℂ)‖ ≠ 0 :=
    (Complex.norm_natCast_cpow_pos_of_pos hn (m : ℂ)).ne'
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hreal (k : ℕ) : 0 < m + (k : ℝ) := by
    positivity
  have hcomplex (k : ℕ) : 0 < ‖z + (k : ℂ)‖ := by
    simpa only [norm_pos_iff, ne_eq] using! upperGammaEuler_complex_factor_pos hm b k
  have hprodreal :
      (∏ k ∈ Finset.range (n + 1),
        (m + (k : ℝ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun k hk => (hreal k).ne')
  have hprodcomplex :
      (∏ k ∈ Finset.range (n + 1),
        ‖z + (k : ℂ)‖) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun k hk => (hcomplex k).ne')
  have hratio :
      ‖Complex.GammaSeq z n‖ /
          ‖Complex.GammaSeq (m : ℂ) n‖ =
        (∏ k ∈ Finset.range (n + 1),
          (‖z + (k : ℂ)‖ / (m + (k : ℝ))))⁻¹ := by
    rw [Complex.GammaSeq, Complex.GammaSeq,
      norm_div, norm_div, norm_mul, norm_mul,
      norm_prod, norm_prod, hpow]
    simp_rw [upperGammaEuler_real_factor_norm hm]
    rw [Finset.prod_div_distrib]
    simp only [norm_natCast]
    field_simp [hpown, hfactorial, hprodreal, hprodcomplex]
  change Real.log (‖Complex.GammaSeq z n‖ /
      ‖Complex.GammaSeq (m : ℂ) n‖) = _
  rw [hratio, Real.log_inv, Real.log_prod]
  intro k hk
  exact div_ne_zero (hcomplex k).ne' (hreal k).ne'

private theorem tendsto_upperGammaEuler_log_norm_ratio
    {m : ℝ} (hm : 0 < m) (b : ℝ) :
    Tendsto
      (fun n : ℕ =>
        Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖))
      atTop
      (𝓝
        (Real.log
          (‖Complex.Gamma
              ((m : ℂ) + Complex.I * (b : ℂ))‖ /
            ‖Complex.Gamma (m : ℂ)‖))) := by
  let z : ℂ := (m : ℂ) + Complex.I * (b : ℂ)
  have hzre : 0 < z.re := by simpa [z] using! hm
  have hnum : ‖Complex.Gamma z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos hzre)
  have hden : ‖Complex.Gamma (m : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos
        (by simpa only [Complex.ofReal_re] using! hm))
  have hratio :=
    (Complex.GammaSeq_tendsto_Gamma z).norm.div
      (Complex.GammaSeq_tendsto_Gamma (m : ℂ)).norm
      hden
  exact hratio.log (div_ne_zero hnum hden)

private theorem upperGammaPositiveShifted_log_norm_eq_neg_damping
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Real.log
        (‖Complex.Gamma
            (((ℓ * η / 2 : ℝ) : ℂ) +
              Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ /
          Real.Gamma (ℓ * η / 2)) =
      -upperGammaDamping ℓ η T := by
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hfinite :
      (fun n : ℕ =>
        Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖)) =ᶠ[atTop]
      (fun n : ℕ =>
        -(∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    calc
      Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖) =
          -(∑ k ∈ Finset.range (n + 1),
            Real.log
              (‖(m : ℂ) + Complex.I * (b : ℂ) +
                    (k : ℂ)‖ /
                (m + (k : ℝ)))) :=
        upperGammaEuler_log_norm_ratio hm b hn
      _ = -(∑ k ∈ Finset.range (n + 1),
            Real.log
              (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                  Complex.I * (T : ℂ)‖ /
                (η + 2 * (k : ℝ) / ℓ))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_add,
          Complex.ofReal_natCast, m, b] using!
          (upperGammaLaplaceRate_log_ratio hℓ hη T k).symm
      _ = -(∫ a : ℝ in Ioi 0,
          upperGammaTruncatedDampingIntegrand ℓ η T n a) := by
        rw [integral_upperGammaTruncatedDampingIntegrand
          hℓ hη T n]
  have hlog := tendsto_upperGammaEuler_log_norm_ratio hm b
  have hdamping :=
    tendsto_integral_upperGammaTruncatedDampingIntegrand
      hℓ hη T
  have hmatch :=
    Filter.Tendsto.congr' hfinite.symm hdamping.neg
  have hidentity := tendsto_nhds_unique hlog hmatch
  have hdennorm :
      ‖Complex.Gamma (m : ℂ)‖ = Real.Gamma m := by
    rw [Complex.Gamma_ofReal]
    exact Complex.norm_of_nonneg
      (Real.Gamma_pos_of_pos hm).le
  rw [hdennorm] at hidentity
  change Real.log
    (‖Complex.Gamma
        ((m : ℂ) + Complex.I * (b : ℂ))‖ /
      Real.Gamma m) = -upperGammaDamping ℓ η T
  exact hidentity

private theorem upperGammaShifted_log_norm_eq_neg_damping
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Real.log
        (‖Complex.Gamma
            (((ℓ * η / 2 : ℝ) : ℂ) -
              Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ /
          Real.Gamma (ℓ * η / 2)) =
      -upperGammaDamping ℓ η T := by
  have hconj :
      ‖Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ =
      ‖Complex.Gamma
          (((ℓ * η / 2 : ℝ) : ℂ) +
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ := by
    have harg (m b : ℝ) :
        starRingEnd ℂ
          ((m : ℂ) + Complex.I * (b : ℂ)) =
          ((m : ℂ) - Complex.I * (b : ℂ)) := by
      simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, neg_mul, sub_eq_add_neg]
    rw [← harg (ℓ * η / 2) (ℓ * T / 2),
      Complex.Gamma_conj,
      Complex.norm_conj]
  rw [hconj]
  exact upperGammaPositiveShifted_log_norm_eq_neg_damping
    hℓ hη T

private theorem upperGammaShifted_modulus_eq_exp_neg_damping
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    ‖Complex.Gamma
        (((ℓ * η / 2 : ℝ) : ℂ) -
          Complex.I * ((ℓ * T / 2 : ℝ) : ℂ))‖ =
      Real.Gamma (ℓ * η / 2) *
        Real.exp (-upperGammaDamping ℓ η T) := by
  let m : ℝ := ℓ * η / 2
  let b : ℝ := ℓ * T / 2
  have hm : 0 < m := by
    try dsimp [m]
    positivity
  have hΓ : 0 < Real.Gamma m :=
    Real.Gamma_pos_of_pos hm
  have hz :
      Complex.Gamma
          ((m : ℂ) - Complex.I * (b : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero] using! hm
  have hratio :
      0 < ‖Complex.Gamma
          ((m : ℂ) - Complex.I * (b : ℂ))‖ /
            Real.Gamma m :=
    div_pos (norm_pos_iff.mpr hz) hΓ
  have hlog :=
    upperGammaShifted_log_norm_eq_neg_damping hℓ hη T
  change Real.log
    (‖Complex.Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))‖ /
      Real.Gamma m) = -upperGammaDamping ℓ η T at hlog
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log hratio] at hexp
  change ‖Complex.Gamma
      ((m : ℂ) - Complex.I * (b : ℂ))‖ =
        Real.Gamma m *
          Real.exp (-upperGammaDamping ℓ η T)
  calc
    ‖Complex.Gamma
        ((m : ℂ) - Complex.I * (b : ℂ))‖ =
        (‖Complex.Gamma
            ((m : ℂ) - Complex.I * (b : ℂ))‖ /
          Real.Gamma m) * Real.Gamma m := by
      rw [div_mul_cancel₀ _ hΓ.ne']
    _ = Real.exp (-upperGammaDamping ℓ η T) *
        Real.Gamma m := by
      rw [hexp]
    _ = Real.Gamma m *
        Real.exp (-upperGammaDamping ℓ η T) := by
      ring

end

section

open Filter MeasureTheory Set
open scoped Topology

private theorem plusSaddleProfile_re_pos_of_relative_residue_bounds
    {ε ℓ r : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    (N : ℕ)
    (hfinite :
      Real.exp (saddleSmallRadiusVariable ε r) *
        |(∑ n ∈ Finset.range (N + 1),
            (-saddleSmallRadiusVariable ε r) ^ n /
              (n.factorial : ℝ) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-(saddleSmallRadiusVariable ε r))| <
        (1 / 2 : ℝ))
    (hremainder :
      Real.exp (saddleSmallRadiusVariable ε r) *
        ‖plusSaddleTaylorRemainder ε ℓ N r /
          (saddleOriginValue ε ℓ : ℂ)‖ <
        (1 / 2 : ℝ)) :
    0 < (plusSaddleProfile ε ℓ r).re := by
  let y : ℝ := saddleSmallRadiusVariable ε r
  let S : ℝ :=
    ∑ n ∈ Finset.range (N + 1),
      (-y) ^ n / (n.factorial : ℝ) *
        plusSaddleSmallRadiusCoefficient ε ℓ n
  let Q : ℂ :=
    plusSaddleTaylorRemainder ε ℓ N r /
      (saddleOriginValue ε ℓ : ℂ)
  have hO : 0 < saddleOriginValue ε ℓ :=
    saddleOriginValue_pos hε ℓ
  have hnormal :
      (plusSaddleProfile ε ℓ r).re /
          saddleOriginValue ε ℓ = S + Q.re := by
    have h := congrArg Complex.re
      (plusSaddleProfile_div_origin_eq_small_radius_residue_series
        hε hℓ horder hr N)
    simpa [S, Q, y, Complex.div_ofReal_re,
      ← Complex.ofReal_neg, ← Complex.ofReal_pow] using! h
  have hexp : 0 < Real.exp y := Real.exp_pos y
  have hone : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  have hfinite' :
      Real.exp y * |S - Real.exp (-y)| < (1 / 2 : ℝ) := by
    simpa only [one_div] using! hfinite
  have hremainder' :
      Real.exp y * ‖Q‖ < (1 / 2 : ℝ) := by
    simpa [Q, y] using! hremainder
  have hSabs :
      -|S - Real.exp (-y)| ≤ S - Real.exp (-y) :=
    neg_abs_le _
  have hSlower :
      (1 / 2 : ℝ) < Real.exp y * S := by
    have hscaled := mul_le_mul_of_nonneg_left
      hSabs hexp.le
    linarith
  have hQabs := Complex.abs_re_le_norm Q
  have hQneg : -‖Q‖ ≤ Q.re := by
    linarith [neg_abs_le Q.re]
  have hQlower :
      -(1 / 2 : ℝ) < Real.exp y * Q.re := by
    have hscaled := mul_le_mul_of_nonneg_left
      hQneg hexp.le
    linarith
  have hsum : 0 < S + Q.re := by
    have hscaled : 0 < Real.exp y * (S + Q.re) := by
      linarith
    exact (mul_pos_iff_of_pos_left hexp).mp hscaled
  exact (div_pos_iff_of_pos_right hO).mp
    (hnormal.symm ▸ hsum)

end

section

open Filter MeasureTheory Set
open scoped Topology BigOperators

private theorem upperPositiveHalfGamma_scaled_sq_le
    (n : ℕ) (x : ℝ) :
    Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 ≤
      ‖Complex.Gamma
        (((((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          Complex.I * (x : ℂ))‖ ^ 2 *
        Real.cosh (Real.pi * x) := by
  induction n with
  | zero =>
      norm_num only [Nat.cast_zero, zero_add]
      have hhalf :
          ‖Complex.Gamma
            (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
            Real.pi / Real.cosh (Real.pi * x) := by
        convert! norm_gamma_half_add_imaginary_sq x using 1; norm_num
      rw [hhalf, Real.Gamma_one_half_eq,
        Real.sq_sqrt Real.pi_pos.le]
      field_simp [(Real.cosh_pos (Real.pi * x)).ne']; norm_num
  | succ n ih =>
      let q : ℝ := (n : ℝ) + 1 / 2
      have hq : 0 < q := by
        try dsimp [q]
        positivity
      have hreal :
          Real.Gamma (((n + 1 : ℕ) : ℝ) + 1 / 2) =
            q * Real.Gamma q := by
        convert! Real.Gamma_add_one hq.ne' using 1
        · simp only [Nat.cast_add, Nat.cast_one, one_div, q]
          ring_nf
      let z : ℂ := (q : ℂ) + Complex.I * (x : ℂ)
      have hz : z ≠ 0 := by
        intro hzero
        have h := congrArg Complex.re hzero
        have hqzero : q = 0 := by simpa [z] using! h
        exact hq.ne' hqzero
      have hcomplex :
          Complex.Gamma
              (((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) +
                Complex.I * (x : ℂ)) =
            z * Complex.Gamma z := by
        convert! Complex.Gamma_add_one z hz using 1
        · simp only [Nat.cast_add, Nat.cast_one, one_div, Complex.ofReal_add,
          Complex.ofReal_natCast,
            Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_ofNat, z, q]
          ring_nf
      have hzlower : q ≤ ‖z‖ := by
        have h := Complex.abs_re_le_norm z
        simpa [z, abs_of_pos hq] using! h
      have hcosh : 0 ≤ Real.cosh (Real.pi * x) :=
        (Real.cosh_pos _).le
      have hqnorm : 0 ≤ ‖Complex.Gamma z‖ ^ 2 :=
        sq_nonneg _
      rw [hreal, hcomplex, norm_mul]
      have ih' :
          Real.Gamma q ^ 2 ≤
            ‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x) := by
        simpa [q, z] using! ih
      calc
        (q * Real.Gamma q) ^ 2 =
            q ^ 2 * Real.Gamma q ^ 2 := by ring
        _ ≤ q ^ 2 *
            (‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x)) :=
          mul_le_mul_of_nonneg_left ih' (sq_nonneg q)
        _ ≤ ‖z‖ ^ 2 *
            (‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x)) := by
          gcongr
        _ = (‖z‖ * ‖Complex.Gamma z‖) ^ 2 *
            Real.cosh (Real.pi * x) := by ring

private theorem upperNegativeContour_shortMeasure_pointwise
    {ε ℓ κ η a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (ha : 0 < a)
    (hmargin : 0 ≤ (1 - 10 * ε * (1 + a))) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) ≤
      (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a := by
  have hfactor : 0 ≤ 1 - 4 * ε := by
    apply (mul_nonneg_iff_of_pos_right hη).mp
    exact mul_nonneg (by linarith [hεsmall]) hη.le
  have hmargintop : (1 - 10 * ε * (1 + a)) ≤ 1 - 10 * ε := by
    linarith [mul_nonneg hε.le ha.le]
  have hbase :
      (ℓ / 2) * Real.exp (-η * a) / a ^ 2 ≤
        upperGammaMeasureDensity ℓ η a := by
    have hvariance :=
      (upperGammaVarianceDensity_pointwise_bounds
        (η := η) hℓ ha).1
    apply (div_le_iff₀ (sq_pos_of_pos ha)).2
    linarith
  have hbasepos :
      0 ≤ (ℓ / 2) * Real.exp (-η * a) / a ^ 2 := by
    positivity
  have hratio :
      Real.cosh (κ * a) / Real.cosh a ≤
        Real.exp ((κ - 1) * a) := by
    convert! cosh_ratio_upper ha.le
      (sub_nonneg.mpr hκ) using 1; ring_nf
  have hexp :
      Real.exp ((η - 2) * a) *
        Real.exp ((κ - 1) * a) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    linarith [mul_nonneg
      (show 0 ≤ 3 - (κ + η) by linarith) ha.le]
  have hcoefficient :
      (1 - 10 * ε * (1 + a)) * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a) ≤
        1 - 4 * ε := by
    calc
      (1 - 10 * ε * (1 + a)) * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a) ≤
        (1 - 10 * ε * (1 + a)) * Real.exp ((η - 2) * a) *
          Real.exp ((κ - 1) * a) := by
          gcongr
      _ = (1 - 10 * ε * (1 + a)) *
          (Real.exp ((η - 2) * a) *
            Real.exp ((κ - 1) * a)) := by ring
      _ ≤ (1 - 10 * ε * (1 + a)) := by
          simpa only [mul_one] using! mul_le_mul_of_nonneg_left hexp hmargin
      _ ≤ 1 - 10 * ε := hmargintop
      _ ≤ 1 - 4 * ε := by linarith
  have hidentity :
      ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) =
        ((1 - 10 * ε * (1 + a)) * Real.exp ((η - 2) * a) *
          (Real.cosh (κ * a) / Real.cosh a)) *
          ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) := by
    have he : Real.exp ((η - 2) * a) *
        Real.exp (-η * a) = Real.exp (-2 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    calc
      (1 - 10 * ε * (1 + a)) * Real.exp (-(a * 2)) =
          (1 - 10 * ε * (1 + a)) *
            (Real.exp ((η - 2) * a) *
              Real.exp (-η * a)) := by
            rw [he]
            congr 1
            ring_nf
      _ = (1 - 10 * ε * (1 + a)) * Real.exp (a * (η - 2)) *
            Real.exp (-(a * η)) := by
            rw [show a * (η - 2) = (η - 2) * a by ring,
              show -(a * η) = -η * a by ring]
            ring
  rw [hidentity]
  calc
    ((1 - 10 * ε * (1 + a)) * Real.exp ((η - 2) * a) *
        (Real.cosh (κ * a) / Real.cosh a)) *
        ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) ≤
      (1 - 4 * ε) *
        ((ℓ / 2) * Real.exp (-η * a) / a ^ 2) :=
      mul_le_mul_of_nonneg_right hcoefficient hbasepos
    _ ≤ (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_left hbase hfactor

private theorem upperNegativeContour_shortDamping_le_gamma
    {ε ℓ κ η : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (T : ℝ) :
    upperShortShellDamping ε ℓ (-κ - 1) T ≤
      (1 - 4 * ε) * upperGammaDamping ℓ η T := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hfactor : 0 ≤ 1 - 4 * ε := by linarith
  have hsubset : Ioc a₀ A ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact ha₀.trans ha.1
  have hgamma := upperGammaDampingIntegrand_integrable hℓ hη T
  have hgammaOn : IntegrableOn
      (upperGammaDampingIntegrand ℓ η T) (Ioc a₀ A) :=
    hgamma.mono_set hsubset
  have hscaledOn : IntegrableOn
      (fun a : ℝ => (1 - 4 * ε) *
        upperGammaDampingIntegrand ℓ η T a)
      (Ioc a₀ A) :=
    hgammaOn.const_mul (1 - 4 * ε)
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (κ * a)) := by
    fun_prop
  have hosc : Continuous
      (fun a : ℝ => 1 - Real.cos (a * T)) := by
    fun_prop
  have hshortInterval : IntervalIntegrable
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (κ * a) *
            (1 - Real.cos (a * T)))
      volume a₀ A := by
    have hneg : IntervalIntegrable
        (fun a : ℝ => -shortShellDensity ε a)
        volume a₀ A := by
      simpa only  using! hs.neg
    exact ((hneg.const_mul ℓ).mul_continuousOn
      hcosh.continuousOn).mul_continuousOn
        hosc.continuousOn
  have hshortOn : IntegrableOn
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (κ * a) *
            (1 - Real.cos (a * T))) (Ioc a₀ A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show a₀ ≤ A by exact horder)).mp hshortInterval
  have hpoint (a : ℝ) (ha : a ∈ Ioc a₀ A) :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (κ * a) *
            (1 - Real.cos (a * T)) ≤
        (1 - 4 * ε) *
          upperGammaDampingIntegrand ℓ η T a := by
    have hcomparison :=
      upperNegativeContour_shortMeasure_pointwise
        hε hεsmall hℓ hκ hη hκη
        (ha₀.trans ha.1)
        (hmargin a ⟨ha.1.le, ha.2⟩)
    have hoscNonneg : 0 ≤ 1 - Real.cos (a * T) :=
      sub_nonneg.mpr (Real.cos_le_one _)
    have hmul :=
      mul_le_mul_of_nonneg_right hcomparison hoscNonneg
    simpa only [mul_neg, neg_mul, mul_assoc, mul_comm, mul_left_comm, upperGammaDampingIntegrand,
      ge_iff_le] using! hmul
  have hmono := setIntegral_mono_on
    hshortOn hscaledOn measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    unfold upperGammaDampingIntegrand
    exact mul_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos hℓ ha).le
  have haesubset :
      Ioc a₀ A ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall fun a ha => hsubset ha
  have hrestrict :=
    setIntegral_mono_set hgamma hnonnegative haesubset
  have hscaleRestrict :=
    mul_le_mul_of_nonneg_left hrestrict hfactor
  have hshortEq :
      upperShortShellDamping ε ℓ (-κ - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (κ * a) *
              (1 - Real.cos (a * T)) := by
    unfold upperShortShellDamping
    rw [show 1 + (-κ - 1) = -κ by ring,
      ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    change
      ℓ * ((-shortShellDensity ε a) *
        Real.cosh ((-κ) * a) *
          (1 - Real.cos (a * T))) =
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (κ * a) *
            (1 - Real.cos (a * T))
    rw [show (-κ) * a = -(κ * a) by ring,
      Real.cosh_neg]
    ring
  calc
    upperShortShellDamping ε ℓ (-κ - 1) T =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (κ * a) *
              (1 - Real.cos (a * T)) := hshortEq
    _ ≤ ∫ a : ℝ in Ioc a₀ A,
          (1 - 4 * ε) *
            upperGammaDampingIntegrand ℓ η T a := hmono
    _ = (1 - 4 * ε) *
          ∫ a : ℝ in Ioc a₀ A,
            upperGammaDampingIntegrand ℓ η T a := by
      rw [integral_const_mul]
    _ ≤ (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0,
            upperGammaDampingIntegrand ℓ η T a :=
      hscaleRestrict
    _ = (1 - 4 * ε) * upperGammaDamping ℓ η T := by
      rfl

private noncomputable def saddleNegativeContourOrdinate (ℓ : ℝ) (N : ℕ) : ℝ :=
  1 + (2 * (N : ℝ) + 1) / ℓ

private noncomputable def saddleNegativeGammaRate (ℓ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 3) / ℓ

private theorem saddleNegativeGammaRate_pos
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    0 < saddleNegativeGammaRate ℓ N := by
  unfold saddleNegativeGammaRate
  positivity

private theorem one_le_saddleNegativeContourOrdinate
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    1 ≤ saddleNegativeContourOrdinate ℓ N := by
  unfold saddleNegativeContourOrdinate
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hq : 0 ≤ (2 * (N : ℝ) + 1) / ℓ := by positivity
  linarith

private theorem saddleNegativeContourOrdinate_add_rate_le_three
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ) :
    saddleNegativeContourOrdinate ℓ N +
        saddleNegativeGammaRate ℓ N ≤ 3 := by
  unfold saddleNegativeContourOrdinate saddleNegativeGammaRate
  have hratio : (4 * (N : ℝ) + 4) / ℓ ≤ 2 := by
    apply (div_le_iff₀ hℓ).2
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    linarith
  calc
    1 + (2 * (N : ℝ) + 1) / ℓ +
        (2 * (N : ℝ) + 3) / ℓ =
      1 + (4 * (N : ℝ) + 4) / ℓ := by ring
    _ ≤ 1 + 2 := by
      simpa only [add_comm, add_le_add_iff_left] using! add_le_add_left hratio 1
    _ = 3 := by norm_num

private theorem upperNegativeContour_reflectedGamma_damping_exp_le_cosh
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    Real.exp
        (2 * upperGammaDamping ℓ
          (saddleNegativeGammaRate ℓ N) (-s / ℓ)) ≤
      Real.cosh (Real.pi * (s / 2)) := by
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let D : ℝ := upperGammaDamping ℓ η (-s / ℓ)
  let q : ℝ := (N : ℝ) + 3 / 2
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hΓ : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hmod :
      ‖Complex.Gamma
        ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
        Real.Gamma q * Real.exp (-D) := by
    have h := upperGammaShifted_modulus_eq_exp_neg_damping
      hℓ hη (-s / ℓ)
    have hmass : ℓ * η / 2 = q := by
      try dsimp [η, q, saddleNegativeGammaRate]
      field_simp [hℓ.ne']
    have hfreq : ℓ * (-s / ℓ) / 2 = -s / 2 := by
      field_simp [hℓ.ne']
    rw [hmass, hfreq] at h
    have harg :
        ((q : ℂ) - Complex.I * (((-s / 2 : ℝ) : ℂ))) =
          (q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [harg] at h
    exact h
  have hhalf := upperPositiveHalfGamma_scaled_sq_le
    (N + 1) (s / 2)
  have hhalfnormal :
      Real.Gamma q ^ 2 ≤
        ‖Complex.Gamma
          ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ ^ 2 *
            Real.cosh (Real.pi * (s / 2)) := by
    have hcast : ((N + 1 : ℕ) : ℝ) + 1 / 2 = q := by
      try dsimp [q]
      norm_num [Nat.cast_add, Nat.cast_one]; ring
    rw [hcast] at hhalf
    exact hhalf
  rw [hmod, mul_pow] at hhalfnormal
  have hcancel :
      1 ≤ Real.exp (-D) ^ 2 *
        Real.cosh (Real.pi * (s / 2)) := by
    have hscaled :
        Real.Gamma q ^ 2 * 1 ≤
          Real.Gamma q ^ 2 *
            (Real.exp (-D) ^ 2 *
              Real.cosh (Real.pi * (s / 2))) := by
      simpa only [mul_one, mul_assoc] using! hhalfnormal
    exact le_of_mul_le_mul_left hscaled
      (sq_pos_of_pos hΓ)
  have hinverse :
      Real.exp (2 * D) * Real.exp (-D) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert! Real.exp_zero using 1; ring_nf
  change Real.exp (2 * D) ≤ Real.cosh (Real.pi * (s / 2))
  calc
    Real.exp (2 * D) = Real.exp (2 * D) * 1 := by ring
    _ ≤ Real.exp (2 * D) *
        (Real.exp (-D) ^ 2 *
          Real.cosh (Real.pi * (s / 2))) :=
      mul_le_mul_of_nonneg_left hcancel (Real.exp_pos _).le
    _ = Real.cosh (Real.pi * (s / 2)) := by
      rw [show Real.exp (2 * D) *
        (Real.exp (-D) ^ 2 * Real.cosh (Real.pi * (s / 2))) =
        (Real.exp (2 * D) * Real.exp (-D) ^ 2) *
          Real.cosh (Real.pi * (s / 2)) by ring,
        hinverse, one_mul]

private theorem upperNegativeHalfGamma_reflection_norm
    (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      ‖Complex.Gamma
        (((((N : ℝ) + 3 / 2) : ℝ) : ℂ) +
          Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
      Real.pi / Real.cosh (Real.pi * (s / 2)) := by
  induction N with
  | zero =>
      let z : ℂ := (1 / 2 : ℂ) +
        Complex.I * (((s / 2 : ℝ) : ℂ))
      have hz : z ≠ 0 := by
        intro hz0
        have h := congrArg Complex.re hz0
        norm_num [z] at h
      have hneg : -z ≠ 0 := neg_ne_zero.mpr hz
      have hargneg : upperNegativeHalfGammaArgument 0 s = -z := by
        simp only [upperNegativeHalfGammaArgument, CharP.cast_eq_zero, one_div, zero_add,
          Complex.ofReal_div,
          Complex.ofReal_ofNat, neg_add_rev, z]
        ring
      have hargpos :
          (((((0 : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
            Complex.I * (((s / 2 : ℝ) : ℂ))) = z + 1 := by
        simp only [CharP.cast_eq_zero, zero_add, Complex.ofReal_div, Complex.ofReal_ofNat,
          one_div, z]
        ring
      have hconjarg : -z + 1 = starRingEnd ℂ z := by
        try dsimp [z]
        simp only [map_add, map_div₀, Complex.conj_ofReal,
          Complex.conj_I, Complex.conj_ofNat, map_mul, map_one]
        push_cast
        ring
      have hnegRec := Complex.Gamma_add_one (-z) hneg
      rw [hconjarg, Complex.Gamma_conj] at hnegRec
      have hnegNorm :
          ‖Complex.Gamma z‖ =
            ‖z‖ * ‖Complex.Gamma (-z)‖ := by
        have h := congrArg norm hnegRec
        simpa only [RCLike.norm_conj, neg_mul, norm_neg, Complex.norm_mul] using! h
      have hposRec := Complex.Gamma_add_one z hz
      have hposNorm :
          ‖Complex.Gamma (z + 1)‖ =
            ‖z‖ * ‖Complex.Gamma z‖ := by
        simpa only [Complex.norm_mul] using! congrArg norm hposRec
      rw [hargneg, hargpos, hposNorm]
      calc
        ‖Complex.Gamma (-z)‖ *
            (‖z‖ * ‖Complex.Gamma z‖) =
          (‖z‖ * ‖Complex.Gamma (-z)‖) *
            ‖Complex.Gamma z‖ := by ring
        _ = ‖Complex.Gamma z‖ ^ 2 := by
          rw [← hnegNorm]
          ring
        _ = Real.pi / Real.cosh (Real.pi * (s / 2)) := by
          try dsimp [z]
          convert! norm_gamma_half_add_imaginary_sq (s / 2)
            using 1
  | succ N ih =>
      let z : ℂ :=
        (((((N : ℝ) + 3 / 2) : ℝ) : ℂ) +
          Complex.I * (((s / 2 : ℝ) : ℂ)))
      have hz : z ≠ 0 := by
        intro hz0
        have h := congrArg Complex.re hz0
        simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div,
          Complex.ofReal_ofNat,
          Complex.add_re, Complex.natCast_re, Complex.div_ofNat_re, Complex.re_ofNat,
            Complex.mul_re, Complex.I_re,
          Complex.ofReal_re, zero_mul, Complex.I_im, Complex.div_ofNat_im, Complex.ofReal_im,
            zero_div, mul_zero, sub_self,
          add_zero, Complex.zero_re, z] at h
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      have harg :
          upperNegativeHalfGammaArgument (N + 1) s = -z := by
        unfold upperNegativeHalfGammaArgument
        simp only [Nat.cast_add, Nat.cast_one, one_div, neg_add_rev, Complex.ofReal_div,
          Complex.ofReal_ofNat,
          Complex.ofReal_add, Complex.ofReal_natCast, z]
        ring
      have hpos :
          (((((N + 1 : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
            Complex.I * (((s / 2 : ℝ) : ℂ))) = z + 1 := by
        simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
          Complex.ofReal_one,
          Complex.ofReal_div, Complex.ofReal_ofNat, z]
        ring
      have hnegRec := Complex.Gamma_add_one
        (upperNegativeHalfGammaArgument (N + 1) s)
        (upperNegativeHalfGammaArgument_ne_zero (N + 1) s)
      rw [upperNegativeHalfGammaArgument_succ_add_one] at hnegRec
      have hnegNorm :
          ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
            ‖z‖ *
              ‖Complex.Gamma
                (upperNegativeHalfGammaArgument (N + 1) s)‖ := by
        have h := congrArg norm hnegRec
        rw [norm_mul, harg, norm_neg] at h
        simpa only [harg] using! h
      have hposRec := Complex.Gamma_add_one z hz
      have hposNorm :
          ‖Complex.Gamma (z + 1)‖ =
            ‖z‖ * ‖Complex.Gamma z‖ := by
        simpa only [Complex.norm_mul] using! congrArg norm hposRec
      rw [hpos, hposNorm]
      calc
        ‖Complex.Gamma
            (upperNegativeHalfGammaArgument (N + 1) s)‖ *
            (‖z‖ * ‖Complex.Gamma z‖) =
          (‖z‖ *
            ‖Complex.Gamma
              (upperNegativeHalfGammaArgument (N + 1) s)‖) *
              ‖Complex.Gamma z‖ := by ring
        _ = ‖Complex.Gamma
            (upperNegativeHalfGammaArgument N s)‖ *
              ‖Complex.Gamma z‖ := by rw [← hnegNorm]
        _ = Real.pi / Real.cosh (Real.pi * (s / 2)) := by
          simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div,
            Complex.ofReal_ofNat, z] using! ih

private theorem upperNegativeHalfGamma_norm_eq_reflected_damping
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp
          (upperGammaDamping ℓ
            (saddleNegativeGammaRate ℓ N) (-s / ℓ)) /
          Real.cosh (Real.pi * (s / 2)) := by
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let D : ℝ := upperGammaDamping ℓ η (-s / ℓ)
  let q : ℝ := (N : ℝ) + 3 / 2
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hq : 0 < q := by
    try dsimp [q]
    positivity
  have hΓ : 0 < Real.Gamma q := Real.Gamma_pos_of_pos hq
  have hmass : ℓ * η / 2 = q := by
    try dsimp [η, q, saddleNegativeGammaRate]
    field_simp [hℓ.ne']
  have hfreq : ℓ * (-s / ℓ) / 2 = -s / 2 := by
    field_simp [hℓ.ne']
  have hmod := upperGammaShifted_modulus_eq_exp_neg_damping
    hℓ hη (-s / ℓ)
  rw [hmass, hfreq] at hmod
  have harg :
      ((q : ℂ) - Complex.I * (((-s / 2 : ℝ) : ℂ))) =
        (q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg] at hmod
  have href := upperNegativeHalfGamma_reflection_norm N s
  change
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      ‖Complex.Gamma
        ((q : ℂ) + Complex.I * (((s / 2 : ℝ) : ℂ)))‖ =
      Real.pi / Real.cosh (Real.pi * (s / 2)) at href
  rw [hmod] at href
  change
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
      (Real.pi / Real.Gamma q) * Real.exp D /
        Real.cosh (Real.pi * (s / 2))
  rw [Real.exp_neg] at href
  field_simp [hΓ.ne', (Real.exp_pos D).ne',
    (Real.cosh_pos (Real.pi * (s / 2))).ne'] at href ⊢
  simpa [D, neg_div, mul_comm, mul_left_comm, mul_assoc] using! href

private theorem upper_log_cosh_ge_abs_sub_log_two (x : ℝ) :
    |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hhalf : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have hp := (Real.exp_pos (-|x|)).le
    linarith
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (Real.cosh_pos x), Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact hhalf

private theorem upperNegativeContour_gamma_mul_exp_short_le
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
      Real.exp
        (upperShortShellDamping ε ℓ
          (-saddleNegativeContourOrdinate ℓ N - 1)
          (-s / ℓ)) ≤
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|) := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  let η : ℝ := saddleNegativeGammaRate ℓ N
  let T : ℝ := -s / ℓ
  let D : ℝ := upperGammaDamping ℓ η T
  let C : ℝ := Real.cosh (Real.pi * (s / 2))
  have hκ : 1 ≤ κ := one_le_saddleNegativeContourOrdinate hℓ N
  have hη : 0 < η := saddleNegativeGammaRate_pos hℓ N
  have hκη : κ + η ≤ 3 :=
    saddleNegativeContourOrdinate_add_rate_le_three hℓ N hN
  have hshort := upperNegativeContour_shortDamping_le_gamma
    hε hεsmall hℓ hκ hη hκη horder hmargin T
  have hD : 0 ≤ D := upperGammaDamping_nonneg hℓ T
  have hC : 0 < C := Real.cosh_pos _
  have hreflect :=
    upperNegativeContour_reflectedGamma_damping_exp_le_cosh
      hℓ N s
  have hDlog : 2 * D ≤ Real.log C := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hC]
    exact hreflect
  have hlog := upper_log_cosh_ge_abs_sub_log_two
    (Real.pi * (s / 2))
  have hfactor : 0 ≤ 2 - 4 * ε := by linarith
  have hphase :
      (2 - 4 * ε) * D - Real.log C ≤
        -(2 * ε) * Real.log C := by
    linarith [mul_nonneg hfactor
      (show 0 ≤ Real.log C - 2 * D by linarith)]
  have hlogphase :
      -(2 * ε) * Real.log C ≤
        2 * ε * Real.log 2 - ε * Real.pi * |s| := by
    have habs : |Real.pi * (s / 2)| =
        Real.pi * |s| / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [habs] at hlog
    linarith [mul_nonneg (show 0 ≤ 2 * ε by positivity)
      (show 0 ≤ Real.log C -
        (Real.pi * |s| / 2 - Real.log 2) by
        try dsimp [C]
        linarith)]
  have hΓ : 0 < Real.Gamma ((N : ℝ) + 3 / 2) := by
    apply Real.Gamma_pos_of_pos
    positivity
  have hpref : 0 ≤ Real.pi /
      Real.Gamma ((N : ℝ) + 3 / 2) := by positivity
  rw [upperNegativeHalfGamma_norm_eq_reflected_damping
    hℓ N s]
  change
    ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
      Real.exp D / C) *
        Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
      (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|)
  have hshortexp :
      Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
        Real.exp ((1 - 4 * ε) * D) :=
    Real.exp_le_exp.mpr hshort
  calc
    ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
      Real.exp D / C) *
        Real.exp (upperShortShellDamping ε ℓ (-κ - 1) T) ≤
      ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp D / C) *
          Real.exp ((1 - 4 * ε) * D) := by
            gcongr
    _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp ((2 - 4 * ε) * D - Real.log C) := by
      have he :
          Real.exp D * Real.exp ((1 - 4 * ε) * D) =
            Real.exp ((2 - 4 * ε) * D) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.exp_sub, Real.exp_log hC]
      calc
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp D / C) *
            Real.exp ((1 - 4 * ε) * D) =
          (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            (Real.exp D *
              Real.exp ((1 - 4 * ε) * D)) / C := by ring
        _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp ((2 - 4 * ε) * D) / C := by rw [he]
        _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            (Real.exp ((2 - 4 * ε) * D) / C) := by ring
    _ ≤ (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (-(2 * ε) * Real.log C) := by
      gcongr
    _ ≤ (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp
          (2 * ε * Real.log 2 - ε * Real.pi * |s|) := by
      gcongr
    _ = (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
        Real.exp (2 * ε * Real.log 2) *
          Real.exp (-ε * Real.pi * |s|) := by
      rw [show 2 * ε * Real.log 2 - ε * Real.pi * |s| =
        (2 * ε * Real.log 2) + (-ε * Real.pi * |s|) by ring,
        Real.exp_add]
      ring

private theorem upperShortShellDamping_neg_frequency
    (ε ℓ δ T : ℝ) :
    upperShortShellDamping ε ℓ δ (-T) =
      upperShortShellDamping ε ℓ δ T := by
  unfold upperShortShellDamping
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  change
    (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * (-T))) =
      (-shortShellDensity ε a) *
        Real.cosh ((1 + δ) * a) *
          (1 - Real.cos (a * T))
  rw [show a * (-T) = -(a * T) by ring, Real.cos_neg]

private theorem saddleTaylorContour_gammaArgument
    (N : ℕ) (s : ℝ) :
    (((saddleTaylorContour N : ℂ) +
      (s : ℂ) * Complex.I) / 2) =
      upperNegativeHalfGammaArgument N (-s) := by
  unfold saddleTaylorContour upperNegativeHalfGammaArgument
  push_cast
  ring

private theorem saddleTaylorContour_shellArgument
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    Complex.I *
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
          (ℓ : ℂ) =
      ((-s / ℓ : ℝ) : ℂ) +
        Complex.I *
          (((-saddleNegativeContourOrdinate ℓ N : ℝ) : ℂ)) := by
  unfold saddleTaylorContour saddleNegativeContourOrdinate
  push_cast
  field_simp [hℓ.ne']
  ring_nf
  simp only [Complex.I_sq, neg_mul, one_mul]; ring

private theorem saddleNegativeContourOrdinate_le_two
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ) :
    saddleNegativeContourOrdinate ℓ N ≤ 2 := by
  unfold saddleNegativeContourOrdinate
  have hratio : (2 * (N : ℝ) + 1) / ℓ ≤ 1 := by
    apply (div_le_iff₀ hℓ).2
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    linarith
  linarith

private theorem upperNegativeContour_gamma_mul_shellExponential_le
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (s : ℝ) :
    ‖Complex.Gamma
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) / 2) *
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          (Complex.I *
            (((saddleTaylorContour N : ℂ) +
              (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
                (ℓ : ℂ)))‖ ≤
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) *
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|)) := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  let T : ℝ := -s / ℓ
  let δ : ℝ := -κ - 1
  let S : ℝ := upperShortShellDamping ε ℓ δ T
  let P : ℝ := positiveShellDamping ε ℓ δ T
  have hP : 0 ≤ P := positiveShellDamping_nonneg hℓ.le
  have hgamma := upperNegativeContour_gamma_mul_exp_short_le
    hε hεsmall hℓ N hN horder hmargin (-s)
  have heven :
      upperShortShellDamping ε ℓ δ (-(-s) / ℓ) = S := by
    have h := upperShortShellDamping_neg_frequency
      ε ℓ δ T
    have hfreq : -T = -(-s) / ℓ := by
      try dsimp [T]
      ring
    rw [hfreq] at h
    exact h
  have hgamma' :
      ‖Complex.Gamma
        (upperNegativeHalfGammaArgument N (-s))‖ *
          Real.exp S ≤
        (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|) := by
    have h :
        ‖Complex.Gamma
          (upperNegativeHalfGammaArgument N (-s))‖ *
            Real.exp
              (upperShortShellDamping ε ℓ δ (s / ℓ)) ≤
          (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp (2 * ε * Real.log 2) *
              Real.exp (-ε * Real.pi * |s|) := by
      simpa only [neg_mul, neg_neg, abs_neg] using! hgamma
    have hfreq : s / ℓ = -T := by
      try dsimp [T]
      ring
    rw [hfreq, upperShortShellDamping_neg_frequency] at h
    exact h
  have hshell := norm_saddleShellExponential_eq_exp_neg_damping
    hε horder ℓ T (-κ)
  have hshell' :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          ((T : ℂ) + Complex.I * ((-κ : ℝ) : ℂ)))‖ =
        Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp (-(P - S)) := by
    rw [realHyperbolicShellPhase_neg] at hshell
    convert! hshell using 1
  have hexp : Real.exp (-(P - S)) ≤ Real.exp S := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [saddleTaylorContour_gammaArgument,
    saddleTaylorContour_shellArgument hℓ N s,
    norm_mul, hshell']
  calc
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
        (Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp (-(P - S))) ≤
      ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
        (Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp S) := by
        gcongr
    _ = Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
        (‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
          Real.exp S) := by ring
    _ ≤ Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|)) :=
      mul_le_mul_of_nonneg_left hgamma' (Real.exp_pos _).le

private noncomputable def saddleNegativeFrequencyMajorant (ε s : ℝ) : ℝ :=
  (1 + |s|) ^ 3 * Real.exp (-ε * Real.pi * |s|)

private theorem saddleNegativeFrequencyMajorant_integrable
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (saddleNegativeFrequencyMajorant ε) := by
  have hrate : 0 < ε * Real.pi := mul_pos hε Real.pi_pos
  have h0 := integrable_abs_pow_mul_exp_neg_mul_abs 0 hrate
  have h1 := integrable_abs_pow_mul_exp_neg_mul_abs 1 hrate
  have h2 := integrable_abs_pow_mul_exp_neg_mul_abs 2 hrate
  have h3 := integrable_abs_pow_mul_exp_neg_mul_abs 3 hrate
  have hsum := h0.add
    ((h1.const_mul 3).add
      ((h2.const_mul 3).add h3))
  apply hsum.congr
  filter_upwards [] with s
  unfold saddleNegativeFrequencyMajorant
  simp only [Pi.add_apply, pow_zero, pow_one]
  ring_nf

private theorem norm_plusPolynomial_negativeContour_le
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (s : ℝ) :
    ‖plusPolynomial ε
      (Complex.I *
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
            (ℓ : ℂ))‖ ≤
      27 * (1 + |(ε / 4)|) * (1 + |s|) ^ 3 := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  have hκ : 1 ≤ κ :=
    one_le_saddleNegativeContourOrdinate hℓ N
  have hκtop : κ ≤ 2 :=
    saddleNegativeContourOrdinate_le_two hℓ N hN
  have hℓone : 1 ≤ ℓ := by
    norm_num [Nat.cast_add, Nat.cast_one] at hN
    have hcast : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hdivide : |s| / ℓ ≤ |s| :=
    (div_le_self (abs_nonneg s) hℓone)
  have hnorm :
      ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        |s| / ℓ + κ := by
    calc
      ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        ‖((-s / ℓ : ℝ) : ℂ)‖ +
          ‖Complex.I * (((-κ : ℝ) : ℂ))‖ :=
        norm_add_le _ _
      _ = |s| / ℓ + κ := by
        simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.norm_div, norm_neg,
          Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hℓ, mul_neg, Complex.norm_mul, Complex.norm_I,
            abs_of_nonneg (show 0 ≤ κ by linarith),
          one_mul]
  have hbase :
      1 + ‖((-s / ℓ : ℝ) : ℂ) +
        Complex.I * (((-κ : ℝ) : ℂ))‖ ≤
        3 * (1 + |s|) := by
    linarith [abs_nonneg s]
  rw [saddleTaylorContour_shellArgument hℓ N s]
  calc
    ‖plusPolynomial ε
        (((-s / ℓ : ℝ) : ℂ) +
          Complex.I * (((-κ : ℝ) : ℂ)))‖ ≤
      (1 + |(ε / 4)|) *
        (1 + ‖((-s / ℓ : ℝ) : ℂ) +
          Complex.I * (((-κ : ℝ) : ℂ))‖) ^ 3 :=
      norm_plusPolynomial_le ε _
    _ ≤ (1 + |(ε / 4)|) *
        (3 * (1 + |s|)) ^ 3 := by
      gcongr
    _ = 27 * (1 + |(ε / 4)|) * (1 + |s|) ^ 3 := by
      ring

private theorem saddleNegativeContour_piExponential_norm
    (ℓ : ℝ) (N : ℕ) (s : ℝ) :
    ‖Complex.exp
      ((((ℓ : ℂ) -
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)) *
          (Real.log Real.pi : ℂ) / 2))‖ =
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.add_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      Complex.sub_im,
    Complex.add_im, Complex.mul_im, zero_add, zero_sub, sub_zero]

private noncomputable def saddleNegativeMellinMajorantCoefficient
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  27 * (1 + |(ε / 4)|) *
    Real.exp (2 * ε * Real.log 2) *
    (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
    Real.exp
      ((ℓ - saddleTaylorContour N) *
        Real.log Real.pi / 2) *
    Real.exp
      (ℓ * realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N))

private theorem plusSaddleMellinData_negativeContour_norm_le
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (s : ℝ) :
    ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖ ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMajorant ε s := by
  let z : ℂ := (saddleTaylorContour N : ℂ) +
    (s : ℂ) * Complex.I
  let q : ℂ := Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)
  have hfactor :=
    upperNegativeContour_gamma_mul_shellExponential_le
      hε hεsmall hℓ N hN horder hmargin s
  have hpoly := norm_plusPolynomial_negativeContour_le
    (ε := ε) hℓ N hN s
  have hpi := saddleNegativeContour_piExponential_norm
    ℓ N s
  change ‖plusSaddleMellinData ε ℓ z‖ ≤ _
  unfold plusSaddleMellinData saddleMellinEnvelope
  change
    ‖(Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)) *
            plusPolynomial ε q‖ ≤ _
  calc
    ‖(Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
        Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)) *
            plusPolynomial ε q‖ =
      ‖Complex.exp
        (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2)‖ *
        ‖Complex.Gamma (z / 2) *
          Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)‖ *
            ‖plusPolynomial ε q‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      ring
    _ ≤ Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
        (Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (saddleNegativeContourOrdinate ℓ N)) *
          ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp (2 * ε * Real.log 2) *
              Real.exp (-ε * Real.pi * |s|))) *
          (27 * (1 + |(ε / 4)|) * (1 + |s|) ^ 3) := by
      have hfactor' :
          ‖Complex.Gamma (z / 2) *
            Complex.exp ((ℓ : ℂ) * mellinShellPhase ε q)‖ ≤
            Real.exp
              (ℓ * realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N)) *
              ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
                Real.exp (2 * ε * Real.log 2) *
                  Real.exp (-ε * Real.pi * |s|)) := by
        simpa only [Complex.norm_mul, neg_mul, z, q] using! hfactor
      have hpoly' :
          ‖plusPolynomial ε q‖ ≤
            27 * (1 + |(ε / 4)|) * (1 + |s|) ^ 3 := by
        simpa only [q, z] using! hpoly
      have hpi' :
          ‖Complex.exp
            (((ℓ : ℂ) - z) *
              (Real.log Real.pi : ℂ) / 2)‖ =
            Real.exp
              ((ℓ - saddleTaylorContour N) *
                Real.log Real.pi / 2) := by
        simpa only [z] using! hpi
      rw [hpi']
      gcongr
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMajorant ε s := by
      unfold saddleNegativeMellinMajorantCoefficient
        saddleNegativeFrequencyMajorant
      ring

private noncomputable def saddleNegativeFrequencyMass (ε : ℝ) : ℝ :=
  ∫ s : ℝ, saddleNegativeFrequencyMajorant ε s

private theorem saddleNegativeFrequencyMass_nonneg (ε : ℝ) :
    0 ≤ saddleNegativeFrequencyMass ε := by
  unfold saddleNegativeFrequencyMass
  apply integral_nonneg
  intro s
  unfold saddleNegativeFrequencyMajorant
  positivity

private theorem plusSaddleMellinData_negativeContour_integral_norm_le
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a))) :
    (∫ s : ℝ,
      ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖) ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε := by
  have hdata : Integrable
      (fun s : ℝ =>
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (s : ℂ) * Complex.I)) := by
    simpa only [pow_zero, one_mul] using!
      plusSaddleMellinData_shiftedLine_moment_integrable
        hε hℓ horder
        (fun n : ℕ => saddleTaylorContour_ne_pole N n) 0
  have hmajor : Integrable
      (fun s : ℝ =>
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMajorant ε s) :=
    (saddleNegativeFrequencyMajorant_integrable hε).const_mul
      (saddleNegativeMellinMajorantCoefficient ε ℓ N)
  calc
    (∫ s : ℝ,
      ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖) ≤
      ∫ s : ℝ,
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMajorant ε s := by
        apply integral_mono hdata.norm hmajor
        intro s
        exact plusSaddleMellinData_negativeContour_norm_le
          hε hεsmall hℓ N hN horder hmargin s
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε := by
      rw [integral_const_mul]
      rfl

private theorem plusSaddleTaylorRemainder_negativeContour_bound
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r‖ ≤
      (1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε := by
  let a : ℝ := saddleTaylorContour N
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hdata : Integrable
      (fun t : ℝ => plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa only [pow_zero, one_mul] using!
      plusSaddleMellinData_shiftedLine_moment_integrable
        hε hℓ horder
        (fun n : ℕ => saddleTaylorContour_ne_pole N n) 0
  have hline :=
    plusSaddleMellinData_negativeContour_integral_norm_le
      hε hεsmall hℓ N hN horder hmargin
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    try dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  unfold plusSaddleTaylorRemainder
  change
    ‖c *
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤ _
  rw [norm_mul, hc]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ,
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
          ‖saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        gcongr
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = (1 / (2 * Real.pi)) *
        (r ^ (2 * N + 1) *
          (∫ t : ℝ,
            ‖plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖)) := by
      rw [saddleMellinInversePower_shiftedLine_integral_norm
        hr (plusSaddleMellinData ε ℓ) hdata]
      change
        (1 / (2 * Real.pi)) *
          (r ^ (-(saddleTaylorContour N)) * _) = _
      rw [saddleTaylorContour_rpow]
    _ ≤ (1 / (2 * Real.pi)) *
        (r ^ (2 * N + 1) *
          (saddleNegativeMellinMajorantCoefficient ε ℓ N *
            saddleNegativeFrequencyMass ε)) := by
      gcongr
    _ = (1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
          saddleNegativeMellinMajorantCoefficient ε ℓ N *
            saddleNegativeFrequencyMass ε := by ring

private theorem saddleSmallRadiusVariable_sqrt_eq_source
    (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (saddleSmallRadiusVariable ε r) =
      r * Real.exp
        (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) := by
  let q : ℝ := r * Real.exp
    (Real.log Real.pi / 2 + saddleShellDerivativeOne ε)
  have hq : 0 ≤ q := by
    try dsimp [q]
    positivity
  have he :
      Real.exp
        (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) ^ 2 =
        Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) := by
    rw [pow_two, ← Real.exp_add]
    rw [show
      (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) +
          (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) =
        Real.log Real.pi + 2 * saddleShellDerivativeOne ε by ring,
      Real.exp_add, Real.exp_log Real.pi_pos]
  have hsq : q ^ 2 = saddleSmallRadiusVariable ε r := by
    try dsimp [q]
    rw [mul_pow, he]
    unfold saddleSmallRadiusVariable
    ring
  have hsqrt := Real.sq_sqrt
    (saddleSmallRadiusVariable_nonneg ε r)
  have hsqrtpos := Real.sqrt_nonneg
    (saddleSmallRadiusVariable ε r)
  change Real.sqrt (saddleSmallRadiusVariable ε r) = q
  nlinarith

private theorem saddleSmallRadiusVariable_halfIntegerFactor
    (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    r ^ (2 * N + 1) *
      Real.exp
        (((2 * N + 1 : ℕ) : ℝ) *
          (Real.log Real.pi / 2 +
            saddleShellDerivativeOne ε)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N := by
  let q : ℝ := r * Real.exp
    (Real.log Real.pi / 2 + saddleShellDerivativeOne ε)
  have hsqrt := saddleSmallRadiusVariable_sqrt_eq_source ε hr
  have hq : q ^ 2 = saddleSmallRadiusVariable ε r := by
    have he :
        Real.exp
          (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) ^ 2 =
          Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) := by
      rw [pow_two, ← Real.exp_add]
      rw [show
        (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) +
            (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) =
          Real.log Real.pi + 2 * saddleShellDerivativeOne ε by ring,
        Real.exp_add, Real.exp_log Real.pi_pos]
    try dsimp [q]
    rw [mul_pow, he]
    unfold saddleSmallRadiusVariable
    ring
  rw [Real.exp_nat_mul]
  rw [← mul_pow]
  change q ^ (2 * N + 1) =
    Real.sqrt (saddleSmallRadiusVariable ε r) *
      saddleSmallRadiusVariable ε r ^ N
  rw [hsqrt, ← hq]
  change q ^ (2 * N + 1) = q * (q ^ 2) ^ N
  rw [← pow_mul, pow_succ]
  ring

private noncomputable def saddleNegativeContourPhaseError
    (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  ℓ *
      (realHyperbolicShellPhase ε
        (saddleNegativeContourOrdinate ℓ N) -
          realHyperbolicShellPhase ε 1) -
    (((2 * N + 1 : ℕ) : ℝ) *
      saddleShellDerivativeOne ε)

private theorem saddleNegativeContour_sourceNormalizationFactor
    (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) /
      (Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hrad := saddleSmallRadiusVariable_halfIntegerFactor
    ε hr N
  have hden :
      Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) ≠ 0 := by
    positivity
  field_simp [hden]
  rw [show ℓ * Real.log Real.pi / 2 =
    (ℓ / 2) * Real.log Real.pi by ring]
  rw [show
    Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
        Real.exp (saddleNegativeContourPhaseError ε ℓ N) =
      (Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N)) by ring]
  rw [← hrad]
  unfold saddleNegativeContourPhaseError saddleTaylorContour
  push_cast
  have hexponents :
      Real.exp
          ((ℓ - -(2 * (N : ℝ) + 1)) *
            Real.log Real.pi / 2) *
        Real.exp
          (ℓ * realHyperbolicShellPhase ε
            (saddleNegativeContourOrdinate ℓ N)) =
      Real.exp
          ((2 * (N : ℝ) + 1) *
            (Real.log Real.pi / 2 +
              saddleShellDerivativeOne ε)) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp
            (ℓ *
              (realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N) -
                  realHyperbolicShellPhase ε 1) -
              (2 * (N : ℝ) + 1) *
                saddleShellDerivativeOne ε)) := by
    rw [← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - -(2 * (N : ℝ) + 1)) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) =
      r ^ (2 * N + 1) *
        (Real.exp
          ((ℓ - -(2 * (N : ℝ) + 1)) *
            Real.log Real.pi / 2) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (saddleNegativeContourOrdinate ℓ N))) := by ring
    _ = r ^ (2 * N + 1) *
      (Real.exp
          ((2 * (N : ℝ) + 1) *
            (Real.log Real.pi / 2 +
              saddleShellDerivativeOne ε)) *
        (Real.exp ((ℓ / 2) * Real.log Real.pi) *
          Real.exp (ℓ * realHyperbolicShellPhase ε 1) *
          Real.exp
            (ℓ *
              (realHyperbolicShellPhase ε
                (saddleNegativeContourOrdinate ℓ N) -
                  realHyperbolicShellPhase ε 1) -
              (2 * (N : ℝ) + 1) *
                saddleShellDerivativeOne ε))) := by
        rw [hexponents]
    _ = _ := by ring

private noncomputable def saddleNegativeRelativeCoefficient (ε : ℝ) : ℝ :=
  27 * (1 + |(ε / 4)|) *
    Real.exp (2 * ε * Real.log 2) *
      saddleNegativeFrequencyMass ε / (4 * (ε / 4))

private theorem saddleNegativeRelativeCoefficient_nonneg
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ saddleNegativeRelativeCoefficient ε := by
  unfold saddleNegativeRelativeCoefficient
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (by positivity))
        (Real.exp_pos _).le)
      (saddleNegativeFrequencyMass_nonneg ε))
    (mul_pos (by norm_num) (div_pos hε four_pos)).le

private theorem saddleNegativeContour_normalizedMajorant_eq
    {ε : ℝ} (hε : 0 < ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε) /
          saddleOriginValue ε ℓ =
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hb : (ε / 4) ≠ 0 := (div_pos hε four_pos).ne'
  have hΓ : Real.Gamma ((N : ℝ) + 3 / 2) ≠ 0 := by
    apply (Real.Gamma_pos_of_pos (by positivity)).ne'
  have horigin :
      saddleOriginValue ε ℓ =
        2 *
          (Real.exp ((ℓ / 2) * Real.log Real.pi) *
            Real.exp (ℓ * realHyperbolicShellPhase ε 1)) *
          (ε / 4) := by
    unfold saddleOriginValue
    rw [Real.rpow_def_of_pos Real.pi_pos]
    rw [show Real.log Real.pi * (ℓ / 2) =
      (ℓ / 2) * Real.log Real.pi by ring]
    ring
  have hphase := saddleNegativeContour_sourceNormalizationFactor
    ε ℓ N hr
  calc
    ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε) /
          saddleOriginValue ε ℓ =
      saddleNegativeRelativeCoefficient ε *
        (r ^ (2 * N + 1) *
          Real.exp
            ((ℓ - saddleTaylorContour N) *
              Real.log Real.pi / 2) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (saddleNegativeContourOrdinate ℓ N)) /
          (Real.exp ((ℓ / 2) * Real.log Real.pi) *
            Real.exp (ℓ * realHyperbolicShellPhase ε 1))) /
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        rw [horigin]
        unfold saddleNegativeMellinMajorantCoefficient
          saddleNegativeRelativeCoefficient
        field_simp [Real.pi_pos.ne', hb, hΓ,
          (Real.exp_pos ((ℓ / 2) * Real.log Real.pi)).ne',
          (Real.exp_pos
            (ℓ * realHyperbolicShellPhase ε 1)).ne']; ring
    _ = saddleNegativeRelativeCoefficient ε *
        (Real.sqrt (saddleSmallRadiusVariable ε r) *
          saddleSmallRadiusVariable ε r ^ N *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N)) /
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        rw [hphase]
    _ = saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
        ring

private theorem plusSaddleTaylorRemainder_negativeContour_relative_bound
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r /
      (saddleOriginValue ε ℓ : ℂ)‖ ≤
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hO := saddleOriginValue_pos hε ℓ
  have hraw := plusSaddleTaylorRemainder_negativeContour_bound
    hε hεsmall hℓ N hN horder hmargin hr
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hO]
  calc
    ‖plusSaddleTaylorRemainder ε ℓ N r‖ /
        saddleOriginValue ε ℓ ≤
      ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε) /
            saddleOriginValue ε ℓ := by
        exact (div_le_div_iff_of_pos_right hO).mpr hraw
    _ = saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) :=
      saddleNegativeContour_normalizedMajorant_eq hε ℓ N hr.le

private theorem exists_saddleNegativeContourPhaseError_bound
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ,
          2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ →
            |saddleNegativeContourPhaseError ε ℓ N| ≤
              K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
  obtain ⟨K, hK, hTaylor⟩ :=
    exists_realHyperbolicShellPhase_quadratic_remainder
      hε horder
  refine ⟨K, hK, ?_⟩
  intro ℓ hℓ N hN
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  have hκlow : 1 ≤ κ :=
    one_le_saddleNegativeContourOrdinate hℓ N
  have hκhigh : κ ≤ 2 :=
    saddleNegativeContourOrdinate_le_two hℓ N hN
  have hκmem : κ ∈ Icc (1 : ℝ) 2 :=
    ⟨hκlow, hκhigh⟩
  have ht := hTaylor κ hκmem
  have hscale :
      ℓ * (κ - 1) = 2 * (N : ℝ) + 1 := by
    try dsimp [κ, saddleNegativeContourOrdinate]
    field_simp [hℓ.ne']; ring
  have hidentity :
      saddleNegativeContourPhaseError ε ℓ N =
        ℓ *
          (realHyperbolicShellPhase ε κ -
            realHyperbolicShellPhase ε 1 -
              (κ - 1) * saddleShellDerivativeOne ε) := by
    unfold saddleNegativeContourPhaseError
    push_cast
    change
      ℓ * (realHyperbolicShellPhase ε κ -
        realHyperbolicShellPhase ε 1) -
          (2 * (N : ℝ) + 1) * saddleShellDerivativeOne ε = _
    rw [← hscale]
    ring
  rw [hidentity, abs_mul, abs_of_pos hℓ]
  calc
    ℓ *
      |realHyperbolicShellPhase ε κ -
        realHyperbolicShellPhase ε 1 -
          (κ - 1) * saddleShellDerivativeOne ε| ≤
      ℓ * (K * (κ - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left ht hℓ.le
    _ = K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
      rw [← hscale]
      field_simp [hℓ.ne']

private theorem eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a))) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 < r → r ≤ saddleSmallRadiusStar ε d →
        let ℓ : ℝ := (d : ℝ) / 2
        let N : ℕ := saddleSmallResidueTruncation ℓ
        let y : ℝ := saddleSmallRadiusVariable ε r
        Real.exp y *
          ‖plusSaddleTaylorRemainder ε ℓ N r /
            (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2 := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_eventually_y_star_le_log_eighth_add hε horder
  obtain ⟨K, hK, hphase⟩ :=
    exists_saddleNegativeContourPhaseError_bound hε horder
  let Kε : ℝ := saddleNegativeRelativeCoefficient ε
  have hKε : 0 ≤ Kε :=
    saddleNegativeRelativeCoefficient_nonneg hε
  have htail := eventually_saddleNegative_relativeGammaTail_lt_half
    hε C K Kε hC hK hKε
  have htaildim :=
    tendsto_saddleResidue_dimension_half.eventually htail
  have hdepth :=
    tendsto_saddleResidue_dimension_half.eventually
      eventually_saddleSmallResidueTruncation_succ_double_le
  filter_upwards [hstar, htaildim, hdepth,
    eventually_gt_atTop (0 : ℕ)] with d hcut htaild hNd hd
  intro r hr hrstar
  try dsimp
  let ℓ : ℝ := (d : ℝ) / 2
  let N : ℕ := saddleSmallResidueTruncation ℓ
  let y : ℝ := saddleSmallRadiusVariable ε r
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  have hy : 0 ≤ y := saddleSmallRadiusVariable_nonneg ε r
  have hyupper : y ≤ Real.log ℓ / 8 + C := by
    exact hcut r hr.le hrstar
  have hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ := hNd
  have hrelative :=
    plusSaddleTaylorRemainder_negativeContour_relative_bound
      hε hεsmall hℓ N hN horder hmargin hr
  have herr := hphase ℓ hℓ N hN
  have herror :
      saddleNegativeContourPhaseError ε ℓ N ≤
        K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
    exact (le_abs_self _).trans herr
  have htarget := htaild y hy hyupper
  change
    Real.exp y *
      ‖plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2
  calc
    Real.exp y *
      ‖plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ)‖ ≤
      Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N)) := by
      gcongr
    _ ≤ Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp
              (K * (2 * (N : ℝ) + 1) ^ 2 / ℓ)) := by
      gcongr
    _ < 1 / 2 := htarget

private theorem eventually_plusSaddleProfile_re_pos_on_star_fixed
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a))) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
        0 < (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  have hfinite :=
    eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
      hε horder
  have hremainder :=
    eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
      hε hεsmall horder hmargin
  filter_upwards [hfinite, hremainder,
    eventually_gt_atTop (0 : ℕ)] with d hfinite_d hrem_d hd
  intro r hr hrstar
  by_cases hzero : r = 0
  · subst r
    simpa only [plusSaddleProfile, ↓reduceIte, Complex.ofReal_re] using!
      (saddleOriginValue_pos hε ((d : ℝ) / 2))
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    have hℓ : 0 < (d : ℝ) / 2 := by positivity
    exact plusSaddleProfile_re_pos_of_relative_residue_bounds
      hε hℓ horder hrpos
      (saddleSmallResidueTruncation ((d : ℝ) / 2))
      (by simpa only [one_div] using! hfinite_d r hr hrstar)
      (by simpa only [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
        one_div] using! hrem_d r hrpos hrstar)

private theorem eventually_plusSaddleProfile_re_pos_on_star :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          0 < (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by
  have hsmall :=
    (tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  apply eventually_plusSaddleProfile_re_pos_on_star_fixed
    hε (le_of_lt hεsmall) horder
  intro a ha
  have h := hmargin a ha
  linarith

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

private theorem saddleRealCpow_hasDerivAt_zero
    {z : ℂ} (hz : 1 < z.re) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ z)
      (0 : ℂ) (0 : ℝ) := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub : 0 < (z - 1).re := by
    simpa only [Complex.sub_re, Complex.one_re, sub_pos] using! sub_pos.mpr hz
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have := congrArg Complex.re heq
    simpa only  using! (ne_of_gt hsub) this
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have htend :
      Tendsto (fun t : ℝ => (t : ℂ) ^ (z - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcontinuous :=
      Complex.continuousAt_ofReal_cpow_const
        (0 : ℝ) (z - 1) (Or.inl hsub)
    simpa only [Complex.ofReal_zero, Complex.zero_cpow hsub0] using!
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! ht
  have htc : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ht0
  simp only [Complex.cpow_sub z 1 htc, Complex.cpow_one, div_eq_mul_inv, zero_add,
    Complex.ofReal_zero, ne_eq,
    hz0, not_false_eq_true, Complex.zero_cpow, sub_zero, Complex.real_smul, Complex.ofReal_inv,
      mul_comm]

private theorem saddleRealCpow_hasDerivAt
    {z : ℂ} (hz : 1 < z.re) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ z)
      (z * (x : ℂ) ^ (z - 1)) x := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  by_cases hx : x = 0
  · subst x
    have hsub : z - 1 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
      linarith
    simpa only [Complex.ofReal_zero, Complex.zero_cpow hsub, mul_zero] using!
      saddleRealCpow_hasDerivAt_zero hz
  · exact hasDerivAt_ofReal_cpow_const hx hz0

private noncomputable def saddlePositiveCpow (z : ℂ) (x : ℝ) : ℂ :=
  ((max x 0 : ℝ) : ℂ) ^ z

private theorem saddlePositiveCpow_continuous
    {z : ℂ} (hz : 0 < z.re) :
    Continuous (saddlePositiveCpow z) := by
  unfold saddlePositiveCpow
  exact (Complex.continuous_ofReal_cpow_const hz).comp
    (continuous_id.max continuous_const)

private theorem saddlePositiveCpow_hasDerivAt_zero
    {z : ℂ} (hz : 1 < z.re) :
    HasDerivAt (saddlePositiveCpow z)
      (0 : ℂ) (0 : ℝ) := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub : 0 < (z - 1).re := by
    change 0 < z.re - 1
    linarith
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have htend :
      Tendsto (saddlePositiveCpow (z - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcontinuous :=
      (saddlePositiveCpow_continuous hsub).continuousAt
        (x := (0 : ℝ))
    simpa only [saddlePositiveCpow, max_self, Complex.ofReal_zero, Complex.zero_cpow hsub0] using!
        hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply htend.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! ht
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · have hmax : max t 0 = 0 := max_eq_right hneg.le
    simp only [saddlePositiveCpow, hmax, Complex.ofReal_zero, Complex.zero_cpow hsub0, zero_add,
      Complex.zero_cpow hz0, max_self, sub_self, smul_zero]
  · have hmax : max t 0 = t := max_eq_left hpos.le
    have htc : (t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ht0
    simp only [saddlePositiveCpow, hmax, Complex.cpow_sub z 1 htc, Complex.cpow_one,
      div_eq_mul_inv, zero_add,
      max_self, Complex.ofReal_zero, ne_eq, hz0, not_false_eq_true, Complex.zero_cpow, sub_zero,
        Complex.real_smul,
      Complex.ofReal_inv, mul_comm]

private theorem saddlePositiveCpow_hasDerivAt
    {z : ℂ} (hz : 1 < z.re) (x : ℝ) :
    HasDerivAt (saddlePositiveCpow z)
      (z * saddlePositiveCpow (z - 1) x) x := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    norm_num at hz
  have hsub0 : z - 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hevent :
        saddlePositiveCpow z =ᶠ[𝓝 x]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      change y < 0 at hy
      simp only [saddlePositiveCpow, max_eq_right hy.le, Complex.ofReal_zero, Complex.zero_cpow hz0]
    have hvalue : saddlePositiveCpow (z - 1) x = 0 := by
      simp only [saddlePositiveCpow, max_eq_right hneg.le, Complex.ofReal_zero,
        Complex.zero_cpow hsub0]
    simpa only [hvalue, mul_zero] using!
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
        hevent
  · subst x
    simp only [saddlePositiveCpow, max_self, Complex.ofReal_zero, Complex.zero_cpow hsub0, mul_zero,
      saddlePositiveCpow_hasDerivAt_zero hz]
  · have hevent :
        saddlePositiveCpow z =ᶠ[𝓝 x]
          (fun y : ℝ => (y : ℂ) ^ z) := by
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      change 0 < y at hy
      simp only [saddlePositiveCpow, max_eq_left hy.le]
    have hvalue :
        saddlePositiveCpow (z - 1) x =
          (x : ℂ) ^ (z - 1) := by
      simp only [saddlePositiveCpow, max_eq_left hpos.le]
    rw [hvalue]
    exact (saddleRealCpow_hasDerivAt hz x).congr_of_eventuallyEq
      hevent

private noncomputable def saddleContourExponent (a t : ℝ) : ℂ :=
  -(((a : ℂ) + (t : ℂ) * Complex.I) / 2)

@[simp] private theorem saddleContourExponent_re (a t : ℝ) :
    (saddleContourExponent a t).re = -a / 2 := by
  simp only [saddleContourExponent, Complex.neg_re, Complex.div_ofNat_re, Complex.add_re,
    Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  ring

private noncomputable def saddleContourExponentPolynomial (a : ℝ) : Polynomial ℂ :=
  Polynomial.C (-(a : ℂ) / 2) -
    Polynomial.C (Complex.I / 2) * Polynomial.X

private theorem saddleContourExponentPolynomial_eval (a t : ℝ) :
    (saddleContourExponentPolynomial a).eval (t : ℂ) =
      saddleContourExponent a t := by
  simp only [saddleContourExponentPolynomial, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul,
    Polynomial.eval_X, saddleContourExponent]
  ring

private noncomputable def saddleContourFallingPolynomial (a : ℝ) (j : ℕ) :
    Polynomial ℂ :=
  ∏ i ∈ Finset.range j,
    (saddleContourExponentPolynomial a -
      Polynomial.C (i : ℂ))

private theorem saddleContourFallingPolynomial_eval_succ
    (a t : ℝ) (j : ℕ) :
    (saddleContourFallingPolynomial a (j + 1)).eval
        (t : ℂ) =
      (saddleContourFallingPolynomial a j).eval
          (t : ℂ) *
        (saddleContourExponent a t - (j : ℂ)) := by
  simp only [saddleContourFallingPolynomial, map_natCast, Finset.prod_range_succ,
    Polynomial.eval_mul,
    Polynomial.eval_sub, saddleContourExponentPolynomial_eval, Polynomial.eval_natCast]

private theorem saddlePolynomialWeightedData_integrable
    {D : ℝ → ℂ}
    (hD : ∀ j : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ j * D t))
    (P : Polynomial ℂ) :
    Integrable (fun t : ℝ =>
      P.eval (t : ℂ) * D t) := by
  have hsum :
      Integrable (fun t : ℝ =>
        ∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff j * ((t : ℂ) ^ j * D t)) := by
    apply integrable_finsetSum
    intro j _
    exact (hD j).const_mul (P.coeff j)
  exact hsum.congr
    (Filter.Eventually.of_forall (fun t : ℝ => by
      change
        (∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff j * ((t : ℂ) ^ j * D t)) =
            P.eval (t : ℂ) * D t
      rw [Polynomial.eval_eq_sum_range]
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring))

private noncomputable def saddlePositiveContourMoment
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ,
    saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u *
      ((saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t)

private theorem saddleContourExponent_sub_nat_re
    (a t : ℝ) (j : ℕ) :
    (saddleContourExponent a t - (j : ℂ)).re =
      -a / 2 - (j : ℝ) := by
  simp only [Complex.sub_re, saddleContourExponent_re, Complex.natCast_re]

private theorem saddlePositiveCpow_norm_le_one
    {z : ℂ} (hz : 0 < z.re)
    {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖saddlePositiveCpow z u‖ ≤ 1 := by
  have hbase : 0 ≤ max u 0 := le_max_right _ _
  have hbaseone : max u 0 ≤ 1 :=
    max_le hu.2.le (by norm_num)
  unfold saddlePositiveCpow
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg
    hbase (ne_of_gt hz)]
  exact Real.rpow_le_one hbase hbaseone hz.le

private theorem saddlePositiveContourPower_frequency_continuous
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) < -a / 2) (u : ℝ) :
    Continuous (fun t : ℝ =>
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u) := by
  have hfrequency :
      Continuous (fun t : ℝ =>
        saddleContourExponent a t - (j : ℂ)) := by
    unfold saddleContourExponent
    fun_prop
  unfold saddlePositiveCpow
  apply hfrequency.const_cpow
  right
  intro t
  apply ne_of_apply_ne Complex.re
  have hpositive :
      0 < (saddleContourExponent a t - (j : ℂ)).re := by
    rw [saddleContourExponent_sub_nat_re]
    linarith
  simpa only [Complex.sub_re, saddleContourExponent_re, Complex.natCast_re, Complex.zero_re,
    ne_eq] using! hpositive.ne'

private theorem saddlePositiveContourMoment_hasDerivAt
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) + 1 < -a / 2)
    {u : ℝ} (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  let W : ℕ → ℝ → ℂ :=
    fun k t =>
      (saddleContourFallingPolynomial a k).eval
          (t : ℂ) * D t
  have hW (k : ℕ) : Integrable (W k) := by
    try dsimp [W]
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a k)
  have hjpos : (j : ℝ) < -a / 2 := by
    linarith
  have hsuccpos : ((j + 1 : ℕ) : ℝ) < -a / 2 := by
    push_cast
    linarith
  have hkernel (k : ℕ) (hk : (k : ℝ) < -a / 2)
      (v : ℝ) :
      AEStronglyMeasurable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (k : ℂ)) v *
            W k t) :=
    (saddlePositiveContourPower_frequency_continuous
      k hk v).aestronglyMeasurable.mul
        (hW k).aestronglyMeasurable
  have hpoint (v : ℝ)
      (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
      Integrable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t) := by
    apply (hW j).norm.mono'
      (hkernel j hjpos v)
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v‖ *
          ‖W j t‖ ≤ 1 * ‖W j t‖ := by
        gcongr
        apply saddlePositiveCpow_norm_le_one
        · rw [saddleContourExponent_sub_nat_re]
          linarith
        · exact hv
      _ = ‖W j t‖ := one_mul _
  have hdiff (t v : ℝ)
      (hv : v ∈ Set.Ioo (-1 : ℝ) 1) :
      HasDerivAt
        (fun x : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) x *
            W j t)
        (saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t) v := by
    have hreal :
        1 < (saddleContourExponent a t - (j : ℂ)).re := by
      rw [saddleContourExponent_sub_nat_re]
      linarith
    have hderiv :=
      (saddlePositiveCpow_hasDerivAt hreal v).mul_const
        (W j t)
    have harg :
        saddleContourExponent a t - ((j + 1 : ℕ) : ℂ) =
          saddleContourExponent a t - (j : ℂ) - 1 := by
      push_cast
      ring
    have hfall :
        W (j + 1) t =
          W j t * (saddleContourExponent a t - (j : ℂ)) := by
      try dsimp [W]
      rw [saddleContourFallingPolynomial_eval_succ]
      ring
    rw [harg, hfall]
    convert! hderiv using 1
    all_goals ring
  have hresult :=
    _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume)
      (F := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v *
          W j t)
      (F' := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t)
      (bound := fun t : ℝ => ‖W (j + 1) t‖)
      (isOpen_Ioo.mem_nhds hu)
      (Filter.Eventually.of_forall
        (fun v => hkernel j hjpos v))
      (hpoint u hu)
      (hkernel (j + 1) hsuccpos u)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        rw [norm_mul]
        calc
          ‖saddlePositiveCpow
                (saddleContourExponent a t -
                  ((j + 1 : ℕ) : ℂ)) v‖ *
              ‖W (j + 1) t‖ ≤
            1 * ‖W (j + 1) t‖ := by
              gcongr
              apply saddlePositiveCpow_norm_le_one
              · rw [saddleContourExponent_sub_nat_re]
                exact sub_pos.mpr hsuccpos
              · exact hv
          _ = ‖W (j + 1) t‖ := one_mul _))
      ((hW (j + 1)).norm)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        exact hdiff t v hv))
  change
    HasDerivAt
      (fun v : ℝ =>
        ∫ t : ℝ,
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t)
      (∫ t : ℝ,
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) u *
          W (j + 1) t) u
  exact hresult.2

private theorem saddlePositiveContourMoment_contDiffOn
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (n j : ℕ)
    (ha : (n : ℝ) + (j : ℝ) + 1 < -a / 2) :
    ContDiffOn ℝ n
      (saddlePositiveContourMoment a j D)
      (Set.Ioo (-1 : ℝ) 1) := by
  induction n generalizing j with
  | zero =>
      change ContDiffOn ℝ 0
        (saddlePositiveContourMoment a j D)
        (Set.Ioo (-1 : ℝ) 1)
      rw [contDiffOn_zero]
      intro u hu
      have hj : (j : ℝ) + 1 < -a / 2 := by
        simpa only [CharP.cast_eq_zero, zero_add] using! ha
      exact
        (saddlePositiveContourMoment_hasDerivAt
          hD j hj hu).continuousAt.continuousWithinAt
  | succ n ih =>
      have hj : (j : ℝ) + 1 < -a / 2 := by
        push_cast at ha
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hnext :
          (n : ℝ) + ((j + 1 : ℕ) : ℝ) + 1 < -a / 2 := by
        push_cast at ha ⊢
        linarith
      rw [show (↑(n + 1) : WithTop ℕ∞) =
          (↑n : WithTop ℕ∞) + 1 by simp only [Nat.cast_add, Nat.cast_one],
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        exact
          (saddlePositiveContourMoment_hasDerivAt
            hD j hj hu).differentiableAt.differentiableWithinAt
      · simp only [WithTop.natCast_ne_top, IsEmpty.forall_iff]
      · exact (ih (j + 1) hnext).congr
          (fun u hu =>
            (saddlePositiveContourMoment_hasDerivAt
              hD j hj hu).deriv)

private theorem saddleMellinInversePower_eq_squaredPositiveCpow
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    saddleMellinInversePower r z =
      saddlePositiveCpow (-z / 2) (r ^ 2) := by
  unfold saddleMellinInversePower
  calc
    (r : ℂ) ^ (-z) =
      (r : ℂ) ^ (((2 : ℝ) : ℂ) * (-z / 2)) := by
        congr 1
        push_cast
        ring
    _ = (((r ^ (2 : ℝ) : ℝ) : ℂ)) ^ (-z / 2) :=
      Complex.cpow_mul_ofReal_nonneg hr.le 2 (-z / 2)
    _ = saddlePositiveCpow (-z / 2) (r ^ 2) := by
      simp only [Real.rpow_ofNat, Complex.ofReal_pow, saddlePositiveCpow, max_eq_left (sq_nonneg r)]

@[simp] private theorem saddlePositiveContourMoment_zero
    {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) < -a / 2) (D : ℝ → ℂ) :
    saddlePositiveContourMoment a j D 0 = 0 := by
  unfold saddlePositiveContourMoment
  have hzero :
      (fun t : ℝ =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) 0 *
          ((saddleContourFallingPolynomial a j).eval
              (t : ℂ) * D t)) =
        fun _ : ℝ => (0 : ℂ) := by
    funext t
    have hexp :
        saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      have hpositive :
          0 < (saddleContourExponent a t - (j : ℂ)).re := by
        rw [saddleContourExponent_sub_nat_re]
        linarith
      simpa only [Complex.sub_re, saddleContourExponent_re, Complex.natCast_re, Complex.zero_re,
        ne_eq] using! hpositive.ne'
    simp only [saddlePositiveCpow, max_self, Complex.ofReal_zero, Complex.zero_cpow hexp, zero_mul]
  rw [hzero, integral_zero]

private noncomputable def plusSaddleSquaredRemainder
    (ε ℓ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment (saddleTaylorContour N) 0
      (fun t : ℝ =>
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I)) u

private noncomputable def minusSaddleSquaredRemainder
    (ε ℓ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment (saddleTaylorContour N) 0
      (fun t : ℝ =>
        minusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I)) u

private theorem plusSaddleTaylorRemainder_eq_squared
    (ε ℓ : ℝ) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    plusSaddleTaylorRemainder ε ℓ N r =
      plusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  unfold plusSaddleTaylorRemainder
    plusSaddleSquaredRemainder
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((saddleTaylorContour N : ℂ) +
      (t : ℂ) * Complex.I)]
  have hq :
      -((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent (saddleTaylorContour N) t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp only [CharP.cast_eq_zero, sub_zero, saddleContourFallingPolynomial, Finset.range_zero,
    map_natCast,
    Finset.prod_empty, Polynomial.eval_one, one_mul]

private theorem minusSaddleTaylorRemainder_eq_squared
    (ε ℓ : ℝ) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    minusSaddleTaylorRemainder ε ℓ N r =
      minusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  unfold minusSaddleTaylorRemainder
    minusSaddleSquaredRemainder
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((saddleTaylorContour N : ℂ) +
      (t : ℂ) * Complex.I)]
  have hq :
      -((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent (saddleTaylorContour N) t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp only [CharP.cast_eq_zero, sub_zero, saddleContourFallingPolynomial, Finset.range_zero,
    map_natCast,
    Finset.prod_empty, Polynomial.eval_one, one_mul]

private theorem plusSaddleSquaredRemainder_contDiffOn
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (n N : ℕ)
    (hshift : (n : ℝ) + 1 <
      -(saddleTaylorContour N) / 2) :
    ContDiffOn ℝ n
      (plusSaddleSquaredRemainder ε ℓ N)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hmoment :
      ∀ k : ℕ,
        Integrable (fun t : ℝ =>
          (t : ℂ) ^ k *
            plusSaddleMellinData ε ℓ
              ((saddleTaylorContour N : ℂ) +
                (t : ℂ) * Complex.I)) := by
    intro k
    exact plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun j : ℕ => saddleTaylorContour_ne_pole N j) k
  have hsmooth :=
    saddlePositiveContourMoment_contDiffOn hmoment
      n 0 (by simpa only [CharP.cast_eq_zero, add_zero] using! hshift)
  exact (contDiff_const.contDiffOn.mul hsmooth)

private theorem minusSaddleSquaredRemainder_contDiffOn
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (n N : ℕ)
    (hshift : (n : ℝ) + 1 <
      -(saddleTaylorContour N) / 2) :
    ContDiffOn ℝ n
      (minusSaddleSquaredRemainder ε ℓ N)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hmoment :
      ∀ k : ℕ,
        Integrable (fun t : ℝ =>
          (t : ℂ) ^ k *
            minusSaddleMellinData ε ℓ
              ((saddleTaylorContour N : ℂ) +
                (t : ℂ) * Complex.I)) := by
    intro k
    exact minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun j : ℕ => saddleTaylorContour_ne_pole N j) k
  have hsmooth :=
    saddlePositiveContourMoment_contDiffOn hmoment
      n 0 (by simpa only [CharP.cast_eq_zero, add_zero] using! hshift)
  exact (contDiff_const.contDiffOn.mul hsmooth)

private noncomputable def saddleSquaredResiduePolynomial
    (c : ℕ → ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    c j * ((u : ℂ) ^ j)

private theorem saddleTaylorContour_negativeHalf_pos (N : ℕ) :
    0 < -(saddleTaylorContour N) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  positivity

@[simp] private theorem saddleSquaredResiduePolynomial_zero
    (c : ℕ → ℂ) (N : ℕ) :
    saddleSquaredResiduePolynomial c N 0 = c 0 := by
  classical
  unfold saddleSquaredResiduePolynomial
  rw [Finset.sum_eq_single 0]
  · simp only [Complex.ofReal_zero, pow_zero, mul_one]
  · intro j _ hj
    simp only [Complex.ofReal_zero, zero_pow hj, mul_zero]
  · simp only [Finset.mem_range, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    not_true_eq_false,
      Complex.ofReal_zero, pow_zero, mul_one, IsEmpty.forall_iff]

private theorem saddleSquaredResiduePolynomial_contDiff
    (c : ℕ → ℂ) (N n : ℕ) :
    ContDiff ℝ n (saddleSquaredResiduePolynomial c N) := by
  unfold saddleSquaredResiduePolynomial
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul
    (Complex.ofRealCLM.contDiff.pow j)

@[simp] private theorem plusSaddleSquaredRemainder_zero
    (ε ℓ : ℝ) (N : ℕ) :
    plusSaddleSquaredRemainder ε ℓ N 0 = 0 := by
  unfold plusSaddleSquaredRemainder
  rw [saddlePositiveContourMoment_zero 0
    (by simpa only [CharP.cast_eq_zero, Nat.ofNat_pos, div_pos_iff_of_pos_right,
      Left.neg_pos_iff] using! saddleTaylorContour_negativeHalf_pos N)]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    mul_zero]

@[simp] private theorem minusSaddleSquaredRemainder_zero
    (ε ℓ : ℝ) (N : ℕ) :
    minusSaddleSquaredRemainder ε ℓ N 0 = 0 := by
  unfold minusSaddleSquaredRemainder
  rw [saddlePositiveContourMoment_zero 0
    (by simpa only [CharP.cast_eq_zero, Nat.ofNat_pos, div_pos_iff_of_pos_right,
      Left.neg_pos_iff] using! saddleTaylorContour_negativeHalf_pos N)]
  simp only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
    mul_zero]

private theorem plusSaddleProfile_eq_squaredTaylor
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    plusSaddleProfile ε ℓ r =
      saddleSquaredResiduePolynomial
        (plusSaddlePoleResidue ε ℓ) N (r ^ 2) +
      plusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  rcases hr.eq_or_lt with hzero | hpositive
  · subst r
    simp only [plusSaddleProfile, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow,
      saddleSquaredResiduePolynomial_zero, plusSaddlePoleResidue_zero hℓ,
        plusSaddleSquaredRemainder_zero, add_zero]
  · rw [plusSaddleProfile_eq_residue_sum_add_remainder
      hε hℓ horder hpositive N,
      plusSaddleTaylorRemainder_eq_squared
        ε ℓ N hpositive]
    congr 1
    unfold saddleSquaredResiduePolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    rw [← pow_mul]

private theorem minusSaddleProfile_eq_squaredTaylor
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    minusSaddleProfile ε ℓ r =
      saddleSquaredResiduePolynomial
        (minusSaddlePoleResidue ε ℓ) N (r ^ 2) +
      minusSaddleSquaredRemainder ε ℓ N (r ^ 2) := by
  rcases hr.eq_or_lt with hzero | hpositive
  · subst r
    simp only [minusSaddleProfile, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow,
      saddleSquaredResiduePolynomial_zero, minusSaddlePoleResidue_zero hℓ,
        minusSaddleSquaredRemainder_zero, add_zero]
  · rw [minusSaddleProfile_eq_residue_sum_add_remainder
      hε hℓ horder hpositive N,
      minusSaddleTaylorRemainder_eq_squared
        ε ℓ N hpositive]
    congr 1
    unfold saddleSquaredResiduePolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    rw [← pow_mul]

private theorem saddleTaylorContour_smoothShift (n : ℕ) :
    (n : ℝ) + 1 <
      -(saddleTaylorContour (n + 2)) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  push_cast
  linarith

private theorem plusSaddleFunction_contDiff_nat
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (n : ℕ) :
    ContDiff ℝ n (plusSaddleFunction ε d) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    let N : ℕ := n + 2
    have hshift :
        (n : ℝ) + 1 <
          -(saddleTaylorContour N) / 2 := by
      exact saddleTaylorContour_smoothShift n
    have hremScalar :
        ContDiffAt ℝ n
          (plusSaddleSquaredRemainder
            ε ((d : ℝ) / 2) N)
          (‖(0 : Euclidean d)‖ ^ 2) := by
      simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using!
        (plusSaddleSquaredRemainder_contDiffOn
          hε hdimension horder n N hshift).contDiffAt
            (isOpen_Ioo.mem_nhds
              (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by
                constructor <;> norm_num))
    have hrem :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            plusSaddleSquaredRemainder
              ε ((d : ℝ) / 2) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      hremScalar.fun_comp
        (f := fun y : Euclidean d => ‖y‖ ^ 2)
        (0 : Euclidean d)
        (contDiff_norm_sq ℝ).contDiffAt
    have hpoly :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            saddleSquaredResiduePolynomial
              (plusSaddlePoleResidue
                ε ((d : ℝ) / 2)) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      (saddleSquaredResiduePolynomial_contDiff
        (plusSaddlePoleResidue ε ((d : ℝ) / 2))
          N n).contDiffAt.fun_comp
            (f := fun y : Euclidean d => ‖y‖ ^ 2)
            (0 : Euclidean d)
            (contDiff_norm_sq ℝ).contDiffAt
    refine (hpoly.add hrem).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y : Euclidean d => ?_))
    exact plusSaddleProfile_eq_squaredTaylor
      hε hdimension horder N (norm_nonneg y)
  · exact
      ((plusSaddleFunction_contDiffOn hε hd horder).contDiffAt
          ((isOpen_compl_singleton
            (x := (0 : Euclidean d))).mem_nhds
              (by simpa only [mem_compl_iff, mem_singleton_iff] using! hx))).of_le
                (mod_cast le_top)

private theorem minusSaddleFunction_contDiff_nat
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (n : ℕ) :
    ContDiff ℝ n (minusSaddleFunction ε d) := by
  have hdimension : 0 < (d : ℝ) / 2 :=
    div_pos (by exact_mod_cast hd) (by norm_num)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    let N : ℕ := n + 2
    have hshift :
        (n : ℝ) + 1 <
          -(saddleTaylorContour N) / 2 := by
      exact saddleTaylorContour_smoothShift n
    have hremScalar :
        ContDiffAt ℝ n
          (minusSaddleSquaredRemainder
            ε ((d : ℝ) / 2) N)
          (‖(0 : Euclidean d)‖ ^ 2) := by
      simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using!
        (minusSaddleSquaredRemainder_contDiffOn
          hε hdimension horder n N hshift).contDiffAt
            (isOpen_Ioo.mem_nhds
              (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by
                constructor <;> norm_num))
    have hrem :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            minusSaddleSquaredRemainder
              ε ((d : ℝ) / 2) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      hremScalar.fun_comp
        (f := fun y : Euclidean d => ‖y‖ ^ 2)
        (0 : Euclidean d)
        (contDiff_norm_sq ℝ).contDiffAt
    have hpoly :
        ContDiffAt ℝ n
          (fun y : Euclidean d =>
            saddleSquaredResiduePolynomial
              (minusSaddlePoleResidue
                ε ((d : ℝ) / 2)) N (‖y‖ ^ 2))
          (0 : Euclidean d) :=
      (saddleSquaredResiduePolynomial_contDiff
        (minusSaddlePoleResidue ε ((d : ℝ) / 2))
          N n).contDiffAt.fun_comp
            (f := fun y : Euclidean d => ‖y‖ ^ 2)
            (0 : Euclidean d)
            (contDiff_norm_sq ℝ).contDiffAt
    refine (hpoly.add hrem).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y : Euclidean d => ?_))
    exact minusSaddleProfile_eq_squaredTaylor
      hε hdimension horder N (norm_nonneg y)
  · exact
      ((minusSaddleFunction_contDiffOn hε hd horder).contDiffAt
          ((isOpen_compl_singleton
            (x := (0 : Euclidean d))).mem_nhds
              (by simpa only [mem_compl_iff, mem_singleton_iff] using! hx))).of_le
                (mod_cast le_top)

private theorem plusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (plusSaddleFunction ε d) := by
  exact contDiff_infty.mpr
    (fun n => plusSaddleFunction_contDiff_nat
      hε hd horder n)

private theorem minusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (minusSaddleFunction ε d) := by
  exact contDiff_infty.mpr
    (fun n => minusSaddleFunction_contDiff_nat
      hε hd horder n)

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology

private theorem saddleRightHalfPlane_boundary_rectangle
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re})
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (T : ℝ) :
    (∫ a in A..B,
      F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
    (∫ a in A..B,
      F ((a : ℂ) + (T : ℂ) * Complex.I)) +
    Complex.I *
      (∫ t in -T..T,
        F ((B : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I *
      (∫ t in -T..T,
        F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  let z : ℂ :=
    (A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I
  let w : ℂ :=
    (B : ℂ) + (T : ℂ) * Complex.I
  have hrect :
      DifferentiableOn ℂ F
        (Complex.reProdIm
          [[z.re, w.re]] [[z.im, w.im]]) := by
    apply hF.mono
    intro u hu
    have hre : u.re ∈ [[z.re, w.re]] :=
      (Complex.mem_reProdIm.mp hu).1
    rcases Set.mem_uIcc.mp hre with hleft | hright
    · have hza : z.re = A := by
        simp only [Complex.ofReal_neg, neg_mul, Complex.add_re, Complex.ofReal_re,
          Complex.neg_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
            add_zero, z]
      rw [hza] at hleft
      exact hA.trans_le hleft.1
    · have hwb : w.re = B := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im,
          Complex.I_im, mul_one, sub_self, add_zero, w]
      rw [hwb] at hright
      exact hB.trans_le hright.1
  have h :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      F z w hrect
  simpa [z, w, Complex.mul_re, Complex.mul_im,
    smul_eq_mul] using! h

private theorem plusSaddleMellinData_positive_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℂ → ℂ := fun z =>
    saddleMellinInversePower r z *
      plusSaddleMellinData ε ℓ z
  have hhol :
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} :=
    (saddleMellinInversePower_differentiable
      hr).differentiableOn.mul
        (plusSaddleMellinData_differentiableOn_rightHalfPlane
          hε horder ℓ)
  have hleft :
      Integrable (fun t : ℝ =>
        F ((A : ℂ) + (t : ℂ) * Complex.I)) :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hA n) hr
  have hright :
      Integrable (fun t : ℝ =>
        F ((B : ℂ) + (t : ℂ) * Complex.I)) :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hB n) hr
  have hlower :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, one_mul] using!
      plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB (-1) (by norm_num)
  have hupper :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + (T : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa only [one_mul] using!
      plusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T => saddleRightHalfPlane_boundary_rectangle
      hhol hA hB T)

private theorem minusSaddleMellinData_positive_vertical_integral_eq
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r)
    (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℂ → ℂ := fun z =>
    saddleMellinInversePower r z *
      minusSaddleMellinData ε ℓ z
  have hhol :
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} :=
    (saddleMellinInversePower_differentiable
      hr).differentiableOn.mul
        (minusSaddleMellinData_differentiableOn_rightHalfPlane
          hε horder ℓ)
  have hleft :
      Integrable (fun t : ℝ =>
        F ((A : ℂ) + (t : ℂ) * Complex.I)) :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hA n) hr
  have hright :
      Integrable (fun t : ℝ =>
        F ((B : ℂ) + (t : ℂ) * Complex.I)) :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole hB n) hr
  have hlower :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, one_mul] using!
      minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB (-1) (by norm_num)
  have hupper :
      Tendsto
        (fun T : ℝ =>
          ∫ a in A..B,
            F ((a : ℂ) + (T : ℂ) * Complex.I))
        Filter.atTop (𝓝 0) := by
    simpa only [one_mul] using!
      minusSaddleMellinData_weighted_horizontalIntegral_tendsto_zero
        hε hℓ horder hr hAB 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T => saddleRightHalfPlane_boundary_rectangle
      hhol hA hB T)

private theorem plusSaddleProfile_eq_positive_contour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (ha : 0 < a) :
    plusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [plusSaddleProfile_eq_normalized_vertical_integral hr]
  congr 1
  rcases le_total ℓ a with hleft | hright
  · exact
      (plusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr hℓ ha hleft).symm
  · exact
      plusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr ha hℓ hright

private theorem minusSaddleProfile_eq_positive_contour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (ha : 0 < a) :
    minusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [minusSaddleProfile_eq_normalized_vertical_integral hr]
  congr 1
  rcases le_total ℓ a with hleft | hright
  · exact
      (minusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr hℓ ha hleft).symm
  · exact
      minusSaddleMellinData_positive_vertical_integral_eq
        hε hℓ horder hr ha hℓ hright

private noncomputable def plusSaddlePositiveSquaredContour
    (ε ℓ a u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment a 0
      (fun t : ℝ =>
        plusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) u

private noncomputable def minusSaddlePositiveSquaredContour
    (ε ℓ a u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    saddlePositiveContourMoment a 0
      (fun t : ℝ =>
        minusSaddleMellinData ε ℓ
          ((a : ℂ) + (t : ℂ) * Complex.I)) u

private theorem plusSaddleProfile_eq_positive_squaredContour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (ha : 0 < a) :
    plusSaddleProfile ε ℓ r =
      plusSaddlePositiveSquaredContour ε ℓ a (r ^ 2) := by
  rw [plusSaddleProfile_eq_positive_contour
    hε hℓ horder hr ha]
  unfold plusSaddlePositiveSquaredContour
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((a : ℂ) + (t : ℂ) * Complex.I)]
  have hq :
      -((a : ℂ) + (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent a t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp only [CharP.cast_eq_zero, sub_zero, saddleContourFallingPolynomial, Finset.range_zero,
    map_natCast,
    Finset.prod_empty, Polynomial.eval_one, one_mul]

private theorem minusSaddleProfile_eq_positive_squaredContour
    {ε ℓ r a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (ha : 0 < a) :
    minusSaddleProfile ε ℓ r =
      minusSaddlePositiveSquaredContour ε ℓ a (r ^ 2) := by
  rw [minusSaddleProfile_eq_positive_contour
    hε hℓ horder hr ha]
  unfold minusSaddlePositiveSquaredContour
    saddlePositiveContourMoment
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [saddleMellinInversePower_eq_squaredPositiveCpow
    hr ((a : ℂ) + (t : ℂ) * Complex.I)]
  have hq :
      -((a : ℂ) + (t : ℂ) * Complex.I) / 2 =
        saddleContourExponent a t := by
    unfold saddleContourExponent
    ring
  rw [hq]
  simp only [CharP.cast_eq_zero, sub_zero, saddleContourFallingPolynomial, Finset.range_zero,
    map_natCast,
    Finset.prod_empty, Polynomial.eval_one, one_mul]

private theorem saddlePositiveCpow_hasDerivAt_of_pos
    {z : ℂ} (hz : z ≠ 0)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (saddlePositiveCpow z)
      (z * saddlePositiveCpow (z - 1) u) u := by
  have hevent :
      saddlePositiveCpow z =ᶠ[𝓝 u]
        (fun v : ℝ => (v : ℂ) ^ z) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    change 0 < v at hv
    simp only [saddlePositiveCpow, max_eq_left hv.le]
  have hvalue :
      saddlePositiveCpow (z - 1) u =
        (u : ℂ) ^ (z - 1) := by
    simp only [saddlePositiveCpow, max_eq_left hu.le]
  rw [hvalue]
  exact
    (hasDerivAt_ofReal_cpow_const hu.ne' hz).congr_of_eventuallyEq
      hevent

private theorem saddlePositiveContourPower_frequency_continuous_of_pos
    (a : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    Continuous (fun t : ℝ =>
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u) := by
  have hfrequency :
      Continuous (fun t : ℝ =>
        saddleContourExponent a t - (j : ℂ)) := by
    unfold saddleContourExponent
    fun_prop
  unfold saddlePositiveCpow
  apply hfrequency.const_cpow
  left
  rw [max_eq_left hu.le]
  exact Complex.ofReal_ne_zero.mpr hu.ne'

private theorem saddlePositiveCpow_norm_le_one_of_nonpos
    {z : ℂ} (hz : z.re ≤ 0)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    ‖saddlePositiveCpow z u‖ ≤ 1 := by
  have hupos : 0 < u := lt_trans zero_lt_one hu
  unfold saddlePositiveCpow
  rw [max_eq_left hupos.le,
    Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu.le hz

private theorem saddlePositiveContourMoment_hasDerivAt_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (j : ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  let W : ℕ → ℝ → ℂ :=
    fun k t =>
      (saddleContourFallingPolynomial a k).eval
          (t : ℂ) * D t
  have hW (k : ℕ) : Integrable (W k) := by
    try dsimp [W]
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a k)
  have hupos : 0 < u := lt_trans zero_lt_one hu
  have hkernel (k : ℕ) (v : ℝ) (hv : 0 < v) :
      AEStronglyMeasurable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (k : ℂ)) v *
            W k t) :=
    (saddlePositiveContourPower_frequency_continuous_of_pos
      a k hv).aestronglyMeasurable.mul
        (hW k).aestronglyMeasurable
  have hpower (k : ℕ) (t : ℝ) :
      (saddleContourExponent a t - (k : ℂ)).re ≤ 0 := by
    rw [saddleContourExponent_sub_nat_re]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hpoint (v : ℝ)
      (hv : v ∈ Set.Ioi (1 : ℝ)) :
      Integrable
        (fun t : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t) := by
    apply (hW j).norm.mono'
      (hkernel j v (lt_trans zero_lt_one hv))
    filter_upwards [] with t
    rw [norm_mul]
    calc
      ‖saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v‖ *
          ‖W j t‖ ≤ 1 * ‖W j t‖ := by
        gcongr
        exact saddlePositiveCpow_norm_le_one_of_nonpos
          (hpower j t) hv
      _ = ‖W j t‖ := one_mul _
  have hdiff (t v : ℝ)
      (hv : v ∈ Set.Ioi (1 : ℝ)) :
      HasDerivAt
        (fun x : ℝ =>
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) x *
            W j t)
        (saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t) v := by
    have hnonzero :
        saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      apply ne_of_apply_ne Complex.re
      rw [saddleContourExponent_sub_nat_re]
      have hk : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hneg : -a / 2 - (j : ℝ) < 0 := by
        linarith
      simpa only [Complex.zero_re, ne_eq] using! hneg.ne
    have hderiv :=
      (saddlePositiveCpow_hasDerivAt_of_pos
        hnonzero (lt_trans zero_lt_one hv)).mul_const
          (W j t)
    have harg :
        saddleContourExponent a t - ((j + 1 : ℕ) : ℂ) =
          saddleContourExponent a t - (j : ℂ) - 1 := by
      push_cast
      ring
    have hfall :
        W (j + 1) t =
          W j t * (saddleContourExponent a t - (j : ℂ)) := by
      try dsimp [W]
      rw [saddleContourFallingPolynomial_eval_succ]
      ring
    rw [harg, hfall]
    convert! hderiv using 1
    all_goals ring
  have hmeas :
      ∀ᶠ v in 𝓝 u,
        AEStronglyMeasurable
          (fun t : ℝ =>
            saddlePositiveCpow
                (saddleContourExponent a t - (j : ℂ)) v *
              W j t) := by
    filter_upwards [Ioi_mem_nhds hupos] with v hv
    exact hkernel j v hv
  have hresult :=
    _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume)
      (F := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - (j : ℂ)) v *
          W j t)
      (F' := fun (v : ℝ) (t : ℝ) =>
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
          W (j + 1) t)
      (bound := fun t : ℝ => ‖W (j + 1) t‖)
      (isOpen_Ioi.mem_nhds hu)
      hmeas
      (hpoint u hu)
      (hkernel (j + 1) u hupos)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        rw [norm_mul]
        calc
          ‖saddlePositiveCpow
                (saddleContourExponent a t -
                  ((j + 1 : ℕ) : ℂ)) v‖ *
              ‖W (j + 1) t‖ ≤
            1 * ‖W (j + 1) t‖ := by
              gcongr
              exact saddlePositiveCpow_norm_le_one_of_nonpos
                (hpower (j + 1) t) hv
          _ = ‖W (j + 1) t‖ := one_mul _))
      ((hW (j + 1)).norm)
      (Filter.Eventually.of_forall (fun t => by
        intro v hv
        exact hdiff t v hv))
  change
    HasDerivAt
      (fun v : ℝ =>
        ∫ t : ℝ,
          saddlePositiveCpow
              (saddleContourExponent a t - (j : ℂ)) v *
            W j t)
      (∫ t : ℝ,
        saddlePositiveCpow
            (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) u *
          W (j + 1) t) u
  exact hresult.2

private theorem saddlePositiveContourMoment_contDiffOn_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (n j : ℕ) :
    ContDiffOn ℝ n
      (saddlePositiveContourMoment a j D)
      (Set.Ioi (1 : ℝ)) := by
  induction n generalizing j with
  | zero =>
      change ContDiffOn ℝ 0
        (saddlePositiveContourMoment a j D)
        (Set.Ioi (1 : ℝ))
      rw [contDiffOn_zero]
      intro u hu
      exact
        (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
          hD ha j hu).continuousAt.continuousWithinAt
  | succ n ih =>
      rw [show (↑(n + 1) : WithTop ℕ∞) =
          (↑n : WithTop ℕ∞) + 1 by simp only [Nat.cast_add, Nat.cast_one],
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro u hu
        exact
          (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
            hD ha j hu).differentiableAt.differentiableWithinAt
      · simp only [WithTop.natCast_ne_top, IsEmpty.forall_iff]
      · exact (ih (j + 1)).congr
          (fun u hu =>
            (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
              hD ha j hu).deriv)

private theorem saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ContDiffOn ℝ ∞
      (saddlePositiveContourMoment a j D)
      (Set.Ioi (1 : ℝ)) := by
  rw [contDiffOn_infty]
  exact fun n =>
    saddlePositiveContourMoment_contDiffOn_of_positiveContour
      hD ha n j

private theorem saddlePositiveContourMoment_iteratedDeriv_of_positiveContour
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    {a : ℝ} (ha : 0 < a) (n j : ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioi (1 : ℝ)) :
    iteratedDeriv n (saddlePositiveContourMoment a j D) u =
      saddlePositiveContourMoment a (j + n) D u := by
  induction n generalizing j u with
  | zero => simp only [iteratedDeriv_zero, add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hevent :
          deriv (saddlePositiveContourMoment a j D) =ᶠ[𝓝 u]
            saddlePositiveContourMoment a (j + 1) D := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact
          (saddlePositiveContourMoment_hasDerivAt_of_positiveContour
            hD ha j hv).deriv
      rw [hevent.iteratedDeriv_eq n]
      simpa only [Nat.add_left_comm, Nat.add_comm] using! ih (j + 1) hu

private noncomputable def saddleContourMomentL1
    (a : ℝ) (j : ℕ) (D : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ,
    ‖(saddleContourFallingPolynomial a j).eval
        (t : ℂ) * D t‖

private theorem saddlePositiveContourMoment_norm_le
    {D : ℝ → ℂ}
    (hD : ∀ k : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ k * D t))
    (a : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖saddlePositiveContourMoment a j D u‖ ≤
      u ^ (-a / 2 - (j : ℝ)) *
        saddleContourMomentL1 a j D := by
  let W : ℝ → ℂ := fun t =>
    (saddleContourFallingPolynomial a j).eval
      (t : ℂ) * D t
  have hW : Integrable W := by
    exact saddlePolynomialWeightedData_integrable hD
      (saddleContourFallingPolynomial a j)
  unfold saddlePositiveContourMoment saddleContourMomentL1
  calc
    ‖∫ t : ℝ,
      saddlePositiveCpow
        (saddleContourExponent a t - (j : ℂ)) u *
        ((saddleContourFallingPolynomial a j).eval
          (t : ℂ) * D t)‖ ≤
      ∫ t : ℝ,
        ‖saddlePositiveCpow
          (saddleContourExponent a t - (j : ℂ)) u *
          ((saddleContourFallingPolynomial a j).eval
            (t : ℂ) * D t)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ,
        u ^ (-a / 2 - (j : ℝ)) *
          ‖(saddleContourFallingPolynomial a j).eval
            (t : ℂ) * D t‖ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          rw [norm_mul]
          congr 1
          unfold saddlePositiveCpow
          rw [max_eq_left hu.le,
            Complex.norm_cpow_eq_rpow_re_of_pos hu,
            saddleContourExponent_sub_nat_re]
    _ = u ^ (-a / 2 - (j : ℝ)) *
          (∫ t : ℝ,
            ‖(saddleContourFallingPolynomial a j).eval
              (t : ℂ) * D t‖) := by
          exact integral_const_mul_of_integrable hW.norm

private theorem plusSaddlePositiveSquaredContour_contDiffOn
    {ε ℓ a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) :
    ContDiffOn ℝ ∞
      (plusSaddlePositiveSquaredContour ε ℓ a)
      (Set.Ioi (1 : ℝ)) := by
  unfold plusSaddlePositiveSquaredContour
  apply contDiffOn_const.mul
  apply saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
      (a := a) (j := 0) _ ha
  intro k
  exact plusSaddleMellinData_shiftedLine_moment_integrable
    hε hℓ horder
    (fun n => saddlePositiveContour_ne_pole ha n) k

private theorem minusSaddlePositiveSquaredContour_contDiffOn
    {ε ℓ a : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) :
    ContDiffOn ℝ ∞
      (minusSaddlePositiveSquaredContour ε ℓ a)
      (Set.Ioi (1 : ℝ)) := by
  unfold minusSaddlePositiveSquaredContour
  apply contDiffOn_const.mul
  apply saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour
      (a := a) (j := 0) _ ha
  intro k
  exact minusSaddleMellinData_shiftedLine_moment_integrable
    hε hℓ horder
    (fun n => saddlePositiveContour_ne_pole ha n) k

private theorem plusSaddlePositiveSquaredContour_eq_of_pos
    {ε ℓ a b u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    plusSaddlePositiveSquaredContour ε ℓ a u =
      plusSaddlePositiveSquaredContour ε ℓ b u := by
  have hroot : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsquare : (Real.sqrt u) ^ 2 = u :=
    Real.sq_sqrt hu.le
  calc
    plusSaddlePositiveSquaredContour ε ℓ a u =
      plusSaddlePositiveSquaredContour ε ℓ a
        ((Real.sqrt u) ^ 2) := by rw [hsquare]
    _ = plusSaddleProfile ε ℓ (Real.sqrt u) :=
      (plusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot ha).symm
    _ = plusSaddlePositiveSquaredContour ε ℓ b
        ((Real.sqrt u) ^ 2) :=
      plusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot hb
    _ = plusSaddlePositiveSquaredContour ε ℓ b u := by
      rw [hsquare]

private theorem minusSaddlePositiveSquaredContour_eq_of_pos
    {ε ℓ a b u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    minusSaddlePositiveSquaredContour ε ℓ a u =
      minusSaddlePositiveSquaredContour ε ℓ b u := by
  have hroot : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsquare : (Real.sqrt u) ^ 2 = u :=
    Real.sq_sqrt hu.le
  calc
    minusSaddlePositiveSquaredContour ε ℓ a u =
      minusSaddlePositiveSquaredContour ε ℓ a
        ((Real.sqrt u) ^ 2) := by rw [hsquare]
    _ = minusSaddleProfile ε ℓ (Real.sqrt u) :=
      (minusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot ha).symm
    _ = minusSaddlePositiveSquaredContour ε ℓ b
        ((Real.sqrt u) ^ 2) :=
      minusSaddleProfile_eq_positive_squaredContour
        hε hℓ horder hroot hb
    _ = minusSaddlePositiveSquaredContour ε ℓ b u := by
      rw [hsquare]

private noncomputable def saddleOuterCutoff (u : ℝ) : ℂ :=
  (Real.smoothTransition (u - 2) : ℂ)

private theorem saddleOuterCutoff_contDiff :
    ContDiff ℝ ∞ saddleOuterCutoff := by
  unfold saddleOuterCutoff
  exact Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp
      (contDiff_id.sub contDiff_const))

private noncomputable def plusSaddleOuterSquaredProfile (ε ℓ u : ℝ) : ℂ :=
  saddleOuterCutoff u *
    plusSaddlePositiveSquaredContour ε ℓ 2 u

private noncomputable def minusSaddleOuterSquaredProfile (ε ℓ u : ℝ) : ℂ :=
  saddleOuterCutoff u *
    minusSaddlePositiveSquaredContour ε ℓ 2 u

private theorem plusSaddleOuterSquaredProfile_contDiff
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (plusSaddleOuterSquaredProfile ε ℓ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u < (2 : ℝ)
  · have hevent :
        plusSaddleOuterSquaredProfile ε ℓ =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      change v < 2 at hv
      have hvzero :
          Real.smoothTransition (v - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp only [plusSaddleOuterSquaredProfile, saddleOuterCutoff, hvzero, Complex.ofReal_zero,
        zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · have hone : u ∈ Set.Ioi (1 : ℝ) := by
      change 1 < u
      linarith
    have hcontour :
        ContDiffAt ℝ ∞
          (plusSaddlePositiveSquaredContour ε ℓ 2) u :=
      (plusSaddlePositiveSquaredContour_contDiffOn
        hε hℓ horder (by norm_num)).contDiffAt
          (isOpen_Ioi.mem_nhds hone)
    exact saddleOuterCutoff_contDiff.contDiffAt.mul hcontour

private theorem minusSaddleOuterSquaredProfile_contDiff
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    ContDiff ℝ ∞ (minusSaddleOuterSquaredProfile ε ℓ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u < (2 : ℝ)
  · have hevent :
        minusSaddleOuterSquaredProfile ε ℓ =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      change v < 2 at hv
      have hvzero :
          Real.smoothTransition (v - 2) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp only [minusSaddleOuterSquaredProfile, saddleOuterCutoff, hvzero, Complex.ofReal_zero,
        zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · have hone : u ∈ Set.Ioi (1 : ℝ) := by
      change 1 < u
      linarith
    have hcontour :
        ContDiffAt ℝ ∞
          (minusSaddlePositiveSquaredContour ε ℓ 2) u :=
      (minusSaddlePositiveSquaredContour_contDiffOn
        hε hℓ horder (by norm_num)).contDiffAt
          (isOpen_Ioi.mem_nhds hone)
    exact saddleOuterCutoff_contDiff.contDiffAt.mul hcontour

private theorem plusSaddleOuterSquaredProfile_eq_zero
    (ε ℓ : ℝ) {u : ℝ} (hu : u < 2) :
    plusSaddleOuterSquaredProfile ε ℓ u = 0 := by
  have hcut : Real.smoothTransition (u - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [plusSaddleOuterSquaredProfile, saddleOuterCutoff, hcut, Complex.ofReal_zero, zero_mul]

private theorem minusSaddleOuterSquaredProfile_eq_zero
    (ε ℓ : ℝ) {u : ℝ} (hu : u < 2) :
    minusSaddleOuterSquaredProfile ε ℓ u = 0 := by
  have hcut : Real.smoothTransition (u - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp only [minusSaddleOuterSquaredProfile, saddleOuterCutoff, hcut, Complex.ofReal_zero, zero_mul]

private theorem plusSaddleOuterSquaredProfile_eq_positiveContour
    {ε ℓ a u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) (hu : 3 < u) :
    plusSaddleOuterSquaredProfile ε ℓ u =
      plusSaddlePositiveSquaredContour ε ℓ a u := by
  have hcut : Real.smoothTransition (u - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold plusSaddleOuterSquaredProfile saddleOuterCutoff
  rw [hcut]
  norm_num
  exact plusSaddlePositiveSquaredContour_eq_of_pos
    hε hℓ horder (by norm_num) ha (by linarith)

private theorem minusSaddleOuterSquaredProfile_eq_positiveContour
    {ε ℓ a u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (ha : 0 < a) (hu : 3 < u) :
    minusSaddleOuterSquaredProfile ε ℓ u =
      minusSaddlePositiveSquaredContour ε ℓ a u := by
  have hcut : Real.smoothTransition (u - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold minusSaddleOuterSquaredProfile saddleOuterCutoff
  rw [hcut]
  norm_num
  exact minusSaddlePositiveSquaredContour_eq_of_pos
    hε hℓ horder (by norm_num) ha (by linarith)

private theorem saddleOuterSquaredProfile_schwartz_decay
    {G : ℝ → ℂ}
    (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ u : ℝ, u < 2 → G u = 0)
    (D : ℝ → ℝ → ℂ)
    (hD : ∀ a : ℝ, 0 < a → ∀ j : ℕ,
      Integrable (fun t : ℝ => (t : ℂ) ^ j * D a t))
    (htail : ∀ a : ℝ, 0 < a → ∀ u : ℝ, 3 < u →
      G u =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          saddlePositiveContourMoment a 0 (D a) u)
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤ C := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let a : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hcontinuous :
      Continuous (fun u : ℝ =>
        ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖) := by
    apply Continuous.mul (by fun_prop)
    exact
      (hG.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
  have hbounded :
      BddAbove
        ((fun u : ℝ =>
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖) ''
            Set.Icc (2 : ℝ) 4) :=
    isCompact_Icc.bddAbove_image hcontinuous.continuousOn
  obtain ⟨B, hB⟩ := hbounded
  let L : ℝ := saddleContourMomentL1 a n (D a)
  have hL : 0 ≤ L := by
    unfold L saddleContourMomentL1
    exact integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨max 0 (max B (‖c‖ * L)), ?_⟩
  intro u
  by_cases hlow : u < (2 : ℝ)
  · have hevent : G =ᶠ[𝓝 u]
          (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hlow] with v hv
      exact hzero v hv
    have hiter :=
      (hevent.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hiter]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply,
      norm_zero, mul_zero] using!
      (le_max_left (0 : ℝ) (max B (‖c‖ * L)))
  · by_cases hupper : u ≤ (4 : ℝ)
    · have hmem : u ∈ Set.Icc (2 : ℝ) 4 :=
        ⟨le_of_not_gt hlow, hupper⟩
      have hinner :
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤ B :=
        hB ⟨u, hmem, rfl⟩
      exact hinner.trans
        ((le_max_left B (‖c‖ * L)).trans
          (le_max_right 0 _))
    · have hu4 : (4 : ℝ) < u := lt_of_not_ge hupper
      have hu3 : (3 : ℝ) < u := by linarith
      have hu0 : (0 : ℝ) < u := by linarith
      have hu1 : (1 : ℝ) ≤ u := by linarith
      have huoi : u ∈ Set.Ioi (1 : ℝ) := by
        change 1 < u
        linarith
      have hevent :
          G =ᶠ[𝓝 u]
            (fun v : ℝ =>
              c * saddlePositiveContourMoment a 0 (D a) v) := by
        filter_upwards [Ioi_mem_nhds hu3] with v hv
        exact htail a ha v hv
      have hiter :
          iteratedDeriv n G u =
            c * saddlePositiveContourMoment a n (D a) u := by
        rw [hevent.iteratedDeriv_eq n,
          iteratedDeriv_const_mul_field,
          saddlePositiveContourMoment_iteratedDeriv_of_positiveContour
            (hD a ha) ha n 0 huoi]
        simp only [zero_add]
      have hmoment :
          ‖saddlePositiveContourMoment a n (D a) u‖ ≤
            u ^ (-a / 2 - (n : ℝ)) * L := by
        exact saddlePositiveContourMoment_norm_le
          (hD a ha) a n hu0
      have hexponent :
          -a / 2 - (n : ℝ) ≤ -(k : ℝ) := by
        try dsimp [a]
        push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hpower :
          u ^ (-a / 2 - (n : ℝ)) ≤
            u ^ (-(k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hu1 hexponent
      have hcancel :
          u ^ k * u ^ (-(k : ℝ)) = 1 := by
        rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
        exact mul_inv_cancel₀ (pow_ne_zero _ hu0.ne')
      have htailbound :
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤
            ‖c‖ * L := by
        calc
          ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ =
              u ^ k *
                (‖c‖ *
                  ‖saddlePositiveContourMoment a n (D a) u‖) := by
                rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
                  hiter, norm_mul, Real.norm_of_nonneg hu0.le]
          _ ≤ u ^ k *
              (‖c‖ *
                (u ^ (-a / 2 - (n : ℝ)) * L)) := by
                gcongr
          _ ≤ u ^ k *
              (‖c‖ * (u ^ (-(k : ℝ)) * L)) := by
                gcongr
          _ = (u ^ k * u ^ (-(k : ℝ))) *
                (‖c‖ * L) := by ring
          _ = ‖c‖ * L := by rw [hcancel, one_mul]
      exact htailbound.trans
        ((le_max_right B (‖c‖ * L)).trans
          (le_max_right 0 _))

private theorem plusSaddleOuterSquaredProfile_schwartz_decay
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (plusSaddleOuterSquaredProfile ε ℓ) u‖ ≤ C := by
  apply saddleOuterSquaredProfile_schwartz_decay
    (plusSaddleOuterSquaredProfile_contDiff hε hℓ horder)
    (fun u hu =>
      plusSaddleOuterSquaredProfile_eq_zero ε ℓ hu)
    (fun a t =>
      plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I))
    _ _ k n
  · intro a ha j
    exact plusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun m => saddlePositiveContour_ne_pole ha m) j
  · intro a ha u hu
    simpa only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
      plusSaddlePositiveSquaredContour] using!
      plusSaddleOuterSquaredProfile_eq_positiveContour
        hε hℓ horder ha hu

private theorem minusSaddleOuterSquaredProfile_schwartz_decay
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ,
      ‖u‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (minusSaddleOuterSquaredProfile ε ℓ) u‖ ≤ C := by
  apply saddleOuterSquaredProfile_schwartz_decay
    (minusSaddleOuterSquaredProfile_contDiff hε hℓ horder)
    (fun u hu =>
      minusSaddleOuterSquaredProfile_eq_zero ε ℓ hu)
    (fun a t =>
      minusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I))
    _ _ k n
  · intro a ha j
    exact minusSaddleMellinData_shiftedLine_moment_integrable
      hε hℓ horder
      (fun m => saddlePositiveContour_ne_pole ha m) j
  · intro a ha u hu
    simpa only [one_div, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat,
      minusSaddlePositiveSquaredContour] using!
      minusSaddleOuterSquaredProfile_eq_positiveContour
        hε hℓ horder ha hu

private noncomputable def plusSaddleOuterScalarSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    𝓢(ℝ, ℂ) where
  toFun := plusSaddleOuterSquaredProfile ε ℓ
  smooth' := plusSaddleOuterSquaredProfile_contDiff
    hε hℓ horder
  decay' := plusSaddleOuterSquaredProfile_schwartz_decay
    hε hℓ horder

private noncomputable def minusSaddleOuterScalarSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    𝓢(ℝ, ℂ) where
  toFun := minusSaddleOuterSquaredProfile ε ℓ
  smooth' := minusSaddleOuterSquaredProfile_contDiff
    hε hℓ horder
  decay' := minusSaddleOuterSquaredProfile_schwartz_decay
    hε hℓ horder

private noncomputable def saddleSquaredSchwartzPullback (d : ℕ) :
    𝓢(ℝ, ℂ) →L[ℂ] TestFunction d := by
  apply SchwartzMap.compCLM ℂ
    (Function.hasTemperateGrowth_norm_sq (Euclidean d))
  refine ⟨1, 1, ?_⟩
  intro x
  change ‖x‖ ≤ 1 * (1 + ‖‖x‖ ^ 2‖) ^ 1
  rw [one_mul, pow_one, Real.norm_of_nonneg (sq_nonneg _)]
  linarith [sq_nonneg (‖x‖ - (1 / 2 : ℝ))]

private noncomputable def plusSaddleOuterSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) : TestFunction d :=
  saddleSquaredSchwartzPullback d
    (plusSaddleOuterScalarSchwartz hε hℓ horder)

private noncomputable def minusSaddleOuterSchwartz
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) : TestFunction d :=
  saddleSquaredSchwartzPullback d
    (minusSaddleOuterScalarSchwartz hε hℓ horder)

@[simp] private theorem plusSaddleOuterSchwartz_apply
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) (x : Euclidean d) :
    plusSaddleOuterSchwartz hε hℓ horder d x =
      plusSaddleOuterSquaredProfile ε ℓ (‖x‖ ^ 2) := rfl

@[simp] private theorem minusSaddleOuterSchwartz_apply
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) (x : Euclidean d) :
    minusSaddleOuterSchwartz hε hℓ horder d x =
      minusSaddleOuterSquaredProfile ε ℓ (‖x‖ ^ 2) := rfl

private theorem plusSaddleOuterDifference_hasCompactSupport
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) :
    HasCompactSupport (fun x : Euclidean d =>
      plusSaddleProfile ε ℓ ‖x‖ -
        plusSaddleOuterSchwartz hε hℓ horder d x) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  by_contra houtside
  have hr2 : (2 : ℝ) < ‖x‖ := by
    by_contra hnot
    apply houtside
    exact mem_closedBall_zero_iff.mpr (le_of_not_gt hnot)
  have hr : 0 < ‖x‖ := by linarith
  have hsquare : (3 : ℝ) < ‖x‖ ^ 2 := by
    linarith [sq_nonneg (‖x‖ - 2)]
  change
    plusSaddleProfile ε ℓ ‖x‖ -
      plusSaddleOuterSchwartz hε hℓ horder d x ≠ 0 at hx
  have houter :
      plusSaddleOuterSchwartz hε hℓ horder d x =
        plusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) := by
    rw [plusSaddleOuterSchwartz_apply]
    exact plusSaddleOuterSquaredProfile_eq_positiveContour
      (a := (2 : ℝ)) hε hℓ horder (by norm_num) hsquare
  have hsource :
      plusSaddleProfile ε ℓ ‖x‖ =
        plusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) :=
    plusSaddleProfile_eq_positive_squaredContour
      (a := (2 : ℝ)) hε hℓ horder hr (by norm_num)
  exact hx (by rw [hsource, houter, sub_self])

private theorem minusSaddleOuterDifference_hasCompactSupport
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (d : ℕ) :
    HasCompactSupport (fun x : Euclidean d =>
      minusSaddleProfile ε ℓ ‖x‖ -
        minusSaddleOuterSchwartz hε hℓ horder d x) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) 2)
  intro x hx
  by_contra houtside
  have hr2 : (2 : ℝ) < ‖x‖ := by
    by_contra hnot
    apply houtside
    exact mem_closedBall_zero_iff.mpr (le_of_not_gt hnot)
  have hr : 0 < ‖x‖ := by linarith
  have hsquare : (3 : ℝ) < ‖x‖ ^ 2 := by
    linarith [sq_nonneg (‖x‖ - 2)]
  change
    minusSaddleProfile ε ℓ ‖x‖ -
      minusSaddleOuterSchwartz hε hℓ horder d x ≠ 0 at hx
  have houter :
      minusSaddleOuterSchwartz hε hℓ horder d x =
        minusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) := by
    rw [minusSaddleOuterSchwartz_apply]
    exact minusSaddleOuterSquaredProfile_eq_positiveContour
      (a := (2 : ℝ)) hε hℓ horder (by norm_num) hsquare
  have hsource :
      minusSaddleProfile ε ℓ ‖x‖ =
        minusSaddlePositiveSquaredContour ε ℓ 2 (‖x‖ ^ 2) :=
    minusSaddleProfile_eq_positive_squaredContour
      (a := (2 : ℝ)) hε hℓ horder hr (by norm_num)
  exact hx (by rw [hsource, houter, sub_self])

private noncomputable def plusSaddleSchwartz
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    TestFunction d where
  toFun := plusSaddleFunction ε d
  smooth' := plusSaddleFunction_contDiff hε hd horder
  decay' := by
    intro k n
    let ℓ : ℝ := (d : ℝ) / 2
    have hℓ : 0 < ℓ := by
      try dsimp [ℓ]
      exact div_pos (by exact_mod_cast hd) (by norm_num)
    let tail : TestFunction d :=
      plusSaddleOuterSchwartz hε hℓ horder d
    have hcompact :
        HasCompactSupport (fun x : Euclidean d =>
          plusSaddleFunction ε d x - tail x) := by
      simpa only [plusSaddleFunction, plusSaddleOuterSchwartz_apply] using!
        plusSaddleOuterDifference_hasCompactSupport
          hε hℓ horder d
    have hsmooth :
        ContDiff ℝ ∞ (fun x : Euclidean d =>
          plusSaddleFunction ε d x - tail x) :=
      (plusSaddleFunction_contDiff hε hd horder).sub
        (tail.smooth ⊤)
    let correction : TestFunction d :=
      hcompact.toSchwartzMap hsmooth
    let full : TestFunction d := tail + correction
    have hfun :
        plusSaddleFunction ε d =
          (fun x : Euclidean d => full x) := by
      funext x
      change
        plusSaddleFunction ε d x =
          tail x +
            (plusSaddleFunction ε d x - tail x)
      ring
    rw [hfun]
    exact full.decay' k n

private noncomputable def minusSaddleSchwartz
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    TestFunction d where
  toFun := minusSaddleFunction ε d
  smooth' := minusSaddleFunction_contDiff hε hd horder
  decay' := by
    intro k n
    let ℓ : ℝ := (d : ℝ) / 2
    have hℓ : 0 < ℓ := by
      try dsimp [ℓ]
      exact div_pos (by exact_mod_cast hd) (by norm_num)
    let tail : TestFunction d :=
      minusSaddleOuterSchwartz hε hℓ horder d
    have hcompact :
        HasCompactSupport (fun x : Euclidean d =>
          minusSaddleFunction ε d x - tail x) := by
      simpa only [minusSaddleFunction, minusSaddleOuterSchwartz_apply] using!
        minusSaddleOuterDifference_hasCompactSupport
          hε hℓ horder d
    have hsmooth :
        ContDiff ℝ ∞ (fun x : Euclidean d =>
          minusSaddleFunction ε d x - tail x) :=
      (minusSaddleFunction_contDiff hε hd horder).sub
        (tail.smooth ⊤)
    let correction : TestFunction d :=
      hcompact.toSchwartzMap hsmooth
    let full : TestFunction d := tail + correction
    have hfun :
        minusSaddleFunction ε d =
          (fun x : Euclidean d => full x) := by
      funext x
      change
        minusSaddleFunction ε d x =
          tail x +
            (minusSaddleFunction ε d x - tail x)
      ring
    rw [hfun]
    exact full.decay' k n

private noncomputable def saddleSourceContourEnvelopeScale
    (ε ℓ u : ℝ) : ℝ :=
  Real.exp (-(ℓ * u) * Real.log Real.pi / 2) *
    Real.Gamma (ℓ * (1 + u) / 2) *
      Real.exp (ℓ * realHyperbolicShellPhase ε u)

private noncomputable def saddleSourceContourDamping
    (ε ℓ u T : ℝ) : ℝ :=
  upperGammaDamping ℓ (1 + u) T +
    positiveShellDamping ε ℓ (u - 1) T -
      upperShortShellDamping ε ℓ (u - 1) T

private theorem saddleSourceContourEnvelopeScale_pos
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) :
    0 < saddleSourceContourEnvelopeScale ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  unfold saddleSourceContourEnvelopeScale
  exact mul_pos
    (mul_pos (Real.exp_pos _)
      (Real.Gamma_pos_of_pos (by positivity)))
    (Real.exp_pos _)

private theorem saddleSourceContour_piExponential_norm
    (ℓ u T : ℝ) :
    ‖Complex.exp
        (((ℓ : ℂ) - saddleSourceMellinContour ℓ u T) *
          (Real.log Real.pi : ℂ) / 2)‖ =
      Real.exp (-(ℓ * u) * Real.log Real.pi / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [saddleSourceMellinContour, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.div_ofNat_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.add_re,
      Complex.one_re,
    Complex.ofReal_im, Complex.add_im, Complex.one_im, add_zero, mul_zero, sub_zero,
      Complex.I_re, zero_mul,
    Complex.I_im, Complex.mul_im, sub_self, Complex.sub_im, one_mul, zero_add, zero_sub,
      sub_neg_eq_add, neg_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj']
  ring

private theorem saddleSourceContour_gamma_norm
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    ‖Complex.Gamma
      (saddleSourceMellinContour ℓ u T / 2)‖ =
      Real.Gamma (ℓ * (1 + u) / 2) *
        Real.exp (-upperGammaDamping ℓ (1 + u) T) := by
  rw [saddleSourceMellinContour_gammaArgument]
  exact upperGammaShifted_modulus_eq_exp_neg_damping
    hℓ (by linarith) T

private theorem saddleSourceContour_shellExponential_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (T : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        (Complex.I *
          (saddleSourceMellinContour ℓ u T - (ℓ : ℂ)) /
            (ℓ : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by
  rw [saddleSourceMellinContour_shellArgument hℓ]
  exact norm_saddleShellExponential_eq_exp_neg_damping
    hε horder ℓ T u

private theorem saddleSourceContour_mellinEnvelope_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (T : ℝ) :
    ‖saddleMellinEnvelope ε ℓ
        (saddleSourceMellinContour ℓ u T)‖ =
      saddleSourceContourEnvelopeScale ε ℓ u *
        Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  have hπ := saddleSourceContour_piExponential_norm ℓ u T
  have hΓ := saddleSourceContour_gamma_norm hℓ hu T
  have hshell := saddleSourceContour_shellExponential_norm
    hε hℓ horder (u := u) T
  have hexp :
      Real.exp (-upperGammaDamping ℓ (1 + u) T) *
          Real.exp
            (-(positiveShellDamping ε ℓ (u - 1) T -
              upperShortShellDamping ε ℓ (u - 1) T)) =
        Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
    rw [← Real.exp_add]
    congr 1
    unfold saddleSourceContourDamping
    ring
  unfold saddleMellinEnvelope
  rw [norm_mul, norm_mul, hπ, hΓ, hshell]
  unfold saddleSourceContourEnvelopeScale
  rw [← hexp]
  ring

private noncomputable def saddleSourceNormalizedEnvelope
    (ε ℓ u T : ℝ) : ℂ :=
  saddleMellinEnvelope ε ℓ
      (saddleSourceMellinContour ℓ u T) /
    (saddleSourceContourEnvelopeScale ε ℓ u : ℂ)

private theorem saddleSourceNormalizedEnvelope_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (T : ℝ) :
    ‖saddleSourceNormalizedEnvelope ε ℓ u T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  unfold saddleSourceNormalizedEnvelope
  rw [norm_div,
    saddleSourceContour_mellinEnvelope_norm
      hε hℓ hu horder T,
    Complex.norm_of_nonneg
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).le,
    mul_div_cancel_left₀ _
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).ne']

private noncomputable def saddleSourceCenteredEnvelope
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceNormalizedEnvelope ε ℓ u T *
    Complex.exp (Complex.I * ((ℓ * T * v : ℝ) : ℂ))

private theorem saddleSourceCenteredEnvelope_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v T : ℝ) :
    ‖saddleSourceCenteredEnvelope ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  unfold saddleSourceCenteredEnvelope
  rw [norm_mul,
    saddleSourceNormalizedEnvelope_norm
      hε hℓ hu horder T,
    Complex.norm_exp_I_mul_ofReal, mul_one]

private noncomputable def saddleSourceCenteredPlusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))

private noncomputable def saddleSourceCenteredMinusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))

private theorem saddleSourceCenteredPlusIntegrand_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v T : ℝ) :
    ‖saddleSourceCenteredPlusIntegrand ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖plusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ := by
  unfold saddleSourceCenteredPlusIntegrand
  rw [norm_mul,
    saddleSourceCenteredEnvelope_norm hε hℓ hu horder]

private theorem saddleSourceCenteredMinusIntegrand_norm
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v T : ℝ) :
    ‖saddleSourceCenteredMinusIntegrand ε ℓ u v T‖ =
      Real.exp (-saddleSourceContourDamping ε ℓ u T) *
        ‖minusPolynomial ε
          ((T : ℂ) + Complex.I * (u : ℂ))‖ := by
  unfold saddleSourceCenteredMinusIntegrand
  rw [norm_mul,
    saddleSourceCenteredEnvelope_norm hε hℓ hu horder]

@[simp] private theorem saddleSourceContourDamping_eq_firstBranch
    (ε ℓ u T : ℝ) :
    saddleSourceContourDamping ε ℓ u T =
      upperFirstBranchSaddleDamping ε ℓ u T := rfl

private theorem saddleSourceContourDamping_eq_secondBranch
    (ε ℓ δ T : ℝ) :
    saddleSourceContourDamping ε ℓ (1 + δ) T =
      upperSaddleDamping ε ℓ δ T := by
  have hη : 1 + (1 + δ) = 2 + δ := by ring
  have hδ : (1 + δ) - 1 = δ := by ring
  simp only [saddleSourceContourDamping, hη, hδ, upperSaddleDamping]

private theorem saddleSourceMellinContour_integral_change
    {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ,
      F (((ℓ * (1 + u) : ℝ) : ℂ) +
        (t : ℂ) * Complex.I)) =
      (ℓ : ℂ) *
        (∫ T : ℝ,
          F (saddleSourceMellinContour ℓ u T)) := by
  let a : ℝ := ℓ * (1 + u)
  let G : ℝ → ℂ := fun t =>
    F ((a : ℂ) + (t : ℂ) * Complex.I)
  have harg (T : ℝ) :
      (a : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * Complex.I =
        saddleSourceMellinContour ℓ u T := by
    try dsimp [a]
    unfold saddleSourceMellinContour
    push_cast
    ring
  have habs : |(-ℓ)⁻¹| = ℓ⁻¹ := by
    rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hℓ)]
  have hchange :
      (∫ T : ℝ,
        F (saddleSourceMellinContour ℓ u T)) =
        ((ℓ⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ,
            F ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    calc
      (∫ T : ℝ,
        F (saddleSourceMellinContour ℓ u T)) =
          ∫ T : ℝ, G ((-ℓ) * T) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with T
            try dsimp [G]
            rw [harg]
      _ = |(-ℓ)⁻¹| • ∫ t : ℝ, G t :=
        MeasureTheory.Measure.integral_comp_mul_left G (-ℓ)
      _ = ((ℓ⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ,
            F ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          rw [habs]
          simp only [Complex.real_smul, Complex.ofReal_inv, G]
  change
    (∫ t : ℝ,
      F ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (ℓ : ℂ) *
        (∫ T : ℝ,
          F (saddleSourceMellinContour ℓ u T))
  rw [hchange]
  push_cast
  rw [← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hℓ.ne'), one_mul]

private theorem plusSaddleProfile_eq_sourceContourIntegral
    {ε ℓ r u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (hu : -1 < u) :
    plusSaddleProfile ε ℓ r =
      ((ℓ / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ T : ℝ,
          saddleMellinInversePower r
              (saddleSourceMellinContour ℓ u T) *
            plusSaddleMellinData ε ℓ
              (saddleSourceMellinContour ℓ u T)) := by
  have ha : 0 < ℓ * (1 + u) := by
    have hη : 0 < 1 + u := by linarith
    positivity
  rw [plusSaddleProfile_eq_positive_contour
    (a := ℓ * (1 + u)) hε hℓ horder hr ha]
  rw [saddleSourceMellinContour_integral_change
    hℓ u (fun z : ℂ =>
      saddleMellinInversePower r z *
        plusSaddleMellinData ε ℓ z)]
  push_cast
  ring

private theorem minusSaddleProfile_eq_sourceContourIntegral
    {ε ℓ r u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (hu : -1 < u) :
    minusSaddleProfile ε ℓ r =
      ((ℓ / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ T : ℝ,
          saddleMellinInversePower r
              (saddleSourceMellinContour ℓ u T) *
            minusSaddleMellinData ε ℓ
              (saddleSourceMellinContour ℓ u T)) := by
  have ha : 0 < ℓ * (1 + u) := by
    have hη : 0 < 1 + u := by linarith
    positivity
  rw [minusSaddleProfile_eq_positive_contour
    (a := ℓ * (1 + u)) hε hℓ horder hr ha]
  rw [saddleSourceMellinContour_integral_change
    hℓ u (fun z : ℂ =>
      saddleMellinInversePower r z *
        minusSaddleMellinData ε ℓ z)]
  push_cast
  ring

private theorem saddleSourceContour_inversePower_exp
    (ℓ u v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) : ℝ) : ℂ) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ)) := by
  unfold saddleMellinInversePower
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le,
    Real.log_exp,
    Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  unfold saddleSourceMellinContour
  push_cast
  ring

private noncomputable def saddleSourceCenteredPrefactor
    (ε ℓ u v : ℝ) : ℝ :=
  (ℓ / (2 * Real.pi)) *
    Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u

private theorem saddleSourceCenteredPrefactor_pos
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (v : ℝ) :
    0 < saddleSourceCenteredPrefactor ε ℓ u v := by
  unfold saddleSourceCenteredPrefactor
  exact mul_pos
    (mul_pos (div_pos hℓ (by positivity))
      (Real.exp_pos _))
    (saddleSourceContourEnvelopeScale_pos
      (ε := ε) hℓ hu)

private theorem saddleSourceContour_envelope_eq_scale_mul_normalized
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    saddleMellinEnvelope ε ℓ
        (saddleSourceMellinContour ℓ u T) =
      (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) *
        saddleSourceNormalizedEnvelope ε ℓ u T := by
  unfold saddleSourceNormalizedEnvelope
  have hn : (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu).ne'
  field_simp [hn]

private theorem plusSaddleProfile_exp_eq_centeredIntegral
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v : ℝ) :
    plusSaddleProfile ε ℓ (Real.exp v) =
      (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) *
        (∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) := by
  rw [plusSaddleProfile_eq_sourceContourIntegral
    hε hℓ horder (Real.exp_pos v) hu]
  have hpoint (T : ℝ) :
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        plusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) *
          saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
        saddleSourceCenteredPlusIntegrand ε ℓ u v T := by
    rw [saddleSourceContour_inversePower_exp,
      plusSaddleMellinData,
      saddleSourceMellinContour_shellArgument hℓ,
      saddleSourceContour_envelope_eq_scale_mul_normalized
        hℓ hu T]
    unfold saddleSourceCenteredPlusIntegrand
      saddleSourceCenteredEnvelope
    push_cast
    ring
  have hintegral :
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          plusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ((Real.exp (-(ℓ * (1 + u) * v)) *
            saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
          (∫ T : ℝ,
            saddleSourceCenteredPlusIntegrand ε ℓ u v T) := by
    calc
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          plusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ∫ T : ℝ,
          ((Real.exp (-(ℓ * (1 + u) * v)) *
              saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
            saddleSourceCenteredPlusIntegrand ε ℓ u v T := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with T
              exact hpoint T
      _ = _ := integral_const_mul _ _
  rw [hintegral]
  unfold saddleSourceCenteredPrefactor
  push_cast
  ring

private theorem minusSaddleProfile_exp_eq_centeredIntegral
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v : ℝ) :
    minusSaddleProfile ε ℓ (Real.exp v) =
      (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) *
        (∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
  rw [minusSaddleProfile_eq_sourceContourIntegral
    hε hℓ horder (Real.exp_pos v) hu]
  have hpoint (T : ℝ) :
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        minusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) *
          saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
        saddleSourceCenteredMinusIntegrand ε ℓ u v T := by
    rw [saddleSourceContour_inversePower_exp,
      minusSaddleMellinData,
      saddleSourceMellinContour_shellArgument hℓ,
      saddleSourceContour_envelope_eq_scale_mul_normalized
        hℓ hu T]
    unfold saddleSourceCenteredMinusIntegrand
      saddleSourceCenteredEnvelope
    push_cast
    ring
  have hintegral :
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          minusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ((Real.exp (-(ℓ * (1 + u) * v)) *
            saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
          (∫ T : ℝ,
            saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
    calc
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          minusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ∫ T : ℝ,
          ((Real.exp (-(ℓ * (1 + u) * v)) *
              saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
            saddleSourceCenteredMinusIntegrand ε ℓ u v T := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with T
              exact hpoint T
      _ = _ := integral_const_mul _ _
  rw [hintegral]
  unfold saddleSourceCenteredPrefactor
  push_cast
  ring

private noncomputable def saddleSourceGaussianVariance
    (ε ℓ u : ℝ) : ℝ :=
  upperSaddleVariance ε ℓ (u - 1)

private noncomputable def saddleSourceGaussianKernel
    (ε ℓ u T : ℝ) : ℝ :=
  Real.exp
    (-(ℓ * saddleSourceGaussianVariance ε ℓ u / 2) * T ^ 2)

private noncomputable def saddleSourceGaussianPlusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    plusPolynomial ε (Complex.I * (u : ℂ))

private noncomputable def saddleSourceGaussianMinusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    minusPolynomial ε (Complex.I * (u : ℂ))

private theorem saddleSourceGaussianKernel_integrable
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Integrable (saddleSourceGaussianKernel ε ℓ u) := by
  unfold saddleSourceGaussianKernel
  exact integrable_exp_neg_mul_sq (by positivity)

private theorem saddleSourceGaussianKernel_integral
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) := by
  exact integral_gaussian
    (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)

private theorem saddleSourceGaussianKernel_integral_pos
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    0 < ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  rw [saddleSourceGaussianKernel_integral]
  positivity

private theorem saddleSourceGaussianPlusIntegrand_integrable
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Integrable (saddleSourceGaussianPlusIntegrand ε ℓ u) := by
  unfold saddleSourceGaussianPlusIntegrand
  exact (saddleSourceGaussianKernel_integrable hℓ hV).ofReal.mul_const _

private theorem saddleSourceGaussianMinusIntegrand_integrable
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u) :
    Integrable (saddleSourceGaussianMinusIntegrand ε ℓ u) := by
  unfold saddleSourceGaussianMinusIntegrand
  exact (saddleSourceGaussianKernel_integrable hℓ hV).ofReal.mul_const _

private theorem saddleSourceGaussianPlusIntegrand_integral
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianPlusIntegrand ε ℓ u T) =
      (Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) : ℂ) *
        plusPolynomial ε (Complex.I * (u : ℂ)) := by
  unfold saddleSourceGaussianPlusIntegrand
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal,
    saddleSourceGaussianKernel_integral]

private theorem saddleSourceGaussianMinusIntegrand_integral
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianMinusIntegrand ε ℓ u T) =
      (Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) : ℂ) *
        minusPolynomial ε (Complex.I * (u : ℂ)) := by
  unfold saddleSourceGaussianMinusIntegrand
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal,
    saddleSourceGaussianKernel_integral]

private theorem eventually_saddleSourceGaussianVariance_secondBranch_pos :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          0 < saddleSourceGaussianVariance ε ℓ (1 + δ) := by
  filter_upwards [eventually_upperSaddleVariance_pos]
    with ε hpositive
  intro ℓ hℓ δ hδ
  convert! hpositive ℓ hℓ δ hδ using 1
  all_goals simp only [saddleSourceGaussianVariance, add_sub_cancel_left]

private theorem plusSaddleProfile_exp_re_pos_of_gaussian_error
    {ε ℓ u v : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T).re) :
    0 < (plusSaddleProfile ε ℓ (Real.exp v)).re := by
  have _hV : 0 < saddleSourceGaussianVariance ε ℓ u := hV
  let J : ℂ := ∫ T : ℝ,
    saddleSourceCenteredPlusIntegrand ε ℓ u v T
  let G : ℂ := ∫ T : ℝ,
    saddleSourceGaussianPlusIntegrand ε ℓ u T
  have hreal : |(J - G).re| ≤ ‖J - G‖ :=
    Complex.abs_re_le_norm _
  have hpositive : 0 < J.re := by
    change ‖J - G‖ < G.re at herror
    have hlower : -‖J - G‖ ≤ (J - G).re := by
      have := (neg_le_of_abs_le hreal)
      exact this
    rw [Complex.sub_re] at hlower
    linarith
  rw [plusSaddleProfile_exp_eq_centeredIntegral
    hε hℓ hu horder v]
  change 0 <
    ((saddleSourceCenteredPrefactor ε ℓ u v : ℂ) * J).re
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos
    (saddleSourceCenteredPrefactor_pos hℓ hu v)
    hpositive

private theorem minusSaddleProfile_exp_re_neg_of_gaussian_error
    {ε ℓ u v : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T).re) :
    (minusSaddleProfile ε ℓ (Real.exp v)).re < 0 := by
  have _hV : 0 < saddleSourceGaussianVariance ε ℓ u := hV
  let J : ℂ := ∫ T : ℝ,
    saddleSourceCenteredMinusIntegrand ε ℓ u v T
  let G : ℂ := ∫ T : ℝ,
    saddleSourceGaussianMinusIntegrand ε ℓ u T
  have hreal : |(J - G).re| ≤ ‖J - G‖ :=
    Complex.abs_re_le_norm _
  have hnegative : J.re < 0 := by
    change ‖J - G‖ < -G.re at herror
    have hupper : (J - G).re ≤ ‖J - G‖ :=
      (le_abs_self _).trans hreal
    rw [Complex.sub_re] at hupper
    linarith
  rw [minusSaddleProfile_exp_eq_centeredIntegral
    hε hℓ hu horder v]
  change
    ((saddleSourceCenteredPrefactor ε ℓ u v : ℂ) * J).re < 0
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg
    (saddleSourceCenteredPrefactor_pos hℓ hu v)
    hnegative

private theorem saddleSourcePositiveShellVariance_nonneg
    (ε δ : ℝ) :
    0 ≤ upperPositiveShellVariance ε δ := by
  unfold upperPositiveShellVariance
  apply intervalIntegral.integral_nonneg
    (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by linarith)
  intro a ha
  unfold positiveShellDensity
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg (shellWeight_pos ε).le
        (Real.cosh_pos a).le)
      (sq_nonneg a))
    (Real.cosh_pos _).le

private theorem upperFirstBranch_shortVariance_le_gamma
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a))) :
    upperShortShellVariance ε (u - 1) ≤
      (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) := by
  let a₀ : ℝ := (ε ^ 3)
  let A : ℝ := (10 * Real.log (1 / ε))
  let η : ℝ := 1 + u
  let γ : ℝ → ℝ := fun a =>
    a ^ 2 * upperGammaMeasureDensity ℓ η a
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha₀ : 0 < a₀ := by
    try dsimp [a₀]
    positivity
  have hfactor : 0 ≤ 1 - 4 * ε := by
    linarith
  have hsubset : Ioc a₀ A ⊆ Ioi (0 : ℝ) := by
    intro a ha
    exact ha₀.trans ha.1
  have hgamma : IntegrableOn γ (Ioi (0 : ℝ)) := by
    exact upperGammaVarianceDensity_integrable hℓ hη
  have hgammaOn : IntegrableOn γ (Ioc a₀ A) :=
    hgamma.mono_set hsubset
  have hscaledOn : IntegrableOn
      (fun a : ℝ => (1 - 4 * ε) * γ a)
      (Ioc a₀ A) :=
    hgammaOn.const_mul (1 - 4 * ε)
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hcosh : Continuous
      (fun a : ℝ => Real.cosh (u * a)) := by
    fun_prop
  have hsquare : Continuous (fun a : ℝ => a ^ 2) := by
    fun_prop
  have hshortInterval : IntervalIntegrable
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2)
      volume a₀ A := by
    have hneg : IntervalIntegrable
        (fun a : ℝ => -shortShellDensity ε a)
        volume a₀ A := by
      simpa only  using! hs.neg
    exact ((hneg.const_mul ℓ).mul_continuousOn
      hcosh.continuousOn).mul_continuousOn
        hsquare.continuousOn
  have hshortOn : IntegrableOn
      (fun a : ℝ =>
        ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2)
      (Ioc a₀ A) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show a₀ ≤ A by exact horder)).mp hshortInterval
  have hpoint (a : ℝ) (ha : a ∈ Ioc a₀ A) :
      ℓ * (-shortShellDensity ε a) *
          Real.cosh (u * a) * a ^ 2 ≤
        (1 - 4 * ε) * γ a := by
    have hcomparison :=
      upperFirstBranch_shortMeasure_pointwise
        hε hεsmall hℓ (ha₀.trans ha.1)
        hulower.le huupper
        (hmargin a ⟨ha.1.le, ha.2⟩)
    have hmul :=
      mul_le_mul_of_nonneg_right hcomparison (sq_nonneg a)
    simpa [γ, η, mul_assoc, mul_left_comm, mul_comm] using! hmul
  have hmono := setIntegral_mono_on
    hshortOn hscaledOn measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] γ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    try dsimp [γ]
    exact mul_nonneg (sq_nonneg a)
      (upperGammaMeasureDensity_pos hℓ ha).le
  have haesubset :
      Ioc a₀ A ≤ᶠ[ae (volume : Measure ℝ)] Ioi 0 :=
    Filter.Eventually.of_forall fun a ha => hsubset ha
  have hrestrict :=
    setIntegral_mono_set hgamma hnonnegative haesubset
  have hscaleRestrict :=
    mul_le_mul_of_nonneg_left hrestrict hfactor
  have hshortEq :
      ℓ * upperShortShellVariance ε (u - 1) =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) * a ^ 2 := by
    unfold upperShortShellVariance
    have hu : 1 + (u - 1) = u := by ring
    rw [hu, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro a ha
    ring
  have hmain :
      ℓ * upperShortShellVariance ε (u - 1) ≤
        (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0, γ a := by
    calc
      ℓ * upperShortShellVariance ε (u - 1) =
        ∫ a : ℝ in Ioc a₀ A,
          ℓ * (-shortShellDensity ε a) *
            Real.cosh (u * a) * a ^ 2 := hshortEq
      _ ≤ ∫ a : ℝ in Ioc a₀ A,
          (1 - 4 * ε) * γ a := hmono
      _ = (1 - 4 * ε) *
          ∫ a : ℝ in Ioc a₀ A, γ a := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ (1 - 4 * ε) *
          ∫ a : ℝ in Ioi 0, γ a := hscaleRestrict
  calc
    upperShortShellVariance ε (u - 1) =
      ℓ⁻¹ * (ℓ * upperShortShellVariance ε (u - 1)) := by
        field_simp [hℓ.ne']
    _ ≤ ℓ⁻¹ *
      ((1 - 4 * ε) * ∫ a : ℝ in Ioi 0, γ a) :=
        mul_le_mul_of_nonneg_left hmain
          (inv_pos.mpr hℓ).le
    _ = (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) := by
      unfold upperGammaVariance
      try dsimp [γ, η]
      ring

private theorem upperFirstBranch_saddleSourceGaussianVariance_lower_bound
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a))) :
    4 * ε * upperGammaVariance ℓ (1 + u) ≤
      saddleSourceGaussianVariance ε ℓ u := by
  have hshort := upperFirstBranch_shortVariance_le_gamma
    hε hεsmall hℓ hulower huupper horder hmargin
  have hpositive :=
    saddleSourcePositiveShellVariance_nonneg ε (u - 1)
  unfold saddleSourceGaussianVariance
    upperSaddleVariance upperNetShellVariance
  have hη : 2 + (u - 1) = 1 + u := by ring
  rw [hη]
  linarith

private theorem eventually_saddleSourceGaussianVariance_firstBranch_pos :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
          0 < saddleSourceGaussianVariance ε ℓ u := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have htendsto : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards
      [htendsto.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  intro ℓ hℓ u hulower huupper
  have hη : 0 < 1 + u := by linarith
  have hgamma :=
    (upperGammaVariance_bounds hℓ hη).1
  have hgammaPos : 0 < upperGammaVariance ℓ (1 + u) :=
    (show 0 < 1 / (2 * (1 + u)) by positivity).trans_le hgamma
  have hbound :=
    upperFirstBranch_saddleSourceGaussianVariance_lower_bound
      hε hεsmall hℓ hulower huupper horder
      (fun a ha =>
        (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans
          (hmargin a ha))
  exact (mul_pos (by positivity : 0 < 4 * ε)
    hgammaPos).trans_le hbound

private theorem saddleSourceCenteredPlusIntegrand_sourcePointwise
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : -1 < u)
    (v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) *
      plusSaddleMellinData ε ℓ
        (saddleSourceMellinContour ℓ u T) =
    ((Real.exp (-(ℓ * (1 + u) * v)) *
        saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
      saddleSourceCenteredPlusIntegrand ε ℓ u v T := by
  rw [saddleSourceContour_inversePower_exp,
    plusSaddleMellinData,
    saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceContour_envelope_eq_scale_mul_normalized
      hℓ hu T]
  unfold saddleSourceCenteredPlusIntegrand
    saddleSourceCenteredEnvelope
  push_cast
  ring

private theorem saddleSourceCenteredMinusIntegrand_sourcePointwise
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : -1 < u)
    (v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) *
      minusSaddleMellinData ε ℓ
        (saddleSourceMellinContour ℓ u T) =
    ((Real.exp (-(ℓ * (1 + u) * v)) *
        saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
      saddleSourceCenteredMinusIntegrand ε ℓ u v T := by
  rw [saddleSourceContour_inversePower_exp,
    minusSaddleMellinData,
    saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceContour_envelope_eq_scale_mul_normalized
      hℓ hu T]
  unfold saddleSourceCenteredMinusIntegrand
    saddleSourceCenteredEnvelope
  push_cast
  ring

private theorem saddleSourceCenteredPlusIntegrand_integrable
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v : ℝ) :
    Integrable (saddleSourceCenteredPlusIntegrand ε ℓ u v) := by
  let a : ℝ := ℓ * (1 + u)
  let c : ℂ :=
    ((Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ)
  have ha : 0 < a := by
    try dsimp [a]
    have : 0 < 1 + u := by linarith
    positivity
  have hline :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      (a := a) (r := Real.exp v)
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole ha n)
      (Real.exp_pos v)
  have hcomp := hline.comp_mul_left'
    (neg_ne_zero.mpr hℓ.ne')
  have hcontour : Integrable (fun T : ℝ =>
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        plusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T)) := by
    apply hcomp.congr
    filter_upwards [] with T
    have harg :
        (a : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * Complex.I =
          saddleSourceMellinContour ℓ u T := by
      try dsimp [a]
      unfold saddleSourceMellinContour
      push_cast
      ring
    rw [harg]
  have hscaled : Integrable
      (fun T : ℝ => c *
        saddleSourceCenteredPlusIntegrand ε ℓ u v T) := by
    apply hcontour.congr
    filter_upwards [] with T
    exact saddleSourceCenteredPlusIntegrand_sourcePointwise
      hℓ hu v T
  have hc : c ≠ 0 := by
    try dsimp [c]
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (Real.exp_pos _)
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu)).ne'
  have hinverse := hscaled.const_mul c⁻¹
  apply hinverse.congr
  filter_upwards [] with T
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem saddleSourceCenteredMinusIntegrand_integrable
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (v : ℝ) :
    Integrable (saddleSourceCenteredMinusIntegrand ε ℓ u v) := by
  let a : ℝ := ℓ * (1 + u)
  let c : ℂ :=
    ((Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ)
  have ha : 0 < a := by
    try dsimp [a]
    have : 0 < 1 + u := by linarith
    positivity
  have hline :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      (a := a) (r := Real.exp v)
      hε hℓ horder
      (fun n => saddlePositiveContour_ne_pole ha n)
      (Real.exp_pos v)
  have hcomp := hline.comp_mul_left'
    (neg_ne_zero.mpr hℓ.ne')
  have hcontour : Integrable (fun T : ℝ =>
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        minusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T)) := by
    apply hcomp.congr
    filter_upwards [] with T
    have harg :
        (a : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * Complex.I =
          saddleSourceMellinContour ℓ u T := by
      try dsimp [a]
      unfold saddleSourceMellinContour
      push_cast
      ring
    rw [harg]
  have hscaled : Integrable
      (fun T : ℝ => c *
        saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
    apply hcontour.congr
    filter_upwards [] with T
    exact saddleSourceCenteredMinusIntegrand_sourcePointwise
      hℓ hu v T
  have hc : c ≠ 0 := by
    try dsimp [c]
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (Real.exp_pos _)
      (saddleSourceContourEnvelopeScale_pos
        (ε := ε) hℓ hu)).ne'
  have hinverse := hscaled.const_mul c⁻¹
  apply hinverse.congr
  filter_upwards [] with T
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end

section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

private noncomputable def upperImaginaryExp (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

private theorem upperImaginaryExp_hasDerivAt (x : ℝ) :
    HasDerivAt upperImaginaryExp
      (Complex.I * upperImaginaryExp x) x := by
  have hreal :
      HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! Complex.ofRealCLM.hasDerivAt
  have hlinear :
      HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ))
        Complex.I x := by
    convert! hreal.const_mul Complex.I using 1
    all_goals simp only [mul_one]
  convert! hlinear.cexp using 1
  all_goals simp only [upperImaginaryExp, mul_comm]

private theorem upperImaginaryExp_iteratedDeriv
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n upperImaginaryExp x =
      Complex.I ^ n * upperImaginaryExp x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv n upperImaginaryExp =
            fun t : ℝ => Complex.I ^ n * upperImaginaryExp t := by
        funext t
        exact ih t
      rw [heq]
      have hderiv :=
        (upperImaginaryExp_hasDerivAt x).const_mul
          (Complex.I ^ n)
      rw [hderiv.deriv]
      rw [pow_succ]
      ring

private theorem upperImaginaryExp_norm (x : ℝ) :
    ‖upperImaginaryExp x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal x

private theorem upperImaginaryExp_contDiff :
    ContDiff ℝ (⊤ : WithTop ℕ∞) upperImaginaryExp := by
  unfold upperImaginaryExp
  have hreal :
      ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul hreal).cexp

private theorem upperImaginaryExp_iteratedDeriv_norm
    (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n upperImaginaryExp x‖ = 1 := by
  rw [upperImaginaryExp_iteratedDeriv,
    norm_mul, norm_pow, upperImaginaryExp_norm]
  simp only [Complex.norm_I, one_pow, mul_one]

private theorem upperImaginaryExp_iteratedDerivWithin_Icc
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (n : ℕ) :
    iteratedDerivWithin n upperImaginaryExp (Icc a b) x =
      Complex.I ^ n * upperImaginaryExp x := by
  have hdiff :
      ContDiffAt ℝ (n : WithTop ℕ∞)
        upperImaginaryExp x :=
    upperImaginaryExp_contDiff.contDiffAt.of_le le_top
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc hab) hdiff hx,
    upperImaginaryExp_iteratedDeriv]

private theorem upperImaginaryExp_taylorWithinEval_two
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval upperImaginaryExp 2
      (Icc (0 : ℝ) x) 0 x =
        1 + Complex.I * (x : ℂ) -
          ((x ^ 2 / 2 : ℝ) : ℂ) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) x :=
    ⟨le_rfl, hx.le⟩
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    taylorWithinEval_succ,
    taylorWithinEval_succ,
    taylor_within_zero_eval,
    upperImaginaryExp_iteratedDerivWithin_Icc hx hzero 1,
    upperImaginaryExp_iteratedDerivWithin_Icc hx hzero 2]
  simp only [upperImaginaryExp, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    CharP.cast_eq_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, sub_zero, pow_one, one_mul,
      Complex.real_smul,
    Nat.factorial_one, Nat.reduceAdd, Complex.I_sq, smul_neg, Complex.ofReal_mul,
      Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_ofNat]
  ring

private theorem upperImaginaryExp_cubicIntegral_norm_le
    {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in (0 : ℝ)..x,
        ((x - t) ^ 2 / 2 : ℝ) •
          iteratedDeriv 3 upperImaginaryExp t‖ ≤
      x ^ 3 / 6 := by
  have hcont :
      Continuous (fun t : ℝ => (x - t) ^ 2 / 2) := by
    fun_prop
  have hint :
      IntervalIntegrable
        (fun t : ℝ => (x - t) ^ 2 / 2)
        volume 0 x := hcont.intervalIntegrable 0 x
  have hnorm :
      ‖∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t‖ ≤
        ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx
    · filter_upwards [] with t ht
      rw [norm_smul, Real.norm_eq_abs,
        upperImaginaryExp_iteratedDeriv_norm, mul_one,
        abs_of_nonneg (by positivity)]
    · exact hint
  have hprimitive (t : ℝ) :
      HasDerivAt (fun z : ℝ => -(x - z) ^ 3 / 6)
        ((x - t) ^ 2 / 2) t := by
    convert! (((hasDerivAt_const t x).sub
      (hasDerivAt_id t)).pow 3).neg.div_const 6 using 1
    all_goals
      simp only [Nat.cast_ofNat, Pi.sub_apply, id, Nat.add_one_sub_one, zero_sub, mul_neg,
        mul_one, neg_neg]
      ring
  calc
    ‖∫ t in (0 : ℝ)..x,
        ((x - t) ^ 2 / 2 : ℝ) •
          iteratedDeriv 3 upperImaginaryExp t‖ ≤
      ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := hnorm
    _ = x ^ 3 / 6 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hprimitive t) hint]
      ring

private theorem upperImaginaryExp_neg (x : ℝ) :
    upperImaginaryExp (-x) =
      starRingEnd ℂ (upperImaginaryExp x) := by
  apply Complex.ext <;>
    simp [upperImaginaryExp, Complex.exp_re, Complex.exp_im,
      Real.cos_neg, Real.sin_neg]

private theorem upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ) +
          ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      x ^ 3 / 6 := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp only [upperImaginaryExp, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, norm_zero, Std.le_refl]
  have hcont :
      ContDiffOn ℝ (3 : ℕ)
        upperImaginaryExp (Set.uIcc 0 x) :=
    (upperImaginaryExp_contDiff.of_le
      (by simp only [le_top] : (3 : WithTop ℕ∞) ≤ ⊤)).contDiffOn
  have htaylor :=
    taylor_integral_remainder
      (f := upperImaginaryExp) (x := x)
      (x₀ := 0) (n := 2) hcont
  rw [Set.uIcc_of_le hx,
    upperImaginaryExp_taylorWithinEval_two hxpos]
    at htaylor
  have hremainder :
      upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ) =
        ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t := by
    calc
      upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ) =
          upperImaginaryExp x -
            (1 + Complex.I * (x : ℂ) -
              ((x ^ 2 / 2 : ℝ) : ℂ)) := by ring
      _ = ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
            iteratedDerivWithin 3 upperImaginaryExp
              (Icc (0 : ℝ) x) t := htaylor
      _ = ∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        change
          ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
              iteratedDerivWithin 3 upperImaginaryExp
                (Icc (0 : ℝ) x) t =
            ((x - t) ^ 2 / 2 : ℝ) •
              iteratedDeriv 3 upperImaginaryExp t
        rw [upperImaginaryExp_iteratedDerivWithin_Icc
          hxpos ht 3,
          ← upperImaginaryExp_iteratedDeriv 3 t]
        norm_num
  rw [hremainder]
  exact upperImaginaryExp_cubicIntegral_norm_le hx

private theorem upperImaginaryExp_quadratic_remainder_norm_le
    (x : ℝ) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ) +
          ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      |x| ^ 3 / 6 := by
  by_cases hx : 0 ≤ x
  · simpa only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
    abs_of_nonneg hx] using!
      upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg hx
  · have hxnegative : x < 0 := lt_of_not_ge hx
    have hf :
        upperImaginaryExp x =
          starRingEnd ℂ (upperImaginaryExp (-x)) := by
      simpa only [neg_neg] using! upperImaginaryExp_neg (-x)
    have hconj :
        upperImaginaryExp x - 1 -
            Complex.I * (x : ℂ) +
              ((x ^ 2 / 2 : ℝ) : ℂ) =
          starRingEnd ℂ
            (upperImaginaryExp (-x) - 1 -
              Complex.I * ((-x : ℝ) : ℂ) +
                (((-x) ^ 2 / 2 : ℝ) : ℂ)) := by
      have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
        simpa only [Complex.ofReal_ofNat] using! Complex.conj_ofReal (2 : ℝ)
      rw [hf]
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
        Complex.ofReal_neg, mul_neg,
        sub_neg_eq_add, even_two, Even.neg_pow, map_add, map_sub, map_one, map_mul,
          Complex.conj_I, Complex.conj_ofReal,
        neg_mul, map_div₀, map_pow, htwo, add_left_inj]
      ring
    calc
      ‖upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ)‖ =
        ‖upperImaginaryExp (-x) - 1 -
          Complex.I * ((-x : ℝ) : ℂ) +
            (((-x) ^ 2 / 2 : ℝ) : ℂ)‖ := by
          rw [hconj, Complex.norm_conj]
      _ ≤ (-x) ^ 3 / 6 :=
        upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg
          (by linarith)
      _ = |x| ^ 3 / 6 := by
        rw [abs_of_neg hxnegative]

private noncomputable def upperGammaCenteredKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ)) *
      (upperGammaMeasureDensity ℓ η a : ℂ)

private noncomputable def upperGammaCenteredPhase
    (ℓ η T : ℝ) : ℂ :=
  ∫ a : ℝ in Ioi 0, upperGammaCenteredKernel ℓ η T a

end

section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

private theorem saddleSourceShiftedCosine_eq_imaginaryExponentials
    (a u T : ℝ) :
    Complex.cos
        ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) =
      ((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          upperImaginaryExp (a * T) +
        ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          upperImaginaryExp (-(a * T)) := by
  have hfirst :
      Complex.exp
          (((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) * Complex.I) =
        (Real.exp (-(u * a)) : ℂ) *
          upperImaginaryExp (a * T) := by
    unfold upperImaginaryExp
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq, mul_neg, mul_one, neg_mul]
    ring
  have hsecond :
      Complex.exp
          (-((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) * Complex.I) =
        (Real.exp (u * a) : ℂ) *
          upperImaginaryExp (-(a * T)) := by
    unfold upperImaginaryExp
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq, mul_neg, mul_one, neg_mul, sub_neg_eq_add]
  unfold Complex.cos
  rw [hfirst, hsecond]
  push_cast
  ring

private noncomputable def saddleSourceCosineQuadraticRemainder
    (a u T : ℝ) : ℂ :=
  Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) -
    (Real.cosh (u * a) : ℂ) +
    Complex.I * ((a * T * Real.sinh (u * a) : ℝ) : ℂ) +
    ((a ^ 2 * T ^ 2 / 2 * Real.cosh (u * a) : ℝ) : ℂ)

private theorem saddleSourceCosineQuadraticRemainder_eq
    (a u T : ℝ) :
    saddleSourceCosineQuadraticRemainder a u T =
      ((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
        (upperImaginaryExp (a * T) - 1 -
          Complex.I * ((a * T : ℝ) : ℂ) +
            (((a * T) ^ 2 / 2 : ℝ) : ℂ)) +
      ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
        (upperImaginaryExp (-(a * T)) - 1 -
          Complex.I * ((-(a * T) : ℝ) : ℂ) +
            (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)) := by
  unfold saddleSourceCosineQuadraticRemainder
  rw [saddleSourceShiftedCosine_eq_imaginaryExponentials,
    Real.cosh_eq, Real.sinh_eq]
  push_cast
  ring

private theorem saddleSourceCosineQuadraticRemainder_norm_le
    (a u T : ℝ) :
    ‖saddleSourceCosineQuadraticRemainder a u T‖ ≤
      Real.cosh (u * a) * |a * T| ^ 3 / 6 := by
  rw [saddleSourceCosineQuadraticRemainder_eq]
  have hfirst := upperImaginaryExp_quadratic_remainder_norm_le
    (a * T)
  have hsecond := upperImaginaryExp_quadratic_remainder_norm_le
    (-(a * T))
  have hwfirst : 0 ≤ Real.exp (-(u * a)) / 2 := by
    positivity
  have hwsecond : 0 ≤ Real.exp (u * a) / 2 := by
    positivity
  calc
    ‖((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ)) +
        ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      ‖((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ))‖ +
        ‖((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          (upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ))‖ :=
        norm_add_le _ _
    _ = (Real.exp (-(u * a)) / 2) *
          ‖upperImaginaryExp (a * T) - 1 -
            Complex.I * ((a * T : ℝ) : ℂ) +
              (((a * T) ^ 2 / 2 : ℝ) : ℂ)‖ +
        (Real.exp (u * a) / 2) *
          ‖upperImaginaryExp (-(a * T)) - 1 -
            Complex.I * ((-(a * T) : ℝ) : ℂ) +
              (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hwfirst, abs_of_nonneg hwsecond]
    _ ≤ (Real.exp (-(u * a)) / 2) *
          (|a * T| ^ 3 / 6) +
        (Real.exp (u * a) / 2) *
          (|a * T| ^ 3 / 6) := by
        have hsecond' :
            ‖upperImaginaryExp (-(a * T)) - 1 -
              Complex.I * ((-(a * T) : ℝ) : ℂ) +
                (((-(a * T)) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
              |a * T| ^ 3 / 6 := by
          simpa only [Complex.ofReal_neg, Complex.ofReal_mul, mul_neg, sub_neg_eq_add, even_two,
            Even.neg_pow,
            Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, abs_mul,
              abs_neg] using! hsecond
        gcongr
    _ = Real.cosh (u * a) * |a * T| ^ 3 / 6 := by
      rw [Real.cosh_eq]
      ring

private theorem saddleSourceWeightedCosineQuadraticRemainder_norm_le
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hb : 0 ≤ b)
    (hw : ContinuousOn w (Icc b c))
    (hwnonneg : ∀ a ∈ Icc b c, 0 ≤ w a)
    (u T : ℝ) :
    ‖∫ a in b..c,
        (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        ∫ a in b..c,
          w a * a ^ 3 * Real.cosh (u * a) := by
  let g : ℝ → ℝ := fun a =>
    (|T| ^ 3 / 6) *
      (w a * a ^ 3 * Real.cosh (u * a))
  have hbase : ContinuousOn
      (fun a : ℝ => w a * a ^ 3 * Real.cosh (u * a))
      (Icc b c) :=
    (hw.mul (continuous_id.pow 3).continuousOn).mul
      (by fun_prop)
  have hg : IntervalIntegrable g volume b c := by
    try dsimp [g]
    exact (continuousOn_const.mul hbase).intervalIntegrable_of_Icc
      hbc
  have hpoint (a : ℝ) (ha : a ∈ Ioc b c) :
      ‖(w a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
        g a := by
    have hmem : a ∈ Icc b c := ⟨ha.1.le, ha.2⟩
    have hwa : 0 ≤ w a := hwnonneg a hmem
    have haa : 0 ≤ a := hb.trans ha.1.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hwa]
    calc
      w a * ‖saddleSourceCosineQuadraticRemainder a u T‖ ≤
        w a *
          (Real.cosh (u * a) * |a * T| ^ 3 / 6) :=
            mul_le_mul_of_nonneg_left
              (saddleSourceCosineQuadraticRemainder_norm_le
                a u T)
              hwa
      _ = g a := by
        try dsimp [g]
        rw [abs_mul, abs_of_nonneg haa]
        ring
  calc
    ‖∫ a in b..c,
        (w a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      ∫ a in b..c, g a := by
        apply intervalIntegral.norm_integral_le_of_norm_le
          hbc _ hg
        filter_upwards [] with a ha
        exact hpoint a ha
    _ = (|T| ^ 3 / 6) *
      ∫ a in b..c,
        w a * a ^ 3 * Real.cosh (u * a) := by
        try dsimp [g]
        rw [intervalIntegral.integral_const_mul]

private theorem saddleSourcePositiveShellQuadraticRemainder_norm_le
    {ε : ℝ} (hε : 0 < ε)
    (u T : ℝ) :
    ‖∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        upperPositiveShellThirdMoment ε (u - 1) := by
  have hB : 0 ≤ (ε⁻¹ ^ 3) := by
    positivity
  have hbound :=
    saddleSourceWeightedCosineQuadraticRemainder_norm_le
      (positiveShellDensity ε)
      (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by linarith)
      hB
      (positiveShellDensity_continuous ε).continuousOn
      (fun a ha => by
        unfold positiveShellDensity
        exact div_nonneg (shellWeight_pos ε).le
          (Real.cosh_pos a).le)
      u T
  convert! hbound using 1
  unfold upperPositiveShellThirdMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  ring_nf

private theorem saddleSourceShortShellQuadraticRemainder_norm_le
    {ε : ℝ} (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (u T : ℝ) :
    ‖∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        upperShortShellThirdMoment ε (u - 1) := by
  have ha₀ : 0 ≤ (ε ^ 3) := by
    positivity
  have hnegative :
      ContinuousOn (fun a : ℝ => -shortShellDensity ε a)
        (Icc (ε ^ 3) (10 * Real.log (1 / ε))) :=
    (shortShellDensity_continuousOn_support hε).neg
  have hnonnegative (a : ℝ)
      (ha : a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε))) :
      0 ≤ -shortShellDensity ε a := by
    have hapos : 0 < a := by
      have : 0 < (ε ^ 3) := by
        positivity
      exact this.trans_le ha.1
    unfold shortShellDensity
    have hm : 0 ≤ (1 - 10 * ε * (1 + a)) := hmargin a ha
    have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
      positivity
    simpa only [neg_mul, neg_neg, ge_iff_le] using!
      div_nonneg
        (mul_nonneg hm (Real.exp_pos _).le)
        hd.le
  have hbound :=
    saddleSourceWeightedCosineQuadraticRemainder_norm_le
      (fun a : ℝ => -shortShellDensity ε a)
      horder ha₀ hnegative hnonnegative u T
  have hnorm :
      ‖∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ =
      ‖∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          ((-shortShellDensity ε a : ℝ) : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ := by
    have heq :
        (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          ((-shortShellDensity ε a : ℝ) : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) =
        -(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro a ha
      push_cast
      ring
    rw [heq, norm_neg]
  rw [hnorm]
  convert! hbound using 1
  unfold upperShortShellThirdMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  ring_nf

private theorem saddleSourceWeightedCosineQuadraticRemainder_integral_eq
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hw : ContinuousOn w (Icc b c))
    (u T : ℝ) :
    (∫ a in b..c,
      (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T) =
      (∫ a in b..c,
        (w a : ℂ) *
          (Complex.cos
            ((a : ℂ) *
              ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        (∫ a in b..c,
          (w a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)) +
        Complex.I *
          ((T * ∫ a in b..c,
            w a * a * Real.sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in b..c,
          w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := by
  let F : ℝ → ℂ := fun a =>
    (w a : ℂ) *
      (Complex.cos
        ((a : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let H : ℝ → ℝ := fun a =>
    w a * (Real.cosh (u * a) - 1)
  let L : ℝ → ℝ := fun a =>
    w a * a * Real.sinh (u * a)
  let V : ℝ → ℝ := fun a =>
    w a * a ^ 2 * Real.cosh (u * a)
  have hwc : ContinuousOn (fun a : ℝ => (w a : ℂ))
      (Icc b c) :=
    Complex.ofRealCLM.continuous.comp_continuousOn hw
  have hkernel : Continuous (fun a : ℝ =>
      Complex.cos
        ((a : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1) := by
    fun_prop
  have hF : IntervalIntegrable F volume b c :=
    (hwc.mul hkernel.continuousOn).intervalIntegrable_of_Icc
      hbc
  have hHreal : ContinuousOn H (Icc b c) := by
    try dsimp [H]
    exact hw.mul (by fun_prop)
  have hLreal : ContinuousOn L (Icc b c) := by
    try dsimp [L]
    exact (hw.mul continuous_id.continuousOn).mul
      (by fun_prop)
  have hVreal : ContinuousOn V (Icc b c) := by
    try dsimp [V]
    exact (hw.mul (continuous_id.pow 2).continuousOn).mul
      (by fun_prop)
  have hH : IntervalIntegrable
      (fun a : ℝ => (H a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hHreal).intervalIntegrable_of_Icc hbc
  have hL : IntervalIntegrable
      (fun a : ℝ => (L a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hLreal).intervalIntegrable_of_Icc hbc
  have hV : IntervalIntegrable
      (fun a : ℝ => (V a : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      hVreal).intervalIntegrable_of_Icc hbc
  have hlinear := hL.const_mul
    (Complex.I * (T : ℂ))
  have hquadratic := hV.const_mul
    (((T ^ 2 / 2 : ℝ) : ℂ))
  have hHcomplex :
      (∫ a in b..c, (H a : ℂ)) =
        ∫ a in b..c,
          (w a : ℂ) * ((Real.cosh (u * a) : ℂ) - 1) := by
    apply intervalIntegral.integral_congr
    intro a ha
    try dsimp [H]
    push_cast
    ring
  calc
    (∫ a in b..c,
      (w a : ℂ) *
        saddleSourceCosineQuadraticRemainder a u T) =
      ∫ a in b..c,
        (F a - (H a : ℂ) +
          (Complex.I * (T : ℂ)) * (L a : ℂ) +
          ((T ^ 2 / 2 : ℝ) : ℂ) * (V a : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro a ha
        try dsimp [F, H, L, V]
        unfold saddleSourceCosineQuadraticRemainder
        push_cast
        ring
    _ = ((∫ a in b..c, F a) -
          (∫ a in b..c, (H a : ℂ)) +
            (Complex.I * (T : ℂ)) *
              (∫ a in b..c, (L a : ℂ))) +
          ((T ^ 2 / 2 : ℝ) : ℂ) *
            (∫ a in b..c, (V a : ℂ)) := by
        rw [intervalIntegral.integral_add
          ((hF.sub hH).add hlinear) hquadratic]
        rw [intervalIntegral.integral_add
          (hF.sub hH) hlinear]
        rw [intervalIntegral.integral_sub hF hH]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ = _ := by
        rw [hHcomplex]
        conv_lhs =>
          rw [intervalIntegral.integral_ofReal,
            intervalIntegral.integral_ofReal]
        try dsimp only [F, L, V]
        simp only [Complex.ofReal_mul, Complex.ofReal_div,
          Complex.ofReal_pow, Complex.ofReal_ofNat]
        ring

private noncomputable def saddleSourceShellCenteredPhase
    (ε ℓ u T : ℝ) : ℂ :=
  (ℓ : ℂ) *
    (mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)) -
      (realHyperbolicShellPhase ε u : ℂ) +
      Complex.I *
        ((T * saddleSourceShellDerivative ε u : ℝ) : ℂ))

private noncomputable def saddleSourceShellQuadraticRemainder
    (ε u T : ℝ) : ℂ :=
  (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    (shortShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T) +
  (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
    (positiveShellDensity ε a : ℂ) *
      saddleSourceCosineQuadraticRemainder a u T)

private theorem saddleSourceShellQuadraticRemainder_eq
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (u T : ℝ) :
    saddleSourceShellQuadraticRemainder ε u T =
      mellinShellPhase ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        (realHyperbolicShellPhase ε u : ℂ) +
        Complex.I *
          ((T * saddleSourceShellDerivative ε u : ℝ) : ℂ) +
        ((T ^ 2 / 2 *
          upperNetShellVariance ε (u - 1) : ℝ) : ℂ) := by
  let Fs : ℂ :=
    ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
      (shortShellDensity ε a : ℂ) *
        (Complex.cos
          ((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let Fp : ℂ :=
    ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
      (positiveShellDensity ε a : ℂ) *
        (Complex.cos
          ((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let Hs : ℂ :=
    ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
      (shortShellDensity ε a : ℂ) *
        ((Real.cosh (u * a) : ℂ) - 1)
  let Hp : ℂ :=
    ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
      (positiveShellDensity ε a : ℂ) *
        ((Real.cosh (u * a) : ℂ) - 1)
  let Ls : ℝ :=
    ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
      shortShellDensity ε a * a * Real.sinh (u * a)
  let Lp : ℝ :=
    ∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
      positiveShellDensity ε a * a * Real.sinh (u * a)
  let Vs : ℝ := upperShortShellVariance ε (u - 1)
  let Vp : ℝ := upperPositiveShellVariance ε (u - 1)
  have hshort :=
    saddleSourceWeightedCosineQuadraticRemainder_integral_eq
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) u T
  have hpositive :=
    saddleSourceWeightedCosineQuadraticRemainder_integral_eq
      (positiveShellDensity ε)
      (show (ε⁻¹ ^ 3) ≤ (ε⁻¹ ^ 3) + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn u T
  have hvariance :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      -Vs := by
    change
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        -(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + (u - 1)) * a))
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hpositivevariance :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      Vp := by
    change
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + (u - 1)) * a))
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hhyperbolic :
      (realHyperbolicShellPhase ε u : ℂ) = Hs + Hp := by
    rw [← mellinShellPhase_imaginary]
    unfold mellinShellPhase
    try dsimp [Hs, Hp]
    congr 1
    · apply intervalIntegral.integral_congr
      intro a ha
      change
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) *
            (Complex.I * (u : ℂ))) - 1) =
          (shortShellDensity ε a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)
      congr 1
      have harg :
          (a : ℂ) * (Complex.I * (u : ℂ)) =
            ((u * a : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.cos_mul_I,
        ← Complex.ofReal_cosh]
    · apply intervalIntegral.integral_congr
      intro a ha
      change
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) *
            (Complex.I * (u : ℂ))) - 1) =
          (positiveShellDensity ε a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)
      congr 1
      have harg :
          (a : ℂ) * (Complex.I * (u : ℂ)) =
            ((u * a : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.cos_mul_I,
        ← Complex.ofReal_cosh]
  have hs :
      (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
        (shortShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T) =
        Fs - Hs +
          Complex.I * ((T * Ls : ℝ) : ℂ) -
          ((T ^ 2 / 2 * Vs : ℝ) : ℂ) := by
    rw [hshort]
    change
      Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) +
          ((T ^ 2 / 2 *
            (∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
              shortShellDensity ε a * a ^ 2 *
                Real.cosh (u * a)) : ℝ) : ℂ) =
        Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) -
          ((T ^ 2 / 2 * Vs : ℝ) : ℂ)
    rw [hvariance]
    push_cast
    ring
  have hp :
      (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
        (positiveShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T) =
        Fp - Hp +
          Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 * Vp : ℝ) : ℂ) := by
    rw [hpositive]
    change
      Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 *
            (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
              positiveShellDensity ε a * a ^ 2 *
                Real.cosh (u * a)) : ℝ) : ℂ) =
        Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 * Vp : ℝ) : ℂ)
    rw [hpositivevariance]
  unfold saddleSourceShellQuadraticRemainder
  rw [hs, hp, hhyperbolic]
  change
    (Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) -
        ((T ^ 2 / 2 * Vs : ℝ) : ℂ)) +
      (Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
        ((T ^ 2 / 2 * Vp : ℝ) : ℂ)) =
      (Fs + Fp) - (Hs + Hp) +
        Complex.I * ((T * (Ls + Lp) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * (Vp - Vs) : ℝ) : ℂ)
  push_cast
  ring

private theorem saddleSourceShellCenteredPhase_cubic_remainder_norm_le
    {ε ℓ : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 ≤ ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hmargin : ∀ a ∈ Icc (ε ^ 3) (10 * Real.log (1 / ε)),
      0 ≤ (1 - 10 * ε * (1 + a)))
    (u T : ℝ) :
    ‖saddleSourceShellCenteredPhase ε ℓ u T +
        ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
          T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
        |T| ^ 3 := by
  have hshort :=
    saddleSourceShortShellQuadraticRemainder_norm_le
      hε horder hmargin u T
  have hpositive :=
    saddleSourcePositiveShellQuadraticRemainder_norm_le
      hε u T
  have hsum :
      ‖saddleSourceShellQuadraticRemainder ε u T‖ ≤
        (|T| ^ 3 / 6) *
          upperNetShellThirdMoment ε (u - 1) := by
    unfold saddleSourceShellQuadraticRemainder
      upperNetShellThirdMoment
    calc
      ‖(∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) +
        (∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          (positiveShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T)‖ ≤
        ‖∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ +
        ‖∫ a in (ε⁻¹ ^ 3)..(ε⁻¹ ^ 3 + 1),
          (positiveShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ :=
          norm_add_le _ _
      _ ≤ (|T| ^ 3 / 6) *
          upperShortShellThirdMoment ε (u - 1) +
        (|T| ^ 3 / 6) *
          upperPositiveShellThirdMoment ε (u - 1) :=
          add_le_add hshort hpositive
      _ = (|T| ^ 3 / 6) *
          (upperPositiveShellThirdMoment ε (u - 1) +
            upperShortShellThirdMoment ε (u - 1)) := by
          ring
  have heq :
      saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ) =
        (ℓ : ℂ) *
          saddleSourceShellQuadraticRemainder ε u T := by
    rw [saddleSourceShellQuadraticRemainder_eq
      hε horder u T]
    unfold saddleSourceShellCenteredPhase
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hℓ]
  calc
    ℓ * ‖saddleSourceShellQuadraticRemainder ε u T‖ ≤
      ℓ * ((|T| ^ 3 / 6) *
        upperNetShellThirdMoment ε (u - 1)) :=
        mul_le_mul_of_nonneg_left hsum hℓ
    _ = (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
      |T| ^ 3 := by
      ring

end

section

open Filter MeasureTheory Set
open scoped Topology

private theorem upperImaginaryExp_centered_norm_le
    (x : ℝ) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ)‖ ≤
      x ^ 2 / 2 + |x| ^ 3 / 6 := by
  let q : ℂ := ((x ^ 2 / 2 : ℝ) : ℂ)
  have hq : ‖q‖ = x ^ 2 / 2 := by
    try dsimp [q]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  calc
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ)‖ =
      ‖(upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) + q) - q‖ := by
        congr 1
        ring
    _ ≤ ‖upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) + q‖ + ‖q‖ :=
      norm_sub_le _ _
    _ ≤ |x| ^ 3 / 6 + x ^ 2 / 2 := by
      rw [hq]
      try dsimp [q]
      exact add_le_add
        (upperImaginaryExp_quadratic_remainder_norm_le x)
        (le_refl _)
    _ = x ^ 2 / 2 + |x| ^ 3 / 6 := by ring

private theorem upperGammaCenteredKernel_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    IntegrableOn (upperGammaCenteredKernel ℓ η T)
      (Ioi 0) := by
  have hvariance :=
    upperGammaVarianceDensity_integrable hℓ hη
  have hthird :=
    upperGammaThirdMomentDensity_integrable hℓ hη
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) +
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    (hvariance.const_mul (T ^ 2 / 2)).add
      (hthird.const_mul (|T| ^ 3 / 6))
  have hmeas : Measurable
      (upperGammaCenteredKernel ℓ η T) := by
    unfold upperGammaCenteredKernel upperImaginaryExp
      upperGammaMeasureDensity
    fun_prop
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi]
    with a ha
  have hdensity :=
    upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold upperGammaCenteredKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  calc
    ‖upperImaginaryExp (a * T) - 1 -
        Complex.I * ((a * T : ℝ) : ℂ)‖ *
          upperGammaMeasureDensity ℓ η a ≤
      ((a * T) ^ 2 / 2 + |a * T| ^ 3 / 6) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right
        (upperImaginaryExp_centered_norm_le (a * T))
        hdensity.le
    _ = (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) +
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [abs_mul, abs_of_pos ha]
      ring

private noncomputable def upperGammaQuadraticKernel
    (ℓ η T a : ℝ) : ℂ :=
  (((a * T) ^ 2 / 2 *
    upperGammaMeasureDensity ℓ η a : ℝ) : ℂ)

private theorem upperGammaQuadraticKernel_integrable
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    IntegrableOn (upperGammaQuadraticKernel ℓ η T)
      (Ioi 0) := by
  have hvariance :=
    upperGammaVarianceDensity_integrable hℓ hη
  have hreal : IntegrableOn
      (fun a : ℝ =>
        (T ^ 2 / 2) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) := hvariance.const_mul (T ^ 2 / 2)
  have hcomplex : IntegrableOn
      (fun a : ℝ =>
        (((T ^ 2 / 2) *
          (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ))
      (Ioi 0) := hreal.ofReal
  apply hcomplex.congr_fun _ measurableSet_Ioi
  intro a ha
  unfold upperGammaQuadraticKernel
  apply congrArg Complex.ofReal
  ring

private theorem integral_upperGammaQuadraticKernel
    {ℓ η : ℝ} (hℓ : 0 < ℓ)
    (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ∫ a : ℝ in Ioi 0,
          (((T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro a ha
          unfold upperGammaQuadraticKernel
          apply congrArg Complex.ofReal
          ring
    _ = ((∫ a : ℝ in Ioi 0,
          (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) :=
          integral_ofReal (𝕜 := ℂ)
    _ = (((T ^ 2 / 2) *
          (∫ a : ℝ in Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) := by
          rw [MeasureTheory.integral_const_mul]
    _ = ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
          congr 1
          unfold upperGammaVariance
          field_simp [hℓ.ne']

private noncomputable def upperGammaCubicRemainderKernel
    (ℓ η T a : ℝ) : ℂ :=
  (upperImaginaryExp (a * T) - 1 -
    Complex.I * ((a * T : ℝ) : ℂ) +
      (((a * T) ^ 2 / 2 : ℝ) : ℂ)) *
        (upperGammaMeasureDensity ℓ η a : ℂ)

private theorem upperGammaCubicRemainderKernel_norm_le
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (T : ℝ) :
    ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
      (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
  have hdensity :=
    upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold upperGammaCubicRemainderKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  calc
    ‖upperImaginaryExp (a * T) - 1 -
        Complex.I * ((a * T : ℝ) : ℂ) +
          (((a * T) ^ 2 / 2 : ℝ) : ℂ)‖ *
            upperGammaMeasureDensity ℓ η a ≤
      (|a * T| ^ 3 / 6) *
        upperGammaMeasureDensity ℓ η a :=
      mul_le_mul_of_nonneg_right
        (upperImaginaryExp_quadratic_remainder_norm_le
          (a * T)) hdensity.le
    _ = (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [abs_mul, abs_of_pos ha]
      ring

private theorem upperGammaCenteredPhase_add_quadratic_eq_integral
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) =
      ∫ a : ℝ in Ioi 0,
        upperGammaCubicRemainderKernel ℓ η T a := by
  have hcenter :=
    upperGammaCenteredKernel_integrable hℓ hη T
  have hquad :=
    upperGammaQuadraticKernel_integrable hℓ hη T
  rw [← integral_upperGammaQuadraticKernel hℓ T]
  unfold upperGammaCenteredPhase
  rw [← MeasureTheory.integral_add hcenter hquad]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  unfold upperGammaCenteredKernel
    upperGammaQuadraticKernel
    upperGammaCubicRemainderKernel
  push_cast
  ring

private theorem upperGammaCenteredPhase_cubic_remainder_norm_le
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
  have hmajor : IntegrableOn
      (fun a : ℝ =>
        (|T| ^ 3 / 6) *
          (a ^ 3 * upperGammaMeasureDensity ℓ η a))
      (Ioi 0) :=
    (upperGammaThirdMomentDensity_integrable hℓ hη).const_mul
      (|T| ^ 3 / 6)
  have hpoint :
      ∀ᵐ a : ℝ ∂volume.restrict (Ioi 0),
        ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
          (|T| ^ 3 / 6) *
            (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with a ha
    exact upperGammaCubicRemainderKernel_norm_le hℓ ha T
  calc
    ‖upperGammaCenteredPhase ℓ η T +
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ)‖ =
      ‖∫ a : ℝ in Ioi 0,
        upperGammaCubicRemainderKernel ℓ η T a‖ := by
          rw [upperGammaCenteredPhase_add_quadratic_eq_integral
            hℓ hη T]
    _ ≤ ∫ a : ℝ in Ioi 0,
        (|T| ^ 3 / 6) *
          (a ^ 3 * upperGammaMeasureDensity ℓ η a) :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor hpoint
    _ = (|T| ^ 3 / 6) *
        (∫ a : ℝ in Ioi 0,
          a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (ℓ * upperGammaThirdMoment ℓ η / 6) * |T| ^ 3 := by
      unfold upperGammaThirdMoment
      field_simp [hℓ.ne']

end
end CohnElkies
