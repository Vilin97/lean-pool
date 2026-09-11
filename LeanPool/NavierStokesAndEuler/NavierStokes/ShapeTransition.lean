/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingSchedule
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The explicit shape transition and its reset-prefix debts

The cutoff and target shape are the actual functions from `OutgoingSchedule`.
Input field bounds are pointwise bounds, not assumptions on the five row debts.
All constants in the estimates may be chosen before the final large `C`.
-/

@[expose] public section


noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ShapeTransition

/-- Log shape, given by `Real.log (OutgoingSchedule.shape eta)`. -/
noncomputable def logShape (eta : ℝ) : ℝ := Real.log (OutgoingSchedule.shape eta)

theorem logShape_contDiff : ContDiff ℝ ∞ logShape :=
  OutgoingSchedule.shape_contDiff.log (fun eta => (OutgoingSchedule.shape_pos eta).ne')

theorem exp_logShape (eta : ℝ) : Real.exp (logShape eta) = OutgoingSchedule.shape eta :=
  Real.exp_log (OutgoingSchedule.shape_pos eta)

/-- Blend, given by `(1 - OutgoingSchedule.sigma (p.1 / T)) * li p.2 + OutgoingSchedule.sigma
(p.1 / T) * logShape p.2`. -/
noncomputable def blend (T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - OutgoingSchedule.sigma (p.1 / T)) * li p.2 +
    OutgoingSchedule.sigma (p.1 / T) * logShape p.2

/-- Log profile, given by `-Real.log C + p.1 / 10 + blend T li p`. -/
noncomputable def logProfile (C T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -Real.log C + p.1 / 10 + blend T li p

/-- Amplitude, given by `Real.exp (p.1 / 10 + blend T li p)`. -/
noncomputable def amplitude (T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (p.1 / 10 + blend T li p)

/-- Angular, given by `Real.exp (logProfile C T li p)`. -/
noncomputable def angular (C T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (logProfile C T li p)

/-- Axial, given by `Gi p.2`. -/
noncomputable def axial (Gi : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := Gi p.2

theorem blend_contDiff (T : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) :
    ContDiff ℝ ∞ (blend T li) :=
  ((contDiff_const.sub (OutgoingSchedule.sigma_contDiff.comp
    (contDiff_fst.div_const T))).mul (hli.comp contDiff_snd)).add
      ((OutgoingSchedule.sigma_contDiff.comp (contDiff_fst.div_const T)).mul
        (logShape_contDiff.comp contDiff_snd))

theorem logProfile_contDiff (C T : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) :
    ContDiff ℝ ∞ (logProfile C T li) :=
  (contDiff_const.add (contDiff_fst.div_const 10)).add (blend_contDiff T hli)

theorem amplitude_contDiff (T : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) :
    ContDiff ℝ ∞ (amplitude T li) :=
  ((contDiff_fst.div_const 10).add (blend_contDiff T hli)).exp

theorem angular_contDiff (C T : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) :
    ContDiff ℝ ∞ (angular C T li) := (logProfile_contDiff C T hli).exp

theorem axial_contDiff {Gi : ℝ → ℝ} (hGi : ContDiff ℝ ∞ Gi) :
    ContDiff ℝ ∞ (axial Gi) := hGi.comp contDiff_snd

theorem angular_pos (C T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) :
    0 < angular C T li p := Real.exp_pos _

theorem log_angular (C T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) :
    Real.log (angular C T li p) = logProfile C T li p := Real.log_exp _

theorem angular_eq_inv_mul {C : ℝ} (hC : 0 < C) (T : ℝ) (li : ℝ → ℝ)
    (p : ℝ × ℝ) : angular C T li p = C⁻¹ * amplitude T li p := by
  unfold angular logProfile amplitude
  rw [show -Real.log C + p.1 / 10 + blend T li p =
    -Real.log C + (p.1 / 10 + blend T li p) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hC]

theorem angular_before {C T y : ℝ} (hC : 0 < C) (hT : 0 < T) (hy : y ≤ 0)
    (li : ℝ → ℝ) (eta : ℝ) :
    angular C T li (y, eta) = C⁻¹ * Real.exp (y / 10 + li eta) := by
  rw [angular_eq_inv_mul hC]
  simp [amplitude, blend,
    OutgoingSchedule.sigma_zero (div_nonpos_of_nonpos_of_nonneg hy hT.le)]

theorem angular_after {C T y : ℝ} (hC : 0 < C) (hT : 0 < T) (hy : T ≤ y)
    (li : ℝ → ℝ) (eta : ℝ) :
    angular C T li (y, eta) = C⁻¹ * Real.exp (y / 10) * OutgoingSchedule.shape eta := by
  rw [angular_eq_inv_mul hC]
  simp only [amplitude, blend,
    OutgoingSchedule.sigma_one ((le_div_iff₀ hT).mpr (by simpa using hy)),
    sub_self, zero_mul, one_mul, zero_add, Real.exp_add, exp_logShape]
  ring

theorem angular_initial {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (li : ℝ → ℝ) (eta : ℝ) :
    angular C T li (0, eta) = C⁻¹ * Real.exp (li eta) := by
  simpa using angular_before hC hT (le_refl 0) li eta

/-! Smoothness above and exact equalities on both closed half-lines give the
actual smooth gluing. The following statement records all radial jets on the
open constant-profile regions as well. -/

theorem angular_jets_before {C T y : ℝ} (hC : 0 < C) (hT : 0 < T) (hy : y < 0)
    (li : ℝ → ℝ) (eta : ℝ) (n : ℕ) :
    iteratedDeriv n (fun s => angular C T li (s, eta)) y =
      iteratedDeriv n (fun s => C⁻¹ * Real.exp (s / 10 + li eta)) y := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [eventually_lt_nhds hy] with s hs
  exact angular_before hC hT hs.le li eta

theorem angular_jets_after {C T y : ℝ} (hC : 0 < C) (hT : 0 < T) (hy : T < y)
    (li : ℝ → ℝ) (eta : ℝ) (n : ℕ) :
    iteratedDeriv n (fun s => angular C T li (s, eta)) y =
      iteratedDeriv n (fun s => C⁻¹ * Real.exp (s / 10) *
        OutgoingSchedule.shape eta) y := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [eventually_gt_nhds hy] with s hs
  exact angular_after hC hT hs.le li eta

/-! ## A duration chosen before `C` -/

theorem sigma_deriv_zero_left {x : ℝ} (hx : x < 0) :
    deriv OutgoingSchedule.sigma x = 0 := by
  have he : OutgoingSchedule.sigma =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact OutgoingSchedule.sigma_zero hy.le
  rw [he.deriv_eq]
  exact deriv_const x 0

theorem sigma_deriv_zero_right {x : ℝ} (hx : 1 < x) :
    deriv OutgoingSchedule.sigma x = 0 := by
  have he : OutgoingSchedule.sigma =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact OutgoingSchedule.sigma_one hy.le
  rw [he.deriv_eq]
  exact deriv_const x 1

theorem sigma_deriv_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv OutgoingSchedule.sigma x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (OutgoingSchedule.sigma_contDiff.continuous_deriv (by simp)).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x < 0
  · simp [sigma_deriv_zero_left hx]
  by_cases hx' : 1 < x
  · simp [sigma_deriv_zero_right hx']
  exact (show |deriv OutgoingSchedule.sigma x| ≤ K from
    hK x ⟨le_of_not_gt hx, le_of_not_gt hx'⟩).trans (le_max_left _ _)

/-- Logarithmic slope, given by `3 / 5 + deriv OutgoingSchedule.sigma (p.1 / T) / T * (logShape
p.2 - li p.2)`. -/
noncomputable def logarithmicSlope (T : ℝ) (li : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  3 / 5 + deriv OutgoingSchedule.sigma (p.1 / T) / T * (logShape p.2 - li p.2)

theorem logProfile_hasDerivAt (C T : ℝ) (li : ℝ → ℝ) (y eta : ℝ) :
    HasDerivAt (fun s => logProfile C T li (s, eta))
      (logarithmicSlope T li (y, eta) - 1 / 2) y := by
  have hs : HasDerivAt OutgoingSchedule.sigma (deriv OutgoingSchedule.sigma (y / T))
      (y / T) := (OutgoingSchedule.sigma_contDiff.differentiable (by
          simp)).differentiableAt.hasDerivAt
  have hc : HasDerivAt (fun s => OutgoingSchedule.sigma (s / T))
      (deriv OutgoingSchedule.sigma (y / T) / T) y := by
    convert! hs.comp y ((hasDerivAt_id y).div_const T) using 1; simp [div_eq_mul_inv]
  have h := ((hasDerivAt_const y (-Real.log C)).add ((hasDerivAt_id y).div_const 10)).add
    ((((hasDerivAt_const y 1).sub hc).mul_const (li eta)).add (hc.mul_const (logShape eta)))
  convert! h using 1; dsimp [logProfile, blend, logarithmicSlope]; ring

theorem logarithmicSlope_eq (C T : ℝ) (li : ℝ → ℝ) (y eta : ℝ) :
    logarithmicSlope T li (y, eta) =
      1 / 2 + deriv (fun s => logProfile C T li (s, eta)) y := by
  rw [(logProfile_hasDerivAt C T li y eta).deriv]
  ring

theorem logarithmicSlope_eq_actual (C T : ℝ) (li : ℝ → ℝ) (y eta : ℝ) :
    logarithmicSlope T li (y, eta) =
      1 / 2 + deriv (fun s => Real.log (angular C T li (s, eta))) y := by
  simp only [log_angular]
  exact logarithmicSlope_eq C T li y eta

theorem logarithmicSlope_bounds {T K B : ℝ} {li : ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (_ : 0 ≤ B)
    (hSigma : ∀ x, |deriv OutgoingSchedule.sigma x| ≤ K)
    (hDuration : 20 * K * B ≤ T) {y eta : ℝ}
    (hData : |logShape eta - li eta| ≤ B) :
    11 / 20 ≤ logarithmicSlope T li (y, eta) ∧
      logarithmicSlope T li (y, eta) ≤ 13 / 20 := by
  have hb : |deriv OutgoingSchedule.sigma (y / T) / T * (logShape eta - li eta)| ≤
      1 / 20 := by
    rw [abs_mul, abs_div, abs_of_pos hT]
    calc
      _ ≤ (K / T) * B := mul_le_mul (div_le_div_of_nonneg_right (hSigma _) hT.le)
        hData (abs_nonneg _) (div_nonneg hK hT.le)
      _ ≤ 1 / 20 := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hT).mpr (by linarith)
  have hab := abs_le.mp hb
  dsimp [logarithmicSlope]
  constructor <;> linarith

theorem exists_duration (B : ℝ) (hB : 0 ≤ B) :
    ∃ T : ℝ, 0 < T ∧ ∀ (li : ℝ → ℝ) (C y eta : ℝ),
      |logShape eta - li eta| ≤ B →
      11 / 20 ≤ 1 / 2 + deriv (fun s => logProfile C T li (s, eta)) y ∧
      1 / 2 + deriv (fun s => logProfile C T li (s, eta)) y ≤ 13 / 20 := by
  obtain ⟨K, hK, hSigma⟩ := sigma_deriv_bounded
  refine ⟨1 + 20 * K * B, by positivity, fun li C y eta hData => ?_⟩
  rw [← logarithmicSlope_eq C]
  exact logarithmicSlope_bounds (by positivity) hK hB hSigma (by linarith) hData

theorem blend_abs_le {T B : ℝ} {li : ℝ → ℝ} {y eta : ℝ}
    (hli : |li eta| ≤ B) (hf : |logShape eta| ≤ B) : |blend T li (y, eta)| ≤ B := by
  have hs0 := OutgoingSchedule.sigma_nonneg (y / T)
  have hs1 := OutgoingSchedule.sigma_le_one (y / T)
  calc
    _ ≤ |(1 - OutgoingSchedule.sigma (y / T)) * li eta| +
        |OutgoingSchedule.sigma (y / T) * logShape eta| := abs_add_le _ _
    _ = (1 - OutgoingSchedule.sigma (y / T)) * |li eta| +
        OutgoingSchedule.sigma (y / T) * |logShape eta| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_nonneg hs0]
    _ ≤ (1 - OutgoingSchedule.sigma (y / T)) * B +
        OutgoingSchedule.sigma (y / T) * B := add_le_add
      (mul_le_mul_of_nonneg_left hli (sub_nonneg.mpr hs1))
      (mul_le_mul_of_nonneg_left hf hs0)
    _ = B := by ring

theorem amplitude_le {T B : ℝ} {li : ℝ → ℝ} {y eta : ℝ}
    (hy : y ≤ T) (hli : |li eta| ≤ B) (hf : |logShape eta| ≤ B) :
    amplitude T li (y, eta) ≤ Real.exp (T / 10 + B) := by
  apply Real.exp_le_exp.mpr
  exact add_le_add (div_le_div_of_nonneg_right hy (by norm_num))
    ((le_abs_self _).trans (blend_abs_le hli hf))

/-! ## Uniform finite parameter jets from the input jets -/

theorem blend_iteratedDeriv (T y : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li)
    (n : ℕ) (eta : ℝ) :
    iteratedDeriv n (fun e => blend T li (y, e)) eta =
      (1 - OutgoingSchedule.sigma (y / T)) * iteratedDeriv n li eta +
        OutgoingSchedule.sigma (y / T) * iteratedDeriv n logShape eta := by
  change iteratedDeriv n ((fun e => (1 - OutgoingSchedule.sigma (y / T)) * li e) +
    (fun e => OutgoingSchedule.sigma (y / T) * logShape e)) eta = _
  rw [iteratedDeriv_add
    ((contDiff_const.mul hli).of_le (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from
        le_top))).contDiffAt
    ((contDiff_const.mul logShape_contDiff).of_le
      (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
    iteratedDeriv_const_mul _ (hli.of_le
      (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
    iteratedDeriv_const_mul _ (logShape_contDiff.of_le
      (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]

theorem convex_abs_le {s a b B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a| ≤ B) (hb : |b| ≤ B) : |(1 - s) * a + s * b| ≤ B := by
  calc
    _ ≤ |(1 - s) * a| + |s * b| := abs_add_le _ _
    _ = (1 - s) * |a| + s * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_nonneg hs0]
    _ ≤ (1 - s) * B + s * B := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hs1))
      (mul_le_mul_of_nonneg_left hb hs0)
    _ = B := by ring

theorem blend_jet_bound (T y : ℝ) {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li)
    (n : ℕ) {eta B : ℝ} (hl : |iteratedDeriv n li eta| ≤ B)
    (hf : |iteratedDeriv n logShape eta| ≤ B) :
    |iteratedDeriv n (fun e => blend T li (y, e)) eta| ≤ B := by
  rw [blend_iteratedDeriv T y hli]
  exact convex_abs_le (OutgoingSchedule.sigma_nonneg _) (OutgoingSchedule.sigma_le_one _) hl hf

theorem amplitude_jet_bound {T y B : ℝ} {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li)
    (hB : 1 ≤ B) (hy : y ≤ T) (n : ℕ) (eta : ℝ)
    (hl : ∀ i ≤ n, |iteratedDeriv i li eta| ≤ B)
    (hf : ∀ i ≤ n, |iteratedDeriv i logShape eta| ≤ B) :
    |iteratedDeriv n (fun e => amplitude T li (y, e)) eta| ≤
      n.factorial * Real.exp (T / 10 + B) * B ^ n := by
  let q : ℝ → ℝ := fun e => y / 10 + blend T li (y, e)
  have hq : ContDiff ℝ ∞ q := contDiff_const.add
    ((blend_contDiff T hli).comp (contDiff_const.prodMk contDiff_id))
  have hqle : q eta ≤ T / 10 + B := add_le_add
    (div_le_div_of_nonneg_right hy (by norm_num))
    ((le_abs_self _).trans (blend_abs_le (hl 0 (Nat.zero_le _)) (hf 0 (Nat.zero_le _))))
  have hExp : ∀ i ≤ n, ‖iteratedFDeriv ℝ i Real.exp (q eta)‖ ≤ Real.exp (T / 10 + B) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have he : iteratedDeriv i Real.exp = Real.exp := by
      simpa using iteratedDeriv_exp_const_mul i 1
    rw [he, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hqle
  have hqjet : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q eta‖ ≤ B ^ i := by
    intro i hi hin
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    change |iteratedDeriv i (fun e => y / 10 + blend T li (y, e)) eta| ≤ B ^ i
    rw [iteratedDeriv_const_add (by omega : 0 < i)]
    exact (blend_jet_bound T y hli i (hl i hin) (hf i hin)).trans
      (le_self_pow₀ hB (by omega))
  have h := norm_iteratedFDeriv_comp_le Real.contDiff_exp hq
    (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))
    eta hExp hqjet
  simpa only [Function.comp_def, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, amplitude, q] using h

theorem angular_iteratedDeriv {C : ℝ} (hC : 0 < C) (T y : ℝ)
    {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) (n : ℕ) (eta : ℝ) :
    iteratedDeriv n (fun e => angular C T li (y, e)) eta =
      C⁻¹ * iteratedDeriv n (fun e => amplitude T li (y, e)) eta := by
  have he : (fun e => angular C T li (y, e)) =
      fun e => C⁻¹ * amplitude T li (y, e) := funext (fun e => angular_eq_inv_mul hC T li (y, e))
  rw [he]
  exact iteratedDeriv_const_mul
    _ (((amplitude_contDiff T hli).comp (contDiff_const.prodMk contDiff_id)).of_le
      (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem angular_jet_bound {C T y B : ℝ} (hC : 0 < C)
    {li : ℝ → ℝ} (hli : ContDiff ℝ ∞ li) (hB : 1 ≤ B) (hy : y ≤ T)
    (n : ℕ) (eta : ℝ)
    (hl : ∀ i ≤ n, |iteratedDeriv i li eta| ≤ B)
    (hf : ∀ i ≤ n, |iteratedDeriv i logShape eta| ≤ B) :
    |iteratedDeriv n (fun e => angular C T li (y, e)) eta| ≤
      (n.factorial * Real.exp (T / 10 + B) * B ^ n) / C := by
  rw [angular_iteratedDeriv hC T y hli, abs_mul, abs_inv, abs_of_pos hC]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (amplitude_jet_bound hli hB hy n eta hl hf) (inv_nonneg.mpr hC.le)

/-! ## The reset clock and exact ideal matching -/

/-- Reset radius, given by `Xi * (C * P) ^ 10`. -/
noncomputable def resetRadius (Xi C P : ℝ) : ℝ := Xi * (C * P) ^ 10

/-- Separation, given by `Real.exp T / (C * P) ^ 10`. -/
noncomputable def separation (T C P : ℝ) : ℝ := Real.exp T / (C * P) ^ 10

/-- Reset clock, given by `y - 10 * Real.log (C * P)`. -/
noncomputable def resetClock (C P y : ℝ) : ℝ := y - 10 * Real.log (C * P)

/-- Ideal angular, given by `P * OutgoingSchedule.shape p.2 * Real.exp (p.1 / 10)`. -/
noncomputable def idealAngular (P : ℝ) (p : ℝ × ℝ) : ℝ :=
  P * OutgoingSchedule.shape p.2 * Real.exp (p.1 / 10)

theorem idealAngular_contDiff (P : ℝ) : ContDiff ℝ ∞ (idealAngular P) :=
  (contDiff_const.mul (OutgoingSchedule.shape_contDiff.comp contDiff_snd)).mul
    (contDiff_fst.div_const 10).exp

theorem angular_after_reset_clock {C P T y : ℝ} (hC : 0 < C) (hP : 0 < P)
    (hT : 0 < T) (hy : T ≤ y) (li : ℝ → ℝ) (eta : ℝ) :
    angular C T li (y, eta) = idealAngular P (resetClock C P y, eta) := by
  rw [angular_after hC hT hy]
  have he : Real.exp (resetClock C P y / 10) = Real.exp (y / 10) / (C * P) := by
    rw [resetClock, show (y - 10 * Real.log (C * P)) / 10 =
      y / 10 - Real.log (C * P) by ring, Real.exp_sub, Real.exp_log (mul_pos hC hP)]
  dsimp only [idealAngular]
  rw [he]
  field_simp [hC.ne', hP.ne']

theorem separation_pos (T : ℝ) {C P : ℝ} (hC : 0 < C) (hP : 0 < P) :
    0 < separation T C P := div_pos (Real.exp_pos _) (pow_pos (mul_pos hC hP) _)

theorem resetRadius_mul_separation (Xi T C P : ℝ) (hCP : C * P ≠ 0) :
    resetRadius Xi C P * separation T C P = Xi * Real.exp T := by
  unfold resetRadius separation
  field_simp [(mul_ne_zero_iff.mp hCP).1, (mul_ne_zero_iff.mp hCP).2]

theorem separation_tendsto (T : ℝ) {P : ℝ} (_ : P ≠ 0) :
    Tendsto (fun C : ℝ => separation T C P) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun C : ℝ => C⁻¹) atTop (𝓝 0)).pow 10
  have hh := h.const_mul (Real.exp T * (P⁻¹) ^ 10)
  simpa [separation, div_eq_mul_inv, inv_pow, mul_inv_rev, mul_pow, zero_pow,
    mul_zero, mul_assoc, mul_left_comm, mul_comm] using hh

theorem separation_eventually_before (T : ℝ) {P : ℝ} (hP : 0 < P) (clock : ℝ) :
    ∀ᶠ C : ℝ in atTop, separation T C P < Real.exp clock :=
  (separation_tendsto T hP.ne').eventually (gt_mem_nhds (Real.exp_pos clock))

/-! ## Actual restoration on reset-clock times `-8` to `-7` -/

/-- Restore, given by `(1 - OutgoingSchedule.sigma (p.1 + 8)) * Gi p.2 + OutgoingSchedule.sigma
(p.1 + 8) * (4 * p.2)`. -/
noncomputable def restore (Gi : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - OutgoingSchedule.sigma (p.1 + 8)) * Gi p.2 +
    OutgoingSchedule.sigma (p.1 + 8) * (4 * p.2)

theorem restore_contDiff {Gi : ℝ → ℝ} (hGi : ContDiff ℝ ∞ Gi) :
    ContDiff ℝ ∞ (restore Gi) :=
  ((contDiff_const.sub (OutgoingSchedule.sigma_contDiff.comp (contDiff_fst.add contDiff_const))).mul
    (hGi.comp contDiff_snd)).add
      ((OutgoingSchedule.sigma_contDiff.comp (contDiff_fst.add contDiff_const)).mul
        (contDiff_const.mul contDiff_snd))

theorem restore_before {z : ℝ} (hz : z ≤ -8) (Gi : ℝ → ℝ) (eta : ℝ) :
    restore Gi (z, eta) = Gi eta := by
  simp [restore, OutgoingSchedule.sigma_zero (by linarith : z + 8 ≤ 0)]

theorem restore_after {z : ℝ} (hz : -7 ≤ z) (Gi : ℝ → ℝ) (eta : ℝ) :
    restore Gi (z, eta) = 4 * eta := by
  simp [restore, OutgoingSchedule.sigma_one (by linarith : 1 ≤ z + 8)]

theorem restore_sub (Gi : ℝ → ℝ) (z eta : ℝ) :
    restore Gi (z, eta) - 4 * eta =
      (1 - OutgoingSchedule.sigma (z + 8)) * (Gi eta - 4 * eta) := by
  dsimp [restore]
  ring

theorem restore_error_le (Gi : ℝ → ℝ) (z eta : ℝ) :
    |restore Gi (z, eta) - 4 * eta| ≤ |Gi eta - 4 * eta| := by
  rw [restore_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (OutgoingSchedule.sigma_le_one _))]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (by linarith [OutgoingSchedule.sigma_nonneg (z + 8)])

theorem restore_error_jet (Gi : ℝ → ℝ) (hGi : ContDiff ℝ ∞ Gi) (z eta : ℝ) (n : ℕ) :
    iteratedDeriv n (fun e => restore Gi (z, e) - 4 * e) eta =
      (1 - OutgoingSchedule.sigma (z + 8)) * iteratedDeriv n (fun e => Gi e - 4 * e) eta := by
  have he : (fun e => restore Gi (z, e) - 4 * e) =
      fun e => (1 - OutgoingSchedule.sigma (z + 8)) * (Gi e - 4 * e) :=
    funext (restore_sub Gi z)
  rw [he]
  exact iteratedDeriv_const_mul _ ((hGi.sub (contDiff_const.mul contDiff_id)).of_le
    (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem restore_error_jet_le (Gi : ℝ → ℝ) (hGi : ContDiff ℝ ∞ Gi) (z eta : ℝ) (n : ℕ) :
    |iteratedDeriv n (fun e => restore Gi (z, e) - 4 * e) eta| ≤
      |iteratedDeriv n (fun e => Gi e - 4 * e) eta| := by
  rw [restore_error_jet Gi hGi, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr (OutgoingSchedule.sigma_le_one _))]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (by linarith [OutgoingSchedule.sigma_nonneg (z + 8)])

/-! ## A smooth physical-radius implementation, including the old axis piece -/

/-- The harmless zero extension avoids evaluating the logarithmic clock at the
axis. On every positive radius this is exactly the cutoff in (19). -/
noncomputable def radialSwitch (Xi T X : ℝ) : ℝ :=
  if X ≤ Xi / 2 then 0 else OutgoingSchedule.sigma (Real.log (X / Xi) / T)

theorem radialSwitch_zero {Xi T X : ℝ} (hXi : 0 < Xi) (hT : 0 < T) (hX : X ≤ Xi) :
    radialSwitch Xi T X = 0 := by
  unfold radialSwitch
  split_ifs with h
  · rfl
  · apply OutgoingSchedule.sigma_zero
    apply div_nonpos_of_nonpos_of_nonneg _ hT.le
    apply Real.log_nonpos
    · exact (div_pos (by linarith : 0 < X) hXi).le
    · exact (div_le_one hXi).mpr hX

theorem radialSwitch_eq {Xi T X : ℝ} (hXi : 0 < Xi) (hT : 0 < T) (hX : 0 < X) :
    radialSwitch Xi T X = OutgoingSchedule.sigma (Real.log (X / Xi) / T) := by
  unfold radialSwitch
  split_ifs with h
  · symm
    apply OutgoingSchedule.sigma_zero
    apply div_nonpos_of_nonpos_of_nonneg _ hT.le
    exact Real.log_nonpos (div_pos hX hXi).le ((div_le_one hXi).mpr (by linarith))
  · rfl

theorem radialSwitch_contDiff {Xi T : ℝ} (hXi : 0 < Xi) (hT : 0 < T) :
    ContDiff ℝ ∞ (radialSwitch Xi T) := by
  apply contDiff_iff_contDiffAt.mpr
  intro X
  by_cases hX : X < Xi
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) X).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hX] with Y hY
    exact radialSwitch_zero hXi hT hY.le
  · have hXpos : 0 < X := hXi.trans_le (le_of_not_gt hX)
    have hc : ContDiffAt ℝ ∞ (fun X : ℝ => OutgoingSchedule.sigma (Real.log (X / Xi) / T)) X :=
      OutgoingSchedule.sigma_contDiff.contDiffAt.comp X
        (((Real.contDiffAt_log.mpr (div_pos hXpos hXi).ne').comp X
          (contDiffAt_id.div_const Xi)).div_const T)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hXpos] with Y hY
    exact radialSwitch_eq hXi hT hY

/-- The supplied old normalized field is continued by its held power law past
`Xi`. Multiplication by this explicit smooth factor performs the transition. -/
noncomputable def shapeField (Xi T : ℝ) (li : ℝ → ℝ) (old : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  old p * Real.exp (radialSwitch Xi T p.1 * (logShape p.2 - li p.2))

theorem shapeField_contDiff {Xi T : ℝ} (hXi : 0 < Xi) (hT : 0 < T)
    {li : ℝ → ℝ} {old : ℝ × ℝ → ℝ} (hli : ContDiff ℝ ∞ li)
    (hold : ContDiff ℝ ∞ old) : ContDiff ℝ ∞ (shapeField Xi T li old) :=
  hold.mul (((radialSwitch_contDiff hXi hT).comp contDiff_fst).mul
    ((logShape_contDiff.comp contDiff_snd).sub (hli.comp contDiff_snd))).exp

theorem shapeField_before {Xi T X : ℝ} (hXi : 0 < Xi) (hT : 0 < T) (hX : X ≤ Xi)
    (li : ℝ → ℝ) (old : ℝ × ℝ → ℝ) (eta : ℝ) :
    shapeField Xi T li old (X, eta) = old (X, eta) := by
  simp [shapeField, radialSwitch_zero hXi hT hX]

theorem shapeField_eq_profile {Xi C T X : ℝ} (hXi : 0 < Xi) (hC : 0 < C)
    (hT : 0 < T) (hX : 0 < X) (li : ℝ → ℝ) (old : ℝ × ℝ → ℝ) (eta : ℝ)
    (hold : old (X, eta) = C⁻¹ * Real.exp (Real.log (X / Xi) / 10 + li eta) /
      Real.sqrt (2 * X)) :
    shapeField Xi T li old (X, eta) =
      angular C T li (Real.log (X / Xi), eta) / Real.sqrt (2 * X) := by
  rw [shapeField, hold, radialSwitch_eq hXi hT hX, angular_eq_inv_mul hC]
  dsimp only [amplitude, blend]
  have he : Real.log (X / Xi) / 10 +
      ((1 - OutgoingSchedule.sigma (Real.log (X / Xi) / T)) * li eta +
        OutgoingSchedule.sigma (Real.log (X / Xi) / T) * logShape eta) =
      (Real.log (X / Xi) / 10 + li eta) +
        OutgoingSchedule.sigma (Real.log (X / Xi) / T) * (logShape eta - li eta) := by ring
  rw [he]
  simp only [Real.exp_add]
  ring

theorem shapeField_jet_bound {Xi C T X B K : ℝ} (hXi : 0 < Xi) (hC : 0 < C)
    (hT : 0 < T) (_ : 0 ≤ X) (hXL : X ≤ Xi * Real.exp T)
    {li : ℝ → ℝ} {old : ℝ × ℝ → ℝ} (hli : ContDiff ℝ ∞ li) (hB : 1 ≤ B)
    (hK : 0 ≤ K) (n : ℕ) (eta : ℝ)
    (hAxis : X ≤ Xi → |iteratedDeriv n (fun e => old (X, e)) eta| ≤ K / C)
    (hHold : Xi ≤ X → ∀ e, old (X, e) =
      C⁻¹ * Real.exp (Real.log (X / Xi) / 10 + li e) / Real.sqrt (2 * X))
    (hl : ∀ i ≤ n, |iteratedDeriv i li eta| ≤ B)
    (hf : ∀ i ≤ n, |iteratedDeriv i logShape eta| ≤ B) :
    |iteratedDeriv n (fun e => shapeField Xi T li old (X, e)) eta| ≤
      (K + (n.factorial * Real.exp (T / 10 + B) * B ^ n) / Real.sqrt (2 * Xi)) / C := by
  by_cases hXXi : X ≤ Xi
  · have he : (fun e => shapeField Xi T li old (X, e)) = fun e => old (X, e) :=
      funext (shapeField_before hXi hT hXXi li old)
    rw [he]
    refine (hAxis hXXi).trans ?_
    apply div_le_div_of_nonneg_right _ hC.le
    exact le_add_of_nonneg_right (by positivity)
  · have hXpos : 0 < X := hXi.trans (lt_of_not_ge hXXi)
    have hy : Real.log (X / Xi) ≤ T :=
      (Real.log_le_iff_le_exp (div_pos hXpos hXi)).mpr
        ((div_le_iff₀ hXi).mpr (by linarith))
    have he : (fun e => shapeField Xi T li old (X, e)) =
        fun e => (Real.sqrt (2 * X))⁻¹ * angular C T li (Real.log (X / Xi), e) := by
      funext e
      rw [shapeField_eq_profile hXi hC hT hXpos li old e (hHold (le_of_not_ge hXXi) e)]
      ring
    have hslice : ContDiff ℝ ∞ (fun e => angular C T li (Real.log (X / Xi), e)) :=
      (angular_contDiff C T hli).comp (contDiff_const.prodMk contDiff_id)
    rw [he, iteratedDeriv_const_mul _ (hslice.of_le (WithTop.coe_le_coe.mpr
      (show (n : ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
      abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hb := angular_jet_bound hC hli hB hy n eta hl hf
    have hs : (Real.sqrt (2 * X))⁻¹ ≤ (Real.sqrt (2 * Xi))⁻¹ := by
      apply inv_anti₀ (Real.sqrt_pos.2 (by positivity))
      exact Real.sqrt_le_sqrt (by linarith)
    calc
      _ ≤ (Real.sqrt (2 * Xi))⁻¹ *
          ((n.factorial * Real.exp (T / 10 + B) * B ^ n) / C) :=
        mul_le_mul hs hb (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        have hkC : 0 ≤ K / C := div_nonneg hK hC.le
        convert! le_add_of_nonneg_left hkC using 1; ring

/-! ## Actual compact integrals and their parameter jets -/

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem partial_jet_continuous {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => iteratedDeriv n (fun e => F (p.1, e)) p.2) := by
  have hd : Continuous (fun p : ℝ × ℝ => iteratedFDeriv ℝ n (fun e => F (p.1, e)) p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun X e => F (X, e)) n p.1 p.2 hF.contDiffAt).continuousAt
  simpa only [iteratedDeriv_eq_iteratedFDeriv] using
    hd.eval_const (fun _ : Fin n => (1 : ℝ))

theorem integral_iteratedDeriv {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (eta : ℝ) :
    iteratedDeriv n (fun e => ∫ x in (0 : ℝ)..r, F (x, e)) eta =
      ∫ x in (0 : ℝ)..r, iteratedDeriv n (fun e => F (x, e)) eta := by
  have hsm : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) r), ContDiff ℝ ∞ (fun e => F (x, e)) :=
    Eventually.of_forall (fun x => hF.comp (contDiff_const.prodMk contDiff_id))
  have hmeas : ∀ k e, AEStronglyMeasurable
      (fun x => iteratedDeriv k (fun q => F (x, q)) e) (volume.restrict (Ioc (0 : ℝ) r)) := by
    intro k e
    exact ((partial_jet_continuous hF k).comp (continuous_id.prodMk
        continuous_const)).aestronglyMeasurable
  have hdom : SmoothParameterIntegral.LocallyDominatedDeriv (fun e x => F (x, e))
      (volume.restrict (Ioc (0 : ℝ) r)) := by
    intro k e
    obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) r)).prod
      (isCompact_closedBall e 1)).exists_bound_of_continuousOn (partial_jet_continuous hF
          k).continuousOn
    refine ⟨1, zero_lt_one, fun _ => B, integrable_const B, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro q hq
    exact hB (x, q) ⟨⟨hx.1.le, hx.2⟩, Metric.ball_subset_closedBall hq⟩
  simpa only [intervalIntegral.integral_of_le hr] using
    SmoothParameterIntegral.iteratedDeriv_integral hsm hmeas hdom n eta

theorem integral_jet_bound {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {r B : ℝ} (hr : 0 ≤ r) (n : ℕ) (eta : ℝ)
    (hB : ∀ x ∈ Ioc (0 : ℝ) r, |iteratedDeriv n (fun e => F (x, e)) eta| ≤ B) :
    |iteratedDeriv n (fun e => ∫ x in (0 : ℝ)..r, F (x, e)) eta| ≤ B * r := by
  rw [integral_iteratedDeriv hF hr]
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => iteratedDeriv n (fun e => F (x, e)) eta)
      (fun x hx => hB x ((uIoc_of_le hr) ▸ hx))

theorem product_jet_bound {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (eta : ℝ) {A B : ℝ} (hA : 0 ≤ A) (_ : 0 ≤ B)
    (hfb : ∀ k ≤ n, |iteratedDeriv k f eta| ≤ A)
    (hgb : ∀ k ≤ n, |iteratedDeriv k g eta| ≤ B) :
    |iteratedDeriv n (fun e => f e * g e) eta| ≤ 2 ^ n * A * B := by
  have h := norm_iteratedFDeriv_mul_le hf hg eta (nat_le_infty n)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  refine h.trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hfb k hkn) (Nat.cast_nonneg _)
      · exact hgb (n - k) (Nat.sub_le _ _)
      · exact abs_nonneg _
      · positivity
    _ = 2 ^ n * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl

/-! ## The five actual scaled history rows -/

/-- Scaled E, given by `Real.sqrt (2 * R * p.1) * f p`. -/
noncomputable def scaledE (R : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * R * p.1) * f p

/-- Row M, given by `∫ x in (0 : ℝ)..r, u (x, eta)`. -/
noncomputable def rowM (u : ℝ × ℝ → ℝ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, u (x, eta)

/-- Row I, given by `∫ x in (0 : ℝ)..r, Real.sqrt (2 * x) * scaledE R f (x, eta)`. -/
noncomputable def rowI (R : ℝ) (f : ℝ × ℝ → ℝ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, Real.sqrt (2 * x) * scaledE R f (x, eta)

/-- Row J, given by `∫ x in (0 : ℝ)..r, u (x, eta) * Real.sqrt (2 * x) * scaledE R f (x, eta)`. -/
noncomputable def rowJ (R : ℝ) (u f : ℝ × ℝ → ℝ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, u (x, eta) * Real.sqrt (2 * x) * scaledE R f (x, eta)

/-- Row S, given by `∫ x in (0 : ℝ)..r, u (x, eta) ^ 2 - scaledE R f (x, eta) ^ 2 / 2`. -/
noncomputable def rowS (R : ℝ) (u f : ℝ × ℝ → ℝ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, u (x, eta) ^ 2 - scaledE R f (x, eta) ^ 2 / 2

/-- Row P, given by `∫ x in (0 : ℝ)..r, scaledE R f (x, eta) ^ 2 / (2 * x)`. -/
noncomputable def rowP (R : ℝ) (f : ℝ × ℝ → ℝ) (r eta : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, scaledE R f (x, eta) ^ 2 / (2 * x)

theorem sqrt_scaled_product {R x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) :
    Real.sqrt (2 * x) * Real.sqrt (2 * R * x) = 2 * Real.sqrt R * x := by
  rw [show 2 * R * x = R * (2 * x) by ring, Real.sqrt_mul hR]
  have hs := Real.sq_sqrt (show 0 ≤ 2 * x by positivity)
  nlinarith [Real.sqrt_nonneg R]

theorem scaledE_sq {R x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x)
    (f : ℝ × ℝ → ℝ) (eta : ℝ) :
    scaledE R f (x, eta) ^ 2 = 2 * R * x * f (x, eta) ^ 2 := by
  rw [scaledE, mul_pow, Real.sq_sqrt (by positivity)]

theorem rowI_normalized {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (f : ℝ × ℝ → ℝ) (eta : ℝ) :
    rowI R f r eta = ∫ x in (0 : ℝ)..r, (2 * Real.sqrt R * x) * f (x, eta) := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0 ≤ x := ((uIcc_of_le hr) ▸ hx).1
  dsimp only [scaledE]
  rw [← mul_assoc, sqrt_scaled_product hR hx0]

theorem rowJ_normalized {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (u f : ℝ × ℝ → ℝ) (eta : ℝ) :
    rowJ R u f r eta =
      ∫ x in (0 : ℝ)..r, (2 * Real.sqrt R * x) * (u (x, eta) * f (x, eta)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0 ≤ x := ((uIcc_of_le hr) ▸ hx).1
  dsimp only [scaledE]
  calc
    _ = (Real.sqrt (2 * x) * Real.sqrt (2 * R * x)) * (u (x, eta) * f (x, eta)) := by ring
    _ = _ := by rw [sqrt_scaled_product hR hx0]

theorem rowS_normalized {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (u f : ℝ × ℝ → ℝ) (eta : ℝ) :
    rowS R u f r eta =
      ∫ x in (0 : ℝ)..r, u (x, eta) ^ 2 - (R * x) * f (x, eta) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0 ≤ x := ((uIcc_of_le hr) ▸ hx).1
  dsimp only
  rw [scaledE_sq hR hx0]
  ring

theorem rowP_normalized {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (f : ℝ × ℝ → ℝ) (eta : ℝ) :
    rowP R f r eta = ∫ x in (0 : ℝ)..r, R * f (x, eta) ^ 2 := by
  unfold rowP
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  have hx' : x ∈ Ioc (0 : ℝ) r := (uIoc_of_le hr) ▸ hx
  rw [scaledE_sq hR hx'.1.le]
  field_simp [hx'.1.ne']


/-- All five finite-jet estimates are estimates of the actual row integrals.
Only the parameter jets of the two input fields are bounded in the hypotheses. -/
theorem rows_jet_bounds {R r B K C : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 < C)
    {u f : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (eta : ℝ)
    (hub : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => u (x, e)) eta| ≤ B)
    (hfb : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => f (x, e)) eta| ≤ K / C) :
    |iteratedDeriv n (rowM u r) eta| ≤ B * r ∧
    |iteratedDeriv n (rowI R f r) eta| ≤ 2 * Real.sqrt R * (K / C) * r ^ 2 ∧
    |iteratedDeriv n (rowJ R u f r) eta| ≤ 2 * Real.sqrt R * (2 ^ n * B * (K / C)) * r ^ 2 ∧
    |iteratedDeriv n (rowS R u f r) eta| ≤
      (2 ^ n * B ^ 2 + R * r * (2 ^ n * (K / C) ^ 2)) * r ∧
    |iteratedDeriv n (rowP R f r) eta| ≤ R * (2 ^ n * (K / C) ^ 2) * r := by
  have hKC : 0 ≤ K / C := div_nonneg hK hC.le
  have hus (x : ℝ) : ContDiff ℝ ∞ (fun e => u (x, e)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hfs (x : ℝ) : ContDiff ℝ ∞ (fun e => f (x, e)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have huf (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      |iteratedDeriv n (fun e => u (x, e) * f (x, e)) eta| ≤ 2 ^ n * B * (K / C) :=
    product_jet_bound (hus x) (hfs x) n eta hB hKC (hub x hx) (hfb x hx)
  have huu (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      |iteratedDeriv n (fun e => u (x, e) ^ 2) eta| ≤ 2 ^ n * B ^ 2 := by
    simpa only [pow_two, mul_assoc] using
      product_jet_bound (hus x) (hus x) n eta hB hB (hub x hx) (hub x hx)
  have hff (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) r) :
      |iteratedDeriv n (fun e => f (x, e) ^ 2) eta| ≤ 2 ^ n * (K / C) ^ 2 := by
    simpa only [pow_two, mul_assoc] using
      product_jet_bound (hfs x) (hfs x) n eta hKC hKC (hfb x hx) (hfb x hx)
  have hM := integral_jet_bound hu hr n eta (fun x hx => hub x hx n le_rfl)
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  · have he : rowI R f r = fun e => ∫ x in (0 : ℝ)..r, (2 * Real.sqrt R * x) * f (x, e) :=
      funext (rowI_normalized hR hr f)
    rw [he]
    have hi := integral_jet_bound
      (F := fun p : ℝ × ℝ => (2 * Real.sqrt R * p.1) * f p)
      (((contDiff_const.mul contDiff_const).mul contDiff_fst).mul hf) hr n eta
      (B := (2 * Real.sqrt R * r) * (K / C)) ?_
    · convert! hi using 1; ring
    · intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      dsimp only
      rw [iteratedDeriv_const_mul _ ((hfs x).of_le (nat_le_infty n)).contDiffAt,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt R * x)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx.2 (by positivity))
        (hfb x hx n le_rfl) (abs_nonneg _) (by positivity)
  · have he : rowJ R u f r = fun e => ∫ x in (0 : ℝ)..r,
        (2 * Real.sqrt R * x) * (u (x, e) * f (x, e)) :=
      funext (rowJ_normalized hR hr u f)
    rw [he]
    have hi := integral_jet_bound
      (F := fun p : ℝ × ℝ => (2 * Real.sqrt R * p.1) * (u p * f p))
      (((contDiff_const.mul contDiff_const).mul contDiff_fst).mul (hu.mul hf)) hr n eta
      (B := (2 * Real.sqrt R * r) * (2 ^ n * B * (K / C))) ?_
    · convert! hi using 1; ring
    · intro x hx
      have hx0 : 0 ≤ x := hx.1.le
      dsimp only
      rw [iteratedDeriv_const_mul _ (((hus x).mul (hfs x)).of_le (nat_le_infty n)).contDiffAt,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt R * x)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx.2 (by positivity))
        (huf x hx) (abs_nonneg _) (by positivity)
  · have he : rowS R u f r = fun e => ∫ x in (0 : ℝ)..r,
        u (x, e) ^ 2 - (R * x) * f (x, e) ^ 2 := funext (rowS_normalized hR hr u f)
    rw [he]
    apply integral_jet_bound ((hu.pow 2).sub ((contDiff_const.mul contDiff_fst).mul (hf.pow 2))) hr
        n eta
    intro x hx
    have hsub := iteratedDeriv_sub (x := eta) (((hus x).pow 2).of_le (nat_le_infty n)).contDiffAt
      (((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => R * x)).mul
        ((hfs x).pow 2)).of_le (nat_le_infty n)).contDiffAt
    change |iteratedDeriv n ((fun e => u (x, e) ^ 2) - (fun e => (R * x) * f (x, e) ^ 2)) eta| ≤ _
    rw [hsub, iteratedDeriv_const_mul _ (((hfs x).pow 2).of_le (nat_le_infty n)).contDiffAt]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (mul_nonneg hR hx.1.le)]
    exact add_le_add (huu x hx) (mul_le_mul (mul_le_mul_of_nonneg_left hx.2 hR)
      (hff x hx) (abs_nonneg _) (mul_nonneg hR hr))
  · have he : rowP R f r = fun e => ∫ x in (0 : ℝ)..r, R * f (x, e) ^ 2 :=
      funext (rowP_normalized hR hr f)
    rw [he]
    apply integral_jet_bound (contDiff_const.mul (hf.pow 2)) hr n eta
    intro x hx
    rw [iteratedDeriv_const_mul _ (((hfs x).pow 2).of_le (nat_le_infty n)).contDiffAt,
      abs_mul, abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_left (hff x hx) hR

/-! The following coefficient contains only fixed upstream data. -/

/-- Prefix coefficient, given by `B + 2 * (L + 1) * K + 2 * (L + 1) * (2 ^ n * B * K) + 2 ^ n *
(B ^ 2 + L * K ^ 2)`. -/
noncomputable def prefixCoefficient (n : ℕ) (B K L : ℝ) : ℝ :=
  B + 2 * (L + 1) * K + 2 * (L + 1) * (2 ^ n * B * K) + 2 ^ n * (B ^ 2 + L * K ^ 2)

/-- Prefix jet size as an element of `ℝ`. -/
noncomputable def prefixJetSize (n : ℕ) (R r : ℝ) (u f : ℝ × ℝ → ℝ) (eta : ℝ) : ℝ :=
  |iteratedDeriv n (rowM u r) eta| + |iteratedDeriv n (rowI R f r) eta| +
    |iteratedDeriv n (rowJ R u f r) eta| + |iteratedDeriv n (rowS R u f r) eta| +
    |iteratedDeriv n (rowP R f r) eta|

theorem prefixJetSize_bound {R r L B K C : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hRL : R * r = L) (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 1 ≤ C)
    {u f : ℝ × ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (eta : ℝ)
    (hub : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => u (x, e)) eta| ≤ B)
    (hfb : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => f (x, e)) eta| ≤ K / C) :
    prefixJetSize n R r u f eta ≤
      prefixCoefficient n B K L * r + (2 ^ n * L * K ^ 2) / C ^ 2 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hL : 0 ≤ L := hRL ▸ mul_nonneg hR hr
  have hKC : 0 ≤ K / C := div_nonneg hK hCpos.le
  have hKCle : K / C ≤ K := div_le_self hK hC
  have hroot : Real.sqrt R ≤ R + 1 := by
    linarith [Real.sqrt_nonneg R, Real.sq_sqrt hR, sq_nonneg (Real.sqrt R - 1)]
  have hrr : Real.sqrt R * r ≤ L + 1 := calc
    _ ≤ (R + 1) * r := mul_le_mul_of_nonneg_right hroot hr
    _ = L + r := by rw [add_mul, hRL, one_mul]
    _ ≤ L + 1 := add_le_add_right hr1 L
  obtain ⟨hM, hI, hJ, hS, hP⟩ := rows_jet_bounds hR hr hB hK hCpos hu hf n eta hub hfb
  have hI' : |iteratedDeriv n (rowI R f r) eta| ≤ (2 * (L + 1) * K) * r := by
    apply hI.trans
    calc
      _ = (2 * (Real.sqrt R * r) * (K / C)) * r := by ring
      _ ≤ _ := by gcongr
  have hJ' : |iteratedDeriv n (rowJ R u f r) eta| ≤
      (2 * (L + 1) * (2 ^ n * B * K)) * r := by
    apply hJ.trans
    calc
      _ = (2 * (Real.sqrt R * r) * (2 ^ n * B * (K / C))) * r := by ring
      _ ≤ _ := by gcongr
  have hS' : |iteratedDeriv n (rowS R u f r) eta| ≤
      (2 ^ n * (B ^ 2 + L * K ^ 2)) * r := by
    apply hS.trans
    rw [hRL]
    calc
      _ ≤ (2 ^ n * B ^ 2 + L * (2 ^ n * K ^ 2)) * r := by gcongr
      _ = _ := by ring
  have hP' : |iteratedDeriv n (rowP R f r) eta| ≤ (2 ^ n * L * K ^ 2) / C ^ 2 := by
    apply hP.trans_eq
    rw [← hRL, div_pow]
    ring
  dsimp [prefixJetSize, prefixCoefficient]
  linarith

theorem prefix_bound_tendsto (n : ℕ) (B K L T P : ℝ) :
    Tendsto (fun C : ℝ => prefixCoefficient n B K L * separation T C P +
      (2 ^ n * L * K ^ 2) / C ^ 2) atTop (𝓝 0) := by
  have hs : Tendsto (fun C : ℝ => separation T C P) atTop (𝓝 0) := by
    by_cases hP : P = 0
    · simp only [separation, hP, mul_zero, zero_pow (by decide : 10 ≠ 0), div_zero]
      exact tendsto_const_nhds
    · exact separation_tendsto T hP
  have hp := ((tendsto_inv_atTop_zero : Tendsto (fun C : ℝ => C⁻¹) atTop (𝓝 0)).pow 2).const_mul
    (2 ^ n * L * K ^ 2)
  convert! (hs.const_mul (prefixCoefficient n B K L)).add hp using 1 <;>
    simp [div_eq_mul_inv, inv_pow]

/-- Uniformity in the external parameter is obtained from uniform input-jet
bounds. The fixed duration, data bounds, and physical prefix length precede `C`. -/
theorem eventually_small_prefix (n : ℕ) {B K Xi T P : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hXi : 0 < Xi) (hP : 0 < P) (S : Set ℝ)
    (u f : ℝ → ℝ × ℝ → ℝ)
    (hu : ∀ C, 1 ≤ C → ContDiff ℝ ∞ (u C))
    (hf : ∀ C, 1 ≤ C → ContDiff ℝ ∞ (f C))
    (hub : ∀ C, 1 ≤ C → ∀ eta ∈ S, ∀ x ∈ Ioc (0 : ℝ) (separation T C P),
      ∀ k ≤ n, |iteratedDeriv k (fun e => u C (x, e)) eta| ≤ B)
    (hfb : ∀ C, 1 ≤ C → ∀ eta ∈ S, ∀ x ∈ Ioc (0 : ℝ) (separation T C P),
      ∀ k ≤ n, |iteratedDeriv k (fun e => f C (x, e)) eta| ≤ K / C)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ C : ℝ in atTop, ∀ eta ∈ S,
      prefixJetSize n (resetRadius Xi C P) (separation T C P) (u C) (f C) eta < eps := by
  have hsmall := (prefix_bound_tendsto n B K (Xi * Real.exp T) T P).eventually (gt_mem_nhds heps)
  have hsep := (separation_tendsto T hP.ne').eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hsep] with C hC hb hs
  intro eta heta
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  exact (prefixJetSize_bound (by unfold resetRadius; positivity)
    (separation_pos T hCpos hP).le hs.le
    (resetRadius_mul_separation Xi T C P (mul_pos hCpos hP).ne') hB hK hC
    (hu C hC) (hf C hC) n eta (hub C hC eta heta) (hfb C hC eta heta)).trans_lt hb

/-! ## The ideal prefix has small rows too -/

/-- Ideal weight I, given by `∫ x in (0 : ℝ)..r, Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)`. -/
noncomputable def idealWeightI (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)

/-- Ideal weight S, given by `∫ x in (0 : ℝ)..r, x ^ (1 / 5 : ℝ) / 2`. -/
noncomputable def idealWeightS (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, x ^ (1 / 5 : ℝ) / 2

/-- Ideal weight P, given by `∫ x in (0 : ℝ)..r, x ^ (1 / 5 : ℝ) / (2 * x)`. -/
noncomputable def idealWeightP (r : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..r, x ^ (1 / 5 : ℝ) / (2 * x)

theorem idealWeightI_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |idealWeightI r| ≤ 2 * r := by
  simpa only [idealWeightI, Real.norm_eq_abs, sub_zero, abs_of_nonneg hr] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)) (C := 2) (a := 0) (b := r) (by
        intro x hx
        have hx' : x ∈ Ioc (0 : ℝ) r := (uIoc_of_le hr) ▸ hx
        have hx0 : 0 ≤ x := hx'.1.le
        have hx1 : x ≤ 1 := hx'.2.trans hr1
        have hs : Real.sqrt (2 * x) ≤ 2 := by
          nlinarith [Real.sq_sqrt (show 0 ≤ 2 * x by positivity), Real.sqrt_nonneg (2 * x)]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.rpow_nonneg hx0 _)]
        exact (mul_le_mul hs (Real.rpow_le_one hx0 hx1 (by norm_num))
          (Real.rpow_nonneg hx0 _) (by norm_num)).trans_eq (by ring)))

theorem idealWeightS_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |idealWeightS r| ≤ r / 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => x ^ (1 / 5 : ℝ) / 2) (C := 1 / 2) (a := 0) (b := r) (by
      intro x hx
      have hx' : x ∈ Ioc (0 : ℝ) r := (uIoc_of_le hr) ▸ hx
      have hx0 : 0 ≤ x := hx'.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_one hx'.1.le (hx'.2.trans hr1) (by norm_num)) (by norm_num))
  calc
    |idealWeightS r| ≤ (1 / 2) * |r - 0| := h
    _ = r / 2 := by rw [sub_zero, abs_of_nonneg hr]; ring

theorem idealWeightP_eq {r : ℝ} (hr : 0 ≤ r) :
    idealWeightP r = (5 / 2) * r ^ (1 / 5 : ℝ) := by
  calc
    _ = ∫ x in (0 : ℝ)..r, (1 / 2 : ℝ) * x ^ (-4 / 5 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      have hx' : x ∈ Ioc (0 : ℝ) r := (uIoc_of_le hr) ▸ hx
      rw [show (-4 / 5 : ℝ) = (1 / 5 : ℝ) - 1 by norm_num,
        Real.rpow_sub hx'.1, Real.rpow_one]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by
          norm_num : (-1 : ℝ) < -4 / 5))]
      norm_num
      ring

/-- Ideal M, given by `r * G eta`. -/
noncomputable def idealM (G : ℝ → ℝ) (r eta : ℝ) : ℝ := r * G eta

/-- Ideal I, given by `idealWeightI r * A eta`. -/
noncomputable def idealI (A : ℝ → ℝ) (r eta : ℝ) : ℝ := idealWeightI r * A eta

/-- Ideal J, given by `idealWeightI r * (G eta * A eta)`. -/
noncomputable def idealJ (G A : ℝ → ℝ) (r eta : ℝ) : ℝ := idealWeightI r * (G eta * A eta)

/-- Ideal S, given by `r * G eta ^ 2 - idealWeightS r * A eta ^ 2`. -/
noncomputable def idealS (G A : ℝ → ℝ) (r eta : ℝ) : ℝ :=
  r * G eta ^ 2 - idealWeightS r * A eta ^ 2

/-- Ideal P, given by `idealWeightP r * A eta ^ 2`. -/
noncomputable def idealP (A : ℝ → ℝ) (r eta : ℝ) : ℝ := idealWeightP r * A eta ^ 2

theorem ideal_power_square {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 10 : ℝ)) ^ 2 = x ^ (1 / 5 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem ideal_rows_are_integrals {r : ℝ} (hr : 0 ≤ r) (G A : ℝ → ℝ) (eta : ℝ) :
    idealM G r eta = (∫ _x in (0 : ℝ)..r, G eta) ∧
    idealI A r eta = (∫ x in (0 : ℝ)..r, Real.sqrt (2 * x) * (A eta * x ^ (1 / 10 : ℝ))) ∧
    idealJ G A r eta = (∫ x in (0 : ℝ)..r, G eta * Real.sqrt (2 * x) *
      (A eta * x ^ (1 / 10 : ℝ))) ∧
    idealS G A r eta = (∫ x in (0 : ℝ)..r, G eta ^ 2 - (A eta * x ^ (1 / 10 : ℝ)) ^ 2 / 2) ∧
    idealP A r eta = (∫ x in (0 : ℝ)..r, (A eta * x ^ (1 / 10 : ℝ)) ^ 2 / (2 * x)) := by
  refine ⟨by simp [idealM], ?_, ?_, ?_, ?_⟩
  · rw [idealI, idealWeightI, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · rw [idealJ, idealWeightI, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · have hpow : IntervalIntegrable (fun x : ℝ => x ^ (1 / 5 : ℝ) / 2 * A eta ^ 2) volume 0 r :=
      ((intervalIntegral.intervalIntegrable_rpow' (by
          norm_num : (-1 : ℝ) < 1 / 5)).div_const 2).mul_const _
    have he : (∫ x in (0 : ℝ)..r, G eta ^ 2 - (A eta * x ^ (1 / 10 : ℝ)) ^ 2 / 2) =
        ∫ x in (0 : ℝ)..r, G eta ^ 2 - (x ^ (1 / 5 : ℝ) / 2) * A eta ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := ((uIcc_of_le hr) ▸ hx).1
      dsimp only
      rw [mul_pow, ideal_power_square hx0]
      ring
    rw [he, intervalIntegral.integral_sub intervalIntegrable_const hpow,
      intervalIntegral.integral_mul_const]
    simp [idealS, idealWeightS]
  · rw [idealP, idealWeightP, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := ((uIcc_of_le hr) ▸ hx).1
    dsimp only
    rw [mul_pow, ideal_power_square hx0]
    ring

/-- Ideal prefix jet size as an element of `ℝ`. -/
noncomputable def idealPrefixJetSize (n : ℕ) (r : ℝ) (G A : ℝ → ℝ) (eta : ℝ) : ℝ :=
  |iteratedDeriv n (idealM G r) eta| + |iteratedDeriv n (idealI A r) eta| +
    |iteratedDeriv n (idealJ G A r) eta| + |iteratedDeriv n (idealS G A r) eta| +
    |iteratedDeriv n (idealP A r) eta|

/-- Ideal prefix coefficient, given by `B + 2 * K + 2 * (2 ^ n * B * K) + 2 ^ n * B ^ 2 + (2 ^ n
* K ^ 2) / 2`. -/
noncomputable def idealPrefixCoefficient (n : ℕ) (B K : ℝ) : ℝ :=
  B + 2 * K + 2 * (2 ^ n * B * K) + 2 ^ n * B ^ 2 + (2 ^ n * K ^ 2) / 2

theorem idealPrefixJetSize_bound {r B K : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) {G A : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hA : ContDiff ℝ ∞ A) (n : ℕ) (eta : ℝ)
    (hGb : ∀ k ≤ n, |iteratedDeriv k G eta| ≤ B)
    (hAb : ∀ k ≤ n, |iteratedDeriv k A eta| ≤ K) :
    idealPrefixJetSize n r G A eta ≤ idealPrefixCoefficient n B K * r +
      (5 / 2) * (2 ^ n * K ^ 2) * r ^ (1 / 5 : ℝ) := by
  have hGG : |iteratedDeriv n (fun e => G e ^ 2) eta| ≤ 2 ^ n * B ^ 2 := by
    simpa only [pow_two, mul_assoc] using product_jet_bound hG hG n eta hB hB hGb hGb
  have hAA : |iteratedDeriv n (fun e => A e ^ 2) eta| ≤ 2 ^ n * K ^ 2 := by
    simpa only [pow_two, mul_assoc] using product_jet_bound hA hA n eta hK hK hAb hAb
  have hGA := product_jet_bound hG hA n eta hB hK hGb hAb
  have hm : |iteratedDeriv n (idealM G r) eta| ≤ B * r := by
    change |iteratedDeriv n (fun e => r * G e) eta| ≤ _
    rw [iteratedDeriv_const_mul _ (hG.of_le (nat_le_infty n)).contDiffAt,
      abs_mul, abs_of_nonneg hr]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hGb n le_rfl) hr
  have hi : |iteratedDeriv n (idealI A r) eta| ≤ 2 * K * r := by
    change |iteratedDeriv n (fun e => idealWeightI r * A e) eta| ≤ _
    rw [iteratedDeriv_const_mul _ (hA.of_le (nat_le_infty n)).contDiffAt, abs_mul]
    convert! mul_le_mul (idealWeightI_bound hr hr1) (hAb n le_rfl)
      (abs_nonneg _) (by positivity) using 1; ring
  have hj : |iteratedDeriv n (idealJ G A r) eta| ≤ 2 * (2 ^ n * B * K) * r := by
    change |iteratedDeriv n (fun e => idealWeightI r * (G e * A e)) eta| ≤ _
    rw [iteratedDeriv_const_mul _ ((hG.mul hA).of_le (nat_le_infty n)).contDiffAt, abs_mul]
    convert! mul_le_mul (idealWeightI_bound hr hr1) hGA (abs_nonneg _) (by
        positivity) using 1; ring
  have hs : |iteratedDeriv n (idealS G A r) eta| ≤
      (2 ^ n * B ^ 2 + (2 ^ n * K ^ 2) / 2) * r := by
    change |iteratedDeriv n ((fun e => r * G e ^ 2) - (fun e => idealWeightS r * A e ^ 2)) eta| ≤ _
    rw [iteratedDeriv_sub ((contDiff_const.mul (hG.pow 2)).of_le (nat_le_infty n)).contDiffAt
      ((contDiff_const.mul (hA.pow 2)).of_le (nat_le_infty n)).contDiffAt,
      iteratedDeriv_const_mul _ ((hG.pow 2).of_le (nat_le_infty n)).contDiffAt,
      iteratedDeriv_const_mul _ ((hA.pow 2).of_le (nat_le_infty n)).contDiffAt]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hr]
    have hleft := mul_le_mul_of_nonneg_left hGG hr
    have hright := mul_le_mul (idealWeightS_bound hr hr1) hAA (abs_nonneg _) (by positivity)
    linarith
  have hp : |iteratedDeriv n (idealP A r) eta| ≤
      (5 / 2) * (2 ^ n * K ^ 2) * r ^ (1 / 5 : ℝ) := by
    change |iteratedDeriv n (fun e => idealWeightP r * A e ^ 2) eta| ≤ _
    rw [iteratedDeriv_const_mul _ ((hA.pow 2).of_le (nat_le_infty n)).contDiffAt,
      abs_mul, idealWeightP_eq hr, abs_of_nonneg (by positivity)]
    convert! mul_le_mul_of_nonneg_left hAA
      (show 0 ≤ (5 / 2 : ℝ) * r ^ (1 / 5 : ℝ) by positivity) using 1; ring
  dsimp [idealPrefixJetSize, idealPrefixCoefficient]
  linarith

theorem separation_fifth_tendsto (T : ℝ) {P : ℝ} (hP : P ≠ 0) :
    Tendsto (fun C : ℝ => separation T C P ^ (1 / 5 : ℝ)) atTop (𝓝 0) := by
  have h := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 5)).tendsto 0
  simpa [Function.comp_def] using h.comp (separation_tendsto T hP)

/-! ## Genuine restoration debts on a positive compact interval -/

theorem smooth_parameter_interval {a b : ℝ} (hab : a ≤ b) {F : ℝ × ℝ → ℝ}
    (hF : ∀ x ∈ Icc a b, ∀ e, ContDiffAt ℝ ∞ F (x, e)) :
    ContDiff ℝ ∞ (fun e => ∫ x in a..b, F (x, e)) ∧
    ∀ n e, iteratedDeriv n (fun q => ∫ x in a..b, F (x, q)) e =
      ∫ x in a..b, iteratedDeriv n (fun q => F (x, q)) e := by
  have hj (k : ℕ) : ContinuousOn
      (fun p : ℝ × ℝ => iteratedDeriv k (fun e => F (p.1, e)) p.2) (Icc a b ×ˢ univ) := by
    rintro ⟨x, e⟩ hx
    have hc := (ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
      (fun x e => F (x, e)) k x e (hF x hx.1 e)).continuousAt.eval_const
        (fun _ : Fin k => (1 : ℝ))
    simpa only [iteratedDeriv_eq_iteratedFDeriv] using hc.continuousWithinAt
  have hs : ∀ᵐ x ∂volume.restrict (Ioc a b), ContDiff ℝ ∞ (fun e => F (x, e)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply contDiff_iff_contDiffAt.mpr
    intro e
    exact (hF x ⟨hx.1.le, hx.2⟩ e).comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hm : ∀ k e, AEStronglyMeasurable
      (fun x => iteratedDeriv k (fun q => F (x, q)) e) (volume.restrict (Ioc a b)) := by
    intro k e
    have hc : ContinuousOn (fun x => iteratedDeriv k (fun q => F (x, q)) e) (Icc a b) :=
      (hj k).comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, mem_univ
          _⟩)
    exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hd : SmoothParameterIntegral.LocallyDominatedDeriv (fun e x => F (x, e))
      (volume.restrict (Ioc a b)) := by
    intro k e
    have hc := (hj k).mono (Set.prod_mono (Subset.refl _) (subset_univ (Metric.closedBall e 1)))
    obtain ⟨B, hB⟩ := ((isCompact_Icc : IsCompact (Icc a b)).prod
      (isCompact_closedBall e 1)).exists_bound_of_continuousOn hc
    refine ⟨1, zero_lt_one, fun _ => B, integrable_const B, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro q hq
    exact hB (x, q) ⟨⟨hx.1.le, hx.2⟩, Metric.ball_subset_closedBall hq⟩
  constructor
  · simpa only [intervalIntegral.integral_of_le hab] using
      SmoothParameterIntegral.contDiff_integral_of_iteratedDeriv hs hm hd
  · intro n e
    simpa only [intervalIntegral.integral_of_le hab] using
      SmoothParameterIntegral.iteratedDeriv_integral hs hm hd n e

theorem integral_jet_bound_on {a b B : ℝ} (hab : a ≤ b) {F : ℝ × ℝ → ℝ}
    (hF : ∀ x ∈ Icc a b, ∀ e, ContDiffAt ℝ ∞ F (x, e)) (n : ℕ) (eta : ℝ)
    (hB : ∀ x ∈ Ioc a b, |iteratedDeriv n (fun e => F (x, e)) eta| ≤ B) :
    |iteratedDeriv n (fun e => ∫ x in a..b, F (x, e)) eta| ≤ B * (b - a) := by
  rw [(smooth_parameter_interval hab hF).2 n eta]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => iteratedDeriv n (fun e => F (x, e)) eta)
      (fun x hx => hB x ((uIoc_of_le hab) ▸ hx))

/-- Restore defect, given by `restore Gi (Real.log p.1, p.2) - 4 * p.2`. -/
noncomputable def restoreDefect (Gi : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  restore Gi (Real.log p.1, p.2) - 4 * p.2

/-- Restore density J, given by `(Real.sqrt (2 * p.1) * p.1 ^ (1 / 10 : ℝ)) * (restoreDefect Gi
p * A p.2)`. -/
noncomputable def restoreDensityJ (Gi A : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.sqrt (2 * p.1) * p.1 ^ (1 / 10 : ℝ)) * (restoreDefect Gi p * A p.2)

/-- Restore density S, given by `restoreDefect Gi p * (restore Gi (Real.log p.1, p.2) + 4 *
p.2)`. -/
noncomputable def restoreDensityS (Gi : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  restoreDefect Gi p * (restore Gi (Real.log p.1, p.2) + 4 * p.2)

theorem restoreDensityJ_eq (Gi A : ℝ → ℝ) (p : ℝ × ℝ) :
    restoreDensityJ Gi A p =
      restore Gi (Real.log p.1, p.2) * Real.sqrt (2 * p.1) * (A p.2 * p.1 ^ (1 / 10 : ℝ)) -
        (4 * p.2) * Real.sqrt (2 * p.1) * (A p.2 * p.1 ^ (1 / 10 : ℝ)) := by
  dsimp [restoreDensityJ, restoreDefect]
  ring

theorem restoreDensityS_eq (Gi : ℝ → ℝ) (p : ℝ × ℝ) :
    restoreDensityS Gi p = restore Gi (Real.log p.1, p.2) ^ 2 - (4 * p.2) ^ 2 := by
  dsimp [restoreDensityS, restoreDefect]
  ring

theorem restore_local_smooth {Gi A : ℝ → ℝ} (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A)
    {x : ℝ} (hx : 0 < x) (eta : ℝ) :
    ContDiffAt ℝ ∞ (restoreDefect Gi) (x, eta) ∧
    ContDiffAt ℝ ∞ (restoreDensityJ Gi A) (x, eta) ∧
    ContDiffAt ℝ ∞ (restoreDensityS Gi) (x, eta) := by
  have hr : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => restore Gi (Real.log p.1, p.2)) (x, eta) :=
    (restore_contDiff hGi).contDiffAt.comp (x, eta)
      (((Real.contDiffAt_log.mpr hx.ne').comp (x, eta) contDiffAt_fst).prodMk contDiffAt_snd)
  have hg : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => 4 * p.2) (x, eta) :=
    contDiffAt_const.mul contDiffAt_snd
  have hd : ContDiffAt ℝ ∞ (restoreDefect Gi) (x, eta) := hr.sub hg
  refine ⟨hd, ?_, hd.mul (hr.add hg)⟩
  exact (((contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity : (2 : ℝ) * x ≠ 0)).mul
    (contDiffAt_fst.rpow_const_of_ne hx.ne')).mul (hd.mul (hA.contDiffAt.comp (x, eta)
        contDiffAt_snd))

/-- Restore debt M, given by `∫ x in a..b, restoreDefect Gi (x, eta)`. -/
noncomputable def restoreDebtM (Gi : ℝ → ℝ) (a b eta : ℝ) : ℝ :=
  ∫ x in a..b, restoreDefect Gi (x, eta)

/-- Restore debt J, given by `∫ x in a..b, restoreDensityJ Gi A (x, eta)`. -/
noncomputable def restoreDebtJ (Gi A : ℝ → ℝ) (a b eta : ℝ) : ℝ :=
  ∫ x in a..b, restoreDensityJ Gi A (x, eta)

/-- Restore debt S, given by `∫ x in a..b, restoreDensityS Gi (x, eta)`. -/
noncomputable def restoreDebtS (Gi : ℝ → ℝ) (a b eta : ℝ) : ℝ :=
  ∫ x in a..b, restoreDensityS Gi (x, eta)

/-- Restore jet size as an element of `ℝ`. -/
noncomputable def restoreJetSize (n : ℕ) (Gi A : ℝ → ℝ) (a b eta : ℝ) : ℝ :=
  |iteratedDeriv n (restoreDebtM Gi a b) eta| +
    |iteratedDeriv n (restoreDebtJ Gi A a b) eta| +
    |iteratedDeriv n (restoreDebtS Gi a b) eta|

/-- The angular field is unchanged during restoration; its two pure-angular
rows have zero restoration debt. These are the other three actual row debts. -/
theorem restoreJetSize_bound {a b B K delta : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hd : 0 ≤ delta)
    {Gi A : ℝ → ℝ} (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A)
    (n : ℕ) (eta : ℝ)
    (hgb : ∀ k ≤ n, |iteratedDeriv k (fun e : ℝ => 4 * e) eta| ≤ B)
    (habound : ∀ k ≤ n, |iteratedDeriv k A eta| ≤ K)
    (hdef : ∀ k ≤ n, |iteratedDeriv k (fun e => Gi e - 4 * e) eta| ≤ delta) :
    restoreJetSize n Gi A a b eta ≤
      delta * (1 + 2 * (2 ^ n * K) + 2 ^ n * (delta + 2 * B)) := by
  have hlen : 0 ≤ b - a := sub_nonneg.mpr hab
  have hlen1 : b - a ≤ 1 := by linarith
  have hrSmooth (x : ℝ) : ContDiff ℝ ∞ (fun e => restore Gi (Real.log x, e)) :=
    (restore_contDiff hGi).comp (contDiff_const.prodMk contDiff_id)
  have hdSmooth (x : ℝ) : ContDiff ℝ ∞ (fun e => restoreDefect Gi (x, e)) :=
    (hrSmooth x).sub (contDiff_const.mul contDiff_id)
  have hdb (x : ℝ) (k : ℕ) (hk : k ≤ n) :
      |iteratedDeriv k (fun e => restoreDefect Gi (x, e)) eta| ≤ delta :=
    (restore_error_jet_le Gi hGi (Real.log x) eta k).trans (hdef k hk)
  have hpSmooth (x : ℝ) : ContDiff ℝ ∞ (fun e => restore Gi (Real.log x, e) + 4 * e) :=
    (hrSmooth x).add (contDiff_const.mul contDiff_id)
  have hpb (x : ℝ) (k : ℕ) (hk : k ≤ n) :
      |iteratedDeriv k (fun e => restore Gi (Real.log x, e) + 4 * e) eta| ≤ delta + 2 * B := by
    have he : (fun e => restore Gi (Real.log x, e) + 4 * e) =
        (fun e => restoreDefect Gi (x, e)) + (fun e : ℝ => 2 * (4 * e)) := by
      funext e
      dsimp [restoreDefect]
      ring
    have hg4 : ContDiff ℝ ∞ (fun e : ℝ => 4 * e) := contDiff_const.mul contDiff_id
    have hg8 : ContDiff ℝ ∞ (fun e : ℝ => 2 * (4 * e)) := contDiff_const.mul hg4
    rw [he, iteratedDeriv_add ((hdSmooth x).of_le (nat_le_infty k)).contDiffAt
      (hg8.of_le (nat_le_infty k)).contDiffAt,
      iteratedDeriv_const_mul _ (hg4.of_le (nat_le_infty k)).contDiffAt]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact add_le_add (hdb x k hk) (mul_le_mul_of_nonneg_left (hgb k hk) (by norm_num))
  have hm : |iteratedDeriv n (restoreDebtM Gi a b) eta| ≤ delta * (b - a) :=
    integral_jet_bound_on hab (fun x hx e => (restore_local_smooth hGi hA (ha.trans_le hx.1) e).1)
      n eta (fun x hx => hdb x n le_rfl)
  have hj : |iteratedDeriv n (restoreDebtJ Gi A a b) eta| ≤
      (2 * (2 ^ n * delta * K)) * (b - a) := by
    apply integral_jet_bound_on hab (fun x hx e => (restore_local_smooth hGi hA (ha.trans_le hx.1)
        e).2.1)
      n eta
    intro x hx
    have hx0 : 0 ≤ x := (ha.trans hx.1).le
    have hx1 : x ≤ 1 := hx.2.trans hb
    have hw : |Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.rpow_nonneg hx0 _)]
      have hs : Real.sqrt (2 * x) ≤ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 * x by positivity), Real.sqrt_nonneg (2 * x)]
      exact (mul_le_mul hs (Real.rpow_le_one hx0 hx1 (by norm_num))
        (Real.rpow_nonneg hx0 _) (by norm_num)).trans_eq (by ring)
    change |iteratedDeriv n (fun e => (Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)) *
      (restoreDefect Gi (x, e) * A e)) eta| ≤ _
    rw [iteratedDeriv_const_mul _ (((hdSmooth x).mul hA).of_le (nat_le_infty n)).contDiffAt,
        abs_mul]
    exact mul_le_mul hw (product_jet_bound (hdSmooth x) hA n eta hd hK (hdb x) habound)
      (abs_nonneg _) (by norm_num)
  have hs : |iteratedDeriv n (restoreDebtS Gi a b) eta| ≤
      (2 ^ n * delta * (delta + 2 * B)) * (b - a) := by
    apply integral_jet_bound_on hab (fun x hx e => (restore_local_smooth hGi hA (ha.trans_le hx.1)
        e).2.2)
      n eta
    intro x hx
    exact product_jet_bound (hdSmooth x) (hpSmooth x) n eta hd (by positivity) (hdb x) (hpb x)
  have hm' := hm.trans (mul_le_of_le_one_right hd hlen1)
  have hj' := hj.trans (mul_le_of_le_one_right (by positivity) hlen1)
  have hs' := hs.trans (mul_le_of_le_one_right (by positivity) hlen1)
  dsimp [restoreJetSize]
  linarith

/-! ## Subtracting the ideal rows and including restoration -/

theorem rows_contDiff {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) {u f : ℝ × ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rowM u r) ∧ ContDiff ℝ ∞ (rowI R f r) ∧
    ContDiff ℝ ∞ (rowJ R u f r) ∧ ContDiff ℝ ∞ (rowS R u f r) ∧
    ContDiff ℝ ∞ (rowP R f r) := by
  refine ⟨(smooth_parameter_interval hr (fun _ _ _ => hu.contDiffAt)).1, ?_, ?_, ?_, ?_⟩
  · have he := funext (rowI_normalized hR hr f)
    rw [he]
    exact (smooth_parameter_interval hr (fun _ _ _ =>
      (((contDiff_const.mul contDiff_fst).mul hf).contDiffAt))).1
  · have he := funext (rowJ_normalized hR hr u f)
    rw [he]
    exact (smooth_parameter_interval hr (fun _ _ _ =>
      (((contDiff_const.mul contDiff_fst).mul (hu.mul hf)).contDiffAt))).1
  · have he := funext (rowS_normalized hR hr u f)
    rw [he]
    exact (smooth_parameter_interval hr (fun _ _ _ =>
      ((hu.pow 2).sub ((contDiff_const.mul contDiff_fst).mul (hf.pow 2))).contDiffAt)).1
  · have he := funext (rowP_normalized hR hr f)
    rw [he]
    exact (smooth_parameter_interval hr (fun _ _ _ =>
      (contDiff_const.mul (hf.pow 2)).contDiffAt)).1

theorem ideal_rows_contDiff (r : ℝ) {G A : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (idealM G r) ∧ ContDiff ℝ ∞ (idealI A r) ∧
    ContDiff ℝ ∞ (idealJ G A r) ∧ ContDiff ℝ ∞ (idealS G A r) ∧
    ContDiff ℝ ∞ (idealP A r) :=
  ⟨contDiff_const.mul hG, contDiff_const.mul hA, contDiff_const.mul (hG.mul hA),
    (contDiff_const.mul (hG.pow 2)).sub (contDiff_const.mul (hA.pow 2)),
    contDiff_const.mul (hA.pow 2)⟩

theorem abs_jet_sub_add_le {F G H : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (n : ℕ) (eta : ℝ) :
    |iteratedDeriv n (fun e => F e - G e + H e) eta| ≤
      |iteratedDeriv n F eta| + |iteratedDeriv n G eta| + |iteratedDeriv n H eta| := by
  change |iteratedDeriv n ((F - G) + H) eta| ≤ _
  rw [iteratedDeriv_add (f := F - G) (g := H) ((hF.sub hG).of_le (nat_le_infty n)).contDiffAt
    (hH.of_le (nat_le_infty n)).contDiffAt,
    iteratedDeriv_sub (hF.of_le (nat_le_infty n)).contDiffAt (hG.of_le (nat_le_infty n)).contDiffAt]
  exact (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)

theorem abs_jet_sub_le {F G : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (n : ℕ) (eta : ℝ) :
    |iteratedDeriv n (fun e => F e - G e) eta| ≤
      |iteratedDeriv n F eta| + |iteratedDeriv n G eta| := by
  change |iteratedDeriv n (F - G) eta| ≤ _
  rw [iteratedDeriv_sub (hF.of_le (nat_le_infty n)).contDiffAt (hG.of_le (nat_le_infty
      n)).contDiffAt]
  exact abs_sub _ _

/-- Reset debt M, given by `rowM u r eta - idealM (fun e => 4 * e) r eta + restoreDebtM Gi r b
eta`. -/
noncomputable def resetDebtM (u : ℝ × ℝ → ℝ) (Gi : ℝ → ℝ) (r b eta : ℝ) : ℝ :=
  rowM u r eta - idealM (fun e => 4 * e) r eta + restoreDebtM Gi r b eta

/-- Reset debt I, given by `rowI R f r eta - idealI A r eta`. -/
noncomputable def resetDebtI (R : ℝ) (f : ℝ × ℝ → ℝ) (A : ℝ → ℝ) (r eta : ℝ) : ℝ :=
  rowI R f r eta - idealI A r eta

/-- Reset debt J, given by `rowJ R u f r eta - idealJ (fun e => 4 * e) A r eta + restoreDebtJ Gi
A r b eta`. -/
noncomputable def resetDebtJ (R : ℝ) (u f : ℝ × ℝ → ℝ) (Gi A : ℝ → ℝ) (r b eta : ℝ) : ℝ :=
  rowJ R u f r eta - idealJ (fun e => 4 * e) A r eta + restoreDebtJ Gi A r b eta

/-- Reset debt S, given by `rowS R u f r eta - idealS (fun e => 4 * e) A r eta + restoreDebtS Gi
r b eta`. -/
noncomputable def resetDebtS (R : ℝ) (u f : ℝ × ℝ → ℝ) (Gi A : ℝ → ℝ) (r b eta : ℝ) : ℝ :=
  rowS R u f r eta - idealS (fun e => 4 * e) A r eta + restoreDebtS Gi r b eta

/-- Reset debt P, given by `rowP R f r eta - idealP A r eta`. -/
noncomputable def resetDebtP (R : ℝ) (f : ℝ × ℝ → ℝ) (A : ℝ → ℝ) (r eta : ℝ) : ℝ :=
  rowP R f r eta - idealP A r eta

/-- Reset debt jet size as an element of `ℝ`. -/
noncomputable def resetDebtJetSize (n : ℕ) (R r b : ℝ) (u f : ℝ × ℝ → ℝ)
    (Gi A : ℝ → ℝ) (eta : ℝ) : ℝ :=
  |iteratedDeriv n (resetDebtM u Gi r b) eta| +
    |iteratedDeriv n (resetDebtI R f A r) eta| +
    |iteratedDeriv n (resetDebtJ R u f Gi A r b) eta| +
    |iteratedDeriv n (resetDebtS R u f Gi A r b) eta| +
    |iteratedDeriv n (resetDebtP R f A r) eta|

theorem resetDebtJetSize_le_parts {R r b : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hrb : r ≤ b)
    {u f : ℝ × ℝ → ℝ} {Gi A : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A) (n : ℕ) (eta : ℝ) :
    resetDebtJetSize n R r b u f Gi A eta ≤ prefixJetSize n R r u f eta +
      idealPrefixJetSize n r (fun e => 4 * e) A eta + restoreJetSize n Gi A r b eta := by
  obtain ⟨huM, huI, huJ, huS, huP⟩ := rows_contDiff hR hr.le hu hf
  have hg4 : ContDiff ℝ ∞ (fun e : ℝ => 4 * e) := contDiff_const.mul contDiff_id
  obtain ⟨hiM, hiI, hiJ, hiS, hiP⟩ := ideal_rows_contDiff r hg4 hA
  have hrM : ContDiff ℝ ∞ (restoreDebtM Gi r b) :=
    (smooth_parameter_interval hrb (fun x hx e => (restore_local_smooth hGi hA (hr.trans_le hx.1)
        e).1)).1
  have hrJ : ContDiff ℝ ∞ (restoreDebtJ Gi A r b) :=
    (smooth_parameter_interval hrb (fun x hx e => (restore_local_smooth hGi hA (hr.trans_le hx.1)
        e).2.1)).1
  have hrS : ContDiff ℝ ∞ (restoreDebtS Gi r b) :=
    (smooth_parameter_interval hrb (fun x hx e => (restore_local_smooth hGi hA (hr.trans_le hx.1)
        e).2.2)).1
  have hm := abs_jet_sub_add_le huM hiM hrM n eta
  have hi := abs_jet_sub_le huI hiI n eta
  have hj := abs_jet_sub_add_le huJ hiJ hrJ n eta
  have hs := abs_jet_sub_add_le huS hiS hrS n eta
  have hp := abs_jet_sub_le huP hiP n eta
  change |iteratedDeriv n (resetDebtM u Gi r b) eta| ≤ _ at hm
  change |iteratedDeriv n (resetDebtI R f A r) eta| ≤ _ at hi
  change |iteratedDeriv n (resetDebtJ R u f Gi A r b) eta| ≤ _ at hj
  change |iteratedDeriv n (resetDebtS R u f Gi A r b) eta| ≤ _ at hs
  change |iteratedDeriv n (resetDebtP R f A r) eta| ≤ _ at hp
  dsimp [resetDebtJetSize, prefixJetSize, idealPrefixJetSize, restoreJetSize]
  linarith only [hm, hi, hj, hs, hp]

/-- Vanishing debt bound as an element of `ℝ`. -/
noncomputable def vanishingDebtBound (n : ℕ) (B K L BG KA r C : ℝ) : ℝ :=
  (prefixCoefficient n B K L + idealPrefixCoefficient n BG KA) * r +
    (2 ^ n * L * K ^ 2) / C ^ 2 + (5 / 2) * (2 ^ n * KA ^ 2) * r ^ (1 / 5 : ℝ)

/-- Restoration bound, given by `delta * (1 + 2 * (2 ^ n * KA) + 2 ^ n * (delta + 2 * BG))`. -/
noncomputable def restorationBound (n : ℕ) (BG KA delta : ℝ) : ℝ :=
  delta * (1 + 2 * (2 ^ n * KA) + 2 ^ n * (delta + 2 * BG))

theorem resetDebtJetSize_bound {R r b L B K C BG KA delta : ℝ}
    (hR : 0 ≤ R) (hr : 0 < r) (hrb : r ≤ b) (hb : b ≤ 1) (hRL : R * r = L)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 1 ≤ C) (hBG : 0 ≤ BG) (hKA : 0 ≤ KA) (hd : 0 ≤ delta)
    {u f : ℝ × ℝ → ℝ} {Gi A : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A)
    (n : ℕ) (eta : ℝ)
    (hub : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => u (x, e)) eta| ≤ B)
    (hfb : ∀ x ∈ Ioc (0 : ℝ) r, ∀ k ≤ n, |iteratedDeriv k (fun e => f (x, e)) eta| ≤ K / C)
    (hgb : ∀ k ≤ n, |iteratedDeriv k (fun e : ℝ => 4 * e) eta| ≤ BG)
    (habound : ∀ k ≤ n, |iteratedDeriv k A eta| ≤ KA)
    (hdef : ∀ k ≤ n, |iteratedDeriv k (fun e => Gi e - 4 * e) eta| ≤ delta) :
    resetDebtJetSize n R r b u f Gi A eta ≤
      vanishingDebtBound n B K L BG KA r C + restorationBound n BG KA delta := by
  have hp := prefixJetSize_bound hR hr.le (hrb.trans hb) hRL hB hK hC hu hf n eta hub hfb
  have hg4 : ContDiff ℝ ∞ (fun e : ℝ => 4 * e) := contDiff_const.mul contDiff_id
  have hi := idealPrefixJetSize_bound hr.le (hrb.trans hb) hBG hKA hg4 hA n eta hgb habound
  have hs := restoreJetSize_bound hr hrb hb hBG hKA hd hGi hA n eta hgb habound hdef
  have ht := resetDebtJetSize_le_parts hR hr hrb hu hf hGi hA n eta
  apply ht.trans
  convert! add_le_add (add_le_add hp hi) hs using 1;
    dsimp [vanishingDebtBound, restorationBound]; ring

theorem vanishingDebtBound_tendsto (n : ℕ) (B K L BG KA T : ℝ) {P : ℝ} (hP : P ≠ 0) :
    Tendsto (fun C : ℝ => vanishingDebtBound n B K L BG KA (separation T C P) C)
      atTop (𝓝 0) := by
  have hp := prefix_bound_tendsto n B K L T P
  have hi := (separation_tendsto T hP).const_mul (idealPrefixCoefficient n BG KA)
  have hs := (separation_fifth_tendsto T hP).const_mul ((5 / 2) * (2 ^ n * KA ^ 2))
  convert! (hp.add hi).add hs using 1
  · funext C
    dsimp [vanishingDebtBound]
    ring
  · ring_nf

/-- Increasing `C` removes only the prefix term. The explicit restoration term
is retained, so the upstream smallness choice is not silently changed. -/
theorem eventually_vanishingDebtBound_lt (n : ℕ) (B K L BG KA T : ℝ)
    {P eps : ℝ} (hP : P ≠ 0) (heps : 0 < eps) :
    ∀ᶠ C : ℝ in atTop, vanishingDebtBound n B K L BG KA (separation T C P) C < eps :=
  (vanishingDebtBound_tendsto n B K L BG KA T hP).eventually (gt_mem_nhds heps)

/-! ## Direct adapter from axis and entry jets to the constructed prefix -/

/-- Shape jet constant, given by `K + (n.factorial * Real.exp (T / 10 + B) * B ^ n) / Real.sqrt
(2 * Xi)`. -/
noncomputable def shapeJetConstant (n : ℕ) (Xi T B K : ℝ) : ℝ :=
  K + (n.factorial * Real.exp (T / 10 + B) * B ^ n) / Real.sqrt (2 * Xi)

theorem shapeJetConstant_nonneg (n : ℕ) {Xi T B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    0 ≤ shapeJetConstant n Xi T B K := by
  unfold shapeJetConstant
  positivity

theorem shapeField_jets_uniform {Xi C T X B K : ℝ} (hXi : 0 < Xi) (hC : 0 < C)
    (hT : 0 < T) (hX : 0 ≤ X) (hXL : X ≤ Xi * Real.exp T)
    {li : ℝ → ℝ} {old : ℝ × ℝ → ℝ} (hli : ContDiff ℝ ∞ li) (hB : 1 ≤ B)
    (hK : 0 ≤ K) (n : ℕ) (eta : ℝ)
    (hAxis : X ≤ Xi → ∀ k ≤ n, |iteratedDeriv k (fun e => old (X, e)) eta| ≤ K / C)
    (hHold : Xi ≤ X → ∀ e, old (X, e) =
      C⁻¹ * Real.exp (Real.log (X / Xi) / 10 + li e) / Real.sqrt (2 * X))
    (hl : ∀ i ≤ n, |iteratedDeriv i li eta| ≤ B)
    (hf : ∀ i ≤ n, |iteratedDeriv i logShape eta| ≤ B) :
    ∀ k ≤ n, |iteratedDeriv k (fun e => shapeField Xi T li old (X, e)) eta| ≤
      shapeJetConstant n Xi T B K / C := by
  intro k hk
  have hb := shapeField_jet_bound hXi hC hT hX hXL hli hB hK k eta
    (fun hx => hAxis hx k hk) hHold (fun i hi => hl i (hi.trans hk)) (fun i hi => hf i (hi.trans
        hk))
  apply hb.trans
  unfold shapeJetConstant
  apply div_le_div_of_nonneg_right _ hC.le
  apply add_le_add_right
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hfact : (k.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hk
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfact (Real.exp_pos _).le)
    (pow_le_pow_right₀ hB hk) (pow_nonneg (zero_le_one.trans hB) _)
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

/-- Scaled family, given by `F (R * p.1, p.2)`. -/
noncomputable def scaledFamily (R : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F (R * p.1, p.2)

theorem scaledFamily_contDiff (R : ℝ) {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (scaledFamily R F) :=
  hF.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)

/-- This theorem assumes axis-field jets and the held entry power law, then
derives the actual constructed prefix-row estimates. No row-smallness
hypothesis occurs. The constant `shapeJetConstant` is independent of `C`. -/
theorem constructed_prefix_bound {Xi C T P B BJ K : ℝ} (hXi : 0 < Xi) (hC : 1 ≤ C)
    (hT : 0 < T) (hP : 0 < P) (hB : 0 ≤ B) (hBJ : 1 ≤ BJ) (hK : 0 ≤ K)
    {li Gi : ℝ → ℝ} {oldU oldF : ℝ × ℝ → ℝ}
    (hli : ContDiff ℝ ∞ li) (hU : ContDiff ℝ ∞ oldU) (hF : ContDiff ℝ ∞ oldF)
    (n : ℕ) (eta : ℝ) (hsep : separation T C P ≤ 1)
    (hAxisU : ∀ X ∈ Icc (0 : ℝ) Xi, ∀ k ≤ n, |iteratedDeriv k (fun e => oldU (X, e)) eta| ≤ B)
    (hGi : ∀ k ≤ n, |iteratedDeriv k Gi eta| ≤ B)
    (hHoldU : ∀ X, Xi ≤ X → ∀ e, oldU (X, e) = Gi e)
    (hAxisF : ∀ X ∈ Icc (0 : ℝ) Xi, ∀ k ≤ n, |iteratedDeriv k (fun e => oldF (X, e)) eta| ≤ K / C)
    (hHoldF : ∀ X, Xi ≤ X → ∀ e, oldF (X, e) =
      C⁻¹ * Real.exp (Real.log (X / Xi) / 10 + li e) / Real.sqrt (2 * X))
    (hl : ∀ i ≤ n, |iteratedDeriv i li eta| ≤ BJ)
    (hshape : ∀ i ≤ n, |iteratedDeriv i logShape eta| ≤ BJ) :
    prefixJetSize n (resetRadius Xi C P) (separation T C P)
      (scaledFamily (resetRadius Xi C P) oldU)
      (scaledFamily (resetRadius Xi C P) (shapeField Xi T li oldF)) eta ≤
      prefixCoefficient n B (shapeJetConstant n Xi T BJ K) (Xi * Real.exp T) * separation T C P +
        (2 ^ n * (Xi * Real.exp T) * (shapeJetConstant n Xi T BJ K) ^ 2) / C ^ 2 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hR : 0 < resetRadius Xi C P := by unfold resetRadius; positivity
  have hr : 0 < separation T C P := separation_pos T hCpos hP
  have hRL := resetRadius_mul_separation Xi T C P (mul_pos hCpos hP).ne'
  apply prefixJetSize_bound hR.le hr.le hsep hRL hB
    (shapeJetConstant_nonneg n (zero_le_one.trans hBJ) hK) hC
    (scaledFamily_contDiff _ hU)
    (scaledFamily_contDiff _ (shapeField_contDiff hXi hT hli hF)) n eta
  · intro x hx k hk
    change |iteratedDeriv k (fun e => oldU (resetRadius Xi C P * x, e)) eta| ≤ B
    have hx0 : 0 ≤ resetRadius Xi C P * x := mul_nonneg hR.le hx.1.le
    by_cases hxXi : resetRadius Xi C P * x ≤ Xi
    · exact hAxisU _ ⟨hx0, hxXi⟩ k hk
    · have he : (fun e => oldU (resetRadius Xi C P * x, e)) = Gi :=
        funext (hHoldU _ (le_of_not_ge hxXi))
      rw [he]
      exact hGi k hk
  · intro x hx k hk
    change |iteratedDeriv k (fun e => shapeField Xi T li oldF (resetRadius Xi C P * x, e)) eta| ≤ _
    have hx0 : 0 ≤ resetRadius Xi C P * x := mul_nonneg hR.le hx.1.le
    have hxL : resetRadius Xi C P * x ≤ Xi * Real.exp T :=
      (mul_le_mul_of_nonneg_left hx.2 hR.le).trans_eq hRL
    exact shapeField_jets_uniform hXi hCpos hT hx0 hxL hli hBJ hK n eta
      (fun hxXi => hAxisF _ ⟨hx0, hxXi⟩) (hHoldF _) hl hshape k hk

/-- The row-debt decomposition used above is the ordinary split of actual
integrals at the separation radius. -/
theorem integral_debt_split {r b : ℝ} {F G : ℝ → ℝ}
    (hF0 : IntervalIntegrable F volume 0 r) (hFr : IntervalIntegrable F volume r b)
    (hG0 : IntervalIntegrable G volume 0 r) (hGr : IntervalIntegrable G volume r b) :
    (∫ x in (0 : ℝ)..b, F x - G x) =
      (∫ x in (0 : ℝ)..r, F x) - (∫ x in (0 : ℝ)..r, G x) +
        (∫ x in r..b, F x - G x) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF0.sub hG0) (hFr.sub hGr),
    intervalIntegral.integral_sub hF0 hG0]

end NavierStokes.ShapeTransition
