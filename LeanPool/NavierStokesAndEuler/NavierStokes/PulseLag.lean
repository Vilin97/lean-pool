/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseAmplitude
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectedPulseAmplitude
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# The actual outgoing pulse lag

The exponential convolution is expanded by two integrations by parts.
The resulting remainder is controlled by the actual second derivative of
the forcing, with constants uniform in the pulse duration.
-/

noncomputable section

namespace NavierStokes.PulseLag

open Set MeasureTheory
open scoped Topology ContDiff

noncomputable def kernel (β y t : ℝ) : ℝ := Real.exp (-β * (y - t))

noncomputable def convolution (β : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, kernel β y t * f t

noncomputable def lag (β m₀ : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  m₀ * Real.exp (-β * y) + convolution β f y

theorem kernel_pos (β y t : ℝ) : 0 < kernel β y t := Real.exp_pos _

theorem kernel_continuous (β y : ℝ) : Continuous (kernel β y) :=
  Real.continuous_exp.comp (continuous_const.fun_mul (continuous_const.sub continuous_id))

theorem kernel_hasDerivAt (β y t : ℝ) :
    HasDerivAt (kernel β y) (β * kernel β y t) t := by
  convert! (((hasDerivAt_const t y).fun_sub (hasDerivAt_id t)).const_mul (-β)).exp using 1
  simp only [kernel, id_eq]
  ring

theorem convolution_eq_weighted (β : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    convolution β f y = Real.exp (-β * y) * ∫ t in (0 : ℝ)..y, Real.exp (β * t) * f t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [kernel]
  rw [show -β * (y - t) = -β * y + β * t by ring, Real.exp_add]
  ring

theorem kernel_integral {β : ℝ} (hβ : β ≠ 0) (y : ℝ) :
    (∫ t in (0 : ℝ)..y, kernel β y t) = (1 - Real.exp (-β * y)) / β := by
  have hd (t : ℝ) : HasDerivAt (fun s => kernel β y s / β) (kernel β y t) t := by
    convert! (kernel_hasDerivAt β y t).div_const β using 1
    field_simp
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((kernel_continuous β y).intervalIntegrable 0 y)
  simpa only [kernel, sub_self, mul_zero, Real.exp_zero, sub_zero, div_sub_div_same] using he

theorem convolution_abs_le {β M y : ℝ} (hβ : 0 < β) (hM : 0 ≤ M) (hy : 0 ≤ y)
    {f : ℝ → ℝ} (hf : Continuous f) (hbound : ∀ t ∈ Icc (0 : ℝ) y, |f t| ≤ M) :
    |convolution β f y| ≤ M / β := by
  have hi : IntervalIntegrable (fun t => kernel β y t * f t) volume 0 y :=
    ((kernel_continuous β y).fun_mul hf).intervalIntegrable 0 y
  have hj : IntervalIntegrable (fun t => kernel β y t * M) volume 0 y :=
    ((kernel_continuous β y).fun_mul continuous_const).intervalIntegrable 0 y
  calc
    |convolution β f y| ≤ ∫ t in (0 : ℝ)..y, |kernel β y t * f t| := by
      simpa only [convolution, Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun t => kernel β y t * f t) hy)
    _ ≤ ∫ t in (0 : ℝ)..y, kernel β y t * M := by
      apply intervalIntegral.integral_mono_on hy hi.norm hj
      intro t ht
      rw [Real.norm_eq_abs]
      rw [abs_mul, abs_of_pos (kernel_pos β y t)]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (kernel_pos β y t).le
    _ = M * ((1 - Real.exp (-β * y)) / β) := by
      rw [intervalIntegral.integral_mul_const, kernel_integral hβ.ne']
      ring
    _ ≤ M / β := by
      have he : 0 ≤ Real.exp (-β * y) := (Real.exp_pos _).le
      have hdiv : (1 - Real.exp (-β * y)) / β ≤ 1 / β :=
        div_le_div_of_nonneg_right (by linarith) hβ.le
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdiv hM

/-- Exact second-order integration-by-parts identity, including the
initial boundary terms. -/
theorem convolution_second_order {β : ℝ} (hβ : β ≠ 0)
    {f f₁ f₂ : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t, HasDerivAt f₁ (f₂ t) t) (hf₂ : Continuous f₂) (y : ℝ) :
    convolution β f y = f y / β - f₁ y / β ^ 2 -
      Real.exp (-β * y) * (f 0 / β - f₁ 0 / β ^ 2) + convolution β f₂ y / β ^ 2 := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.mpr (fun t => (hf₁ t).continuousAt)
  have hd (t : ℝ) : HasDerivAt
      (fun s => kernel β y s * (f s / β - f₁ s / β ^ 2))
      (kernel β y t * f t - (kernel β y t * f₂ t) / β ^ 2) t := by
    convert! (kernel_hasDerivAt β y t).fun_mul ((hf t).div_const β |>.fun_sub
      ((hf₁ t).div_const (β ^ 2))) using 1
    field_simp ; ring
  have hi : IntervalIntegrable (fun t => kernel β y t * f t) volume 0 y :=
    ((kernel_continuous β y).fun_mul hc).intervalIntegrable 0 y
  have hi₂ : IntervalIntegrable (fun t => (kernel β y t * f₂ t) / β ^ 2) volume 0 y :=
    (((kernel_continuous β y).fun_mul hf₂).div_const (β ^ 2)).intervalIntegrable 0 y
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hi.sub hi₂)
  rw [intervalIntegral.integral_sub hi hi₂, intervalIntegral.integral_div] at he
  simp only [kernel, sub_self, mul_zero, Real.exp_zero, one_mul, sub_zero] at he
  dsimp only [convolution, kernel]
  linarith

theorem lag_second_order_error {β M y : ℝ} (hβ : 0 < β) (hM : 0 ≤ M) (hy : 0 ≤ y)
    {f f₁ f₂ : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t, HasDerivAt f₁ (f₂ t) t) (hf₂ : Continuous f₂)
    (hzero : f 0 = 0) (hzero₁ : f₁ 0 = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) y, |f₂ t| ≤ M) (m₀ : ℝ) :
    |lag β m₀ f y - (f y / β - f₁ y / β ^ 2 + m₀ * Real.exp (-β * y))| ≤ M / β ^ 3 := by
  have he := convolution_second_order hβ.ne' hf hf₁ hf₂ y
  rw [hzero, hzero₁] at he
  simp only [zero_div, sub_zero, mul_zero] at he
  have herr : lag β m₀ f y - (f y / β - f₁ y / β ^ 2 + m₀ * Real.exp (-β * y)) =
      convolution β f₂ y / β ^ 2 := by rw [lag, he]; ring
  rw [herr, abs_div, abs_of_pos (sq_pos_of_pos hβ)]
  have hb := div_le_div_of_nonneg_right (convolution_abs_le hβ hM hy hf₂ hbound)
    (sq_nonneg β)
  refine hb.trans_eq ?_
  rw [div_div]
  congr 1
  ring

theorem convolution_linear (β q A y : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    convolution β (fun t => q * f t + A * g t) y =
      q * convolution β f y + A * convolution β g y := by
  have heq : (fun t => kernel β y t * (q * f t + A * g t)) =
      (fun t => q * (kernel β y t * f t) + A * (kernel β y t * g t)) := by
    funext t
    ring
  unfold convolution
  rw [heq, intervalIntegral.integral_add
    ((continuous_const.fun_mul ((kernel_continuous β y).fun_mul hf)).intervalIntegrable 0 y)
    ((continuous_const.fun_mul ((kernel_continuous β y).fun_mul hg)).intervalIntegrable 0 y),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem lag_eq_linearLag (β m₀ : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    lag β m₀ f y = OutgoingTail.linearLag (fun _ => β) f m₀ y := by
  have hp (t : ℝ) : OutgoingSchedule.primitive (fun _ => β) t = β * t := by
    simp only [OutgoingSchedule.primitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [lag, convolution_eq_weighted, OutgoingTail.linearLag]
  simp only [hp]
  rw [show -(β * y) = -β * y by ring]
  simp only [OutgoingSchedule.primitive]
  ring

theorem lag_hasDerivAt (β m₀ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (y : ℝ) :
    HasDerivAt (lag β m₀ f) (f y - β * lag β m₀ f y) y := by
  have heq : lag β m₀ f = OutgoingTail.linearLag (fun _ => β) f m₀ :=
    funext (lag_eq_linearLag β m₀ f)
  rw [heq]
  exact OutgoingTail.linearLag_hasDerivAt continuous_const hf m₀ y

section ActualPulse

open OutgoingSchedule OutgoingPulseBounds

noncomputable def decay (c : Parameters) : ℝ := 1 / 2 - c.lam

theorem decay_pos (c : Parameters) : 0 < decay c := by
  dsimp [decay]
  linarith [c.lam_lt]

theorem decay_inv_cube_le (c : Parameters) {M : ℝ} (hM : 0 ≤ M) :
    M / decay c ^ 3 ≤ 16 * M := by
  have hd : (2 / 5 : ℝ) ≤ decay c := by dsimp [decay]; linarith [c.lam_lt]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) hd 3
  have hb : 1 ≤ 16 * decay c ^ 3 := by norm_num at hp; linarith
  apply (div_le_iff₀ (pow_pos (decay_pos c) 3)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb hM]

/-- The exponential correction is smaller than a fixed quadratic rate,
uniformly for every positive lambda. -/
theorem exponential_correction_quadratic {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (-(1 / (4 * lam))) ≤ 64 * lam ^ 2 := by
  have hx : 0 < 1 / (8 * lam) := by positivity
  have he : 1 / (8 * lam) ≤ Real.exp (1 / (8 * lam)) := by
    linarith [Real.add_one_le_exp (1 / (8 * lam))]
  have hs := pow_le_pow_left₀ hx.le he 2
  rw [← Real.exp_nat_mul] at hs
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos hx) hs
  have harg : (2 : ℝ) * (1 / (8 * lam)) = 1 / (4 * lam) := by ring
  norm_num only [Nat.cast_ofNat] at hi
  rw [harg, one_div, ← Real.exp_neg] at hi
  convert! hi using 1
  field_simp ; ring

noncomputable def mainSecondBound : ℝ := 1 + Classical.choose
  (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 2)

theorem mainSecondBound_pos : 0 < mainSecondBound := by
  have h := (Classical.choose_spec (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 2)).1
  dsimp [mainSecondBound]
  linarith

theorem main_second_le (z : ℝ) : |iteratedDeriv 2 mainPulse z| ≤ mainSecondBound := by
  have h := (Classical.choose_spec (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 2)).2 z
  dsimp [mainSecondBound]
  linarith

noncomputable def forcing (c : Parameters) (q A y : ℝ) : ℝ :=
  A * mainPulse (c.lam * y) + affineProfile c q A y

theorem forcing_contDiff (c : Parameters) (q A : ℝ) : ContDiff ℝ ∞ (forcing c q A) :=
  (contDiff_const.mul (mainPulse_contDiff.comp (contDiff_const.mul contDiff_id))).add
    (affineProfile_contDiff c q A)

theorem forcing_eq_pulseRatio (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    forcing c (parameterPolynomial eta) (amp eta) y = pulseRatio c amp (y, eta) := by
  rw [pulseRatio, correction_log_eq_affineProfile]
  rfl

theorem affineProfile_zero_left (c : Parameters) (q A : ℝ) {y : ℝ} (hy : y ≤ 0) :
    affineProfile c q A y = 0 := by
  have hz (j : Fin 2) : logTemplate (y - center c j) = 0 := by
    rw [← bump_log_translate]
    by_contra hb
    have hsupport := LocalizedMomentRepair.bump_tsupport_subset_open
      (c.lower j) (c.upper j) (c.lower_lt_upper j) (subset_tsupport _ hb)
    have hey : Real.exp y ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hy
    linarith [c.one_lt_lower j, hsupport.1]
  simp only [affineProfile, hz, mul_zero, Finset.sum_const_zero]

theorem forcing_zero_left (c : Parameters) (q A : ℝ) {y : ℝ} (hy : y ≤ 0) :
    forcing c q A y = 0 := by
  rw [forcing, mainPulse_zero_left (mul_nonpos_of_nonneg_of_nonpos c.lam_pos.le hy),
    affineProfile_zero_left c q A hy]
  ring

theorem deriv_zero_of_zero_left {f : ℝ → ℝ} (hf : ∀ y ≤ 0, f y = 0) : deriv f 0 = 0 := by
  have hd : HasDerivWithinAt f 0 (Iic 0) 0 :=
    (hasDerivWithinAt_const 0 (Iic 0) 0).congr (fun y hy => hf y hy) (hf 0 le_rfl)
  exact hd.deriv_eq_zero (uniqueDiffOn_Iic 0 0 self_mem_Iic)

theorem forcing_jet_formula (c : Parameters) (q A : ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (forcing c q A) y =
      A * c.lam ^ k * iteratedDeriv k mainPulse (c.lam * y) +
        iteratedDeriv k (affineProfile c q A) y := by
  have hm : ContDiff ℝ k (fun t => mainPulse (c.lam * t)) :=
    (mainPulse_contDiff.comp (contDiff_const.mul contDiff_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  have hc : ContDiff ℝ k (affineProfile c q A) := (affineProfile_contDiff c q A).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  change iteratedDeriv k ((fun t => A * mainPulse (c.lam * t)) + affineProfile c q A) y = _
  rw [iteratedDeriv_add (contDiff_const.mul hm).contDiffAt hc.contDiffAt,
    iteratedDeriv_const_mul A hm.contDiffAt,
    iteratedDeriv_comp_const_mul (mainPulse_contDiff.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)) c.lam]
  ring

noncomputable def forcingBound (P m : ℝ) : ℝ := mainSecondBound + 64 * correctionJetBound P m 2

theorem forcingBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < forcingBound P m := by
  have hc := correctionJetBound_pos hP m 2
  dsimp [forcingBound]
  linarith [mainSecondBound_pos]

theorem forcing_second_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A y : ℝ) : |iteratedDeriv 2 (forcing c q A) y| ≤
      forcingBound c.P c.m * (|q| + |A|) * c.lam ^ 2 := by
  rw [forcing_jet_formula]
  have hc := affineProfile_jet_bound c hsmall q A 2 y
  have he := exponential_correction_quadratic c.lam_pos
  have hm : |A * c.lam ^ 2 * iteratedDeriv 2 mainPulse (c.lam * y)| ≤
      |A| * c.lam ^ 2 * mainSecondBound := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c.lam)]
    exact mul_le_mul_of_nonneg_left (main_second_le _) (by positivity)
  have hc' : |iteratedDeriv 2 (affineProfile c q A) y| ≤
      correctionJetBound c.P c.m 2 * (64 * c.lam ^ 2) * (|q| + |A|) :=
    hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (correctionJetBound_pos c.P_pos c.m 2).le) (by positivity))
  have hab : |A| ≤ |q| + |A| := by linarith [abs_nonneg q]
  have hmain := mul_le_mul_of_nonneg_right hab
    (mul_nonneg (sq_nonneg c.lam) mainSecondBound_pos.le)
  calc
    _ ≤ |A * c.lam ^ 2 * iteratedDeriv 2 mainPulse (c.lam * y)| +
        |iteratedDeriv 2 (affineProfile c q A) y| := abs_add_le _ _
    _ ≤ |A| * c.lam ^ 2 * mainSecondBound +
        correctionJetBound c.P c.m 2 * (64 * c.lam ^ 2) * (|q| + |A|) := add_le_add hm hc'
    _ ≤ _ := by dsimp [forcingBound]; nlinarith

noncomputable def affineLag (c : Parameters) (q A y : ℝ) : ℝ :=
  lag (decay c) (prefixCoefficient c 0 * q) (forcing c q A) y

noncomputable def lagBound (P m : ℝ) : ℝ := 16 * forcingBound P m

theorem lagBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < lagBound P m :=
  mul_pos (by norm_num) (forcingBound_pos hP m)

theorem affineLag_error (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |affineLag c q A y - (forcing c q A y / decay c -
      deriv (forcing c q A) y / decay c ^ 2 +
        (prefixCoefficient c 0 * q) * Real.exp (-decay c * y))| ≤
      lagBound c.P c.m * (|q| + |A|) * c.lam ^ 2 := by
  have hf := forcing_contDiff c q A
  have hd : ∀ t, HasDerivAt (forcing c q A) (deriv (forcing c q A) t) t :=
    fun t => (hf.differentiable (by simp) t).hasDerivAt
  have hd₁ : ∀ t, HasDerivAt (deriv (forcing c q A))
      (iteratedDeriv 2 (forcing c q A) t) t := by
    intro t
    simpa only [iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_zero] using
      (hf.differentiable_iteratedDeriv 1 (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 1)
        t).hasDerivAt
  have hc₂ := hf.continuous_iteratedDeriv 2 (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hM : 0 ≤ forcingBound c.P c.m * (|q| + |A|) * c.lam ^ 2 := by
    have hp := forcingBound_pos c.P_pos c.m
    positivity
  have he := lag_second_order_error (decay_pos c) hM hy hd hd₁ hc₂
    (forcing_zero_left c q A le_rfl)
    (deriv_zero_of_zero_left (fun t ht => forcing_zero_left c q A ht))
    (fun t _ => forcing_second_bound c hsmall q A t) (prefixCoefficient c 0 * q)
  exact he.trans ((decay_inv_cube_le c hM).trans_eq (by dsimp [lagBound]; ring))

/-- The actual radial mass average divided by the actual angular profile,
at pulse-relative log time `y`. -/
noncomputable def normalizedLag (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  massMoment c amp eta (c.pulseStart + y) /
    (Real.exp (c.pulseStart + y) *
      angular c.P c.dropLength c.lam (c.pulseStart + y, eta))

theorem pulse_denominator (c : Parameters) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (c.pulseStart + y) * angular c.P c.dropLength c.lam (c.pulseStart + y, eta) =
      (momentScale c 0 * shape eta) * Real.exp (decay c * y) := by
  rw [angular_pulse c eta (by linarith)]
  have hsub : c.pulseStart + y - c.pulseStart = y := by ring
  rw [hsub, Real.exp_add]
  have he : Real.exp y * Real.exp (-(1 / 2 + c.lam) * y) = Real.exp (decay c * y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [decay]
    ring
  norm_num only [momentScale, ite_eq_left rfl]
  simp only [ite_true]
  calc
    _ = (Real.exp c.pulseStart * pulseAmplitude c * shape eta) *
        (Real.exp y * Real.exp (-(1 / 2 + c.lam) * y)) := by ring
    _ = _ := by rw [he]

theorem massMoment_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    massMoment c amp eta (c.pulseStart + y) = massMoment c amp eta c.pulseStart +
      (momentScale c 0 * shape eta) *
        ∫ t in (0 : ℝ)..y, Real.exp (decay c * t) * forcing c (parameterPolynomial eta) (amp eta) t
          := by
  let g : ℝ → ℝ := fun t => Real.exp t * axial c amp (t, eta)
  have hg : Continuous g := Real.continuous_exp.mul (axial_radial_contDiff c amp eta).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) 0 c.pulseStart)
    (hg.intervalIntegrable (μ := volume) c.pulseStart (c.pulseStart + y))
  have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := y) g c.pulseStart
  simp only [add_zero] at hshift
  have hpart : (∫ t in c.pulseStart..c.pulseStart + y, g t) =
      (momentScale c 0 * shape eta) *
        ∫ t in (0 : ℝ)..y, Real.exp (decay c * t) * forcing c (parameterPolynomial eta) (amp eta) t
          := by
    rw [← hshift, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) y := by simpa only [uIcc_of_le hy] using ht
    have h := mass_integrand_pulse c amp eta (y := c.pulseStart + t) (by linarith [ht'.1])
    have hsub : c.pulseStart + t - c.pulseStart = t := by ring
    rw [hsub, radialPulse_exp, ← forcing_eq_pulseRatio] at h
    have hdecay : c.exponents 0 + 1 = decay c := by norm_num [Parameters.exponents, decay]; ring
    rw [hdecay] at h
    exact h
  change (4 * eta + ∫ t in (0 : ℝ)..c.pulseStart + y, g t) =
    (4 * eta + ∫ t in (0 : ℝ)..c.pulseStart, g t) + _
  rw [← hadd, hpart]
  ring

/-- The exact exponential-convolution representation of the actual lag;
it is derived from the radial mass integral. -/
theorem normalizedLag_eq_affineLag (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    normalizedLag c amp eta y = affineLag c (parameterPolynomial eta) (amp eta) y := by
  have hs : momentScale c 0 * shape eta ≠ 0 :=
    ne_of_gt (mul_pos (momentScale_pos c 0) (shape_pos eta))
  have hpre := normalized_mass_prefix c amp eta
  have hd0 := pulse_denominator c eta (y := 0) le_rfl
  simp only [add_zero, mul_zero, Real.exp_zero, mul_one] at hd0
  rw [hd0] at hpre
  have hpre' : massMoment c amp eta c.pulseStart =
      (prefixCoefficient c 0 * parameterPolynomial eta) * (momentScale c 0 * shape eta) := by
    apply (div_eq_iff hs).mp
    simpa only [parameterPolynomial, mul_assoc] using hpre
  rw [normalizedLag, massMoment_pulse c amp eta hy, pulse_denominator c eta hy, hpre',
    affineLag, lag, convolution_eq_weighted]
  have he : Real.exp (-decay c * y) = (Real.exp (decay c * y))⁻¹ := by
    rw [show -decay c * y = -(decay c * y) by ring, Real.exp_neg]
  rw [he]
  field_simp [(momentScale_pos c 0).ne', (shape_pos eta).ne']

/-- The actual mass lag satisfies the pulse ODE, including its right
derivative at pulse time zero. -/
theorem normalizedLag_hasDerivWithinAt (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    HasDerivWithinAt (normalizedLag c amp eta)
      (pulseRatio c amp (y, eta) - decay c * normalizedLag c amp eta y) (Ici 0) y := by
  have h := lag_hasDerivAt (decay c) (prefixCoefficient c 0 * parameterPolynomial eta)
    (forcing_contDiff c (parameterPolynomial eta) (amp eta)).continuous y
  change HasDerivAt (affineLag c (parameterPolynomial eta) (amp eta))
    (forcing c (parameterPolynomial eta) (amp eta) y -
      decay c * affineLag c (parameterPolynomial eta) (amp eta) y) y at h
  have hd := (h.hasDerivWithinAt (s := Ici 0)).congr
    (fun t ht => normalizedLag_eq_affineLag c amp eta ht)
    (normalizedLag_eq_affineLag c amp eta hy)
  rw [forcing_eq_pulseRatio, ← normalizedLag_eq_affineLag c amp eta hy] at hd
  exact hd

theorem normalizedLag_ode (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : 0 < y) :
    deriv (normalizedLag c amp eta) y + decay c * normalizedLag c amp eta y =
      pulseRatio c amp (y, eta) := by
  rw [((normalizedLag_hasDerivWithinAt c amp eta hy.le).hasDerivAt (Ici_mem_nhds hy)).deriv]
  ring

theorem normalizedLag_error (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) {y : ℝ} (hy : 0 ≤ y) :
    |normalizedLag c amp eta y - (pulseRatio c amp (y, eta) / decay c -
      deriv (fun t => pulseRatio c amp (t, eta)) y / decay c ^ 2 +
        (prefixCoefficient c 0 * parameterPolynomial eta) * Real.exp (-decay c * y))| ≤
      lagBound c.P c.m * (2 + |amp eta|) * c.lam ^ 2 := by
  have hfun : (fun t => pulseRatio c amp (t, eta)) =
      forcing c (parameterPolynomial eta) (amp eta) := by
    funext t
    exact (forcing_eq_pulseRatio c amp eta t).symm
  rw [normalizedLag_eq_affineLag c amp eta hy, hfun,
    ← forcing_eq_pulseRatio c amp eta y]
  apply (affineLag_error c hsmall _ _ hy).trans
  have hq := parameterPolynomial_bound heta
  have hpos := lagBound_pos c.P_pos c.m
  gcongr

theorem forcing_jet_decomposition (c : Parameters) (q A : ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (forcing c q A) y =
      q * iteratedDeriv k (forcing c 1 0) y + A * iteratedDeriv k (forcing c 0 1) y := by
  rw [forcing_jet_formula, forcing_jet_formula, forcing_jet_formula,
    affineProfile_jet_decomposition c q A k y]
  ring

theorem affineLag_decomposition (c : Parameters) (q A y : ℝ) :
    affineLag c q A y = q * affineLag c 1 0 y + A * affineLag c 0 1 y := by
  have hF : forcing c q A = fun t => q * forcing c 1 0 t + A * forcing c 0 1 t := by
    funext t
    simpa only [iteratedDeriv_zero] using forcing_jet_decomposition c q A 0 t
  simp only [affineLag, lag]
  rw [hF, convolution_linear (decay c) q A y
    (forcing_contDiff c 1 0).continuous (forcing_contDiff c 0 1).continuous]
  ring

theorem affineLag_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) (y : ℝ) :
    HasDerivAt (fun t => affineLag c (parameterPolynomial t) (amp t) y)
      (affineLag c (1 + 3 * eta ^ 2) amp' y) eta := by
  have hF : (fun t => affineLag c (parameterPolynomial t) (amp t) y) =
      (fun t => parameterPolynomial t * affineLag c 1 0 y + amp t * affineLag c 0 1 y) := by
    funext t
    exact affineLag_decomposition c _ _ y
  rw [hF, affineLag_decomposition c (1 + 3 * eta ^ 2) amp' y]
  exact ((parameterPolynomial_hasDerivAt eta).mul_const _).add (ha.mul_const _)

theorem normalizedLag_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun t => normalizedLag c amp t y)
      (affineLag c (1 + 3 * eta ^ 2) amp' y) eta :=
  (affineLag_eta_hasDerivAt c ha y).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => normalizedLag_eq_affineLag c amp t hy))

noncomputable def affineError (c : Parameters) (q A y : ℝ) : ℝ :=
  affineLag c q A y - (forcing c q A y / decay c - deriv (forcing c q A) y / decay c ^ 2 +
    (prefixCoefficient c 0 * q) * Real.exp (-decay c * y))

theorem affineError_decomposition (c : Parameters) (q A y : ℝ) :
    affineError c q A y = q * affineError c 1 0 y + A * affineError c 0 1 y := by
  have h₀ := forcing_jet_decomposition c q A 0 y
  have h₁ := forcing_jet_decomposition c q A 1 y
  simp only [iteratedDeriv_zero] at h₀
  simp only [iteratedDeriv_one] at h₁
  simp only [affineError]
  rw [affineLag_decomposition c q A y, h₀, h₁]
  ring

theorem affineError_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) (y : ℝ) :
    HasDerivAt (fun t => affineError c (parameterPolynomial t) (amp t) y)
      (affineError c (1 + 3 * eta ^ 2) amp' y) eta := by
  have hF : (fun t => affineError c (parameterPolynomial t) (amp t) y) =
      (fun t => parameterPolynomial t * affineError c 1 0 y + amp t * affineError c 0 1 y) := by
    funext t
    exact affineError_decomposition c _ _ y
  rw [hF, affineError_decomposition c (1 + 3 * eta ^ 2) amp' y]
  exact ((parameterPolynomial_hasDerivAt eta).mul_const _).add (ha.mul_const _)

/-- Error in the two-term expansion of the actual normalized mass lag,
with its exact exponentially decaying initial value retained. -/
noncomputable def pulseError (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  normalizedLag c amp eta y - (pulseRatio c amp (y, eta) / decay c -
    deriv (fun t => pulseRatio c amp (t, eta)) y / decay c ^ 2 +
      (prefixCoefficient c 0 * parameterPolynomial eta) * Real.exp (-decay c * y))

theorem pulseError_eq_affineError (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : 0 ≤ y) :
    pulseError c amp eta y = affineError c (parameterPolynomial eta) (amp eta) y := by
  have hF : (fun t => pulseRatio c amp (t, eta)) = forcing c (parameterPolynomial eta) (amp eta) :=
    by
    funext t
    exact (forcing_eq_pulseRatio c amp eta t).symm
  rw [pulseError, affineError, normalizedLag_eq_affineLag c amp eta hy, hF,
    ← forcing_eq_pulseRatio c amp eta y]

theorem pulseError_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun t => pulseError c amp t y)
      (affineError c (1 + 3 * eta ^ 2) amp' y) eta :=
  (affineError_eta_hasDerivAt c ha y).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t => pulseError_eq_affineError c amp t hy))

theorem pulseError_eta_bound (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) {y : ℝ} (hy : 0 ≤ y) :
    |deriv (fun t => pulseError c amp t y) eta| ≤
      lagBound c.P c.m * (4 + |amp'|) * c.lam ^ 2 := by
  rw [(pulseError_eta_hasDerivAt c ha hy).deriv]
  apply (affineLag_error c hsmall _ _ hy).trans
  have hq : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
      parameterPolynomial_derivative_bound heta
  have hpos := lagBound_pos c.P_pos c.m
  gcongr

noncomputable def scaledPulse (c : Parameters) (amp : ℝ → ℝ) (eta z : ℝ) : ℝ :=
  pulseRatio c amp (z / c.lam, eta)

theorem scaledPulse_deriv (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    c.lam * deriv (scaledPulse c amp eta) (c.lam * y) =
      deriv (fun t => pulseRatio c amp (t, eta)) y := by
  have hF : (fun t => pulseRatio c amp (t, eta)) = forcing c (parameterPolynomial eta) (amp eta) :=
    by
    funext t
    exact (forcing_eq_pulseRatio c amp eta t).symm
  have hf := forcing_contDiff c (parameterPolynomial eta) (amp eta)
  have hc : HasDerivAt (scaledPulse c amp eta)
      (deriv (forcing c (parameterPolynomial eta) (amp eta)) y / c.lam) (c.lam * y) := by
    have hscaled : scaledPulse c amp eta =
        fun z => forcing c (parameterPolynomial eta) (amp eta) (z / c.lam) := by
      funext z
      exact (forcing_eq_pulseRatio c amp eta (z / c.lam)).symm
    rw [hscaled]
    have h := ((hf.differentiable (by simp) ((c.lam * y) / c.lam)).hasDerivAt).comp (c.lam * y)
      ((hasDerivAt_id (c.lam * y)).div_const c.lam)
    simpa only [Function.comp_def, id_eq, mul_div_cancel_left₀ y c.lam_pos.ne', one_div,
      mul_inv_rev, mul_one, one_mul, div_eq_mul_inv] using h
  rw [hc.deriv, hF]
  field_simp [c.lam_pos.ne']

theorem pulseError_scaled (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    pulseError c amp eta y = normalizedLag c amp eta y -
      (pulseRatio c amp (y, eta) / decay c -
        c.lam * deriv (scaledPulse c amp eta) (c.lam * y) / decay c ^ 2 +
        (prefixCoefficient c 0 * parameterPolynomial eta) * Real.exp (-decay c * y)) := by
  rw [scaledPulse_deriv]
  rfl

noncomputable def fullError (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  normalizedLag c amp eta y - (pulseRatio c amp (y, eta) / decay c -
    c.lam * deriv (scaledPulse c amp eta) (c.lam * y) / decay c ^ 2)

theorem fullError_eq (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    fullError c amp eta y = pulseError c amp eta y +
      (prefixCoefficient c 0 * parameterPolynomial eta) * Real.exp (-decay c * y) := by
  rw [pulseError_scaled, fullError]
  ring

theorem fullError_eta_hasDerivAt (c : Parameters) {amp : ℝ → ℝ} {eta amp' : ℝ}
    (ha : HasDerivAt amp amp' eta) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun t => fullError c amp t y)
      (affineError c (1 + 3 * eta ^ 2) amp' y +
        (prefixCoefficient c 0 * (1 + 3 * eta ^ 2)) * Real.exp (-decay c * y)) eta := by
  have hfun : (fun t => fullError c amp t y) = fun t => pulseError c amp t y +
      (prefixCoefficient c 0 * parameterPolynomial t) * Real.exp (-decay c * y) := by
    funext t
    exact fullError_eq c amp t y
  rw [hfun]
  exact (pulseError_eta_hasDerivAt c ha hy).add
    (((parameterPolynomial_hasDerivAt eta).const_mul _).mul_const _)

theorem initial_memory_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    (q : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |(prefixCoefficient c 0 * q) * Real.exp (-decay c * y)| ≤
      prefixBound c.P c.m 0 * |q| * c.lam ^ 2 := by
  have hp := prefixCoefficient_small c hwait hsmall 0
  have he : Real.exp (-decay c * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (decay_pos c).le) hy)
  have hpow : c.lam ^ 29 ≤ c.lam ^ 2 :=
    pow_le_pow_of_le_one c.lam_pos.le (by linarith [c.lam_lt]) (by norm_num)
  have hP := prefixBound_pos c.P_pos c.m 0
  calc
    _ = |prefixCoefficient c 0| * |q| * Real.exp (-decay c * y) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (prefixBound c.P c.m 0 * c.lam ^ 29) * |q| * 1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hp (abs_nonneg q)) he
        (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg hP.le (pow_nonneg c.lam_pos.le _)) (abs_nonneg q))
    _ ≤ prefixBound c.P c.m 0 * |q| * c.lam ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (prefixBound_pos c.P_pos c.m 0).le (abs_nonneg q))
      nlinarith

noncomputable def fullLagBound (P m : ℝ) : ℝ := 5 * lagBound P m + 4 * prefixBound P m 0

theorem fullLagBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < fullLagBound P m := by
  have h₁ := lagBound_pos hP m
  have h₂ := prefixBound_pos hP m 0
  dsimp [fullLagBound]
  linarith

/-- A common explicit constant bounds the actual lag error and its first
parameter derivative on the full nonnegative pulse-time half-line. -/
theorem fullError_bounds_of_amplitude_bounds (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |amp'| ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) :
    |fullError c amp eta y| ≤ fullLagBound c.P c.m * c.lam ^ 2 ∧
      |deriv (fun t => fullError c amp t y) eta| ≤ fullLagBound c.P c.m * c.lam ^ 2 := by
  have hL := lagBound_pos c.P_pos c.m
  have hP := prefixBound_pos c.P_pos c.m 0
  have hq := parameterPolynomial_bound heta
  have hq' : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
      parameterPolynomial_derivative_bound heta
  constructor
  · have hmain : |pulseError c amp eta y| ≤ 4 * lagBound c.P c.m * c.lam ^ 2 := by
      apply (normalizedLag_error c hsmall amp heta hy).trans
      have ht : 2 + |amp eta| ≤ 4 := by linarith
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hL.le)
        (sq_nonneg c.lam)
      nlinarith
    have hmemory : |(prefixCoefficient c 0 * parameterPolynomial eta) * Real.exp (-decay c * y)| ≤
        2 * prefixBound c.P c.m 0 * c.lam ^ 2 := by
      apply (initial_memory_bound c hwait hsmall _ hy).trans
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hP.le)
        (sq_nonneg c.lam)
      nlinarith
    rw [fullError_eq]
    refine (abs_add_le _ _).trans ((add_le_add hmain hmemory).trans ?_)
    dsimp [fullLagBound]
    nlinarith [sq_nonneg c.lam]
  · rw [(fullError_eta_hasDerivAt c ha hy).deriv]
    have hmain : |affineError c (1 + 3 * eta ^ 2) amp' y| ≤
        5 * lagBound c.P c.m * c.lam ^ 2 := by
      apply (affineLag_error c hsmall _ _ hy).trans
      have hs : |1 + 3 * eta ^ 2| + |amp'| ≤ 5 := by linarith
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hL.le)
        (sq_nonneg c.lam)
      nlinarith
    have hmemory : |(prefixCoefficient c 0 * (1 + 3 * eta ^ 2)) * Real.exp (-decay c * y)| ≤
        4 * prefixBound c.P c.m 0 * c.lam ^ 2 := by
      apply (initial_memory_bound c hwait hsmall _ hy).trans
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hP.le)
        (sq_nonneg c.lam)
      nlinarith
    refine (abs_add_le _ _).trans ((add_le_add hmain hmemory).trans_eq ?_)
    dsimp [fullLagBound]
    ring

/-- The concrete energy-closing amplitude satisfies the lag estimate. -/
theorem amplitude_fullError_bounds (d : OutgoingTail.TailData)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120) (hscale : PulseAmplitude.errorScale d.core ≤ 1 / 1000)
    {eta y : ℝ} (heta : eta ^ 2 ≤ 1) (hy : 0 ≤ y) :
    |fullError d.core (PulseAmplitude.amplitude d) eta y| ≤
        fullLagBound d.core.P d.core.m * d.core.lam ^ 2 ∧
      |deriv (fun t => fullError d.core (PulseAmplitude.amplitude d) t y) eta| ≤
        fullLagBound d.core.P d.core.m * d.core.lam ^ 2 := by
  have hs := PulseAmplitude.amplitude_spec d hsmall hwait hscale
  have hb := hs.2 eta heta
  apply fullError_bounds_of_amplitude_bounds d.core hwait hsmall
    ((PulseAmplitude.amplitude_contDiff d).differentiable (by simp) eta).hasDerivAt
  · have h := sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [sq_abs eta]
  · rw [abs_of_pos (PulseAmplitude.amplitude_pos d eta)]
    exact hb.2.1.le
  · have hd := hb.2.2.2.1
    linarith
  · exact hy

/-- One positive threshold and one constant, selected before lambda,
control the lag and its first parameter derivative throughout the pulse. -/
theorem exists_uniform_lag_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam₀ C : ℝ, 0 < lam₀ ∧ 0 < C ∧ ∀ d : OutgoingTail.TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ → ∀ eta y : ℝ, eta ^ 2 ≤ 1 → 0 ≤ y →
        |fullError d.core (PulseAmplitude.amplitude d) eta y| ≤ C * d.core.lam ^ 2 ∧
        |deriv (fun t => fullError d.core (PulseAmplitude.amplitude d) t y) eta| ≤
          C * d.core.lam ^ 2 := by
  obtain ⟨δ, hδ, hrate⟩ := PulseAmplitude.exists_rate_threshold (PulseAmplitude.errorConstant P m)
  refine ⟨min δ (1 / 120), fullLagBound P m, lt_min hδ (by norm_num), fullLagBound_pos hP m, ?_⟩
  intro d hdP hdm hwait hsmall eta y heta hy
  have hl : d.core.lam ≤ 1 / 120 := (hsmall.trans_le (min_le_right _ _)).le
  have he : PulseAmplitude.errorScale d.core ≤ 1 / 1000 := by
    unfold PulseAmplitude.errorScale
    rw [hdP, hdm]
    exact hrate d.core.lam d.core.lam_pos (hsmall.trans_le (min_le_left _ _))
  simpa only [hdP, hdm] using amplitude_fullError_bounds d hwait hl he heta hy

theorem smooth_amplitude_fullError_bounds (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp)
    (hamp : ∀ eta : ℝ, eta ^ 2 ≤ 1 → |amp eta| ≤ 6 / 5)
    (hamp' : ∀ eta : ℝ, eta ^ 2 ≤ 1 → |deriv amp eta| ≤ 1) :
    ∀ eta y : ℝ, eta ^ 2 ≤ 1 → 0 ≤ y →
      |fullError c amp eta y| ≤ fullLagBound c.P c.m * c.lam ^ 2 ∧
        |deriv (fun t => fullError c amp t y) eta| ≤ fullLagBound c.P c.m * c.lam ^ 2 := by
  intro eta y heta hy
  apply fullError_bounds_of_amplitude_bounds c hwait hsmall
    (ha.differentiable (by simp) eta).hasDerivAt
  · exact (sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa using heta)
  · exact hamp eta heta
  · exact hamp' eta heta
  · exact hy

/-- The same lag estimate for the amplitude which closes the energy after
the actual angular-moment reset. -/
theorem corrected_amplitude_fullError_bounds
    {d : OutgoingTail.TailData} {K : ℝ} (w : UniformAngularReset.ResetWitness d K)
    (hK : 0 < K) (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 120)
    (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000) :
    ∀ eta y : ℝ, eta ^ 2 ≤ 1 → 0 ≤ y →
      |fullError d.core (CorrectedPulseAmplitude.amplitude d w.coefficients) eta y| ≤
        fullLagBound d.core.P d.core.m * d.core.lam ^ 2 ∧
      |deriv (fun t => fullError d.core (CorrectedPulseAmplitude.amplitude d w.coefficients) t y)
        eta| ≤
        fullLagBound d.core.P d.core.m * d.core.lam ^ 2 := by
  have hs := CorrectedPulseAmplitude.amplitude_spec w hK hsmall hwait hscale
  apply smooth_amplitude_fullError_bounds d.core hwait hsmall hs.1
  · intro eta heta
    rw [abs_of_pos (CorrectedPulseAmplitude.amplitude_pos d w.coefficients eta)]
    exact (hs.2 eta heta).2.1.le
  · intro eta heta
    have hd := (hs.2 eta heta).2.2.2.1
    linarith

/-- The corrected amplitude and reset witness are actually constructed by
`exists_corrected_amplitude`; an additional fixed threshold makes their
first derivative at most one. The common lag constant is independent of
lambda, the terminal parameter, eta, and pulse time. -/
theorem exists_corrected_uniform_lag_threshold (P m : ℝ) (hP : 0 < P) :
    ∃ lam₀ K C : ℝ, 0 < lam₀ ∧ 0 < K ∧ 0 < C ∧ ∀ d : OutgoingTail.TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ → ∃ w : UniformAngularReset.ResetWitness d K,
        ContDiff ℝ ∞ (CorrectedPulseAmplitude.amplitude d w.coefficients) ∧
        ∀ eta : ℝ, eta ^ 2 ≤ 1 →
          9 / 10 < CorrectedPulseAmplitude.amplitude d w.coefficients eta ∧
          CorrectedPulseAmplitude.amplitude d w.coefficients eta < 6 / 5 ∧
          CorrectedPulseAmplitude.totalEnergy d w.coefficients
            (CorrectedPulseAmplitude.amplitude d w.coefficients eta) eta = 0 ∧
          ∀ y : ℝ, 0 ≤ y →
            |fullError d.core (CorrectedPulseAmplitude.amplitude d w.coefficients) eta y| ≤
              C * d.core.lam ^ 2 ∧
            |deriv (fun t => fullError d.core (CorrectedPulseAmplitude.amplitude d w.coefficients)
              t y) eta| ≤
              C * d.core.lam ^ 2 := by
  obtain ⟨lamA, K, Cderiv, hlamA, hK, hCderiv, hA⟩ :=
    CorrectedPulseAmplitude.exists_corrected_amplitude P m hP
  obtain ⟨δ, hδ, hrate⟩ := PulseAmplitude.exists_rate_threshold Cderiv
  refine ⟨min lamA (min δ (1 / 120)), K, fullLagBound P m,
    lt_min hlamA (lt_min hδ (by norm_num)), hK, fullLagBound_pos hP m, ?_⟩
  intro d hdP hdm hwait hl
  have hlA : d.core.lam < lamA := hl.trans_le (min_le_left _ _)
  have hlrest : d.core.lam < min δ (1 / 120) := hl.trans_le (min_le_right _ _)
  have hsmall : d.core.lam ≤ 1 / 120 := (hlrest.trans_le (min_le_right _ _)).le
  obtain ⟨w, hs, hspec⟩ := hA d hdP hdm hwait hlA
  have hr := hrate d.core.lam d.core.lam_pos (hlrest.trans_le (min_le_left _ _))
  have hderiv : ∀ eta : ℝ, eta ^ 2 ≤ 1 →
      |deriv (CorrectedPulseAmplitude.amplitude d w.coefficients) eta| ≤ 1 := by
    intro eta heta
    have hb := (hspec eta heta).2.2.2.1
    have hsmallrate : Cderiv * d.core.lam * (1 + Real.log (1 / d.core.lam)) ≤ 1 / 1000 := by
      simpa only [PulseAmplitude.logarithmicRate, mul_assoc] using hr
    linarith
  refine ⟨w, hs, fun eta heta => ?_⟩
  have hb := hspec eta heta
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
  intro y hy
  have hlag := smooth_amplitude_fullError_bounds d.core hwait hsmall hs
    (fun eta heta => by
      rw [abs_of_pos (CorrectedPulseAmplitude.amplitude_pos d w.coefficients eta)]
      exact (hspec eta heta).2.1.le) hderiv eta y heta hy
  simpa only [hdP, hdm] using hlag

end ActualPulse

end NavierStokes.PulseLag

end
