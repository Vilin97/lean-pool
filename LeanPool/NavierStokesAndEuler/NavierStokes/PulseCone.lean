/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseLag
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingEntranceCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseEnergyHistory
public import LeanPool.NavierStokesAndEuler.NavierStokes.ShapedWaitBounds

@[expose] public section

/-!
# The actual pulse contribution to the outgoing stress cone

The endpoint lower bound, pulse stress expansions, and numerical cone
margins are derived from the actual corrected fields and their histories.
One small-parameter threshold preserves every prechosen reset witness.
-/

noncomputable section

namespace NavierStokes.PulseCone

open Set Filter MeasureTheory
open scoped Topology ContDiff
open OutgoingSchedule OutgoingPulseBounds PulseLag

noncomputable def forceConstant (P m : ℝ) : ℝ := mainBound + correctionJetBound P m 0

theorem forceConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < forceConstant P m :=
  add_pos mainBound_pos (correctionJetBound_pos hP m 0)

theorem forcing_abs_le (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (q A y : ℝ) :
    |forcing c q A y| ≤ forceConstant c.P c.m * (|q| + |A|) := by
  have hc := affineProfile_jet_bound c hsmall q A 0 y
  simp only [iteratedDeriv_zero] at hc
  have he : Real.exp (-(1 / (4 * c.lam))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by have hp := c.lam_pos; positivity))
  have hc' : |affineProfile c q A y| ≤ correctionJetBound c.P c.m 0 * (|q| + |A|) := by
    refine hc.trans ?_
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (correctionJetBound_pos c.P_pos c.m 0).le) (by positivity : 0 ≤
        |q| + |A|)
    simpa only [mul_one] using h
  have hm : |A * mainPulse (c.lam * y)| ≤ mainBound * |A| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (mainPulse_abs_le (c.lam * y)) (abs_nonneg A)]
  calc
    _ ≤ |A * mainPulse (c.lam * y)| + |affineProfile c q A y| := abs_add_le _ _
    _ ≤ mainBound * |A| + correctionJetBound c.P c.m 0 * (|q| + |A|) := add_le_add hm hc'
    _ ≤ _ := by dsimp [forceConstant]; nlinarith [mul_nonneg mainBound_pos.le (abs_nonneg q)]

theorem initial_coefficient_le (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120) :
    |prefixCoefficient c 0| ≤ prefixBound c.P c.m 0 := by
  apply (prefixCoefficient_small c hwait hsmall 0).trans
  have hp : c.lam ^ 29 ≤ 1 := pow_le_one₀ c.lam_pos.le (by linarith [c.lam_lt])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (prefixBound_pos c.P_pos c.m 0).le

theorem decay_div_le_three (c : Parameters) {M : ℝ} (hM : 0 ≤ M) :
    M / decay c ≤ 3 * M := by
  have hd : (2 / 5 : ℝ) ≤ decay c := by dsimp [decay]; linarith [c.lam_lt]
  apply (div_le_iff₀ (decay_pos c)).mpr
  nlinarith [mul_nonneg hM (show 0 ≤ 3 * decay c - 1 by linarith)]

theorem affineLag_abs_le (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |affineLag c q A y| ≤ prefixBound c.P c.m 0 * |q| +
      3 * forceConstant c.P c.m * (|q| + |A|) := by
  have hB : 0 ≤ forceConstant c.P c.m * (|q| + |A|) :=
    mul_nonneg (forceConstant_pos c.P_pos c.m).le (by positivity)
  have hc := convolution_abs_le (decay_pos c) hB hy (forcing_contDiff c q A).continuous
    (fun t _ => forcing_abs_le c hsmall q A t)
  have hc' := hc.trans (decay_div_le_three c hB)
  have he : Real.exp (-decay c * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (decay_pos c).le) hy)
  have hp : |(prefixCoefficient c 0 * q) * Real.exp (-decay c * y)| ≤
      prefixBound c.P c.m 0 * |q| := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right (initial_coefficient_le c hwait hsmall)
      (abs_nonneg q))
      he (Real.exp_pos _).le (mul_nonneg (prefixBound_pos c.P_pos c.m 0).le (abs_nonneg q))
    simpa only [mul_one] using h
  calc
    _ ≤ |(prefixCoefficient c 0 * q) * Real.exp (-decay c * y)| +
        |convolution (decay c) (forcing c q A) y| := abs_add_le _ _
    _ ≤ prefixBound c.P c.m 0 * |q| + 3 * (forceConstant c.P c.m * (|q| + |A|)) :=
      add_le_add hp hc'
    _ = _ := by ring

noncomputable def averageConstant (P m : ℝ) : ℝ := 4 * prefixBound P m 0 + 18 * forceConstant P m

theorem averageConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < averageConstant P m := by
  have hp := prefixBound_pos hP m 0
  have hf := forceConstant_pos hP m
  dsimp [averageConstant]
  linarith

/-- Uniform bounds for the actual pulse ratio, normalized mass history,
and its first parameter derivative. -/
theorem pulse_data_bounds (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |amp'| ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) :
    |pulseRatio c amp (y, eta)| ≤ 6 * forceConstant c.P c.m ∧
      |normalizedLag c amp eta y| ≤ averageConstant c.P c.m ∧
      |deriv (fun t => normalizedLag c amp t y) eta| ≤ averageConstant c.P c.m := by
  have hq := parameterPolynomial_bound heta
  have hq' : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
      parameterPolynomial_derivative_bound heta
  have hp := prefixBound_pos c.P_pos c.m 0
  have hf := forceConstant_pos c.P_pos c.m
  constructor
  · rw [← forcing_eq_pulseRatio c amp eta y]
    apply (forcing_abs_le c hsmall _ _ y).trans
    nlinarith [mul_le_mul_of_nonneg_left (show |parameterPolynomial eta| + |amp eta| ≤ 6 by
      linarith) hf.le]
  constructor
  · rw [normalizedLag_eq_affineLag c amp eta hy]
    apply (affineLag_abs_le c hwait hsmall _ _ hy).trans
    dsimp [averageConstant]
    have hs : |parameterPolynomial eta| + |amp eta| ≤ 6 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hq hp.le, mul_le_mul_of_nonneg_left hs hf.le]
  · rw [(normalizedLag_eta_hasDerivAt c ha hy).deriv]
    apply (affineLag_abs_le c hwait hsmall _ _ hy).trans
    dsimp [averageConstant]
    have hs : |1 + 3 * eta ^ 2| + |amp'| ≤ 6 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hq' hp.le, mul_le_mul_of_nonneg_left hs hf.le]

noncomputable def energyConstant (P m : ℝ) : ℝ := P * Real.exp (Real.exp m + 12)

theorem energyConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < energyConstant P m :=
  mul_pos hP (Real.exp_pos _)

theorem shape_le_one (eta : ℝ) : shape eta ≤ 1 := by
  unfold shape
  rw [← one_div]
  apply (div_le_one (by positivity : 0 < 1 + eta ^ 2)).mpr
  nlinarith [sq_nonneg eta]

theorem pulse_angular_small (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    angular c.P c.dropLength c.lam (c.pulseStart + y, eta) ≤
      energyConstant c.P c.m * c.lam ^ 30 := by
  rw [angular_pulse c eta (by linarith)]
  have hsub : c.pulseStart + y - c.pulseStart = y := by ring
  rw [hsub]
  have he : Real.exp (-(1 / 2 + c.lam) * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (by linarith [c.lam_pos]) hy)
  have h := mul_le_mul (mul_le_mul (pulseAmplitude_small c hwait) (shape_le_one eta)
    (shape_pos eta).le (by have hp := c.P_pos; positivity)) he (Real.exp_pos _).le
    (by have hp := c.P_pos; positivity)
  simpa only [mul_one, energyConstant] using h

noncomputable def shapeGradient (eta : ℝ) : ℝ := 2 * eta / (1 + eta ^ 2)

theorem shapeGradient_bound {eta : ℝ} (heta : |eta| ≤ 1) : |shapeGradient eta| ≤ 2 := by
  rw [shapeGradient, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (by positivity : 0 < 1 + eta ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 1 + eta ^ 2)).mpr
  nlinarith [sq_nonneg eta]

theorem source_remainder_bound {E lam a b c m mp R M F : ℝ}
    (hE : 0 ≤ E) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1)
    (ha : |a| ≤ 3) (hb : |b| ≤ 1) (hc : |c| ≤ 3)
    (hm : |m| ≤ M) (hmp : |mp| ≤ M) (hR : |R| ≤ F) :
    |E * (-lam * (a * m + b * mp) + c * R)| ≤ E * (4 * M + 3 * F) := by
  have hm₁ : |a * m| ≤ 3 * M := by
    rw [abs_mul]
    exact mul_le_mul ha hm (abs_nonneg m) (by norm_num)
  have hm₂ : |b * mp| ≤ M := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hb hmp (abs_nonneg mp) (by norm_num)
  have hsum : |a * m + b * mp| ≤ 4 * M := by
    exact (abs_add_le _ _).trans (by linarith)
  have hterm : |-lam * (a * m + b * mp)| ≤ 4 * M := by
    rw [abs_mul, abs_neg, abs_of_nonneg hlam]
    have h := mul_le_mul hlam' hsum (abs_nonneg _) (by norm_num)
    simpa only [one_mul] using h
  have hr : |c * R| ≤ 3 * F := by
    rw [abs_mul]
    exact mul_le_mul hc hR (abs_nonneg R) (by norm_num)
  rw [abs_mul, abs_of_nonneg hE]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hterm hr)) hE

theorem geometric_coefficient_bounds {h eta : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 2)
    (heta : |eta| ≤ 1) :
    |2 * (1 / 2 - h) * eta - (1 - eta ^ 2) * shapeGradient eta| ≤ 3 ∧
      |1 - eta ^ 2| ≤ 1 ∧ |2 * h * eta + (1 - eta ^ 2) * shapeGradient eta| ≤ 3 := by
  have hs : eta ^ 2 ≤ 1 := by nlinarith [sq_abs eta, sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 :
    ℝ) ≤ 1) |>.mpr heta]
  have hd : |1 - eta ^ 2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; nlinarith [sq_nonneg eta]
  have hD : |1 / 2 - h| ≤ 1 / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hg : |(1 - eta ^ 2) * shapeGradient eta| ≤ 2 := by
    rw [abs_mul]
    have hm := mul_le_mul hd (shapeGradient_bound heta) (abs_nonneg _) (by norm_num)
    norm_num at hm ⊢
    exact hm
  have hDeta : |2 * (1 / 2 - h) * eta| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul hD heta (abs_nonneg eta) (by norm_num)]
  have heta' : |2 * h * eta| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hh]
    nlinarith [mul_le_mul hh' heta (abs_nonneg eta) (by norm_num)]
  exact ⟨(abs_sub _ _).trans (by linarith), hd, (abs_add_le _ _).trans (by linarith)⟩

noncomputable def pulseAngularSource (c : Parameters) (h : ℝ) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  let E := angular c.P c.dropLength c.lam (c.pulseStart + y, eta)
  let R := pulseRatio c amp (y, eta)
  let m := normalizedLag c amp eta y
  let mp := deriv (fun t => normalizedLag c amp t y) eta
  c.lam * (1 - 2 * (1 / 2 - h) * eta * E * m -
      (1 - eta ^ 2) * E * (mp - shapeGradient eta * m)) -
    h * (1 - 2 * eta * E * R) +
    ((1 / 2 - h) * eta + (1 - eta ^ 2) * E * R) * shapeGradient eta

theorem pulseAngularSource_error_identity (c : Parameters) (h : ℝ) (amp : ℝ → ℝ) (eta y : ℝ) :
    pulseAngularSource c h amp eta y - (c.lam - h + (1 / 2 - h) * eta * shapeGradient eta) =
      angular c.P c.dropLength c.lam (c.pulseStart + y, eta) *
        (-c.lam * ((2 * (1 / 2 - h) * eta - (1 - eta ^ 2) * shapeGradient eta) *
          normalizedLag c amp eta y + (1 - eta ^ 2) * deriv (fun t => normalizedLag c amp t y) eta)
            +
          (2 * h * eta + (1 - eta ^ 2) * shapeGradient eta) * pulseRatio c amp (y, eta)) := by
  unfold pulseAngularSource
  ring

noncomputable def sourceConstant (P m : ℝ) : ℝ :=
  energyConstant P m * (4 * averageConstant P m + 18 * forceConstant P m)

theorem sourceConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < sourceConstant P m := by
  have he := energyConstant_pos hP m
  have ha := averageConstant_pos hP m
  have hf := forceConstant_pos hP m
  dsimp [sourceConstant]
  positivity

theorem pulseAngularSource_error_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 2)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |amp'| ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) :
    |pulseAngularSource c h amp eta y - (c.lam - h + (1 / 2 - h) * eta * shapeGradient eta)| ≤
      sourceConstant c.P c.m * c.lam ^ 30 := by
  obtain ⟨hR, hm, hmp⟩ := pulse_data_bounds c hwait hsmall ha heta hamp hamp' hy
  obtain ⟨hc₁, hc₂, hc₃⟩ := geometric_coefficient_bounds hh hh' heta
  rw [pulseAngularSource_error_identity]
  have hb := source_remainder_bound
    (angular_pos c.P_pos c.dropLength c.lam (c.pulseStart + y, eta)).le
    c.lam_pos.le (show c.lam ≤ 1 by linarith [c.lam_lt])
    hc₁ hc₂ hc₃ hm hmp hR
  refine hb.trans ?_
  have hp : 0 ≤ 4 * averageConstant c.P c.m + 18 * forceConstant c.P c.m := by
    have ha := averageConstant_pos c.P_pos c.m
    have hf := forceConstant_pos c.P_pos c.m
    positivity
  have he := mul_le_mul_of_nonneg_right (pulse_angular_small c hwait eta hy) hp
  dsimp [sourceConstant]
  nlinarith

theorem pulseAngularSource_lower (d : OutgoingTail.TailData)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (herr : sourceConstant d.core.P d.core.m * d.core.lam ^ 29 ≤ 1 / 8)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |amp'| ≤ 1)
    {y : ℝ} (hy : 0 ≤ y) :
    3 * d.core.lam / 8 ≤ pulseAngularSource d.core d.h amp eta y := by
  have he := pulseAngularSource_error_bound d.core hwait hsmall d.h_pos.le d.h_lt_half.le
    ha heta hamp hamp' hy
  have herr' := mul_le_mul_of_nonneg_right herr d.core.lam_pos.le
  have hpow : d.core.lam ^ 29 * d.core.lam = d.core.lam ^ 30 := by ring
  rw [mul_assoc, hpow] at herr'
  have hg : 0 ≤ eta * shapeGradient eta := by
    have heq : eta * shapeGradient eta = 2 * eta ^ 2 / (1 + eta ^ 2) := by
      unfold shapeGradient
      ring
    rw [heq]
    positivity
  have hc := mul_nonneg (show 0 ≤ 1 / 2 - d.h by linarith [d.h_lt_half]) hg
  have hlo := (abs_le.mp he).1
  nlinarith [d.h_small]

/-- A lower barrier for the exact scalar lag equation on a finite interval.
Only the differential equation and a lower source bound are used. -/
theorem ode_lower_barrier {r s L : ℝ} (hr : 0 < r) (hL : 0 ≤ L)
    {Q S : ℝ → ℝ}
    (hQ : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt Q (S t - r * Q t) t)
    (hS : ∀ t ∈ Icc (0 : ℝ) L, s ≤ S t) :
    s / r + (Q 0 - s / r) * Real.exp (-r * L) ≤ Q L := by
  let G : ℝ → ℝ := fun t => Real.exp (r * t) * (Q t - s / r)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt G (Real.exp (r * t) * (S t - s)) t := by
    convert! (((hasDerivAt_id t).const_mul r).exp).mul ((hQ t ht).sub_const (s / r)) using 1
    dsimp [G]
    field_simp ; ring
  have hcont : ContinuousOn G (Icc (0 : ℝ) L) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hm : MonotoneOn G (Icc (0 : ℝ) L) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hS t (interior_subset ht))))
  have hg := hm ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩ hL
  have hp := mul_le_mul_of_nonneg_right hg (Real.exp_pos (-r * L)).le
  have he : Real.exp (r * L) * Real.exp (-r * L) = 1 := by
    rw [← Real.exp_add]
    convert! Real.exp_zero using 1
    ring_nf
  dsimp [G] at hp
  simp only [mul_zero, Real.exp_zero, one_mul] at hp
  have hre : (Real.exp (r * L) * (Q L - s / r)) * Real.exp (-r * L) = Q L - s / r := by
    calc
      _ = (Real.exp (r * L) * Real.exp (-r * L)) * (Q L - s / r) := by ring
      _ = _ := by rw [he, one_mul]
  rw [hre] at hp
  linarith

theorem pulse_memory_small (c : Parameters) :
    Real.exp (-(1 - c.lam) * c.pulseLength) ≤ 1 / 3 := by
  have htime : 2 ≤ (1 - c.lam) * c.pulseLength := by
    unfold Parameters.pulseLength
    rw [← mul_div_assoc]
    apply (le_div_iff₀ c.lam_pos).mpr
    linarith [c.lam_lt]
  have hex : 3 ≤ Real.exp ((1 - c.lam) * c.pulseLength) := by
    linarith [Real.add_one_le_exp ((1 - c.lam) * c.pulseLength)]
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hex
  rw [one_div, ← Real.exp_neg] at hi
  convert! hi using 1
  ring_nf

/-- The long actual pulse turns a nonnegative incoming angular lag and
the lower source `3*lambda/8` into the endpoint bound needed by the tail. -/
theorem pulse_endpoint_lower (c : Parameters) {Q S : ℝ → ℝ} (hQ₀ : 0 ≤ Q 0)
    (hQ : ∀ t ∈ Icc (0 : ℝ) c.pulseLength,
      HasDerivAt Q (S t - (1 - c.lam) * Q t) t)
    (hS : ∀ t ∈ Icc (0 : ℝ) c.pulseLength, 3 * c.lam / 8 ≤ S t) :
    c.lam / 4 ≤ Q c.pulseLength := by
  have hr : 0 < 1 - c.lam := by linarith [c.lam_lt]
  have hlower := ode_lower_barrier hr c.pulseLength_pos.le hQ hS
  have hm := pulse_memory_small c
  have he := Real.exp_pos (-(1 - c.lam) * c.pulseLength)
  have hpos : 0 ≤ (3 * c.lam / 8) / (1 - c.lam) := by have hl := c.lam_pos; positivity
  have hdiv : 3 * c.lam / 8 ≤ (3 * c.lam / 8) / (1 - c.lam) := by
    apply (le_div_iff₀ hr).mpr
    nlinarith [c.lam_pos]
  have hmain := mul_le_mul hdiv (show (2 / 3 : ℝ) ≤ 1 - Real.exp (-(1 - c.lam) * c.pulseLength) by
    linarith)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) hpos
  have hini := mul_nonneg hQ₀ he.le
  nlinarith

/-! ## Binding the pulse formulas to the actual corrected histories -/

open OutgoingHistories
open OutgoingTail (TailData)
open UniformAngularReset (ResetWitness)

variable {d : TailData} {K : ℝ}

/-- One-sided equality before the endpoint determines the true radial
derivative there as well, since both profiles are smooth. -/
theorem E_radial_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    dY (E w) (y, eta) = angular d.core.P d.core.dropLength d.core.lam (y, eta) *
      (slope d.core.dropLength d.core.lam y - 1 / 2) := by
  have hd := ((radialAmplitude_hasDerivAt d.core.P d.core.dropLength d.core.lam y).mul_const
    (shape eta)).hasDerivWithinAt (s := Iic d.core.endpoint)
  have hd' := hd.congr (fun t ht => E_before w eta ht) (E_before w eta hy)
  have he := (uniqueDiffOn_Iic d.core.endpoint y hy).eq_deriv _
    (dY_hasDerivAt (E_smooth w) (y, eta)).hasDerivWithinAt hd'
  calc
    _ = (radialAmplitude d.core.P d.core.dropLength d.core.lam y *
      (slope d.core.dropLength d.core.lam y - 1 / 2)) * shape eta := he
    _ = _ := by unfold angular; ring

theorem E_parameter_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    dEta (E w) (y, eta) = E w (y, eta) * (-shapeGradient eta) := by
  have hd := (UniformAngularReset.shape_hasDerivAt eta).const_mul
    (radialAmplitude d.core.P d.core.dropLength d.core.lam y)
  have hd' := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => E_before w t hy))
  calc
    _ = radialAmplitude d.core.P d.core.dropLength d.core.lam y *
      (shape eta * (-(2 * eta / (1 + eta ^ 2)))) :=
        (dEta_hasDerivAt (E_smooth w) (y, eta)).unique hd'
    _ = _ := by rw [E_before w eta hy]; unfold angular shapeGradient; ring

theorem E_parameter_ratio_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    dEta (E w) (y, eta) / E w (y, eta) = -shapeGradient eta := by
  rw [E_parameter_before w eta hy]
  field_simp [(E_pos w (y, eta)).ne']

theorem H_radial_ratio_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.core.endpoint) :
    dY (H w) (y, eta) / H w (y, eta) = slope d.core.dropLength d.core.lam y := by
  have hd := (((hasDerivAt_id y).div_const 2).exp).fun_mul
    (dY_hasDerivAt (E_smooth w) (y, eta))
  have he := (dY_hasDerivAt (H_smooth w) (y, eta)).unique hd
  rw [he, E_radial_before w eta hy, ← E_before w eta hy]
  unfold H
  dsimp only [Prod.fst, id_eq]
  field_simp [(Real.exp_pos (y / 2)).ne', (E_pos w (y, eta)).ne'] ; ring

theorem H_radial_ratio_pulse (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    dY (H w) (d.core.pulseStart + y, eta) / H w (d.core.pulseStart + y, eta) =
      -d.core.lam := by
  rw [H_radial_ratio_before w eta (by dsimp [Parameters.endpoint]; linarith)]
  apply slope_hold d.core.dropLength_pos.le
  have hh := d.core.pulseStart_ge_hold
  dsimp [Parameters.holdStart] at hh
  linarith

theorem U_pulse (w : ResetWitness d K) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    U d amp (d.core.pulseStart + y, eta) =
      E w (d.core.pulseStart + y, eta) * pulseRatio d.core amp (y, eta) := by
  rw [U, axial_pulse d.core amp eta (by linarith), radialPulse_exp,
    E_before w eta (by dsimp [Parameters.endpoint]; linarith)]
  congr 2
  ring_nf

theorem Ubar_pulse (w : ResetWitness d K) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy' : y ≤ d.core.pulseLength) :
    Ubar d amp (d.core.pulseStart + y, eta) =
      E w (d.core.pulseStart + y, eta) * normalizedLag d.core amp eta y := by
  rw [Ubar, M_eq_massMoment,
    E_before w eta (by dsimp [Parameters.endpoint]; linarith)]
  unfold normalizedLag X
  dsimp only [Prod.fst]
  field_simp [(Real.exp_pos (d.core.pulseStart + y)).ne',
    (angular_pos d.core.P_pos d.core.dropLength d.core.lam (d.core.pulseStart + y, eta)).ne']

theorem Ubar_parameter_pulse (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    dEta (Ubar d amp) (d.core.pulseStart + y, eta) =
      E w (d.core.pulseStart + y, eta) *
        (deriv (fun t => normalizedLag d.core amp t y) eta -
          shapeGradient eta * normalizedLag d.core amp eta y) := by
  have hn := (normalizedLag_eta_hasDerivAt d.core
    ((ha.differentiable (by simp) eta).hasDerivAt) hy).differentiableAt.hasDerivAt
  have hd := (dEta_hasDerivAt (E_smooth w) (d.core.pulseStart + y, eta)).mul hn
  have hd' := hd.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => Ubar_pulse w amp t hy'))
  have he := (dEta_hasDerivAt (Ubar_smooth d ha) (d.core.pulseStart + y, eta)).unique hd'
  rw [he, E_parameter_before w eta (by dsimp [Parameters.endpoint]; linarith)]
  ring

/-- The source estimate is for the actual stress history: no source
formula or lag approximation is an input. -/
theorem Sq_pulse (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    Sq w amp (d.core.pulseStart + y, eta) = pulseAngularSource d.core d.h amp eta y := by
  rw [Sq_formula, H_radial_ratio_pulse w eta hy hy',
    E_parameter_ratio_before w eta (by dsimp [Parameters.endpoint]; linarith),
    W_formula d ha, Ubar_pulse w amp eta hy', Ubar_parameter_pulse w ha eta hy hy',
    U_pulse w amp eta hy hy', E_before w eta (by dsimp [Parameters.endpoint]; linarith)]
  dsimp only [Prod.snd, StressAlgebra.axialExponent, StressAlgebra.coordinateFactor,
    pulseAngularSource]
  ring

theorem Qs_pulse_hasDerivAt (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    HasDerivAt (fun t => Qs w amp (d.core.pulseStart + t, eta))
      (pulseAngularSource d.core d.h amp eta y -
        (1 - d.core.lam) * Qs w amp (d.core.pulseStart + y, eta)) y := by
  have hd := (Qs_hasDerivAt w ha (d.core.pulseStart + y, eta)).comp y
    ((hasDerivAt_id y).const_add d.core.pulseStart)
  rw [Sq_pulse w ha eta hy hy', H_radial_ratio_pulse w eta hy hy'] at hd
  simp only [mul_one, Function.comp_def] at hd
  exact hd

/-- The actual angular lag at the endpoint, initially conditional only
on its incoming sign and explicit schedule/amplitude bounds. -/
theorem Qs_endpoint_lower_of_nonnegative_entry (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (herr : sourceConstant d.core.P d.core.m * d.core.lam ^ 29 ≤ 1 / 8)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hentry : 0 ≤ Qs w amp (d.core.pulseStart, eta)) :
    d.core.lam / 4 ≤ Qs w amp (d.core.endpoint, eta) := by
  have h := pulse_endpoint_lower d.core
    (Q := fun t => Qs w amp (d.core.pulseStart + t, eta))
    (S := pulseAngularSource d.core d.h amp eta)
    (by simpa only [add_zero] using hentry)
    (fun t ht => Qs_pulse_hasDerivAt w ha eta ht.1 ht.2)
    (fun t ht => pulseAngularSource_lower d hwait hsmall herr
      ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp' ht.1)
  exact h

/-- A positive threshold selected from the two fixed prefix parameters. -/
noncomputable def sourceThreshold (P m : ℝ) : ℝ :=
  min (1 / 120) (1 / (8 * sourceConstant P m))

theorem sourceThreshold_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < sourceThreshold P m := by
  have hc := sourceConstant_pos hP m
  unfold sourceThreshold
  positivity

theorem source_error_small (c : Parameters)
    (hsmall : c.lam ≤ sourceThreshold c.P c.m) :
    sourceConstant c.P c.m * c.lam ^ 29 ≤ 1 / 8 := by
  have hc := sourceConstant_pos c.P_pos c.m
  have hlam : c.lam ≤ 1 := by
    have h := hsmall.trans (min_le_left _ _)
    linarith
  have hp : c.lam ^ 29 ≤ c.lam := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one c.lam_pos.le hlam (show 1 ≤ 29 by norm_num)
  have hprod := (le_div_iff₀ (show 0 < 8 * sourceConstant c.P c.m by positivity)).mp
    (hsmall.trans (min_le_right _ _))
  have hm := mul_le_mul_of_nonneg_left hp hc.le
  nlinarith

/-- Exact stability estimate for a scalar lag around a constant source.
The source error is allowed to have either sign. -/
theorem ode_equilibrium_error {r s δ L : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    {Q S : ℝ → ℝ}
    (hQ : ∀ t ∈ Icc (0 : ℝ) L, HasDerivAt Q (S t - r * Q t) t)
    (hS : ∀ t ∈ Icc (0 : ℝ) L, |S t - s| ≤ δ) :
    |Q L - s / r| ≤ |Q 0 - s / r| * Real.exp (-r * L) + δ / r := by
  have hlo := ode_lower_barrier hr hL hQ
    (s := s - δ) (fun t ht => by have h := (abs_le.mp (hS t ht)).1; linarith)
  have hneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt (fun t => -Q t) (-S t - r * (-Q t)) t := by
    convert! (hQ t ht).neg using 1
    ring
  have hhi := ode_lower_barrier hr hL hneg
    (s := -(s + δ)) (S := fun t => -S t)
    (fun t ht => by
      have h := (abs_le.mp (hS t ht)).2
      change -(s + δ) ≤ -S t
      linarith)
  have he : 0 ≤ Real.exp (-r * L) := (Real.exp_pos _).le
  have hp := mul_le_mul_of_nonneg_right (le_abs_self (Q 0 - s / r)) he
  have hm := mul_le_mul_of_nonneg_right (neg_abs_le (Q 0 - s / r)) he
  have hδr : 0 ≤ δ / r := div_nonneg hδ hr.le
  have hδe := mul_nonneg hδr he
  rw [abs_le]
  constructor
  · rw [sub_div] at hlo
    nlinarith
  · rw [neg_div, add_div] at hhi
    nlinarith

/-- Uniform angular-lag error throughout the actual pulse; the incoming
error is retained explicitly for the shaped-wait theorem to supply. -/
theorem Qs_pulse_equilibrium_error (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |Qs w amp (d.core.pulseStart + y, eta) -
      (d.core.lam - d.h + (1 / 2 - d.h) * eta * shapeGradient eta) / (1 - d.core.lam)| ≤
      |Qs w amp (d.core.pulseStart, eta) -
        (d.core.lam - d.h + (1 / 2 - d.h) * eta * shapeGradient eta) / (1 - d.core.lam)| *
          Real.exp (-(1 - d.core.lam) * y) +
        sourceConstant d.core.P d.core.m * d.core.lam ^ 30 / (1 - d.core.lam) := by
  have h := ode_equilibrium_error (show 0 < 1 - d.core.lam by linarith [d.core.lam_lt])
    (show 0 ≤ sourceConstant d.core.P d.core.m * d.core.lam ^ 30 by
      have hc := sourceConstant_pos d.core.P_pos d.core.m; positivity) hy
    (Q := fun t => Qs w amp (d.core.pulseStart + t, eta))
    (S := pulseAngularSource d.core d.h amp eta)
    (fun t ht => Qs_pulse_hasDerivAt w ha eta ht.1 (ht.2.trans hy'))
    (fun t ht => pulseAngularSource_error_bound d.core hwait hsmall d.h_pos.le d.h_lt_half.le
      ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp' ht.1)
  simpa only [add_zero] using h

/-- The actual endpoint lower bound follows from the constructed incoming
history and numerical parameter restrictions, with no incoming-lag or
source estimate assumed. -/
theorem Qs_endpoint_lower (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (hpulse : sourceConstant d.core.P d.core.m * d.core.lam ^ 29 ≤ 1 / 8)
    (hh₁ : d.h ≤ 1 / 100)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1) :
    d.core.lam / 4 ≤ Qs w amp (d.core.endpoint, eta) :=
  Qs_endpoint_lower_of_nonnegative_entry w hwait hsmall hpulse ha heta hamp hamp'
    (OutgoingEntranceCone.canonical_Qs_pos_at_pulseStart w ha hh₁ hhT heta).le

theorem Qs_endpoint_lower_of_threshold (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ sourceThreshold d.core.P d.core.m)
    (hh₁ : d.h ≤ 1 / 100)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1) :
    d.core.lam / 4 ≤ Qs w amp (d.core.endpoint, eta) :=
  Qs_endpoint_lower w hwait (hsmall.trans (min_le_left _ _))
    (source_error_small d.core hsmall) hh₁ hhT ha heta hamp hamp'

/-- The final energy-closing amplitude, including the angular reset, is
the amplitude used in this endpoint theorem. -/
theorem corrected_Qs_endpoint_lower (w : ResetWitness d K) (hK : 0 < K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hpulse : sourceConstant d.core.P d.core.m * d.core.lam ^ 29 ≤ 1 / 8)
    (hh₁ : d.h ≤ 1 / 100)
    (hhT : d.h ≤ Real.exp (-(d.core.holdStart + 3 / 5)) / 8)
    {eta : ℝ} (heta : |eta| ≤ 1) :
    d.core.lam / 4 ≤ Qs w (CorrectedPulseAmplitude.amplitude d w.coefficients)
      (d.core.endpoint, eta) := by
  have hs := CorrectedPulseAmplitude.amplitude_spec w hK hsmall hwait hscale
  have heta₂ : eta ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1)).mpr heta
    nlinarith [sq_abs eta]
  have hb := hs.2 eta heta₂
  apply Qs_endpoint_lower w hwait hsmall hpulse hh₁ hhT hs.1 heta
  · rw [abs_of_pos (CorrectedPulseAmplitude.amplitude_pos d w.coefficients eta)]
    exact hb.2.1.le
  · have hd := hb.2.2.2.1
    linarith

/-! ## The axial identity and the genuine pressure remainder -/

theorem Ns_integrated_Ubar (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (p : Point) :
    Ns w amp p = -W d amp p * U d amp p +
      StressAlgebra.axialExponent d.h * (Ubar d amp p - p.2 * dEta (Ubar d amp) p) +
      (4 * d.h * p.2 * S w amp p - StressAlgebra.coordinateFactor p.2 * dEta (S w amp) p) / X p +
      4 * StressAlgebra.velocityExponent d.h * p.2 * Pi w p -
        StressAlgebra.coordinateFactor p.2 * dEta (Pi w) p := by
  rw [Ns_integrated, Ubar_parameter d ha]
  unfold Ubar
  ring

noncomputable def axialHistoryError (w : ResetWitness d K) (amp : ℝ → ℝ)
    (eta y : ℝ) : ℝ :=
  let p := (d.core.pulseStart + y, eta)
  (1 - W d amp p) * pulseRatio d.core amp (y, eta) +
    ((4 * d.h * eta * S w amp p - (1 - eta ^ 2) * dEta (S w amp) p) / X p +
      4 * (1 / 2 + d.h) * eta * Pi w p - (1 - eta ^ 2) * dEta (Pi w) p) / E w p

/-- Exact substitution in the integrated axial stress.  The error is an
explicit expression in the same constructed energy and pressure histories. -/
theorem Ns_pulse_identity (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    Ns w amp (d.core.pulseStart + y, eta) / E w (d.core.pulseStart + y, eta) =
      -pulseRatio d.core amp (y, eta) +
        ((1 / 2 - d.h) + (1 / 2 - d.h) * eta * shapeGradient eta) * normalizedLag d.core amp eta y -
        (1 / 2 - d.h) * eta * deriv (fun t => normalizedLag d.core amp t y) eta +
        axialHistoryError w amp eta y := by
  rw [Ns_integrated_Ubar w ha, U_pulse w amp eta hy hy', Ubar_pulse w amp eta hy',
    Ubar_parameter_pulse w ha eta hy hy']
  dsimp only [Prod.snd, StressAlgebra.axialExponent, StressAlgebra.velocityExponent,
    StressAlgebra.coordinateFactor, axialHistoryError]
  field_simp [(E_pos w (d.core.pulseStart + y, eta)).ne'] ; ring

theorem Pi_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.endpoint) :
    Pi w (y, eta) = FuturePressureBounds.Pi d y eta := by
  have hI : (∫ t in (0 : ℝ)..y, pressureWeight w (t, eta)) =
      (shape eta ^ 2 / 2) *
        ∫ t in (0 : ℝ)..y, radialAmplitude d.core.P d.core.dropLength d.core.lam t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ≤ d.core.endpoint := ((uIcc_of_le hy ▸ ht).2).trans hy'
    change E w (t, eta) ^ 2 / 2 = _
    rw [E_before w eta ht']
    unfold angular
    ring
  rw [FuturePressureBounds.Pi_eq_radial_history d hy hy' eta]
  change initialPi d eta + (∫ t in (0 : ℝ)..y, pressureWeight w (t, eta)) = _
  rw [hI]
  unfold initialPi
  ring

theorem Pi_parameter_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.endpoint) :
    dEta (Pi w) (y, eta) = deriv (FuturePressureBounds.Pi d y) eta := by
  rw [dEta_eq_deriv (Pi_smooth w)]
  have he : (fun eta => Pi w (y, eta)) = FuturePressureBounds.Pi d y :=
    funext (fun eta => Pi_before w eta hy hy')
  rw [he]

/-- Uniform value and first parameter derivative bounds for the actual
canonical pressure throughout the pulse. -/
theorem pulse_pressure_bounds (w : ResetWitness d K) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |Pi w (d.core.pulseStart + y, eta)| ≤ (FuturePressureBounds.envelopeConstant / 2) *
        E w (d.core.pulseStart + y, eta) ^ 2 ∧
      |dEta (Pi w) (d.core.pulseStart + y, eta)| ≤
        2 * FuturePressureBounds.envelopeConstant * |eta| * E w (d.core.pulseStart + y, eta) ^ 2 :=
          by
  have hy₀ : 0 ≤ d.core.pulseStart + y := by linarith [d.core.pulseStart_pos]
  have hyend : d.core.pulseStart + y ≤ d.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith
  rw [Pi_before w eta hy₀ hyend, Pi_parameter_before w eta hy₀ hyend, E_before w eta hyend]
  have h := FuturePressureBounds.uniform_pressure_bounds d hy₀ heta
  rw [OutgoingTail.finalAngular_before d eta hyend] at h
  exact ⟨h.1, h.2.1⟩

/-! ## Actual viscous coefficients on the pulse -/

noncomputable def radialA (w : ResetWitness d K) (p : Point) : ℝ :=
  2 - 2 * (dY (H w) p / H w p)

noncomputable def shearB (w : ResetWitness d K) (amp : ℝ → ℝ) (p : Point) : ℝ :=
  2 * dY (U d amp) p / E w p

noncomputable def directionRatio (w : ResetWitness d K) (amp : ℝ → ℝ) (p : Point) : ℝ :=
  Ns w amp p / (E w p * Qs w amp p)

theorem radialA_pulse (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    radialA w (d.core.pulseStart + y, eta) = 2 + 2 * d.core.lam := by
  rw [radialA, H_radial_ratio_pulse w eta hy hy']
  ring

theorem E_radial_pulse (w : ResetWitness d K) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    dY (E w) (d.core.pulseStart + y, eta) =
      E w (d.core.pulseStart + y, eta) * (-(1 / 2 + d.core.lam)) := by
  have hyend : d.core.pulseStart + y ≤ d.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith
  rw [E_radial_before w eta hyend, ← E_before w eta hyend,
    slope_hold d.core.dropLength_pos.le (by
      have h := d.core.pulseStart_ge_hold
      dsimp [Parameters.holdStart] at h
      linarith)]
  ring

theorem U_radial_pulse (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    dY (U d amp) (d.core.pulseStart + y, eta) =
      E w (d.core.pulseStart + y, eta) *
        (deriv (fun t => pulseRatio d.core amp (t, eta)) y -
          (1 / 2 + d.core.lam) * pulseRatio d.core amp (y, eta)) := by
  have hshift := (hasDerivAt_id y).const_add d.core.pulseStart
  have hU := (dY_hasDerivAt (U_smooth d ha) (d.core.pulseStart + y, eta)).comp y hshift
  have hE := (dY_hasDerivAt (E_smooth w) (d.core.pulseStart + y, eta)).comp y hshift
  have hRsmooth : ContDiff ℝ ∞ (fun t => pulseRatio d.core amp (t, eta)) :=
    (pulseRatio_contDiff d.core ha).comp (contDiff_id.prodMk contDiff_const)
  have hR := (hRsmooth.differentiable (by simp) y).hasDerivAt
  have hp := (hE.mul hR).hasDerivWithinAt (s := Icc (0 : ℝ) d.core.pulseLength)
  have hp' := hp.congr (fun t ht => U_pulse w amp eta ht.1 ht.2) (U_pulse w amp eta hy hy')
  have he := (uniqueDiffOn_Icc d.core.pulseLength_pos y ⟨hy, hy'⟩).eq_deriv _
    hU.hasDerivWithinAt hp'
  simp only [mul_one] at he
  change dY (U d amp) (d.core.pulseStart + y, eta) =
    dY (E w) (d.core.pulseStart + y, eta) * pulseRatio d.core amp (y, eta) +
      E w (d.core.pulseStart + y, eta) * deriv (fun t => pulseRatio d.core amp (t, eta)) y at he
  rw [he, E_radial_pulse w eta hy hy']
  ring

theorem shearB_pulse (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    shearB w amp (d.core.pulseStart + y, eta) = -pulseRatio d.core amp (y, eta) +
      2 * d.core.lam * (deriv (scaledPulse d.core amp eta) (d.core.lam * y) -
        pulseRatio d.core amp (y, eta)) := by
  rw [shearB, U_radial_pulse w ha eta hy hy', ← scaledPulse_deriv d.core amp eta y]
  field_simp [(E_pos w (d.core.pulseStart + y, eta)).ne'] ; ring

/-! ## Quantitative pulse jets and parameter sensitivity -/

theorem mainPulse_deriv_formula (z : ℝ) :
    deriv mainPulse z = sigma (50 * z) * (1 - sigma (z - 10)) -
      pulseRamp z * deriv sigma (z - 10) := by
  have hr : HasDerivAt pulseRamp (sigma (50 * z)) z :=
    primitive_hasDerivAt (sigma_contDiff.continuous.comp (continuous_const.mul continuous_id)) z
  have hs := (sigma_contDiff.differentiable (by simp) (z - 10)).hasDerivAt.comp z
    ((hasDerivAt_id z).sub_const 10)
  have h := hr.fun_mul ((hasDerivAt_const z (1 : ℝ)).fun_sub hs)
  change HasDerivAt mainPulse _ z at h
  rw [h.deriv]
  simp only [Function.comp_apply, id_eq]
  ring

/-- Only this upper derivative bound is used for the favorable cutoff sign. -/
theorem mainPulse_deriv_le_one {z : ℝ} (hz : 0 ≤ z) : deriv mainPulse z ≤ 1 := by
  rw [mainPulse_deriv_formula]
  have hprod := mul_le_mul (sigma_le_one (50 * z))
    (show 1 - sigma (z - 10) ≤ 1 by linarith [sigma_nonneg (z - 10)])
    (sub_nonneg.mpr (sigma_le_one (z - 10))) zero_le_one
  have hcut := mul_nonneg (PulseAmplitude.pulseRamp_nonneg hz)
    (OutgoingTail.sigma_derivative_nonneg (z - 10))
  nlinarith

noncomputable def mainFirstBound : ℝ := 1 + Classical.choose
  (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 1)

theorem mainFirstBound_pos : 0 < mainFirstBound := by
  have h := (Classical.choose_spec (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 1)).1
  dsimp [mainFirstBound]
  linarith

theorem main_first_le (z : ℝ) : |deriv mainPulse z| ≤ mainFirstBound := by
  have h := (Classical.choose_spec (LocalizedMomentRepair.smooth_compact_derivative_bound mainPulse
    mainPulse_contDiff mainPulse_hasCompactSupport 1)).2 z
  have he : |deriv mainPulse z| = |iteratedDeriv 1 mainPulse z| := by rw [iteratedDeriv_one]
  rw [he]
  dsimp [mainFirstBound]
  linarith

theorem scaledPulse_deriv_formula (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    deriv (scaledPulse c amp eta) (c.lam * y) =
      amp eta * deriv mainPulse (c.lam * y) +
        deriv (affineProfile c (parameterPolynomial eta) (amp eta)) y / c.lam := by
  have hs := scaledPulse_deriv c amp eta y
  have heq : (fun t => pulseRatio c amp (t, eta)) =
      forcing c (parameterPolynomial eta) (amp eta) :=
    funext (fun t => (forcing_eq_pulseRatio c amp eta t).symm)
  rw [heq] at hs
  have hf := forcing_jet_formula c (parameterPolynomial eta) (amp eta) 1 y
  simp only [iteratedDeriv_one, pow_one] at hf
  rw [hf] at hs
  apply mul_left_cancel₀ c.lam_pos.ne'
  calc
    _ = amp eta * c.lam * deriv mainPulse (c.lam * y) +
        deriv (affineProfile c (parameterPolynomial eta) (amp eta)) y := hs
    _ = _ := by field_simp [c.lam_pos.ne']

noncomputable def valueRepairConstant (P m : ℝ) : ℝ := 384 * correctionJetBound P m 0
noncomputable def derivativeRepairConstant (P m : ℝ) : ℝ := 384 * correctionJetBound P m 1

theorem valueRepairConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < valueRepairConstant P m := mul_pos (by norm_num) (correctionJetBound_pos hP m 0)
theorem derivativeRepairConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < derivativeRepairConstant P m := mul_pos (by norm_num) (correctionJetBound_pos hP m 1)

theorem scaledPulse_correction_bounds (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (y : ℝ) :
    |pulseRatio c amp (y, eta) - amp eta * mainPulse (c.lam * y)| ≤
        valueRepairConstant c.P c.m * c.lam ^ 2 ∧
      |deriv (scaledPulse c amp eta) (c.lam * y) - amp eta * deriv mainPulse (c.lam * y)| ≤
        derivativeRepairConstant c.P c.m * c.lam := by
  have hq : |parameterPolynomial eta| + |amp eta| ≤ 6 := by
    linarith [parameterPolynomial_bound heta]
  have hb (k : ℕ) : |iteratedDeriv k (affineProfile c (parameterPolynomial eta) (amp eta)) y| ≤
      384 * correctionJetBound c.P c.m k * c.lam ^ 2 := by
    apply (affineProfile_jet_bound c hsmall _ _ k y).trans
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (exponential_correction_quadratic c.lam_pos)
        (correctionJetBound_pos c.P_pos c.m k).le) hq
      (by positivity : 0 ≤ |parameterPolynomial eta| + |amp eta|)
      (by have hc := correctionJetBound_pos c.P_pos c.m k; positivity :
        0 ≤ correctionJetBound c.P c.m k * (64 * c.lam ^ 2))
    convert! h using 1
    ring
  constructor
  · rw [← forcing_eq_pulseRatio c amp eta y]
    simpa only [forcing, add_sub_cancel_left, iteratedDeriv_zero, valueRepairConstant] using hb 0
  · rw [scaledPulse_deriv_formula, add_sub_cancel_left, abs_div, abs_of_pos c.lam_pos]
    apply (div_le_iff₀ c.lam_pos).mpr
    simpa only [iteratedDeriv_one, derivativeRepairConstant, pow_two, mul_assoc] using hb 1

noncomputable def derivativeConstant (P m : ℝ) : ℝ :=
  2 * mainFirstBound + derivativeRepairConstant P m

theorem derivativeConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < derivativeConstant P m := by
  have hm := mainFirstBound_pos
  have hc := derivativeRepairConstant_pos hP m
  dsimp [derivativeConstant]
  positivity

theorem scaledPulse_deriv_abs_le (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (y : ℝ) :
    |deriv (scaledPulse c amp eta) (c.lam * y)| ≤ derivativeConstant c.P c.m := by
  have he := (scaledPulse_correction_bounds c hsmall amp heta hamp y).2
  have hm : |amp eta * deriv mainPulse (c.lam * y)| ≤ 2 * mainFirstBound := by
    rw [abs_mul]
    exact (mul_le_mul hamp (main_first_le _) (abs_nonneg _) (by norm_num)).trans
      (by nlinarith [mainFirstBound_pos])
  have hc := mul_le_mul_of_nonneg_left (show c.lam ≤ 1 by linarith [c.lam_lt])
    (derivativeRepairConstant_pos c.P_pos c.m).le
  have htriangle := abs_add_le (deriv (scaledPulse c amp eta) (c.lam * y) -
    amp eta * deriv mainPulse (c.lam * y)) (amp eta * deriv mainPulse (c.lam * y))
  rw [sub_add_cancel] at htriangle
  dsimp [derivativeConstant]
  nlinarith

theorem forcing_fine_abs_le (c : Parameters) (hsmall : c.lam ≤ 1 / 120) (q A y : ℝ) :
    |forcing c q A y| ≤ mainBound * |A| +
      64 * correctionJetBound c.P c.m 0 * (|q| + |A|) * c.lam ^ 2 := by
  have hc := affineProfile_jet_bound c hsmall q A 0 y
  simp only [iteratedDeriv_zero] at hc
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exponential_correction_quadratic c.lam_pos)
      (correctionJetBound_pos c.P_pos c.m 0).le) (by positivity : 0 ≤ |q| + |A|)
  have hm : |A * mainPulse (c.lam * y)| ≤ mainBound * |A| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (mainPulse_abs_le (c.lam * y)) (abs_nonneg A)]
  apply (abs_add_le _ _).trans
  change |A * mainPulse (c.lam * y)| + |affineProfile c q A y| ≤ _
  nlinarith

theorem affineLag_fine_abs_le (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    (q A : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |affineLag c q A y| ≤ 3 * mainBound * |A| +
      (prefixBound c.P c.m 0 * |q| + 192 * correctionJetBound c.P c.m 0 * (|q| + |A|)) * c.lam ^ 2
        := by
  have hB : 0 ≤ mainBound * |A| + 64 * correctionJetBound c.P c.m 0 * (|q| + |A|) * c.lam ^ 2 := by
    have hm := mainBound_pos
    have hc := correctionJetBound_pos c.P_pos c.m 0
    positivity
  have hc := (convolution_abs_le (decay_pos c) hB hy (forcing_contDiff c q A).continuous
    (fun t _ => forcing_fine_abs_le c hsmall q A t)).trans (decay_div_le_three c hB)
  have hi := initial_memory_bound c hwait hsmall q hy
  have ht := abs_add_le ((prefixCoefficient c 0 * q) * Real.exp (-decay c * y))
    (convolution (decay c) (forcing c q A) y)
  change |affineLag c q A y| ≤ _ at ht
  nlinarith

noncomputable def parameterLagConstant (P m : ℝ) : ℝ :=
  4 * prefixBound P m 0 + 960 * correctionJetBound P m 0

theorem parameterLagConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < parameterLagConstant P m := by
  have hp := prefixBound_pos hP m 0
  have hc := correctionJetBound_pos hP m 0
  dsimp [parameterLagConstant]
  positivity

/-- The parameter derivative has the small amplitude-derivative factor;
the remaining dependence is quadratically small in lambda. -/
theorem normalizedLag_parameter_fine_bound (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) (hsmall : c.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} {eta amp' : ℝ} (ha : HasDerivAt amp amp' eta)
    (heta : |eta| ≤ 1) (hamp' : |amp'| ≤ 1) {y : ℝ} (hy : 0 ≤ y) :
    |deriv (fun t => normalizedLag c amp t y) eta| ≤
      3 * mainBound * |amp'| + parameterLagConstant c.P c.m * c.lam ^ 2 := by
  rw [(normalizedLag_eta_hasDerivAt c ha hy).deriv]
  apply (affineLag_fine_abs_le c hwait hsmall _ _ hy).trans
  have hq : |1 + 3 * eta ^ 2| ≤ 4 := by
    simpa only [(parameterPolynomial_hasDerivAt eta).deriv] using
      parameterPolynomial_derivative_bound heta
  have hp := mul_le_mul_of_nonneg_left hq (prefixBound_pos c.P_pos c.m 0).le
  have hs := mul_le_mul_of_nonneg_left (show |1 + 3 * eta ^ 2| + |amp'| ≤ 5 by linarith)
    (correctionJetBound_pos c.P_pos c.m 0).le
  have hcoeff : prefixBound c.P c.m 0 * |1 + 3 * eta ^ 2| +
      192 * correctionJetBound c.P c.m 0 * (|1 + 3 * eta ^ 2| + |amp'|) ≤ parameterLagConstant c.P
        c.m := by
    dsimp [parameterLagConstant]
    nlinarith
  exact add_le_add_right (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg c.lam)) _

/-! ## The coefficient in the pulse-direction expansion -/

noncomputable def geometricSource (d : TailData) (eta : ℝ) : ℝ :=
  (1 / 2 - d.h) * eta * shapeGradient eta

noncomputable def equilibriumNumerator (d : TailData) (eta : ℝ) : ℝ :=
  d.core.lam - d.h + geometricSource d eta

noncomputable def angularEquilibrium (d : TailData) (eta : ℝ) : ℝ :=
  equilibriumNumerator d eta / (1 - d.core.lam)

noncomputable def derivativeCoefficient (d : TailData) (eta : ℝ) : ℝ :=
  d.core.lam * ((1 / 2 - d.h) + geometricSource d eta) * (1 - d.core.lam) /
    (decay d.core ^ 2 * equilibriumNumerator d eta)

theorem eta_shapeGradient_nonneg (eta : ℝ) : 0 ≤ eta * shapeGradient eta := by
  have he : eta * shapeGradient eta = 2 * eta ^ 2 / (1 + eta ^ 2) := by
    unfold shapeGradient
    ring
  rw [he]
  positivity

theorem eta_shapeGradient_bounds {eta : ℝ} (heta : |eta| ≤ 1) :
    eta ^ 2 ≤ eta * shapeGradient eta ∧ eta * shapeGradient eta ≤ 1 := by
  have he : eta * shapeGradient eta = 2 * eta ^ 2 / (1 + eta ^ 2) := by
    unfold shapeGradient
    ring
  have hs : eta ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1)).mpr heta
    nlinarith [sq_abs eta]
  rw [he]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 1 + eta ^ 2)).mpr
    nlinarith [mul_nonneg (sq_nonneg eta) (sub_nonneg.mpr hs)]
  · apply (div_le_iff₀ (by positivity : 0 < 1 + eta ^ 2)).mpr
    linarith

theorem geometricSource_nonneg (d : TailData) (eta : ℝ) : 0 ≤ geometricSource d eta := by
  have h := mul_nonneg (show 0 ≤ 1 / 2 - d.h by linarith [d.h_lt_half])
    (eta_shapeGradient_nonneg eta)
  simpa only [geometricSource, mul_assoc] using h

theorem equilibriumNumerator_pos (d : TailData) (eta : ℝ) : 0 < equilibriumNumerator d eta := by
  have hg := geometricSource_nonneg d eta
  dsimp [equilibriumNumerator]
  linarith [d.h_small, d.core.lam_pos]

theorem pulse_geometric_bounds (d : TailData) {eta : ℝ} (heta : |eta| ≤ 1) :
    (1 / 2 - d.h) + geometricSource d eta ≤ 1 ∧
      d.core.lam / 2 + (2 / 5) * eta ^ 2 ≤ equilibriumNumerator d eta := by
  obtain ⟨hg₁, hg₂⟩ := eta_shapeGradient_bounds heta
  have hD : (2 / 5 : ℝ) ≤ 1 / 2 - d.h := by linarith [d.h_small, d.core.lam_lt]
  have hc₁ := mul_le_mul_of_nonneg_left hg₁ (show 0 ≤ 1 / 2 - d.h by linarith)
  have hc₂ := mul_le_mul_of_nonneg_left hg₂ (show 0 ≤ 1 / 2 - d.h by linarith)
  have hc₃ := mul_le_mul_of_nonneg_right hD (sq_nonneg eta)
  dsimp [geometricSource, equilibriumNumerator] at *
  constructor <;> nlinarith [d.h_pos, d.h_small]

theorem derivativeCoefficient_nonneg (d : TailData) (eta : ℝ) :
    0 ≤ derivativeCoefficient d eta := by
  have hg := geometricSource_nonneg d eta
  have hA := (equilibriumNumerator_pos d eta).le
  have hD : 0 ≤ 1 / 2 - d.h := by linarith [d.h_lt_half]
  have hr : 0 ≤ 1 - d.core.lam := by linarith [d.core.lam_lt]
  have hl := d.core.lam_pos.le
  dsimp [derivativeCoefficient]
  positivity

/-- A concrete version of `C_d <= 2+o(1)`, uniform in the parameter. -/
theorem derivativeCoefficient_le (d : TailData)
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000) (eta : ℝ) :
    derivativeCoefficient d eta ≤ 2001 / 1000 := by
  have hb : (49999 / 100000 : ℝ) ≤ decay d.core := by dsimp [decay]; linarith
  have hb₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 49999 / 100000) hb 2
  have hbase : (1 / 2 : ℝ) ≤ (2001 / 1000) * decay d.core ^ 2 * (99999 / 100000) := by
    nlinarith
  have hg := geometricSource_nonneg d eta
  have hD : 0 ≤ 1 / 2 - d.h := by linarith [d.h_lt_half]
  have hA : (99999 / 100000) * d.core.lam + geometricSource d eta ≤ equilibriumNumerator d eta := by
    dsimp [equilibriumNumerator]
    linarith
  have hnum : d.core.lam * ((1 / 2 - d.h) + geometricSource d eta) * (1 - d.core.lam) ≤
      d.core.lam * (1 / 2 + geometricSource d eta) := by
    have hm := mul_le_mul_of_nonneg_left (show 1 - d.core.lam ≤ 1 by linarith [d.core.lam_pos])
      (mul_nonneg d.core.lam_pos.le (add_nonneg hD hg))
    have hh' := mul_le_mul_of_nonneg_left d.h_pos.le d.core.lam_pos.le
    nlinarith
  have hbase' := mul_le_mul_of_nonneg_right hbase d.core.lam_pos.le
  have hc : d.core.lam ≤ (2001 / 1000) * decay d.core ^ 2 := by nlinarith [d.core.lam_pos]
  have hc' := mul_le_mul_of_nonneg_right hc hg
  have hA' := mul_le_mul_of_nonneg_left hA
    (show 0 ≤ (2001 / 1000) * decay d.core ^ 2 by positivity)
  unfold derivativeCoefficient
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos (decay_pos d.core)) (equilibriumNumerator_pos d
    eta))).mpr
  nlinarith

noncomputable def mainDirection (d : TailData) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  ((1 - d.core.lam) / decay d.core) * pulseRatio d.core amp (y, eta) -
    derivativeCoefficient d eta * deriv (scaledPulse d.core amp eta) (d.core.lam * y)

private theorem direction_identity_algebra {β C A r : ℝ} (lam R Z : ℝ)
    (hβ : β ≠ 0) (hA : A ≠ 0) (hr : r ≠ 0) (hrel : A = C - β) :
    -R + C * (R / β - lam * Z / β ^ 2) =
      A / r * (r / β * R - (lam * C * r / (β ^ 2 * A)) * Z) := by
  rw [hrel] at hA ⊢
  field_simp ; ring

theorem mainDirection_identity (d : TailData) (eta R Z : ℝ) :
    -R + ((1 / 2 - d.h) + geometricSource d eta) *
      (R / decay d.core - d.core.lam * Z / decay d.core ^ 2) =
    angularEquilibrium d eta * (((1 - d.core.lam) / decay d.core) * R -
      derivativeCoefficient d eta * Z) := by
  have hr : 1 - d.core.lam ≠ 0 := by linarith [d.core.lam_lt]
  apply direction_identity_algebra d.core.lam R Z (decay_pos d.core).ne'
    (equilibriumNumerator_pos d eta).ne' hr
  dsimp [equilibriumNumerator, decay]
  ring

/-- The actual mass expansion is inserted into the actual axial history. -/
theorem Ns_pulse_expansion (w : ResetWitness d K) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) (eta : ℝ) {y : ℝ}
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    Ns w amp (d.core.pulseStart + y, eta) / E w (d.core.pulseStart + y, eta) =
      angularEquilibrium d eta * mainDirection d amp eta y +
        ((1 / 2 - d.h) + geometricSource d eta) * fullError d.core amp eta y -
        (1 / 2 - d.h) * eta * deriv (fun t => normalizedLag d.core amp t y) eta +
        axialHistoryError w amp eta y := by
  rw [Ns_pulse_identity w ha eta hy hy']
  unfold mainDirection
  rw [← mainDirection_identity]
  unfold fullError geometricSource
  ring

/-! ## Strict numerical margins, stable under quantified errors -/

theorem first_quadratic_margin (R : ℝ) :
    -2 * R ^ 2 + (241 / 100) * R ≤ 73 / 100 := by
  nlinarith [sq_nonneg (R - 241 / 400)]

theorem second_quadratic_margin (R : ℝ) :
    -(7 / 2) * R ^ 2 + (241 / 50) * R ≤ 167 / 100 := by
  nlinarith [sq_nonneg (R - 241 / 350)]

theorem ideal_cross_bound {R C Z : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hC' : C ≤ 2001 / 1000) (hZ : Z ≤ 6 / 5) :
    -R * (2 * R - C * Z) ≤ -2 * R ^ 2 + (241 / 100) * R := by
  have hc := mul_le_mul_of_nonneg_left hZ hC
  have hcz : C * Z ≤ 241 / 100 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hcz hR
  nlinarith

noncomputable def coneErrorBudget (F M eps lam : ℝ) : ℝ :=
  2 * eps * (M + F + 1) + eps * (2 * F + 1) / 2 + 2 * lam * (M + 1) ^ 2

/-- A completely numerical perturbation lemma.  The actual profile
estimates below supply both errors and the small budget. -/
theorem perturbed_cone_margins {lam R C Z b v eps F M : ℝ}
    (hlam : 0 ≤ lam) (hF : 0 ≤ F) (hM : 0 ≤ M) (heps : 0 ≤ eps) (heps' : eps ≤ 1)
    (hR : 0 ≤ R) (hR' : R ≤ F) (hC : 0 ≤ C) (hC' : C ≤ 2001 / 1000)
    (hZ : Z ≤ 6 / 5) (hmain : |2 * R - C * Z| ≤ M)
    (hb : |b + R| ≤ eps) (hv : |v - (2 * R - C * Z)| ≤ eps)
    (hbudget : coneErrorBudget F M eps lam ≤ 1 / 100) :
    b * v ≤ 74 / 100 ∧
      2 * b * v + b ^ 2 / (2 + 2 * lam) + 2 * lam * v ^ 2 ≤ 168 / 100 := by
  let v₀ := 2 * R - C * Z
  have hvabs : |v| ≤ M + 1 := by
    have h := abs_add_le (v - v₀) v₀
    rw [sub_add_cancel] at h
    change |v - v₀| ≤ eps at hv
    change |v₀| ≤ M at hmain
    linarith
  have hbabs : |b| ≤ F + 1 := by
    have h := abs_sub (b + R) R
    rw [add_sub_cancel_right, abs_of_nonneg hR] at h
    linarith
  have hcross : |b * v + R * v₀| ≤ eps * (M + F + 1) := by
    have he : b * v + R * v₀ = (b + R) * v - R * (v - v₀) := by ring
    rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hR]
    have h₁ := mul_le_mul hb hvabs (abs_nonneg v) heps
    have h₂ := mul_le_mul hR' hv (abs_nonneg _) hF
    nlinarith
  have hdiff : |b - R| ≤ 2 * F + 1 := by
    have h := abs_sub b R
    rw [abs_of_nonneg hR] at h
    linarith
  have hsq : b ^ 2 ≤ R ^ 2 + eps * (2 * F + 1) := by
    have hprod := mul_le_mul hb hdiff (abs_nonneg (b - R)) heps
    rw [← abs_mul] at hprod
    have he : (b + R) * (b - R) = b ^ 2 - R ^ 2 := by ring
    rw [he] at hprod
    have h := (abs_le.mp hprod).2
    linarith
  have ha : (2 : ℝ) ≤ 2 + 2 * lam := by linarith
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg b) (by norm_num : (0 : ℝ) < 2) ha
  have hvsq : v ^ 2 ≤ (M + 1) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg v) (by linarith : 0 ≤ M + 1)).mpr hvabs
    simpa only [sq_abs] using h
  have hvsq' := mul_le_mul_of_nonneg_left hvsq (show 0 ≤ 2 * lam by linarith)
  have hideal := ideal_cross_bound hR hC hC' hZ
  change -R * v₀ ≤ -2 * R ^ 2 + (241 / 100) * R at hideal
  have hcross' := (abs_le.mp hcross).2
  have hnonneg₁ : 0 ≤ eps * (2 * F + 1) / 2 := by positivity
  have hnonneg₂ : 0 ≤ 2 * lam * (M + 1) ^ 2 := by positivity
  dsimp [coneErrorBudget] at hbudget
  have hcrossBound : b * v ≤ -2 * R ^ 2 + (241 / 100) * R + eps * (M + F + 1) := by
    calc
      _ = (b * v + R * v₀) + (-R * v₀) := by ring
      _ ≤ eps * (M + F + 1) + (-2 * R ^ 2 + (241 / 100) * R) := add_le_add hcross' hideal
      _ = _ := by ring
  constructor
  · have herr : eps * (M + F + 1) ≤ 1 / 200 := by
      nlinarith only [hbudget, hnonneg₁, hnonneg₂]
    calc
      _ ≤ -2 * R ^ 2 + (241 / 100) * R + eps * (M + F + 1) := hcrossBound
      _ ≤ 73 / 100 + 1 / 200 := add_le_add (first_quadratic_margin R) herr
      _ ≤ _ := by norm_num
  · have hdiv' : b ^ 2 / (2 + 2 * lam) ≤ R ^ 2 / 2 + eps * (2 * F + 1) / 2 := by
      apply hdiv.trans
      linarith only [hsq]
    have hsum := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hcrossBound (by norm_num : (0 : ℝ) ≤ 2)) hdiv') hvsq'
    calc
      _ ≤ 2 * (-2 * R ^ 2 + (241 / 100) * R + eps * (M + F + 1)) +
          (R ^ 2 / 2 + eps * (2 * F + 1) / 2) + 2 * lam * (M + 1) ^ 2 := by
            convert! hsum using 1
            ring
      _ = (-(7 / 2) * R ^ 2 + (241 / 50) * R) +
          (2 * eps * (M + F + 1) + eps * (2 * F + 1) / 2 + 2 * lam * (M + 1) ^ 2) := by ring
      _ ≤ 167 / 100 + 1 / 100 := add_le_add (second_quadratic_margin R) hbudget
      _ = _ := by norm_num

theorem perturbed_true_cone {lam R C Z b v eps F M : ℝ}
    (hlam : 0 < lam) (hF : 0 ≤ F) (hM : 0 ≤ M) (heps : 0 ≤ eps) (heps' : eps ≤ 1)
    (hR : 0 ≤ R) (hR' : R ≤ F) (hC : 0 ≤ C) (hC' : C ≤ 2001 / 1000)
    (hZ : Z ≤ 6 / 5) (hmain : |2 * R - C * Z| ≤ M)
    (hb : |b + R| ≤ eps) (hv : |v - (2 * R - C * Z)| ≤ eps)
    (hbudget : coneErrorBudget F M eps lam ≤ 1 / 100) :
    0 < (2 + 2 * lam) - b * v ∧
      2 * b * v + b ^ 2 / (2 + 2 * lam) + ((2 + 2 * lam) - 2) * v ^ 2 < 2 ∧
      2 < (2 + 2 * lam) * (1 + (b / (2 + 2 * lam)) ^ 2) := by
  have h := perturbed_cone_margins hlam.le hF hM heps heps' hR hR' hC hC' hZ hmain hb hv hbudget
  have hsq := sq_nonneg (b / (2 + 2 * lam))
  have hprod := mul_nonneg (show 0 ≤ 2 + 2 * lam by linarith) hsq
  constructor
  · linarith [h.1]
  constructor
  · nlinarith [h.2]
  · nlinarith

/-! ## The axial history error is derived from actual moments -/

theorem W_pulse_error_bound (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |1 - W d amp (d.core.pulseStart + y, eta)| ≤
      4 * averageConstant d.core.P d.core.m * E w (d.core.pulseStart + y, eta) := by
  have hid : 1 - W d amp (d.core.pulseStart + y, eta) = E w (d.core.pulseStart + y, eta) *
      ((2 * (1 / 2 - d.h) * eta - (1 - eta ^ 2) * shapeGradient eta) * normalizedLag d.core amp eta
        y +
        (1 - eta ^ 2) * deriv (fun t => normalizedLag d.core amp t y) eta) := by
    rw [W_formula d ha, Ubar_pulse w amp eta hy', Ubar_parameter_pulse w ha eta hy hy']
    dsimp only [Prod.snd, StressAlgebra.axialExponent, StressAlgebra.coordinateFactor]
    ring
  have hdata := pulse_data_bounds d.core hwait hsmall
    ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp' hy
  obtain ⟨hcoef, hd, _⟩ := geometric_coefficient_bounds d.h_pos.le d.h_lt_half.le heta
  have h₁ := mul_le_mul hcoef hdata.2.1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  have h₂ := mul_le_mul hd hdata.2.2 (abs_nonneg _) zero_le_one
  rw [← abs_mul] at h₁ h₂
  have hs := abs_add_le
    ((2 * (1 / 2 - d.h) * eta - (1 - eta ^ 2) * shapeGradient eta) * normalizedLag d.core amp eta y)
    ((1 - eta ^ 2) * deriv (fun t => normalizedLag d.core amp t y) eta)
  rw [hid, abs_mul, abs_of_pos (E_pos w _)]
  have hm : |(2 * (1 / 2 - d.h) * eta - (1 - eta ^ 2) * shapeGradient eta) * normalizedLag d.core
    amp eta y +
      (1 - eta ^ 2) * deriv (fun t => normalizedLag d.core amp t y) eta| ≤ 4 * averageConstant
        d.core.P d.core.m := by
    linarith
  convert! mul_le_mul_of_nonneg_left hm (E_pos w _).le using 1
  ring

private theorem normalized_axial_bound {E u R a b c S Seta P Peta M F Ks Kp Kpe : ℝ}
    (hE : 0 ≤ E) (hu : |u| ≤ M) (hR : |R| ≤ F)
    (ha : |a| ≤ 2) (hb : |b| ≤ 1) (hc : |c| ≤ 4)
    (hS : |S| ≤ Ks) (hSe : |Seta| ≤ Ks) (hP : |P| ≤ Kp) (hPe : |Peta| ≤ Kpe) :
    |E * (u * R + a * S - b * Seta + c * P - b * Peta)| ≤ E * (M * F + 3 * Ks + 4 * Kp + Kpe) := by
  have huR := mul_le_mul hu hR (abs_nonneg R) ((abs_nonneg u).trans hu)
  have haS := mul_le_mul ha hS (abs_nonneg S) (by norm_num : (0 : ℝ) ≤ 2)
  have hbSe := mul_le_mul hb hSe (abs_nonneg Seta) zero_le_one
  have hcP := mul_le_mul hc hP (abs_nonneg P) (by norm_num : (0 : ℝ) ≤ 4)
  have hbPe := mul_le_mul hb hPe (abs_nonneg Peta) zero_le_one
  rw [← abs_mul] at huR haS hbSe hcP hbPe
  have hs : |u * R + a * S - b * Seta + c * P - b * Peta| ≤ M * F + 3 * Ks + 4 * Kp + Kpe := by
    linarith [abs_add_le (u * R) (a * S), abs_sub (u * R + a * S) (b * Seta),
      abs_add_le (u * R + a * S - b * Seta) (c * P),
      abs_sub (u * R + a * S - b * Seta + c * P) (b * Peta)]
  rw [abs_mul, abs_of_nonneg hE]
  exact mul_le_mul_of_nonneg_left hs hE

noncomputable def axialErrorConstant (P m : ℝ) : ℝ := energyConstant P m *
  (24 * averageConstant P m * forceConstant P m +
    3 * PulseEnergyHistory.historyConstant P m * Real.exp 26 + 4 *
      FuturePressureBounds.envelopeConstant)

theorem axialErrorConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < axialErrorConstant P m := by
  have he := energyConstant_pos hP m
  have hm := averageConstant_pos hP m
  have hf := forceConstant_pos hP m
  have hh := PulseEnergyHistory.historyConstant_pos P m
  have hp := FuturePressureBounds.envelopeConstant_pos
  dsimp [axialErrorConstant]
  positivity

theorem axialHistoryError_bound (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |axialHistoryError w amp eta y| ≤ axialErrorConstant d.core.P d.core.m * d.core.lam ^ 29 := by
  let p := (d.core.pulseStart + y, eta)
  have hE : 0 < E w p := E_pos w p
  have hX : 0 < X p := X_pos p
  have hEsq : 0 < E w p ^ 2 := sq_pos_of_pos hE
  have hden : 0 < X p * E w p ^ 2 := mul_pos hX hEsq
  have hdata := pulse_data_bounds d.core hwait hsmall
    ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp' hy
  have hW := W_pulse_error_bound w hwait hsmall ha heta hamp hamp' hy hy'
  have hS := PulseEnergyHistory.pulse_history_bounds w ha hwait hsmall heta hamp hamp' hy hy'
  have hP := pulse_pressure_bounds w heta hy hy'
  have hcoef := geometric_coefficient_bounds d.h_pos.le d.h_lt_half.le heta
  have ha' : |4 * d.h * eta| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos d.h_pos]
    have h := mul_le_mul d.h_lt_half.le heta (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  have hc' : |4 * (1 / 2 + d.h) * eta| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by linarith [d.h_pos] : 0 < 1 / 2 + d.h)]
    have h := mul_le_mul (show 1 / 2 + d.h ≤ 1 by linarith [d.h_lt_half]) heta (abs_nonneg eta)
      zero_le_one
    nlinarith
  have hw' : |(1 - W d amp p) / E w p| ≤ 4 * averageConstant d.core.P d.core.m := by
    rw [abs_div, abs_of_pos hE]
    exact (div_le_iff₀ hE).mpr hW
  have hs' : |S w amp p / (X p * E w p ^ 2)| ≤
      PulseEnergyHistory.historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam := by
    rw [abs_div, abs_of_pos hden]
    exact hS.1
  have hse' : |dEta (S w amp) p / (X p * E w p ^ 2)| ≤
      PulseEnergyHistory.historyConstant d.core.P d.core.m * Real.exp 26 / d.core.lam := by
    rw [abs_div, abs_of_pos hden]
    exact hS.2
  have hp' : |Pi w p / E w p ^ 2| ≤ FuturePressureBounds.envelopeConstant / 2 := by
    rw [abs_div, abs_of_pos hEsq]
    exact (div_le_iff₀ hEsq).mpr hP.1
  have hpe' : |dEta (Pi w) p / E w p ^ 2| ≤ 2 * FuturePressureBounds.envelopeConstant := by
    rw [abs_div, abs_of_pos hEsq]
    apply (div_le_iff₀ hEsq).mpr
    apply hP.2.trans
    have h := mul_le_mul_of_nonneg_left heta
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) FuturePressureBounds.envelopeConstant_pos.le)
    have h' := mul_le_mul_of_nonneg_right h hEsq.le
    simpa only [mul_one] using h'
  have hid : axialHistoryError w amp eta y = E w p *
      (((1 - W d amp p) / E w p) * pulseRatio d.core amp (y, eta) +
        (4 * d.h * eta) * (S w amp p / (X p * E w p ^ 2)) -
        (1 - eta ^ 2) * (dEta (S w amp) p / (X p * E w p ^ 2)) +
        (4 * (1 / 2 + d.h) * eta) * (Pi w p / E w p ^ 2) -
        (1 - eta ^ 2) * (dEta (Pi w) p / E w p ^ 2)) := by
    unfold axialHistoryError
    dsimp only [p] at *
    field_simp [hE.ne', hX.ne'] ; ring
  have hb := normalized_axial_bound hE.le hw' hdata.1 ha' hcoef.2.1 hc' hs' hse' hp' hpe'
  rw [← hid] at hb
  let A := 24 * averageConstant d.core.P d.core.m * forceConstant d.core.P d.core.m +
    4 * FuturePressureBounds.envelopeConstant
  let B := 3 * PulseEnergyHistory.historyConstant d.core.P d.core.m * Real.exp 26
  have hA : 0 ≤ A := by
    have hm := averageConstant_pos d.core.P_pos d.core.m
    have hf := forceConstant_pos d.core.P_pos d.core.m
    have hp := FuturePressureBounds.envelopeConstant_pos
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    have hh := PulseEnergyHistory.historyConstant_pos d.core.P d.core.m
    dsimp [B]
    positivity
  have hb' : |axialHistoryError w amp eta y| ≤ E w p * (A + B / d.core.lam) := by
    convert! hb using 1
    dsimp [A, B]
    ring
  have hAB : A + B / d.core.lam ≤ (A + B) / d.core.lam := by
    apply (le_div_iff₀ d.core.lam_pos).mpr
    have hl : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
    have hx := mul_le_mul_of_nonneg_left hl hA
    rw [add_mul, div_mul_cancel₀ _ d.core.lam_pos.ne']
    simpa only [mul_one] using add_le_add_left hx B
  have he : E w p ≤ energyConstant d.core.P d.core.m * d.core.lam ^ 30 := by
    rw [E_before w eta (by dsimp [Parameters.endpoint]; linarith)]
    exact pulse_angular_small d.core hwait eta hy
  calc
    _ ≤ E w p * (A + B) / d.core.lam := by
      simpa only [mul_div_assoc] using hb'.trans (mul_le_mul_of_nonneg_left hAB hE.le)
    _ ≤ (energyConstant d.core.P d.core.m * d.core.lam ^ 30) * (A + B) / d.core.lam := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (add_nonneg hA hB))
        d.core.lam_pos.le
    _ = axialErrorConstant d.core.P d.core.m * d.core.lam ^ 29 := by
      have hc : axialErrorConstant d.core.P d.core.m = energyConstant d.core.P d.core.m * (A + B)
        := by
        dsimp [axialErrorConstant, A, B]
        ring
      rw [hc]
      field_simp [d.core.lam_pos.ne']

/-! ## Division by the angular lag near the equator -/

theorem denominator_bounds (d : TailData) {eta Q : ℝ} (heta : |eta| ≤ 1)
    (hQ : equilibriumNumerator d eta / 2 ≤ Q) :
    0 < Q ∧ 1 / Q ≤ 4 / d.core.lam ∧ |eta| / Q ≤ 4 / Real.sqrt d.core.lam := by
  have hA := (pulse_geometric_bounds d heta).2
  have hq : d.core.lam / 4 + eta ^ 2 / 5 ≤ Q := by linarith
  have hQpos : 0 < Q := by nlinarith [d.core.lam_pos, sq_nonneg eta]
  have hs := Real.sqrt_pos.mpr d.core.lam_pos
  have hs₂ := Real.sq_sqrt d.core.lam_pos.le
  refine ⟨hQpos, ?_, ?_⟩
  · apply (div_le_div_iff₀ hQpos d.core.lam_pos).mpr
    nlinarith [sq_nonneg eta]
  · apply (div_le_div_iff₀ hQpos hs).mpr
    nlinarith [sq_nonneg (Real.sqrt d.core.lam - |eta| / 2), sq_abs eta]

noncomputable def mainDirectionBound (P m : ℝ) : ℝ :=
  18 * forceConstant P m + 3 * derivativeConstant P m

theorem mainDirectionBound_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < mainDirectionBound P m := by
  have hf := forceConstant_pos hP m
  have hd := derivativeConstant_pos hP m
  dsimp [mainDirectionBound]
  positivity

theorem mainDirection_abs_le (d : TailData)
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    {amp : ℝ → ℝ} {eta : ℝ} (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (y : ℝ) :
    |mainDirection d amp eta y| ≤ mainDirectionBound d.core.P d.core.m := by
  have hc := derivativeCoefficient_le d hsmall hh eta
  have hc₀ := derivativeCoefficient_nonneg d eta
  have hR : |pulseRatio d.core amp (y, eta)| ≤ 6 * forceConstant d.core.P d.core.m := by
    rw [← forcing_eq_pulseRatio]
    apply (forcing_abs_le d.core (by linarith) _ _ y).trans
    have hsum : |parameterPolynomial eta| + |amp eta| ≤ 6 := by linarith [parameterPolynomial_bound
      heta]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hsum (forceConstant_pos d.core.P_pos d.core.m).le
  have hZ := scaledPulse_deriv_abs_le d.core (by linarith) amp heta hamp y
  have hr₀ : 0 ≤ (1 - d.core.lam) / decay d.core :=
    div_nonneg (by linarith [d.core.lam_lt]) (decay_pos d.core).le
  have hr : (1 - d.core.lam) / decay d.core ≤ 3 := by
    apply (div_le_iff₀ (decay_pos d.core)).mpr
    dsimp [decay]
    linarith [d.core.lam_lt]
  have h₁ := mul_le_mul hr hR (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  have h₂ := mul_le_mul (hc.trans (by norm_num : (2001 / 1000 : ℝ) ≤ 3)) hZ
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  rw [mainDirection]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg hr₀, abs_of_nonneg hc₀]
  dsimp [mainDirectionBound]
  nlinarith

private theorem quotient_remainder_bound
    {N Q q B C D eta e m H eQ eE eM eH BM I J : ℝ}
    (hQ : 0 < Q) (hid : N = q * B + C * e - D * eta * m + H)
    (hC : |C| ≤ 1) (hD : |D| ≤ 1) (hq : |Q - q| ≤ eQ)
    (he : |e| ≤ eE) (hm : |m| ≤ eM) (hH : |H| ≤ eH) (hB : |B| ≤ BM)
    (hI : 1 / Q ≤ I) (hJ : |eta| / Q ≤ J) :
    |N / Q - B| ≤ I * (eQ * BM + eE + eH) + J * eM := by
  have hq' : |q - Q| ≤ eQ := by simpa only [abs_sub_comm] using hq
  have ht₁ := mul_le_mul hq' hB (abs_nonneg B) ((abs_nonneg _).trans hq')
  have ht₂ := mul_le_mul hC he (abs_nonneg e) zero_le_one
  have hDeta : |D * eta| ≤ |eta| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (abs_nonneg eta)
  have ht₃ := mul_le_mul hDeta hm (abs_nonneg m) (abs_nonneg eta)
  rw [← abs_mul] at ht₁ ht₂ ht₃
  have hs : |(q - Q) * B + C * e + H - D * eta * m| ≤
      eQ * BM + eE + eH + |eta| * eM := by
    linarith [abs_add_le ((q - Q) * B) (C * e), abs_add_le ((q - Q) * B + C * e) H,
      abs_sub ((q - Q) * B + C * e + H) (D * eta * m)]
  have heq : N / Q - B = ((q - Q) * B + C * e + H - D * eta * m) / Q := by
    rw [hid]
    field_simp ; ring
  rw [heq, abs_div, abs_of_pos hQ]
  have hA : 0 ≤ eQ * BM + eE + eH := by
    have heQ := (abs_nonneg _).trans hq
    have heB := (abs_nonneg _).trans hB
    have heE := (abs_nonneg _).trans he
    have heH := (abs_nonneg _).trans hH
    positivity
  calc
    _ ≤ (eQ * BM + eE + eH + |eta| * eM) / Q := div_le_div_of_nonneg_right hs hQ.le
    _ = (eQ * BM + eE + eH) * (1 / Q) + eM * (|eta| / Q) := by ring
    _ ≤ (eQ * BM + eE + eH) * I + eM * J := add_le_add
      (mul_le_mul_of_nonneg_left hI hA)
      (mul_le_mul_of_nonneg_left hJ ((abs_nonneg _).trans hm))
    _ = _ := by ring

/-- A quantified division step retaining every error term.  Its two
angular-lag hypotheses are supplied by the shaped-wait estimate. -/
theorem directionRatio_error_bound (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y Cq : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength)
    (hQlow : equilibriumNumerator d eta / 2 ≤ Qs w amp (d.core.pulseStart + y, eta))
    (hQerr : |Qs w amp (d.core.pulseStart + y, eta) - angularEquilibrium d eta| ≤ Cq * d.core.lam ^
      28) :
    |directionRatio w amp (d.core.pulseStart + y, eta) - mainDirection d amp eta y| ≤
      (4 / d.core.lam) * (Cq * d.core.lam ^ 28 * mainDirectionBound d.core.P d.core.m +
        fullLagBound d.core.P d.core.m * d.core.lam ^ 2 + axialErrorConstant d.core.P d.core.m *
          d.core.lam ^ 29) +
      (4 / Real.sqrt d.core.lam) * (3 * mainBound * |deriv amp eta| +
        parameterLagConstant d.core.P d.core.m * d.core.lam ^ 2) := by
  have hden := denominator_bounds d heta hQlow
  have hdata := fullError_bounds_of_amplitude_bounds d.core hwait (by linarith)
    ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp hamp' hy
  have hmp := normalizedLag_parameter_fine_bound d.core hwait (by linarith)
    ((ha.differentiable (by simp) eta).hasDerivAt) heta hamp' hy
  have hH := axialHistoryError_bound w hwait (by linarith) ha heta hamp hamp' hy hy'
  have hB := mainDirection_abs_le d hsmall hh heta hamp y
  have hC : |(1 / 2 - d.h) + geometricSource d eta| ≤ 1 := by
    rw [abs_of_nonneg (by have hg := geometricSource_nonneg d eta; linarith [d.h_lt_half])]
    exact (pulse_geometric_bounds d heta).1
  have hD : |1 / 2 - d.h| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [d.h_lt_half])]
    linarith [d.h_pos]
  have hb := quotient_remainder_bound hden.1 (Ns_pulse_expansion w ha eta hy hy')
    hC hD hQerr hdata.1 hmp hH hB hden.2.1 hden.2.2
  simpa only [directionRatio, div_div] using hb

noncomputable def mainRatio (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  amp eta * mainPulse (c.lam * y)

noncomputable def mainSlope (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  amp eta * deriv mainPulse (c.lam * y)

noncomputable def idealDirection (d : TailData) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  2 * mainRatio d.core amp eta y - derivativeCoefficient d eta * mainSlope d.core amp eta y

noncomputable def mainRatioBound : ℝ := 2 * mainBound
noncomputable def idealDirectionBound : ℝ := 4 * mainBound + 6 * mainFirstBound

theorem mainRatioBound_pos : 0 < mainRatioBound := mul_pos (by norm_num) mainBound_pos
theorem idealDirectionBound_pos : 0 < idealDirectionBound := by
  have h₁ := mainBound_pos
  have h₂ := mainFirstBound_pos
  dsimp [idealDirectionBound]
  positivity

theorem main_profile_bounds (d : TailData)
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    {amp : ℝ → ℝ} {eta y : ℝ} (hamp₀ : 0 ≤ amp eta) (hamp : |amp eta| ≤ 6 / 5) (hy : 0 ≤ y) :
    0 ≤ mainRatio d.core amp eta y ∧ mainRatio d.core amp eta y ≤ mainRatioBound ∧
      mainSlope d.core amp eta y ≤ 6 / 5 ∧ |idealDirection d amp eta y| ≤ idealDirectionBound := by
  have hR₀ : 0 ≤ mainRatio d.core amp eta y := mul_nonneg hamp₀
    (PulseAmplitude.mainPulse_nonneg (mul_nonneg d.core.lam_pos.le hy))
  have hR : |mainRatio d.core amp eta y| ≤ mainRatioBound := by
    rw [mainRatio, abs_mul]
    have h := mul_le_mul hamp (mainPulse_abs_le (d.core.lam * y)) (abs_nonneg _) (by norm_num : (0
      : ℝ) ≤ 6 / 5)
    dsimp [mainRatioBound]
    nlinarith [mainBound_pos]
  have hZ : |mainSlope d.core amp eta y| ≤ 2 * mainFirstBound := by
    rw [mainSlope, abs_mul]
    have h := mul_le_mul hamp (main_first_le (d.core.lam * y)) (abs_nonneg _) (by norm_num : (0 :
      ℝ) ≤ 6 / 5)
    nlinarith [mainFirstBound_pos]
  have hZup := mul_le_mul_of_nonneg_left
    (mainPulse_deriv_le_one (mul_nonneg d.core.lam_pos.le hy)) hamp₀
  have hCd : |derivativeCoefficient d eta| ≤ 3 := by
    rw [abs_of_nonneg (derivativeCoefficient_nonneg d eta)]
    exact (derivativeCoefficient_le d hsmall hh eta).trans (by norm_num)
  refine ⟨hR₀, (abs_le.mp hR).2, ?_, ?_⟩
  · dsimp [mainSlope]
    have h := (abs_le.mp hamp).2
    linarith
  · have h₂ := mul_le_mul hCd hZ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    rw [idealDirection]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
    dsimp [idealDirectionBound, mainRatioBound] at *
    nlinarith

theorem pulseRatio_abs_le (c : Parameters) (hsmall : c.lam ≤ 1 / 120)
    (amp : ℝ → ℝ) {eta : ℝ} (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (y : ℝ) :
    |pulseRatio c amp (y, eta)| ≤ 6 * forceConstant c.P c.m := by
  rw [← forcing_eq_pulseRatio]
  apply (forcing_abs_le c hsmall _ _ y).trans
  have hsum : |parameterPolynomial eta| + |amp eta| ≤ 6 := by linarith [parameterPolynomial_bound
    heta]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsum (forceConstant_pos c.P_pos c.m).le

noncomputable def shearErrorConstant (P m : ℝ) : ℝ :=
  valueRepairConstant P m + 2 * derivativeConstant P m + 12 * forceConstant P m

noncomputable def directionMainErrorConstant (P m : ℝ) : ℝ :=
  18 * forceConstant P m + 2 * valueRepairConstant P m + 3 * derivativeRepairConstant P m

theorem shearErrorConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < shearErrorConstant P m := by
  have hv := valueRepairConstant_pos hP m
  have hd := derivativeConstant_pos hP m
  have hf := forceConstant_pos hP m
  dsimp [shearErrorConstant]
  positivity

theorem directionMainErrorConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < directionMainErrorConstant P m := by
  have hv := valueRepairConstant_pos hP m
  have hd := derivativeRepairConstant_pos hP m
  have hf := forceConstant_pos hP m
  dsimp [directionMainErrorConstant]
  positivity

theorem shearB_main_error (w : ResetWitness d K) (hsmall : d.core.lam ≤ 1 / 120)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |shearB w amp (d.core.pulseStart + y, eta) + mainRatio d.core amp eta y| ≤
      shearErrorConstant d.core.P d.core.m * d.core.lam := by
  have hR := pulseRatio_abs_le d.core hsmall amp heta hamp y
  have hZ := scaledPulse_deriv_abs_le d.core hsmall amp heta hamp y
  have he := (scaledPulse_correction_bounds d.core hsmall amp heta hamp y).1
  have hpow : d.core.lam ^ 2 ≤ d.core.lam := by nlinarith [d.core.lam_pos, d.core.lam_lt]
  have hscale := mul_le_mul_of_nonneg_left hpow (valueRepairConstant_pos d.core.P_pos d.core.m).le
  have hid : shearB w amp (d.core.pulseStart + y, eta) + mainRatio d.core amp eta y =
      -(pulseRatio d.core amp (y, eta) - mainRatio d.core amp eta y) + 2 * d.core.lam *
        (deriv (scaledPulse d.core amp eta) (d.core.lam * y) - pulseRatio d.core amp (y, eta)) := by
    rw [shearB_pulse w ha eta hy hy']
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_neg, abs_mul, abs_of_nonneg (show 0 ≤ 2 * d.core.lam by linarith [d.core.lam_pos])]
  have hdiff := (abs_sub (deriv (scaledPulse d.core amp eta) (d.core.lam * y))
    (pulseRatio d.core amp (y, eta))).trans (add_le_add hZ hR)
  have hm := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 2 * d.core.lam by linarith [d.core.lam_pos])
  dsimp only [mainRatio] at *
  dsimp [shearErrorConstant]
  nlinarith

theorem mainDirection_ideal_error (d : TailData)
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    {amp : ℝ → ℝ} {eta : ℝ} (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (y : ℝ) :
    |mainDirection d amp eta y - idealDirection d amp eta y| ≤
      directionMainErrorConstant d.core.P d.core.m * d.core.lam := by
  have hR := pulseRatio_abs_le d.core (by linarith) amp heta hamp y
  have hc := scaledPulse_correction_bounds d.core (by linarith) amp heta hamp y
  have hCd : |derivativeCoefficient d eta| ≤ 3 := by
    rw [abs_of_nonneg (derivativeCoefficient_nonneg d eta)]
    exact (derivativeCoefficient_le d hsmall hh eta).trans (by norm_num)
  have hratio : |d.core.lam / decay d.core| ≤ 3 * d.core.lam := by
    rw [abs_of_pos (div_pos d.core.lam_pos (decay_pos d.core))]
    exact decay_div_le_three d.core d.core.lam_pos.le
  have hid : mainDirection d amp eta y - idealDirection d amp eta y =
      (d.core.lam / decay d.core) * pulseRatio d.core amp (y, eta) +
        2 * (pulseRatio d.core amp (y, eta) - mainRatio d.core amp eta y) -
        derivativeCoefficient d eta *
          (deriv (scaledPulse d.core amp eta) (d.core.lam * y) - mainSlope d.core amp eta y) := by
    unfold mainDirection idealDirection
    field_simp [(decay_pos d.core).ne']
    dsimp [decay]
    ring
  have h₁ := mul_le_mul hratio hR (abs_nonneg _) (show 0 ≤ 3 * d.core.lam by linarith
    [d.core.lam_pos])
  have h₃ := mul_le_mul hCd hc.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
  have hpow : d.core.lam ^ 2 ≤ d.core.lam := by nlinarith [d.core.lam_pos, d.core.lam_lt]
  have hscale := mul_le_mul_of_nonneg_left hpow (valueRepairConstant_pos d.core.P_pos d.core.m).le
  rw [hid]
  apply (abs_sub _ _).trans
  apply (add_le_add_left (abs_add_le _ _) _).trans
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp [directionMainErrorConstant, mainRatio, mainSlope] at *
  nlinarith

/-! ## The shaped wait supplies the actual angular equilibrium error -/

theorem canonical_wait_for_power28 (c : Parameters)
    (hwait : c.wait = 60 * Real.log (1 / c.lam)) :
    ShapedWaitBounds.waitForPower c 28 ≤ c.wait := by
  rw [hwait]
  unfold ShapedWaitBounds.waitForPower
  rw [one_div, Real.log_inv]
  norm_num only [Nat.cast_ofNat]
  apply (div_le_iff₀ (show 0 < 1 - c.lam by linarith [c.lam_lt])).mpr
  have hl : 0 ≤ -Real.log c.lam := by
    have h := PulseAmplitude.log_inverse_nonneg c
    simpa only [one_div, Real.log_inv] using h
  have hm := mul_nonneg hl (show 0 ≤ (1 : ℝ) / 10 - c.lam by linarith [c.lam_lt])
  nlinarith

noncomputable def angularErrorConstant (P m : ℝ) : ℝ := 19 + 2 * sourceConstant P m

theorem angularErrorConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < angularErrorConstant P m := by
  have h := sourceConstant_pos hP m
  dsimp [angularErrorConstant]
  positivity

/-- The equilibrium approximation now has no initial-error hypothesis. -/
theorem actual_Qs_pulse_error (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (hh : d.h ≤ 1 / 100) {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |Qs w amp (d.core.pulseStart + y, eta) - angularEquilibrium d eta| ≤
      angularErrorConstant d.core.P d.core.m * d.core.lam ^ 28 := by
  have hi := ShapedWaitBounds.canonical_Qs_pulseStart_power_error w ha hh heta 28
    (canonical_wait_for_power28 d.core hwait)
  change |Qs w amp (d.core.pulseStart, eta) - angularEquilibrium d eta| ≤ 19 * d.core.lam ^ 28 at hi
  have hb := Qs_pulse_equilibrium_error w hwait hsmall ha heta hamp hamp' hy hy'
  change |Qs w amp (d.core.pulseStart + y, eta) - angularEquilibrium d eta| ≤
    |Qs w amp (d.core.pulseStart, eta) - angularEquilibrium d eta| *
      Real.exp (-(1 - d.core.lam) * y) + _ at hb
  have hr : 0 < 1 - d.core.lam := by linarith [d.core.lam_lt]
  have hexp : Real.exp (-(1 - d.core.lam) * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) hy)
  have hiprod := mul_le_mul hi hexp (Real.exp_pos _).le
    (show 0 ≤ 19 * d.core.lam ^ 28 by positivity)
  have hpow : d.core.lam ^ 30 ≤ d.core.lam ^ 28 :=
    pow_le_pow_of_le_one d.core.lam_pos.le (by linarith [d.core.lam_lt]) (by norm_num)
  have hs := mul_le_mul_of_nonneg_left hpow (sourceConstant_pos d.core.P_pos d.core.m).le
  have hfac : 1 ≤ 2 * (1 - d.core.lam) := by linarith [d.core.lam_lt]
  have hfac' := mul_le_mul_of_nonneg_left hfac
    (mul_nonneg (sourceConstant_pos d.core.P_pos d.core.m).le (pow_nonneg d.core.lam_pos.le 28))
  have hc : sourceConstant d.core.P d.core.m * d.core.lam ^ 30 / (1 - d.core.lam) ≤
      2 * sourceConstant d.core.P d.core.m * d.core.lam ^ 28 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith only [hs, hfac']
  dsimp [angularErrorConstant]
  nlinarith only [hb, hiprod, hc]

theorem actual_Qs_pulse_lower (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam)) (hsmall : d.core.lam ≤ 1 / 120)
    (hh : d.h ≤ 1 / 100)
    (hnum : angularErrorConstant d.core.P d.core.m * d.core.lam ^ 27 ≤ 1 / 4)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y : ℝ}
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    equilibriumNumerator d eta / 2 ≤ Qs w amp (d.core.pulseStart + y, eta) := by
  have he := actual_Qs_pulse_error w hwait hsmall hh ha heta hamp hamp' hy hy'
  have herr := mul_le_mul_of_nonneg_right hnum d.core.lam_pos.le
  have hpow : d.core.lam ^ 27 * d.core.lam = d.core.lam ^ 28 := by ring
  rw [mul_assoc, hpow] at herr
  have hA := (pulse_geometric_bounds d heta).2
  have heq : equilibriumNumerator d eta ≤ angularEquilibrium d eta := by
    apply (le_div_iff₀ (show 0 < 1 - d.core.lam by linarith [d.core.lam_lt])).mpr
    nlinarith [mul_nonneg (equilibriumNumerator_pos d eta).le d.core.lam_pos.le]
  have hlo := (abs_le.mp he).1
  nlinarith [sq_nonneg eta]

/-! ## A single explicit vanishing rate for the cone errors -/

noncomputable def coneRate (lam : ℝ) : ℝ :=
  lam + Real.sqrt lam * (1 + Real.log (1 / lam))

theorem coneRate_parts {lam : ℝ} (hlam : 0 < lam) (hsmall : lam ≤ 1) :
    0 ≤ coneRate lam ∧ lam ≤ coneRate lam ∧
      Real.sqrt lam * (1 + Real.log (1 / lam)) ≤ coneRate lam := by
  have hl : 0 ≤ Real.log (1 / lam) :=
    Real.log_nonneg ((le_div_iff₀ hlam).mpr (by simpa only [one_mul] using hsmall))
  have hs := Real.sqrt_nonneg lam
  have hp : 0 ≤ Real.sqrt lam * (1 + Real.log (1 / lam)) := by positivity
  dsimp [coneRate]
  exact ⟨add_nonneg hlam.le hp, le_add_of_nonneg_right hp, le_add_of_nonneg_left hlam.le⟩

theorem coneRate_tendsto_zero : Tendsto coneRate (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).mono_left inf_le_left
    simp only [Real.sqrt_zero] at h
    exact h
  have hl : Tendsto (fun x : ℝ => Real.log x * Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2))
  convert! (hi.add hs).sub hl using 1
  · funext x
    simp only [coneRate, one_div, Real.log_inv]
    ring
  · norm_num

private theorem raw_error_le_rate {lam Q B M H P A F v : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1)
    (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hv : v ≤ A * lam * (1 + Real.log (1 / lam))) :
    (4 / lam) * (Q * lam ^ 28 * B + M * lam ^ 2 + H * lam ^ 29) +
      (4 / Real.sqrt lam) * (3 * F * v + P * lam ^ 2) ≤
      (4 * (Q * B + M + H + P) + 12 * F * A) * coneRate lam := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hs₂ := Real.sq_sqrt hlam.le
  have hp28 : lam ^ 28 ≤ lam ^ 2 := pow_le_pow_of_le_one hlam.le hsmall (by norm_num)
  have hp29 : lam ^ 29 ≤ lam ^ 2 := pow_le_pow_of_le_one hlam.le hsmall (by norm_num)
  have hfirstInside : Q * lam ^ 28 * B + M * lam ^ 2 + H * lam ^ 29 ≤
      (Q * B + M + H) * lam ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hp28 (mul_nonneg hQ hB)
    have h₂ := mul_le_mul_of_nonneg_left hp29 hH
    nlinarith only [h₁, h₂]
  have hfirst : (4 / lam) * (Q * lam ^ 28 * B + M * lam ^ 2 + H * lam ^ 29) ≤
      4 * (Q * B + M + H) * lam := by
    have h := mul_le_mul_of_nonneg_left hfirstInside (by positivity : 0 ≤ 4 / lam)
    convert! h using 1
    field_simp [hlam.ne']
  have hv' : v / Real.sqrt lam ≤ A * Real.sqrt lam * (1 + Real.log (1 / lam)) := by
    apply (div_le_iff₀ hs).mpr
    calc
      v ≤ A * lam * (1 + Real.log (1 / lam)) := hv
      _ = A * Real.sqrt lam * (1 + Real.log (1 / lam)) * Real.sqrt lam := by
        calc
          _ = A * (Real.sqrt lam) ^ 2 * (1 + Real.log (1 / lam)) := by rw [hs₂]
          _ = _ := by ring
  have hp2 : lam ^ 2 / Real.sqrt lam ≤ lam := by
    apply (div_le_iff₀ hs).mpr
    have hl : lam ≤ Real.sqrt lam := Real.le_sqrt_of_sq_le (by nlinarith only [hlam, hsmall])
    nlinarith only [mul_le_mul_of_nonneg_left hl hlam.le]
  have hsecond : (4 / Real.sqrt lam) * (3 * F * v + P * lam ^ 2) ≤
      12 * F * A * (Real.sqrt lam * (1 + Real.log (1 / lam))) + 4 * P * lam := by
    have h₁ := mul_le_mul_of_nonneg_left hv' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hF)
    have h₂ := mul_le_mul_of_nonneg_left hp2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hP)
    calc
      _ = 12 * F * (v / Real.sqrt lam) + 4 * P * (lam ^ 2 / Real.sqrt lam) := by ring
      _ ≤ _ := by
        convert! add_le_add h₁ h₂ using 1
        ring
  have hr := coneRate_parts hlam hsmall
  have hlinear := mul_le_mul_of_nonneg_left hr.2.1
    (show 0 ≤ 4 * (Q * B + M + H + P) by positivity)
  have hparameter := mul_le_mul_of_nonneg_left hr.2.2
    (show 0 ≤ 12 * F * A by positivity)
  nlinarith only [hfirst, hsecond, hlinear, hparameter]

noncomputable def directionErrorConstant (P m A : ℝ) : ℝ :=
  4 * (angularErrorConstant P m * mainDirectionBound P m + fullLagBound P m +
    axialErrorConstant P m + parameterLagConstant P m) + 12 * mainBound * A

theorem directionErrorConstant_pos {P A : ℝ} (hP : 0 < P) (m : ℝ) (hA : 0 ≤ A) :
    0 < directionErrorConstant P m A := by
  have hq := angularErrorConstant_pos hP m
  have hb := mainDirectionBound_pos hP m
  have hm := fullLagBound_pos hP m
  have hh := axialErrorConstant_pos hP m
  have hp := parameterLagConstant_pos hP m
  have hf := mainBound_pos
  dsimp [directionErrorConstant]
  positivity

noncomputable def componentConstant (P m A : ℝ) : ℝ :=
  directionErrorConstant P m A + directionMainErrorConstant P m + shearErrorConstant P m + 1

theorem componentConstant_pos {P A : ℝ} (hP : 0 < P) (m : ℝ) (hA : 0 ≤ A) :
    0 < componentConstant P m A := by
  have hd := directionErrorConstant_pos hP m hA
  have hm := directionMainErrorConstant_pos hP m
  have hs := shearErrorConstant_pos hP m
  dsimp [componentConstant]
  positivity

theorem actual_component_errors (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    (hnum : angularErrorConstant d.core.P d.core.m * d.core.lam ^ 27 ≤ 1 / 4)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y A : ℝ} (hA : 0 ≤ A)
    (heta : |eta| ≤ 1) (hamp : |amp eta| ≤ 6 / 5) (hamp' : |deriv amp eta| ≤ 1)
    (hamprate : |deriv amp eta| ≤ A * d.core.lam * (1 + Real.log (1 / d.core.lam)))
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    |shearB w amp (d.core.pulseStart + y, eta) + mainRatio d.core amp eta y| ≤
        componentConstant d.core.P d.core.m A * coneRate d.core.lam ∧
      |directionRatio w amp (d.core.pulseStart + y, eta) - idealDirection d amp eta y| ≤
        componentConstant d.core.P d.core.m A * coneRate d.core.lam := by
  have hlam_le : d.core.lam ≤ 1 := by linarith
  have hh₁ : d.h ≤ 1 / 100 := by linarith
  have hQlow := actual_Qs_pulse_lower w hwait (by linarith) hh₁ hnum ha heta hamp hamp' hy hy'
  have hQerr := actual_Qs_pulse_error w hwait (by linarith) hh₁ ha heta hamp hamp' hy hy'
  have hraw := directionRatio_error_bound w hwait hsmall hh ha heta hamp hamp' hy hy' hQlow hQerr
  have hr := raw_error_le_rate d.core.lam_pos hlam_le
    (angularErrorConstant_pos d.core.P_pos d.core.m).le
    (mainDirectionBound_pos d.core.P_pos d.core.m).le
    (fullLagBound_pos d.core.P_pos d.core.m).le
    (axialErrorConstant_pos d.core.P_pos d.core.m).le
    (parameterLagConstant_pos d.core.P_pos d.core.m).le hA mainBound_pos.le hamprate
  have hmain : |directionRatio w amp (d.core.pulseStart + y, eta) - mainDirection d amp eta y| ≤
      directionErrorConstant d.core.P d.core.m A * coneRate d.core.lam := hraw.trans hr
  have hparts := coneRate_parts d.core.lam_pos hlam_le
  have hD := directionErrorConstant_pos d.core.P_pos d.core.m hA
  have hM := directionMainErrorConstant_pos d.core.P_pos d.core.m
  have hS := shearErrorConstant_pos d.core.P_pos d.core.m
  have hbig₁ : shearErrorConstant d.core.P d.core.m ≤ componentConstant d.core.P d.core.m A := by
    dsimp [componentConstant]
    linarith
  have hbig₂ : directionErrorConstant d.core.P d.core.m A + directionMainErrorConstant d.core.P
    d.core.m ≤
      componentConstant d.core.P d.core.m A := by
    dsimp [componentConstant]
    linarith
  constructor
  · exact (shearB_main_error w (by linarith) ha heta hamp hy hy').trans
      ((mul_le_mul_of_nonneg_left hparts.2.1 hS.le).trans
        (mul_le_mul_of_nonneg_right hbig₁ hparts.1))
  · have hdelta := mainDirection_ideal_error d hsmall hh heta hamp y
    have hdelta' := hdelta.trans (mul_le_mul_of_nonneg_left hparts.2.1 hM.le)
    have htri := abs_add_le (directionRatio w amp (d.core.pulseStart + y, eta) - mainDirection d
      amp eta y)
      (mainDirection d amp eta y - idealDirection d amp eta y)
    rw [sub_add_sub_cancel] at htri
    have hsum := htri.trans (add_le_add hmain hdelta')
    rw [← add_mul] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_right hbig₂ hparts.1)

noncomputable def pulseBudget (P m A lam : ℝ) : ℝ :=
  coneErrorBudget mainRatioBound idealDirectionBound (componentConstant P m A * coneRate lam) lam

private theorem cone_budget_eps_le_one {F M eps lam : ℝ}
    (hF : 0 ≤ F) (hM : 0 ≤ M) (heps : 0 ≤ eps) (hlam : 0 ≤ lam)
    (hb : coneErrorBudget F M eps lam ≤ 1 / 100) : eps ≤ 1 := by
  have h₁ := mul_nonneg heps (add_nonneg hM hF)
  have h₂ : 0 ≤ eps * (2 * F + 1) / 2 := by positivity
  have h₃ : 0 ≤ 2 * lam * (M + 1) ^ 2 := by positivity
  dsimp [coneErrorBudget] at hb
  nlinarith only [h₁, h₂, h₃, hb]

/-- The numerical margins refer only to the actual global stress histories
and the actual first radial derivatives of the corrected fields. -/
structure PulseConeAt (w : ResetWitness d K) (amp : ℝ → ℝ) (p : Point) : Prop where
  angular_positive : 0 < Qs w amp p
  first_margin : shearB w amp p * directionRatio w amp p ≤ 74 / 100
  second_margin : 2 * shearB w amp p * directionRatio w amp p +
    shearB w amp p ^ 2 / radialA w p + (radialA w p - 2) * directionRatio w amp p ^ 2 ≤ 168 / 100
  radial_gt_two : 2 < radialA w p

theorem PulseConeAt.true_criterion {w : ResetWitness d K} {amp : ℝ → ℝ} {p : Point}
    (h : PulseConeAt w amp p) :
    0 < radialA w p - shearB w amp p * directionRatio w amp p ∧
      2 * shearB w amp p * directionRatio w amp p + shearB w amp p ^ 2 / radialA w p +
        (radialA w p - 2) * directionRatio w amp p ^ 2 < 2 ∧
      2 < radialA w p * (1 + (shearB w amp p / radialA w p) ^ 2) := by
  have ha := h.radial_gt_two
  have hmul := mul_nonneg (show 0 ≤ radialA w p by linarith)
    (sq_nonneg (shearB w amp p / radialA w p))
  refine ⟨?_, ?_, ?_⟩
  · linarith [h.first_margin]
  · linarith [h.second_margin]
  · nlinarith only [ha, hmul]

/-- The full pulse cone for any smooth amplitude with the proved size and
first-derivative rate. Every further hypothesis is a scalar parameter bound. -/
theorem actual_pulse_cone (w : ResetWitness d K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    (hnum : angularErrorConstant d.core.P d.core.m * d.core.lam ^ 27 ≤ 1 / 4)
    {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) {eta y A : ℝ} (hA : 0 ≤ A)
    (heta : |eta| ≤ 1) (hamp₀ : 0 ≤ amp eta) (hamp : |amp eta| ≤ 6 / 5)
    (hamp' : |deriv amp eta| ≤ 1)
    (hamprate : |deriv amp eta| ≤ A * d.core.lam * (1 + Real.log (1 / d.core.lam)))
    (hbudget : pulseBudget d.core.P d.core.m A d.core.lam ≤ 1 / 100)
    (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    PulseConeAt w amp (d.core.pulseStart + y, eta) := by
  let eps := componentConstant d.core.P d.core.m A * coneRate d.core.lam
  have heps : 0 ≤ eps := mul_nonneg (componentConstant_pos d.core.P_pos d.core.m hA).le
    (coneRate_parts d.core.lam_pos (by linarith)).1
  have heps' : eps ≤ 1 := cone_budget_eps_le_one mainRatioBound_pos.le idealDirectionBound_pos.le
    heps d.core.lam_pos.le hbudget
  have he := actual_component_errors w hwait hsmall hh hnum ha hA heta hamp hamp' hamprate hy hy'
  have hm := main_profile_bounds d hsmall hh hamp₀ hamp hy
  have hc := perturbed_cone_margins d.core.lam_pos.le mainRatioBound_pos.le
    idealDirectionBound_pos.le
    heps heps' hm.1 hm.2.1 (derivativeCoefficient_nonneg d eta) (derivativeCoefficient_le d hsmall
      hh eta)
    hm.2.2.1 hm.2.2.2 he.1 he.2 hbudget
  have hQ := actual_Qs_pulse_lower w hwait (by linarith) (by linarith) hnum ha heta hamp hamp' hy
    hy'
  refine ⟨(denominator_bounds d heta hQ).1, hc.1, ?_, ?_⟩
  · rw [radialA_pulse w eta hy hy']
    convert! hc.2 using 1
    ring
  · rw [radialA_pulse w eta hy hy']
    linarith [d.core.lam_pos]

noncomputable def amplitudeDerivativeConstant (P m K : ℝ) : ℝ :=
  128 * CorrectedPulseAmplitude.combinedConstant P m K

theorem amplitudeDerivativeConstant_pos {P K : ℝ} (hP : 0 < P) (m : ℝ) (hK : 0 < K) :
    0 < amplitudeDerivativeConstant P m K :=
  mul_pos (by norm_num) (CorrectedPulseAmplitude.combinedConstant_pos hP m K hK)

noncomputable def correctedPulseBudget (P m K lam : ℝ) : ℝ :=
  pulseBudget P m (amplitudeDerivativeConstant P m K) lam

/-- The full actual pulse cone for the same corrected amplitude and reset
witness as the global schedule. No stress or cone estimate is assumed. -/
theorem corrected_pulse_cone (w : ResetWitness d K) (hK : 0 < K)
    (hwait : d.core.wait = 60 * Real.log (1 / d.core.lam))
    (hsmall : d.core.lam ≤ 1 / 100000) (hh : d.h ≤ d.core.lam / 100000)
    (hscale : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000)
    (hnum : angularErrorConstant d.core.P d.core.m * d.core.lam ^ 27 ≤ 1 / 4)
    (hbudget : correctedPulseBudget d.core.P d.core.m K d.core.lam ≤ 1 / 100)
    {eta y : ℝ} (heta : |eta| ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ d.core.pulseLength) :
    PulseConeAt w (CorrectedPulseAmplitude.amplitude d w.coefficients)
      (d.core.pulseStart + y, eta) := by
  have hs := CorrectedPulseAmplitude.amplitude_spec w hK (by linarith) hwait hscale
  have heta₂ : eta ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg eta) (by norm_num : (0 : ℝ) ≤ 1)).mpr heta
    nlinarith [sq_abs eta]
  have hb := hs.2 eta heta₂
  have hamp : |CorrectedPulseAmplitude.amplitude d w.coefficients eta| ≤ 6 / 5 := by
    rw [abs_of_pos (CorrectedPulseAmplitude.amplitude_pos d w.coefficients eta)]
    exact hb.2.1.le
  have hamp' : |deriv (CorrectedPulseAmplitude.amplitude d w.coefficients) eta| ≤ 1 := by
    have hd := hb.2.2.2.1
    linarith
  have hrate : |deriv (CorrectedPulseAmplitude.amplitude d w.coefficients) eta| ≤
      amplitudeDerivativeConstant d.core.P d.core.m K * d.core.lam *
        (1 + Real.log (1 / d.core.lam)) := by
    convert! hb.2.2.2.1 using 1
    dsimp [amplitudeDerivativeConstant, CorrectedPulseAmplitude.combinedScale,
      PulseAmplitude.logarithmicRate]
    ring
  exact actual_pulse_cone w hwait hsmall hh hnum hs.1
    (amplitudeDerivativeConstant_pos d.core.P_pos d.core.m hK).le heta
    (by linarith [hb.1]) hamp hamp' hrate hbudget hy hy'

theorem pulseBudget_tendsto_zero (P m A : ℝ) :
    Tendsto (pulseBudget P m A) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left inf_le_left
  have he := coneRate_tendsto_zero.const_mul (componentConstant P m A)
  have h := ((he.const_mul (2 * (idealDirectionBound + mainRatioBound + 1))).add
    (he.const_mul ((2 * mainRatioBound + 1) / 2))).add
      (hi.const_mul (2 * (idealDirectionBound + 1) ^ 2))
  convert! h using 1
  · funext lam
    dsimp [pulseBudget, coneErrorBudget]
    ring
  · ring_nf

theorem exists_pulseBudget_threshold (P m A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, 0 < lam → lam < δ → pulseBudget P m A lam ≤ 1 / 100 := by
  have he : ∀ᶠ lam in 𝓝[>] (0 : ℝ), pulseBudget P m A lam < 1 / 100 :=
    (pulseBudget_tendsto_zero P m A).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  exact ⟨δ, hδ, fun lam hlam hlt => (hsub ⟨hlam, hlt⟩).le⟩

/-- One threshold is chosen after the fixed prefix and reset constant.
It works for every supplied reset witness, keeps its actual energy-closing
amplitude, and is uniform over the full pulse and the physical parameter band. -/
theorem exists_corrected_pulse_threshold (P m K : ℝ) (hP : 0 < P) (hK : 0 < K) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ d : TailData,
      d.core.P = P → d.core.m = m → d.core.wait = 60 * Real.log (1 / d.core.lam) →
      d.core.lam < lam₀ → d.h ≤ d.core.lam / 100000 → ∀ w : ResetWitness d K,
        ∀ eta y : ℝ, |eta| ≤ 1 → 0 ≤ y → y ≤ d.core.pulseLength →
          PulseConeAt w (CorrectedPulseAmplitude.amplitude d w.coefficients)
            (d.core.pulseStart + y, eta) := by
  obtain ⟨δbudget, hδbudget, hbudget⟩ := exists_pulseBudget_threshold P m
    (amplitudeDerivativeConstant P m K)
  obtain ⟨δscale, hδscale, hscale⟩ :=
    PulseAmplitude.exists_rate_threshold (CorrectedPulseAmplitude.combinedConstant P m K)
  have hC := angularErrorConstant_pos hP m
  refine ⟨min δbudget (min δscale (min (1 / 100000) (1 / (4 * angularErrorConstant P m)))),
    lt_min hδbudget (lt_min hδscale (lt_min (by norm_num) (by positivity))), ?_⟩
  intro d hdP hdm hwait hlam hh w eta y heta hy hy'
  have hb : d.core.lam < δbudget := hlam.trans_le (min_le_left _ _)
  have hr := hlam.trans_le (min_le_right _ _)
  have hs : d.core.lam < δscale := hr.trans_le (min_le_left _ _)
  have hr' := hr.trans_le (min_le_right _ _)
  have hsmall : d.core.lam ≤ 1 / 100000 := (hr'.trans_le (min_le_left _ _)).le
  have hCsmall : d.core.lam ≤ 1 / (4 * angularErrorConstant P m) :=
    (hr'.trans_le (min_le_right _ _)).le
  have hnum : angularErrorConstant d.core.P d.core.m * d.core.lam ^ 27 ≤ 1 / 4 := by
    rw [hdP, hdm]
    have hp : d.core.lam ^ 27 ≤ d.core.lam := by
      simpa only [pow_one] using pow_le_pow_of_le_one d.core.lam_pos.le
        (show d.core.lam ≤ 1 by linarith) (show 1 ≤ 27 by norm_num)
    have hm := mul_le_mul_of_nonneg_left hp hC.le
    have hd := (le_div_iff₀ (show 0 < 4 * angularErrorConstant P m by positivity)).mp hCsmall
    nlinarith only [hm, hd]
  have hscale' : CorrectedPulseAmplitude.combinedScale d K ≤ 1 / 1000 := by
    dsimp [CorrectedPulseAmplitude.combinedScale]
    rw [hdP, hdm]
    exact hscale d.core.lam d.core.lam_pos hs
  have hbudget' : correctedPulseBudget d.core.P d.core.m K d.core.lam ≤ 1 / 100 := by
    dsimp only [correctedPulseBudget]
    rw [hdP, hdm]
    exact hbudget d.core.lam d.core.lam_pos hb
  exact corrected_pulse_cone w hK hwait hsmall hh hscale' hnum hbudget' heta hy hy'

end NavierStokes.PulseCone

end
