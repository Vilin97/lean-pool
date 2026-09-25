/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.WavePacket
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Two-fold nonstationary phase away from a wave packet

This file proves the `k = 2` instance of the oscillatory estimate used in
equation (3.2) of the paper. The proof differentiates the phase in the
original kernel variable twice; it does not use the erroneous square-root
substitution displayed in the paper.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped Interval

namespace QuadraticCarleson

/-- The off-support action, in packet coordinates. -/
noncomputable def offSupportOscillatoryAction (modulation s t x : ℝ) : ℂ :=
  ∫ u : ℝ, (wavePacket s t u : ℂ) *
    phase (modulation * (x - u) ^ 2) / ((x - u : ℝ) : ℂ)

/-- First derivative of the rescaled packet. -/
noncomputable def wavePacketDeriv (s t u : ℝ) : ℝ :=
  t⁻¹ * (deriv baseBump ((u - s) / t) * t⁻¹)

/-- Second derivative of the rescaled packet. -/
noncomputable def wavePacketSecondDeriv (s t u : ℝ) : ℝ :=
  t⁻¹ * (iteratedDeriv 2 baseBump ((u - s) / t) * t⁻¹ * t⁻¹)

theorem hasDerivAt_wavePacket (s : ℝ) {t : ℝ} (_ht : t ≠ 0) (u : ℝ) :
    HasDerivAt (wavePacket s t) (wavePacketDeriv s t u) u := by
  unfold wavePacket wavePacketDeriv
  simpa [div_eq_mul_inv, mul_assoc] using
    ((baseBump_smooth.differentiable (by simp) ((u - s) / t)).hasDerivAt.comp u
      ((hasDerivAt_id u).sub_const s |>.div_const t) |>.const_mul t⁻¹)

theorem hasDerivAt_wavePacketDeriv (s : ℝ) {t : ℝ} (_ht : t ≠ 0) (u : ℝ) :
    HasDerivAt (wavePacketDeriv s t) (wavePacketSecondDeriv s t u) u := by
  unfold wavePacketDeriv wavePacketSecondDeriv
  have hiter : iteratedDeriv 2 baseBump = deriv (deriv baseBump) := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  have hdiff : Differentiable ℝ (deriv baseBump) := by
    simpa only [iteratedDeriv_one] using
      baseBump_smooth.differentiable_iteratedDeriv 1 (by simp)
  simpa [div_eq_mul_inv, mul_assoc] using
    ((hdiff ((u - s) / t)).hasDerivAt.comp u
      ((hasDerivAt_id u).sub_const s |>.div_const t) |>.mul_const t⁻¹ |>.const_mul t⁻¹)

theorem hasDerivAt_quadraticPhase (modulation x u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ phase (modulation * (x - v) ^ 2))
      (((-(4 * Real.pi * modulation * (x - u)) : ℝ) : ℂ) * Complex.I *
        phase (modulation * (x - u) ^ 2)) u := by
  unfold phase
  have hreal : HasDerivAt (fun v : ℝ ↦ 2 * Real.pi * (modulation * (x - v) ^ 2))
      (-(4 * Real.pi * modulation * (x - u))) u := by
    have hraw := (((hasDerivAt_const u modulation).mul
      (((hasDerivAt_const u x).sub (hasDerivAt_id u)).pow 2)).const_mul
        (2 * Real.pi))
    simpa [mul_assoc] using hraw.congr_deriv (by
      simp only [Pi.sub_apply, id_eq]
      ring)
  have hcomplex : HasDerivAt
      (fun v : ℝ ↦ ((2 * Real.pi * (modulation * (x - v) ^ 2) : ℝ) : ℂ) * Complex.I)
      (((-(4 * Real.pi * modulation * (x - u)) : ℝ) : ℂ) * Complex.I) u := by
    exact hreal.ofReal_comp.mul_const Complex.I
  convert hcomplex.cexp using 1; ring

/-- The fixed explicit constant in the two-fold estimate. -/
noncomputable def offSupportOscillatoryConstant : ℝ :=
  (27 * (∫ v : ℝ, |iteratedDeriv 2 baseBump v|) +
    810 * (∫ v : ℝ, |deriv baseBump v|) + 7776) / (4 * Real.pi) ^ 2

private noncomputable def oscillatoryCoeff (modulation : ℝ) : ℂ :=
  ((-(4 * Real.pi * modulation) : ℝ) : ℂ) * Complex.I

private noncomputable def ibpAmplitude0
    (modulation x : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℂ :=
  (p u : ℂ) / (oscillatoryCoeff modulation * ((x - u : ℝ) : ℂ) ^ 2)

private noncomputable def ibpAmplitude0Deriv
    (modulation x : ℝ) (p p' : ℝ → ℝ) (u : ℝ) : ℂ :=
  (p' u : ℂ) / (oscillatoryCoeff modulation * ((x - u : ℝ) : ℂ) ^ 2) +
    2 * (p u : ℂ) / (oscillatoryCoeff modulation * ((x - u : ℝ) : ℂ) ^ 3)

private noncomputable def ibpAmplitude1
    (modulation x : ℝ) (p p' : ℝ → ℝ) (u : ℝ) : ℂ :=
  (p' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 3) +
    2 * (p u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 4)

private noncomputable def ibpAmplitude1Deriv
    (modulation x : ℝ) (p p' p'' : ℝ → ℝ) (u : ℝ) : ℂ :=
  (p'' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 3) +
    5 * (p' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 4) +
    8 * (p u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 5)

private theorem oscillatoryCoeff_ne_zero {modulation : ℝ} (hmod : 0 < modulation) :
    oscillatoryCoeff modulation ≠ 0 := by
  rw [oscillatoryCoeff]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hmod.ne')))
    Complex.I_ne_zero

private theorem hasDerivAt_ibpAmplitude0
    {modulation x u : ℝ} {p p' : ℝ → ℝ} (hmod : 0 < modulation)
    (hxu : x - u ≠ 0) (hp : HasDerivAt p (p' u) u) :
    HasDerivAt (ibpAmplitude0 modulation x p)
      (ibpAmplitude0Deriv modulation x p p' u) u := by
  have hz : HasDerivAt (fun v : ℝ ↦ ((x - v : ℝ) : ℂ)) (-1 : ℂ) u :=
    by
      convert ((hasDerivAt_const u x).sub (hasDerivAt_id u)).ofReal_comp using 1 <;>
        norm_num
  have hpC : HasDerivAt (fun v : ℝ ↦ (p v : ℂ)) (p' u : ℂ) u := hp.ofReal_comp
  have hd : oscillatoryCoeff modulation ≠ 0 := oscillatoryCoeff_ne_zero hmod
  have hzc : ((x - u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxu
  have hden : HasDerivAt
      (fun v : ℝ ↦ oscillatoryCoeff modulation * ((x - v : ℝ) : ℂ) ^ 2)
      (-2 * oscillatoryCoeff modulation * ((x - u : ℝ) : ℂ)) u := by
    exact ((hz.pow 2).const_mul (oscillatoryCoeff modulation)).congr_deriv (by ring)
  unfold ibpAmplitude0 ibpAmplitude0Deriv
  have hquot := hpC.div hden (mul_ne_zero hd (pow_ne_zero 2 hzc))
  apply hquot.congr_deriv
  field_simp [hd, hzc]
  ring

private theorem hasDerivAt_ibpAmplitude1
    {modulation x u : ℝ} {p p' p'' : ℝ → ℝ} (hmod : 0 < modulation)
    (hxu : x - u ≠ 0) (hp : HasDerivAt p (p' u) u)
    (hp' : HasDerivAt p' (p'' u) u) :
    HasDerivAt (ibpAmplitude1 modulation x p p')
      (ibpAmplitude1Deriv modulation x p p' p'' u) u := by
  have hz : HasDerivAt (fun v : ℝ ↦ ((x - v : ℝ) : ℂ)) (-1 : ℂ) u :=
    by
      convert ((hasDerivAt_const u x).sub (hasDerivAt_id u)).ofReal_comp using 1 <;>
        norm_num
  have hpC : HasDerivAt (fun v : ℝ ↦ (p v : ℂ)) (p' u : ℂ) u := hp.ofReal_comp
  have hp'C : HasDerivAt (fun v : ℝ ↦ (p' v : ℂ)) (p'' u : ℂ) u := hp'.ofReal_comp
  have hd : oscillatoryCoeff modulation ≠ 0 := oscillatoryCoeff_ne_zero hmod
  have hzc : ((x - u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxu
  have hden3 : HasDerivAt
      (fun v : ℝ ↦ oscillatoryCoeff modulation ^ 2 * ((x - v : ℝ) : ℂ) ^ 3)
      (-3 * oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 2) u := by
    exact ((hz.pow 3).const_mul (oscillatoryCoeff modulation ^ 2)).congr_deriv (by ring)
  have hden4 : HasDerivAt
      (fun v : ℝ ↦ oscillatoryCoeff modulation ^ 2 * ((x - v : ℝ) : ℂ) ^ 4)
      (-4 * oscillatoryCoeff modulation ^ 2 * ((x - u : ℝ) : ℂ) ^ 3) u := by
    exact ((hz.pow 4).const_mul (oscillatoryCoeff modulation ^ 2)).congr_deriv (by ring)
  unfold ibpAmplitude1 ibpAmplitude1Deriv
  have hquot := (hp'C.div hden3
      (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 3 hzc))).add
    ((hpC.const_mul 2).div hden4
      (mul_ne_zero (pow_ne_zero 2 hd) (pow_ne_zero 4 hzc)))
  apply hquot.congr_deriv
  field_simp [hd, hzc]
  ring

private theorem twofold_integration_by_parts
    {modulation x l r : ℝ} {p p' p'' : ℝ → ℝ}
    (hmod : 0 < modulation)
    (hxu : ∀ u ∈ uIcc l r, x - u ≠ 0)
    (hpcont : Continuous p) (hp'cont : Continuous p') (hp''cont : Continuous p'')
    (hp : ∀ u ∈ uIcc l r, HasDerivAt p (p' u) u)
    (hp' : ∀ u ∈ uIcc l r, HasDerivAt p' (p'' u) u)
    (hpl : p l = 0) (hpr : p r = 0) (hp'l : p' l = 0) (hp'r : p' r = 0) :
    (∫ u in l..r, (p u : ℂ) * phase (modulation * (x - u) ^ 2) /
        ((x - u : ℝ) : ℂ)) =
      ∫ u in l..r, ibpAmplitude1Deriv modulation x p p' p'' u *
        phase (modulation * (x - u) ^ 2) := by
  let q : ℝ → ℂ := fun u ↦ phase (modulation * (x - u) ^ 2)
  let q' : ℝ → ℂ := fun u ↦
    (((-(4 * Real.pi * modulation * (x - u)) : ℝ) : ℂ) * Complex.I) * q u
  let A0 := ibpAmplitude0 modulation x p
  let A0' := ibpAmplitude0Deriv modulation x p p'
  let A1 := ibpAmplitude1 modulation x p p'
  let A1' := ibpAmplitude1Deriv modulation x p p' p''
  have hq : ∀ u ∈ uIcc l r, HasDerivAt q (q' u) u := by
    intro u hu
    exact hasDerivAt_quadraticPhase modulation x u
  have hA0 : ∀ u ∈ uIcc l r, HasDerivAt A0 (A0' u) u := by
    intro u hu
    exact hasDerivAt_ibpAmplitude0 hmod (hxu u hu) (hp u hu)
  have hA1 : ∀ u ∈ uIcc l r, HasDerivAt A1 (A1' u) u := by
    intro u hu
    exact hasDerivAt_ibpAmplitude1 hmod (hxu u hu) (hp u hu) (hp' u hu)
  have hqcont : ContinuousOn q (uIcc l r) := fun u hu ↦
    (hq u hu).continuousAt.continuousWithinAt
  have hA0cont : ContinuousOn A0 (uIcc l r) := fun u hu ↦
    (hA0 u hu).continuousAt.continuousWithinAt
  have hA1cont : ContinuousOn A1 (uIcc l r) := fun u hu ↦
    (hA1 u hu).continuousAt.continuousWithinAt
  have hq'cont : Continuous q' := by
    dsimp only [q', q]
    unfold phase
    fun_prop
  have hA0'cont : ContinuousOn A0' (uIcc l r) := by
    dsimp only [A0']
    unfold ibpAmplitude0Deriv
    apply ContinuousOn.add
    · apply (Complex.continuous_ofReal.comp hp'cont).continuousOn.div
        (continuous_const.mul
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow
            2)).continuousOn
      intro u hu
      exact mul_ne_zero (oscillatoryCoeff_ne_zero hmod)
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hxu u hu)))
    · apply (continuous_const.mul (Complex.continuous_ofReal.comp hpcont)).continuousOn.div
        (continuous_const.mul
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow
            3)).continuousOn
      intro u hu
      exact mul_ne_zero (oscillatoryCoeff_ne_zero hmod)
        (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (hxu u hu)))
  have hA1'cont : ContinuousOn A1' (uIcc l r) := by
    dsimp only [A1']
    unfold ibpAmplitude1Deriv
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · apply (Complex.continuous_ofReal.comp hp''cont).continuousOn.div
          (continuous_const.mul
            ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow
              3)).continuousOn
        intro u hu
        exact mul_ne_zero (pow_ne_zero 2 (oscillatoryCoeff_ne_zero hmod))
          (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (hxu u hu)))
      · apply (continuous_const.mul (Complex.continuous_ofReal.comp hp'cont)).continuousOn.div
          (continuous_const.mul
            ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow
              4)).continuousOn
        intro u hu
        exact mul_ne_zero (pow_ne_zero 2 (oscillatoryCoeff_ne_zero hmod))
          (pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (hxu u hu)))
    · apply (continuous_const.mul (Complex.continuous_ofReal.comp hpcont)).continuousOn.div
        (continuous_const.mul
          ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow
            5)).continuousOn
      intro u hu
      exact mul_ne_zero (pow_ne_zero 2 (oscillatoryCoeff_ne_zero hmod))
        (pow_ne_zero 5 (Complex.ofReal_ne_zero.mpr (hxu u hu)))
  have hibp0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA0 hq hA0'cont.intervalIntegrable (hq'cont.intervalIntegrable l r)
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA1 hq hA1'cont.intervalIntegrable (hq'cont.intervalIntegrable l r)
  have hfirst : ∀ u ∈ uIcc l r,
      (p u : ℂ) * q u / ((x - u : ℝ) : ℂ) = A0 u * q' u := by
    intro u hu
    have hd := oscillatoryCoeff_ne_zero hmod
    have hzc : ((x - u : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hxu u hu)
    dsimp only [A0, q', q]
    unfold ibpAmplitude0 oscillatoryCoeff
    field_simp [hmod.ne', Real.pi_ne_zero]
    push_cast
    ring
  have hsecond : ∀ u ∈ uIcc l r, A0' u * q u = A1 u * q' u := by
    intro u hu
    have hd := oscillatoryCoeff_ne_zero hmod
    have hzc : ((x - u : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hxu u hu)
    dsimp only [A0', A1, q', q]
    unfold ibpAmplitude0Deriv ibpAmplitude1 oscillatoryCoeff
    field_simp [hmod.ne', Real.pi_ne_zero]
    push_cast
    ring
  have hA0left : A0 l = 0 := by simp [A0, ibpAmplitude0, hpl]
  have hA0right : A0 r = 0 := by simp [A0, ibpAmplitude0, hpr]
  have hA1left : A1 l = 0 := by simp [A1, ibpAmplitude1, hpl, hp'l]
  have hA1right : A1 r = 0 := by simp [A1, ibpAmplitude1, hpr, hp'r]
  calc
    (∫ u in l..r, (p u : ℂ) * phase (modulation * (x - u) ^ 2) /
        ((x - u : ℝ) : ℂ)) = ∫ u in l..r, A0 u * q' u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hfirst u (by simpa using hu)
    _ = -(∫ u in l..r, A0' u * q u) := by
      rw [hibp0, hA0left, hA0right]
      simp
    _ = -(∫ u in l..r, A1 u * q' u) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      exact hsecond u (by simpa using hu)
    _ = ∫ u in l..r, A1' u * q u := by
      rw [hibp1, hA1left, hA1right]
      simp
    _ = ∫ u in l..r, ibpAmplitude1Deriv modulation x p p' p'' u *
        phase (modulation * (x - u) ^ 2) := rfl

theorem continuous_wavePacketDeriv (s t : ℝ) : Continuous (wavePacketDeriv s t) := by
  have hderiv : Continuous (deriv baseBump) := by
    simpa only [iteratedDeriv_one] using
      baseBump_smooth.continuous_iteratedDeriv 1 (by simp)
  unfold wavePacketDeriv
  fun_prop

theorem continuous_wavePacketSecondDeriv (s t : ℝ) :
    Continuous (wavePacketSecondDeriv s t) := by
  have hderiv : Continuous (iteratedDeriv 2 baseBump) :=
    baseBump_smooth.continuous_iteratedDeriv 2 (by simp)
  unfold wavePacketSecondDeriv
  fun_prop

theorem baseBump_neg_third_eq_zero : baseBump (-1 / 3) = 0 := by
  rw [← notMem_support]
  rw [baseBump, baseBumpData.support_normed_eq]
  simp [baseBumpData]
  norm_num

theorem baseBump_third_eq_zero : baseBump (1 / 3) = 0 := by
  rw [← notMem_support]
  rw [baseBump, baseBumpData.support_normed_eq]
  simp [baseBumpData]
  norm_num

theorem deriv_baseBump_neg_third_eq_zero : deriv baseBump (-1 / 3) = 0 := by
  apply deriv_of_notMem_tsupport
  rw [baseBump, baseBumpData.tsupport_normed_eq]
  simp [baseBumpData]
  norm_num

theorem deriv_baseBump_third_eq_zero : deriv baseBump (1 / 3) = 0 := by
  apply deriv_of_notMem_tsupport
  rw [baseBump, baseBumpData.tsupport_normed_eq]
  simp [baseBumpData]
  norm_num

theorem wavePacket_left_third_eq_zero (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    wavePacket s t (s - t / 3) = 0 := by
  rw [wavePacket, show (s - t / 3 - s) / t = -1 / 3 by field_simp; ring,
    baseBump_neg_third_eq_zero, mul_zero]

theorem wavePacket_right_third_eq_zero (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    wavePacket s t (s + t / 3) = 0 := by
  rw [wavePacket, show (s + t / 3 - s) / t = 1 / 3 by field_simp; ring,
    baseBump_third_eq_zero, mul_zero]

theorem wavePacketDeriv_left_third_eq_zero (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    wavePacketDeriv s t (s - t / 3) = 0 := by
  rw [wavePacketDeriv, show (s - t / 3 - s) / t = -1 / 3 by field_simp; ring,
    deriv_baseBump_neg_third_eq_zero]
  ring

theorem wavePacketDeriv_right_third_eq_zero (s : ℝ) {t : ℝ} (ht : t ≠ 0) :
    wavePacketDeriv s t (s + t / 3) = 0 := by
  rw [wavePacketDeriv, show (s + t / 3 - s) / t = 1 / 3 by field_simp; ring,
    deriv_baseBump_third_eq_zero]
  ring

private theorem integrable_abs_deriv_baseBump :
    Integrable (fun v : ℝ ↦ |deriv baseBump v|) := by
  have hc : Continuous (fun v : ℝ ↦ |deriv baseBump v|) := by
    have hd : Continuous (deriv baseBump) := by
      simpa only [iteratedDeriv_one] using
        baseBump_smooth.continuous_iteratedDeriv 1 (by simp)
    fun_prop
  exact hc.integrable_of_hasCompactSupport baseBump_hasCompactSupport.deriv.abs

private theorem integrable_abs_secondDeriv_baseBump :
    Integrable (fun v : ℝ ↦ |iteratedDeriv 2 baseBump v|) := by
  have hc : Continuous (fun v : ℝ ↦ |iteratedDeriv 2 baseBump v|) := by
    have hd := baseBump_smooth.continuous_iteratedDeriv 2 (by simp)
    fun_prop
  have hs : HasCompactSupport (iteratedDeriv 2 baseBump) := by
    have hiter : iteratedDeriv 2 baseBump = deriv (deriv baseBump) := by
      rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hiter]
    exact baseBump_hasCompactSupport.deriv.deriv
  have hsabs : HasCompactSupport (fun v : ℝ ↦ |iteratedDeriv 2 baseBump v|) := by
    change HasCompactSupport |iteratedDeriv 2 baseBump|
    exact hs.abs
  exact hc.integrable_of_hasCompactSupport hsabs

theorem integral_abs_wavePacketDeriv (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, |wavePacketDeriv s t u| =
      t⁻¹ * ∫ v : ℝ, |deriv baseBump v| := by
  simp_rw [wavePacketDeriv, abs_mul, abs_inv, abs_of_pos ht]
  rw [integral_sub_right_eq_self
    (fun u : ℝ ↦ t⁻¹ * (|deriv baseBump (u / t)| * t⁻¹)) s]
  rw [integral_const_mul, integral_mul_const]
  have hscale : (∫ u : ℝ, |deriv baseBump (u / t)|) =
      t * ∫ v : ℝ, |deriv baseBump v| := by
    simpa [abs_of_pos ht, smul_eq_mul] using
      Measure.integral_comp_div (fun v : ℝ ↦ |deriv baseBump v|) t
  rw [hscale]
  field_simp [ht.ne']

theorem integral_abs_wavePacketSecondDeriv (s : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, |wavePacketSecondDeriv s t u| =
      t⁻¹ ^ 2 * ∫ v : ℝ, |iteratedDeriv 2 baseBump v| := by
  simp_rw [wavePacketSecondDeriv, abs_mul, abs_inv, abs_of_pos ht]
  rw [integral_sub_right_eq_self
    (fun u : ℝ ↦ t⁻¹ * (|iteratedDeriv 2 baseBump (u / t)| * t⁻¹ * t⁻¹)) s]
  rw [integral_const_mul, integral_mul_const, integral_mul_const]
  have hscale : (∫ u : ℝ, |iteratedDeriv 2 baseBump (u / t)|) =
      t * ∫ v : ℝ, |iteratedDeriv 2 baseBump v| := by
    simpa [abs_of_pos ht, smul_eq_mul] using
      Measure.integral_comp_div (fun v : ℝ ↦ |iteratedDeriv 2 baseBump v|) t
  rw [hscale]
  field_simp [ht.ne']

private theorem integrable_abs_wavePacketDeriv (s : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ ↦ |wavePacketDeriv s t u|) := by
  have hs : HasCompactSupport (wavePacketDeriv s t) := by
    have heq : wavePacketDeriv s t = deriv (wavePacket s t) := by
      funext u
      exact (hasDerivAt_wavePacket s ht.ne' u).deriv.symm
    rw [heq]
    exact (wavePacket_hasCompactSupport s ht).deriv
  exact (continuous_wavePacketDeriv s t).abs.integrable_of_hasCompactSupport hs.abs

private theorem integrable_abs_wavePacketSecondDeriv (s : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun u : ℝ ↦ |wavePacketSecondDeriv s t u|) := by
  have hs : HasCompactSupport (wavePacketSecondDeriv s t) := by
    have heq : wavePacketSecondDeriv s t = deriv (wavePacketDeriv s t) := by
      funext u
      exact (hasDerivAt_wavePacketDeriv s ht.ne' u).deriv.symm
    rw [heq]
    have hp : HasCompactSupport (wavePacketDeriv s t) := by
      have heq' : wavePacketDeriv s t = deriv (wavePacket s t) := by
        funext u
        exact (hasDerivAt_wavePacket s ht.ne' u).deriv.symm
      rw [heq']
      exact (wavePacket_hasCompactSupport s ht).deriv
    exact hp.deriv
  exact (continuous_wavePacketSecondDeriv s t).abs.integrable_of_hasCompactSupport hs.abs

theorem half_length_le_abs_center {s t x : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) : t / 2 ≤ |x - s| := by
  rw [mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonpos] <;> linarith
  · rw [abs_of_nonneg] <;> linarith

theorem third_interval_separation {s t x u : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2))
    (hu : u ∈ uIcc (s - t / 3) (s + t / 3)) :
    |x - s| / 3 ≤ |x - u| := by
  have hlr : s - t / 3 ≤ s + t / 3 := by linarith
  rw [uIcc_of_le hlr, mem_Icc] at hu
  have hus : |u - s| ≤ t / 3 := by
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have hts := half_length_le_abs_center ht hx
  have htri : |x - s| ≤ |x - u| + |u - s| := by
    calc
      |x - s| = |(x - u) + (u - s)| := by ring_nf
      _ ≤ |x - u| + |u - s| := abs_add_le _ _
  linarith

private theorem support_oscillatory_integrand_subset
    {modulation s t x : ℝ} (ht : 0 < t) :
    Function.support (fun u : ℝ ↦ (wavePacket s t u : ℂ) *
      phase (modulation * (x - u) ^ 2) / ((x - u : ℝ) : ℂ)) ⊆
        Ioc (s - t / 3) (s + t / 3) := by
  intro u hu
  have hp : wavePacket s t u ≠ 0 := by
    intro hp
    apply hu
    simp [hp]
  have hsupp := wavePacket_support ht hp
  constructor <;> linarith [hsupp.1, hsupp.2]

private theorem norm_phase_oscillatory (a : ℝ) : ‖phase a‖ = 1 := by
  rw [phase]
  simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * a)

private theorem norm_oscillatoryCoeff (modulation : ℝ) (hmod : 0 < modulation) :
    ‖oscillatoryCoeff modulation‖ = 4 * Real.pi * modulation := by
  rw [oscillatoryCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_neg, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg Real.pi_pos.le,
    abs_of_pos hmod]

/-- The corrected twice-integrated identity for the fixed wave packet. -/
theorem offSupportOscillatoryAction_eq_twiceIntegrated
    {modulation s t x : ℝ} (hmod : 0 < modulation) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    offSupportOscillatoryAction modulation s t x =
      ∫ u in (s - t / 3)..(s + t / 3),
        ibpAmplitude1Deriv modulation x (wavePacket s t)
          (wavePacketDeriv s t) (wavePacketSecondDeriv s t) u *
            phase (modulation * (x - u) ^ 2) := by
  rw [offSupportOscillatoryAction]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (support_oscillatory_integrand_subset ht)]
  apply twofold_integration_by_parts hmod
  · intro u hu
    have hsep := third_interval_separation ht hx hu
    have hdistpos : 0 < |x - s| :=
      lt_of_lt_of_le (half_pos ht) (half_length_le_abs_center ht hx)
    exact sub_ne_zero.mpr (by
      intro hux
      subst x
      rw [sub_self, abs_zero] at hsep
      linarith)
  · exact continuous_wavePacket s t
  · exact continuous_wavePacketDeriv s t
  · exact continuous_wavePacketSecondDeriv s t
  · intro u hu
    exact hasDerivAt_wavePacket s ht.ne' u
  · intro u hu
    exact hasDerivAt_wavePacketDeriv s ht.ne' u
  · exact wavePacket_left_third_eq_zero s ht.ne'
  · exact wavePacket_right_third_eq_zero s ht.ne'
  · exact wavePacketDeriv_left_third_eq_zero s ht.ne'
  · exact wavePacketDeriv_right_third_eq_zero s ht.ne'

private theorem norm_ibpAmplitude1Deriv_le
    {modulation x u a : ℝ} {p p' p'' : ℝ → ℝ} (hmod : 0 < modulation)
    (ha : 0 < a) (hsep : a / 3 ≤ |x - u|) :
    ‖ibpAmplitude1Deriv modulation x p p' p'' u *
        phase (modulation * (x - u) ^ 2)‖ ≤
      (27 * |p'' u| / a ^ 3 + 405 * |p' u| / a ^ 4 +
        1944 * |p u| / a ^ 5) / (4 * Real.pi * modulation) ^ 2 := by
  have hz : 0 < |x - u| := lt_of_lt_of_le (by positivity : 0 < a / 3) hsep
  have h3 : (a / 3) ^ 3 ≤ |x - u| ^ 3 := pow_le_pow_left₀ (by positivity) hsep 3
  have h4 : (a / 3) ^ 4 ≤ |x - u| ^ 4 := pow_le_pow_left₀ (by positivity) hsep 4
  have h5 : (a / 3) ^ 5 ≤ |x - u| ^ 5 := pow_le_pow_left₀ (by positivity) hsep 5
  have hD : 0 < (4 * Real.pi * modulation) ^ 2 := by positivity
  have hpow3 : a ^ 3 ≤ 27 * |x - u| ^ 3 := by
    calc
      a ^ 3 = 27 * (a / 3) ^ 3 := by ring
      _ ≤ 27 * |x - u| ^ 3 := mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hpow4 : a ^ 4 ≤ 81 * |x - u| ^ 4 := by
    calc
      a ^ 4 = 81 * (a / 3) ^ 4 := by ring
      _ ≤ 81 * |x - u| ^ 4 := mul_le_mul_of_nonneg_left h4 (by norm_num)
  have hpow5 : a ^ 5 ≤ 243 * |x - u| ^ 5 := by
    calc
      a ^ 5 = 243 * (a / 3) ^ 5 := by ring
      _ ≤ 243 * |x - u| ^ 5 := mul_le_mul_of_nonneg_left h5 (by norm_num)
  have hterm2 :
      |p'' u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 3) ≤
        (27 * |p'' u| / a ^ 3) / (4 * Real.pi * modulation) ^ 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hD (pow_pos hz 3))
      (mul_pos (pow_pos ha 3) hD)).2
    have h := mul_le_mul_of_nonneg_left hpow3
      (mul_nonneg (abs_nonneg (p'' u)) hD.le)
    nlinarith
  have hterm1 :
      5 * |p' u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 4) ≤
        (405 * |p' u| / a ^ 4) / (4 * Real.pi * modulation) ^ 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hD (pow_pos hz 4))
      (mul_pos (pow_pos ha 4) hD)).2
    have h := mul_le_mul_of_nonneg_left hpow4
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (abs_nonneg (p' u))) hD.le)
    nlinarith
  have hterm0 :
      8 * |p u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 5) ≤
        (1944 * |p u| / a ^ 5) / (4 * Real.pi * modulation) ^ 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hD (pow_pos hz 5))
      (mul_pos (pow_pos ha 5) hD)).2
    have h := mul_le_mul_of_nonneg_left hpow5
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (abs_nonneg (p u))) hD.le)
    nlinarith
  rw [norm_mul, norm_phase_oscillatory, mul_one]
  unfold ibpAmplitude1Deriv
  calc
    ‖(p'' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 3) +
        5 * (p' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 4) +
        8 * (p u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 5)‖ ≤
      ‖(p'' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 3)‖ +
        ‖5 * (p' u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 4)‖ +
        ‖8 * (p u : ℂ) / (oscillatoryCoeff modulation ^ 2 * ↑(x - u) ^ 5)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ = |p'' u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 3) +
        5 * |p' u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 4) +
        8 * |p u| / ((4 * Real.pi * modulation) ^ 2 * |x - u| ^ 5) := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        norm_oscillatoryCoeff modulation hmod]
      norm_num
    _ ≤ (27 * |p'' u| / a ^ 3) / (4 * Real.pi * modulation) ^ 2 +
        (405 * |p' u| / a ^ 4) / (4 * Real.pi * modulation) ^ 2 +
        (1944 * |p u| / a ^ 5) / (4 * Real.pi * modulation) ^ 2 :=
      add_le_add (add_le_add hterm2 hterm1) hterm0
    _ = (27 * |p'' u| / a ^ 3 + 405 * |p' u| / a ^ 4 +
        1944 * |p u| / a ^ 5) / (4 * Real.pi * modulation) ^ 2 := by ring

/-- The `k = 2` oscillatory off-support estimate used in equation (3.2).
All constants are uniform in the interval, evaluation point, and positive
modulation. -/
theorem offSupportOscillatoryAction_norm_le
    {modulation s t x : ℝ} (hmod : 0 < modulation) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportOscillatoryAction modulation s t x‖ ≤
      offSupportOscillatoryConstant /
        (modulation ^ 2 * t ^ 2 * |x - s| ^ 3) := by
  let a := |x - s|
  let D := (4 * Real.pi * modulation) ^ 2
  let g : ℝ → ℝ := fun u ↦
    ((27 / a ^ 3) * |wavePacketSecondDeriv s t u| +
      (405 / a ^ 4) * |wavePacketDeriv s t u| +
      (1944 / a ^ 5) * |wavePacket s t u|) / D
  have ha : 0 < a :=
    lt_of_lt_of_le (half_pos ht) (half_length_le_abs_center ht hx)
  have hD : 0 < D := by dsimp [D]; positivity
  have hpabs : Integrable (fun u : ℝ ↦ |wavePacket s t u|) := by
    simpa only [Real.norm_eq_abs] using (wavePacket_integrable s ht).norm
  have hg : Integrable g := by
    dsimp only [g]
    exact ((((integrable_abs_wavePacketSecondDeriv s ht).const_mul (27 / a ^ 3)).add
      ((integrable_abs_wavePacketDeriv s ht).const_mul (405 / a ^ 4))).add
        (hpabs.const_mul (1944 / a ^ 5))).div_const D
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    dsimp only [g]
    positivity
  have hlr : s - t / 3 ≤ s + t / 3 := by linarith
  rw [offSupportOscillatoryAction_eq_twiceIntegrated hmod ht hx]
  calc
    ‖∫ u in (s - t / 3)..(s + t / 3),
        ibpAmplitude1Deriv modulation x (wavePacket s t)
          (wavePacketDeriv s t) (wavePacketSecondDeriv s t) u *
            phase (modulation * (x - u) ^ 2)‖ ≤
        ∫ u in (s - t / 3)..(s + t / 3), g u := by
      apply intervalIntegral.norm_integral_le_of_norm_le hlr
      · filter_upwards with u hu
        have hsep := third_interval_separation ht hx (by
          rw [uIcc_of_le hlr]
          exact ⟨hu.1.le, hu.2⟩)
        have hpoint := norm_ibpAmplitude1Deriv_le
          (p := wavePacket s t) (p' := wavePacketDeriv s t)
          (p'' := wavePacketSecondDeriv s t) hmod ha hsep
        dsimp only [g, a, D]
        convert hpoint using 1; ring
      · exact hg.intervalIntegrable
    _ ≤ ∫ u : ℝ, g u := by
      rw [intervalIntegral.integral_of_le hlr]
      exact setIntegral_le_integral hg (ae_of_all _ hg0)
    _ = (((27 / a ^ 3) * (t⁻¹ ^ 2 * ∫ v : ℝ, |iteratedDeriv 2 baseBump v|) +
          (405 / a ^ 4) * (t⁻¹ * ∫ v : ℝ, |deriv baseBump v|) +
          (1944 / a ^ 5)) / D) := by
      dsimp only [g]
      have hsum :
          (∫ u : ℝ,
              (27 / a ^ 3) * |wavePacketSecondDeriv s t u| +
                (405 / a ^ 4) * |wavePacketDeriv s t u| +
                (1944 / a ^ 5) * |wavePacket s t u|) =
            (∫ u : ℝ, (27 / a ^ 3) * |wavePacketSecondDeriv s t u|) +
              (∫ u : ℝ, (405 / a ^ 4) * |wavePacketDeriv s t u|) +
              (∫ u : ℝ, (1944 / a ^ 5) * |wavePacket s t u|) := by
        have hab := integral_add
          ((integrable_abs_wavePacketSecondDeriv s ht).const_mul (27 / a ^ 3))
          ((integrable_abs_wavePacketDeriv s ht).const_mul (405 / a ^ 4))
        have habc := integral_add
          (((integrable_abs_wavePacketSecondDeriv s ht).const_mul (27 / a ^ 3)).add
            ((integrable_abs_wavePacketDeriv s ht).const_mul (405 / a ^ 4)))
          (hpabs.const_mul (1944 / a ^ 5))
        simpa only [Pi.add_apply, hab] using habc
      rw [integral_div, hsum,
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_abs_wavePacketSecondDeriv s ht,
        integral_abs_wavePacketDeriv s ht]
      have hpint : (∫ u : ℝ, |wavePacket s t u|) = 1 := by
        calc
          (∫ u : ℝ, |wavePacket s t u|) = ∫ u : ℝ, wavePacket s t u := by
            apply integral_congr_ae
            exact ae_of_all _ fun u ↦ abs_of_nonneg (wavePacket_nonneg s u ht)
          _ = 1 := wavePacket_integral s ht
      rw [hpint]
      ring
    _ ≤ offSupportOscillatoryConstant /
        (modulation ^ 2 * t ^ 2 * |x - s| ^ 3) := by
      have hdist : t / 2 ≤ a := by
        exact half_length_le_abs_center ht hx
      have hta : t ≤ 2 * a := by linarith
      have ht2a2 : t ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      have hI1 : 0 ≤ ∫ v : ℝ, |deriv baseBump v| :=
        integral_nonneg fun _ ↦ abs_nonneg _
      have hI2 : 0 ≤ ∫ v : ℝ, |iteratedDeriv 2 baseBump v| :=
        integral_nonneg fun _ ↦ abs_nonneg _
      have hlinear :
          405 * (∫ v : ℝ, |deriv baseBump v|) * t ≤
            810 * (∫ v : ℝ, |deriv baseBump v|) * a := by
        have h := mul_le_mul_of_nonneg_left hta
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 405) hI1)
        nlinarith
      have hconstant : 1944 * t ^ 2 ≤ 7776 * a ^ 2 := by
        nlinarith
      dsimp only [D]
      change _ ≤ offSupportOscillatoryConstant /
        (modulation ^ 2 * t ^ 2 * a ^ 3)
      unfold offSupportOscillatoryConstant
      field_simp [ne_of_gt hmod, ne_of_gt ht, ne_of_gt ha, Real.pi_ne_zero]
      nlinarith

end QuadraticCarleson
