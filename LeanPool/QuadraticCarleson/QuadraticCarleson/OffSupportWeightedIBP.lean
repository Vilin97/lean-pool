/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportOscillatory
public import LeanPool.QuadraticCarleson.QuadraticCarleson.OffSupportPacketDerivatives

/-!
# Weighted off-support integration by parts

The exact one-step recurrence for arbitrary packet derivatives and denominator
powers. All integrations by parts take place strictly away from the pole.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped Interval

namespace QuadraticCarleson

/-- The complex coefficient multiplying the spatial displacement when differentiating the
quadratic phase. -/
noncomputable def quadraticOscillatoryCoeff (lam : ℝ) : ℂ :=
  ((-(4 * Real.pi * lam) : ℝ) : ℂ) * Complex.I

theorem quadraticOscillatoryCoeff_ne_zero {lam : ℝ} (hlam : lam ≠ 0) :
    quadraticOscillatoryCoeff lam ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hlam)))
    Complex.I_ne_zero

theorem norm_quadraticOscillatoryCoeff (lam : ℝ) :
    ‖quadraticOscillatoryCoeff lam‖ = 4 * Real.pi * |lam| := by
  simp only [quadraticOscillatoryCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_neg, abs_mul, abs_of_nonneg Real.pi_pos.le]
  norm_num

/-- The oscillatory action with a differentiated wave packet and an inverse-power spatial
weight. -/
noncomputable def offSupportWeightedAction (lam : ℝ) (r q : ℕ) (s t x : ℝ) : ℂ :=
  ∫ u : ℝ, (iteratedWavePacketDeriv r s t u : ℂ) *
    phase (lam * (x - u) ^ 2) / ((x - u : ℝ) : ℂ) ^ q

private theorem hasDerivAt_weightedAmplitude (q : ℕ)
    {x u : ℝ} {p p' : ℝ → ℝ} (hxu : x - u ≠ 0)
    (hp : HasDerivAt p (p' u) u) :
    HasDerivAt (fun v : ℝ ↦ (p v : ℂ) / ((x - v : ℝ) : ℂ) ^ (q + 1))
      ((p' u : ℂ) / ((x - u : ℝ) : ℂ) ^ (q + 1) +
        (q + 1 : ℂ) * (p u : ℂ) / ((x - u : ℝ) : ℂ) ^ (q + 2)) u := by
  have hz : HasDerivAt (fun v : ℝ ↦ ((x - v : ℝ) : ℂ)) (-1 : ℂ) u := by
    convert ((hasDerivAt_const u x).sub (hasDerivAt_id u)).ofReal_comp using 1 <;>
      norm_num
  have hzc := Complex.ofReal_ne_zero.mpr hxu
  apply ((hp.ofReal_comp).div (hz.pow (q + 1)) (pow_ne_zero _ hzc)).congr_deriv
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply, pow_succ]
  field_simp
  ring

private theorem weighted_interval_integration_by_parts (q : ℕ)
    {lam x l r : ℝ} {p p' : ℝ → ℝ} (hlam : lam ≠ 0)
    (hxu : ∀ u ∈ uIcc l r, x - u ≠ 0)
    (hpcont : Continuous p) (hp'cont : Continuous p')
    (hp : ∀ u ∈ uIcc l r, HasDerivAt p (p' u) u)
    (hpl : p l = 0) (hpr : p r = 0) :
    (∫ u in l..r, (p u : ℂ) * phase (lam * (x - u) ^ 2) /
        ((x - u : ℝ) : ℂ) ^ q) =
      -(quadraticOscillatoryCoeff lam)⁻¹ *
        ((∫ u in l..r, (p' u : ℂ) * phase (lam * (x - u) ^ 2) /
          ((x - u : ℝ) : ℂ) ^ (q + 1)) +
        (q + 1 : ℂ) * (∫ u in l..r, (p u : ℂ) * phase (lam * (x - u) ^ 2) /
          ((x - u : ℝ) : ℂ) ^ (q + 2))) := by
  let Q : ℝ → ℂ := fun u ↦ phase (lam * (x - u) ^ 2)
  let Q' : ℝ → ℂ := fun u ↦ quadraticOscillatoryCoeff lam * ((x - u : ℝ) : ℂ) * Q u
  let A : ℝ → ℂ := fun u ↦ (p u : ℂ) / ((x - u : ℝ) : ℂ) ^ (q + 1)
  let A' : ℝ → ℂ := fun u ↦
    (p' u : ℂ) / ((x - u : ℝ) : ℂ) ^ (q + 1) +
      (q + 1 : ℂ) * (p u : ℂ) / ((x - u : ℝ) : ℂ) ^ (q + 2)
  have hQ : ∀ u ∈ uIcc l r, HasDerivAt Q (Q' u) u := by
    intro u hu
    apply (hasDerivAt_quadraticPhase lam x u).congr_deriv
    dsimp [Q', Q, quadraticOscillatoryCoeff]
    push_cast
    ring
  have hA : ∀ u ∈ uIcc l r, HasDerivAt A (A' u) u := by
    intro u hu
    exact hasDerivAt_weightedAmplitude q (hxu u hu) (hp u hu)
  have hQcont : Continuous Q := by dsimp [Q, phase]; fun_prop
  have hQ'cont : Continuous Q' := by dsimp [Q']; fun_prop
  have hdivcont (n : ℕ) (v : ℝ → ℝ) (hv : Continuous v) :
      ContinuousOn (fun u ↦ (v u : ℂ) / ((x - u : ℝ) : ℂ) ^ n) (uIcc l r) := by
    apply (Complex.continuous_ofReal.comp hv).continuousOn.div
      ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).pow n).continuousOn
    intro u hu
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hxu u hu))
  have hA'cont : ContinuousOn A' (uIcc l r) := by
    simpa only [A', Pi.add_def, mul_div_assoc] using (hdivcont (q + 1) p' hp'cont).add
      ((hdivcont (q + 2) p hpcont).const_mul (q + 1 : ℂ))
  have hFcont (n : ℕ) (v : ℝ → ℝ) (hv : Continuous v) :
      ContinuousOn (fun u ↦ (v u : ℂ) * Q u / ((x - u : ℝ) : ℂ) ^ n)
        (uIcc l r) := by
    simpa only [Pi.mul_def, div_mul_eq_mul_div] using
      (hdivcont n v hv).mul hQcont.continuousOn
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA hQ hA'cont.intervalIntegrable (hQ'cont.intervalIntegrable l r)
  have hAl : A l = 0 := by simp [A, hpl]
  have hAr : A r = 0 := by simp [A, hpr]
  have hsplit : (∫ u in l..r, A' u * Q u) =
      (∫ u in l..r, (p' u : ℂ) * Q u / ((x - u : ℝ) : ℂ) ^ (q + 1)) +
        (q + 1 : ℂ) *
          (∫ u in l..r, (p u : ℂ) * Q u / ((x - u : ℝ) : ℂ) ^ (q + 2)) := by
    have hfun : (fun u ↦ A' u * Q u) = fun u ↦
        (p' u : ℂ) * Q u / ((x - u : ℝ) : ℂ) ^ (q + 1) +
          (q + 1 : ℂ) * ((p u : ℂ) * Q u / ((x - u : ℝ) : ℂ) ^ (q + 2)) := by
      funext u
      dsimp [A']
      ring
    rw [hfun, intervalIntegral.integral_add (hFcont (q + 1) p' hp'cont).intervalIntegrable
      ((hFcont (q + 2) p hpcont).intervalIntegrable.const_mul _),
      intervalIntegral.integral_const_mul]
  calc
    _ = (quadraticOscillatoryCoeff lam)⁻¹ * (∫ u in l..r, A u * Q' u) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      have hzc := Complex.ofReal_ne_zero.mpr (hxu u hu)
      have hc := quadraticOscillatoryCoeff_ne_zero hlam
      dsimp only [A, Q', Q]
      simp only [pow_succ]
      field_simp
    _ = _ := by rw [hibp, hAl, hAr, hsplit]; dsimp [Q]; ring

private theorem weighted_integrand_support (r q : ℕ) {lam s t x : ℝ} (ht : 0 < t) :
    support (fun u : ℝ ↦ (iteratedWavePacketDeriv r s t u : ℂ) *
      phase (lam * (x - u) ^ 2) / ((x - u : ℝ) : ℂ) ^ q) ⊆
        Ioc (s - t / 3) (s + t / 3) := by
  intro u hu
  have hp : iteratedWavePacketDeriv r s t u ≠ 0 := by
    intro hp
    apply hu
    simp [hp]
  have hsupp := iteratedWavePacketDeriv_support r ht hp
  constructor <;> linarith [hsupp.1, hsupp.2]

theorem offSupportWeightedAction_step (r q : ℕ) {lam s t x : ℝ}
    (hlam : lam ≠ 0) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    offSupportWeightedAction lam r q s t x =
      -(quadraticOscillatoryCoeff lam)⁻¹ *
        (offSupportWeightedAction lam (r + 1) (q + 1) s t x +
          (q + 1 : ℂ) * offSupportWeightedAction lam r (q + 2) s t x) := by
  simp only [offSupportWeightedAction]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (weighted_integrand_support r q ht),
    ← intervalIntegral.integral_eq_integral_of_support_subset
      (weighted_integrand_support (r + 1) (q + 1) ht),
    ← intervalIntegral.integral_eq_integral_of_support_subset
      (weighted_integrand_support r (q + 2) ht)]
  apply weighted_interval_integration_by_parts q hlam
  · intro u hu
    have hsep := third_interval_separation ht hx hu
    have hdistpos : 0 < |x - s| :=
      lt_of_lt_of_le (half_pos ht) (half_length_le_abs_center ht hx)
    apply abs_pos.mp
    linarith
  · exact continuous_iteratedWavePacketDeriv r s t
  · exact continuous_iteratedWavePacketDeriv (r + 1) s t
  · intro u hu
    exact hasDerivAt_iteratedWavePacketDeriv r s ht.ne' u
  · exact iteratedWavePacketDeriv_left_third_eq_zero r s ht
  · exact iteratedWavePacketDeriv_right_third_eq_zero r s ht

theorem offSupportWeightedAction_norm_le_step (r q : ℕ) {lam s t x : ℝ}
    (hlam : lam ≠ 0) (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportWeightedAction lam r q s t x‖ ≤
      (‖offSupportWeightedAction lam (r + 1) (q + 1) s t x‖ +
        (q + 1 : ℝ) * ‖offSupportWeightedAction lam r (q + 2) s t x‖) /
          (4 * Real.pi * |lam|) := by
  rw [offSupportWeightedAction_step r q hlam ht hx, norm_mul, norm_neg, norm_inv,
    norm_quadraticOscillatoryCoeff]
  rw [div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  exact (norm_add_le _ _).trans (by
    rw [norm_mul, show (q + 1 : ℂ) = ((q + 1 : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast]
    simp)

theorem offSupportWeightedAction_norm_le_zero (r q : ℕ) {lam s t x : ℝ}
    (ht : 0 < t) (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportWeightedAction lam r q s t x‖ ≤
      (3 : ℝ) ^ q * (∫ v : ℝ, |iteratedDeriv r baseBump v|) /
        (t ^ r * |x - s| ^ q) := by
  let d := |x - s|
  let g : ℝ → ℝ := fun u ↦ ((3 : ℝ) ^ q / d ^ q) * |iteratedWavePacketDeriv r s t u|
  have hd : 0 < d :=
    lt_of_lt_of_le (half_pos ht) (half_length_le_abs_center ht hx)
  have hg : Integrable g :=
    (integrable_abs_iteratedWavePacketDeriv r s ht).const_mul _
  have hg0 : ∀ u, 0 ≤ g u := by intro u; dsimp [g]; positivity
  have hlr : s - t / 3 ≤ s + t / 3 := by linarith
  have hphase (a : ℝ) : ‖phase a‖ = 1 := by
    rw [phase]
    simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * a)
  rw [offSupportWeightedAction, ← intervalIntegral.integral_eq_integral_of_support_subset
    (weighted_integrand_support r q ht)]
  calc
    _ ≤ ∫ u in (s - t / 3)..(s + t / 3), g u := by
      apply intervalIntegral.norm_integral_le_of_norm_le hlr
      · filter_upwards with u hu
        have hsep : d / 3 ≤ |x - u| := third_interval_separation ht hx (by
          rw [uIcc_of_le hlr]
          exact ⟨hu.1.le, hu.2⟩)
        simp only [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          hphase, mul_one]
        calc
          |iteratedWavePacketDeriv r s t u| / |x - u| ^ q ≤
              |iteratedWavePacketDeriv r s t u| / (d / 3) ^ q :=
            div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos (by positivity) q)
              (pow_le_pow_left₀ (by positivity) hsep q)
          _ = g u := by
            dsimp [g]
            rw [div_pow]
            field_simp
      · exact hg.intervalIntegrable
    _ ≤ ∫ u : ℝ, g u := by
      rw [intervalIntegral.integral_of_le hlr]
      exact setIntegral_le_integral hg (ae_of_all _ hg0)
    _ = _ := by
      dsimp [g, d]
      rw [integral_const_mul, integral_abs_iteratedWavePacketDeriv r s ht, inv_pow]
      ring


end QuadraticCarleson
