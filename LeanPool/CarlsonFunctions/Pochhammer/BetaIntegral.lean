/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Probability.Distributions.Beta

/-!
# Further results about the Euler Beta integral

This file is a temporary home for results intended to accompany
`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`.
-/

open MeasureTheory

public noncomputable section

namespace Complex

/-- The scaled Beta kernel is interval-integrable on `[0, a]` under the usual convergence
conditions. -/
theorem intervalIntegrable_betaKernel_scaled {u v : ℂ}
    (hu : 0 < u.re) (hv : 0 < v.re) {a : ℝ} (ha : 0 ≤ a) :
    IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ (u - 1) * ((a : ℂ) - x) ^ (v - 1)) volume 0 a := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hf := betaIntegral_convergent hu hv
  have hcomp := hf.comp_mul_left (c := a⁻¹) (by finiteness) (by finiteness)
  have hz : (0 : ℝ) / a⁻¹ = 0 := by simp
  have hone : (1 : ℝ) / a⁻¹ = a := by field_simp [hpos.ne']
  have hI : IntervalIntegrable
      (fun x : ℝ => ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) *
        (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1)) volume 0 a := by
    simpa [hz, hone] using hcomp
  have hpow : IntervalIntegrable
      (fun x : ℝ => (a : ℂ) ^ (u - 1 + (v - 1)) *
        (((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) *
          (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1))) volume 0 a :=
    hI.const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at hpow ⊢
  refine hpow.congr_fun (fun x hx => ?_) measurableSet_Ioc
  have hx0 : 0 < x := hx.1
  have hxa : x ≤ a := hx.2
  have hx' : 0 ≤ a⁻¹ * x := by positivity
  have hx'' : a⁻¹ * x ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hpos]
    exact hxa
  have h1 : (x : ℂ) ^ (u - 1) =
      (a : ℂ) ^ (u - 1) * ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) := by
    have hxeq : x = a * (a⁻¹ * x) := by field_simp [hpos.ne']
    calc
      (x : ℂ) ^ (u - 1) = ((a * (a⁻¹ * x) : ℝ) : ℂ) ^ (u - 1) := by rw [← hxeq]
      _ = (a : ℂ) ^ (u - 1) * ((a⁻¹ * x : ℝ) : ℂ) ^ (u - 1) := by
        rw [ofReal_mul, mul_cpow_ofReal_nonneg ha hx']
  have h2 : ((a : ℂ) - x) ^ (v - 1) =
      (a : ℂ) ^ (v - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1) := by
    have hunit : 0 ≤ 1 - a⁻¹ * x := sub_nonneg.mpr hx''
    have hmul : a - x = a * (1 - a⁻¹ * x) := by field_simp [hpos.ne']
    calc
      ((a : ℂ) - x) ^ (v - 1) = ((a - x : ℝ) : ℂ) ^ (v - 1) := by simp
      _ = ((a * (1 - a⁻¹ * x) : ℝ) : ℂ) ^ (v - 1) := by rw [hmul]
      _ = (a : ℂ) ^ (v - 1) * ((1 - a⁻¹ * x : ℝ) : ℂ) ^ (v - 1) := by
        rw [ofReal_mul, mul_cpow_ofReal_nonneg ha hunit]
      _ = (a : ℂ) ^ (v - 1) * (1 - ((a⁻¹ * x : ℝ) : ℂ)) ^ (v - 1) := by simp
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  rw [h1, h2, mul_mul_mul_comm, ← mul_assoc, ← cpow_add _ _ ha0]
  ring

/-- Scaling identity for the `L¹` norm of the complex Beta kernel.  Unlike integrability of the
kernel, this pointwise change-of-scale identity needs no conditions on the real parts of the
parameters. -/
theorem integral_norm_betaKernel_scaled (u v : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ t in (0 : ℝ)..a, ‖(t : ℂ) ^ (u - 1) * ((a : ℂ) - t) ^ (v - 1)‖ =
      a ^ (u.re + v.re - 1) *
        ∫ t in (0 : ℝ)..1, ‖(t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)‖ := by
  have hchg :=
    intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => ‖(t : ℂ) ^ (u - 1) * ((a : ℂ) - t) ^ (v - 1)‖)
      (a := 0) (b := 1) a
  simp only [mul_zero, mul_one] at hchg
  rw [← hchg, smul_eq_mul]
  simp_rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  rw [← integral_const_mul, ← integral_const_mul]
  rw [setIntegral_congr_set (μ := volume) Ioo_ae_eq_Ioc.symm,
    setIntegral_congr_set (μ := volume) Ioo_ae_eq_Ioc.symm]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hpos : 0 < a * t := mul_pos ha ht0
  have hpos' : 0 < a * (1 - t) := mul_pos ha (sub_pos.mpr ht1)
  have h1 : ‖((a * t : ℝ) : ℂ) ^ (u - 1)‖ = a ^ (u.re - 1) * t ^ (u.re - 1) := by
    rw [norm_cpow_eq_rpow_re_of_pos hpos, Real.mul_rpow ha.le ht0.le, sub_re, one_re]
  have h2 : ‖((a : ℂ) - (a * t : ℝ)) ^ (v - 1)‖ =
      a ^ (v.re - 1) * (1 - t) ^ (v.re - 1) := by
    have h : (a : ℂ) - (a * t : ℝ) = ((a * (1 - t) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h, norm_cpow_eq_rpow_re_of_pos hpos', Real.mul_rpow ha.le (sub_nonneg.mpr ht1.le),
      sub_re, one_re]
  have h3 : ‖(t : ℂ) ^ (u - 1) * (1 - (t : ℂ)) ^ (v - 1)‖ =
      t ^ (u.re - 1) * (1 - t) ^ (v.re - 1) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
      show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht1), sub_re, one_re]
  have hrpow : a * a ^ (u.re - 1) * a ^ (v.re - 1) = a ^ (u.re + v.re - 1) := by
    have h1 : a * a ^ (u.re - 1) = a ^ u.re := by
      rw [mul_comm, ← Real.rpow_add_one ha.ne', sub_add_cancel]
    rw [h1, ← Real.rpow_add ha]
    ring_nf
  rw [norm_mul, h1, h2, h3]
  calc
    a * (a ^ (u.re - 1) * t ^ (u.re - 1) *
        (a ^ (v.re - 1) * (1 - t) ^ (v.re - 1))) =
        (a * a ^ (u.re - 1) * a ^ (v.re - 1)) *
          (t ^ (u.re - 1) * (1 - t) ^ (v.re - 1)) := by ring
    _ = a ^ (u.re + v.re - 1) *
        (t ^ (u.re - 1) * (1 - t) ^ (v.re - 1)) := by rw [hrpow]

end Complex

namespace Real

/-- The real Beta kernel is integrable on every nonnegative closed interval. -/
theorem integrableOn_Icc_rpow_mul_sub_rpow
    {a c s : ℝ} (ha : 0 < a) (hc : 0 < c) (hs : 0 ≤ s) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (s - t) ^ (c - 1)) (Set.Icc 0 s) := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mp
    (Complex.intervalIntegrable_betaKernel_scaled
      (u := (a : ℂ)) (v := (c : ℂ)) (by simpa) (by simpa) hs)
  refine IntegrableOn.congr_fun h.norm (fun t ht => ?_) measurableSet_Icc
  have hcast : (t : ℂ) ^ ((a : ℂ) - 1) * ((s : ℂ) - t) ^ ((c : ℂ) - 1) =
      ((t ^ (a - 1) * (s - t) ^ (c - 1) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2), Complex.ofReal_sub, Complex.ofReal_one]
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- The real Euler beta kernel is integrable on the closed unit interval. -/
theorem integrableOn_Icc_rpow_mul_one_sub_rpow
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (c - 1)) (Set.Icc 0 1) :=
  integrableOn_Icc_rpow_mul_sub_rpow ha hc zero_le_one

/-- The real Euler beta integral in set-integral form. -/
theorem integral_Icc_rpow_mul_one_sub_rpow
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ t in Set.Icc (0 : ℝ) 1, t ^ (a - 1) * (1 - t) ^ (c - 1) = ProbabilityTheory.beta a c := by
  have hbeta :
      (↑(∫ t in Set.Icc (0 : ℝ) 1,
        t ^ (a - 1) * (1 - t) ^ (c - 1)) : ℂ) =
        Complex.betaIntegral (a : ℂ) (c : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc]
    have hcast :
        (∫ t in Set.Ioc (0 : ℝ) 1,
          (↑(t ^ (a - 1) * (1 - t) ^ (c - 1)) : ℂ)) =
          ↑(∫ t in Set.Ioc (0 : ℝ) 1,
            t ^ (a - 1) * (1 - t) ^ (c - 1)) := integral_ofReal
    rw [← hcast]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    have ha_cast : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by norm_num
    have hc_cast : (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) := by norm_num
    have ht_cast : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by norm_num
    rw [ha_cast, hc_cast, ht_cast, ← Complex.ofReal_cpow (le_of_lt ht.1),
      ← Complex.ofReal_cpow (by linarith [ht.2])]
    norm_cast
  apply Complex.ofReal_injective
  rw [hbeta, Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (c : ℂ) (by simpa) (by simpa)]
  simp [ProbabilityTheory.beta, ← Complex.Gamma_ofReal]

/-- The scaled real Euler beta integral in set-integral form. -/
theorem integral_Icc_rpow_mul_sub_rpow
    {a c s : ℝ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) :
    ∫ t in Set.Icc (0 : ℝ) s, t ^ (a - 1) * (s - t) ^ (c - 1) = s ^ (a + c - 1) * ProbabilityTheory.beta a c := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.le]
  have hchange := intervalIntegral.smul_integral_comp_mul_left
    (f := fun t : ℝ => t ^ (a - 1) * (s - t) ^ (c - 1)) (a := 0) (b := 1) s
  simp only [smul_eq_mul, mul_zero, mul_one] at hchange
  rw [← hchange]
  have hs0 : 0 ≤ s := hs.le
  have hfactor : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (s * t) ^ (a - 1) * (s - s * t) ^ (c - 1) =
        s ^ (a + c - 2) * (t ^ (a - 1) * (1 - t) ^ (c - 1)) := by
    intro t ht
    rw [show s - s * t = s * (1 - t) by ring,
      Real.mul_rpow hs0 ht.1, Real.mul_rpow hs0 (sub_nonneg.mpr ht.2)]
    calc
      s ^ (a - 1) * t ^ (a - 1) * (s ^ (c - 1) * (1 - t) ^ (c - 1)) =
          (s ^ (a - 1) * s ^ (c - 1)) *
            (t ^ (a - 1) * (1 - t) ^ (c - 1)) := by ring
      _ = s ^ ((a - 1) + (c - 1)) *
            (t ^ (a - 1) * (1 - t) ^ (c - 1)) := by rw [Real.rpow_add hs]
      _ = s ^ (a + c - 2) * (t ^ (a - 1) * (1 - t) ^ (c - 1)) := by ring_nf
  have hintegral :
      ∫ t in (0 : ℝ)..1, (s * t) ^ (a - 1) * (s - s * t) ^ (c - 1) =
        ∫ t in (0 : ℝ)..1,
          s ^ (a + c - 2) * (t ^ (a - 1) * (1 - t) ^ (c - 1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hfactor t (by simpa [Set.uIcc_of_le zero_le_one] using ht)
  rw [hintegral,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc,
    integral_Icc_rpow_mul_one_sub_rpow ha hc]
  have hpow : s * s ^ (a + c - 2) = s ^ (a + c - 1) := by
    calc
      s * s ^ (a + c - 2) = s ^ (1 : ℝ) * s ^ (a + c - 2) := by
        rw [Real.rpow_one]
      _ = s ^ ((1 : ℝ) + (a + c - 2)) :=
        (Real.rpow_add hs (1 : ℝ) (a + c - 2)).symm
      _ = s ^ (a + c - 1) := by ring_nf
  rw [← mul_assoc, hpow]

/-- The nonnegative Beta integral on an arbitrary positive interval. -/
theorem lintegral_Icc_rpow_mul_sub_rpow {a c s : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) :
    ∫⁻ x in Set.Icc 0 s, ENNReal.ofReal (x ^ (a - 1) * (s - x) ^ (c - 1)) =
      ENNReal.ofReal (s ^ (a + c - 1) * ProbabilityTheory.beta a c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Icc_rpow_mul_sub_rpow ha hc hs.le)
    (by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.1 _)
        (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _))]
  rw [integral_Icc_rpow_mul_sub_rpow ha hc hs]

end Real

namespace MeasureTheory

/-- The beta integral at positive integer parameters, in a form convenient for simplex
monomial integrals. -/
theorem integral_Icc_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) 1, t ^ a * (1 - t) ^ b =
      (Nat.factorial a * Nat.factorial b : ℝ) / Nat.factorial (a + b + 1) := by
  have h := Real.integral_Icc_rpow_mul_one_sub_rpow
    (a := (a : ℝ) + 1) (c := (b : ℝ) + 1) (by positivity) (by positivity)
  have hsum : (a : ℝ) + 1 + ((b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  simpa only [add_sub_cancel_right, Real.rpow_natCast, ProbabilityTheory.beta,
    hsum, Real.Gamma_nat_eq_factorial] using h

end MeasureTheory

end
