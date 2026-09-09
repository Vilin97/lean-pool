/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlotColoring
public import LeanPool.NavierStokesAndEuler.NavierStokes.Scaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# The actual native chart scales

The floor index is the one defined from the manuscript's logarithmic formula
in `SlotColoring`. This module derives the coefficient comparisons in (25),
their reciprocal bounds, the rounded carrier scale, and polynomial/exponential
decay along the actual dyadic sequence.
-/

noncomputable section

namespace NavierStokes.ChartScales

open Filter
open scoped Topology

abbrev Tg : ℝ := SlotColoring.coverGrowth
def Lambda : ℝ := 4 - Real.sqrt 2
def rho : ℝ := Real.log Lambda / Real.log Tg
def kappa : ℝ := 1 / 100000
def radialExponent (h : ℝ) : ℝ := 2 * ((1 + h) * rho - h * kappa)

abbrev Q (n : ℕ) : ℝ := SlotColoring.dyadicQ n
def S (n : ℕ) : ℝ := (n : ℝ) ^ 2
def epsilon (h : ℝ) (n : ℕ) : ℝ := Q n ^ h
abbrev nativeIndex (h : ℝ) (n : ℕ) : ℕ := SlotColoring.nativeIndex h n

def timeCoefficient (h : ℝ) (n : ℕ) : ℝ := Tg ^ nativeIndex h n * Q n ^ (1 + h)
def radialCoefficient (h : ℝ) (n : ℕ) : ℝ :=
  Lambda ^ nativeIndex h n * Q n ^ (radialExponent h / 2)

theorem sqrt_two_lt_two : Real.sqrt (2 : ℝ) < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

theorem Tg_one_lt : 1 < Tg := by
  unfold Tg SlotColoring.coverGrowth
  linarith [Real.sqrt_nonneg (2 : ℝ)]

theorem Tg_pos : 0 < Tg := lt_trans zero_lt_one Tg_one_lt
theorem log_Tg_pos : 0 < Real.log Tg := SlotColoring.log_coverGrowth_pos

theorem Lambda_two_lt : 2 < Lambda := by
  unfold Lambda
  linarith [sqrt_two_lt_two]

theorem Lambda_pos : 0 < Lambda := lt_trans (by norm_num) Lambda_two_lt
theorem log_Lambda_pos : 0 < Real.log Lambda := Real.log_pos (by linarith [Lambda_two_lt])

/-- A coarse explicit bound suffices to show that the radial power is positive. -/
theorem rho_lower : (1 / 3 : ℝ) ≤ rho := by
  have hl : Real.log (2 : ℝ) ≤ Real.log Lambda := Real.log_le_log (by norm_num) Lambda_two_lt.le
  have ht : Tg ≤ (2 : ℝ) ^ 3 := by
    unfold Tg SlotColoring.coverGrowth
    norm_num
    linarith [sqrt_two_lt_two]
  have htlog := Real.log_le_log Tg_pos ht
  rw [Real.log_pow] at htlog
  norm_num at htlog
  unfold rho
  apply (le_div_iff₀ log_Tg_pos).mpr
  linarith

theorem rho_pos : 0 < rho := lt_of_lt_of_le (by norm_num) rho_lower

/-- This includes the manuscript's range `0<h<1/2`, and in fact every `h≥0`. -/
theorem radialExponent_pos (h : ℝ) (hh : 0 ≤ h) : 0 < radialExponent h := by
  have hk : kappa < rho := by unfold kappa; linarith [rho_lower]
  have hm := mul_nonneg hh (sub_nonneg.mpr hk.le)
  unfold radialExponent
  nlinarith [rho_pos]

theorem Q_pos (n : ℕ) : 0 < Q n := Real.rpow_pos_of_pos (by norm_num) _

theorem Q_le_one (n : ℕ) : Q n ≤ 1 := by
  calc
    Q n ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg n))
    _ = 1 := Real.rpow_zero _

theorem S_pos {n : ℕ} (hn : 1 ≤ n) : 0 < S n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact pow_pos hn' _

theorem epsilon_pos (h : ℝ) (n : ℕ) : 0 < epsilon h n := Real.rpow_pos_of_pos (Q_pos n) _

theorem epsilon_le_one (h : ℝ) (hh : 0 ≤ h) (n : ℕ) : epsilon h n ≤ 1 :=
  Real.rpow_le_one (Q_pos n).le (Q_le_one n) hh

theorem timeCoefficient_pos (h : ℝ) (n : ℕ) : 0 < timeCoefficient h n :=
  mul_pos (pow_pos Tg_pos _) (Real.rpow_pos_of_pos (Q_pos n) _)

theorem radialCoefficient_pos (h : ℝ) (n : ℕ) : 0 < radialCoefficient h n :=
  mul_pos (pow_pos Lambda_pos _) (Real.rpow_pos_of_pos (Q_pos n) _)

theorem Tg_rpow_rho : Tg ^ rho = Lambda := by
  rw [Real.rpow_def_of_pos Tg_pos]
  have he : Real.log Tg * rho = Real.log Lambda := by
    unfold rho
    field_simp [ne_of_gt log_Tg_pos]
  rw [he, Real.exp_log Lambda_pos]

theorem Lambda_pow_eq (n : ℕ) : Lambda ^ n = ((Tg ^ n : ℝ) ^ rho) := by
  calc
    Lambda ^ n = (Tg ^ rho) ^ n := by rw [Tg_rpow_rho]
    _ = Tg ^ (rho * (n : ℝ)) := (Real.rpow_mul_natCast Tg_pos.le rho n).symm
    _ = Tg ^ ((n : ℝ) * rho) := by rw [mul_comm]
    _ = (Tg ^ n : ℝ) ^ rho := Real.rpow_natCast_mul Tg_pos.le n rho

private theorem growth_at_nativeArgument (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Tg ^ SlotColoring.nativeArgument h n = Q n ^ (-1 - h) / S n := by
  have ha : 0 < Q n ^ (-1 - h) / S n := div_pos (Real.rpow_pos_of_pos (Q_pos n) _) (S_pos hn)
  change Tg ^ (Real.log (Q n ^ (-1 - h) / S n) / Real.log Tg) = _
  rw [Real.rpow_def_of_pos Tg_pos]
  have he : Real.log Tg * (Real.log (Q n ^ (-1 - h) / S n) / Real.log Tg) =
      Real.log (Q n ^ (-1 - h) / S n) := by field_simp [ne_of_gt log_Tg_pos]
  rw [he, Real.exp_log ha]

theorem native_power_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    Tg ^ nativeIndex h n ≤ Q n ^ (-1 - h) / S n ∧
      Q n ^ (-1 - h) / S n ≤ Tg * Tg ^ nativeIndex h n := by
  have hlo := Nat.floor_le (SlotColoring.nativeArgument_nonneg h hh hn)
  have hhi := (Nat.lt_floor_add_one (SlotColoring.nativeArgument h n)).le
  have lo := Real.rpow_le_rpow_of_exponent_le Tg_one_lt.le hlo
  have hi := Real.rpow_le_rpow_of_exponent_le Tg_one_lt.le hhi
  rw [growth_at_nativeArgument h (by omega), Real.rpow_natCast] at lo
  rw [growth_at_nativeArgument h (by omega), Real.rpow_add Tg_pos,
    Real.rpow_natCast, Real.rpow_one] at hi
  exact ⟨lo, by simpa only [nativeIndex, SlotColoring.nativeIndex, mul_comm] using hi⟩

private theorem target_times_Q (h : ℝ) {n : ℕ} :
    (Q n ^ (-1 - h) / S n) * Q n ^ (1 + h) = 1 / S n := by
  calc
    (Q n ^ (-1 - h) / S n) * Q n ^ (1 + h) =
        (Q n ^ (-1 - h) * Q n ^ (1 + h)) / S n := by ring
    _ = 1 / S n := by
      rw [← Real.rpow_add (Q_pos n)]
      have he : (-1 - h) + (1 + h) = 0 := by ring
      rw [he, Real.rpow_zero]

/-- The actual floor index gives the complete `c_i` comparison in (25). -/
theorem timeCoefficient_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    1 / (Tg * S n) ≤ timeCoefficient h n ∧ timeCoefficient h n ≤ 1 / S n := by
  obtain ⟨hl, hu⟩ := native_power_bounds h hh hn
  have hQ := (Real.rpow_pos_of_pos (Q_pos n) (1 + h)).le
  constructor
  · have hu' := mul_le_mul_of_nonneg_right hu hQ
    rw [target_times_Q] at hu'
    have hdiv : (1 / S n) / Tg ≤ timeCoefficient h n := by
      apply (div_le_iff₀ Tg_pos).mpr
      simpa [timeCoefficient, mul_assoc, mul_comm, mul_left_comm] using hu'
    simpa only [div_div, mul_comm] using hdiv
  · have hl' := mul_le_mul_of_nonneg_right hl hQ
    simpa only [target_times_Q, timeCoefficient] using hl'

/-- The radial coefficient is an exact power of the time coefficient,
with the explicit small-viscosity loss. -/
theorem radialCoefficient_eq (h : ℝ) (n : ℕ) :
    radialCoefficient h n = epsilon h n ^ (-kappa) * timeCoefficient h n ^ rho := by
  have he : epsilon h n ^ (-kappa) = Q n ^ (-h * kappa) := by
    unfold epsilon
    rw [← Real.rpow_mul (Q_pos n).le]
    congr 1
    ring
  have hc : timeCoefficient h n ^ rho =
      (Tg ^ nativeIndex h n : ℝ) ^ rho * Q n ^ ((1 + h) * rho) := by
    unfold timeCoefficient
    rw [Real.mul_rpow (pow_nonneg Tg_pos.le _) (Real.rpow_nonneg (Q_pos n).le _),
      ← Real.rpow_mul (Q_pos n).le]
  rw [he, hc]
  unfold radialCoefficient
  rw [Lambda_pow_eq]
  have hd : radialExponent h / 2 = (-h * kappa) + (1 + h) * rho := by
    unfold radialExponent
    ring
  rw [hd, Real.rpow_add (Q_pos n)]
  ring

private theorem one_div_S_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 / S n) ^ rho = S n ^ (-rho) := by
  rw [Real.div_rpow zero_le_one (S_pos hn).le, Real.one_rpow,
    Real.rpow_neg (S_pos hn).le]
  exact one_div _

private theorem one_div_TS_rpow {n : ℕ} (hn : 1 ≤ n) :
    (1 / (Tg * S n)) ^ rho = S n ^ (-rho) / Lambda := by
  rw [Real.div_rpow zero_le_one (mul_pos Tg_pos (S_pos hn)).le, Real.one_rpow,
    Real.mul_rpow Tg_pos.le (S_pos hn).le, Tg_rpow_rho, Real.rpow_neg (S_pos hn).le]
  simp [div_eq_mul_inv, mul_comm]

/-- The full `M_i` comparison in (25), obtained from the actual native index. -/
theorem radialCoefficient_bounds (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    epsilon h n ^ (-kappa) * S n ^ (-rho) / Lambda ≤ radialCoefficient h n ∧
      radialCoefficient h n ≤ epsilon h n ^ (-kappa) * S n ^ (-rho) := by
  obtain ⟨hcL, hcU⟩ := timeCoefficient_bounds h hh hn
  have hp := (Real.rpow_pos_of_pos (epsilon_pos h n) (-kappa)).le
  have hl := Real.rpow_le_rpow (one_div_nonneg.mpr (mul_pos Tg_pos (S_pos (by omega))).le)
    hcL rho_pos.le
  have hu := Real.rpow_le_rpow (timeCoefficient_pos h n).le hcU rho_pos.le
  rw [one_div_TS_rpow (by omega)] at hl
  rw [one_div_S_rpow (by omega)] at hu
  rw [radialCoefficient_eq]
  constructor
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hl hp
  · exact mul_le_mul_of_nonneg_left hu hp

theorem timeCoefficient_inv_upper (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (timeCoefficient h n)⁻¹ ≤ Tg * S n := by
  have hl := (timeCoefficient_bounds h hh hn).1
  have hi := one_div_le_one_div_of_le (one_div_pos.mpr (mul_pos Tg_pos (S_pos (by omega)))) hl
  simpa only [one_div, inv_inv] using hi

theorem radialCoefficient_inv_upper (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (radialCoefficient h n)⁻¹ ≤ Lambda * epsilon h n ^ kappa * S n ^ rho := by
  have hl := (radialCoefficient_bounds h hh hn).1
  have hpos : 0 < epsilon h n ^ (-kappa) * S n ^ (-rho) / Lambda :=
    div_pos (mul_pos (Real.rpow_pos_of_pos (epsilon_pos h n) _)
      (Real.rpow_pos_of_pos (S_pos (by omega)) _)) Lambda_pos
  have hi := one_div_le_one_div_of_le hpos hl
  have hS : 0 < S n := S_pos (by omega)
  simpa [Real.rpow_neg (epsilon_pos h n).le, Real.rpow_neg hS.le,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hi

theorem timeCoefficient_inv_lower (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    S n ≤ (timeCoefficient h n)⁻¹ := by
  have hi := one_div_le_one_div_of_le (timeCoefficient_pos h n) (timeCoefficient_bounds h hh hn).2
  simpa only [one_div, inv_inv] using hi

def slotLength (r0 h : ℝ) (n : ℕ) : ℝ := 2 * r0 / timeCoefficient h n

/-- The native slot has length comparable to the actual slow scale `n²`. -/
theorem slotLength_bounds (r0 h : ℝ) (hr : 0 ≤ r0) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    2 * r0 * S n ≤ slotLength r0 h n ∧ slotLength r0 h n ≤ 2 * r0 * Tg * S n := by
  have hm : 0 ≤ 2 * r0 := by positivity
  have hl := mul_le_mul_of_nonneg_left (timeCoefficient_inv_lower h hh hn) hm
  have hu := mul_le_mul_of_nonneg_left (timeCoefficient_inv_upper h hh hn) hm
  exact ⟨by simpa only [slotLength, div_eq_mul_inv] using hl,
    by simpa only [slotLength, div_eq_mul_inv, mul_assoc] using hu⟩

/-- The carrier is the genuine rounded integer frequency used in the manuscript. -/
def carrier (h : ℝ) (n : ℕ) : ℕ := Scaling.carrierFrequency (epsilon h n)

theorem carrier_viscosity_bounds (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    1 ≤ epsilon h n * (carrier h n : ℝ) ^ 2 ∧
      epsilon h n * (carrier h n : ℝ) ^ 2 ≤ 4 := by
  obtain ⟨hl, hu, h4⟩ := Scaling.order_one_viscosity (epsilon_pos h n) (epsilon_le_one h hh n)
  exact ⟨hl, hu.trans h4⟩

theorem carrier_inv_bounds (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    Real.sqrt (epsilon h n) / 2 ≤ 1 / (carrier h n : ℝ) ∧
      1 / (carrier h n : ℝ) ≤ Real.sqrt (epsilon h n) :=
  Scaling.reciprocal_frequency_bounds (epsilon_pos h n) (epsilon_le_one h hh n)

theorem slow_power_epsilon_identity (h a b : ℝ) (n : ℕ) :
    S n ^ a * epsilon h n ^ b =
      (n : ℝ) ^ (2 * a) * Real.exp (-(h * b * Real.log 2) * (n : ℝ)) := by
  have hS : S n ^ a = (n : ℝ) ^ (2 * a) := by
    simpa only [S, Nat.cast_ofNat] using
      (Real.rpow_natCast_mul (Nat.cast_nonneg n) 2 a).symm
  have he : epsilon h n ^ b = Real.exp (-(h * b * Real.log 2) * (n : ℝ)) := by
    unfold epsilon
    rw [← Real.rpow_mul (Q_pos n).le]
    unfold Q SlotColoring.dyadicQ
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hS, he]

/-- Every fixed real power of the slow scale is dominated by every positive
power of the actual small-viscosity scale, provided `h>0`. -/
theorem slow_power_epsilon_tendsto_zero (h : ℝ) (hh : 0 < h) (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => S n ^ a * epsilon h n ^ b) atTop (𝓝 0) := by
  have hc : 0 < h * b * Real.log 2 :=
    mul_pos (mul_pos hh hb) (Real.log_pos (by norm_num))
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 * a) (h * b * Real.log 2) hc).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [slow_power_epsilon_identity, Function.comp_def] using ht

theorem eventually_slow_power_epsilon_lt (h : ℝ) (hh : 0 < h) (a b δ : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, S n ^ a * epsilon h n ^ b < δ :=
  (tendsto_order.1 (slow_power_epsilon_tendsto_zero h hh a b hb)).2 δ hδ

theorem exists_slow_power_epsilon_cutoff (h : ℝ) (hh : 0 < h) (a b δ : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, S n ^ a * epsilon h n ^ b < δ :=
  eventually_atTop.1 (eventually_slow_power_epsilon_lt h hh a b δ hb hδ)

/-- The rounding error `1/k`, multiplied by any fixed slow power, also
vanishes along the actual dyadic sequence. -/
theorem slow_power_div_carrier_tendsto_zero (h : ℝ) (hh : 0 < h) (a : ℝ) :
    Tendsto (fun n : ℕ => S n ^ a / (carrier h n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => div_nonneg (Real.rpow_nonneg (sq_nonneg (n : ℝ)) a) (Nat.cast_nonneg _))
    (g := fun n : ℕ => S n ^ a * epsilon h n ^ (1 / 2 : ℝ))
  · intro n
    calc
      S n ^ a / (carrier h n : ℝ) = S n ^ a * (1 / (carrier h n : ℝ)) := by ring
      _ ≤ S n ^ a * Real.sqrt (epsilon h n) :=
        mul_le_mul_of_nonneg_left (carrier_inv_bounds h hh.le n).2
          (Real.rpow_nonneg (sq_nonneg (n : ℝ)) a)
      _ = S n ^ a * epsilon h n ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
  · exact slow_power_epsilon_tendsto_zero h hh a (1 / 2) (by norm_num)

end NavierStokes.ChartScales
