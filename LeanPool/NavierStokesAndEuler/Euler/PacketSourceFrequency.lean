/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionScalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! The literal source truncation floor(k^ϑ), ϑ=10⁻⁶, meets the packet
and correction guards from finitely many fixed-cost bounds. -/

noncomputable section

namespace EulerPacketSourceFrequency

open Real Filter EulerPacketCoarseMajorant EulerPacketCorrectionScalar

def theta : ℝ := 1/1000000
def expansion (k : ℝ) : ℝ := k^theta
def truncation (k : ℝ) : ℕ := Nat.floor (expansion k)
def smallPower (k : ℝ) : ℝ := k^(theta/100)

theorem expansion_pos (k : ℝ) (hk : 0 < k) : 0 < expansion k :=
  Real.rpow_pos_of_pos hk _

theorem truncation_bounds (k : ℝ) (hk : 1 ≤ k) :
    1 ≤ truncation k ∧ expansion k-1 ≤ (truncation k : ℝ) ∧
      (truncation k : ℝ) ≤ expansion k := by
  have hx : 1 ≤ expansion k := Real.one_le_rpow hk (by norm_num [theta])
  exact ⟨(Nat.one_le_floor_iff _).mpr hx,(Nat.sub_one_lt_floor _).le,
    Nat.floor_le (zero_le_one.trans hx)⟩

theorem smallPower_le_expansion (k : ℝ) (hk : 1 ≤ k) : smallPower k ≤ expansion k :=
  Real.rpow_le_rpow_of_exponent_le hk (by norm_num [theta])

theorem smallPower_le_frequency (k : ℝ) (hk : 1 ≤ k) : smallPower k ≤ k := by
  simpa only [Real.rpow_one,smallPower] using
    Real.rpow_le_rpow_of_exponent_le (x := k) hk (by norm_num [theta] : theta/100 ≤ 1)

theorem smallPower_le_gradeCap (k : ℝ) (hk : 1 ≤ k) : smallPower k ≤ k^(1/100 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hk (by norm_num [theta])

theorem tailBase_frequency (R H C k : ℝ) (hC : 0 ≤ C) (hk : 1 ≤ k)
    (hc : tailPolynomialConstant R H C ≤ smallPower k) :
    tailBase R H C (truncation k) ≤ k^(1/100 : ℝ) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  obtain ⟨hn,_,hnx⟩ := truncation_bounds k hk
  calc
    _ ≤ tailPolynomialConstant R H C*(truncation k : ℝ)^222 :=
      tailBase_polynomial_bound R H C hC _ hn
    _ ≤ smallPower k*(expansion k)^222 :=
      mul_le_mul hc (pow_le_pow_left₀ (Nat.cast_nonneg _) hnx 222)
        (by positivity) (Real.rpow_pos_of_pos hk0 _).le
    _ = k^(theta/100+theta*222) := by
      unfold smallPower expansion
      rw [← Real.rpow_mul_natCast hk0.le,← Real.rpow_add hk0]
      norm_num
    _ ≤ k^(1/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk (by norm_num [theta])

/-- The source's very small power is below the exponential margin in
the error target exp(-sqrt(k^ϑ)). -/
theorem smallPower_le_exp_sqrt (k : ℝ) (hk : 0 < k) :
    smallPower k ≤ Real.exp (Real.sqrt (expansion k)) := by
  have hx : 0 ≤ expansion k := (expansion_pos k hk).le
  have hl := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have hlog : Real.log (expansion k)=theta*Real.log k := Real.log_rpow hk theta
  have hs := Real.sqrt_nonneg (expansion k)
  unfold smallPower
  rw [Real.rpow_def_of_pos hk]
  apply Real.exp_le_exp.mpr
  rw [hlog] at hl
  nlinarith only [hl,hs]

theorem correction_guards (C T D ρ0 k : ℝ) (hk : 1 ≤ k) (hρ : 0 < ρ0)
    (hX : 64 ≤ expansion k) (hlog : 1 ≤ Real.log k)
    (hgrowth : 12*C*T ≤ smallPower k)
    (hdrift : 8*C*T*D/ρ0 ≤ smallPower k)
    (herror : 8*C*T/ρ0 ≤ smallPower k) :
    2*residual k (expansion k)*Real.exp (3*C*T) ≤ delta (expansion k)/2 ∧
      2*C*(D/k+delta (expansion k))*T ≤ ρ0/2 := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  constructor
  · apply residual_small C T k (expansion k) hX hlog
    have hh := hgrowth.trans (smallPower_le_expansion k hk)
    linarith
  · apply radius_decay C T D ρ0 k (expansion k) hk0
    · have hh := (div_le_iff₀ hρ).mp (hdrift.trans (smallPower_le_frequency k hk))
      nlinarith only [hh]
    · have hh := (div_le_iff₀ hρ).mp (herror.trans (smallPower_le_exp_sqrt k hk0))
      nlinarith only [hh]

/-- Every finite list of fixed source costs fits the required very small
power after one sufficiently large frequency choice. -/
theorem fixed_costs_eventually (cost : Finset ℝ) :
    ∀ᶠ k : ℝ in atTop, 4 ≤ k ∧ 64 ≤ expansion k ∧ 1 ≤ Real.log k ∧
      ∀ c ∈ cost, c ≤ smallPower k := by
  have hpow := _root_.tendsto_rpow_atTop (by norm_num [theta] : 0 < theta/100)
  have hcost : ∀ᶠ k : ℝ in atTop, ∀ c ∈ cost, c ≤ smallPower k := by
    apply (Finset.eventually_all cost).mpr
    intro c _
    exact hpow.eventually_ge_atTop c
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    (_root_.tendsto_rpow_atTop (by norm_num [theta] : 0 < theta)).eventually_ge_atTop 64,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,hcost] with k hk hx hl hc
  exact ⟨hk,hx,hl,hc⟩

end EulerPacketSourceFrequency
