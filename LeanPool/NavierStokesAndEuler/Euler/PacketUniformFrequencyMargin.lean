/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedSmallness
public import LeanPool.NavierStokesAndEuler.Euler.PacketGraphFlowFrequency

@[expose] public section

/-! Parent-independent frequency margins. Once every source cost is below
the same tiny power, these margins yield both small physical errors and
the genuine small-velocity flow guard. -/

noncomputable section

namespace EulerPacketSourceFrequency

open Real Filter EulerPacketCorrectionScalar

theorem smallPower_le_power (k p : ℝ) (hk : 1 ≤ k) (hp : theta/100 ≤ p) :
    smallPower k ≤ k^p := Real.rpow_le_rpow_of_exponent_le hk hp

theorem cost_div_le_inverse_half (C k : ℝ) (hk : 1 ≤ k) (hC : C ≤ smallPower k) :
    C/k ≤ k^(-(1/2 : ℝ)) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  apply (div_le_iff₀ hk0).mpr
  calc
    C ≤ k^(1/2 : ℝ) := hC.trans (smallPower_le_power k (1/2) hk (by norm_num [theta]))
    _ = k^(-(1/2 : ℝ))*k := by
      simpa only [show (-(1/2 : ℝ))+1=1/2 by norm_num,Real.rpow_one] using
        Real.rpow_add hk0 (-(1/2 : ℝ)) 1

theorem cost_delta_le (C k : ℝ) (hk : 1 ≤ k) (hC : C ≤ smallPower k)
    (hd : delta (expansion k) ≤ k^(-(3 : ℝ))) :
    C*delta (expansion k) ≤ k^(-(5/2 : ℝ)) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  calc
    _ ≤ k^(1/2 : ℝ)*k^(-(3 : ℝ)) :=
      mul_le_mul (hC.trans (smallPower_le_power k (1/2) hk (by norm_num [theta]))) hd
        (delta_pos _).le (Real.rpow_nonneg hk0.le _)
    _ = _ := by rw [← Real.rpow_add hk0]; norm_num

theorem cost_frequency_delta_le_inverse_half (C k : ℝ) (hk : 1 ≤ k)
    (hC : C ≤ smallPower k) (hd : delta (expansion k) ≤ k^(-(3 : ℝ))) :
    C*k*delta (expansion k) ≤ k^(-(1/2 : ℝ)) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  calc
    _ = (C*delta (expansion k))*k := by ring
    _ ≤ k^(-(5/2 : ℝ))*k := mul_le_mul_of_nonneg_right (cost_delta_le C k hk hC hd) hk0.le
    _ = k^(-(3/2 : ℝ)) := by
      simpa only [show (-(5/2 : ℝ))+1=-(3/2) by norm_num,Real.rpow_one] using
        (Real.rpow_add hk0 (-(5/2 : ℝ)) 1).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk (by norm_num)

theorem physical_error_le_inverse_quarter (C E k : ℝ) (hk : 1 ≤ k)
    (hC : C ≤ smallPower k) (hE : E ≤ smallPower k)
    (hd : delta (expansion k) ≤ k^(-(3 : ℝ))) (hroot : 2 ≤ k^(1/4 : ℝ)) :
    C/k+E*k*delta (expansion k) ≤ k^(-(1/4 : ℝ)) := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  calc
    _ ≤ k^(-(1/2 : ℝ))+k^(-(1/2 : ℝ)) :=
      add_le_add (cost_div_le_inverse_half C k hk hC) (cost_frequency_delta_le_inverse_half E k hk
        hE hd)
    _ = 2*k^(-(1/2 : ℝ)) := by ring
    _ ≤ k^(1/4 : ℝ)*k^(-(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hk0.le _)
    _ = _ := by rw [← Real.rpow_add hk0]; norm_num

theorem liftedAmplitude_small_of_costs (C E R T k : ℝ) (hk : 1 ≤ k)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hC : C ≤ smallPower k) (hE : E ≤ smallPower k)
    (hRw : R ≤ smallPower k) (hTw : T ≤ smallPower k)
    (hd : delta (expansion k) ≤ k^(-(3 : ℝ))) (hroot : 16 ≤ k^(1/4 : ℝ)) :
    liftedAmplitude C E k ≤ 2*k^(-(1/2 : ℝ)) ∧
    liftedAmplitude C E k*R*T ≤ 1/8 := by
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hcoef := smallPower_le_power k (1/8) hk (by norm_num [theta])
  have hRk := hRw.trans hcoef
  have hTk := hTw.trans hcoef
  have ha : liftedAmplitude C E k ≤ 2*k^(-(1/2 : ℝ)) := by
    have he := (cost_delta_le E k hk hE hd).trans
      (Real.rpow_le_rpow_of_exponent_le hk (by norm_num : -(5/2 : ℝ) ≤ -(1/2 : ℝ)))
    unfold liftedAmplitude
    linarith only [cost_div_le_inverse_half C k hk hC,he]
  refine ⟨ha,?_⟩
  calc
    _ ≤ (2*k^(-(1/2 : ℝ)))*R*T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hR) hT
    _ ≤ (2*k^(-(1/2 : ℝ)))*k^(1/8 : ℝ)*k^(1/8 : ℝ) := by gcongr
    _ = 2*k^(-(1/4 : ℝ)) := by
      calc
        _ = 2*(k^(-(1/2 : ℝ))*(k^(1/8 : ℝ)*k^(1/8 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hk0,← Real.rpow_add hk0]; norm_num
    _ ≤ 1/8 := by
      rw [Real.rpow_neg hk0.le,← div_eq_mul_inv]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hk0 _)).mpr (by linarith)

/-- This one numerical threshold is independent of all parent fields,
all source costs and all stages of the iteration. -/
theorem universal_margin_eventually (K : ℝ) :
    ∀ᶠ k : ℝ in atTop, 4 ≤ k ∧ 64 ≤ expansion k ∧ 1 ≤ Real.log k ∧
      delta (expansion k) ≤ k^(-(3 : ℝ)) ∧ 16 ≤ k^(1/4 : ℝ) ∧
      max 71 K ≤ k^(1/24 : ℝ) := by
  filter_upwards [fixed_costs_eventually (∅ : Finset ℝ),
    correction_eventually_lt_inverse_power 1 3,
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).eventually_ge_atTop 16,
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/24)).eventually_ge_atTop (max 71 K)]
    with k hbase hd hroot hK
  exact ⟨hbase.1,hbase.2.1,hbase.2.2.1,by simpa only [one_mul] using hd.le,hroot,hK⟩

end EulerPacketSourceFrequency
