/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketLowBoundPropagation

@[expose] public section

/-! Pointwise and partial-sum consequences of the one global scale
choice, ready for a finite-prefix packet induction. -/

noncomputable section

namespace EulerPacketInductionScales.Scales

open Real Finset EulerScale EulerBaseDatum EulerPacketLowConstants
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleActual EulerPacketSourceScaleGuards
  EulerPacketBaseGuardScales EulerPacketPressureScale EulerParentRenewalScale
  EulerPacketUniformSource EulerPacketSourceFrequency

variable {c B : ℝ} (S : Scales c B)

theorem x_one : 1 ≤ S.X := (by norm_num : (1 : ℝ) ≤ 8).trans S.x_large
theorem x_pos : 0 < S.X := zero_lt_one.trans_le S.x_one
theorem j_one : 1 ≤ S.J := by have h := S.stage_large; omega

theorem sequence_one (n : ℕ) : 1 ≤ scaleSequence S.J S.X n :=
  quadratic_growth_one_le S.J S.j_one (scaleSequence S.J S.X) S.x_one
    (scaleSequence_succ S.J S.X) n

theorem previousShear_one (n : ℕ) : 1 ≤ previousShear S.J S.X n :=
  EulerNormalPacketParameters.previousShear_one S.J S.j_one S.X S.x_one n

theorem shear_one (n : ℕ) : 1 ≤ shear S.J S.X n := S.previousShear_one (n+1)

theorem spike_pos (n : ℕ) : 0 < spike S.J S.X n := exp_pos _

theorem spike_one (n : ℕ) : spike S.J S.X n ≤ 1 := by
  unfold spike
  apply exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (zero_le_one.trans (S.sequence_one n)))
    (pow_nonneg (Nat.cast_nonneg _) _)

theorem support_pos (n : ℕ) : 0 < supportScale S.J S.X n := exp_pos _

theorem support_one (n : ℕ) : supportScale S.J S.X n ≤ 1 := by
  unfold supportScale
  apply exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (zero_le_one.trans (S.sequence_one n)))
    (rpow_nonneg (Nat.cast_nonneg _) _)

theorem previousFrequency_one (n : ℕ) : 1 ≤ previousFrequency S.J S.D S.X n := by
  cases n with
  | zero => exact S.first.frequency.one_le
  | succ n => exact (S.normal_frequency n).one_le

theorem priorError_nonneg (n : ℕ) : 0 ≤ priorError S.J S.D S.X n :=
  rpow_nonneg (zero_le_one.trans (S.previousFrequency_one n)) _

theorem priorError_one (n : ℕ) : priorError S.J S.D S.X n ≤ 1 := by
  cases n with
  | zero => exact S.first.error_small
  | succ n => exact (S.correction_series.term_le n).trans (S.delta_small.trans (by norm_num))

theorem shear_separation (n : ℕ) :
    previousShear S.J S.X n^2 ≤ shear S.J S.X n/4 := by
  have hp := (actualParentRatio_le S.J S.j_one S.X S.x_pos S.actual.initial_shear n).trans
    ((S.actual.normal.parent.term_le n).trans (S.delta_small.trans (by norm_num : (1 : ℝ)/16 ≤
      1/4)))
  have hh : 0 < shear S.J S.X n := exp_pos _
  have h := (div_le_iff₀ hh).mp hp
  linarith only [h]

theorem olderShear_le (n : ℕ) : olderShear S.J S.X n ≤ previousShear S.J S.X n := by
  cases n with
  | zero => exact S.previousShear_one 0
  | succ n =>
    have hp := S.previousShear_one n
    have hs := S.shear_separation n
    change previousShear S.J S.X n ≤ shear S.J S.X n
    nlinarith only [hp,hs,sq_nonneg (previousShear S.J S.X n-1)]

theorem frequency_cost (n : ℕ) :
    (EulerNormalPacketParameters.frequencySpec 4).cost S.J (scaleSequence S.J S.X) n ≤ 1 :=
  (S.frequency_series.term_le n).trans (S.delta_small.trans (by norm_num))

theorem source_frequency (n : ℕ) (P : ℝ) (hP : 1 ≤ P)
    (hPE : P ≤ EulerNormalPacketParameters.envelope S.J 4 S.X n) :
    frequencyConstant*P^frequencyPower ≤ smallPower (frequency S.J S.X n) :=
  EulerNormalPacketParameters.frequency_guard S.J 4 S.X P n hP hPE (S.frequency_cost n)

theorem secondary_frequency (n : ℕ) (K : ℝ)
    (hK : K ≤ previousFrequency S.J S.D S.X n^80) :
    K ≤ frequency S.J S.X n ∧
      (supportScale S.J S.X n)⁻¹ ≤ (frequency S.J S.X n)^(3/4 : ℝ) :=
  EulerNormalPacketParameters.secondary_frequency_guards S.J S.D (by have h := S.stage_large; omega)
    4 S.X K S.x_one n S.actual.initial_frequency hK (S.frequency_cost n)
    (S.normal_frequency n).one_le

theorem initial_partial_sum (n : ℕ) :
    ∑ i ∈ range n, initialIncrement S.J S.X i ≤ 2*S.δ := finite_sum_le S.initial_series n

theorem pressure_partial_sum (n : ℕ) :
    ∑ i ∈ range n, pressureIncrement S.J S.X i ≤ 3*S.δ := finite_sum_le S.pressure_series n

theorem activation_small {n : ℕ} (hn : n ≠ 0) :
    frameConstant*(1+olderShear S.J S.X n)+priorError S.J S.D S.X n ≤
      activationMargin*previousShear S.J S.X n := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    exact activation_smallness S.j_one frame_properties.1 S.x_one S.actual
      (S.activation_series.weaken S.delta_activation) (priorError S.J S.D S.X (n+1))
      (S.priorError_one (n+1)) n

theorem localized_guard (T K Be Bc : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
    (hKcap : K ≤ initialCoefficientCost+1) (hBecap : Be ≤ initialCoefficientCost+1)
    (hBccap : Bc ≤ gradientConstant*S.X^1000+2) (hTcap : T ≤ baseHorizon S.J S.X) :
    K*(T^2/2)+Be*T+EulerMeanHarmonic.boundaryLocalizationC2*Bc*(baseRadius S.X)^3*T ≤ 1/2 :=
  EulerPacketLowBoundPropagation.localized_guard S.J S.X K Be Bc
    (initialCoefficientCost+1) (initialCoefficientCost+1) gradientConstant
    EulerMeanHarmonic.boundaryLocalizationC2 T hK hBe hBc hT
    EulerMeanHarmonic.boundaryLocalizationC2_nonneg (baseRadius_pos S.x_pos).le
    hKcap hBecap hBccap hTcap S.localized

end EulerPacketInductionScales.Scales
