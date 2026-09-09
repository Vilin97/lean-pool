/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketNestedHorizons
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleGeometry
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Reciprocal history times fit the literal previous-frequency budget.
Only the first geometric step needs coupling and tilt bounds. All later
step lengths are nonnegative independently of any future frame invariant. -/

@[expose] public section


noncomputable section

namespace EulerParentHistoryFrequency

open Real EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceParameterScales EulerPacketSourceScaleActual
  EulerPacketNestedHorizons EulerPacketBaseGuardScales

theorem frequency_monotone (J : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 0 ≤ X) :
    Monotone (frequency J X) := by
  apply monotone_nat_of_le_succ
  intro n
  let j : ℝ := (J+n : ℕ)
  have hj2 : (2 : ℝ) ≤ j := by
    dsimp [j]
    exact_mod_cast (show 2 ≤ J+n by omega)
  have hj0 : 0 < j := by linarith only [hj2]
  have hx : 0 ≤ scaleSequence J X n :=
    hX.trans (sequence_initial_le J (by omega) X hX n)
  have hadd : ((J+(n+1) : ℕ) : ℝ)=j+1 := by
    dsimp [j]
    push_cast
    ring
  have hstep : j+1 ≤ j^2 := by nlinarith only [hj2,sq_nonneg (j-2)]
  have hsq : (j+1)^2 ≤ (j^2)^2 := pow_le_pow_left₀ (by positivity) hstep 2
  apply exp_le_exp.mpr
  change scaleSequence J X n/j^2 ≤ scaleSequence J X (n+1)/((J+(n+1) : ℕ) : ℝ)^2
  rw [scaleSequence_succ,hadd]
  apply (div_le_div_iff₀ (sq_pos_of_pos hj0) (sq_pos_of_pos (by positivity))).2
  calc
    scaleSequence J X n*(j+1)^2 ≤ scaleSequence J X n*(j^2)^2 :=
      mul_le_mul_of_nonneg_left hsq hx
    _ = (j^2*scaleSequence J X n)*j^2 := by ring

theorem initial_frequency_le_first (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) :
    X^D ≤ frequency J X 0 := by
  let j : ℝ := (J-1 : ℕ)
  have hj2 : (2 : ℝ) ≤ j := by
    dsimp [j]
    exact_mod_cast (show 2 ≤ J-1 by omega)
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hadd : (J : ℝ)=j+1 := by
    dsimp [j]
    exact_mod_cast (show J=J-1+1 by omega)
  have hstep : j+1 ≤ j^2 := by nlinarith only [hj2,sq_nonneg (j-2)]
  have hsq : (J : ℝ)^2 ≤ j^4 := by
    rw [hadd]
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hstep 2
  apply hbase.trans
  change exp (X/j^4) ≤ exp (X/(J : ℝ)^2)
  exact exp_le_exp.mpr (div_le_div_of_nonneg_left hX (sq_pos_of_pos hJ0) hsq)

theorem initial_frequency_le_previous (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    X^D ≤ previousFrequency J D X n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    exact (initial_frequency_le_first J D hJ X hX hbase).trans
      (frequency_monotone J (by omega) X hX (Nat.zero_le n))

theorem previousFrequency_one_le (J D : ℕ) (hJ : 3 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    1 ≤ previousFrequency J D X n :=
  (one_le_pow₀ hX).trans
    (initial_frequency_le_previous J D hJ X (zero_le_one.trans hX) hbase n)

theorem base_inverse_le_initial_frequency (J D : ℕ) (hJ : 1 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X) : 12/baseHorizon J X ≤ X^D := by
  have hx1 : 1 ≤ X := by linarith only [hX]
  have hx0 : 0 ≤ X := zero_le_one.trans hx1
  have hxpow : 2 ≤ X^1000 := hX.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (by decide : 1 ≤ 1000))
  calc
    12/baseHorizon J X ≤ 2*X^1000 := base_inverse_time_le J hJ X hx1
    _ ≤ X^1000*X^1000 := mul_le_mul_of_nonneg_right hxpow (pow_nonneg hx0 1000)
    _ = X^2000 := by rw [← pow_add]
    _ ≤ X^D := pow_le_pow_right₀ hx1 hD

theorem base_inverse_le_previous_frequency (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    12/baseHorizon J X ≤ previousFrequency J D X n :=
  (base_inverse_le_initial_frequency J D (by omega) hD X hX).trans
    (initial_frequency_le_previous J D hJ X (by linarith only [hX]) hbase n)

theorem base_inverse_le_previous_frequency_pow80 (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (X : ℝ) (hX : 2 ≤ X)
    (hbase : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    12/baseHorizon J X ≤ previousFrequency J D X n^80 := by
  have hk := previousFrequency_one_le J D hJ X (by linarith only [hX]) hbase n
  exact (base_inverse_le_previous_frequency J D hJ hD X hX hbase n).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hk (by decide : 1 ≤ 80))

theorem stepLength_nonneg (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 ≤ X)
    (a β : ℕ → ℝ) (n : ℕ) : 0 ≤ stepLength J X a β n :=
  div_nonneg (hX.trans (sequence_initial_le J hJ X hX (n+1))) (sqrt_nonneg _)

theorem activation_lower_of_initial (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    baseHorizon J X/12 ≤ activationTime J X a β n := by
  have hxnext : 0 ≤ scaleSequence J X 1 :=
    hX.le.trans (sequence_initial_le J hJ X hX.le 1)
  have hfirst : timeWidth J X 0/6 ≤ stepLength J X a β 0 :=
    (EulerPacketScaleGeometry.activation_time_bounds ha ha₂
      (previousShear_pos J hX 0) hX hxnext hβ hβ₂).1
  have hsum : stepLength J X a β 0 ≤ activationTime J X a β n := by
    apply Finset.single_le_sum
    · intro i _
      exact stepLength_nonneg J hJ X hX.le a β i
    · exact Finset.mem_range.mpr (by omega)
  rw [baseHorizon_eq_timeWidth J hX]
  linarith only [hfirst,hsum]

theorem reciprocal_activation_le_base (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    (activationTime J X a β n)⁻¹ ≤ 12/baseHorizon J X := by
  have hb := baseHorizon_pos J hJ hX
  have hs := activation_lower_of_initial J hJ X hX a β ha ha₂ hβ hβ₂ hn
  have hi := one_div_le_one_div_of_le (div_pos hb (by norm_num)) hs
  simpa only [one_div,inv_div] using hi

theorem actual_reciprocal_activation (J D : ℕ) (hJ : 3 ≤ J) (hD : 2000 ≤ D)
    (C c X δ : ℝ) (hX : 2 ≤ X) (hb : ActualBounds J D C c X δ)
    (a β : ℕ → ℝ) (ha : 1 / 2 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hβ : 1 / 2 ≤ β 0 * X ^ 2) (hβ₂ : β 0 * X ^ 2 ≤ 2) {n : ℕ} (hn : 1 ≤ n) :
    (activationTime J X a β n)⁻¹ ≤ 12/baseHorizon J X ∧
      12/baseHorizon J X ≤ previousFrequency J D X n^80 :=
  ⟨reciprocal_activation_le_base J (by omega) X (by linarith only [hX])
      a β ha ha₂ hβ hβ₂ hn,
    base_inverse_le_previous_frequency_pow80 J D hJ hD X hX hb.initial_frequency n⟩

end EulerParentHistoryFrequency
