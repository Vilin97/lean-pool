/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards

@[expose] public section

/-! The literal activation times and nested horizons in (38). The same
positive initial time interval is available to every finite packet state. -/

noncomputable section

namespace EulerPacketNestedHorizons

open Finset Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketSourceScaleGuards EulerPacketBaseGuardScales

def stepLength (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  scaleSequence J X (n+1)/sqrt (β n*a n*previousShear J X n)

def activationTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, stepLength J X a β i

def horizonTime (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) : ℝ :=
  activationTime J X a β n+2*timeWidth J X n

@[simp] theorem activationTime_zero (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) :
    activationTime J X a β 0=0 := by simp [activationTime]

theorem activationTime_succ (J : ℕ) (X : ℝ) (a β : ℕ → ℝ) (n : ℕ) :
    activationTime J X a β (n+1)=activationTime J X a β n+stepLength J X a β n := by
  exact sum_range_succ _ n

@[simp] theorem horizonTime_zero (J : ℕ) {X : ℝ} (hX : 0 < X) (a β : ℕ → ℝ) :
    horizonTime J X a β 0=baseHorizon J X := by
  rw [horizonTime,activationTime_zero,zero_add,baseHorizon_eq_timeWidth J hX]

variable (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X) (a β : ℕ → ℝ)
  (ha : ∀ n, 1/2 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
  (hβ : ∀ n, 1/2 ≤ β n*scaleSequence J X n^2)
  (hβ₂ : ∀ n, β n*scaleSequence J X n^2 ≤ 2)

include hJ hX ha ha₂ hβ hβ₂ in
theorem stepLength_bounds (n : ℕ) :
    timeWidth J X n/6 ≤ stepLength J X a β n ∧
      stepLength J X a β n ≤ 2*timeWidth J X n/3 := by
  have hx := quadratic_growth_pos J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
  exact activation_time_bounds (ha n) (ha₂ n) (previousShear_pos J hX n)
    (hx n) (hx (n+1)).le (hβ n) (hβ₂ n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem stepLength_pos (n : ℕ) : 0 < stepLength J X a β n :=
  lt_of_lt_of_le (div_pos (timeWidth_pos J hJ hX n) (by norm_num))
    (stepLength_bounds J hJ X hX a β ha ha₂ hβ hβ₂ n).1

include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_strictMono : StrictMono (activationTime J X a β) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [activationTime_succ]
  exact lt_add_of_pos_right _ (stepLength_pos J hJ X hX a β ha ha₂ hβ hβ₂ n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_nonneg (n : ℕ) : 0 ≤ activationTime J X a β n := by
  simpa only [activationTime_zero] using
    (activationTime_strictMono J hJ X hX a β ha ha₂ hβ hβ₂).monotone (Nat.zero_le n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_pos {n : ℕ} (hn : 0 < n) : 0 < activationTime J X a β n := by
  simpa only [activationTime_zero] using
    activationTime_strictMono J hJ X hX a β ha ha₂ hβ hβ₂ hn

include hJ hX ha ha₂ hβ hβ₂ in
theorem horizonTime_pos (n : ℕ) : 0 < horizonTime J X a β n := by
  exact add_pos_of_nonneg_of_pos
    (activationTime_nonneg J hJ X hX a β ha ha₂ hβ hβ₂ n)
    (mul_pos (by norm_num) (timeWidth_pos J hJ hX n))

include hJ hX in
theorem activationTime_lt_horizon (n : ℕ) :
    activationTime J X a β n < horizonTime J X a β n := by
  exact lt_add_of_pos_right _ (mul_pos (by norm_num) (timeWidth_pos J hJ hX n))

include hJ hX ha ha₂ hβ hβ₂ in
theorem horizonTime_succ_le (n : ℕ) (hw : timeWidth J X (n+1) ≤ timeWidth J X n/2) :
    horizonTime J X a β (n+1) ≤ horizonTime J X a β n := by
  unfold horizonTime
  rw [activationTime_succ]
  exact nested_horizon_of_width_ratio (timeWidth_pos J hJ hX n).le
    (stepLength_bounds J hJ X hX a β ha ha₂ hβ hβ₂ n).2 hw

include hJ hX ha ha₂ hβ hβ₂ in
theorem horizonTime_antitone (hw : ∀ n, timeWidth J X (n+1) ≤ timeWidth J X n/2) :
    Antitone (horizonTime J X a β) := by
  exact antitone_nat_of_succ_le (fun n =>
    horizonTime_succ_le J hJ X hX a β ha ha₂ hβ hβ₂ n (hw n))

include hJ hX ha ha₂ hβ hβ₂ in
theorem horizonTime_le_base (hw : ∀ n, timeWidth J X (n+1) ≤ timeWidth J X n/2) (n : ℕ) :
    horizonTime J X a β n ≤ baseHorizon J X := by
  simpa only [horizonTime_zero J hX a β] using
    horizonTime_antitone J hJ X hX a β ha ha₂ hβ hβ₂ hw (Nat.zero_le n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem activationTime_lower {n : ℕ} (hn : 1 ≤ n) :
    baseHorizon J X/12 ≤ activationTime J X a β n := by
  have hfirst := (stepLength_bounds J hJ X hX a β ha ha₂ hβ hβ₂ 0).1
  have hm := (activationTime_strictMono J hJ X hX a β ha ha₂ hβ hβ₂).monotone hn
  rw [show (1 : ℕ)=0+1 by rfl,activationTime_succ,activationTime_zero,zero_add] at hm
  rw [baseHorizon_eq_timeWidth J hX]
  linarith only [hfirst,hm]

include hJ hX ha ha₂ hβ hβ₂ in
theorem common_positive_interval (n : ℕ) : baseHorizon J X/12 < horizonTime J X a β n := by
  by_cases hn : n=0
  · subst n
    rw [horizonTime_zero J hX]
    have hb := baseHorizon_pos J hJ hX
    linarith only [hb]
  · exact (activationTime_lower J hJ X hX a β ha ha₂ hβ hβ₂ (by omega)).trans_lt
      (activationTime_lt_horizon J hJ X hX a β n)

include hJ hX ha ha₂ hβ hβ₂ in
theorem reciprocal_horizon_le (n : ℕ) :
    (horizonTime J X a β n)⁻¹ ≤ 12/baseHorizon J X := by
  have hb := baseHorizon_pos J hJ hX
  have hs := common_positive_interval J hJ X hX a β ha ha₂ hβ hβ₂ n
  have h := one_div_le_one_div_of_le (div_pos hb (by norm_num)) hs.le
  simpa only [one_div,inv_div] using h

include hJ hX ha ha₂ hβ hβ₂ in
theorem reciprocal_activation_le {n : ℕ} (hn : 1 ≤ n) :
    (activationTime J X a β n)⁻¹ ≤ 12/baseHorizon J X := by
  have hb := baseHorizon_pos J hJ hX
  have hs := activationTime_lower J hJ X hX a β ha ha₂ hβ hβ₂ hn
  have h := one_div_le_one_div_of_le (div_pos hb (by norm_num)) hs
  simpa only [one_div,inv_div] using h

end EulerPacketNestedHorizons
