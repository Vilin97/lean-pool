/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketChoice
public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleSequence

@[expose] public section

/-! The literal base scale constructs the first actual smooth Euler
packet state and its localized source bounds. -/

noncomputable section

namespace EulerBaseDatum.FirstScaleGuards

open Real EulerParentPacketFrames EulerPacketBaseGuardScales EulerPacketSourceScaleSequence
  EulerPacketSourceScaleChoice EulerPacketFirstLowBounds

variable {J D : ℕ} {X : ℝ} (H : FirstScaleGuards J D X)

include H

theorem x_pos : 0 < X := zero_lt_one.trans_le H.x_one

theorem tilt_bound : |X^(-2 : ℝ)| ≤ 1 := by
  rw [abs_of_nonneg (rpow_nonneg H.x_pos.le _)]
  exact rpow_le_one_of_one_le_of_nonpos H.x_one (by norm_num)

theorem core_pos : 0 < baseRadius X := baseRadius_pos H.x_pos

theorem core_one : baseRadius X ≤ 1 := H.radius_small.trans (by norm_num)

theorem time_pos (hJ : 1 ≤ J) : 0 < baseHorizon J X := baseHorizon_pos J hJ H.x_pos

theorem spike_pos : 0 < X^(-1010 : ℝ) := rpow_pos_of_pos H.x_pos _

theorem spike_one : X^(-1010 : ℝ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos H.x_one (by norm_num)

theorem shear_pos : 0 < X^1000 := pow_pos H.x_pos _

omit H in
theorem nextRadius_pos : 0 < supportScale J X 0 := exp_pos _

theorem nextRadius_one : supportScale J X 0 ≤ 1 := by
  unfold supportScale
  apply exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr H.x_pos.le)
    (rpow_nonneg (Nat.cast_nonneg _) _)

def packet (hJ : 1 ≤ J) :
    FirstPacketChoice (X^(-2 : ℝ)) H.tilt_bound (baseRadius X) H.core_pos H.core_one
      (baseHorizon J X) (H.time_pos hJ) H.local_time
      (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
      (supportScale J X 0) nextRadius_pos H.nextRadius_one :=
  Classical.choice (exists_firstPacketChoice (X^(-2 : ℝ)) H.tilt_bound
    (baseRadius X) H.core_pos H.core_one (baseHorizon J X) (H.time_pos hJ) H.local_time
    (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
    (supportScale J X 0) nextRadius_pos H.nextRadius_one H.spike_one H.shear_pos
    H.source_frequency H.label_frequency H.radius_frequency)

def parent (hJ : 1 ≤ J) : Parent := (H.packet hJ).parent

def state (hJ : 1 ≤ J) : SmoothState (H.parent hJ) := (H.packet hJ).state

theorem state_label (hJ : 1 ≤ J) : (H.state hJ).labels.K=(X^D)^80 :=
  (H.packet hJ).state_label_constant

theorem parent_time (hJ : 1 ≤ J) : (H.parent hJ).T=baseHorizon J X := rfl

theorem parent_scale (hJ : 1 ≤ J) : (H.parent hJ).ell=supportScale J X 0 := rfl

def lowBounds (hJ : 1 ≤ J) : LowBounds (H.parent hJ) :=
  FirstPacketChoice.lowBounds (X^(-2 : ℝ)) H.tilt_bound (baseRadius X) H.core_pos H.core_one
    (baseHorizon J X) (H.time_pos hJ) H.local_time
    (X^(-1010 : ℝ)) H.spike_pos (X^1000) (X^D) H.frequency
    (supportScale J X 0) nextRadius_pos H.nextRadius_one (H.packet hJ)
    H.radius_small H.spike_one H.shear_pos.le (by
    simpa only [literalInitialPressureCost,literalInitialError,← add_assoc] using H.localized)

theorem lowBounds_values (hJ : 1 ≤ J) :
    (H.lowBounds hJ).Be=initialCoefficientCost ∧
    (H.lowBounds hJ).Bc=initialCoefficientCost+X^1000*firstRatio+literalInitialError D X ∧
    (H.lowBounds hJ).r=baseRadius X ∧
    (H.lowBounds hJ).K=initialCoefficientCost+literalInitialPressureCost D X := by
  refine ⟨rfl,rfl,rfl,?_⟩
  change initialCoefficientCost+2*initialCoefficientCost*X^(-1010 : ℝ)*(X^1000*firstRatio)+
    (X^D)^(-(1/4 : ℝ))=initialCoefficientCost+literalInitialPressureCost D X
  unfold literalInitialPressureCost literalInitialError
  ring

end EulerBaseDatum.FirstScaleGuards
