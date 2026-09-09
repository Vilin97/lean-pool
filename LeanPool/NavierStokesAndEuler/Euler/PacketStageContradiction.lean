/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionScaleBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInductionStage
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVaryingHorizon
import LeanPool.NavierStokesAndEuler.Euler.PacketStageGrowth
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution
import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Series

/-! Any actual family of packet stages with convergent H³ initial data
excludes an ordinary Euler evolution on the base horizon. Each stage is
compared only on its own genuine horizon. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction.Stage

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerSmoothL2Series
  EulerPacketInductionScales EulerPacketSourceScaleActual EulerPacketBaseGuardScales
open scoped Topology

variable {c B : ℝ} {S : Scales c B} (P : ∀ n, Stage S n) (u₀ : Space → Space)
  (hinit : Tendsto (fun n => derivativeSum 3
    ((fun x => (P n).state.evolution.velocity (0, x)) - u₀)) atTop (𝓝 0))

include P hinit

theorem false_of_evolution
    (U : Evolution (baseHorizon S.J S.X) (baseHorizon_pos S.J S.j_one S.x_pos).le)
    (hU₀ : (U.velocity ⟨0, le_rfl, (baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field = u₀) :
    False := by
  let durations : ℕ → ℝ := fun n => (P n).parent.T
  let hD : ∀ n, 0 ≤ durations n := fun n => (P n).parent.T_pos.le
  let hDT : ∀ n, durations n ≤ baseHorizon S.J S.X := fun n => (P n).horizon_le
  let V : ∀ n, Evolution (durations n) (hD n) :=
    fun n => (P n).state.regularity.ordinaryEvolution
  let times : ∀ n, Icc (0 : ℝ) (durations n) :=
    fun n => ⟨(P n).time,(P n).time_nonneg,(P n).time_lt.le⟩
  have hfield (n : ℕ) :
      (((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n))
        ⟨0,le_rfl,hD n⟩).field = (fun x => (P n).state.evolution.velocity (0,x))-u₀ := by
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((P n).state.regularity.velocity ⟨0,le_rfl,(P n).parent.T_pos.le⟩).field x -
        (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field x = _
    rw [hU₀,← (P n).state.regularity.velocity_match ⟨0,le_rfl,(P n).parent.T_pos.le⟩ x]
    rfl
  have hnorm (n : ℕ) :
      tensorNorm 3 ((U.restrictTime (durations n) (hD n) (hDT n)).difference
        (V n) ⟨0,le_rfl,hD n⟩) =
      derivativeSum 3 ((fun x => (P n).state.evolution.velocity (0,x))-u₀) := by
    rw [tensorNorm_eq_derivativeSum,hfield]
  have hlim : Tendsto (fun n => tensorNorm 3
      ((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n) ⟨0,le_rfl,hD n⟩))
      atTop (𝓝 0) := by
    simpa only [hnorm] using hinit
  have hno := U.no_gradient_escape_of_initial_tendsto_varying durations hD hDT V hlim times
  apply hno
  have hactual (n : ℕ) : ((V n).velocity (times n)).field =
      fun x => (P n).state.evolution.velocity ((P n).time,x) :=
    funext (fun x => ((P n).state.regularity.velocity_match (times n) x).symm)
  have heq : (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) =
      fun n => (P n).activationGradient := by
    funext n
    rw [hactual]
    rfl
  rw [heq]
  exact gradient_atTop P

theorem no_euler_evolution_of_initial_H3 :
    ¬ ∃ U : Evolution (baseHorizon S.J S.X) (baseHorizon_pos S.J S.j_one S.x_pos).le,
      (U.velocity ⟨0,le_rfl,(baseHorizon_pos S.J S.j_one S.x_pos).le⟩).field=u₀ := by
  rintro ⟨U,hU⟩
  exact false_of_evolution P u₀ hinit U hU

end EulerPacketInduction.Stage
