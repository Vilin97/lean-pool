/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteLifespan
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVaryingHorizon
import LeanPool.NavierStokesAndEuler.Euler.ParentOrdinaryEvolution

/-!
# Every packet horizon covers the canonical lifespan

The horizons of the actual recursive family decrease. If its limiting
datum had an evolution through any one of those horizons, comparison
with the tail of the packet family would bound the divergent activation
gradients. This applies the proved varying-horizon H³ stability theorem.
-/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerPhysicalL2Scaling EulerOrdinarySobolev EulerSmoothL2Series
  EulerPacketSourceScaleSequence
open scoped Topology

theorem packets_horizon_succ (n : ℕ) :
    (packets (n+1)).parent.T = (packets n).nextHorizon := by
  rw [(packets (n+1)).horizon_eq]
  have ht : (packets (n+1)).time = (packets n).nextTime :=
    stages_time constructionScales le_rfl le_rfl n
  rw [ht]
  rfl

theorem packets_horizon_antitone : Antitone (fun n => (packets n).parent.T) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [packets_horizon_succ]
  exact (packets n).nextHorizon_le

theorem initialDatum_no_packet_horizon (N : ℕ) :
    ¬ HasEulerEvolution initialDatum (packets N).parent.T := by
  rintro ⟨hT,U,hU₀⟩
  let durations : ℕ → ℝ := fun n => (packets (n+N)).parent.T
  let hD : ∀ n, 0 ≤ durations n := fun n => (packets (n+N)).parent.T_pos.le
  let hDT : ∀ n, durations n ≤ (packets N).parent.T :=
    fun n => packets_horizon_antitone (by omega)
  let V : ∀ n, Evolution (durations n) (hD n) :=
    fun n => (packets (n+N)).state.regularity.ordinaryEvolution
  let times : ∀ n, Icc (0 : ℝ) (durations n) :=
    fun n => ⟨(packets (n+N)).time,(packets (n+N)).time_nonneg,
      (packets (n+N)).time_lt.le⟩
  have hfield (n : ℕ) :
      (((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n))
        ⟨0,le_rfl,hD n⟩).field =
      (fun x => (packets (n+N)).state.evolution.velocity (0,x))-initialDatum.field := by
    funext x
    rw [Evolution.difference,fieldSub_field]
    change ((packets (n+N)).state.regularity.velocity
      ⟨0,le_rfl,(packets (n+N)).parent.T_pos.le⟩).field x -
        (U.velocity ⟨0,le_rfl,hT.le⟩).field x = _
    rw [hU₀,← (packets (n+N)).state.regularity.velocity_match
      ⟨0,le_rfl,(packets (n+N)).parent.T_pos.le⟩ x]
    rfl
  have hnorm (n : ℕ) :
      tensorNorm 3 ((U.restrictTime (durations n) (hD n) (hDT n)).difference
        (V n) ⟨0,le_rfl,hD n⟩) =
      derivativeSum 3 ((fun x => (packets (n+N)).state.evolution.velocity (0,x)) -
        initialDatum.field) := by
    rw [tensorNorm_eq_derivativeSum,hfield]
  have hlim : Tendsto (fun n => tensorNorm 3
      ((U.restrictTime (durations n) (hD n) (hDT n)).difference (V n)
        ⟨0,le_rfl,hD n⟩)) atTop (𝓝 0) := by
    simpa only [hnorm, Function.comp_def] using
      (initialDatum_Hm 3).comp (tendsto_add_atTop_nat N)
  apply U.no_gradient_escape_of_initial_tendsto_varying durations hD hDT V hlim times
  have hactual (n : ℕ) : ((V n).velocity (times n)).field =
      fun x => (packets (n+N)).state.evolution.velocity ((packets (n+N)).time,x) :=
    funext (fun x => ((packets (n+N)).state.regularity.velocity_match (times n) x).symm)
  have heq : (fun n => ‖fderiv ℝ ((V n).velocity (times n)).field 0‖) =
      fun n => (packets (n+N)).activationGradient := by
    funext n
    rw [hactual]
    rfl
  rw [heq]
  exact packets_gradient_atTop.comp (tendsto_add_atTop_nat N)

theorem lifespan_le_packet_horizon (n : ℕ) :
    lifespan.duration ≤ (packets n).parent.T := by
  by_contra h
  exact initialDatum_no_packet_horizon n
    (lifespan.shorter (packets n).parent.T (packets n).parent.T_pos (lt_of_not_ge h))

end EulerPacketInduction
