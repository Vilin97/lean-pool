/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseInductionStage
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSuccessor
public import LeanPool.NavierStokesAndEuler.Euler.PacketStageGrowth

/-! The actual infinite packet family, from the concrete first stage
and the two genuine successor constructions. -/

@[expose] public section


noncomputable section

namespace EulerPacketInduction

open Set Filter EulerSmoothLimit EulerPacketInductionScales EulerPacketLowConstants
  EulerParentNeighborThreshold EulerPacketSourceScaleSequence
open scoped Topology

namespace Stage

variable {q : ℕ} {B : ℝ} {S : Scales (q : ℝ) B}

/-- Successor as an element of `Stage S (n+1)`. -/
def successor {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
    (hB : commonThreshold gradientConstant hessianConstant ≤ B) : Stage S (n+1) := by
  cases n with
  | zero => exact P.forwardNext hq hB
  | succ n => exact P.joinedNext (Nat.succ_ne_zero n) hq hB

theorem successor_time {n : ℕ} (P : Stage S n) (hq : requiredExponent ≤ q)
    (hB : commonThreshold gradientConstant hessianConstant ≤ B) :
    (P.successor hq hB).time=P.nextTime := by
  cases n with
  | zero => exact P.forwardNext_time hq hB
  | succ n => exact P.joinedNext_time (Nat.succ_ne_zero n) hq hB

end Stage

variable {q : ℕ} {B : ℝ} (S : Scales (q : ℝ) B) (hq : requiredExponent ≤ q)
  (hB : commonThreshold gradientConstant hessianConstant ≤ B)

/-- Stages as an element of `(n : ℕ) → Stage S n | 0 => S.firstStage | n+1 => (stages
n).successor hq hB`. -/
def stages : (n : ℕ) → Stage S n
  | 0 => S.firstStage
  | n+1 => (stages n).successor hq hB

theorem stages_zero : stages S hq hB 0=S.firstStage := rfl

theorem stages_succ (n : ℕ) :
    stages S hq hB (n+1)=(stages S hq hB n).successor hq hB := rfl

theorem stages_time (n : ℕ) :
    (stages S hq hB (n+1)).time=(stages S hq hB n).nextTime :=
  (stages S hq hB n).successor_time hq hB

theorem stages_initial_step (n : ℕ) (hn : n ≠ 0) :
    (fun x => (stages S hq hB (n+1)).state.evolution.velocity (0,x)) =
      (fun x => (stages S hq hB n).state.evolution.velocity (0,x)) +
      (((stages S hq hB n).joinedInput hn hq hB).high (frequency S.J S.X n) +
        ((stages S hq hB n).joinedInput hn hq hB).mean (frequency S.J S.X n)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact (stages S hq hB (n+1)).joinedNext_initial_velocity (Nat.succ_ne_zero n) hq hB

theorem stages_gradient_atTop :
    Tendsto (fun n => (stages S hq hB n).activationGradient) atTop atTop :=
  Stage.gradient_atTop (stages S hq hB)

/-- Construction scales: an abbreviation for `Scales (requiredExponent : ℝ) (commonThreshold
gradientConstant hessianConstant)`. -/
abbrev ConstructionScales :=
  Scales (requiredExponent : ℝ) (commonThreshold gradientConstant hessianConstant)

/-- Construction scales, given by `Classical.choice (exists_scales (requiredExponent : ℝ)
(commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))`. -/
def constructionScales : ConstructionScales :=
  Classical.choice (exists_scales (requiredExponent : ℝ)
    (commonThreshold gradientConstant hessianConstant) (Nat.cast_nonneg _))

/-- Packets, given by `stages constructionScales le_rfl le_rfl n`. -/
def packets (n : ℕ) : Stage constructionScales n := stages constructionScales le_rfl le_rfl n

theorem packets_gradient_atTop :
    Tendsto (fun n => (packets n).activationGradient) atTop atTop := Stage.gradient_atTop packets

end EulerPacketInduction
