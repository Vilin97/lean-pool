/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.FinalAssembly
import LeanPool.ScottishBook155.ProtectedChainLimit
import LeanPool.ScottishBook155.RegularDirectLimit

/-!
# Final assembly from a scheduled protected chain

This file isolates the last step of the transfinite argument.  Once a coherent
chain and its bookkeeping obligations have been constructed, regularity shows
that the completed direct limits contain no points beyond the stage union, and
the schedule gives surjectivity of the final map.
-/

namespace ScottishBook155

private abbrev RI := RecursionIndex.{0}

/-- The exact output required from the transfinite recursion. -/
structure ScheduledProtectedChain where
  /-- The protected chain produced by the transfinite construction, with distance scale
  one half and projection bound one. -/
  chain : ProtectedChain (ι := RI) ((1 : ℝ) / 2) 1
  /-- An enumeration of each stage target by recursion indices for the processing
  schedule. -/
  enumerate : ∀ i, RI → (chain.stage i).target
  enumerate_surjective : ∀ i, Function.Surjective (enumerate i)
  processed : ∀ i ξ,
    ∃ x : (chain.stage (bookkeepingReceivingStage (i, ξ))).source,
      (chain.stage (bookkeepingReceivingStage (i, ξ))).map x =
        chain.targetSystem.embed i (bookkeepingReceivingStage (i, ξ))
          (bookkeepingReceivingStage_gt (i, ξ)).le (enumerate i ξ)
  /-- The index at which the initial bent-map witness is embedded in the protected chain. -/
  seedIndex : RI
  /-- The isometric embedding of the real-line seed into the scheduled source stage. -/
  seedSource : ℝ →ₗᵢ[ℝ] (chain.stage seedIndex).source
  /-- The isometric embedding of the bent seed target into the scheduled target stage. -/
  seedTarget : OneSum ℝ →ₗᵢ[ℝ] (chain.stage seedIndex).target
  seedCompatible : ∀ t,
    (chain.stage seedIndex).map (seedSource t) = seedTarget (bentMapL1 t)

namespace ScheduledProtectedChain

variable (D : ScheduledProtectedChain)

noncomputable local instance sourceDirectedSystem :
    DirectedSystem (fun i => (D.chain.stage i).source)
      (D.chain.sourceSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ D.chain.sourceSystem

noncomputable local instance targetDirectedSystem :
    DirectedSystem (fun i => (D.chain.stage i).target)
      (D.chain.targetSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ D.chain.targetSystem

/-- The Banach space obtained by completing the direct limit of the source stages. -/
abbrev FinalSource := D.chain.LimitSource
/-- The Banach space obtained by completing the direct limit of the target stages. -/
abbrev FinalTarget := D.chain.LimitTarget

/-- The map induced on completed limits by the compatible protected stage maps. -/
noncomputable def finalMap : D.FinalSource → D.FinalTarget :=
  D.chain.completedMap (by norm_num)

theorem finalMap_completedOf (i : RI) (x : (D.chain.stage i).source) :
    D.finalMap (NormedDirectLimit.completedOf _ D.chain.sourceSystem.embed i x) =
      NormedDirectLimit.completedOf _ D.chain.targetSystem.embed i
        ((D.chain.stage i).map x) := by
  exact CompletedLimitMap.completedMap_completedOf _ _
    D.chain.sourceSystem.embed D.chain.targetSystem.embed
    (fun i => (D.chain.stage i).map) D.chain.compatible
    (D.chain.stage_nonexpansive (by norm_num)) i x

theorem commonSourceStage (x y : D.FinalSource) :
    ∃ (i : RI) (x₀ y₀ : (D.chain.stage i).source),
      NormedDirectLimit.completedOf _ D.chain.sourceSystem.embed i x₀ = x ∧
      NormedDirectLimit.completedOf _ D.chain.sourceSystem.embed i y₀ = y := by
  obtain ⟨i, xi, hxi⟩ := RegularDirectLimit.exists_completedOf
    (fun i => (D.chain.stage i).source) D.chain.sourceSystem.embed x
  obtain ⟨j, yj, hyj⟩ := RegularDirectLimit.exists_completedOf
    (fun i => (D.chain.stage i).source) D.chain.sourceSystem.embed y
  let k := max i j
  refine ⟨k, D.chain.sourceSystem.embed i k (le_max_left _ _) xi,
    D.chain.sourceSystem.embed j k (le_max_right _ _) yj, ?_, ?_⟩
  · rw [NormedDirectLimit.completedOf_f]
    exact hxi
  · rw [NormedDirectLimit.completedOf_f]
    exact hyj

theorem finalMap_surjective : Function.Surjective D.finalMap := by
  intro y
  obtain ⟨i, yi, hyi⟩ := RegularDirectLimit.exists_completedOf
    (fun i => (D.chain.stage i).target) D.chain.targetSystem.embed y
  obtain ⟨ξ, hξ⟩ := D.enumerate_surjective i yi
  subst yi
  obtain ⟨x, hx⟩ := D.processed i ξ
  refine ⟨NormedDirectLimit.completedOf _ D.chain.sourceSystem.embed
    (bookkeepingReceivingStage (i, ξ)) x, ?_⟩
  rw [D.finalMap_completedOf, hx, NormedDirectLimit.completedOf_f]
  exact hyi

/-- A completed scheduled chain supplies exactly the data consumed by the
final metric argument. -/
noncomputable def toFinalAssemblyData : FinalAssemblyData.{0} where
  source := RealBanachSpace.ofType D.FinalSource
  target := RealBanachSpace.ofType D.FinalTarget
  map := D.finalMap
  stageIndex := RI
  stage := D.chain.stage
  sourceEmbedding := fun i =>
    NormedDirectLimit.completedOf _ D.chain.sourceSystem.embed i
  targetEmbedding := fun i =>
    NormedDirectLimit.completedOf _ D.chain.targetSystem.embed i
  compatible := D.finalMap_completedOf
  commonStage := D.commonSourceStage
  surjective := D.finalMap_surjective
  seedIndex := D.seedIndex
  seedSource := D.seedSource
  seedTarget := D.seedTarget
  seedCompatible := D.seedCompatible

theorem claim14 (D : ScheduledProtectedChain) : Claim14.{0} :=
  claim14_of_finalAssembly (toFinalAssemblyData D)

end ScheduledProtectedChain

end ScottishBook155
