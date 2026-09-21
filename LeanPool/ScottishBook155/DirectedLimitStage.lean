/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CompletedLimitMap
import LeanPool.ScottishBook155.CoherentRetractionLimit
import LeanPool.ScottishBook155.LimitStageCore
import LeanPool.ScottishBook155.StageSystem

/-!
# Protected stages from completed directed limits

This file combines the completed nonlinear limit map with coherent source and
target projections. Contractive source projections prove short-distance
preservation; eventual target recovery and injectivity of the earlier stages
prove injectivity of the completed map.
-/

namespace ScottishBook155

open Filter

universe u

namespace DirectedLimitStage

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable (M N : ι → Type u)
variable [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
variable [∀ i, CompleteSpace (M i)]
variable [∀ i, NormedAddCommGroup (N i)] [∀ i, NormedSpace ℝ (N i)]
variable [∀ i, CompleteSpace (N i)]
variable (eM : ∀ i j : ι, i ≤ j → M i →ₗᵢ[ℝ] M j)
variable (eN : ∀ i j : ι, i ≤ j → N i →ₗᵢ[ℝ] N j)
variable [DirectedSystem M (eM · · ·)] [DirectedSystem N (eN · · ·)]


local instance sourceLinearDirectedSystem :
    DirectedSystem M (NormedDirectLimit.linearMap M eM · · ·) where
  map_self {_i} x := DirectedSystem.map_self (f := (eM · · ·)) x
  map_map {_k _j _i} hij hjk x :=
    DirectedSystem.map_map (f := (eM · · ·)) hij hjk x

local instance targetLinearDirectedSystem :
    DirectedSystem N (NormedDirectLimit.linearMap N eN · · ·) where
  map_self {_i} x := DirectedSystem.map_self (f := (eN · · ·)) x
  map_map {_k _j _i} hij hjk x :=
    DirectedSystem.map_map (f := (eN · · ·)) hij hjk x

variable (V : ∀ i, M i → N i)
variable (hV : ∀ i j (hij : i ≤ j) x,
  V j (eM i j hij x) = eN i j hij (V i x))
variable (sourceProjection : CoherentRetractionLimit.ProjectionSystem M eM)
variable (targetProjection : CoherentRetractionLimit.ProjectionSystem N eN)

/-- The completed direct limit of the source stages. -/
abbrev Source := NormedDirectLimit.CompletedCarrier M eM
/-- The completed direct limit of the target stages. -/
abbrev Target := NormedDirectLimit.CompletedCarrier N eN

/-- The continuous extension to completed limits of the compatible nonexpansive stage
maps. -/
noncomputable def limitMap :
    Source M eM → Target N eN :=
  CompletedLimitMap.completedMap M N eM eN V

include hV in
omit [∀ (i : ι), CompleteSpace (N i)] in
/-- The completed limit map preserves the protected scale whenever every
earlier stage does. -/
theorem limitMap_preservesUpTo {r : ℝ}
    (sourceProjection : CoherentRetractionLimit.ProjectionSystem M eM)
    (stagePreserves : ∀ i, PreservesUpTo r (V i))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y) :
    PreservesUpTo r
      (limitMap M N eM eN V) := by
  intro x y hxy
  let sourceApprox := fun a z =>
    CoherentRetractionLimit.ProjectionSystem.approx M eM sourceProjection a z
  let f := limitMap M N eM eN V
  have hx : Tendsto (fun a => sourceApprox a x) atTop (nhds x) :=
    CoherentRetractionLimit.ProjectionSystem.approx_tendsto M eM sourceProjection x
  have hy : Tendsto (fun a => sourceApprox a y) atTop (nhds y) :=
    CoherentRetractionLimit.ProjectionSystem.approx_tendsto M eM sourceProjection y
  have hf : Continuous f :=
    (CompletedLimitMap.completedMap_lipschitz M N eM eN V hV hLip).continuous
  have himage : Tendsto (fun a => dist (f (sourceApprox a x))
      (f (sourceApprox a y))) atTop (nhds (dist (f x) (f y))) :=
    ((hf.tendsto x).comp hx).dist ((hf.tendsto y).comp hy)
  have hpointwise : ∀ a,
      dist (f (sourceApprox a x)) (f (sourceApprox a y)) =
        dist (sourceApprox a x) (sourceApprox a y) := by
    intro a
    let Px := CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
      (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x
    let Py := CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
      (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) y
    change dist (f (NormedDirectLimit.completedOf M eM a Px))
        (f (NormedDirectLimit.completedOf M eM a Py)) =
      dist (NormedDirectLimit.completedOf M eM a Px)
        (NormedDirectLimit.completedOf M eM a Py)
    change dist
        (CompletedLimitMap.completedMap M N eM eN V
          (NormedDirectLimit.completedOf M eM a Px))
        (CompletedLimitMap.completedMap M N eM eN V
          (NormedDirectLimit.completedOf M eM a Py)) =
      dist (NormedDirectLimit.completedOf M eM a Px)
        (NormedDirectLimit.completedOf M eM a Py)
    rw [CompletedLimitMap.completedMap_completedOf M N eM eN V hV hLip,
      CompletedLimitMap.completedMap_completedOf M N eM eN V hV hLip,
      (NormedDirectLimit.completedOf N eN a).isometry.dist_eq,
      (NormedDirectLimit.completedOf M eM a).isometry.dist_eq]
    apply stagePreserves a
    have hcontract :=
      (CoherentRetractionLimit.ProjectionSystem.approx_dist_le M eM
        sourceProjection a x y).trans hxy
    change dist (NormedDirectLimit.completedOf M eM a Px)
        (NormedDirectLimit.completedOf M eM a Py) ≤ r at hcontract
    rwa [(NormedDirectLimit.completedOf M eM a).isometry.dist_eq] at hcontract
  have hsource : Tendsto (fun a => dist (f (sourceApprox a x))
      (f (sourceApprox a y))) atTop (nhds (dist x y)) := by
    apply (hx.dist hy).congr'
    filter_upwards [] with a
    exact (hpointwise a).symm
  exact tendsto_nhds_unique himage hsource

/-- Eventual recovery by the coherent target projections makes the completed
limit map injective. -/
theorem limitMap_injective
    (stageInjective : ∀ i, Function.Injective (V i))
    (eventualRecovery : ∀ x : Source M eM, ∀ᶠ a in atTop,
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    Function.Injective (limitMap M N eM eN V) := by
  apply injective_of_eventual_stage_recovery (l := (atTop : Filter ι))
    (limitMap M N eM eN V) V stageInjective
    (fun a x => CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
      (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)
    (fun a x => NormedDirectLimit.completedOf M eM a x)
    (fun a y => CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
      (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a) y)
  · exact CoherentRetractionLimit.ProjectionSystem.approx_tendsto M eM
      sourceProjection
  · exact eventualRecovery

/-- A positive uniform recovery band implies the eventual recovery hypothesis
needed for injectivity. -/
theorem eventualRecovery_of_bounded
    {L : ℝ} (hL : 0 < L)
    (boundedRecovery : ∀ (a : ι) (x : Source M eM),
      dist x (CoherentRetractionLimit.ProjectionSystem.approx M eM
        sourceProjection a x) ≤ L →
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    ∀ x : Source M eM, ∀ᶠ a in atTop,
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x) := by
  intro x
  filter_upwards [CoherentRetractionLimit.ProjectionSystem.eventually_dist_approx_le
    M eM sourceProjection hL x] with a ha
  exact boundedRecovery a x ha

/-- Open-band version of `eventualRecovery_of_bounded`. -/
theorem eventualRecovery_of_bounded_lt
    {L : ℝ} (hL : 0 < L)
    (boundedRecovery : ∀ (a : ι) (x : Source M eM),
      dist x (CoherentRetractionLimit.ProjectionSystem.approx M eM
        sourceProjection a x) < L →
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    ∀ x : Source M eM, ∀ᶠ a in atTop,
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x) := by
  intro x
  filter_upwards [CoherentRetractionLimit.ProjectionSystem.eventually_dist_approx_lt
    M eM sourceProjection hL x] with a ha
  exact boundedRecovery a x ha

/-- The completed directed limit is another protected stage. -/
noncomputable def toProtectedStage {r : ℝ}
    (stageInjective : ∀ i, Function.Injective (V i))
    (stagePreserves : ∀ i, PreservesUpTo r (V i))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y)
    (eventualRecovery : ∀ x : Source M eM, ∀ᶠ a in atTop,
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    ProtectedStage.{u} r where
  source := RealBanachSpace.ofType (Source M eM)
  target := RealBanachSpace.ofType (Target N eN)
  map := limitMap M N eM eN V
  injective := limitMap_injective M N eM eN V sourceProjection targetProjection
    stageInjective eventualRecovery
  preservesUpTo := limitMap_preservesUpTo M N eM eN V hV sourceProjection
    stagePreserves hLip

/-- Version of `toProtectedStage` using the uniform bounded-recovery
invariant maintained by the recursion. -/
noncomputable def toProtectedStageOfBounded {r L : ℝ} (hL : 0 < L)
    (stageInjective : ∀ i, Function.Injective (V i))
    (stagePreserves : ∀ i, PreservesUpTo r (V i))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y)
    (boundedRecovery : ∀ (a : ι) (x : Source M eM),
      dist x (CoherentRetractionLimit.ProjectionSystem.approx M eM
        sourceProjection a x) ≤ L →
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    ProtectedStage.{u} r :=
  toProtectedStage M N eM eN V hV sourceProjection targetProjection
    stageInjective stagePreserves hLip
    (eventualRecovery_of_bounded M N eM eN V sourceProjection targetProjection
      hL boundedRecovery)

/-- Version of `toProtectedStage` for an open uniform recovery band. -/
noncomputable def toProtectedStageOfBoundedLt {r L : ℝ} (hL : 0 < L)
    (stageInjective : ∀ i, Function.Injective (V i))
    (stagePreserves : ∀ i, PreservesUpTo r (V i))
    (hLip : ∀ i x y, dist (V i x) (V i y) ≤ dist x y)
    (boundedRecovery : ∀ (a : ι) (x : Source M eM),
      dist x (CoherentRetractionLimit.ProjectionSystem.approx M eM
        sourceProjection a x) < L →
      CoherentRetractionLimit.ProjectionFamily.completedProjection N eN
          (CoherentRetractionLimit.ProjectionSystem.family N eN targetProjection a)
          (limitMap M N eM eN V x) =
        V a (CoherentRetractionLimit.ProjectionFamily.completedProjection M eM
          (CoherentRetractionLimit.ProjectionSystem.family M eM sourceProjection a) x)) :
    ProtectedStage.{u} r :=
  toProtectedStage M N eM eN V hV sourceProjection targetProjection
    stageInjective stagePreserves hLip
    (eventualRecovery_of_bounded_lt M N eM eN V sourceProjection targetProjection
      hL boundedRecovery)

end DirectedLimitStage

end ScottishBook155
