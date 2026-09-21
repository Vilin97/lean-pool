/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.StageSystem
import LeanPool.ScottishBook155.LpTruncation

/-!
# Coherent completed limit stages

This file packages the two limit-stage arguments: common finite truncations
preserve the protected metric scale, and coherent prefix recovery forces
global injectivity.
-/

namespace ScottishBook155

open Filter

universe u

/-- A common earlier stage through which one finite-coordinate truncation of
the limit map factors isometrically. -/
structure FiniteTruncationStage
    (r : ℝ) (M₀ : RealBanachSpace.{u}) (ι : Type u)
    (N : RealBanachSpace.{u})
    (V : L1ExtensionSpace M₀ ι → N) (s : Finset ι) where
  /-- The protected stage through which this finite coordinate truncation factors. -/
  stage : ProtectedStage.{u} r
  /-- The lift into the earlier source stage, preserving the distances of the finite
  truncation. -/
  sourceLift : L1ExtensionSpace M₀ ι → stage.source
  /-- The linear isometric embedding of the earlier target stage into the limit target. -/
  targetEmbedding : stage.target →ₗᵢ[ℝ] N
  sourceDistance : ∀ x y,
    dist (sourceLift x) (sourceLift y) =
      dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y)
  compatible : ∀ x,
    V (l1ExtensionTruncation s x) = targetEmbedding (stage.map (sourceLift x))

/-- A common earlier-stage factorization proves distance preservation for the
corresponding finite truncation. -/
theorem FiniteTruncationStage.preserves
    {r : ℝ} {M₀ : RealBanachSpace.{u}} {ι : Type u}
    {N : RealBanachSpace.{u}} {V : L1ExtensionSpace M₀ ι → N}
    {s : Finset ι} (D : FiniteTruncationStage r M₀ ι N V s)
    {x y : L1ExtensionSpace M₀ ι}
    (hxy : dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y) ≤ r) :
    dist (V (l1ExtensionTruncation s x))
        (V (l1ExtensionTruncation s y)) =
      dist (l1ExtensionTruncation s x) (l1ExtensionTruncation s y) := by
  rw [D.compatible x, D.compatible y, D.targetEmbedding.isometry.dist_eq]
  rw [D.stage.preservesUpTo (D.sourceDistance x y ▸ hxy), D.sourceDistance]

/-- Data furnished at a completed limit by the coherent increasing system.
The prefix recovery maps are written with values in the full coordinate model,
extending earlier-stage vectors by zero. -/
structure CoordinateLimitData (r : ℝ) (M₀ : RealBanachSpace.{u})
    (ι : Type u) where
  /-- The real Banach target of the completed coordinate-limit construction. -/
  target : RealBanachSpace.{u}
  /-- The map from the full L1 coordinate extension into the limit target. -/
  map : L1ExtensionSpace M₀ ι → target
  continuous : Continuous map
  /-- A factorization through a protected earlier stage for each finite set of
  coordinates. -/
  finiteStage : ∀ s : Finset ι,
    FiniteTruncationStage r M₀ ι target map s
  /-- The indices used to approximate the full coordinate model by prefixes. -/
  stageIndex : Type u
  /-- The filter along which the prefixes cover every coordinate and recovery becomes
  exact. -/
  stageFilter : Filter stageIndex
  [stageFilterNeBot : NeBot stageFilter]
  /-- The coordinates retained by each prefix approximation. -/
  prefixSets : stageIndex → Set ι
  prefixCovers : ∀ i, ∀ᶠ a in stageFilter, i ∈ prefixSets a
  /-- Recovery maps from the target to the full coordinate model, agreeing eventually with
  prefix truncation on images. -/
  recover : stageIndex → target → L1ExtensionSpace M₀ ι
  eventualRecovery : ∀ x, ∀ᶠ a in stageFilter,
    recover a (map x) = l1ExtensionSetTruncation (prefixSets a) x

attribute [instance] CoordinateLimitData.stageFilterNeBot

/-- The coherent completed limit data define another protected stage. -/
noncomputable def CoordinateLimitData.toProtectedStage
    {r : ℝ} {M₀ : RealBanachSpace.{u}} {ι : Type u}
    (D : CoordinateLimitData r M₀ ι) : ProtectedStage.{u} r where
  source := RealBanachSpace.ofType (L1ExtensionSpace M₀ ι)
  target := D.target
  map := D.map
  injective := by
    apply injective_of_eventuallySeparating_recovery D.map
      (fun a => l1ExtensionSetTruncation (D.prefixSets a)) D.recover D.eventualRecovery
    intro x y hxy
    exact eq_of_eventually_l1ExtensionSetTruncation_eq D.prefixSets D.prefixCovers hxy
  preservesUpTo :=
    preservesUpTo_of_l1ExtensionTruncations D.continuous fun s _ _ hxy =>
      (D.finiteStage s).preserves hxy

end ScottishBook155
