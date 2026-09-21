/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.StageSystem

/-!
# Coherent links in a protected-stage chain

The uniform recovery law is stable when one more active or idle successor is
attached. This is the successor induction step used by the transfinite chain.
-/

namespace ScottishBook155

universe u

/-- A coherent embedding/retraction link from an earlier protected stage to a
later one, with the uniform recovery band retained. -/
structure ProtectedLink {r : ℝ}
    (A S : ProtectedStage.{u} r) (L : ℝ) where
  /-- The isometric embedding from the earlier source space into the later source space. -/
  sourceEmbedding : A.source →ₗᵢ[ℝ] S.source
  /-- The continuous linear retraction from the later source space to the earlier one. -/
  sourceProjection : S.source →L[ℝ] A.source
  /-- The isometric embedding from the earlier target space into the later target space. -/
  targetEmbedding : A.target →ₗᵢ[ℝ] S.target
  /-- The continuous linear retraction from the later target space to the earlier one. -/
  targetProjection : S.target →L[ℝ] A.target
  compatible : ∀ x, S.map (sourceEmbedding x) = targetEmbedding (A.map x)
  sourceRetracts : ∀ x, sourceProjection (sourceEmbedding x) = x
  targetRetracts : ∀ y, targetProjection (targetEmbedding y) = y
  sourceContractive : ∀ z, ‖sourceProjection z‖ ≤ ‖z‖
  targetContractive : ∀ z, ‖targetProjection z‖ ≤ ‖z‖
  recovers : ∀ z, dist z (sourceEmbedding (sourceProjection z)) < L →
    targetProjection (S.map z) = A.map (sourceProjection z)

/-- The identity link. -/
noncomputable def ProtectedLink.refl {r L : ℝ} (S : ProtectedStage.{u} r) :
    ProtectedLink S S L where
  sourceEmbedding := LinearIsometry.id
  sourceProjection := ContinuousLinearMap.id ℝ S.source
  targetEmbedding := LinearIsometry.id
  targetProjection := ContinuousLinearMap.id ℝ S.target
  compatible := fun _ => rfl
  sourceRetracts := fun _ => rfl
  targetRetracts := fun _ => rfl
  sourceContractive := fun _ => le_rfl
  targetContractive := fun _ => le_rfl
  recovers := fun _ _ => rfl

/-- A single transition as a link. -/
noncomputable def ProtectedTransition.toLink
    {r L : ℝ} {S : ProtectedStage.{u} r}
    (T : ProtectedTransition S L) : ProtectedLink S T.next L where
  sourceEmbedding := T.sourceEmbedding
  sourceProjection := T.sourceProjection
  targetEmbedding := T.targetEmbedding
  targetProjection := T.targetProjection
  compatible := T.compatible
  sourceRetracts := T.sourceRetracts
  targetRetracts := T.targetRetracts
  sourceContractive := T.sourceContractive
  targetContractive := T.targetContractive
  recovers := fun z hz => T.recovers z hz.le

/-- Append one successor transition to an existing coherent link. -/
noncomputable def ProtectedLink.extend
    {r L : ℝ} {A S : ProtectedStage.{u} r}
    (P : ProtectedLink A S L) (T : ProtectedTransition S L) :
    ProtectedLink A T.next L where
  sourceEmbedding := T.sourceEmbedding.comp P.sourceEmbedding
  sourceProjection := P.sourceProjection.comp T.sourceProjection
  targetEmbedding := T.targetEmbedding.comp P.targetEmbedding
  targetProjection := P.targetProjection.comp T.targetProjection
  compatible x := by
    change T.next.map (T.sourceEmbedding (P.sourceEmbedding x)) =
      T.targetEmbedding (P.targetEmbedding (A.map x))
    rw [T.compatible, P.compatible]
  sourceRetracts x := by
    change P.sourceProjection
      (T.sourceProjection (T.sourceEmbedding (P.sourceEmbedding x))) = x
    rw [T.sourceRetracts, P.sourceRetracts]
  targetRetracts y := by
    change P.targetProjection
      (T.targetProjection (T.targetEmbedding (P.targetEmbedding y))) = y
    rw [T.targetRetracts, P.targetRetracts]
  sourceContractive z :=
    (P.sourceContractive (T.sourceProjection z)).trans (T.sourceContractive z)
  targetContractive z :=
    (P.targetContractive (T.targetProjection z)).trans (T.targetContractive z)
  recovers z hz := by
    let q : S.source := T.sourceProjection z
    let m : A.source := P.sourceProjection q
    have himmediate : dist z (T.sourceEmbedding q) < L := by
      exact (T.sourceNearest z (P.sourceEmbedding m)).trans_lt hz
    have hproject : dist q (P.sourceEmbedding m) ≤
        dist z (T.sourceEmbedding (P.sourceEmbedding m)) := by
      calc
        dist q (P.sourceEmbedding m) =
            dist (T.sourceProjection z)
              (T.sourceProjection (T.sourceEmbedding (P.sourceEmbedding m))) := by
                rw [T.sourceRetracts]
        _ ≤ dist z (T.sourceEmbedding (P.sourceEmbedding m)) := by
          rw [dist_eq_norm, ← map_sub, dist_eq_norm]
          exact T.sourceContractive _
    have hold : dist q (P.sourceEmbedding m) < L := hproject.trans_lt hz
    change P.targetProjection (T.targetProjection (T.next.map z)) = A.map m
    rw [T.recovers z himmediate.le, P.recovers q hold]

end ScottishBook155
