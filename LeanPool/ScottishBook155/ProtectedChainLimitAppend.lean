/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.ProtectedChainLimit
import LeanPool.ScottishBook155.ProtectedChainSuccessor

/-!
# Appending a completed limit stage to a coherent chain
-/

namespace ScottishBook155

universe u

namespace ProtectedChain

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {r L : ℝ} (C : ProtectedChain (ι := ι) r L)

noncomputable local instance appendLimitSourceDirectedSystem :
    DirectedSystem (fun i ↦ (C.stage i).source)
      (C.sourceSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.sourceSystem

noncomputable local instance appendLimitTargetDirectedSystem :
    DirectedSystem (fun i ↦ (C.stage i).target)
      (C.targetSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.targetSystem

/-- The family obtained by placing the completed limit stage at a new top. -/
noncomputable def appendLimitStage (hr : 0 < r) (hL : 0 < L) :
    WithTop ι → ProtectedStage.{u} r
  | ⊤ => C.limitStage hr hL
  | (i : ι) => C.stage i

/-- The old links and the canonical links into the completed limit. -/
noncomputable def appendLimitLink (hr : 0 < r) (hL : 0 < L)
    (i j : WithTop ι) (hij : i ≤ j) :
    ProtectedLink (C.appendLimitStage hr hL i)
      (C.appendLimitStage hr hL j) L := by
  induction j using WithTop.recTopCoe with
  | top =>
      induction i using WithTop.recTopCoe with
      | top => exact ProtectedLink.refl (C.limitStage hr hL)
      | coe i => exact C.toLimitLink hr hL i
  | coe j =>
      induction i using WithTop.recTopCoe with
      | top => exact False.elim (by simpa using hij)
      | coe i => exact C.link i j (by simpa using hij)

/-- Adjoin the completed direct limit as one new top stage. -/
noncomputable def appendLimit (hr : 0 < r) (hL : 0 < L) :
    ProtectedChain (ι := WithTop ι) r L where
  stage := C.appendLimitStage hr hL
  sourceSystem := {
    embed := fun i j hij => (C.appendLimitLink hr hL i j hij).sourceEmbedding
    project := fun i j hij => (C.appendLimitLink hr hL i j hij).sourceProjection
    embed_refl := by
      intro i x
      induction i using WithTop.recTopCoe with
      | top => rfl
      | coe i => exact C.sourceSystem.embed_refl i x
    embed_trans := by
      intro i j k hij hjk x
      induction k using WithTop.recTopCoe with
      | top =>
          induction j using WithTop.recTopCoe with
          | top => rfl
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hij)
              | coe i =>
                  change NormedDirectLimit.completedOf _ C.sourceSystem.embed j
                      (C.sourceSystem.embed i j (by simpa using hij) x) =
                    NormedDirectLimit.completedOf _ C.sourceSystem.embed i x
                  exact NormedDirectLimit.completedOf_f _ C.sourceSystem.embed
                    (by simpa using hij) x
      | coe k =>
          induction j using WithTop.recTopCoe with
          | top => exact False.elim (by simpa using hjk)
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hij)
              | coe i =>
                  exact C.sourceSystem.embed_trans i j k
                    (by simpa using hij) (by simpa using hjk) x
    project_embed := by
      intro a i j hai hij x
      induction j using WithTop.recTopCoe with
      | top =>
          induction i using WithTop.recTopCoe with
          | top =>
              induction a using WithTop.recTopCoe with
              | top => rfl
              | coe a => rfl
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hai)
              | coe a =>
                  change (C.stage i).source at x
                  change CoherentRetractionLimit.ProjectionFamily.completedProjection _
                      C.sourceSystem.embed
                      (CoherentRetractionLimit.ProjectionSystem.family _
                        C.sourceSystem.embed C.sourceProjectionSystem a)
                      (NormedDirectLimit.completedOf _ C.sourceSystem.embed i x) =
                    C.sourceSystem.project a i (by simpa using hai) x
                  rw [CoherentRetractionLimit.ProjectionFamily.completedProjection_completedOf]
                  change CoherentBiSystem.totalProject _ C.sourceSystem a i x = _
                  rw [CoherentBiSystem.totalProject_of_ge _ C.sourceSystem
                    (by simpa using hai)]
      | coe j =>
          induction i using WithTop.recTopCoe with
          | top => exact False.elim (by simpa using hij)
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hai)
              | coe a =>
                  exact C.sourceSystem.project_embed a i j
                    (by simpa using hai) (by simpa using hij) x
    project_retracts := fun i j hij =>
      (C.appendLimitLink hr hL i j hij).sourceRetracts
    project_contractive := fun i j hij =>
      (C.appendLimitLink hr hL i j hij).sourceContractive }
  targetSystem := {
    embed := fun i j hij => (C.appendLimitLink hr hL i j hij).targetEmbedding
    project := fun i j hij => (C.appendLimitLink hr hL i j hij).targetProjection
    embed_refl := by
      intro i x
      induction i using WithTop.recTopCoe with
      | top => rfl
      | coe i => exact C.targetSystem.embed_refl i x
    embed_trans := by
      intro i j k hij hjk x
      induction k using WithTop.recTopCoe with
      | top =>
          induction j using WithTop.recTopCoe with
          | top => rfl
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hij)
              | coe i =>
                  change NormedDirectLimit.completedOf _ C.targetSystem.embed j
                      (C.targetSystem.embed i j (by simpa using hij) x) =
                    NormedDirectLimit.completedOf _ C.targetSystem.embed i x
                  exact NormedDirectLimit.completedOf_f _ C.targetSystem.embed
                    (by simpa using hij) x
      | coe k =>
          induction j using WithTop.recTopCoe with
          | top => exact False.elim (by simpa using hjk)
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hij)
              | coe i =>
                  exact C.targetSystem.embed_trans i j k
                    (by simpa using hij) (by simpa using hjk) x
    project_embed := by
      intro a i j hai hij x
      induction j using WithTop.recTopCoe with
      | top =>
          induction i using WithTop.recTopCoe with
          | top =>
              induction a using WithTop.recTopCoe with
              | top => rfl
              | coe a => rfl
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hai)
              | coe a =>
                  change (C.stage i).target at x
                  change CoherentRetractionLimit.ProjectionFamily.completedProjection _
                      C.targetSystem.embed
                      (CoherentRetractionLimit.ProjectionSystem.family _
                        C.targetSystem.embed C.targetProjectionSystem a)
                      (NormedDirectLimit.completedOf _ C.targetSystem.embed i x) =
                    C.targetSystem.project a i (by simpa using hai) x
                  rw [CoherentRetractionLimit.ProjectionFamily.completedProjection_completedOf]
                  change CoherentBiSystem.totalProject _ C.targetSystem a i x = _
                  rw [CoherentBiSystem.totalProject_of_ge _ C.targetSystem
                    (by simpa using hai)]
      | coe j =>
          induction i using WithTop.recTopCoe with
          | top => exact False.elim (by simpa using hij)
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simpa using hai)
              | coe a =>
                  exact C.targetSystem.project_embed a i j
                    (by simpa using hai) (by simpa using hij) x
    project_retracts := fun i j hij =>
      (C.appendLimitLink hr hL i j hij).targetRetracts
    project_contractive := fun i j hij =>
      (C.appendLimitLink hr hL i j hij).targetContractive }
  compatible := fun i j hij => (C.appendLimitLink hr hL i j hij).compatible
  recovers := fun i j hij => (C.appendLimitLink hr hL i j hij).recovers

/-- Restricting an appended limit chain back to the old indices recovers the
original chain. -/
theorem appendLimit_reindex_withTopCoe {κ : Type} [LinearOrder κ] [Nonempty κ]
    {r L : ℝ} (D : ProtectedChain (ι := κ) r L)
    (hr : 0 < r) (hL : 0 < L) :
    (D.appendLimit hr hL).reindex
      (withTopCoeOrderEmbedding (ι := κ)) = D := by
  apply ProtectedChain.ext rfl
  · apply heq_of_eq
    apply CoherentBiSystem.ext
    · funext i j hij
      rfl
    · funext i j hij
      rfl
  · apply heq_of_eq
    apply CoherentBiSystem.ext
    · funext i j hij
      rfl
    · funext i j hij
      rfl

end ProtectedChain

end ScottishBook155
