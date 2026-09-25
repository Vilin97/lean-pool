/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.ProtectedChain


/-!
# Constant coherent protected chains
-/

@[expose] public section

namespace ScottishBook155

universe u

/-- A constant family of one protected stage is a coherent chain. -/
noncomputable def constantProtectedChain
    {ι : Type u} [LinearOrder ι] {r L : ℝ} (S : ProtectedStage.{u} r) :
    ProtectedChain (ι := ι) r L where
  stage := fun _ ↦ S
  sourceSystem := {
    embed := fun _ _ _ ↦ LinearIsometry.id
    project := fun _ _ _ ↦ ContinuousLinearMap.id ℝ S.source
    embed_refl := fun _ _ ↦ rfl
    embed_trans := fun _ _ _ _ _ _ ↦ rfl
    project_embed := fun _ _ _ _ _ _ ↦ rfl
    project_retracts := fun _ _ _ _ ↦ rfl
    project_contractive := fun _ _ _ _ ↦ le_rfl }
  targetSystem := {
    embed := fun _ _ _ ↦ LinearIsometry.id
    project := fun _ _ _ ↦ ContinuousLinearMap.id ℝ S.target
    embed_refl := fun _ _ ↦ rfl
    embed_trans := fun _ _ _ _ _ _ ↦ rfl
    project_embed := fun _ _ _ _ _ _ ↦ rfl
    project_retracts := fun _ _ _ _ ↦ rfl
    project_contractive := fun _ _ _ _ ↦ le_rfl }
  compatible := fun _ _ _ _ ↦ rfl
  recovers := fun _ _ _ _ _ ↦ rfl

end ScottishBook155
