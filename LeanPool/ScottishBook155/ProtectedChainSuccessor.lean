/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.ProtectedChainReindex
public import LeanPool.ScottishBook155.ProtectedChainCore


/-!
# Appending a protected successor to a coherent chain

This file packages the successor clause independently of the transfinite
recursion.  The new index is the top point of `WithTop ι`.
-/

@[expose] public section

namespace ScottishBook155

universe u

namespace ProtectedChain

variable {ι : Type u} [LinearOrder ι] [OrderTop ι]
variable {r L : ℝ} (C : ProtectedChain (ι := ι) r L)

/-- The coherent systems of a chain give a protected link between any two
comparable stages. -/
noncomputable def link (i j : ι) (hij : i ≤ j) :
    ProtectedLink (C.stage i) (C.stage j) L where
  sourceEmbedding := C.sourceSystem.embed i j hij
  sourceProjection := C.sourceSystem.project i j hij
  targetEmbedding := C.targetSystem.embed i j hij
  targetProjection := C.targetSystem.project i j hij
  compatible := C.compatible i j hij
  sourceRetracts := C.sourceSystem.project_retracts i j hij
  targetRetracts := C.targetSystem.project_retracts i j hij
  sourceContractive := C.sourceSystem.project_contractive i j hij
  targetContractive := C.targetSystem.project_contractive i j hij
  recovers := C.recovers i j hij

variable {C}

/-- The stage family obtained by adjoining a new top stage. -/
noncomputable def appendStage
    (T : ProtectedTransition (C.stage ⊤) L) :
    WithTop ι → ProtectedStage.{u} r
  | ⊤ => T.next
  | (i : ι) => C.stage i

/-- Links in the chain with one new top stage. -/
noncomputable def appendLink
    (T : ProtectedTransition (C.stage ⊤) L)
    (i j : WithTop ι) (hij : i ≤ j) :
    ProtectedLink (appendStage T i) (appendStage T j) L := by
  induction j using WithTop.recTopCoe with
  | top =>
      induction i using WithTop.recTopCoe with
      | top => exact ProtectedLink.refl T.next
      | coe i => exact (C.link i ⊤ le_top).extend T
  | coe j =>
      induction i using WithTop.recTopCoe with
      | top => exact False.elim (by simp at hij)
      | coe i => exact C.link i j (by simpa using hij)

@[simp]
theorem appendLink_coe_coe
    (T : ProtectedTransition (C.stage ⊤) L)
    (i j : ι) (hij : (i : WithTop ι) ≤ j) :
    appendLink T i j hij = C.link i j (by simpa using hij) := rfl

@[simp]
theorem appendLink_coe_top
    (T : ProtectedTransition (C.stage ⊤) L) (i : ι) :
    appendLink T i ⊤ le_top = (C.link i ⊤ le_top).extend T := rfl

@[simp]
theorem appendLink_top_top
    (T : ProtectedTransition (C.stage ⊤) L) :
    appendLink T ⊤ ⊤ le_rfl = ProtectedLink.refl T.next := rfl

/-- The coherent protected chain after one successor transition. -/
noncomputable def append
    (T : ProtectedTransition (C.stage ⊤) L) :
    ProtectedChain (ι := WithTop ι) r L where
  stage := appendStage T
  sourceSystem := {
    embed := fun i j hij => (appendLink T i j hij).sourceEmbedding
    project := fun i j hij => (appendLink T i j hij).sourceProjection
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
              | top => exact False.elim (by simp at hij)
              | coe i =>
                  change T.sourceEmbedding
                      (C.sourceSystem.embed j ⊤ le_top
                        (C.sourceSystem.embed i j (by simpa using hij) x)) =
                    T.sourceEmbedding (C.sourceSystem.embed i ⊤ le_top x)
                  exact congrArg T.sourceEmbedding
                    (C.sourceSystem.embed_trans i j ⊤ (by simpa using hij) le_top x)
      | coe k =>
          induction j using WithTop.recTopCoe with
          | top => exact False.elim (by simp at hjk)
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simp at hij)
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
              | top => exact False.elim (by simp at hai)
              | coe a =>
                  change C.sourceSystem.project a ⊤ le_top
                      (T.sourceProjection
                        (T.sourceEmbedding
                          (C.sourceSystem.embed i ⊤ le_top x))) =
                    C.sourceSystem.project a i (by simpa using hai) x
                  rw [T.sourceRetracts]
                  exact C.sourceSystem.project_embed a i ⊤
                    (by simpa using hai) le_top x
      | coe j =>
          induction i using WithTop.recTopCoe with
          | top => exact False.elim (by simp at hij)
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simp at hai)
              | coe a =>
                  exact C.sourceSystem.project_embed a i j
                    (by simpa using hai) (by simpa using hij) x
    project_retracts := fun i j hij => (appendLink T i j hij).sourceRetracts
    project_contractive := fun i j hij =>
      (appendLink T i j hij).sourceContractive }
  targetSystem := {
    embed := fun i j hij => (appendLink T i j hij).targetEmbedding
    project := fun i j hij => (appendLink T i j hij).targetProjection
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
              | top => exact False.elim (by simp at hij)
              | coe i =>
                  change T.targetEmbedding
                      (C.targetSystem.embed j ⊤ le_top
                        (C.targetSystem.embed i j (by simpa using hij) x)) =
                    T.targetEmbedding (C.targetSystem.embed i ⊤ le_top x)
                  exact congrArg T.targetEmbedding
                    (C.targetSystem.embed_trans i j ⊤ (by simpa using hij) le_top x)
      | coe k =>
          induction j using WithTop.recTopCoe with
          | top => exact False.elim (by simp at hjk)
          | coe j =>
              induction i using WithTop.recTopCoe with
              | top => exact False.elim (by simp at hij)
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
              | top => exact False.elim (by simp at hai)
              | coe a =>
                  change C.targetSystem.project a ⊤ le_top
                      (T.targetProjection
                        (T.targetEmbedding
                          (C.targetSystem.embed i ⊤ le_top x))) =
                    C.targetSystem.project a i (by simpa using hai) x
                  rw [T.targetRetracts]
                  exact C.targetSystem.project_embed a i ⊤
                    (by simpa using hai) le_top x
      | coe j =>
          induction i using WithTop.recTopCoe with
          | top => exact False.elim (by simp at hij)
          | coe i =>
              induction a using WithTop.recTopCoe with
              | top => exact False.elim (by simp at hai)
              | coe a =>
                  exact C.targetSystem.project_embed a i j
                    (by simpa using hai) (by simpa using hij) x
    project_retracts := fun i j hij => (appendLink T i j hij).targetRetracts
    project_contractive := fun i j hij =>
      (appendLink T i j hij).targetContractive }
  compatible := fun i j hij => (appendLink T i j hij).compatible
  recovers := fun i j hij => (appendLink T i j hij).recovers

/-- Restricting an appended successor chain back to the old indices recovers
the original chain. -/
theorem append_reindex_withTopCoe {κ : Type} [LinearOrder κ] [OrderTop κ]
    {r L : ℝ} (D : ProtectedChain (ι := κ) r L)
    (T : ProtectedTransition (D.stage ⊤) L) :
    (D.append T).reindex (withTopCoeOrderEmbedding (ι := κ)) = D := by
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
