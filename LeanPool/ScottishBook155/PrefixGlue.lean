/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.TransfinitePrefix
import LeanPool.ScottishBook155.ProtectedChainSuccessor
import LeanPool.ScottishBook155.ProtectedChainTransport

/-!
# Gluing compatible closed prefixes below a limit
-/

namespace ScottishBook155

private abbrev RI := RecursionIndex.{0}

/-- A family of closed prefixes which literally restrict to one another. -/
structure CompatiblePrefixFamily (j : RI) where
  /-- The closed protected prefix assigned to each index below the limit. -/
  item : ∀ i : Set.Iio j, ProtectedPrefix i.1
  coherent : ∀ (i k : Set.Iio j) (hik : i.1 ≤ k.1),
    ((item k).restriction hik).chain = (item i).chain

namespace ProtectedPrefix

/-- The top-to-top link supplied by a restriction equality. -/
noncomputable def linkOfRestriction {i k : RI}
    (Pi : ProtectedPrefix i) (Pk : ProtectedPrefix k) (hik : i ≤ k)
    (hchain : (Pk.restriction hik).chain = Pi.chain) :
    ProtectedLink Pi.topStage Pk.topStage 1 := by
  let P := Pk.chain.link
    ⟨i, hik⟩ ⟨k, show k ≤ k from le_rfl⟩ hik
  have hstage : Pk.chain.stage ⟨i, hik⟩ = Pi.topStage :=
    congrArg
      (fun C : ProtectedChain (ι := Set.Iic i) ((1 : ℝ) / 2) 1 ↦
        C.stage ⟨i, show i ≤ i from le_rfl⟩) hchain
  exact P.castSource hstage

end ProtectedPrefix

namespace CompatiblePrefixFamily

variable {j : RI} (F : CompatiblePrefixFamily j)

/-- The top stage of the prefix indexed by `i`. -/
abbrev stage (i : Set.Iio j) : ProtectedStage.{0} ((1 : ℝ) / 2) :=
  (F.item i).topStage

/-- The canonical protected link between two members of a compatible prefix
family. -/
noncomputable def link (i k : Set.Iio j) (hik : i ≤ k) :
    ProtectedLink (F.stage i) (F.stage k) 1 :=
  (F.item i).linkOfRestriction (F.item k) hik (F.coherent i k hik)

/-- Equality between an earlier top stage and the corresponding stage inside a
later compatible prefix. -/
theorem stageEq (i k : Set.Iio j) (hik : i ≤ k) :
    (F.item k).chain.stage ⟨i.1, hik⟩ = F.stage i :=
  congrArg
    (fun C : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
      C.stage ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩)
    (F.coherent i k hik)

theorem link_sourceEmbedding_apply (i k : Set.Iio j) (hik : i ≤ k)
    (x : (F.stage i).source) :
    (F.link i k hik).sourceEmbedding x =
      (F.item k).chain.sourceSystem.embed
        ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
        (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x) := by
  exact ProtectedLink.castSource_sourceEmbedding
    (F.stageEq i k hik) ((F.item k).chain.link
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) x

theorem link_targetEmbedding_apply (i k : Set.Iio j) (hik : i ≤ k)
    (x : (F.stage i).target) :
    (F.link i k hik).targetEmbedding x =
      (F.item k).chain.targetSystem.embed
        ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
        (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x) := by
  exact ProtectedLink.castSource_targetEmbedding
    (F.stageEq i k hik) ((F.item k).chain.link
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) x

theorem link_sourceProjection_apply (i k : Set.Iio j) (hik : i ≤ k)
    (z : (F.stage k).source) :
    (F.link i k hik).sourceProjection z =
      ProtectedStage.castSourcePoint (F.stageEq i k hik)
        ((F.item k).chain.sourceSystem.project
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik z) := by
  exact ProtectedLink.castSource_sourceProjection
    (F.stageEq i k hik) ((F.item k).chain.link
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) z

theorem link_targetProjection_apply (i k : Set.Iio j) (hik : i ≤ k)
    (z : (F.stage k).target) :
    (F.link i k hik).targetProjection z =
      ProtectedStage.castTargetPoint (F.stageEq i k hik)
        ((F.item k).chain.targetSystem.project
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik z) := by
  exact ProtectedLink.castSource_targetProjection
    (F.stageEq i k hik) ((F.item k).chain.link
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) z

theorem source_cast_embed_eq_later (i k m : Set.Iio j)
    (hik : i ≤ k) (hkm : k ≤ m) (x : (F.stage i).source) :
    ProtectedStage.castSourcePoint (F.stageEq k m hkm).symm
        ((F.item k).chain.sourceSystem.embed
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
          (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x)) =
      (F.item m).chain.sourceSystem.embed
        ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik
        (ProtectedStage.castSourcePoint
          (F.stageEq i m (hik.trans hkm)).symm x) := by
  let C := ((F.item m).restriction hkm).chain
  let D := (F.item k).chain
  let a : Set.Iic k.1 := ⟨i.1, hik⟩
  let b : Set.Iic k.1 := ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩
  let x₀ : (C.stage a).source :=
    ProtectedStage.castSourcePoint
      (F.stageEq i m (hik.trans hkm)).symm x
  have ht := ProtectedChain.source_embed_transport
    (C := C) (D := D) (F.coherent k m hkm) a b hik x₀
  dsimp [C, D, a, b, ProtectedPrefix.restriction,
    ProtectedChain.reindex] at ht
  have hx₀ :
      ProtectedStage.castSourcePoint
          (congrArg
            (fun E : ProtectedChain (ι := Set.Iic k.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, hik⟩)
            (F.coherent k m hkm)) x₀ =
        ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x := by
    exact ProtectedStage.castSourcePoint_trans _ _ x
  have ht' := ht.trans (congrArg
    ((F.item k).chain.sourceSystem.embed
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) hx₀)
  change
    ProtectedStage.castSourcePoint (F.stageEq k m hkm)
        ((F.item m).chain.sourceSystem.embed
          ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀) =
      (F.item k).chain.sourceSystem.embed
        ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
        (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x) at ht'
  calc
    ProtectedStage.castSourcePoint (F.stageEq k m hkm).symm
        ((F.item k).chain.sourceSystem.embed
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
          (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x)) =
      ProtectedStage.castSourcePoint (F.stageEq k m hkm).symm
        (ProtectedStage.castSourcePoint (F.stageEq k m hkm)
          ((F.item m).chain.sourceSystem.embed
            ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀)) := by
              rw [ht']
    _ = (F.item m).chain.sourceSystem.embed
          ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀ := by simp
    _ = _ := rfl

theorem target_cast_embed_eq_later (i k m : Set.Iio j)
    (hik : i ≤ k) (hkm : k ≤ m) (x : (F.stage i).target) :
    ProtectedStage.castTargetPoint (F.stageEq k m hkm).symm
        ((F.item k).chain.targetSystem.embed
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
          (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x)) =
      (F.item m).chain.targetSystem.embed
        ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik
        (ProtectedStage.castTargetPoint
          (F.stageEq i m (hik.trans hkm)).symm x) := by
  let C := ((F.item m).restriction hkm).chain
  let D := (F.item k).chain
  let a : Set.Iic k.1 := ⟨i.1, hik⟩
  let b : Set.Iic k.1 := ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩
  let x₀ : (C.stage a).target :=
    ProtectedStage.castTargetPoint
      (F.stageEq i m (hik.trans hkm)).symm x
  have ht := ProtectedChain.target_embed_transport
    (C := C) (D := D) (F.coherent k m hkm) a b hik x₀
  dsimp [C, D, a, b, ProtectedPrefix.restriction,
    ProtectedChain.reindex] at ht
  have hx₀ :
      ProtectedStage.castTargetPoint
          (congrArg
            (fun E : ProtectedChain (ι := Set.Iic k.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, hik⟩)
            (F.coherent k m hkm)) x₀ =
        ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x := by
    exact ProtectedStage.castTargetPoint_trans _ _ x
  have ht' := ht.trans (congrArg
    ((F.item k).chain.targetSystem.embed
      ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik) hx₀)
  change
    ProtectedStage.castTargetPoint (F.stageEq k m hkm)
        ((F.item m).chain.targetSystem.embed
          ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀) =
      (F.item k).chain.targetSystem.embed
        ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
        (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x) at ht'
  calc
    ProtectedStage.castTargetPoint (F.stageEq k m hkm).symm
        ((F.item k).chain.targetSystem.embed
          ⟨i.1, hik⟩ ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hik
          (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x)) =
      ProtectedStage.castTargetPoint (F.stageEq k m hkm).symm
        (ProtectedStage.castTargetPoint (F.stageEq k m hkm)
          ((F.item m).chain.targetSystem.embed
            ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀)) := by
              rw [ht']
    _ = (F.item m).chain.targetSystem.embed
          ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩ hik x₀ := by simp
    _ = _ := rfl

theorem source_cast_project_eq_later (a i k : Set.Iio j)
    (hai : a ≤ i) (hik : i ≤ k) (x : (F.stage i).source) :
    ProtectedStage.castSourcePoint (F.stageEq a k (hai.trans hik))
        ((F.item k).chain.sourceSystem.project
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai
          (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x)) =
      ProtectedStage.castSourcePoint (F.stageEq a i hai)
        ((F.item i).chain.sourceSystem.project
          ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x) := by
  let C := ((F.item k).restriction hik).chain
  let D := (F.item i).chain
  let b : Set.Iic i.1 := ⟨a.1, hai⟩
  let c : Set.Iic i.1 := ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩
  let z : (C.stage c).source :=
    ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x
  have ht := ProtectedChain.source_project_transport
    (C := C) (D := D) (F.coherent i k hik) b c hai z
  dsimp [C, D, b, c, ProtectedPrefix.restriction,
    ProtectedChain.reindex] at ht
  have hz :
      ProtectedStage.castSourcePoint
          (congrArg
            (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩)
            (F.coherent i k hik)) z = x := by
    dsimp [z]
    have heq :
        congrArg
            (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩)
            (F.coherent i k hik) = F.stageEq i k hik :=
      Subsingleton.elim _ _
    rw [heq]
    exact ProtectedStage.castSourcePoint_apply_symm (F.stageEq i k hik) x
  have ht' := ht.trans (congrArg
    ((F.item i).chain.sourceSystem.project
      ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai) hz)
  change
    ProtectedStage.castSourcePoint
        (congrArg
          (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
            E.stage ⟨a.1, hai⟩)
          (F.coherent i k hik))
        ((F.item k).chain.sourceSystem.project
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai z) =
      (F.item i).chain.sourceSystem.project
        ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x at ht'
  dsimp [z] at ht'
  have hfactor : F.stageEq a k (hai.trans hik) =
      (congrArg
        (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
          E.stage ⟨a.1, hai⟩)
        (F.coherent i k hik)).trans (F.stageEq a i hai) :=
    Subsingleton.elim _ _
  rw [hfactor]
  let ea := congrArg
    (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
      E.stage ⟨a.1, hai⟩) (F.coherent i k hik)
  let p := (F.item k).chain.sourceSystem.project
    ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai
    (ProtectedStage.castSourcePoint (F.stageEq i k hik).symm x)
  change ProtectedStage.castSourcePoint ea p =
    (F.item i).chain.sourceSystem.project
      ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x at ht'
  calc
    ProtectedStage.castSourcePoint (ea.trans (F.stageEq a i hai)) p =
        ProtectedStage.castSourcePoint (F.stageEq a i hai)
          (ProtectedStage.castSourcePoint ea p) :=
      (ProtectedStage.castSourcePoint_trans ea (F.stageEq a i hai) p).symm
    _ = _ := by
      dsimp [ea, p]
      rw [ht']

theorem target_cast_project_eq_later (a i k : Set.Iio j)
    (hai : a ≤ i) (hik : i ≤ k) (x : (F.stage i).target) :
    ProtectedStage.castTargetPoint (F.stageEq a k (hai.trans hik))
        ((F.item k).chain.targetSystem.project
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai
          (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x)) =
      ProtectedStage.castTargetPoint (F.stageEq a i hai)
        ((F.item i).chain.targetSystem.project
          ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x) := by
  let C := ((F.item k).restriction hik).chain
  let D := (F.item i).chain
  let b : Set.Iic i.1 := ⟨a.1, hai⟩
  let c : Set.Iic i.1 := ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩
  let z : (C.stage c).target :=
    ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x
  have ht := ProtectedChain.target_project_transport
    (C := C) (D := D) (F.coherent i k hik) b c hai z
  dsimp [C, D, b, c, ProtectedPrefix.restriction,
    ProtectedChain.reindex] at ht
  have hz :
      ProtectedStage.castTargetPoint
          (congrArg
            (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩)
            (F.coherent i k hik)) z = x := by
    dsimp [z]
    have heq :
        congrArg
            (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
              E.stage ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩)
            (F.coherent i k hik) = F.stageEq i k hik :=
      Subsingleton.elim _ _
    rw [heq]
    exact ProtectedStage.castTargetPoint_apply_symm (F.stageEq i k hik) x
  have ht' := ht.trans (congrArg
    ((F.item i).chain.targetSystem.project
      ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai) hz)
  change
    ProtectedStage.castTargetPoint
        (congrArg
          (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
            E.stage ⟨a.1, hai⟩)
          (F.coherent i k hik))
        ((F.item k).chain.targetSystem.project
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai z) =
      (F.item i).chain.targetSystem.project
        ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x at ht'
  dsimp [z] at ht'
  have hfactor : F.stageEq a k (hai.trans hik) =
      (congrArg
        (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
          E.stage ⟨a.1, hai⟩)
        (F.coherent i k hik)).trans (F.stageEq a i hai) :=
    Subsingleton.elim _ _
  rw [hfactor]
  let ea := congrArg
    (fun E : ProtectedChain (ι := Set.Iic i.1) ((1 : ℝ) / 2) 1 =>
      E.stage ⟨a.1, hai⟩) (F.coherent i k hik)
  let p := (F.item k).chain.targetSystem.project
    ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩ hai
    (ProtectedStage.castTargetPoint (F.stageEq i k hik).symm x)
  change ProtectedStage.castTargetPoint ea p =
    (F.item i).chain.targetSystem.project
      ⟨a.1, hai⟩ ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ hai x at ht'
  calc
    ProtectedStage.castTargetPoint (ea.trans (F.stageEq a i hai)) p =
        ProtectedStage.castTargetPoint (F.stageEq a i hai)
          (ProtectedStage.castTargetPoint ea p) :=
      (ProtectedStage.castTargetPoint_trans ea (F.stageEq a i hai) p).symm
    _ = _ := by
      dsimp [ea, p]
      rw [ht']

/-- Glue a compatible family of closed prefixes into one protected chain on
the open initial segment. -/
noncomputable def openChain :
    ProtectedChain (ι := Set.Iio j) ((1 : ℝ) / 2) 1 where
  stage := F.stage
  sourceSystem := {
    embed := fun i k hik => (F.link i k hik).sourceEmbedding
    project := fun i k hik => (F.link i k hik).sourceProjection
    embed_refl := by
      intro i x
      simp only [link, ProtectedPrefix.linkOfRestriction,
        ProtectedLink.castSource]
      exact (F.item i).chain.sourceSystem.embed_refl
        ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ x
    embed_trans := by
      intro i k m hik hkm x
      rw [F.link_sourceEmbedding_apply k m hkm,
        F.link_sourceEmbedding_apply i k hik,
        F.link_sourceEmbedding_apply i m (hik.trans hkm),
        F.source_cast_embed_eq_later i k m hik hkm]
      exact (F.item m).chain.sourceSystem.embed_trans
        ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩
        ⟨m.1, show m.1 ≤ m.1 from le_rfl⟩ hik hkm _
    project_embed := by
      intro a i k hai hik x
      rw [F.link_sourceProjection_apply a k (hai.trans hik),
        F.link_sourceEmbedding_apply i k hik,
        F.link_sourceProjection_apply a i hai,
        (F.item k).chain.sourceSystem.project_embed
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩
          ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hai hik,
        F.source_cast_project_eq_later a i k hai hik]
    project_retracts := fun i k hik => (F.link i k hik).sourceRetracts
    project_contractive := fun i k hik => (F.link i k hik).sourceContractive }
  targetSystem := {
    embed := fun i k hik => (F.link i k hik).targetEmbedding
    project := fun i k hik => (F.link i k hik).targetProjection
    embed_refl := by
      intro i x
      simp only [link, ProtectedPrefix.linkOfRestriction,
        ProtectedLink.castSource]
      exact (F.item i).chain.targetSystem.embed_refl
        ⟨i.1, show i.1 ≤ i.1 from le_rfl⟩ x
    embed_trans := by
      intro i k m hik hkm x
      rw [F.link_targetEmbedding_apply k m hkm,
        F.link_targetEmbedding_apply i k hik,
        F.link_targetEmbedding_apply i m (hik.trans hkm),
        F.target_cast_embed_eq_later i k m hik hkm]
      exact (F.item m).chain.targetSystem.embed_trans
        ⟨i.1, hik.trans hkm⟩ ⟨k.1, hkm⟩
        ⟨m.1, show m.1 ≤ m.1 from le_rfl⟩ hik hkm _
    project_embed := by
      intro a i k hai hik x
      rw [F.link_targetProjection_apply a k (hai.trans hik),
        F.link_targetEmbedding_apply i k hik,
        F.link_targetProjection_apply a i hai,
        (F.item k).chain.targetSystem.project_embed
          ⟨a.1, hai.trans hik⟩ ⟨i.1, hik⟩
          ⟨k.1, show k.1 ≤ k.1 from le_rfl⟩ hai hik,
        F.target_cast_project_eq_later a i k hai hik]
    project_retracts := fun i k hik => (F.link i k hik).targetRetracts
    project_contractive := fun i k hik => (F.link i k hik).targetContractive }
  compatible := fun i k hik => (F.link i k hik).compatible
  recovers := fun i k hik => (F.link i k hik).recovers

/-- Include the closed initial segment ending at `i` into the ambient open
initial segment below `j`. -/
noncomputable def closedToOpen (i : Set.Iio j) :
    Set.Iic i.1 ↪o Set.Iio j where
  toFun := fun a =>
    (⟨a.1, by
      exact lt_of_le_of_lt
        (show a.1 ≤ i.1 from a.2) (show i.1 < j from i.2)⟩ : Set.Iio j)
  inj' := fun a b h => Subtype.ext
    (congrArg (fun z : Set.Iio j => z.1) h)
  map_rel_iff' := by intro a b; rfl

theorem closedToOpen_le (i : Set.Iio j) (a : Set.Iic i.1) :
    closedToOpen i a ≤ i := a.2

/-- The glued open chain restricts at every member of the compatible family to
the closed prefix supplied at that member. -/
theorem openChain_restriction (i : Set.Iio j) :
    F.openChain.reindex (closedToOpen i) = (F.item i).chain := by
  have hstage :
      (F.openChain.reindex (closedToOpen i)).stage =
        (F.item i).chain.stage := by
    funext a
    exact (F.stageEq (closedToOpen i a) i (closedToOpen_le i a)).symm
  apply ProtectedChain.ext_transport hstage
  · apply CoherentBiSystem.ext
    · funext a b hab
      apply LinearIsometry.ext
      intro x
      rw [ProtectedChain.transportSourceSystem_embed]
      let a' := closedToOpen i a
      let b' := closedToOpen i b
      have ha : congrFun hstage a =
          (F.stageEq a' i (closedToOpen_le i a)).symm :=
        Subsingleton.elim _ _
      have hb : congrFun hstage b =
          (F.stageEq b' i (closedToOpen_le i b)).symm :=
        Subsingleton.elim _ _
      rw [ha, hb]
      change ProtectedStage.castSourcePoint
          (F.stageEq b' i (closedToOpen_le i b)).symm
          ((F.link a' b' hab).sourceEmbedding
            (ProtectedStage.castSourcePoint
              (F.stageEq a' i (closedToOpen_le i a)) x)) = _
      rw [F.link_sourceEmbedding_apply a' b' hab]
      have h := F.source_cast_embed_eq_later a' b' i hab b.2
        (ProtectedStage.castSourcePoint
          (F.stageEq a' i (closedToOpen_le i a)) x)
      rw [h]
      exact congrArg ((F.item i).chain.sourceSystem.embed a b hab)
        (ProtectedStage.castSourcePoint_symm_apply
          (F.stageEq a' i (closedToOpen_le i a)) x)
    · funext a b hab
      apply ContinuousLinearMap.ext
      intro z
      rw [ProtectedChain.transportSourceSystem_project]
      let a' := closedToOpen i a
      let b' := closedToOpen i b
      have ha : congrFun hstage a =
          (F.stageEq a' i (closedToOpen_le i a)).symm :=
        Subsingleton.elim _ _
      have hb : congrFun hstage b =
          (F.stageEq b' i (closedToOpen_le i b)).symm :=
        Subsingleton.elim _ _
      rw [ha, hb]
      change ProtectedStage.castSourcePoint
          (F.stageEq a' i (closedToOpen_le i a)).symm
          ((F.link a' b' hab).sourceProjection
            (ProtectedStage.castSourcePoint
              (F.stageEq b' i (closedToOpen_le i b)) z)) = _
      rw [F.link_sourceProjection_apply a' b' hab]
      have h := F.source_cast_project_eq_later a' b' i hab b.2
        (ProtectedStage.castSourcePoint
          (F.stageEq b' i (closedToOpen_le i b)) z)
      rw [← h]
      exact (ProtectedStage.castSourcePoint_symm_apply
        (F.stageEq a' i (closedToOpen_le i a)) _).trans
        (congrArg ((F.item i).chain.sourceSystem.project a b hab)
          (ProtectedStage.castSourcePoint_symm_apply
            (F.stageEq b' i (closedToOpen_le i b)) z))
  · apply CoherentBiSystem.ext
    · funext a b hab
      apply LinearIsometry.ext
      intro x
      rw [ProtectedChain.transportTargetSystem_embed]
      let a' := closedToOpen i a
      let b' := closedToOpen i b
      have ha : congrFun hstage a =
          (F.stageEq a' i (closedToOpen_le i a)).symm :=
        Subsingleton.elim _ _
      have hb : congrFun hstage b =
          (F.stageEq b' i (closedToOpen_le i b)).symm :=
        Subsingleton.elim _ _
      rw [ha, hb]
      change ProtectedStage.castTargetPoint
          (F.stageEq b' i (closedToOpen_le i b)).symm
          ((F.link a' b' hab).targetEmbedding
            (ProtectedStage.castTargetPoint
              (F.stageEq a' i (closedToOpen_le i a)) x)) = _
      rw [F.link_targetEmbedding_apply a' b' hab]
      have h := F.target_cast_embed_eq_later a' b' i hab b.2
        (ProtectedStage.castTargetPoint
          (F.stageEq a' i (closedToOpen_le i a)) x)
      rw [h]
      exact congrArg ((F.item i).chain.targetSystem.embed a b hab)
        (ProtectedStage.castTargetPoint_symm_apply
          (F.stageEq a' i (closedToOpen_le i a)) x)
    · funext a b hab
      apply ContinuousLinearMap.ext
      intro z
      rw [ProtectedChain.transportTargetSystem_project]
      let a' := closedToOpen i a
      let b' := closedToOpen i b
      have ha : congrFun hstage a =
          (F.stageEq a' i (closedToOpen_le i a)).symm :=
        Subsingleton.elim _ _
      have hb : congrFun hstage b =
          (F.stageEq b' i (closedToOpen_le i b)).symm :=
        Subsingleton.elim _ _
      rw [ha, hb]
      change ProtectedStage.castTargetPoint
          (F.stageEq a' i (closedToOpen_le i a)).symm
          ((F.link a' b' hab).targetProjection
            (ProtectedStage.castTargetPoint
              (F.stageEq b' i (closedToOpen_le i b)) z)) = _
      rw [F.link_targetProjection_apply a' b' hab]
      have h := F.target_cast_project_eq_later a' b' i hab b.2
        (ProtectedStage.castTargetPoint
          (F.stageEq b' i (closedToOpen_le i b)) z)
      rw [← h]
      exact (ProtectedStage.castTargetPoint_symm_apply
        (F.stageEq a' i (closedToOpen_le i a)) _).trans
        (congrArg ((F.item i).chain.targetSystem.project a b hab)
          (ProtectedStage.castTargetPoint_symm_apply
            (F.stageEq b' i (closedToOpen_le i b)) z))

end CompatiblePrefixFamily

namespace ProtectedPrefix

/-- The prefix obtained by adjoining a completed limit stage restricts to
every member of the compatible family used to build that limit. -/
theorem ofLimit_restriction {j : RI} (hj : Order.IsSuccLimit j)
    (F : CompatiblePrefixFamily j)
    (hSource : ∀ i, Cardinal.mk (F.openChain.stage i).source ≤ stageCardinal)
    (hTarget : ∀ i, Cardinal.mk (F.openChain.stage i).target ≤ stageCardinal)
    (i : Set.Iio j) :
    ((ofLimit j hj F.openChain hSource hTarget).restriction i.2.le) =
      F.item i := by
  apply ProtectedPrefix.ext
  unfold ofLimit restriction
  dsimp
  let : Nonempty (Set.Iio j) := ⟨i⟩
  let hr : (0 : ℝ) < 1 / 2 := by norm_num
  let hL : (0 : ℝ) < 1 := by norm_num
  let e := (initialSegmentWithTop j).toOrderEmbedding
  let f : Set.Iic i.1 ↪o Set.Iic j :=
    { toFun := fun a =>
        (⟨a.1, by
          exact (show a.1 ≤ i.1 from a.2).trans
            (show i.1 ≤ j from i.2.le)⟩ : Set.Iic j)
      inj' := fun a b h => Subtype.ext
        (congrArg (fun z : Set.Iic j => z.1) h)
      map_rel_iff' := by intro a b; rfl }
  change ((F.openChain.appendLimit hr hL).reindex e).reindex f =
    (F.item i).chain
  rw [ProtectedChain.reindex_comp]
  rw [ProtectedChain.reindex_congr _ (f.trans e)
    ((CompatiblePrefixFamily.closedToOpen i).trans
      (ProtectedChain.withTopCoeOrderEmbedding (ι := Set.Iio j)))]
  · rw [← ProtectedChain.reindex_comp]
    rw [ProtectedChain.appendLimit_reindex_withTopCoe]
    exact F.openChain_restriction i
  · intro a
    change initialSegmentWithTop j
        ⟨a.1, (show a.1 ≤ i.1 from a.2).trans
          (show i.1 ≤ j from i.2.le)⟩ =
      ((CompatiblePrefixFamily.closedToOpen i a : Set.Iio j) :
        WithTop (Set.Iio j))
    rw [initialSegmentWithTop_apply_lt j a.1
      (lt_of_le_of_lt (show a.1 ≤ i.1 from a.2)
        (show i.1 < j from i.2))]
    rfl

end ProtectedPrefix

end ScottishBook155
