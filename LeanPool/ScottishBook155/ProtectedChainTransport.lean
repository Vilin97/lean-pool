/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.ProtectedChainReindex
import LeanPool.ScottishBook155.ProtectedChainSuccessor

/-!
# Transport along equal protected stages and chains

The transfinite construction compares restrictions whose stage types are only
propositionally equal.  These pointwise transport operations keep all large
dependent elimination out of the coherence proofs.
 -/

namespace ScottishBook155

namespace ProtectedStage

/-- Transport a source point along equality of protected stages. -/
noncomputable def castSourcePoint {r : ℝ} {A B : ProtectedStage.{0} r}
    (h : A = B) : A.source → B.source := by
  subst B
  exact id

/-- Transport a target point along equality of protected stages. -/
noncomputable def castTargetPoint {r : ℝ} {A B : ProtectedStage.{0} r}
    (h : A = B) : A.target → B.target := by
  subst B
  exact id

@[simp]
theorem castSourcePoint_rfl {r : ℝ} {A : ProtectedStage.{0} r}
    (h : A = A) (x : A.source) : castSourcePoint h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

@[simp]
theorem castTargetPoint_rfl {r : ℝ} {A : ProtectedStage.{0} r}
    (h : A = A) (x : A.target) : castTargetPoint h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

theorem castSourcePoint_trans {r : ℝ} {A B C : ProtectedStage.{0} r}
    (h : A = B) (h' : B = C) (x : A.source) :
    castSourcePoint h' (castSourcePoint h x) =
      castSourcePoint (h.trans h') x := by
  subst B
  subst C
  simp

theorem castTargetPoint_trans {r : ℝ} {A B C : ProtectedStage.{0} r}
    (h : A = B) (h' : B = C) (x : A.target) :
    castTargetPoint h' (castTargetPoint h x) =
      castTargetPoint (h.trans h') x := by
  subst B
  subst C
  simp

@[simp]
theorem castSourcePoint_symm_apply {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : A.source) :
    castSourcePoint h.symm (castSourcePoint h x) = x := by
  subst B
  simp

@[simp]
theorem castSourcePoint_apply_symm {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : B.source) :
    castSourcePoint h (castSourcePoint h.symm x) = x := by
  subst B
  simp

@[simp]
theorem castTargetPoint_symm_apply {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : A.target) :
    castTargetPoint h.symm (castTargetPoint h x) = x := by
  subst B
  simp

@[simp]
theorem castTargetPoint_apply_symm {r : ℝ}
    {A B : ProtectedStage.{0} r} (h : A = B) (x : B.target) :
    castTargetPoint h (castTargetPoint h.symm x) = x := by
  subst B
  simp

end ProtectedStage

namespace ProtectedLink

/-- Change the source stage of a protected link along an equality. -/
noncomputable def castSource {r L : ℝ}
    {A A' B : ProtectedStage.{0} r} (h : A = A')
    (P : ProtectedLink A B L) : ProtectedLink A' B L := by
  subst A'
  exact P

theorem castSource_sourceEmbedding {r L : ℝ}
    {A A' B : ProtectedStage.{0} r} (h : A = A')
    (P : ProtectedLink A B L) (x : A'.source) :
    (P.castSource h).sourceEmbedding x =
      P.sourceEmbedding (ProtectedStage.castSourcePoint h.symm x) := by
  subst A'
  simp [ProtectedLink.castSource]

theorem castSource_sourceProjection {r L : ℝ}
    {A A' B : ProtectedStage.{0} r} (h : A = A')
    (P : ProtectedLink A B L) (z : B.source) :
    (P.castSource h).sourceProjection z =
      ProtectedStage.castSourcePoint h (P.sourceProjection z) := by
  subst A'
  simp [ProtectedLink.castSource]

theorem castSource_targetEmbedding {r L : ℝ}
    {A A' B : ProtectedStage.{0} r} (h : A = A')
    (P : ProtectedLink A B L) (x : A'.target) :
    (P.castSource h).targetEmbedding x =
      P.targetEmbedding (ProtectedStage.castTargetPoint h.symm x) := by
  subst A'
  simp [ProtectedLink.castSource]

theorem castSource_targetProjection {r L : ℝ}
    {A A' B : ProtectedStage.{0} r} (h : A = A')
    (P : ProtectedLink A B L) (z : B.target) :
    (P.castSource h).targetProjection z =
      ProtectedStage.castTargetPoint h (P.targetProjection z) := by
  subst A'
  simp [ProtectedLink.castSource]

end ProtectedLink

namespace ProtectedChain

/-- Transport a source bidirectional system along equality of its protected
stage family. -/
noncomputable def transportSourceSystem {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).source)) :
    CoherentBiSystem (fun i => (T i).source) := by
  subst T
  exact B

/-- Transport a target bidirectional system along equality of its protected
stage family. -/
noncomputable def transportTargetSystem {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).target)) :
    CoherentBiSystem (fun i => (T i).target) := by
  subst T
  exact B

theorem transportSourceSystem_embed {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).source))
    (i k : ι) (hik : i ≤ k) (x : (T i).source) :
    (transportSourceSystem h B).embed i k hik x =
      ProtectedStage.castSourcePoint (congrFun h k)
        (B.embed i k hik
          (ProtectedStage.castSourcePoint (congrFun h i).symm x)) := by
  subst T
  simp [transportSourceSystem]

theorem transportSourceSystem_project {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).source))
    (i k : ι) (hik : i ≤ k) (z : (T k).source) :
    (transportSourceSystem h B).project i k hik z =
      ProtectedStage.castSourcePoint (congrFun h i)
        (B.project i k hik
          (ProtectedStage.castSourcePoint (congrFun h k).symm z)) := by
  subst T
  simp [transportSourceSystem]

theorem transportTargetSystem_embed {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).target))
    (i k : ι) (hik : i ≤ k) (x : (T i).target) :
    (transportTargetSystem h B).embed i k hik x =
      ProtectedStage.castTargetPoint (congrFun h k)
        (B.embed i k hik
          (ProtectedStage.castTargetPoint (congrFun h i).symm x)) := by
  subst T
  simp [transportTargetSystem]

theorem transportTargetSystem_project {ι : Type} [LinearOrder ι]
    {r : ℝ} {S T : ι → ProtectedStage.{0} r} (h : S = T)
    (B : CoherentBiSystem (fun i => (S i).target))
    (i k : ι) (hik : i ≤ k) (z : (T k).target) :
    (transportTargetSystem h B).project i k hik z =
      ProtectedStage.castTargetPoint (congrFun h i)
        (B.project i k hik
          (ProtectedStage.castTargetPoint (congrFun h k).symm z)) := by
  subst T
  simp [transportTargetSystem]

/-- Equality of protected chains from equality after transporting the two
dependent bidirectional systems. -/
theorem ext_transport {ι : Type} [LinearOrder ι] [Nonempty ι]
    {r L : ℝ} {C D : ProtectedChain (ι := ι) r L}
    (hstage : C.stage = D.stage)
    (hsource : transportSourceSystem hstage C.sourceSystem = D.sourceSystem)
    (htarget : transportTargetSystem hstage C.targetSystem = D.targetSystem) :
    C = D := by
  cases C
  cases D
  dsimp at hstage hsource htarget ⊢
  cases hstage
  cases hsource
  cases htarget
  rfl

theorem source_embed_transport {ι : Type} [LinearOrder ι]
    {r L : ℝ} {C D : ProtectedChain (ι := ι) r L} (h : C = D)
    (i k : ι) (hik : i ≤ k) (x : (C.stage i).source) :
    ProtectedStage.castSourcePoint
        (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage k) h)
        (C.sourceSystem.embed i k hik x) =
      D.sourceSystem.embed i k hik
        (ProtectedStage.castSourcePoint
          (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage i) h) x) := by
  subst D
  simp

theorem target_embed_transport {ι : Type} [LinearOrder ι]
    {r L : ℝ} {C D : ProtectedChain (ι := ι) r L} (h : C = D)
    (i k : ι) (hik : i ≤ k) (x : (C.stage i).target) :
    ProtectedStage.castTargetPoint
        (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage k) h)
        (C.targetSystem.embed i k hik x) =
      D.targetSystem.embed i k hik
        (ProtectedStage.castTargetPoint
          (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage i) h) x) := by
  subst D
  simp

theorem source_project_transport {ι : Type} [LinearOrder ι]
    {r L : ℝ} {C D : ProtectedChain (ι := ι) r L} (h : C = D)
    (i k : ι) (hik : i ≤ k) (z : (C.stage k).source) :
    ProtectedStage.castSourcePoint
        (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage i) h)
        (C.sourceSystem.project i k hik z) =
      D.sourceSystem.project i k hik
        (ProtectedStage.castSourcePoint
          (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage k) h) z) := by
  subst D
  simp

theorem target_project_transport {ι : Type} [LinearOrder ι]
    {r L : ℝ} {C D : ProtectedChain (ι := ι) r L} (h : C = D)
    (i k : ι) (hik : i ≤ k) (z : (C.stage k).target) :
    ProtectedStage.castTargetPoint
        (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage i) h)
        (C.targetSystem.project i k hik z) =
      D.targetSystem.project i k hik
        (ProtectedStage.castTargetPoint
          (congrArg (fun E : ProtectedChain (ι := ι) r L => E.stage k) h) z) := by
  subst D
  simp

end ProtectedChain

end ScottishBook155
