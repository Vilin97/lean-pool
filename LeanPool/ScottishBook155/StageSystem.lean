/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.Claim14
import LeanPool.ScottishBook155.ProtectedExtensionTheorem

/-!
# Successor-stage interface for claim 14

This file packages exactly the data exported by the protected one-point
extension in the form needed by the transfinite construction.
-/

namespace ScottishBook155

open ENNReal WithLp

universe u

/-- A stage map with the two invariants maintained throughout the recursion. -/
structure ProtectedStage (r : ℝ) where
  source : RealBanachSpace.{u}
  target : RealBanachSpace.{u}
  map : source → target
  injective : Function.Injective map
  preservesUpTo : PreservesUpTo r map

/-- The complete interface of one active successor transition. -/
structure ProtectedSuccessor {r : ℝ} (S : ProtectedStage.{u} r)
    (L : ℝ) (y : S.target) where
  next : ProtectedStage.{u} r
  height : ℝ
  sourceEquiv : OneSum S.source ≃ₗᵢ[ℝ] next.source
  targetEmbedding : S.target →ₗᵢ[ℝ] next.target
  targetRetraction : next.target →L[ℝ] S.target
  compatible : ∀ m,
    next.map (sourceEquiv (toLp 1 (m, 0))) = targetEmbedding (S.map m)
  hits : next.map (sourceEquiv (toLp 1 ((0 : S.source), height))) =
    targetEmbedding y
  retracts : ∀ n, targetRetraction (targetEmbedding n) = n
  contractive : ∀ z, ‖targetRetraction z‖ ≤ ‖z‖
  flatRecovery : ∀ (m : S.source) (s : ℝ), |s| ≤ L →
    targetRetraction (next.map (sourceEquiv (toLp 1 (m, s)))) = S.map m

/-- The canonical old-source embedding into an l-one successor source. -/
noncomputable def oneSumSourceEmbedding (M : RealBanachSpace.{u}) :
    M →ₗᵢ[ℝ] OneSum M where
  toLinearMap :=
    { toFun := fun m => toLp 1 (m, 0)
      map_add' := by
        intro x y
        rw [← WithLp.toLp_add]
        apply (WithLp.toLp_injective (p := (1 : ℝ≥0∞)))
        simp
      map_smul' := by
        intro c x
        rw [← WithLp.toLp_smul]
        apply (WithLp.toLp_injective (p := (1 : ℝ≥0∞)))
        simp }
  norm_map' m := WithLp.norm_toLp_fst 1 M ℝ m

/-- The source embedding associated to a protected successor. -/
noncomputable def ProtectedSuccessor.sourceEmbedding
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) : S.source →ₗᵢ[ℝ] P.next.source :=
  P.sourceEquiv.toLinearIsometry.comp (oneSumSourceEmbedding S.source)

/-- Projection of a protected successor source onto the old source. -/
noncomputable def ProtectedSuccessor.sourceProjection
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) : P.next.source →L[ℝ] S.source :=
  (WithLp.fstL 1 ℝ S.source ℝ).comp
    P.sourceEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem ProtectedSuccessor.sourceEmbedding_apply
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) (m : S.source) :
    P.sourceEmbedding m = P.sourceEquiv (toLp 1 (m, 0)) :=
  rfl

@[simp]
theorem ProtectedSuccessor.sourceProjection_apply
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) (m : S.source) (s : ℝ) :
    P.sourceProjection (P.sourceEquiv (toLp 1 (m, s))) = m := by
  simp [ProtectedSuccessor.sourceProjection]

/-- The source projection is a left inverse of the old-stage embedding. -/
theorem ProtectedSuccessor.sourceProjection_retracts
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) (m : S.source) :
    P.sourceProjection (P.sourceEmbedding m) = m := by
  simp

/-- The successor retraction recovers the old stage throughout the uniform
source band of radius `L`. -/
theorem ProtectedSuccessor.recovers_of_dist_le
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) (z : P.next.source)
    (hz : dist z (P.sourceEmbedding (P.sourceProjection z)) ≤ L) :
    P.targetRetraction (P.next.map z) = S.map (P.sourceProjection z) := by
  let w : OneSum S.source := P.sourceEquiv.symm z
  let m : S.source := w.fst
  let s : ℝ := w.snd
  have hw : toLp 1 (m, s) = w := rfl
  have hzrepr : z = P.sourceEquiv (toLp 1 (m, s)) := by
    rw [hw]
    exact P.sourceEquiv.apply_symm_apply z |>.symm
  have hproj : P.sourceProjection z = m := by
    rw [hzrepr]
    exact P.sourceProjection_apply m s
  have hdist : dist z (P.sourceEmbedding (P.sourceProjection z)) = |s| := by
    rw [hzrepr, P.sourceProjection_apply, P.sourceEmbedding_apply,
      P.sourceEquiv.isometry.dist_eq,
      oneSum_dist_eq]
    simp
  rw [hzrepr, P.sourceProjection_apply]
  exact P.flatRecovery m s (hdist ▸ hz)

/-- A uniform successor transition, covering both active protected
extensions and idle steps. -/
structure ProtectedTransition {r : ℝ} (S : ProtectedStage.{u} r) (L : ℝ) where
  next : ProtectedStage.{u} r
  sourceEmbedding : S.source →ₗᵢ[ℝ] next.source
  sourceProjection : next.source →L[ℝ] S.source
  targetEmbedding : S.target →ₗᵢ[ℝ] next.target
  targetProjection : next.target →L[ℝ] S.target
  compatible : ∀ x, next.map (sourceEmbedding x) = targetEmbedding (S.map x)
  sourceRetracts : ∀ x, sourceProjection (sourceEmbedding x) = x
  targetRetracts : ∀ y, targetProjection (targetEmbedding y) = y
  sourceContractive : ∀ z, ‖sourceProjection z‖ ≤ ‖z‖
  targetContractive : ∀ z, ‖targetProjection z‖ ≤ ‖z‖
  sourceNearest : ∀ z m,
    dist z (sourceEmbedding (sourceProjection z)) ≤ dist z (sourceEmbedding m)
  recovers : ∀ z, dist z (sourceEmbedding (sourceProjection z)) ≤ L →
    targetProjection (next.map z) = S.map (sourceProjection z)

/-- An active protected successor as a uniform transition. -/
noncomputable def ProtectedSuccessor.toTransition
    {r L : ℝ} {S : ProtectedStage.{u} r} {y : S.target}
    (P : ProtectedSuccessor S L y) : ProtectedTransition S L where
  next := P.next
  sourceEmbedding := P.sourceEmbedding
  sourceProjection := P.sourceProjection
  targetEmbedding := P.targetEmbedding
  targetProjection := P.targetRetraction
  compatible := P.compatible
  sourceRetracts := P.sourceProjection_retracts
  targetRetracts := P.retracts
  sourceContractive z := by
    change ‖(WithLp.fstL 1 ℝ S.source ℝ)
        (P.sourceEquiv.symm z)‖ ≤ ‖z‖
    calc
      ‖(WithLp.fstL 1 ℝ S.source ℝ) (P.sourceEquiv.symm z)‖ ≤
          ‖P.sourceEquiv.symm z‖ := by
            simpa using WithLp.norm_fst_le S.source (P.sourceEquiv.symm z)
      _ = ‖z‖ := P.sourceEquiv.symm.norm_map z
  targetContractive := P.contractive
  sourceNearest z n := by
    let w : OneSum S.source := P.sourceEquiv.symm z
    let m : S.source := w.fst
    let s : ℝ := w.snd
    have hw : toLp 1 (m, s) = w := rfl
    have hzrepr : z = P.sourceEquiv (toLp 1 (m, s)) := by
      rw [hw]
      exact P.sourceEquiv.apply_symm_apply z |>.symm
    rw [hzrepr, P.sourceProjection_apply, P.sourceEmbedding_apply,
      P.sourceEmbedding_apply, P.sourceEquiv.isometry.dist_eq,
      P.sourceEquiv.isometry.dist_eq, oneSum_dist_eq, oneSum_dist_eq]
    simp
  recovers := P.recovers_of_dist_le

/-- The idle successor transition. -/
noncomputable def idleTransition {r L : ℝ} (S : ProtectedStage.{u} r) :
    ProtectedTransition S L where
  next := S
  sourceEmbedding := LinearIsometry.id
  sourceProjection := ContinuousLinearMap.id ℝ S.source
  targetEmbedding := LinearIsometry.id
  targetProjection := ContinuousLinearMap.id ℝ S.target
  compatible := fun _ => rfl
  sourceRetracts := fun _ => rfl
  targetRetracts := fun _ => rfl
  sourceContractive := fun _ => le_rfl
  targetContractive := fun _ => le_rfl
  sourceNearest := fun _ _ => by simp
  recovers := fun _ _ => rfl

/-- Claim 13 supplies every active successor transition required by the
claim-14 recursion. -/
noncomputable def protectedSuccessor
    {r L : ℝ} (hr : 0 < r) (hL : 0 < L)
    (S : ProtectedStage.{u} r) (y : S.target) (hy : y ∉ Set.range S.map) :
    ProtectedSuccessor S L y := by
  let H := protectedHeight S.map y L r
  let hV := preservesUpTo_nonexpansive hr S.preservesUpTo
  have hLH : L < H := protectedHeight_L_lt hL hr
  have hattachGap : dist (S.map 0) y < H := protectedHeight_attachment_gap hL hr
  let hattach : ∀ p q,
      dist (attachmentMap S.map y p) (attachmentMap S.map y q) ≤
        dist (attachmentPoint (0 : S.source) H p) (attachmentPoint 0 H q) :=
    attachmentMap_dist_le hV 0 y hattachGap
  have hgap : dist y (S.map 0) ≤ H - L := protectedHeight_retraction_gap hr
  have hH : 2 * r + dist (S.map 0) y < H := protectedHeight_short_gap hL hr
  let E := RealBanachSpace.ofType (OneSum S.source)
  let F := RealBanachSpace.ofType
    (ProtectedExtensionSpace S.map 0 y H hattach)
  let W : E → F :=
    protectedExtensionSourceEmbedding S.map 0 y L H hattach hLH hL.le hV hgap
  let T : S.target →ₗᵢ[ℝ] F :=
    protectedExtensionTargetLinearIsometry S.map 0 y H hattach
  let R : F →L[ℝ] S.target :=
    protectedExtensionProjection S.map 0 y H hattach
  let next : ProtectedStage r :=
    { source := E
      target := F
      map := W
      injective := protectedExtensionSourceEmbedding_injective S.map 0 y L H hattach
        hLH hL.le hV hgap S.injective hy
      preservesUpTo := protectedExtensionSourceEmbedding_preservesUpTo hattach hLH hL.le
        hV hgap hr hH S.preservesUpTo }
  exact
    { next := next
      height := H
      sourceEquiv := LinearIsometryEquiv.refl ℝ (OneSum S.source)
      targetEmbedding := T
      targetRetraction := R
      compatible := fun m =>
        protectedExtensionSourceEmbedding_base S.map 0 y L H hattach hLH hL.le
          hV hgap m
      hits := protectedExtensionSourceEmbedding_hits S.map 0 y L H hattach hLH hL.le
        hV hgap
      retracts := fun n => protectedExtensionProjection_target S.map 0 y H hattach n
      contractive := fun z => protectedExtensionProjection_norm_le S.map 0 y H hattach z
      flatRecovery := fun m s hs =>
        protectedExtensionProjection_source_of_le S.map 0 y L H hattach hLH hL.le
          hV hgap m (le_trans (le_abs_self s) hs) }

end ScottishBook155
