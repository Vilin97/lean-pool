/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.ProtectedChain


/-!
# The limit clause for protected chains

The uniform recovery identity passes from a coherent protected chain to its
completed direct limit. Together with `DirectedLimitStage`, this constructs a
new protected stage at every nonempty limit segment.
-/

@[expose] public section

namespace ScottishBook155

open Filter

universe u

namespace ProtectedChain

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable {r L : ℝ} (C : ProtectedChain (ι := ι) r L)

noncomputable local instance sourceDirectedSystem :
    DirectedSystem (fun i => (C.stage i).source)
      (C.sourceSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.sourceSystem

noncomputable local instance targetDirectedSystem :
    DirectedSystem (fun i => (C.stage i).target)
      (C.targetSystem.embed · · ·) :=
  CoherentBiSystem.directedSystem _ C.targetSystem

/-- The completed direct limit of the source spaces in the protected chain. -/
abbrev LimitSource := NormedDirectLimit.CompletedCarrier
  (fun i => (C.stage i).source) C.sourceSystem.embed

/-- The completed direct limit of the target spaces in the protected chain. -/
abbrev LimitTarget := NormedDirectLimit.CompletedCarrier
  (fun i => (C.stage i).target) C.targetSystem.embed

/-- The compatible source projections, packaged for extension to the completed limit. -/
noncomputable def sourceProjectionSystem :=
  CoherentBiSystem.projectionSystem _ C.sourceSystem

/-- The compatible target projections, packaged for extension to the completed limit. -/
noncomputable def targetProjectionSystem :=
  CoherentBiSystem.projectionSystem _ C.targetSystem

/-- The map between completed limits induced by the uniformly nonexpansive stage maps. -/
noncomputable def completedMap : C.LimitSource → C.LimitTarget :=
  DirectedLimitStage.limitMap _ _ C.sourceSystem.embed C.targetSystem.embed
    (fun i => (C.stage i).map)

private theorem stage_recovery_band (a k : ι) (hak : a ≤ k)
    (xk : (C.stage k).source)
    (hlt : dist (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)
      (CoherentRetractionLimit.ProjectionSystem.approx _ C.sourceSystem.embed
        C.sourceProjectionSystem a
        (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)) < L) :
    dist xk (C.sourceSystem.embed a k hak (C.sourceSystem.project a k hak xk)) < L := by
  rw [CoherentRetractionLimit.ProjectionSystem.approx] at hlt
  change dist (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)
      (NormedDirectLimit.completedOf _ C.sourceSystem.embed a
        (CoherentRetractionLimit.ProjectionFamily.completedProjection _
          C.sourceSystem.embed
          (CoherentRetractionLimit.ProjectionSystem.family _
            C.sourceSystem.embed C.sourceProjectionSystem a)
          (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk))) < L
    at hlt
  have hsproj :
      CoherentRetractionLimit.ProjectionFamily.completedProjection _
          C.sourceSystem.embed
          (CoherentRetractionLimit.ProjectionSystem.family _
            C.sourceSystem.embed C.sourceProjectionSystem a)
          (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk) =
        CoherentBiSystem.totalProject _ C.sourceSystem a k xk := by
    rw [CoherentRetractionLimit.ProjectionFamily.completedProjection_completedOf]
    rfl
  rw [hsproj] at hlt
  change dist (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)
      (NormedDirectLimit.completedOf _ C.sourceSystem.embed a
        (CoherentBiSystem.totalProject _ C.sourceSystem a k xk)) < L at hlt
  rw [CoherentBiSystem.totalProject_of_ge _ C.sourceSystem hak] at hlt
  change dist (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)
      (NormedDirectLimit.completedOf _ C.sourceSystem.embed a
        (C.sourceSystem.project a k hak xk)) < L at hlt
  rw [← NormedDirectLimit.completedOf_f _ C.sourceSystem.embed hak] at hlt
  simpa only [
    (NormedDirectLimit.completedOf _ C.sourceSystem.embed k).isometry.dist_eq]
    using hlt

/-- Recovery to a fixed component extends from the algebraic direct limit to
the completed limit throughout the open recovery band. -/
theorem completed_recovery_of_dist_lt (hr : 0 < r) (a : ι)
    (x : C.LimitSource)
    (hx : dist x (CoherentRetractionLimit.ProjectionSystem.approx _
      C.sourceSystem.embed C.sourceProjectionSystem a x) < L) :
    CoherentRetractionLimit.ProjectionFamily.completedProjection _
        C.targetSystem.embed
        (CoherentRetractionLimit.ProjectionSystem.family _
          C.targetSystem.embed C.targetProjectionSystem a)
        (C.completedMap x) =
      (C.stage a).map
        (CoherentRetractionLimit.ProjectionFamily.completedProjection _
          C.sourceSystem.embed
          (CoherentRetractionLimit.ProjectionSystem.family _
            C.sourceSystem.embed C.sourceProjectionSystem a) x) := by
  let sApprox := fun z : C.LimitSource =>
    CoherentRetractionLimit.ProjectionSystem.approx _ C.sourceSystem.embed
      C.sourceProjectionSystem a z
  let tProject :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection _
      C.targetSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.targetSystem.embed
        C.targetProjectionSystem a)
  let sProject :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection _
      C.sourceSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.sourceSystem.embed
        C.sourceProjectionSystem a)
  let f := C.completedMap
  have hsApprox : Continuous sApprox :=
    (NormedDirectLimit.completedOf _ C.sourceSystem.embed a).continuous.comp
      (CoherentRetractionLimit.ProjectionFamily.completedProjection _
        C.sourceSystem.embed
        (CoherentRetractionLimit.ProjectionSystem.family _ C.sourceSystem.embed
          C.sourceProjectionSystem a)).continuous
  have hf : Continuous f :=
    (CompletedLimitMap.completedMap_lipschitz _ _ C.sourceSystem.embed
      C.targetSystem.embed (fun i => (C.stage i).map) C.compatible
      (C.stage_nonexpansive hr)).continuous
  have ht : Continuous (fun z => tProject (f z)) := tProject.continuous.comp hf
  have hstage : Continuous (C.stage a).map :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun p q => by
      convert C.stage_nonexpansive hr a p q using 1
      norm_num).continuous
  have hs : Continuous (fun z => (C.stage a).map (sProject z)) :=
    hstage.comp sProject.continuous
  let P : C.LimitSource → Prop := fun z =>
    L ≤ dist z (sApprox z) ∨ tProject (f z) = (C.stage a).map (sProject z)
  have hPclosed : IsClosed {z | P z} := by
    change IsClosed ({z | L ≤ dist z (sApprox z)} ∪
      {z | tProject (f z) = (C.stage a).map (sProject z)})
    exact (isClosed_le continuous_const (continuous_id.dist hsApprox)).union
      (isClosed_eq ht hs)
  have hP : P x := by
    refine UniformSpace.Completion.denseRange_coe.induction_on x hPclosed ?_
    intro d
    let i := NormedDirectLimit.reprIndex _ C.sourceSystem.embed d
    let xi := NormedDirectLimit.reprValue _ C.sourceSystem.embed d
    have hdi := NormedDirectLimit.repr_spec _ C.sourceSystem.embed d
    let k := max a i
    have hak : a ≤ k := le_max_left _ _
    have hik : i ≤ k := le_max_right _ _
    let xk := C.sourceSystem.embed i k hik xi
    have hki : NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk =
        (↑d : C.LimitSource) := by
      calc
        NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk =
            NormedDirectLimit.completedOf _ C.sourceSystem.embed i xi :=
          NormedDirectLimit.completedOf_f _ C.sourceSystem.embed hik xi
        _ = (↑d : C.LimitSource) := congrArg ((↑) :
          NormedDirectLimit.Carrier _ C.sourceSystem.embed → C.LimitSource) hdi
    rw [← hki]
    by_cases hband : L ≤ dist
        (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)
        (sApprox (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk))
    · exact Or.inl hband
    · right
      have hstageBand : dist xk
          (C.sourceSystem.embed a k hak (C.sourceSystem.project a k hak xk)) < L :=
        C.stage_recovery_band a k hak xk (lt_of_not_ge hband)
      dsimp [tProject, sProject, f, ProtectedChain.completedMap]
      unfold DirectedLimitStage.limitMap
      change
        CoherentRetractionLimit.ProjectionFamily.completedProjection _
            C.targetSystem.embed
            (CoherentRetractionLimit.ProjectionSystem.family _
              C.targetSystem.embed C.targetProjectionSystem a)
            (CompletedLimitMap.completedMap _ _ C.sourceSystem.embed
              C.targetSystem.embed (fun i => (C.stage i).map)
              (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk)) =
          (C.stage a).map
            (CoherentRetractionLimit.ProjectionFamily.completedProjection _
              C.sourceSystem.embed
              (CoherentRetractionLimit.ProjectionSystem.family _
                C.sourceSystem.embed C.sourceProjectionSystem a)
              (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk))
      have hfcomp :
          CompletedLimitMap.completedMap _ _ C.sourceSystem.embed
              C.targetSystem.embed (fun i => (C.stage i).map)
              (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk) =
            NormedDirectLimit.completedOf _ C.targetSystem.embed k
              ((C.stage k).map xk) := by
        exact CompletedLimitMap.completedMap_completedOf _ _
          C.sourceSystem.embed C.targetSystem.embed (fun i => (C.stage i).map)
          C.compatible (C.stage_nonexpansive hr) k xk
      rw [hfcomp]
      have htproj :
          CoherentRetractionLimit.ProjectionFamily.completedProjection _
              C.targetSystem.embed
              (CoherentRetractionLimit.ProjectionSystem.family _
                C.targetSystem.embed C.targetProjectionSystem a)
              (NormedDirectLimit.completedOf _ C.targetSystem.embed k
                ((C.stage k).map xk)) =
            CoherentBiSystem.totalProject _ C.targetSystem a k
              ((C.stage k).map xk) := by
        rw [CoherentRetractionLimit.ProjectionFamily.completedProjection_completedOf]
        rfl
      rw [htproj]
      have hsproj :
          CoherentRetractionLimit.ProjectionFamily.completedProjection _
              C.sourceSystem.embed
              (CoherentRetractionLimit.ProjectionSystem.family _
                C.sourceSystem.embed C.sourceProjectionSystem a)
              (NormedDirectLimit.completedOf _ C.sourceSystem.embed k xk) =
            CoherentBiSystem.totalProject _ C.sourceSystem a k xk := by
        rw [CoherentRetractionLimit.ProjectionFamily.completedProjection_completedOf]
        rfl
      rw [hsproj]
      change CoherentBiSystem.totalProject _ C.targetSystem a k
          ((C.stage k).map xk) =
        (C.stage a).map
          (CoherentBiSystem.totalProject _ C.sourceSystem a k xk)
      rw [CoherentBiSystem.totalProject_of_ge _ C.targetSystem hak,
        CoherentBiSystem.totalProject_of_ge _ C.sourceSystem hak]
      exact C.recovers a k hak xk hstageBand
  rcases hP with hfar | heq
  · exact False.elim ((not_le_of_gt hx) hfar)
  · exact heq

/-- The completed direct limit of a protected chain is again a protected
stage.  This is the limit clause used by the transfinite recursion. -/
noncomputable def limitStage (hr : 0 < r) (hL : 0 < L) :
    ProtectedStage.{u} r :=
  DirectedLimitStage.toProtectedStageOfBoundedLt _ _
    C.sourceSystem.embed C.targetSystem.embed (fun i => (C.stage i).map)
    C.compatible C.sourceProjectionSystem C.targetProjectionSystem hL
    (fun i => (C.stage i).injective)
    (fun i => (C.stage i).preservesUpTo)
    (C.stage_nonexpansive hr)
    (C.completed_recovery_of_dist_lt hr)

/-- Every component is coherently linked to the completed limit stage. -/
noncomputable def toLimitLink (hr : 0 < r) (hL : 0 < L) (a : ι) :
    ProtectedLink (C.stage a) (C.limitStage hr hL) L where
  sourceEmbedding := NormedDirectLimit.completedOf _ C.sourceSystem.embed a
  sourceProjection :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection _
      C.sourceSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.sourceSystem.embed
        C.sourceProjectionSystem a)
  targetEmbedding := NormedDirectLimit.completedOf _ C.targetSystem.embed a
  targetProjection :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection _
      C.targetSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.targetSystem.embed
        C.targetProjectionSystem a)
  compatible x := by
    change C.completedMap
        (NormedDirectLimit.completedOf _ C.sourceSystem.embed a x) =
      NormedDirectLimit.completedOf _ C.targetSystem.embed a ((C.stage a).map x)
    exact CompletedLimitMap.completedMap_completedOf _ _ C.sourceSystem.embed
      C.targetSystem.embed (fun i => (C.stage i).map) C.compatible
      (C.stage_nonexpansive hr) a x
  sourceRetracts x :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection_retracts _
      C.sourceSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.sourceSystem.embed
        C.sourceProjectionSystem a) x
  targetRetracts y :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection_retracts _
      C.targetSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.targetSystem.embed
        C.targetProjectionSystem a) y
  sourceContractive z :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection_norm_le _
      C.sourceSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.sourceSystem.embed
        C.sourceProjectionSystem a) z
  targetContractive z :=
    CoherentRetractionLimit.ProjectionFamily.completedProjection_norm_le _
      C.targetSystem.embed
      (CoherentRetractionLimit.ProjectionSystem.family _ C.targetSystem.embed
        C.targetProjectionSystem a) z
  recovers z hz := C.completed_recovery_of_dist_lt hr a z hz

end ProtectedChain

end ScottishBook155
