/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.BentSeedStage


/-!
# Final-union assembly for claim 14

The transfinite recursion is separated from the last metric argument.  The
data below state exactly what the increasing union and bookkeeping must
provide; the theorem proves that those data yield the canonical claim-14
witness.
-/

@[expose] public section

namespace ScottishBook155

universe u

/-- The output required from the transfinite recursion before the final metric
deduction.  Every pair of source points must lie in one common protected stage,
and the initial bent stage must remain compatible with the final map. -/
structure FinalAssemblyData where
  /-- The final real Banach source assembled from the protected stages. -/
  source : RealBanachSpace.{u}
  /-- The final real Banach target assembled from the protected stages. -/
  target : RealBanachSpace.{u}
  /-- The final map whose restriction to each stage agrees with that stage map. -/
  map : source → target
  /-- The type indexing the protected stages used in the final assembly. -/
  stageIndex : Type u
  /-- The family of stages that preserve distances up to one half. -/
  stage : stageIndex → ProtectedStage.{u} ((1 : ℝ) / 2)
  /-- Linear isometric embeddings of the stage sources into the final source. -/
  sourceEmbedding : ∀ i, (stage i).source →ₗᵢ[ℝ] source
  /-- Linear isometric embeddings of the stage targets into the final target. -/
  targetEmbedding : ∀ i, (stage i).target →ₗᵢ[ℝ] target
  compatible : ∀ i x,
    map (sourceEmbedding i x) = targetEmbedding i ((stage i).map x)
  commonStage : ∀ x y : source, ∃ (i : stageIndex)
    (x₀ y₀ : (stage i).source),
      sourceEmbedding i x₀ = x ∧ sourceEmbedding i y₀ = y
  surjective : Function.Surjective map
  /-- The stage carrying the initial bent-map witness. -/
  seedIndex : stageIndex
  /-- The isometric inclusion of the real-line source of the bent seed into its stage. -/
  seedSource : ℝ →ₗᵢ[ℝ] (stage seedIndex).source
  /-- The isometric inclusion of the one-sum target of the bent seed into its stage. -/
  seedTarget : OneSum ℝ →ₗᵢ[ℝ] (stage seedIndex).target
  seedCompatible : ∀ t,
    (stage seedIndex).map (seedSource t) = seedTarget (bentMapL1 t)

theorem FinalAssemblyData.injective (D : FinalAssemblyData.{u}) :
    Function.Injective D.map := by
  intro x y hxy
  obtain ⟨i, x₀, y₀, rfl, rfl⟩ := D.commonStage x y
  rw [D.compatible, D.compatible] at hxy
  have hstage : (D.stage i).map x₀ = (D.stage i).map y₀ :=
    (D.targetEmbedding i).injective hxy
  exact congrArg (D.sourceEmbedding i) ((D.stage i).injective hstage)

theorem FinalAssemblyData.preservesUpTo (D : FinalAssemblyData.{u}) :
    PreservesUpTo ((1 : ℝ) / 2) D.map := by
  intro x y hxy
  obtain ⟨i, x₀, y₀, rfl, rfl⟩ := D.commonStage x y
  rw [D.compatible, D.compatible, (D.targetEmbedding i).isometry.dist_eq,
    (D.sourceEmbedding i).isometry.dist_eq]
  apply (D.stage i).preservesUpTo
  simpa only [(D.sourceEmbedding i).isometry.dist_eq] using hxy

theorem FinalAssemblyData.contractsSeed (D : FinalAssemblyData.{u}) :
    dist (D.map (D.sourceEmbedding D.seedIndex (D.seedSource (-1))))
        (D.map (D.sourceEmbedding D.seedIndex (D.seedSource 2))) ≠
      dist (D.sourceEmbedding D.seedIndex (D.seedSource (-1)))
        (D.sourceEmbedding D.seedIndex (D.seedSource 2)) := by
  rw [D.compatible, D.compatible, D.seedCompatible, D.seedCompatible,
    (D.targetEmbedding D.seedIndex).isometry.dist_eq,
    (D.seedTarget).isometry.dist_eq,
    (D.sourceEmbedding D.seedIndex).isometry.dist_eq,
    (D.seedSource).isometry.dist_eq]
  obtain ⟨himage, hsource⟩ := bentMapL1_contraction
  rw [himage, hsource]
  norm_num

/-- A completed transfinite assembly yields the exact canonical claim 14. -/
theorem claim14_of_finalAssembly (D : FinalAssemblyData.{u}) :
    Claim14.{u} := by
  refine ⟨claim14WitnessOfHalfScale D.source D.target D.map
    ⟨D.injective, D.surjective⟩ D.preservesUpTo
    (p := D.sourceEmbedding D.seedIndex (D.seedSource (-1)))
    (q := D.sourceEmbedding D.seedIndex (D.seedSource 2)) D.contractsSeed⟩

end ScottishBook155
