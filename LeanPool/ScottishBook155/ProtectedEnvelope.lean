/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.CombinedEmbedding
import LeanPool.ScottishBook155.DenseSequenceCardinal
import LeanPool.ScottishBook155.RetractiveEnvelope

/-!
# A globally injective linearly retractive envelope

The retractive dual-evaluation coordinate supplies the linear projection and
all selected exact distances.  The collapsed-quotient Kuratowski coordinate
separates the remaining pairs without changing those metric estimates.
-/

namespace ScottishBook155

open ENNReal lp

noncomputable section

universe u v

/-- The ambient product carrying the retractive and quotient-Kuratowski
coordinates. -/
abbrev ProtectedEnvelopeAmbient (P : Type u) (N : Type v) [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :=
  RetractiveEnvelope P N j × ℓ^∞(CollapsedQuotient P (Set.range j), ℝ)

/-- A generating point with an arbitrary old-target coordinate.  Allowing the
first coordinate to vary independently ensures that every retractive metric
embedding lands in the same closed linear span. -/
noncomputable def protectedEnvelopeGenerator {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (z : N × P) : ProtectedEnvelopeAmbient P N j :=
  ((z.1, relativeEvaluation j z.2),
    quotientKuratowski (Set.range j) (j 0) z.2)

/-- The actual protected envelope is the closed linear span of the generating
metric coordinates, rather than the whole ambient function space.  This is
the density-controlled target used in the transfinite construction. -/
abbrev ProtectedEnvelope (P : Type u) (N : Type v) [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :=
  (Submodule.span ℝ (Set.range (protectedEnvelopeGenerator j))).topologicalClosure

/-- Finite linear combinations of generators, included in the closed span. -/
noncomputable def protectedEnvelopeDenseMap {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) : (N × P →₀ ℝ) → ProtectedEnvelope P N j := fun c =>
  ⟨Finsupp.linearCombination ℝ (protectedEnvelopeGenerator j) c, by
    apply (Submodule.span ℝ
      (Set.range (protectedEnvelopeGenerator j))).le_topologicalClosure
    exact (Finsupp.mem_span_range_iff_exists_finsupp).2 ⟨c, rfl⟩⟩

/-- Finite linear combinations of generators are dense in the protected
envelope. -/
theorem protectedEnvelopeDenseMap_denseRange {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) : DenseRange (protectedEnvelopeDenseMap j) := by
  intro z
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hz : (z : ProtectedEnvelopeAmbient P N j) ∈ closure
      (Submodule.span ℝ
        (Set.range (protectedEnvelopeGenerator j)) : Set
          (ProtectedEnvelopeAmbient P N j)) := z.property
  obtain ⟨y, hyspan, hyz⟩ := (Metric.mem_closure_iff.mp hz) ε hε
  obtain ⟨c, hc⟩ :=
    (Finsupp.mem_span_range_iff_exists_finsupp).1 hyspan
  refine ⟨protectedEnvelopeDenseMap j c, ⟨c, rfl⟩, ?_⟩
  change dist (z : ProtectedEnvelopeAmbient P N j)
      (Finsupp.linearCombination ℝ (protectedEnvelopeGenerator j) c) < ε
  change dist (z : ProtectedEnvelopeAmbient P N j)
      (c.sum fun i a => a • protectedEnvelopeGenerator j i) < ε
  rw [hc]
  exact hyz

/-- The closed span embeds into sequences of finite generator combinations.
This is the cardinal estimate used at active successor stages. -/
noncomputable def protectedEnvelopeSequenceEmbedding {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) :
    ProtectedEnvelope P N j ↪ (ℕ → (N × P →₀ ℝ)) :=
  DenseSequenceCardinal.sequenceEmbedding (protectedEnvelopeDenseMap j)
    (protectedEnvelopeDenseMap_denseRange j)

/-- The raw metric coordinate in the ambient product. -/
noncomputable def protectedEnvelopeEmbeddingAmbient {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N) (p : P) : ProtectedEnvelopeAmbient P N j :=
  combinedEmbedding (retractiveEmbedding j R) (Set.range j) (j 0) p

/-- The final metric embedding, based at the zero point of the old target. -/
noncomputable def protectedEnvelopeEmbedding {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N) (p : P) : ProtectedEnvelope P N j :=
  ⟨protectedEnvelopeEmbeddingAmbient j R p, by
    apply (Submodule.span ℝ
      (Set.range (protectedEnvelopeGenerator j))).le_topologicalClosure
    exact Submodule.subset_span ⟨(R p, p), rfl⟩⟩

/-- The raw old-target embedding in the ambient product. -/
noncomputable def protectedTargetLinearAmbient {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    N →ₗ[ℝ] ProtectedEnvelopeAmbient P N j where
  toFun n := (retractiveTargetLinear j n, 0)
  map_add' n m := by simp
  map_smul' c n := by simp

theorem protectedEnvelopeGenerator_target {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (n : N) :
    protectedEnvelopeGenerator j (n, j n) = protectedTargetLinearAmbient j n := by
  change combinedEmbedding (retractiveEmbedding j (fun _ => n))
      (Set.range j) (j 0) (j n) = (retractiveTargetLinear j n, 0)
  rw [combinedEmbedding_of_mem (Set.mem_range_self 0) (Set.mem_range_self n)]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact (relativeTargetLinear_apply j n).symm
  · rfl

/-- The old target embeds linearly into the density-controlled envelope. -/
noncomputable def protectedTargetLinear {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    N →ₗ[ℝ] ProtectedEnvelope P N j where
  toFun n := ⟨protectedTargetLinearAmbient j n, by
    apply (Submodule.span ℝ
      (Set.range (protectedEnvelopeGenerator j))).le_topologicalClosure
    exact Submodule.subset_span
      ⟨(n, j n), protectedEnvelopeGenerator_target j n⟩⟩
  map_add' n m := by
    apply Subtype.ext
    exact (protectedTargetLinearAmbient j).map_add n m
  map_smul' c n := by
    apply Subtype.ext
    exact (protectedTargetLinearAmbient j).map_smul c n

theorem norm_protectedTargetLinear_eq {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (hj : Isometry j) (n : N) :
    ‖protectedTargetLinear j n‖ = ‖n‖ := by
  change max ‖retractiveTargetLinear j n‖ ‖(0 :
    ℓ^∞(CollapsedQuotient P (Set.range j), ℝ))‖ = ‖n‖
  rw [norm_retractiveTargetLinear_eq j hj n, _root_.norm_zero, max_eq_left]
  exact norm_nonneg n

/-- The old target is a linear isometric subspace of the protected envelope. -/
noncomputable def protectedTargetLinearIsometry {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (hj : Isometry j) : N →ₗᵢ[ℝ] ProtectedEnvelope P N j where
  toLinearMap := protectedTargetLinear j
  norm_map' := norm_protectedTargetLinear_eq j hj

/-- Projection through the first two product coordinates. -/
noncomputable def protectedEnvelopeProjection {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    ProtectedEnvelope P N j →L[ℝ] N :=
  (retractiveProjection j).comp
    ((ContinuousLinearMap.fst ℝ (RetractiveEnvelope P N j)
      ℓ^∞(CollapsedQuotient P (Set.range j), ℝ)).comp
        (Submodule.subtypeL
          (Submodule.span ℝ
            (Set.range (protectedEnvelopeGenerator j))).topologicalClosure))

theorem protectedEnvelopeProjection_norm_le {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (z : ProtectedEnvelope P N j) :
    ‖protectedEnvelopeProjection j z‖ ≤ ‖z‖ := by
  exact (retractiveProjection_norm_le j z.1.1).trans (le_max_left _ _)

theorem protectedEnvelopeProjection_target {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (n : N) :
    protectedEnvelopeProjection j (protectedTargetLinear j n) = n := rfl

theorem protectedEnvelopeEmbedding_target {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N) (hR : ∀ n, R (j n) = n) (n : N) :
    protectedEnvelopeEmbedding j R (j n) = protectedTargetLinear j n := by
  apply Subtype.ext
  change protectedEnvelopeEmbeddingAmbient j R (j n) =
    protectedTargetLinearAmbient j n
  rw [protectedEnvelopeEmbeddingAmbient,
    combinedEmbedding_of_mem (Set.mem_range_self 0) (Set.mem_range_self n),
    retractiveEmbedding_target j R hR n]
  rfl

theorem protectedEnvelopeProjection_embedding {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N) (p : P) :
    protectedEnvelopeProjection j (protectedEnvelopeEmbedding j R p) = R p := rfl

/-- The final embedding is nonexpansive. -/
theorem protectedEnvelopeEmbedding_dist_le {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N)
    (hR : ∀ p q, dist (R p) (R q) ≤ dist p q) (p q : P) :
    dist (protectedEnvelopeEmbedding j R p) (protectedEnvelopeEmbedding j R q) ≤
      dist p q := by
  change dist (protectedEnvelopeEmbeddingAmbient j R p)
      (protectedEnvelopeEmbeddingAmbient j R q) ≤ dist p q
  rw [protectedEnvelopeEmbeddingAmbient]
  apply combinedEmbedding_dist_le
  exact retractiveEmbedding_dist_le j R hR

/-- Every distance retained by relative evaluation remains exact after adding
the injectivity coordinate. -/
theorem protectedEnvelopeEmbedding_dist_eq {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : N → P) (R : P → N)
    (hR : ∀ p q, dist (R p) (R q) ≤ dist p q) {p q : P}
    (heval : dist (relativeEvaluation j p) (relativeEvaluation j q) = dist p q) :
    dist (protectedEnvelopeEmbedding j R p) (protectedEnvelopeEmbedding j R q) =
      dist p q := by
  change dist (protectedEnvelopeEmbeddingAmbient j R p)
      (protectedEnvelopeEmbeddingAmbient j R q) = dist p q
  rw [protectedEnvelopeEmbeddingAmbient]
  apply combinedEmbedding_dist_eq
  exact retractiveEmbedding_dist_eq j R hR heval

/-- If the old target is complete and isometrically embedded, the final metric
embedding is globally injective. -/
theorem protectedEnvelopeEmbedding_injective {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (j : N → P) (hj : Isometry j) (R : P → N) (hR : ∀ n, R (j n) = n) :
    Function.Injective (protectedEnvelopeEmbedding j R) := by
  intro x y hxy
  have hxy' : protectedEnvelopeEmbeddingAmbient j R x =
      protectedEnvelopeEmbeddingAmbient j R y := congrArg Subtype.val hxy
  apply (combinedEmbedding_injective (Set.range_nonempty j)
    hj.isClosedEmbedding.isClosed_range (base := j 0) ?_) hxy'
  intro x hx y hy hxy
  ·
    rcases hx with ⟨n, rfl⟩
    rcases hy with ⟨m, rfl⟩
    rw [retractiveEmbedding_target j R hR n,
      retractiveEmbedding_target j R hR m] at hxy
    exact congrArg j ((retractiveTargetLinearIsometry j hj).injective hxy)

end

end ScottishBook155
