/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.RelativeEnvelope


/-!
# A retractive dual-evaluation envelope

The dual-evaluation coordinate already gives the metric part of the relative
envelope.  Adjoining the old target as a max-product coordinate makes the
retraction linear and explicit: it is first-coordinate projection.
-/

@[expose] public section

namespace ScottishBook155

open ENNReal lp

universe u v

/-- The old target together with the dual-evaluation relative coordinate. -/
abbrev RetractiveEnvelope (P : Type u) (N : Type v) [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :=
  N × ℓ^∞(RelativeFunctional P N j, ℝ)

/-- Embed the attached metric space using a chosen metric retraction and the
relative evaluation coordinate. -/
noncomputable def retractiveEmbedding {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (R : P → N) (p : P) :
    RetractiveEnvelope P N j :=
  (R p, relativeEvaluation j p)

/-- The old target embeds linearly in both coordinates. -/
noncomputable def retractiveTargetLinear {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    N →ₗ[ℝ] RetractiveEnvelope P N j where
  toFun n := (n, relativeTargetLinear j n)
  map_add' n m := by simp
  map_smul' c n := by simp

theorem norm_retractiveTargetLinear_eq {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (n : N) : ‖retractiveTargetLinear j n‖ = ‖n‖ := by
  change max ‖n‖ ‖relativeTargetLinear j n‖ = ‖n‖
  exact max_eq_left (norm_relativeTargetLinear_le j n)

/-- The old target is a linear isometric subspace of the retractive envelope. -/
noncomputable def retractiveTargetLinearIsometry {P : Type u} {N : Type v}
    [MetricSpace P] [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    N →ₗᵢ[ℝ] RetractiveEnvelope P N j where
  toLinearMap := retractiveTargetLinear j
  norm_map' := norm_retractiveTargetLinear_eq j

/-- First-coordinate projection is the contractive linear retraction. -/
noncomputable def retractiveProjection {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) :
    RetractiveEnvelope P N j →L[ℝ] N :=
  ContinuousLinearMap.fst ℝ N ℓ^∞(RelativeFunctional P N j, ℝ)

theorem retractiveProjection_target {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (n : N) :
    retractiveProjection j (retractiveTargetLinear j n) = n := rfl

theorem retractiveProjection_norm_le {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P)
    (z : RetractiveEnvelope P N j) : ‖retractiveProjection j z‖ ≤ ‖z‖ := by
  exact le_max_left _ _

theorem retractiveEmbedding_target {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (R : P → N)
    (hR : ∀ n, R (j n) = n) (n : N) :
    retractiveEmbedding j R (j n) = retractiveTargetLinear j n := by
  apply Prod.ext
  · exact hR n
  · exact (relativeTargetLinear_apply j n).symm

theorem retractiveProjection_embedding {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (R : P → N) (p : P) :
    retractiveProjection j (retractiveEmbedding j R p) = R p := rfl

/-- A nonexpansive metric retraction and relative evaluation jointly give a
nonexpansive embedding into the max-product envelope. -/
theorem retractiveEmbedding_dist_le {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (R : P → N)
    (hR : ∀ p q, dist (R p) (R q) ≤ dist p q) (p q : P) :
    dist (retractiveEmbedding j R p) (retractiveEmbedding j R q) ≤ dist p q := by
  rw [Prod.dist_eq]
  exact max_le (hR p q) (relativeEvaluation_dist_le j p q)

/-- Every distance retained by relative evaluation remains exact in the
retractive envelope. -/
theorem retractiveEmbedding_dist_eq {P : Type u} {N : Type v} [MetricSpace P]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : N → P) (R : P → N)
    (hR : ∀ p q, dist (R p) (R q) ≤ dist p q) {p q : P}
    (heval : dist (relativeEvaluation j p) (relativeEvaluation j q) = dist p q) :
    dist (retractiveEmbedding j R p) (retractiveEmbedding j R q) = dist p q := by
  apply le_antisymm (retractiveEmbedding_dist_le j R hR p q)
  rw [Prod.dist_eq]
  change dist p q ≤ max (dist (R p) (R q))
    (dist (relativeEvaluation j p) (relativeEvaluation j q))
  rw [heval]
  exact le_max_right _ _

end ScottishBook155
