/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.AdjunctionRetraction
import LeanPool.ScottishBook155.RetractiveEnvelope

/-!
# The adjunction inside a linearly retractive Banach envelope

This file specializes the retractive dual-evaluation envelope to the metric
adjunction.  The resulting metric embedding is nonexpansive, retains all
protected short source distances, extends the linear isometric copy of the old
target, and recovers the nonlinear adjunction retraction by a contractive
linear projection.
-/

namespace ScottishBook155

open ENNReal WithLp

universe u v

/-- The retractive-envelope embedding of the adjunction space, using its canonical target
inclusion and retraction. -/
noncomputable def adjunctionEnvelopeEmbedding
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (p : AdjunctionSpace V a y H hattach) :=
  retractiveEmbedding (adjunctionTargetMk V a y H hattach)
    (adjunctionRetraction V a y L H hattach hLH hL hV hgap) p

theorem adjunctionEnvelopeEmbedding_target
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (n : N) :
    adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap
        (adjunctionTargetMk V a y H hattach n) =
      retractiveTargetLinear (adjunctionTargetMk V a y H hattach) n := by
  apply retractiveEmbedding_target
  exact adjunctionRetraction_target V a y L H hattach hLH hL hV hgap

theorem adjunctionEnvelopeEmbedding_dist_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (p q : AdjunctionSpace V a y H hattach) :
    dist (adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap p)
        (adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap q) ≤
      dist p q := by
  apply retractiveEmbedding_dist_le
  exact adjunctionRetraction_dist_le V a y L H hattach hLH hL hV hgap

theorem adjunctionEnvelopeProjection_recovery
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (p : AdjunctionSpace V a y H hattach) :
    retractiveProjection (adjunctionTargetMk V a y H hattach)
        (adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap p) =
      adjunctionRetraction V a y L H hattach hLH hL hV hgap p := rfl

/-- The retractive envelope retains every protected short source distance. -/
theorem adjunctionEnvelopeEmbedding_source_dist_eq_of_short
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L)
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) (m₀ m₁ : M) {s₀ s₁ : ℝ}
    (hd : dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) ≤ r) :
    let p₀ := adjunctionSourceMk V a y H hattach (toLp 1 (m₀, s₀))
    let p₁ := adjunctionSourceMk V a y H hattach (toLp 1 (m₁, s₁))
    dist (adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap p₀)
        (adjunctionEnvelopeEmbedding V a y L H hattach hLH hL hV hgap p₁) =
      dist p₀ p₁ := by
  dsimp only
  apply retractiveEmbedding_dist_eq
  · exact adjunctionRetraction_dist_le V a y L H hattach hLH hL hV hgap
  · exact relativeEvaluation_adjunctionSource_dist_eq_of_short hattach hr hH hshort
      m₀ m₁ hd

end ScottishBook155
