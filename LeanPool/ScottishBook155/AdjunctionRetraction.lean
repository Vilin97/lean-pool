/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.AdjunctionFormula
import LeanPool.ScottishBook155.ProtectedExtension

/-!
# The nonlinear retraction of the metric adjunction

The flat source retraction agrees with the attachment map.  Together with the
identity on the old target it is nonexpansive for the adjunction predistance,
so it descends through metric separation.
-/

namespace ScottishBook155

open ENNReal WithLp

universe u v

noncomputable def sourceRetractionOne
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ) (x : OneSum M) : N :=
  sourceRetraction V a y L H x.fst x.snd

noncomputable def adjunctionRetractionPre
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ) : OneSum M ⊕ N → N
  | Sum.inl x => sourceRetractionOne V a y L H x
  | Sum.inr n => n

theorem sourceRetractionOne_attachment
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L) (p : M ⊕ Unit) :
    sourceRetractionOne V a y L H (attachmentPoint a H p) = attachmentMap V y p := by
  exact sourceRetraction_attachment hLH hL p

theorem sourceRetractionOne_dist_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x z : OneSum M) :
    dist (sourceRetractionOne V a y L H x) (sourceRetractionOne V a y L H z) ≤
      dist x z :=
  sourceRetraction_dist_le hLH hV hgap x z

theorem sourceRetractionOne_dist_le_excursionCost
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x₀ x₁ : OneSum M) :
    dist (sourceRetractionOne V a y L H x₀) (sourceRetractionOne V a y L H x₁) ≤
      attachmentExcursionCost V a y H x₀ x₁ := by
  rw [attachmentExcursionCost]
  apply le_ciInf
  intro p
  apply le_ciInf
  intro q
  calc
    dist (sourceRetractionOne V a y L H x₀) (sourceRetractionOne V a y L H x₁) ≤
        dist (sourceRetractionOne V a y L H x₀)
            (sourceRetractionOne V a y L H (attachmentPoint a H p)) +
          dist (sourceRetractionOne V a y L H (attachmentPoint a H p))
            (sourceRetractionOne V a y L H (attachmentPoint a H q)) +
          dist (sourceRetractionOne V a y L H (attachmentPoint a H q))
            (sourceRetractionOne V a y L H x₁) := dist_triangle4 _ _ _ _
    _ = dist (sourceRetractionOne V a y L H x₀) (attachmentMap V y p) +
          dist (attachmentMap V y p) (attachmentMap V y q) +
          dist (attachmentMap V y q) (sourceRetractionOne V a y L H x₁) := by
      rw [sourceRetractionOne_attachment hLH hL,
        sourceRetractionOne_attachment hLH hL]
    _ ≤ dist x₀ (attachmentPoint a H p) +
          dist (attachmentMap V y p) (attachmentMap V y q) +
          dist (attachmentPoint a H q) x₁ := by
      have hleft := sourceRetractionOne_dist_le hLH hV hgap x₀ (attachmentPoint a H p)
      have hright := sourceRetractionOne_dist_le hLH hV hgap
        (attachmentPoint a H q) x₁
      rw [sourceRetractionOne_attachment hLH hL] at hleft hright
      linarith

theorem sourceRetractionOne_dist_le_sourceAdjunctionDist
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x₀ x₁ : OneSum M) :
    dist (sourceRetractionOne V a y L H x₀) (sourceRetractionOne V a y L H x₁) ≤
      sourceAdjunctionDist V a y H x₀ x₁ := by
  rw [sourceAdjunctionDist, le_min_iff]
  exact ⟨sourceRetractionOne_dist_le hLH hV hgap x₀ x₁,
    sourceRetractionOne_dist_le_excursionCost hLH hL hV hgap x₀ x₁⟩

theorem sourceRetractionOne_dist_le_attachmentTargetCost
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x : OneSum M) (n : N) :
    dist (sourceRetractionOne V a y L H x) n ≤ attachmentTargetCost V a y H x n := by
  rw [attachmentTargetCost]
  apply le_ciInf
  intro p
  calc
    dist (sourceRetractionOne V a y L H x) n ≤
        dist (sourceRetractionOne V a y L H x)
            (sourceRetractionOne V a y L H (attachmentPoint a H p)) +
          dist (sourceRetractionOne V a y L H (attachmentPoint a H p)) n :=
      dist_triangle _ _ _
    _ = dist (sourceRetractionOne V a y L H x) (attachmentMap V y p) +
          dist (attachmentMap V y p) n := by
      rw [sourceRetractionOne_attachment hLH hL]
    _ ≤ dist x (attachmentPoint a H p) + dist (attachmentMap V y p) n := by
      have hsource := sourceRetractionOne_dist_le hLH hV hgap x (attachmentPoint a H p)
      rw [sourceRetractionOne_attachment hLH hL] at hsource
      exact add_le_add hsource le_rfl

theorem adjunctionRetractionPre_dist_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H : ℝ}
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (z w : OneSum M ⊕ N) :
    dist (adjunctionRetractionPre V a y L H z) (adjunctionRetractionPre V a y L H w) ≤
      adjunctionPreDist V a y H z w := by
  cases z with
  | inl x =>
      cases w with
      | inl z => exact sourceRetractionOne_dist_le_sourceAdjunctionDist hLH hL hV hgap x z
      | inr n => exact sourceRetractionOne_dist_le_attachmentTargetCost hLH hL hV hgap x n
  | inr n =>
      cases w with
      | inl x =>
          rw [dist_comm]
          exact sourceRetractionOne_dist_le_attachmentTargetCost hLH hL hV hgap x n
      | inr m => exact le_rfl

/-- The pointed nonexpansive retraction from the metric adjunction to the old
target. -/
noncomputable def adjunctionRetraction
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) : AdjunctionSpace V a y H hattach → N := by
  letI := adjunctionPseudoMetricSpace V a y H hattach
  change (@SeparationQuotient (OneSum M ⊕ N)
    (adjunctionPseudoMetricSpace V a y H hattach).toUniformSpace.toTopologicalSpace) → N
  apply @SeparationQuotient.lift (OneSum M ⊕ N) N
    (adjunctionPseudoMetricSpace V a y H hattach).toUniformSpace.toTopologicalSpace
    (adjunctionRetractionPre V a y L H)
  intro z w hzw
  apply dist_eq_zero.mp
  have hle := adjunctionRetractionPre_dist_le hLH hL hV hgap z w
  have hzero := hzw.dist_eq_zero
  change adjunctionPreDist V a y H z w = 0 at hzero
  rw [hzero] at hle
  exact le_antisymm hle dist_nonneg

theorem adjunctionRetraction_source
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x : OneSum M) :
    adjunctionRetraction V a y L H hattach hLH hL hV hgap
      (adjunctionSourceMk V a y H hattach x) = sourceRetractionOne V a y L H x := rfl

theorem adjunctionRetraction_target
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (n : N) :
    adjunctionRetraction V a y L H hattach hLH hL hV hgap
      (adjunctionTargetMk V a y H hattach n) = n := rfl

/-- The descended retraction is nonexpansive for the metric-quotient distance. -/
theorem adjunctionRetraction_dist_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (p q : AdjunctionSpace V a y H hattach) :
    dist (adjunctionRetraction V a y L H hattach hLH hL hV hgap p)
        (adjunctionRetraction V a y L H hattach hLH hL hV hgap q) ≤ dist p q := by
  refine Quotient.inductionOn₂' p q ?_
  intro z w
  exact adjunctionRetractionPre_dist_le hLH hL hV hgap z w

end ScottishBook155
