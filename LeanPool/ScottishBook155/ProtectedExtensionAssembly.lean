/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.AdjunctionRetractiveEnvelope
public import LeanPool.ScottishBook155.ProtectedEnvelope


/-!
# Assembly of the protected one-point extension

This module combines the metric adjunction, the retractive dual-evaluation
coordinate, and the quotient Kuratowski coordinate.  It records the source and
target embeddings and the linear recovery map together with the properties
used by the successor construction.
-/

@[expose] public section

namespace ScottishBook155

open ENNReal WithLp

noncomputable section

universe u v

/-- The canonical copy of the old source as the zero-height hyperplane. -/
noncomputable def protectedSourceBaseLinearIsometry
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    M →ₗᵢ[ℝ] OneSum M where
  toLinearMap := (WithLp.linearEquiv 1 ℝ (M × ℝ)).symm.toLinearMap.comp
    (LinearMap.inl ℝ M ℝ)
  norm_map' m := by
    have h := oneSum_dist_eq (toLp 1 (m, 0) : OneSum M) 0
    convert h using 1 <;> simp

/-- The protected envelope of the metric adjunction, relative to its original target
space. -/
abbrev ProtectedExtensionSpace
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :=
  ProtectedEnvelope (AdjunctionSpace V a y H hattach) N
    (adjunctionTargetMk V a y H hattach)

/-- The map from the extended source into the protected envelope of the adjunction. -/
noncomputable def protectedExtensionSourceEmbedding
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x : OneSum M) :
    ProtectedExtensionSpace V a y H hattach :=
  protectedEnvelopeEmbedding (adjunctionTargetMk V a y H hattach)
    (adjunctionRetraction V a y L H hattach hLH hL hV hgap)
    (adjunctionSourceMk V a y H hattach x)

/-- The linear embedding of the original target into the protected extension space. -/
noncomputable def protectedExtensionTargetLinear
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    N →ₗ[ℝ] ProtectedExtensionSpace V a y H hattach :=
  protectedTargetLinear (adjunctionTargetMk V a y H hattach)

/-- The continuous linear projection from the protected extension back to the original
target. -/
noncomputable def protectedExtensionProjection
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    ProtectedExtensionSpace V a y H hattach →L[ℝ] N :=
  protectedEnvelopeProjection (adjunctionTargetMk V a y H hattach)

theorem protectedExtensionTargetLinear_norm
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) (n : N) :
    ‖protectedExtensionTargetLinear V a y H hattach n‖ = ‖n‖ := by
  exact norm_protectedTargetLinear_eq _ n

/-- The assembled old-target map is a linear isometric embedding. -/
noncomputable def protectedExtensionTargetLinearIsometry
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) :
    N →ₗᵢ[ℝ] ProtectedExtensionSpace V a y H hattach where
  toLinearMap := protectedExtensionTargetLinear V a y H hattach
  norm_map' := protectedExtensionTargetLinear_norm V a y H hattach

theorem protectedExtensionProjection_norm_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (z : ProtectedExtensionSpace V a y H hattach) :
    ‖protectedExtensionProjection V a y H hattach z‖ ≤ ‖z‖ :=
  protectedEnvelopeProjection_norm_le _ z

theorem protectedExtensionProjection_target
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q)) (n : N) :
    protectedExtensionProjection V a y H hattach
      (protectedExtensionTargetLinear V a y H hattach n) = n := rfl

theorem protectedExtensionSourceEmbedding_dist_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x z : OneSum M) :
    dist (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap x)
        (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap z) ≤
      dist x z := by
  calc
    _ ≤ dist (adjunctionSourceMk V a y H hattach x)
        (adjunctionSourceMk V a y H hattach z) :=
      protectedEnvelopeEmbedding_dist_le _ _
        (adjunctionRetraction_dist_le V a y L H hattach hLH hL hV hgap) _ _
    _ = sourceAdjunctionDist V a y H x z := rfl
    _ ≤ dist x z := sourceAdjunctionDist_le V a y H x z

theorem protectedExtensionSourceEmbedding_injective
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [CompleteSpace N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L)
    (hinj : Function.Injective V) (hy : y ∉ Set.range V) :
    Function.Injective
      (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap) :=
  (protectedEnvelopeEmbedding_injective _
    (adjunctionTargetMk_isometry V a y H hattach) _
    (adjunctionRetraction_target V a y L H hattach hLH hL hV hgap)).comp
      (adjunctionSourceMk_injective V a y H hattach
        (attachmentMap_injective hinj hy))

/-- The assembled embedding preserves every protected short source distance. -/
theorem protectedExtensionSourceEmbedding_dist_eq_of_short
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
    dist (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap
          (toLp 1 (m₀, s₀)))
        (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap
          (toLp 1 (m₁, s₁))) =
      dist (toLp 1 (m₀, s₀) : OneSum M) (toLp 1 (m₁, s₁)) := by
  calc
    _ = dist (adjunctionSourceMk V a y H hattach (toLp 1 (m₀, s₀)))
        (adjunctionSourceMk V a y H hattach (toLp 1 (m₁, s₁))) := by
      apply protectedEnvelopeEmbedding_dist_eq
      · exact adjunctionRetraction_dist_le V a y L H hattach hLH hL hV hgap
      · exact relativeEvaluation_adjunctionSource_dist_eq_of_short hattach hr hH hshort
          m₀ m₁ hd
    _ = _ := dist_adjunctionSourceMk_of_short hattach hr
      (by have : 0 ≤ dist (V a) y := dist_nonneg; linarith) hshort hd

theorem protectedExtensionSourceEmbedding_preservesUpTo
    {M : Type u} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {N : Type v} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V : M → N} {a : M} {y : N} {L H r : ℝ}
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L)
    (hr : 0 < r) (hH : 2 * r + dist (V a) y < H)
    (hshort : PreservesUpTo r V) :
    PreservesUpTo r
      (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap) := by
  intro x z hd
  have hx : (toLp 1 (x.fst, x.snd) : OneSum M) = x := rfl
  have hz : (toLp 1 (z.fst, z.snd) : OneSum M) = z := rfl
  rw [← hx, ← hz] at hd ⊢
  exact protectedExtensionSourceEmbedding_dist_eq_of_short hattach hLH hL
    hV hgap hr hH hshort x.fst z.fst hd

theorem protectedExtensionSourceEmbedding_base
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (m : M) :
    protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap
        (toLp 1 (m, 0)) =
      protectedExtensionTargetLinear V a y H hattach (V m) := by
  rw [protectedExtensionSourceEmbedding, show (toLp 1 (m, 0) : OneSum M) =
      attachmentPoint a H (Sum.inl m) by rfl,
    adjunctionMk_glued V a y H hattach (Sum.inl m)]
  exact protectedEnvelopeEmbedding_target _ _
    (adjunctionRetraction_target V a y L H hattach hLH hL hV hgap) (V m)

theorem protectedExtensionSourceEmbedding_hits
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) :
    protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap
        (toLp 1 (a, H)) =
      protectedExtensionTargetLinear V a y H hattach y := by
  rw [protectedExtensionSourceEmbedding, show (toLp 1 (a, H) : OneSum M) =
      attachmentPoint a H (Sum.inr ()) by rfl,
    adjunctionMk_glued V a y H hattach (Sum.inr ())]
  exact protectedEnvelopeEmbedding_target _ _
    (adjunctionRetraction_target V a y L H hattach hLH hL hV hgap) y

theorem protectedExtensionProjection_source
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (x : OneSum M) :
    protectedExtensionProjection V a y H hattach
        (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap x) =
      sourceRetractionOne V a y L H x := by
  rw [protectedExtensionSourceEmbedding, protectedExtensionProjection,
    protectedEnvelopeProjection_embedding,
    adjunctionRetraction_source V a y L H hattach hLH hL hV hgap]

theorem protectedExtensionProjection_source_of_le
    {M : Type u} {N : Type v} [NormedAddCommGroup M] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (V : M → N) (a : M) (y : N) (L H : ℝ)
    (hattach : ∀ p q, dist (attachmentMap V y p) (attachmentMap V y q) ≤
      dist (attachmentPoint a H p) (attachmentPoint a H q))
    (hLH : L < H) (hL : 0 ≤ L)
    (hV : ∀ m n, dist (V m) (V n) ≤ dist m n)
    (hgap : dist y (V a) ≤ H - L) (m : M) {s : ℝ} (hs : s ≤ L) :
    protectedExtensionProjection V a y H hattach
        (protectedExtensionSourceEmbedding V a y L H hattach hLH hL hV hgap
          (toLp 1 (m, s))) = V m := by
  rw [protectedExtensionProjection_source]
  exact sourceRetraction_of_le hLH hs

end

end ScottishBook155
