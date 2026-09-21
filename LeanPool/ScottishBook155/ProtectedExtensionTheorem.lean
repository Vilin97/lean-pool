/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import LeanPool.ScottishBook155.ProtectedExtensionAssembly

/-!
# Existence form of the protected one-point extension

The preceding files construct the extension from a height satisfying explicit
inequalities.  Here the height is chosen and the resulting properties are
packaged in the hypothesis form of the manuscript's protected-extension lemma.
-/

namespace ScottishBook155

open ENNReal WithLp

universe u v

/-- A concrete height leaving room for the attachment gap, the recovery
collar, and the protected metric scale. -/
noncomputable def protectedHeight
    {M : Type u} {N : Type v} [Zero M] [PseudoMetricSpace N]
    (V : M → N) (y : N) (L r : ℝ) : ℝ :=
  dist (V 0) y + L + 4 * r

theorem protectedHeight_L_lt
    {M : Type u} {N : Type v} [Zero M] [PseudoMetricSpace N]
    {V : M → N} {y : N} {L r : ℝ} (_hL : 0 < L) (hr : 0 < r) :
    L < protectedHeight V y L r := by
  have hdist : 0 ≤ dist (V 0) y := dist_nonneg
  simp only [protectedHeight]
  linarith

theorem protectedHeight_attachment_gap
    {M : Type u} {N : Type v} [Zero M] [PseudoMetricSpace N]
    {V : M → N} {y : N} {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    dist (V 0) y < protectedHeight V y L r := by
  simp only [protectedHeight]
  linarith

theorem protectedHeight_retraction_gap
    {M : Type u} {N : Type v} [Zero M] [PseudoMetricSpace N]
    {V : M → N} {y : N} {L r : ℝ} (hr : 0 < r) :
    dist y (V 0) ≤ protectedHeight V y L r - L := by
  rw [dist_comm]
  simp only [protectedHeight]
  linarith

theorem protectedHeight_short_gap
    {M : Type u} {N : Type v} [Zero M] [PseudoMetricSpace N]
    {V : M → N} {y : N} {L r : ℝ} (hL : 0 < L) (hr : 0 < r) :
    2 * r + dist (V 0) y < protectedHeight V y L r := by
  simp only [protectedHeight]
  linarith

/-- The complete protected-extension package: a concrete Banach target and
maps satisfying local isometry, injectivity, extension, point-hitting, linear
retraction, and collar recovery. -/
theorem exists_protectedExtension
    {M : Type u} {N : Type v}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    {V : M → N} {y : N} {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hinj : Function.Injective V)
    (hshort : PreservesUpTo r V) (hy : y ∉ Set.range V) :
    ∃ (H : ℝ)
      (hattach : ∀ p q,
        dist (attachmentMap V y p) (attachmentMap V y q) ≤
          dist (attachmentPoint (0 : M) H p) (attachmentPoint 0 H q))
      (hLH : L < H) (hgap : dist y (V 0) ≤ H - L),
      Function.Injective
          (protectedExtensionSourceEmbedding V 0 y L H hattach hLH hL.le
            (preservesUpTo_nonexpansive hr hshort) hgap) ∧
        PreservesUpTo r
          (protectedExtensionSourceEmbedding V 0 y L H hattach hLH hL.le
            (preservesUpTo_nonexpansive hr hshort) hgap) ∧
        (∀ m,
          protectedExtensionSourceEmbedding V 0 y L H hattach hLH hL.le
              (preservesUpTo_nonexpansive hr hshort) hgap (toLp 1 (m, 0)) =
            protectedExtensionTargetLinear V 0 y H hattach (V m)) ∧
        protectedExtensionSourceEmbedding V 0 y L H hattach hLH hL.le
            (preservesUpTo_nonexpansive hr hshort) hgap (toLp 1 ((0 : M), H)) =
          protectedExtensionTargetLinear V 0 y H hattach y ∧
        (∀ n, ‖protectedExtensionTargetLinear V 0 y H hattach n‖ = ‖n‖) ∧
        (∀ z : ProtectedExtensionSpace V 0 y H hattach,
          ‖protectedExtensionProjection V 0 y H hattach z‖ ≤ ‖z‖) ∧
        (∀ n, protectedExtensionProjection V 0 y H hattach
          (protectedExtensionTargetLinear V 0 y H hattach n) = n) ∧
        (∀ (m : M) (s : ℝ), |s| ≤ L →
          protectedExtensionProjection V 0 y H hattach
              (protectedExtensionSourceEmbedding V 0 y L H hattach hLH hL.le
                (preservesUpTo_nonexpansive hr hshort) hgap (toLp 1 (m, s))) =
            V m) := by
  let H := protectedHeight V y L r
  let hV := preservesUpTo_nonexpansive hr hshort
  have hLH : L < H := protectedHeight_L_lt hL hr
  have hattachGap : dist (V 0) y < H := protectedHeight_attachment_gap hL hr
  let hattach : ∀ p q,
      dist (attachmentMap V y p) (attachmentMap V y q) ≤
        dist (attachmentPoint (0 : M) H p) (attachmentPoint 0 H q) :=
    attachmentMap_dist_le hV 0 y hattachGap
  have hgap : dist y (V 0) ≤ H - L := protectedHeight_retraction_gap hr
  have hH : 2 * r + dist (V 0) y < H := protectedHeight_short_gap hL hr
  refine ⟨H, hattach, hLH, hgap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact protectedExtensionSourceEmbedding_injective V 0 y L H hattach hLH hL.le
      hV hgap hinj hy
  · exact protectedExtensionSourceEmbedding_preservesUpTo hattach hLH hL.le hV hgap
      hr hH hshort
  · intro m
    exact protectedExtensionSourceEmbedding_base V 0 y L H hattach hLH hL.le
      hV hgap m
  · exact protectedExtensionSourceEmbedding_hits V 0 y L H hattach hLH hL.le
      hV hgap
  · exact protectedExtensionTargetLinear_norm V 0 y H hattach
  · exact protectedExtensionProjection_norm_le V 0 y H hattach
  · exact protectedExtensionProjection_target V 0 y H hattach
  · intro m s hs
    exact protectedExtensionProjection_source_of_le V 0 y L H hattach hLH hL.le
      hV hgap m (le_trans (le_abs_self s) hs)

end ScottishBook155
