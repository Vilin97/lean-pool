/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Boundary

/-! # Interior -/

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoli_nonneg_of_radiusAgreement
    {F G : ℝ → ℝ} (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ) :
    ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ := by
  intro ρ hρ hρ_upper
  rw [hagree hρ hρ_upper]
  exact hG_nonneg hρ hρ_upper

/-- Agreement of radius quantities also transfers the boundedness hypothesis
needed by the deterministic radius iteration. -/
theorem coarseCaccioppoli_radiusBoundedAbove_of_radiusAgreement
    {F G : ℝ → ℝ} (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove G) :
    CoarseCaccioppoliRadiusBoundedAbove F := by
  rcases hbounded with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro ρ hρ hρ_upper
  rw [hagree hρ hρ_upper]
  exact hB hρ hρ_upper

/-- A boundary note-shaped raw estimate for `G` can be reused for `F` whenever
the two radius quantities agree on the deterministic interval. -/
theorem coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h G) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  have hρ₁_upper : ρ₁ ≤ 1 := le_trans hlt.le hρ₂
  have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
  simpa [hagree hρ₁ hρ₁_upper, hagree hρ₂_lower hρ₂] using
    hraw hρ₁ hlt hρ₂

/-- The interior middle layer can consume the same local note-shaped estimate
as the boundary proof, provided the underlying radius quantity is unchanged by
centering. -/
theorem coarseCaccioppoli_interior_noteRawEstimate_of_boundary_noteEstimate_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h G) :
    CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F := by
  unfold CoarseCaccioppoliInteriorNoteRawEstimate
  exact coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
    Q a s t C uL2Sq h hagree hraw

/-- The centered interior proof packages into the same pre-recurrence middle
layer once the raw estimate is transported across a radius agreement
`F = G`. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_boundary_noteEstimate_of_radiusAgreement
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h G)
    (hctrl : CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  unfold CoarseCaccioppoliInteriorNoteCoefficientControl at hctrl
  unfold CoarseCaccioppoliInteriorPreRecurrence
  exact coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate
    Q a s t C uL2Sq h
    (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
      Q a s t C uL2Sq h hagree hraw)
    hctrl

/-- Interior coarse Caccioppoli from the same note-shaped local estimate as the
boundary proof, together with an abstract radius agreement encoding the
centering step `v := u - (u)_Q`. -/
theorem coarseCaccioppoli_interior_qone_of_boundary_noteEstimate_of_radiusAgreement_of_heightChoice_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F G : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h G)
    (hheight : CoarseCaccioppoliInteriorHeightChoice Q a s t C h)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorBound
  exact coarseCaccioppoli_boundary_qone_of_noteEstimate_of_heightChoice_of_triadicGapScaleChoice
    Q a s t C uL2Sq h hC hs ht hst hu
    (coarseCaccioppoli_nonneg_of_radiusAgreement hagree hG_nonneg)
    (coarseCaccioppoli_radiusBoundedAbove_of_radiusAgreement hagree hG_bounded)
    (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
      Q a s t C uL2Sq h hagree hraw)
    hheight hcrossscale

/-- Interior coarse Caccioppoli in the completed pre-Besov form: the same
boundary-style local estimate as above, transported across the centering
agreement `F = G`, now combines with the note's actual explicit height choice
without any extra cross-scale hypothesis. -/
theorem coarseCaccioppoli_interior_qone_of_boundary_noteEstimate_of_radiusAgreement_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) G) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorExplicitHeightBound
  exact coarseCaccioppoli_boundary_qone_of_noteEstimate_of_explicitHeightOfScaleChoice
    Q a s t C uL2Sq k hC hs ht hst hu
    (coarseCaccioppoli_nonneg_of_radiusAgreement hagree hG_nonneg)
    (coarseCaccioppoli_radiusBoundedAbove_of_radiusAgreement hagree hG_bounded)
    hscale
    (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
      Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
      hagree hraw)

/-- Interior coarse Caccioppoli with the localized explicit height, transported
from a boundary-style note estimate across the radius agreement. -/
theorem coarseCaccioppoli_interior_qone_of_boundary_noteEstimate_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) G) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorExplicitHeightBound
  exact
    coarseCaccioppoli_boundary_qone_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu
      (coarseCaccioppoli_nonneg_of_radiusAgreement hagree hG_nonneg)
      (coarseCaccioppoli_radiusBoundedAbove_of_radiusAgreement hagree hG_bounded)
      hscale
      (coarseCaccioppoli_boundary_noteRawEstimate_of_radiusAgreement
        Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        hagree hraw)

/-- Interior coarse Caccioppoli with the localized explicit height, transported
from a boundary-style note estimate available only on the deterministic
Chapter-3 radius sequence. -/
theorem coarseCaccioppoli_interior_qone_of_boundary_noteEstimate_on_radiusSequence_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F G : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      ∀ n : ℕ,
        G (coarseCaccioppoliRadiusSequence n) ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C
            (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1)) *
              G (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1)) *
                Real.sqrt (G (coarseCaccioppoliRadiusSequence (n + 1)))) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  have hG :
      G (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
    unfold coarseCaccioppoliInteriorExplicitHeightBound
    exact
      coarseCaccioppoli_boundary_qone_of_noteEstimate_on_radiusSequence_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k hC hs ht hst hu hG_nonneg hG_bounded hscale hraw
  have hEq : F (1 / 3 : ℝ) = G (1 / 3 : ℝ) := by
    exact hagree (by norm_num) (by norm_num)
  calc
    F (1 / 3 : ℝ) = G (1 / 3 : ℝ) := hEq
    _ ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := hG

/-- Interior coarse Caccioppoli in the same pre-Besov explicit-height form,
when the caller already supplies the interior local estimate directly rather
than transporting it from the boundary proof. -/
theorem coarseCaccioppoli_interior_qone_of_noteEstimate_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorExplicitHeightBound
  unfold CoarseCaccioppoliInteriorNoteRawEstimate at hraw
  exact coarseCaccioppoli_boundary_qone_of_noteEstimate_of_explicitHeightOfScaleChoice
    Q a s t C uL2Sq k hC hs ht hst hu hnonneg hbounded hscale hraw

/-- Interior coarse Caccioppoli with the localized explicit height, when the
caller supplies the interior note estimate directly. -/
theorem coarseCaccioppoli_interior_qone_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorExplicitHeightBound
  unfold CoarseCaccioppoliInteriorNoteRawEstimate at hraw
  exact
    coarseCaccioppoli_boundary_qone_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hnonneg hbounded hscale hraw

/-- Interior coarse Caccioppoli currently reuses the same radius-iteration
backbone as the boundary version, provided the caller supplies the interior
radius-recursion explicitly. -/
theorem coarseCaccioppoli_interior_qone_of_radius_recurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec :
      CoarseCaccioppoliRadiusRecurrence F
        (coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq)
        (coarseCaccioppoliBeta s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliInteriorBound
  exact coarseCaccioppoli_boundary_qone_of_radius_recurrence
    Q a s t C uL2Sq hC hs ht hst hu hbounded hrec

/-- Interior coarse Caccioppoli from the same already-absorbed pre-recurrence
surface as the boundary version. -/
theorem coarseCaccioppoli_interior_qone_of_preRecurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hpre : CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  unfold CoarseCaccioppoliInteriorPreRecurrence at hpre
  exact coarseCaccioppoli_interior_qone_of_radius_recurrence
    Q a s t C uL2Sq hC hs ht hst hu hbounded
    (coarseCaccioppoli_boundary_radius_recurrence_of_preRecurrence
      Q a s t C uL2Sq hnonneg hpre)

/-- Interior coarse Caccioppoli from the explicit-height pre-recurrence middle
layer. -/
theorem coarseCaccioppoli_interior_qone_of_explicitHeightPreRecurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hpre :
      CoarseCaccioppoliInteriorExplicitHeightPreRecurrence Q a s t C uL2Sq F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  unfold CoarseCaccioppoliInteriorExplicitHeightPreRecurrence at hpre
  unfold coarseCaccioppoliInteriorExplicitHeightBound
  exact coarseCaccioppoli_boundary_qone_of_explicitHeightPreRecurrence
    Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded hpre

/-- Interior pre-recurrence from the same note-shaped raw estimate and
note-shaped coefficient-control surface as the boundary version. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_noteEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hraw : CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F)
    (hctrl : CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  unfold CoarseCaccioppoliInteriorNoteRawEstimate at hraw
  unfold CoarseCaccioppoliInteriorNoteCoefficientControl at hctrl
  unfold CoarseCaccioppoliInteriorPreRecurrence
  exact coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate
    Q a s t C uL2Sq h hraw hctrl

/-- Interior pre-recurrence from the note-shaped raw estimate plus the two
remaining note-specific bookkeeping obligations. -/
theorem coarseCaccioppoli_interior_preRecurrence_of_noteEstimate_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hraw : CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorPreRecurrence Q a s t C uL2Sq F := by
  unfold CoarseCaccioppoliInteriorNoteRawEstimate at hraw
  unfold CoarseCaccioppoliInteriorPreRecurrence
  exact coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate_of_absorptionCondition_of_crossTermBound
    Q a s t C uL2Sq h hC hs ht hst hraw habs hcross

/-- Interior coarse Caccioppoli from the same raw local-estimate plus
coefficient-control surface as the boundary version. -/
theorem coarseCaccioppoli_interior_qone_of_rawEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ} {α B : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliInteriorRawEstimate F α B)
    (hctrl : CoarseCaccioppoliInteriorCoefficientControl Q a s t C uL2Sq α B) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  unfold CoarseCaccioppoliInteriorRawEstimate at hraw
  unfold CoarseCaccioppoliInteriorCoefficientControl at hctrl
  apply coarseCaccioppoli_interior_qone_of_preRecurrence
    Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded
  exact coarseCaccioppoli_boundary_preRecurrence_of_rawEstimate
    Q a s t C uL2Sq hraw hctrl

/-- Interior coarse Caccioppoli from the same note-shaped raw estimate and
note-shaped coefficient-control surface as the boundary version. -/
theorem coarseCaccioppoli_interior_qone_of_noteEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F)
    (hctrl : CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  unfold CoarseCaccioppoliInteriorNoteRawEstimate at hraw
  unfold CoarseCaccioppoliInteriorNoteCoefficientControl at hctrl
  exact coarseCaccioppoli_interior_qone_of_rawEstimate
    Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded hraw hctrl

/-- The split interior note-specific bookkeeping conditions imply the packaged
note-shaped coefficient-control surface. -/
theorem coarseCaccioppoli_interior_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h := by
  exact
    coarseCaccioppoli_boundary_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
      Q a s t C uL2Sq h hC hs ht hst habs hcross

/-- The same explicit `h`-choice bookkeeping and stronger triadic-scale cross
estimate also recover the packaged interior coefficient-control surface. -/
theorem coarseCaccioppoli_interior_noteCoefficientControl_of_heightChoice_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hheight : CoarseCaccioppoliInteriorHeightChoice Q a s t C h)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h := by
  exact
    coarseCaccioppoli_boundary_noteCoefficientControl_of_heightChoice_of_triadicGapScaleChoice
      Q a s t C uL2Sq h hC hs ht hst hu hheight hcrossscale

/-- Interior coarse Caccioppoli from the note-shaped raw estimate plus the two
remaining note-specific bookkeeping obligations. -/
theorem coarseCaccioppoli_interior_qone_of_noteEstimate_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliInteriorNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  have hctrl :
      CoarseCaccioppoliInteriorNoteCoefficientControl Q a s t C uL2Sq h :=
    coarseCaccioppoli_interior_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
      Q a s t C uL2Sq h hC hs ht hst habs hcross
  exact coarseCaccioppoli_interior_qone_of_noteEstimate
    Q a s t C uL2Sq h hC hs ht hst hu hnonneg hbounded hraw hctrl

/-- Interior coarse Caccioppoli from the note-shaped local estimate, the
explicit note-facing `h` choice, and the remaining stronger triadic-scale
cross-term inequality. -/
theorem coarseCaccioppoli_interior_qone_of_noteEstimate_of_heightChoice_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliInteriorNoteRawEstimate Q a s t C uL2Sq h F)
    (hheight : CoarseCaccioppoliInteriorHeightChoice Q a s t C h)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliInteriorBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_interior_qone_of_noteEstimate
    Q a s t C uL2Sq h hC hs ht hst hu hnonneg hbounded hraw
  exact
    coarseCaccioppoli_interior_noteCoefficientControl_of_heightChoice_of_triadicGapScaleChoice
      Q a s t C uL2Sq h hC hs ht hst hu hheight hcrossscale

end

end Homogenization
