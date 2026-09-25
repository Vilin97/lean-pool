/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Boundary.NoteRhs
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration

/-! # Explicit Height -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

/-- Boundary coarse Caccioppoli from the already-absorbed pre-recurrence
surface. This is the current next-safe theorem interface before the upstream
Besov cutoff/pairing step is formalized. -/
theorem coarseCaccioppoli_boundary_qone_of_preRecurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hpre : CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_boundary_qone_of_radius_recurrence
    Q a s t C uL2Sq hC hs ht hst hu hbounded
  exact coarseCaccioppoli_boundary_radius_recurrence_of_preRecurrence
    Q a s t C uL2Sq hnonneg hpre

/-- Boundary coarse Caccioppoli from the explicit-height pre-recurrence middle
layer. -/
theorem coarseCaccioppoli_boundary_qone_of_explicitHeightPreRecurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hpre :
      CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
  have h :=
    coarseCaccioppoli_radius_iteration
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_nonneg
        Q a s t C uL2Sq hC hs ht hst hu)
      hbounded
      (coarseCaccioppoli_boundary_radius_recurrence_of_explicitHeightPreRecurrence
        Q a s t C uL2Sq hnonneg hpre)
  simpa [mul_comm] using h

/-- Boundary coarse Caccioppoli from the raw local single-cube estimate and the
separate coefficient bookkeeping surface. -/
theorem coarseCaccioppoli_boundary_qone_of_rawEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ} {α B : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliBoundaryRawEstimate F α B)
    (hctrl : CoarseCaccioppoliBoundaryCoefficientControl Q a s t C uL2Sq α B) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_boundary_qone_of_preRecurrence
    Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded
  exact coarseCaccioppoli_boundary_preRecurrence_of_rawEstimate
    Q a s t C uL2Sq hraw hctrl

/-- Boundary coarse Caccioppoli from the note-shaped raw estimate and the
note-shaped coefficient-control surface. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (hctrl : CoarseCaccioppoliBoundaryNoteCoefficientControl Q a s t C uL2Sq h) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  exact coarseCaccioppoli_boundary_qone_of_rawEstimate
    Q a s t C uL2Sq hC hs ht hst hu hnonneg hbounded hraw hctrl

/-- The split note-specific bookkeeping conditions imply the packaged
note-shaped coefficient-control surface. -/
theorem coarseCaccioppoli_boundary_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryNoteCoefficientControl Q a s t C uL2Sq h := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact coarseCaccioppoliBoundaryAlphaOfHeight_nonneg
      Q a s t C h hC hs ht hst hlt
  · exact habs hρ₁ hlt hρ₂
  · exact coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg
      Q a s C uL2Sq h hC hs hlt
  · exact hcross hρ₁ hlt hρ₂

/-- The note-facing explicit `h` choice plus the stronger triadic-scale
cross-term estimate recover the packaged boundary coefficient-control surface.
-/
theorem coarseCaccioppoli_boundary_noteCoefficientControl_of_heightChoice_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hheight : CoarseCaccioppoliBoundaryHeightChoice Q a s t C h)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    CoarseCaccioppoliBoundaryNoteCoefficientControl Q a s t C uL2Sq h := by
  apply coarseCaccioppoli_boundary_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
    Q a s t C uL2Sq h hC hs ht hst
  · exact coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t C h hC hs ht hst hheight
  · exact coarseCaccioppoli_boundary_noteCrossTermBound_of_triadicGapScaleChoice
      Q a s t C uL2Sq h hC hs ht hst hu hcrossscale

/-- Boundary coarse Caccioppoli from the note-shaped raw estimate plus the two
remaining note-specific bookkeeping obligations. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_boundary_qone_of_noteEstimate
    Q a s t C uL2Sq h hC hs ht hst hu hnonneg hbounded hraw
  exact
    coarseCaccioppoli_boundary_noteCoefficientControl_of_absorptionCondition_of_crossTermBound
      Q a s t C uL2Sq h hC hs ht hst habs hcross

/-- Boundary coarse Caccioppoli with the explicit-height recursion RHS, for any
height whose absorption and cross-term square bound have already been proved.
This factors out the final radius-iteration step so localized height choices
can reuse the same bound. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_absorptionCondition_of_explicitCrossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^
            (2 : ℕ) ≤
          coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hden_nonneg : 0 ≤ s * (1 - s) := by nlinarith
  have hM_nonneg :
      0 ≤ C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
    exact mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hp_nonneg : 0 ≤ coarseCaccioppoliPower s t :=
    coarseCaccioppoli_power_nonneg hs hst
  have hrec_nonneg :
      0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
    unfold coarseCaccioppoliBoundaryRecursionRhs
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hM_nonneg _)) hLambda_nonneg)
      hu
  have hexplicit_nonneg :
      0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq := by
    unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
    refine add_nonneg ?_ ?_
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) hLambda_nonneg)
        hu
    · refine mul_nonneg ?_ hrec_nonneg
      refine mul_nonneg ?_ hC
      exact mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)
  have hrec :
      CoarseCaccioppoliRadiusRecurrence F
        (coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq)
        (coarseCaccioppoliBeta s t) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
    have hF₂_nonneg : 0 ≤ F ρ₂ := hnonneg hρ₂_lower hρ₂
    calc
      F ρ₁ ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ * F ρ₂ +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ *
              Real.sqrt (F ρ₂) := hraw hρ₁ hlt hρ₂
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^
              (2 : ℕ) := by
            exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg (habs hρ₁ hlt hρ₂)
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
              Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (hcross hρ₁ hlt hρ₂) ((1 / 2 : ℝ) * F ρ₂)
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
  have hiter :=
    coarseCaccioppoli_radius_iteration
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := hexplicit_nonneg)
      hbounded hrec
  simpa [mul_comm] using hiter

/-- Boundary coarse Caccioppoli from the note-shaped local estimate, the
explicit note-facing `h` choice, and the remaining stronger triadic-scale
cross-term inequality. This is the current closest pre-Besov theorem surface
to the note's coefficient-bookkeeping step. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_heightChoice_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (hheight : CoarseCaccioppoliBoundaryHeightChoice Q a s t C h)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_boundary_qone_of_noteEstimate
    Q a s t C uL2Sq h hC hs ht hst hu hnonneg hbounded hraw
  exact
    coarseCaccioppoli_boundary_noteCoefficientControl_of_heightChoice_of_triadicGapScaleChoice
      Q a s t C uL2Sq h hC hs ht hst hu hheight hcrossscale

/-- Boundary coarse Caccioppoli with the note's actual explicit
`h = max {k + 4, ceil(...)}` height formula, once the caller supplies a triadic
scale choice `k(ρ₁, ρ₂)` and the remaining stronger triadic-scale cross-term
estimate. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_explicitHeightOfScaleChoice_of_triadicGapScaleChoice
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
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F)
    (hcrossscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ j : ℕ, CoarseCaccioppoliTriadicGapScaleChoice j ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ)
              (2 * s *
                coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ j) / 81) (coarseCaccioppoliPower s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  apply coarseCaccioppoli_boundary_qone_of_noteEstimate_of_heightChoice_of_triadicGapScaleChoice
    Q a s t C uL2Sq
    (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
    hC hs ht hst hu hnonneg hbounded hraw
  · exact coarseCaccioppoli_boundary_heightChoice_of_explicitHeightOfScaleChoice
      Q a s t C k hC hs ht hst hscale
  · exact hcrossscale

/-- Boundary coarse Caccioppoli in the completed pre-Besov form: once the
caller supplies the note-shaped local estimate and the actual explicit height
formula `h = max {k + 4, ceil(...)}`, the remaining coefficient arithmetic is
fully internal to this file and no extra cross-scale hypothesis remains. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_explicitHeightOfScaleChoice
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
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t C
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_heightChoice_of_explicitHeightOfScaleChoice
      Q a s t C k hC hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C
        (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t C
      (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hheight
  have hcross :=
    coarseCaccioppoli_boundary_noteCrossTermBound_of_explicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hscale
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hden_nonneg : 0 ≤ s * (1 - s) := by nlinarith
  have hM_nonneg :
      0 ≤ C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
    exact mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hp_nonneg : 0 ≤ coarseCaccioppoliPower s t :=
    coarseCaccioppoli_power_nonneg hs hst
  have hrec_nonneg :
      0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
    unfold coarseCaccioppoliBoundaryRecursionRhs
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hM_nonneg _)) hLambda_nonneg)
      hu
  have hexplicit_nonneg :
      0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq := by
    unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
    refine add_nonneg ?_ ?_
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) hLambda_nonneg)
        hu
    · refine mul_nonneg ?_ hrec_nonneg
      refine mul_nonneg ?_ hC
      exact mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)
  have hrec :
      CoarseCaccioppoliRadiusRecurrence F
        (coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq)
        (coarseCaccioppoliBeta s t) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
    have hF₂_nonneg : 0 ≤ F ρ₂ := hnonneg hρ₂_lower hρ₂
    calc
      F ρ₁ ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C
              (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂ * F ρ₂ +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
              (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂ *
              Real.sqrt (F ρ₂) := hraw hρ₁ hlt hρ₂
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
              (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂) ^ (2 : ℕ) := by
            exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg (habs hρ₁ hlt hρ₂)
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
              Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (hcross hρ₁ hlt hρ₂) ((1 / 2 : ℝ) * F ρ₂)
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
  have h :=
    coarseCaccioppoli_radius_iteration
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := hexplicit_nonneg)
      hbounded hrec
  simpa [mul_comm] using h

/-- Boundary coarse Caccioppoli with the localized explicit height. This keeps
the same final explicit-height bound while adding the scale-localization lower
bound `h >= 4 / s` to the local height. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice
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
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) F) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
      Q a s t C k hC hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t C
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hheight
  exact
    coarseCaccioppoli_boundary_qone_of_noteEstimate_of_absorptionCondition_of_explicitCrossTermBound
      Q a s t C uL2Sq
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hu hnonneg hbounded hraw habs
      (coarseCaccioppoli_boundary_noteCrossTermBound_of_localizedExplicitHeightOfScaleChoice
        Q a s t C uL2Sq k hC hs ht hst hu hscale)

/-- Boundary coarse Caccioppoli from the localized explicit-height note estimate
only on the deterministic Chapter-3 radius sequence. This is the concrete
iteration surface used when the local cutoff construction is only available for
the consecutive pairs `(ρ_n, ρ_{n+1})`. -/
theorem coarseCaccioppoli_boundary_qone_of_noteEstimate_on_radiusSequence_of_localizedExplicitHeightOfScaleChoice
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
      ∀ n : ℕ,
        F (coarseCaccioppoliRadiusSequence n) ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C
            (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1)) *
              F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1)) *
                Real.sqrt (F (coarseCaccioppoliRadiusSequence (n + 1)))) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
      Q a s t C k hC hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t C
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hheight
  have hcross :=
    coarseCaccioppoli_boundary_noteCrossTermBound_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq k hC hs ht hst hu hscale
  have hrec :
      CoarseCaccioppoliRadiusSequenceRecurrence F
        (coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq)
        (coarseCaccioppoliBeta s t) := by
    intro n
    have hρ₁ := (coarseCaccioppoliRadiusSequence_mem_Icc n).1
    have hρ₂ := (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
    have hρ₂_lower := (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).1
    have hlt :
        coarseCaccioppoliRadiusSequence n <
          coarseCaccioppoliRadiusSequence (n + 1) :=
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
    have hF₂_nonneg : 0 ≤ F (coarseCaccioppoliRadiusSequence (n + 1)) :=
      hnonneg hρ₂_lower hρ₂
    calc
      F (coarseCaccioppoliRadiusSequence n)
          ≤ coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C
                (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
                (coarseCaccioppoliRadiusSequence n)
                (coarseCaccioppoliRadiusSequence (n + 1)) *
              F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
                (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
                (coarseCaccioppoliRadiusSequence n)
                (coarseCaccioppoliRadiusSequence (n + 1)) *
              Real.sqrt (F (coarseCaccioppoliRadiusSequence (n + 1))) := hraw n
      _ ≤ (1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
            (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) ^ (2 : ℕ) := by
            exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg (habs hρ₁ hlt hρ₂)
      _ ≤ (1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
              Real.rpow
                (coarseCaccioppoliRadiusSequence (n + 1) -
                  coarseCaccioppoliRadiusSequence n)
                (-coarseCaccioppoliBeta s t) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (hcross hρ₁ hlt hρ₂)
                ((1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)))
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
  have h :=
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_nonneg
        Q a s t C uL2Sq hC hs ht hst hu)
      hbounded hrec
  simpa [mul_comm] using h

theorem
    coarseCaccioppoli_boundary_qone_of_noteEstimate_on_radiusSequence_of_localizedExplicitHeightOfScaleChoice_split
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      ∀ n : ℕ,
        F (coarseCaccioppoliRadiusSequence n) ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Calpha
            (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
              Q a s t Calpha k)
            (coarseCaccioppoliRadiusSequence n)
            (coarseCaccioppoliRadiusSequence (n + 1)) *
              F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                Q a s t Calpha k)
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1)) *
                Real.sqrt (F (coarseCaccioppoliRadiusSequence (n + 1)))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBoundSplit
        Q a s t Calpha Ccross uL2Sq := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t Calpha
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) :=
    coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
      Q a s t Calpha k hCalpha.le hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t Calpha
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t Calpha
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
        Q a s t Calpha k)
      hCalpha.le hs ht hst hheight
  have hcross :=
    coarseCaccioppoli_boundary_noteCrossTermBoundSplit_of_localizedExplicitHeightOfScaleChoice
      Q a s t Calpha Ccross uL2Sq k hCalpha hCcross hs ht hst hu hscale
  have hrec :
      CoarseCaccioppoliRadiusSequenceRecurrence F
        (coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
          Q a s t Calpha Ccross uL2Sq)
        (coarseCaccioppoliBeta s t) := by
    intro n
    have hρ₁ := (coarseCaccioppoliRadiusSequence_mem_Icc n).1
    have hρ₂ := (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
    have hρ₂_lower := (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).1
    have hlt :
        coarseCaccioppoliRadiusSequence n <
          coarseCaccioppoliRadiusSequence (n + 1) :=
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
    have hF₂_nonneg : 0 ≤ F (coarseCaccioppoliRadiusSequence (n + 1)) :=
      hnonneg hρ₂_lower hρ₂
    calc
      F (coarseCaccioppoliRadiusSequence n)
          ≤ coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Calpha
                (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                  Q a s t Calpha k)
                (coarseCaccioppoliRadiusSequence n)
                (coarseCaccioppoliRadiusSequence (n + 1)) *
              F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
                (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                  Q a s t Calpha k)
                (coarseCaccioppoliRadiusSequence n)
                (coarseCaccioppoliRadiusSequence (n + 1)) *
              Real.sqrt (F (coarseCaccioppoliRadiusSequence (n + 1))) := hraw n
      _ ≤ (1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
            (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                Q a s t Calpha k)
              (coarseCaccioppoliRadiusSequence n)
              (coarseCaccioppoliRadiusSequence (n + 1))) ^ (2 : ℕ) := by
            exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg
              (habs hρ₁ hlt hρ₂)
      _ ≤ (1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
            coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
                Q a s t Calpha Ccross uL2Sq *
              Real.rpow
                (coarseCaccioppoliRadiusSequence (n + 1) -
                  coarseCaccioppoliRadiusSequence n)
                (-coarseCaccioppoliBeta s t) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (hcross hρ₁ hlt hρ₂)
                ((1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)))
  unfold coarseCaccioppoliBoundaryExplicitHeightBoundSplit
  have h :=
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_nonneg
        Q a s t Calpha Ccross uL2Sq hCalpha.le hCcross hs ht hst hu)
      hbounded hrec
  simpa [mul_comm] using h

/-- Boundary coarse Caccioppoli from an all-radii split note-shaped raw estimate,
using the standard beta-dependent radius iteration.  This is the note-facing
iteration endpoint needed to keep the explicit `s,t` exponents under control. -/
theorem
    coarseCaccioppoli_boundary_qone_standard_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice_split
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimateSplit Q a s t Calpha Ccross uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) F) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
          Q a s t Calpha Ccross uL2Sq *
        coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t) := by
  have hheight :
      CoarseCaccioppoliBoundaryHeightChoice Q a s t Calpha
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) :=
    coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
      Q a s t Calpha k hCalpha.le hs ht hst hscale
  have habs :
      CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t Calpha
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) :=
    coarseCaccioppoli_boundary_noteAbsorptionCondition_of_heightChoice
      Q a s t Calpha
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
        Q a s t Calpha k)
      hCalpha.le hs ht hst hheight
  have hcross :=
    coarseCaccioppoli_boundary_noteCrossTermBoundSplit_of_localizedExplicitHeightOfScaleChoice
      Q a s t Calpha Ccross uL2Sq k hCalpha hCcross hs ht hst hu hscale
  have hrec :
      CoarseCaccioppoliRadiusRecurrence F
        (coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
          Q a s t Calpha Ccross uL2Sq)
        (coarseCaccioppoliBeta s t) := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
    have hF₂_nonneg : 0 ≤ F ρ₂ := hnonneg hρ₂_lower hρ₂
    calc
      F ρ₁ ≤
          coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Calpha
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                Q a s t Calpha k) ρ₁ ρ₂ * F ρ₂ +
            coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                Q a s t Calpha k) ρ₁ ρ₂ * Real.sqrt (F ρ₂) := hraw hρ₁ hlt hρ₂
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
              (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
                Q a s t Calpha k) ρ₁ ρ₂) ^ (2 : ℕ) := by
            exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg
              (habs hρ₁ hlt hρ₂)
      _ ≤ (1 / 2 : ℝ) * F ρ₂ +
            coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
                Q a s t Calpha Ccross uL2Sq *
              Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (hcross hρ₁ hlt hρ₂) ((1 / 2 : ℝ) * F ρ₂)
  exact
    coarseCaccioppoli_standard_radius_iteration
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_nonneg
        Q a s t Calpha Ccross uL2Sq hCalpha.le hCcross hs ht hst hu)
      hbounded hrec

theorem
    coarseCaccioppoli_boundary_qone_standard_le_noteRhs_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice_split
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) (hTheta : 0 < ThetaRatio Q s t a)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimateSplit Q a s t Calpha Ccross uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
          Q a s t Calpha k) F) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
          Q a s t Calpha Ccross)
        uL2Sq := by
  have hqone :
      F (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit
          Q a s t Calpha Ccross uL2Sq := by
    have h :=
      coarseCaccioppoli_boundary_qone_standard_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice_split
        (Q := Q) (a := a) (s := s) (t := t) (Calpha := Calpha)
        (Ccross := Ccross) (uL2Sq := uL2Sq) (k := k)
        hCalpha hCcross hs ht hst hu hnonneg hbounded hscale hraw
    simpa [coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit,
      mul_comm, mul_left_comm, mul_assoc] using h
  exact hqone.trans
    (coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit_le_noteRhs_standardExplicitNoteConstantSplit
      Q a s t Calpha Ccross uL2Sq hs ht hst hu hTheta)

end

end Homogenization
