/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Boundary.NoteRhs.StandardSplit
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration

/-! # Note Rhs -/

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoliInteriorNoteRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliInteriorNoteRhs Q a s t C uL2Sq := by
  simpa [coarseCaccioppoliInteriorNoteRhs] using
    coarseCaccioppoliBoundaryNoteRhs_nonneg Q a s t C uL2Sq hC hs ht hst hu

theorem coarseCaccioppoliInteriorNoteRhs_mono_C {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C₁ C₂ uL2Sq : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₁C₂ : C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliInteriorNoteRhs Q a s t C₁ uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t C₂ uL2Sq := by
  simpa [coarseCaccioppoliInteriorNoteRhs] using
    coarseCaccioppoliBoundaryNoteRhs_mono_C
      Q a s t C₁ C₂ uL2Sq hC₁ hC₁C₂ hs ht hst hu

theorem coarseCaccioppoliInteriorNoteRhs_mul_const_le_of_mul_constant_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t M C₁ C₂ uL2Sq : ℝ)
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    M * coarseCaccioppoliInteriorNoteRhs Q a s t C₁ uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t C₂ uL2Sq := by
  simpa [coarseCaccioppoliInteriorNoteRhs] using
    coarseCaccioppoliBoundaryNoteRhs_mul_const_le_of_mul_constant_le
      Q a s t M C₁ C₂ uL2Sq hM hC₁ hMC₁C₂ hs ht hst hu

theorem coarseCaccioppoliBoundaryRecursionRhs_eq_zero_of_uL2Sq_eq_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq = 0 := by
  simp [coarseCaccioppoliBoundaryRecursionRhs, hu]

theorem
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_eq_zero_of_uL2Sq_eq_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq = 0 := by
  subst uL2Sq
  simp [coarseCaccioppoliBoundaryExplicitHeightRecursionRhs,
    coarseCaccioppoliBoundaryRecursionRhs]

theorem coarseCaccioppoliBoundaryExplicitHeightBound_eq_zero_of_uL2Sq_eq_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq = 0 := by
  simp [coarseCaccioppoliBoundaryExplicitHeightBound,
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_eq_zero_of_uL2Sq_eq_zero
      Q a s t C uL2Sq hu]

theorem coarseCaccioppoliBoundaryNoteRhs_eq_zero_of_uL2Sq_eq_zero {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliBoundaryNoteRhs Q a s t C uL2Sq = 0 := by
  simp [coarseCaccioppoliBoundaryNoteRhs, hu]

theorem
    coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_uL2Sq_eq_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq := by
  rw [coarseCaccioppoliBoundaryExplicitHeightBound_eq_zero_of_uL2Sq_eq_zero
    Q a s t Cinternal uL2Sq hu,
    coarseCaccioppoliBoundaryNoteRhs_eq_zero_of_uL2Sq_eq_zero
      Q a s t Cnote uL2Sq hu]

theorem
    coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_uL2Sq_eq_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (hu : uL2Sq = 0) :
    coarseCaccioppoliInteriorExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t Cnote uL2Sq := by
  exact
    coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_boundary Q a s t
      Cinternal Cnote uL2Sq
      (coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_uL2Sq_eq_zero
        Q a s t Cinternal Cnote uL2Sq hu)

theorem coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (hcoeff :
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq := by
  rw [coarseCaccioppoliBoundaryExplicitHeightBound_eq_coeff_mul_uL2Sq,
    coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq]
  exact mul_le_mul_of_nonneg_right hcoeff hu

theorem coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_coeff_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (hcoeff :
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliInteriorExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t Cnote uL2Sq :=
  coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_boundary Q a s t
    Cinternal Cnote uL2Sq
    (coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le
      Q a s t Cinternal Cnote uL2Sq hcoeff hu)

theorem
    coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le_noteCoeff_of_noteConstant_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cadequate Cnote uL2Sq : ℝ)
    (hcoeff :
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t Cadequate)
    (hCadequate : 0 ≤ Cadequate) (hCadequateCnote : Cadequate ≤ Cnote)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq := by
  exact
    coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le
      Q a s t Cinternal Cnote uL2Sq
      (le_trans hcoeff
        (coarseCaccioppoliBoundaryNoteCoeff_mono_C
          Q a s t Cadequate Cnote hCadequate hCadequateCnote hs ht hst))
      hu

theorem
    coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_coeff_le_noteCoeff_of_noteConstant_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cadequate Cnote uL2Sq : ℝ)
    (hcoeff :
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t Cadequate)
    (hCadequate : 0 ≤ Cadequate) (hCadequateCnote : Cadequate ≤ Cnote)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliInteriorExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t Cnote uL2Sq :=
  coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_boundary Q a s t
    Cinternal Cnote uL2Sq
    (coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le_noteCoeff_of_noteConstant_le
      Q a s t Cinternal Cadequate Cnote uL2Sq hcoeff
      hCadequate hCadequateCnote hs ht hst hu)

theorem coarseCaccioppoliBoundaryCoeff_le_of_explicitHeightBound_le_noteRhs
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (hu : 0 < uL2Sq)
    (h :
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq) :
    coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
      coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote := by
  rw [coarseCaccioppoliBoundaryExplicitHeightBound_eq_coeff_mul_uL2Sq,
    coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq] at h
  exact (mul_le_mul_iff_of_pos_right hu).1 h

theorem coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_iff_coeff_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ) (hu : 0 < uL2Sq) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq ↔
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t Cinternal ≤
        coarseCaccioppoliBoundaryNoteCoeff Q a s t Cnote := by
  constructor
  · exact
      coarseCaccioppoliBoundaryCoeff_le_of_explicitHeightBound_le_noteRhs
        Q a s t Cinternal Cnote uL2Sq hu
  · intro hcoeff
    exact
      coarseCaccioppoliBoundaryExplicitHeightBound_le_noteRhs_of_coeff_le
        Q a s t Cinternal Cnote uL2Sq hcoeff hu.le

/-- Boundary coarse Caccioppoli in the current honest Chapter-3 form: once the
local cutoff/Besov step has produced the radius-recursion with the note-facing
multiscale prefactor, the deterministic radius iteration yields the final
boundary bound. -/
theorem coarseCaccioppoli_boundary_qone_of_radius_recurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec :
      CoarseCaccioppoliRadiusRecurrence F
        (coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq)
        (coarseCaccioppoliBeta s t)) :
    F (1 / 3 : ℝ) ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliBoundaryBound
  have h :=
    coarseCaccioppoli_radius_iteration
      (hβ := coarseCaccioppoli_beta_nonneg hs hst)
      (hA := coarseCaccioppoliBoundaryRecursionRhs_nonneg Q a s t C uL2Sq hC hs ht hst hu)
      hbounded hrec
  simpa [mul_comm] using h

/-- The local single-cube estimate plus coefficient bookkeeping imply the
already-absorbed pre-recurrence surface. This is the current pre-Besov bridge
between the note's local estimate and the iteration backbone. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_rawEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ} {α B : ℝ → ℝ → ℝ}
    (hraw : CoarseCaccioppoliBoundaryRawEstimate F α B)
    (hctrl : CoarseCaccioppoliBoundaryCoefficientControl Q a s t C uL2Sq α B) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨α ρ₁ ρ₂, B ρ₁ ρ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hctrl hρ₁ hlt hρ₂).1
  · exact (hctrl hρ₁ hlt hρ₂).2.1
  · exact (hctrl hρ₁ hlt hρ₂).2.2.1
  · exact hraw hρ₁ hlt hρ₂
  · exact (hctrl hρ₁ hlt hρ₂).2.2.2

/-- Boundary pre-recurrence from the note-shaped raw estimate and note-shaped
coefficient-control surface. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (hctrl : CoarseCaccioppoliBoundaryNoteCoefficientControl Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  exact coarseCaccioppoli_boundary_preRecurrence_of_rawEstimate
    Q a s t C uL2Sq hraw hctrl

/-- Boundary pre-recurrence from the note-shaped raw estimate plus the two
remaining note-specific bookkeeping obligations. -/
theorem coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate_of_absorptionCondition_of_crossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross : CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h) :
    CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F := by
  apply coarseCaccioppoli_boundary_preRecurrence_of_noteEstimate
    Q a s t C uL2Sq h hraw
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact coarseCaccioppoliBoundaryAlphaOfHeight_nonneg
      Q a s t C h hC hs ht hst hlt
  · exact habs hρ₁ hlt hρ₂
  · exact coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg
      Q a s C uL2Sq h hC hs hlt
  · exact hcross hρ₁ hlt hρ₂

/-- Explicit-height pre-recurrence from a note-shaped raw estimate, absorption,
and the enlarged explicit-height cross-term square bound. -/
theorem coarseCaccioppoli_boundary_explicitHeightPreRecurrence_of_noteEstimate_of_absorptionCondition_of_explicitCrossTermBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hraw : CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F)
    (habs : CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h)
    (hcross :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^
            (2 : ℕ) ≤
          coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)) :
    CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine
    ⟨coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂,
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂,
      ?_, ?_, ?_, ?_, ?_⟩
  · exact coarseCaccioppoliBoundaryAlphaOfHeight_nonneg
      Q a s t C h hC hs ht hst hlt
  · exact habs hρ₁ hlt hρ₂
  · exact coarseCaccioppoliBoundaryCrossCoeffOfHeight_nonneg
      Q a s C uL2Sq h hC hs hlt
  · exact hraw hρ₁ hlt hρ₂
  · exact hcross hρ₁ hlt hρ₂

/-- The pre-recurrence middle layer of the boundary proof implies the abstract
radius-recursion used by the deterministic iteration backbone. -/
theorem coarseCaccioppoli_boundary_radius_recurrence_of_preRecurrence {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hpre : CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F) :
    CoarseCaccioppoliRadiusRecurrence F
      (coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq)
      (coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hpre hρ₁ hlt hρ₂ with ⟨α, B, -, hα_le, -, hstep, hBsq⟩
  have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
  have hF₂_nonneg : 0 ≤ F ρ₂ := hnonneg hρ₂_lower hρ₂
  calc
    F ρ₁ ≤ α * F ρ₂ + B * Real.sqrt (F ρ₂) := hstep
    _ ≤ (1 / 2 : ℝ) * F ρ₂ + B ^ (2 : ℕ) := by
      exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg hα_le
    _ ≤ (1 / 2 : ℝ) * F ρ₂ +
          coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hBsq ((1 / 2 : ℝ) * F ρ₂)

/-- Explicit-height pre-recurrence implies the radius recurrence with the
enlarged explicit-height prefactor. -/
theorem coarseCaccioppoli_boundary_radius_recurrence_of_explicitHeightPreRecurrence
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    {F : ℝ → ℝ}
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hpre :
      CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F) :
    CoarseCaccioppoliRadiusRecurrence F
      (coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq)
      (coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  rcases hpre hρ₁ hlt hρ₂ with ⟨α, B, -, hα_le, -, hstep, hBsq⟩
  have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
  have hF₂_nonneg : 0 ≤ F ρ₂ := hnonneg hρ₂_lower hρ₂
  calc
    F ρ₁ ≤ α * F ρ₂ + B * Real.sqrt (F ρ₂) := hstep
    _ ≤ (1 / 2 : ℝ) * F ρ₂ + B ^ (2 : ℕ) := by
      exact coarseCaccioppoli_absorb_cross_term hF₂_nonneg hα_le
    _ ≤ (1 / 2 : ℝ) * F ρ₂ +
          coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hBsq ((1 / 2 : ℝ) * F ρ₂)

end

end Homogenization
