/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleUnion

/-! # Bad Tail Union -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Tail union for quantitative bad scales

This file contains the union bound over all bad scales at or above a level
`N`.  It is the quantitative tail-event layer used before constructing the
random minimal scale; it deliberately does not introduce an eventual
almost-sure stopping scale.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that at least one bad scale occurs at or above `N`. -/
def badTailEvent (Bad : ℕ → Set Ω) (N : ℕ) : Set Ω :=
  {ω | ∃ K : ℕ, N ≤ K ∧ ω ∈ Bad K}

omit [MeasurableSpace Ω] in
theorem badScaleEvent_antitone
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} (hα : 0 ≤ α)
    {N K : ℕ} (hNK : N ≤ K) :
    badScaleEvent H t α K ⊆ badScaleEvent H t α N := by
  intro ω hω
  rcases hω with ⟨m, n, hnm, hKm, hbad⟩
  refine ⟨m, n, hnm, hNK.trans hKm, ?_⟩
  have hsub_le : m - K ≤ m - N := Nat.sub_le_sub_left hNK m
  have hcast_le : ((m - K : ℕ) : ℝ) ≤ ((m - N : ℕ) : ℝ) := by
    exact_mod_cast hsub_le
  have hexp_le :
      -α * ((m - N : ℕ) : ℝ) ≤ -α * ((m - K : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonpos_left hcast_le (by linarith)
  have hrhs_le :
      (3 : ℝ) ^ (-α * ((m - N : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (-α * ((m - K : ℕ) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_le
  exact lt_of_le_of_lt hrhs_le hbad

omit [MeasurableSpace Ω] in
theorem badTailEvent_badScaleEvent_subset
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} (hα : 0 ≤ α) {N : ℕ} :
    badTailEvent (badScaleEvent H t α) N ⊆ badScaleEvent H t α N := by
  intro ω hω
  rcases hω with ⟨K, hNK, hK⟩
  exact badScaleEvent_antitone (H := H) (t := t) (α := α) hα hNK hK

omit [MeasurableSpace Ω] in
theorem badTailEvent_eq_iUnion_shift
    {Bad : ℕ → Set Ω} {N : ℕ} :
    badTailEvent Bad N = ⋃ j : ℕ, Bad (N + j) := by
  ext ω
  constructor
  · rintro ⟨K, hNK, hK⟩
    refine Set.mem_iUnion.2 ⟨K - N, ?_⟩
    have hKN : N + (K - N) = K := Nat.add_sub_of_le hNK
    simpa [hKN] using hK
  · rintro hω
    rcases Set.mem_iUnion.1 hω with ⟨j, hj⟩
    exact ⟨N + j, Nat.le_add_right N j, hj⟩

/-- Countable union bound for bad-tail events. -/
theorem measureReal_badTailEvent_le_tsum_shift
    {μ : Measure Ω} [IsFiniteMeasure μ] {Bad : ℕ → Set Ω} {N : ℕ}
    (hBad : Summable fun j : ℕ => μ.real (Bad (N + j))) :
    μ.real (badTailEvent Bad N) ≤
      ∑' j : ℕ, μ.real (Bad (N + j)) := by
  rw [badTailEvent_eq_iUnion_shift]
  exact measureReal_iUnion_nat_le_tsum (μ := μ) hBad

/-- The concrete bad-tail event for the finite-probe bad-scale events. -/
def probeBadTailEvent {Ω : Type*}
    (H : ℕ → ℕ → Ω → ℝ) (t α : ℝ) (N : ℕ) : Set Ω :=
  badTailEvent (badScaleEvent H t α) N

/-- Union bound for the concrete finite-probe bad-tail event. -/
theorem measureReal_probeBadTailEvent_le_tsum_shift
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {N : ℕ}
    (hBad : Summable fun j : ℕ =>
      μ.real (badScaleEvent H t α (N + j))) :
    μ.real (probeBadTailEvent H t α N) ≤
      ∑' j : ℕ, μ.real (badScaleEvent H t α (N + j)) := by
  exact measureReal_badTailEvent_le_tsum_shift
    (μ := μ) (Bad := badScaleEvent H t α) (N := N) hBad

end

end Section57
end Ch05
end Book
end Homogenization
