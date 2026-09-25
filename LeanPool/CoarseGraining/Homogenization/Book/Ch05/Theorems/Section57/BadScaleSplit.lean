/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadEventSummability

/-! # Bad Scale Split -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory

/-!
# Deterministic splitting of bad-scale events

This file records the exact trichotomy used in the proof of
Theorem `t.homogenization.quenched`: the localized high range, the crude
bottom range, and the crude complementary top range.
-/

noncomputable section

variable {Ω : Type*}

/-- The intermediate scale selected for a bad pair in the high-range
argument. -/
noncomputable def selectedBadPairScale
    (K a t α : ℝ) (q m n : ℕ) : ℕ :=
  let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  Nat.ceil
    ((a * Real.log 3)⁻¹ *
      (Real.log (max (2 * K) 1) + x * Real.log 3))

/-- High part of a bad-scale event: the selected intermediate scale is
strictly below `n`, so the localized first-quenched estimate applies. -/
def highBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ,
    selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- High part in the sharp range where the bad scale lies below the localized
scale.  This branch keeps the `q`-scale concentration gain. -/
def highTopBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ,
    q ≤ n ∧
    selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- High part in the bottom range.  The localized estimate still applies, but
the sharp `q ≤ n` concentration gain is not available. -/
def highBottomBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ,
    n ≤ q ∧
    selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- Crude bottom part: the selected localized scale is not available and the
localized scale is below the bad scale. -/
def crudeBottomBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ,
    n ≤ q ∧
    ¬ selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

/-- Crude top complement: the bad scale is below `n`, but the selected
intermediate scale is not available below `n`. -/
def crudeTopBadScaleEvent
    (H : ℕ → ℕ → Ω → ℝ) (K a t α : ℝ) (q : ℕ) : Set Ω :=
  {ω | ∃ m n : ℕ,
    q ≤ n ∧
    ¬ selectedBadPairScale K a t α q m n < n ∧
    ω ∈ badPairEvent H t α q m n}

theorem badScaleEvent_subset_split
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    badScaleEvent H t α q ⊆
      highBadScaleEvent H K a t α q ∪
        crudeBottomBadScaleEvent H K a t α q ∪
          crudeTopBadScaleEvent H K a t α q := by
  intro ω hω
  rcases hω with ⟨m, n, hnm, hqm, hbad⟩
  have hpair : ω ∈ badPairEvent H t α q m n := by
    exact ⟨hnm, hqm, hbad⟩
  by_cases hhigh : selectedBadPairScale K a t α q m n < n
  · exact Or.inl (Or.inl ⟨m, n, hhigh, hpair⟩)
  · by_cases hnq : n ≤ q
    · exact Or.inl (Or.inr ⟨m, n, hnq, hhigh, hpair⟩)
    · have hqn : q ≤ n := le_of_lt (Nat.lt_of_not_ge hnq)
      exact Or.inr ⟨m, n, hqn, hhigh, hpair⟩

theorem badScaleEvent_subset_sharp_split
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    badScaleEvent H t α q ⊆
      highTopBadScaleEvent H K a t α q ∪
        highBottomBadScaleEvent H K a t α q ∪
          crudeBottomBadScaleEvent H K a t α q ∪
            crudeTopBadScaleEvent H K a t α q := by
  intro ω hω
  rcases hω with ⟨m, n, hnm, hqm, hbad⟩
  have hpair : ω ∈ badPairEvent H t α q m n := by
    exact ⟨hnm, hqm, hbad⟩
  by_cases hhigh : selectedBadPairScale K a t α q m n < n
  · by_cases hqn : q ≤ n
    · exact Or.inl (Or.inl (Or.inl ⟨m, n, hqn, hhigh, hpair⟩))
    · have hnq : n ≤ q := le_of_lt (Nat.lt_of_not_ge hqn)
      exact Or.inl (Or.inl (Or.inr ⟨m, n, hnq, hhigh, hpair⟩))
  · by_cases hnq : n ≤ q
    · exact Or.inl (Or.inr ⟨m, n, hnq, hhigh, hpair⟩)
    · have hqn : q ≤ n := le_of_lt (Nat.lt_of_not_ge hnq)
      exact Or.inr ⟨m, n, hqn, hhigh, hpair⟩

theorem measureReal_badScaleEvent_le_split
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    μ.real (badScaleEvent H t α q) ≤
      μ.real (highBadScaleEvent H K a t α q) +
        μ.real (crudeBottomBadScaleEvent H K a t α q) +
          μ.real (crudeTopBadScaleEvent H K a t α q) := by
  have hsubset := badScaleEvent_subset_split
    (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (badScaleEvent H t α q)
        ≤ μ.real
            (highBadScaleEvent H K a t α q ∪
              crudeBottomBadScaleEvent H K a t α q ∪
                crudeTopBadScaleEvent H K a t α q) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤
        μ.real (highBadScaleEvent H K a t α q ∪
          crudeBottomBadScaleEvent H K a t α q) +
          μ.real (crudeTopBadScaleEvent H K a t α q) :=
          measureReal_union_le _ _
    _ ≤
        (μ.real (highBadScaleEvent H K a t α q) +
          μ.real (crudeBottomBadScaleEvent H K a t α q)) +
            μ.real (crudeTopBadScaleEvent H K a t α q) := by
          exact add_le_add (measureReal_union_le _ _) le_rfl
    _ =
        μ.real (highBadScaleEvent H K a t α q) +
          μ.real (crudeBottomBadScaleEvent H K a t α q) +
            μ.real (crudeTopBadScaleEvent H K a t α q) := by
          ring

theorem measureReal_badScaleEvent_le_sharp_split
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    μ.real (badScaleEvent H t α q) ≤
      μ.real (highTopBadScaleEvent H K a t α q) +
        μ.real (highBottomBadScaleEvent H K a t α q) +
          μ.real (crudeBottomBadScaleEvent H K a t α q) +
            μ.real (crudeTopBadScaleEvent H K a t α q) := by
  have hsubset := badScaleEvent_subset_sharp_split
    (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (badScaleEvent H t α q)
        ≤ μ.real
            (highTopBadScaleEvent H K a t α q ∪
              highBottomBadScaleEvent H K a t α q ∪
                crudeBottomBadScaleEvent H K a t α q ∪
                  crudeTopBadScaleEvent H K a t α q) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤
        μ.real (highTopBadScaleEvent H K a t α q ∪
          highBottomBadScaleEvent H K a t α q ∪
            crudeBottomBadScaleEvent H K a t α q) +
          μ.real (crudeTopBadScaleEvent H K a t α q) :=
          measureReal_union_le _ _
    _ ≤
        (μ.real (highTopBadScaleEvent H K a t α q ∪
          highBottomBadScaleEvent H K a t α q) +
            μ.real (crudeBottomBadScaleEvent H K a t α q)) +
          μ.real (crudeTopBadScaleEvent H K a t α q) := by
          exact add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤
        ((μ.real (highTopBadScaleEvent H K a t α q) +
          μ.real (highBottomBadScaleEvent H K a t α q)) +
            μ.real (crudeBottomBadScaleEvent H K a t α q)) +
          μ.real (crudeTopBadScaleEvent H K a t α q) := by
          exact add_le_add
            (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl
    _ =
        μ.real (highTopBadScaleEvent H K a t α q) +
          μ.real (highBottomBadScaleEvent H K a t α q) +
            μ.real (crudeBottomBadScaleEvent H K a t α q) +
              μ.real (crudeTopBadScaleEvent H K a t α q) := by
          ring

end

end Section57
end Ch05
end Book
end Homogenization
