/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.KernelUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentUnion

/-! # Bad Scale Component Summation -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Summing split bad-scale components

This file begins the passage from fixed-pair component estimates to
bad-scale component estimates.  The high-top branch has one geometric direction
and one finite row multiplicity, so it uses the linear kernel union bound.
-/

noncomputable section

variable {Ω : Type*}

theorem highTopBadScaleEvent_subset_linearRows
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    highTopBadScaleEvent H K a t α q ⊆
      ⋃ r : ℕ, ⋃ j : Fin (r + 1),
        highTopPairEvent H K a t α q (q + r) (q + j.val) := by
  intro ω hω
  rcases hω with ⟨m, n, hqn, hhigh, hpair⟩
  rcases hpair with ⟨hnm, hqm, hbad⟩
  let r : ℕ := m - q
  let j : Fin (r + 1) :=
    ⟨n - q, by
      have hsub_le : n - q ≤ m - q := Nat.sub_le_sub_right (le_of_lt hnm) q
      omega⟩
  refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  have hm : q + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hqm
  have hn : q + j.val = n := by
    dsimp [j]
    exact Nat.add_sub_of_le hqn
  simpa [highTopPairEvent, hm, hn] using
    (⟨hqn, hhigh, ⟨hnm, hqm, hbad⟩⟩ :
      ω ∈ highTopPairEvent H K a t α q m n)

theorem highBottomBadScaleEvent_subset_constRows
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    highBottomBadScaleEvent H K a t α q ⊆
      ⋃ r : ℕ, ⋃ j : Fin (q + 1),
        highBottomPairEvent H K a t α q (q + r) (q - j.val) := by
  intro ω hω
  rcases hω with ⟨m, n, hnq, hhigh, hpair⟩
  rcases hpair with ⟨hnm, hqm, hbad⟩
  let r : ℕ := m - q
  let j : Fin (q + 1) := ⟨q - n, by omega⟩
  refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  have hm : q + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hqm
  have hn : q - j.val = n := by
    dsimp [j]
    exact Nat.sub_sub_self hnq
  simpa [highBottomPairEvent, hm, hn] using
    (⟨hnq, hhigh, ⟨hnm, hqm, hbad⟩⟩ :
      ω ∈ highBottomPairEvent H K a t α q m n)

theorem crudeBottomBadScaleEvent_subset_constRows
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ} :
    crudeBottomBadScaleEvent H K a t α q ⊆
      ⋃ r : ℕ, ⋃ j : Fin (q + 1),
        crudeBottomPairEvent H K a t α q (q + r) (q - j.val) := by
  intro ω hω
  rcases hω with ⟨m, n, hnq, hnot, hpair⟩
  rcases hpair with ⟨hnm, hqm, hbad⟩
  let r : ℕ := m - q
  let j : Fin (q + 1) := ⟨q - n, by omega⟩
  refine Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  have hm : q + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hqm
  have hn : q - j.val = n := by
    dsimp [j]
    exact Nat.sub_sub_self hnq
  have hnℓ : n ≤ selectedBadPairScale K a t α q m n := le_of_not_gt hnot
  simpa [crudeBottomPairEvent, hm, hn] using
    (⟨hnq, hnℓ, ⟨hnm, hqm, hbad⟩⟩ :
      ω ∈ crudeBottomPairEvent H K a t α q m n)

variable [MeasurableSpace Ω]

theorem measureReal_highTopBadScaleEvent_le_exp_linear_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (r + 1)),
      μ.real (highTopPairEvent H K a t α q (q + r) (q + j.val)) ≤
        C * Real.exp (-((A * ρ ^ r) ^ η))) :
    μ.real (highTopBadScaleEvent H K a t α q) ≤
      C * (Real.exp (-(A ^ η)) * linearExpKernelConst ρ η) := by
  let E : (r : ℕ) → Fin (r + 1) → Set Ω :=
    fun r j => highTopPairEvent H K a t α q (q + r) (q + j.val)
  have hsubset :
      highTopBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j := by
    simpa [E] using
      highTopBadScaleEvent_subset_linearRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (highTopBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ C * (Real.exp (-(A ^ η)) * linearExpKernelConst ρ η) :=
          measureReal_iUnion_linearRows_le_exp_linear_kernel
            (μ := μ) (E := E) hC hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

/-- Weighted high-top summation.  This is the no-loss version of the
linear-row component bound: the row-dependent finite-union prefactor is carried
as `w ^ r` and absorbed only by the weighted kernel. -/
theorem measureReal_highTopBadScaleEvent_le_weighted_exp_linear_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C w : ℝ}
    (hC : 0 ≤ C) (hw : 0 < w) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (r + 1)),
      μ.real (highTopPairEvent H K a t α q (q + r) (q + j.val)) ≤
        C * (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
    μ.real (highTopBadScaleEvent H K a t α q) ≤
      C * (Real.exp (-(A ^ η)) *
        weightedLinearExpKernelConst w (ρ ^ η)) := by
  let E : (r : ℕ) → Fin (r + 1) → Set Ω :=
    fun r j => highTopPairEvent H K a t α q (q + r) (q + j.val)
  have hsubset :
      highTopBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j := by
    simpa [E] using
      highTopBadScaleEvent_subset_linearRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (highTopBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ C * (Real.exp (-(A ^ η)) *
        weightedLinearExpKernelConst w (ρ ^ η)) :=
          measureReal_iUnion_linearRows_le_weighted_exp_linear_kernel
            (μ := μ) (E := E) hC hw hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

theorem measureReal_highBottomBadScaleEvent_le_exp_constRows_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (q + 1)),
      μ.real (highBottomPairEvent H K a t α q (q + r) (q - j.val)) ≤
        C * Real.exp (-((A * ρ ^ r) ^ η))) :
    μ.real (highBottomBadScaleEvent H K a t α q) ≤
      ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) := by
  let E : ℕ → Fin (q + 1) → Set Ω :=
    fun r j => highBottomPairEvent H K a t α q (q + r) (q - j.val)
  have hsubset :
      highBottomBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j := by
    simpa [E] using
      highBottomBadScaleEvent_subset_constRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (highBottomBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) :=
          measureReal_iUnion_constRows_le_exp_kernel
            (μ := μ) (Q := q + 1) (E := E) hC hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

/-- Weighted high-bottom summation with a fixed finite row size. -/
theorem measureReal_highBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C w : ℝ}
    (hC : 0 ≤ C) (hw : 0 < w) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (q + 1)),
      μ.real (highBottomPairEvent H K a t α q (q + r) (q - j.val)) ≤
        C * (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
    μ.real (highBottomBadScaleEvent H K a t α q) ≤
      ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) *
          weightedGeometricExpKernelConst w (ρ ^ η)) := by
  let E : ℕ → Fin (q + 1) → Set Ω :=
    fun r j => highBottomPairEvent H K a t α q (q + r) (q - j.val)
  have hsubset :
      highBottomBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j := by
    simpa [E] using
      highBottomBadScaleEvent_subset_constRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (highBottomBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) *
          weightedGeometricExpKernelConst w (ρ ^ η)) :=
          measureReal_iUnion_constRows_le_weighted_exp_kernel
            (μ := μ) (Q := q + 1) (E := E) hC hw hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

theorem measureReal_crudeBottomBadScaleEvent_le_exp_constRows_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (q + 1)),
      μ.real (crudeBottomPairEvent H K a t α q (q + r) (q - j.val)) ≤
        C * Real.exp (-((A * ρ ^ r) ^ η))) :
    μ.real (crudeBottomBadScaleEvent H K a t α q) ≤
      ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) := by
  let E : ℕ → Fin (q + 1) → Set Ω :=
    fun r j => crudeBottomPairEvent H K a t α q (q + r) (q - j.val)
  have hsubset :
      crudeBottomBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j := by
    simpa [E] using
      crudeBottomBadScaleEvent_subset_constRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (crudeBottomBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) :=
          measureReal_iUnion_constRows_le_exp_kernel
            (μ := μ) (Q := q + 1) (E := E) hC hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

/-- Weighted crude-bottom summation with a fixed finite row size. -/
theorem measureReal_crudeBottomBadScaleEvent_le_weighted_exp_constRows_kernel_of_reindexed_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {K a t α : ℝ} {q : ℕ}
    {A ρ η C w : ℝ}
    (hC : 0 ≤ C) (hw : 0 < w) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hpair : ∀ (r : ℕ) (j : Fin (q + 1)),
      μ.real (crudeBottomPairEvent H K a t α q (q + r) (q - j.val)) ≤
        C * (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
    μ.real (crudeBottomBadScaleEvent H K a t α q) ≤
      ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) *
          weightedGeometricExpKernelConst w (ρ ^ η)) := by
  let E : ℕ → Fin (q + 1) → Set Ω :=
    fun r j => crudeBottomPairEvent H K a t α q (q + r) (q - j.val)
  have hsubset :
      crudeBottomBadScaleEvent H K a t α q ⊆
        ⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j := by
    simpa [E] using
      crudeBottomBadScaleEvent_subset_constRows
        (H := H) (K := K) (a := a) (t := t) (α := α) (q := q)
  calc
    μ.real (crudeBottomBadScaleEvent H K a t α q)
        ≤ μ.real (⋃ r : ℕ, ⋃ j : Fin (q + 1), E r j) :=
          measureReal_mono (μ := μ) hsubset
    _ ≤ ((q + 1 : ℕ) : ℝ) * C *
        (Real.exp (-(A ^ η)) *
          weightedGeometricExpKernelConst w (ρ ^ η)) :=
          measureReal_iUnion_constRows_le_weighted_exp_kernel
            (μ := μ) (Q := q + 1) (E := E) hC hw hA hρ hη
            (by
              intro r j
              simpa [E] using hpair r j)

end

end Section57
end Ch05
end Book
end Homogenization
