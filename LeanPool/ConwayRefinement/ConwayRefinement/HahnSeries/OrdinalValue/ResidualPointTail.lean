/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint

/-!
# Final tails of Berarducci residual points

For a cutoff `η`, `residualPointTail b η` is the final part of `X(b)` strictly above `η`.
Since every residual point is strictly negative, this is exactly `X(b) ∩ (η, 0)`.

The source phrase "sufficiently close to zero" is represented later by
`nhdsWithin 0 (Set.Iio 0)`. Its generic cutoff interface prevents a silent change of side or
inclusion of zero.

The remaining results isolate elementary consequences of well-ordering and least-upper-bound
hypotheses. They are the proved part of the interface needed to state and partially prove
Berarducci, Lemmas 6.8 and 6.9.
-/

universe v

open scoped HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

/-- The residual points strictly above the real cutoff `η`. -/
def residualPointTail (b : SeriesWithOrdinalValueAboveOne K) (η : ℝ) : Set ℝ :=
  residualPointSet b ∩ Set.Ioi η

/-- Membership in a residual-point tail records both residual-point membership and the strict
cutoff inequality. -/
theorem mem_residualPointTail_iff
    {b : SeriesWithOrdinalValueAboveOne K} {η γ : ℝ} :
    γ ∈ residualPointTail b η ↔ γ ∈ residualPointSet b ∧ η < γ :=
  (Iff.rfl)

/-- A residual-point tail is exactly the intersection of `X(b)` with `(η, 0)`. -/
theorem residualPointTail_eq_inter_Ioo
    (b : SeriesWithOrdinalValueAboveOne K) (η : ℝ) :
    residualPointTail b η = residualPointSet b ∩ Set.Ioo η 0 := by
  ext γ
  rw [mem_residualPointTail_iff]
  constructor
  · rintro ⟨hγ, hηγ⟩
    exact ⟨hγ, hηγ, residualPointSet_subset_Iio b hγ⟩
  · rintro ⟨hγ, hηγ, _⟩
    exact ⟨hγ, hηγ⟩

/-- Every residual-point tail is contained in `X(b)`. -/
theorem residualPointTail_subset_residualPointSet
    (b : SeriesWithOrdinalValueAboveOne K) (η : ℝ) :
    residualPointTail b η ⊆ residualPointSet b :=
  Set.inter_subset_left

/-- Residual-point tails are antitone in their cutoff. -/
theorem residualPointTail_antitone
    (b : SeriesWithOrdinalValueAboveOne K) : Antitone (residualPointTail b) := by
  intro η ξ hηξ γ hγ
  exact ⟨hγ.1, hηξ.trans_lt hγ.2⟩

/-- A tail of a partially well-ordered residual-point set is partially well ordered. -/
theorem residualPointTail_isPWO
    (b : SeriesWithOrdinalValueAboveOne K) (η : ℝ)
    (hX : (residualPointSet b).IsPWO) :
    (residualPointTail b η).IsPWO :=
  hX.mono (residualPointTail_subset_residualPointSet b η)

/-- If zero is the least upper bound of `X(b)`, every tail with negative cutoff is nonempty and
still has least upper bound zero. -/
theorem residualPointTail_nonempty_and_isLUB
    (b : SeriesWithOrdinalValueAboveOne K) {η : ℝ} (hη : η < 0)
    (hX : IsLUB (residualPointSet b) 0) :
    (residualPointTail b η).Nonempty ∧ IsLUB (residualPointTail b η) 0 := by
  obtain ⟨x, hxX, hηx, _⟩ := hX.exists_between hη
  have hxTail : x ∈ residualPointTail b η := ⟨hxX, hηx⟩
  refine ⟨⟨x, hxTail⟩, ⟨?_, ?_⟩⟩
  · intro y hy
    exact hX.1 hy.1
  · intro a ha
    apply hX.2
    intro y hy
    by_cases hηy : η < y
    · exact ha ⟨hy, hηy⟩
    · exact (le_of_not_gt hηy).trans (hηx.le.trans (ha hxTail))

end Berarducci
