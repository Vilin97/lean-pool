/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.SetTheory.Cardinal.Basic

/-!
# The rearrangement number

Convergence is taken along the natural partial sums. In particular, ordinary
`Summable a` would be the wrong definition of conditional convergence over `ℝ`.
We use mathlib's `SummationFilter.conditional ℕ` explicitly.
-/

open Filter Finset Cardinal
open scoped Topology

namespace NonMRR

/-- The sum of the first `n` terms. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, a i

theorem hasSum_conditional_iff {a : ℕ → ℝ} {s : ℝ} :
    HasSum a s (SummationFilter.conditional ℕ) ↔
      Tendsto (partialSum a) atTop (𝓝 s) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

/-- A real series together with its unique natural sum and conditional convergence proofs. -/
structure ConditionalSeries where
  term : ℕ → ℝ
  sum : ℝ
  converges : HasSum term sum (SummationFilter.conditional ℕ)
  not_absolute : ¬ Summable (fun n ↦ |term n|)

/-- A permutation rearranges a series when it fails to preserve its natural sum. -/
def Rearranges (a : ConditionalSeries) (π : Equiv.Perm ℕ) : Prop :=
  ¬ HasSum (a.term ∘ π) a.sum (SummationFilter.conditional ℕ)

/-- A family which rearranges every conditionally convergent real series. -/
def IsRearranging (s : Set (Equiv.Perm ℕ)) : Prop :=
  ∀ a : ConditionalSeries, ∃ π ∈ s, Rearranges a π

/-- The rearrangement number, with the cardinal-minimum definition in the manuscript. -/
noncomputable def rr : Cardinal :=
  sInf {κ | ∃ s : Set (Equiv.Perm ℕ), IsRearranging s ∧ #s = κ}

theorem rr_le_cardinal {s : Set (Equiv.Perm ℕ)} (hs : IsRearranging s) : rr ≤ #s :=
  csInf_le' ⟨s, hs, rfl⟩

/-- A common preserved series witnesses that a family is not rearranging. -/
theorem not_isRearranging_of_preserves {s : Set (Equiv.Perm ℕ)} (a : ConditionalSeries)
    (h : ∀ π ∈ s, HasSum (a.term ∘ π) a.sum (SummationFilter.conditional ℕ)) :
    ¬ IsRearranging s := by
  intro hs
  obtain ⟨π, hπ, hbad⟩ := hs a
  exact hbad (h π hπ)

/-- A witness whose natural and rearranged sums are zero has the required semantics. -/
theorem not_isRearranging_of_zero_witness {s : Set (Equiv.Perm ℕ)} {a : ℕ → ℝ}
    (ha : Tendsto (partialSum a) atTop (𝓝 0))
    (hab : ¬ Summable (fun n ↦ |a n|))
    (hπ : ∀ π ∈ s, Tendsto (partialSum (a ∘ π)) atTop (𝓝 0)) :
    ¬ IsRearranging s := by
  let series : ConditionalSeries := ⟨a, 0, hasSum_conditional_iff.mpr ha, hab⟩
  apply not_isRearranging_of_preserves series
  intro π hmem
  exact hasSum_conditional_iff.mpr (hπ π hmem)

/-- The alternating harmonic series supplies an actual challenge. -/
theorem conditionalSeries_nonempty : Nonempty ConditionalSeries := by
  have hanti : Antitone (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  obtain ⟨s, hs⟩ := hanti.tendsto_alternating_series_of_tendsto_zero
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨⟨(fun n ↦ (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))), s,
    hasSum_conditional_iff.mpr hs, ?_⟩⟩
  have heq (n : ℕ) : |(-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))| =
      1 / ((n : ℝ) + 1) := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_of_nonneg (by positivity)
  simp only [heq]
  intro hab
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hab

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
