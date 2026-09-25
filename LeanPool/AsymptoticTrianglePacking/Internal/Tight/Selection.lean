/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — generic selection tools

Two elementary tools used to extract a single good outcome of a nibble round.

* `exists_notMem_of_measureReal_add_lt_one` — if two events have total probability `< 1`, some
  outcome avoids both.  (This is what replaces the union bound over vertices: the two events are
  "too many bad vertices" and "too little coverage", and each is controlled by a Markov inequality.)
* `card_filter_mul_le_sum` — the counting form of Markov's inequality: at most `(∑ᵢ gᵢ)/t` indices
  satisfy `t ≤ gᵢ`, for a nonnegative `g`.
* `measureReal_ge_le_integral_div` — the real-valued Markov inequality.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ProbabilityTheory

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- If two events have total probability `< 1`, some outcome avoids both. -/
theorem exists_notMem_of_measureReal_add_lt_one {A B : Set Ω}
    (h : (ℙ : Measure Ω).real A + (ℙ : Measure Ω).real B < 1) :
    ∃ ω : Ω, ω ∉ A ∧ ω ∉ B := by
  by_contra hcon
  push Not at hcon
  have huniv : A ∪ B = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hωA : ω ∈ A
    · exact Or.inl hωA
    · exact Or.inr (hcon ω hωA)
  have h1 : (ℙ : Measure Ω).real (A ∪ B) = 1 := by
    rw [huniv]; simp
  have h2 : (ℙ : Measure Ω).real (A ∪ B) ≤ (ℙ : Measure Ω).real A + (ℙ : Measure Ω).real B :=
    measureReal_union_le A B
  linarith only [h, h1, h2]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **Markov's inequality**, real-valued form. -/
theorem measureReal_ge_le_integral_div {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    (hint : Integrable f (ℙ : Measure Ω)) {c : ℝ} (hc : 0 < c) :
    (ℙ : Measure Ω).real {ω | c ≤ f ω} ≤ (∫ ω, f ω ∂(ℙ : Measure Ω)) / c := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf) hint c
  rw [le_div_iff₀ hc, mul_comm]
  exact h

/-- **Counting Markov.**  At most `(∑ᵢ gᵢ)/t` indices satisfy `t ≤ gᵢ`. -/
theorem card_filter_mul_le_sum {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (t : ℝ) :
    ((Finset.univ.filter (fun i => t ≤ g i)).card : ℝ) * t ≤ ∑ i, g i := by
  classical
  calc ((Finset.univ.filter (fun i => t ≤ g i)).card : ℝ) * t
      = ∑ _i ∈ Finset.univ.filter (fun i => t ≤ g i), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => t ≤ g i), g i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => hg i)

end LeanPool.AsymptoticTrianglePacking.Internal
