/-
Copyright (c) 2026 pannous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pannous
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac

/-!
  Proof: picking a random real number has probability zero.
  =========================================================

  For any continuous probability distribution on ℝ (or any space with no
  "atoms"), the probability of landing on any *specific* value is exactly 0.

  Key concept: `NoAtoms μ` — a typeclass asserting μ {x} = 0 for all x.
  Lebesgue measure on ℝ (and ℝⁿ) is a `NoAtoms` instance.

  This explains why "the probability of picking exactly π" is 0, even though
  such an event is not impossible — it just has measure (probability) zero.
-/

open MeasureTheory Set

-- ─── 1. The `NoAtoms` typeclass ───────────────────────────────────────────────
-- A measure μ has no atoms if every singleton set has measure 0.

-- ─── 2. Lebesgue measure on ℝ has no atoms ───────────────────────────────────
-- Mathlib provides this instance automatically.

-- Direct corollary: every singleton in ℝ has Lebesgue measure zero.
theorem real_singleton_prob_zero (x : ℝ) : volume ({x} : Set ℝ) = 0 :=
  measure_singleton x

-- ─── 3. Generalisation: any NoAtoms probability measure ──────────────────────
-- Works for the uniform distribution on [0,1], Normal, Exponential, etc.
theorem continuous_measure_singleton_zero
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] (x : ℝ) :
    μ {x} = 0 :=
  measure_singleton x

-- ─── 4. Finite sets also have probability 0 ──────────────────────────────────
-- The probability of picking any element of a finite list is also 0.
theorem finite_set_prob_zero
    (μ : Measure ℝ) [NoAtoms μ] (s : Set ℝ) (hs : s.Finite) :
    μ s = 0 :=
  hs.measure_zero μ

-- Example: {0, 1, π} has measure 0.
example : volume ({0, 1, Real.pi} : Set ℝ) = 0 :=
  (toFinite _).measure_zero volume

-- ─── 5. Even countably infinite sets have probability 0 ──────────────────────
-- ℕ ↪ ℝ is countable, so its image has Lebesgue measure 0.
theorem naturals_prob_zero : volume (Set.range ((↑) : ℕ → ℝ)) = 0 :=
  (Set.countable_range _).measure_zero volume

-- Likewise for ℚ ↪ ℝ (rationals are countable, so measure-zero in ℝ).
theorem rationals_prob_zero : volume (Set.range ((↑) : ℚ → ℝ)) = 0 :=
  Set.countable_range _ |>.measure_zero volume

-- ─── 6. Almost-surely irrational ─────────────────────────────────────────────
-- A random real number is almost surely NOT a rational.
theorem ae_irrational : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Set.range ((↑) : ℚ → ℝ) := by
  rw [ae_iff]
  -- goal: volume {x | ¬ x ∉ range (↑)} = 0, i.e. volume (range ↑ : Set ℝ) = 0
  simp only [not_not]
  exact rationals_prob_zero

-- ─── 7. Contrast: discrete measures DO have atoms ────────────────────────────
-- For a finite or countable probability space, P({x}) can be positive.
-- Example: Dirac measure δ₀ gives probability 1 to the single point {0}.
example : Measure.dirac (0 : ℝ) {0} = 1 := by simp

-- The Dirac measure is NOT NoAtoms — it has all its mass at one atom.
-- That's why discreteness (finiteness of the space) matters:
-- only uncountably infinite spaces with "spread-out" measures have NoAtoms.
