/-
Copyright (c) 2026 pannous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pannous
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Probability.ConditionalProbability

/-!
  Proof: hitting any specific point on a 2-D disc has probability zero.
  ======================================================================

  When a dart lands uniformly at random inside a disc, the probability
  of hitting any single exact point z ∈ ℂ is 0.

  Strategy:
    1. Every singleton {z} ⊂ ℂ has area 0:
         {z} = closedBall z 0  →  area = π · 0² = 0
    2. The conditional probability of an event of area 0 is 0.

  This mirrors the 1-D result (ℝ) but for the complex plane (ℝ²).
-/

open MeasureTheory Set Metric ProbabilityTheory

-- ─── 1. Every point in ℂ has area zero ───────────────────────────────────────
-- {z} = closedBall z 0, and area(closedBall z r) = π r², so area({z}) = π·0² = 0.

theorem complex_singleton_area_zero (z : ℂ) : volume ({z} : Set ℂ) = 0 := by
  rw [← closedBall_zero]          -- {z} = closedBall z 0
  simp  -- π · 0² = 0

-- ─── 2. ℂ has no atoms ────────────────────────────────────────────────────────
-- Registering the NoAtoms typeclass lets us use `measure_singleton` everywhere.

/-- The Lebesgue measure on `ℂ` has no atoms: every singleton has area zero. -/
instance complexNoAtoms : NoAtoms (volume : Measure ℂ) where
  measure_singleton := complex_singleton_area_zero

-- ─── 3. Dart theorem: probability of hitting any single point is 0 ────────────
-- Conditional probability: P({z} | dart lands in disc) = 0.
-- The conditional measure satisfies:
--   (volume[|D]) {z} = (volume D)⁻¹ · volume(D ∩ {z})
-- and volume(D ∩ {z}) ≤ volume {z} = 0.

theorem dart_hits_point_prob_zero (centre : ℂ) (R : ℝ) (z : ℂ) :
    (volume[|ball centre R]) ({z} : Set ℂ) = 0 := by
  rw [ProbabilityTheory.cond_apply' (measurableSet_singleton z) volume]
  exact mul_eq_zero_of_right _
    (measure_mono_null Set.inter_subset_right (complex_singleton_area_zero z))

-- ─── 4. Any finite set of target points also has probability 0 ───────────────

theorem dart_hits_finite_set_prob_zero (centre : ℂ) (R : ℝ)
    (s : Set ℂ) (hs : s.Finite) :
    (volume[|ball centre R]) s = 0 := by
  rw [ProbabilityTheory.cond_apply' hs.measurableSet volume]
  exact mul_eq_zero_of_right _
    (measure_mono_null Set.inter_subset_right (hs.measure_zero volume))

-- ─── 5. Concrete examples ────────────────────────────────────────────────────

-- The origin inside the unit disc has probability 0.
example : (volume[|ball (0:ℂ) 1]) ({0} : Set ℂ) = 0 :=
  dart_hits_point_prob_zero 0 1 0

-- Any specific point (here: ½ + ⅓i) has probability 0.
example : (volume[|ball (0:ℂ) 1]) ({(1/2 : ℂ) + Complex.I * (1/3)} : Set ℂ) = 0 :=
  dart_hits_point_prob_zero 0 1 _

-- A finite target set {0, 1, i} has probability 0.
example : (volume[|ball (0:ℂ) 1]) ({0, 1, Complex.I} : Set ℂ) = 0 :=
  dart_hits_finite_set_prob_zero 0 1 _ (toFinite _)

-- ─── 6. Geometric recap ──────────────────────────────────────────────────────
-- Disc area = πR² > 0, singleton area = 0.
-- P({z} | disc) = 0 / (πR²) = 0.
example (R : ℝ) :
    volume (ball (0:ℂ) R) = ENNReal.ofReal R ^ 2 * NNReal.pi := by
  simp [Complex.volume_ball]
