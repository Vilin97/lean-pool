/-
Copyright (c) 2026 pannous. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pannous
-/
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
  High School Probability Examples in Lean 4 / Mathlib
  =====================================================
  Three classic examples:
    1. Fair die  — P(rolling a 6) = 1/6
    2. Fair coin — P(heads)       = 1/2
    3. Dart board (geometric probability) — P(bullseye) = 1/4
-/

open MeasureTheory ProbabilityTheory PMF ENNReal

-- ─── 1. Fair Die ─────────────────────────────────────────────────────────────
-- Model a 6-sided die as a uniform distribution over Fin 6.

/-- A fair six-sided die, modelled as the uniform distribution over `Fin 6`. -/
noncomputable def fairDie : PMF (Fin 6) := uniformOfFintype (Fin 6)

-- P(rolling any specific face) = 1/6
theorem fairDie_prob (i : Fin 6) : fairDie i = (6 : ℝ≥0∞)⁻¹ := by
  simp [fairDie, uniformOfFintype_apply, Fintype.card_fin]

-- All faces together sum to 1
example : ∑' i : Fin 6, fairDie i = 1 := fairDie.tsum_coe

-- ─── 2. Fair Coin ─────────────────────────────────────────────────────────────
-- Model a coin flip as a uniform distribution over Bool.

/-- A fair coin, modelled as the uniform distribution over `Bool`. -/
noncomputable def fairCoin : PMF Bool := uniformOfFintype Bool

-- P(heads) = P(tails) = 1/2
theorem fairCoin_heads : fairCoin true  = (2 : ℝ≥0∞)⁻¹ := by
  simp [fairCoin, uniformOfFintype_apply, Fintype.card_bool]

theorem fairCoin_tails : fairCoin false = (2 : ℝ≥0∞)⁻¹ := by
  simp [fairCoin, uniformOfFintype_apply, Fintype.card_bool]

-- ─── 3. Dart Board — Geometric Probability ────────────────────────────────────
-- A dart lands at a random point inside a large circle of radius 2 (area 4π).
-- The bullseye is the inner circle of radius 1 (area π).
-- P(bullseye) = area(r=1) / area(r=2) = π / 4π = 1/4.
--
-- We model the plane as ℂ (= ℝ²) with the Lebesgue measure.
-- Key lemma: volume (Metric.ball a r : Set ℂ) = (ofReal r)² · ↑NNReal.pi

-- Area of bullseye  (r = 1)  = π
example : volume (Metric.ball (0:ℂ) 1) = NNReal.pi := by
  simp [Complex.volume_ball]

-- Area of dartboard (r = 2)  = 4π
example : volume (Metric.ball (0:ℂ) 2) = 4 * NNReal.pi := by
  simp only [Complex.volume_ball, ENNReal.ofReal_ofNat, show (2:ℝ≥0∞)^2 = 4 from by norm_num]

-- P(bullseye) = 1/4
theorem dart_probability :
    volume (Metric.ball (0:ℂ) 1) / volume (Metric.ball (0:ℂ) 2) = (4 : ℝ≥0∞)⁻¹ := by
  simp only [Complex.volume_ball, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_pow, one_mul]
  -- goal: ↑NNReal.pi / ((2:ℝ≥0∞)^2 * ↑NNReal.pi) = 4⁻¹
  have hpi0 : (NNReal.pi : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne'
  have hpiT : (NNReal.pi : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  norm_num
  -- goal: ↑NNReal.pi / (4 * ↑NNReal.pi) = 4⁻¹
  -- Proof: a / (b * a) = b⁻¹   (rearrange using mul_inv and inv_mul_cancel)
  rw [ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl (by norm_num : (4:ℝ≥0∞) ≠ 0)) (Or.inr hpi0),
      mul_assoc, ENNReal.inv_mul_cancel hpi0 hpiT, mul_one]
