/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic of the residual-order ledger

The candidate manuscript, Proposition 10.3, assigns real
exponents to analytic estimates. This file checks the arithmetic of those
assignments, conditional on the estimates being valid. It does not define the
analytic classes, construct a correction, or prove an estimate for a PDE.

The manuscript fixes `κ = 10⁻⁵` in §8.1 and again in §10.2. The results below
hold uniformly for `0 ≤ κ ≤ 10⁻⁵` and `σ ≥ 1/5`. Fractions are exact rationals
in the real numbers; no floating-point calculation is used.
-/

namespace NavierStokes.ExponentLedger

noncomputable section

/-- The good-wave residual exponent `B = 1/2 + σ`. -/
def waveExponent (σ : ℝ) : ℝ := 1 / 2 + σ

/-- The mean and defect target exponent `C = 1 + σ`. -/
def meanExponent (σ : ℝ) : ℝ := 1 + σ

/-- The intermediate exponent `H₁ = C - 2κ`. -/
def meanUpdateExponent (σ κ : ℝ) : ℝ := meanExponent σ - 2 * κ

/-- Minimum of the four listed gains for the particular wave correction. -/
def particularGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 3 * κ) (1 / 2 - κ))
    (waveExponent σ - κ)) (2 / 5)

/-- Minimum of the four listed gains for the signed wave correction. -/
def signedGain (σ κ : ℝ) : ℝ :=
  min (min (min (1 / 2 - 4 * κ) (2 / 5 - κ))
    (1 / 2 - 2 * κ)) (waveExponent σ - 3 * κ)

/-- The five distinct gains listed for the signed bar residual, after divergence.
The subtracted bump repeats the fourth bound and so contributes no new minimum. -/
def signedBarGain (σ κ : ℝ) : ℝ :=
  min (min (min (min (9 / 50 - 2 * κ) (1 / 2 - 3 * κ))
    (σ - 3 * κ)) (1 - κ)) (1 - 2 * κ)

theorem mean_eq_wave_add_half (σ : ℝ) :
    meanExponent σ = waveExponent σ + 1 / 2 := by
  unfold meanExponent waveExponent
  ring

theorem wave_at_least_seven_tenths {σ : ℝ} (hσ : 1 / 5 ≤ σ) :
    7 / 10 ≤ waveExponent σ := by
  unfold waveExponent
  linarith

theorem mean_at_least_six_fifths {σ : ℝ} (hσ : 1 / 5 ≤ σ) :
    6 / 5 ≤ meanExponent σ := by
  unfold meanExponent
  linarith

theorem wave_increment (σ : ℝ) :
    waveExponent (σ + 1 / 10) = waveExponent σ + 1 / 10 := by
  unfold waveExponent
  ring

theorem mean_increment (σ : ℝ) :
    meanExponent (σ + 1 / 10) = meanExponent σ + 1 / 10 := by
  unfold meanExponent
  ring

theorem parameter_lower_bound_preserved {σ : ℝ} (hσ : 1 / 5 ≤ σ) :
    1 / 5 ≤ σ + 1 / 10 := by
  linarith

/-! ## Step 1: particular correction -/

/-- The displayed lower bound is in fact equality for the stated parameter range. -/
theorem particular_gain_eq {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    particularGain σ κ = 2 / 5 := by
  unfold particularGain waveExponent
  apply le_antisymm (min_le_right _ _)
  simp only [le_min_iff]
  exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, le_refl _⟩

theorem particular_linear_margin {σ κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    waveExponent σ + 2 / 5 ≤ waveExponent σ + 1 / 2 - 3 * κ := by
  linarith

theorem particular_old_wave_margin {σ κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    waveExponent σ + 2 / 5 ≤ waveExponent σ + 1 / 2 - κ := by
  linarith

theorem particular_square_margin {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    waveExponent σ + 2 / 5 ≤ 2 * waveExponent σ - κ := by
  unfold waveExponent
  linarith

theorem particular_gain_exceeds_tenth {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    waveExponent (σ + 1 / 10) < waveExponent σ + particularGain σ κ := by
  rw [particular_gain_eq hσ hκ, wave_increment]
  linarith

theorem particular_tensor_exponent (σ : ℝ) :
    waveExponent σ + 1 / 2 = meanExponent σ := by
  exact (mean_eq_wave_add_half σ).symm

/-! ## Step 2: signed correction -/

theorem signed_gain_eq {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    signedGain σ κ = 2 / 5 - κ := by
  unfold signedGain waveExponent
  apply le_antisymm
  · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  · simp only [le_min_iff]
    exact ⟨⟨⟨by linarith, le_refl _⟩, by linarith⟩, by linarith⟩

theorem signed_gain_exceeds_tenth {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    waveExponent (σ + 1 / 10) < waveExponent σ + signedGain σ κ := by
  rw [signed_gain_eq hσ hκ, wave_increment]
  linarith

theorem signed_old_difference_identity (σ κ : ℝ) :
    waveExponent σ + 17 / 25 - κ = meanExponent σ + 9 / 50 - κ := by
  unfold waveExponent meanExponent
  ring

theorem signed_square_identity (σ κ : ℝ) :
    2 * waveExponent σ - 2 * κ = meanExponent σ + σ - 2 * κ := by
  unfold waveExponent meanExponent
  ring

theorem signed_old_difference_after_divergence (σ κ : ℝ) :
    (waveExponent σ + 17 / 25 - κ) - κ =
      meanExponent σ + (9 / 50 - 2 * κ) := by
  unfold waveExponent meanExponent
  ring

theorem signed_curl_after_divergence (σ κ : ℝ) :
    (meanExponent σ + 1 / 2 - 2 * κ) - κ =
      meanExponent σ + (1 / 2 - 3 * κ) := by
  ring

theorem signed_square_after_divergence (σ κ : ℝ) :
    (2 * waveExponent σ - 2 * κ) - κ =
      meanExponent σ + (σ - 3 * κ) := by
  unfold waveExponent meanExponent
  ring

theorem old_difference_bar_margin {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    17 / 100 < 9 / 50 - 2 * κ := by
  linarith

theorem curl_bar_margin {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    17 / 100 < 1 / 2 - 3 * κ := by
  linarith

theorem square_bar_margin {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    17 / 100 < σ - 3 * κ := by
  linarith

theorem axial_bar_margin {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    17 / 100 < 1 - κ := by
  linarith

theorem pressure_bar_margin {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    17 / 100 < 1 - 2 * κ := by
  linarith

/-- Every listed contribution exceeds the claimed `.17` bar-residual gain. -/
theorem signed_bar_gain_exceeds_seventeen_hundredths {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    17 / 100 < signedBarGain σ κ := by
  unfold signedBarGain
  simp only [lt_min_iff]
  exact ⟨⟨⟨⟨old_difference_bar_margin hκ, curl_bar_margin hκ⟩,
    square_bar_margin hσ hκ⟩, axial_bar_margin hκ⟩, pressure_bar_margin hκ⟩

/-! ## Steps 3 and 4: mean and defect updates -/

theorem mean_update_wave_identity (σ κ : ℝ) :
    meanUpdateExponent σ κ = waveExponent σ + 1 / 2 - 2 * κ := by
  unfold meanUpdateExponent
  rw [mean_eq_wave_add_half]

theorem mean_update_wave_margin {σ κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    waveExponent (σ + 1 / 10) < meanUpdateExponent σ κ := by
  rw [mean_update_wave_identity, wave_increment]
  linarith

theorem temporal_mean_gain_identity (σ κ : ℝ) :
    meanUpdateExponent σ κ + 1 - 2 * κ = meanExponent σ + (1 - 4 * κ) := by
  unfold meanUpdateExponent
  ring

theorem completed_mean_gain_eq {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    min (17 / 100) (1 - 4 * κ) = 17 / 100 := by
  apply min_eq_left
  linarith

theorem completed_mean_margin {σ κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    meanExponent (σ + 1 / 10) <
      meanExponent σ + min (17 / 100) (1 - 4 * κ) := by
  rw [completed_mean_gain_eq hκ, mean_increment]
  linarith

theorem rank_defect_gain_identity (σ κ : ℝ) :
    meanUpdateExponent σ κ + 9 / 10 - 2 * κ =
      meanExponent σ + 9 / 10 - 4 * κ := by
  unfold meanUpdateExponent
  ring

theorem completed_defect_margin {σ κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    meanExponent (σ + 1 / 10) < meanExponent σ + 9 / 10 - 4 * κ := by
  rw [mean_increment]
  linarith

/-! ## Cumulative exponent bounds -/

theorem signed_increment_lower_bound {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκ : κ ≤ 1 / 100000) :
    69999 / 100000 ≤ waveExponent σ - κ := by
  unfold waveExponent
  linarith

theorem signed_increment_above_cumulative_difference {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    17 / 25 < waveExponent σ - κ := by
  have h := signed_increment_lower_bound hσ hκ
  linarith

theorem particular_increment_above_cumulative_difference {σ : ℝ}
    (hσ : 1 / 5 ≤ σ) :
    17 / 25 < waveExponent σ := by
  have h := wave_at_least_seven_tenths hσ
  linarith

theorem mean_increment_above_cumulative_mean {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    9 / 10 < meanUpdateExponent σ κ := by
  unfold meanUpdateExponent meanExponent
  linarith

theorem radial_increment_above_cumulative_radial {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    19 / 10 < meanUpdateExponent σ κ + 1 := by
  have h := mean_increment_above_cumulative_mean hσ hκ
  linarith

theorem particular_pressure_above_cumulative_mean {σ : ℝ}
    (hσ : 1 / 5 ≤ σ) :
    9 / 10 < waveExponent σ + 1 / 2 := by
  have h := wave_at_least_seven_tenths hσ
  linarith

theorem signed_pressure_above_cumulative_mean {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : κ ≤ 1 / 100000) :
    9 / 10 < waveExponent σ - κ + 1 / 2 := by
  have h := signed_increment_lower_bound hσ hκ
  linarith

/-! ## Exact fixed choice and quantifier bookkeeping -/

theorem manuscript_kappa_admissible :
    (0 : ℝ) ≤ 1 / 100000 ∧ (1 / 100000 : ℝ) ≤ 1 / 100000 := by
  norm_num

/-- A stricter `κ < 10⁻⁶` also suffices, but is not the manuscript's choice. -/
theorem smaller_kappa_admissible {κ : ℝ} (hκ : κ < 1 / 1000000) :
    κ ≤ 1 / 100000 := by
  linarith

/-- The most restrictive `.17` bar margin has this exact threshold. -/
theorem old_difference_bar_margin_iff (κ : ℝ) :
    17 / 100 < 9 / 50 - 2 * κ ↔ κ < 1 / 200 := by
  constructor <;> intro h <;> linarith

/-- Iterated accuracy parameters; this does not assert existence of the iterates. -/
def stageParameter (n : ℕ) : ℝ := 1 / 5 + (n : ℝ) / 10

theorem stage_parameter_zero : stageParameter 0 = 1 / 5 := by
  norm_num [stageParameter]

theorem stage_parameter_succ (n : ℕ) :
    stageParameter (n + 1) = stageParameter n + 1 / 10 := by
  unfold stageParameter
  push_cast
  ring

theorem stage_parameter_admissible (n : ℕ) :
    1 / 5 ≤ stageParameter n := by
  unfold stageParameter
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The same fixed κ works for the numerical comparisons at every finite stage. -/
theorem all_stage_arithmetic (n : ℕ) {κ : ℝ} (hκ : κ ≤ 1 / 100000) :
    waveExponent (stageParameter (n + 1)) <
        waveExponent (stageParameter n) + particularGain (stageParameter n) κ ∧
    waveExponent (stageParameter (n + 1)) <
        waveExponent (stageParameter n) + signedGain (stageParameter n) κ ∧
    waveExponent (stageParameter (n + 1)) < meanUpdateExponent (stageParameter n) κ ∧
    meanExponent (stageParameter (n + 1)) <
        meanExponent (stageParameter n) + min (17 / 100) (1 - 4 * κ) ∧
    meanExponent (stageParameter (n + 1)) <
        meanExponent (stageParameter n) + 9 / 10 - 4 * κ := by
  rw [stage_parameter_succ]
  exact ⟨particular_gain_exceeds_tenth (stage_parameter_admissible n) hκ,
    signed_gain_exceeds_tenth (stage_parameter_admissible n) hκ,
    mean_update_wave_margin hκ, completed_mean_margin hκ, completed_defect_margin hκ⟩

end

end NavierStokes.ExponentLedger
