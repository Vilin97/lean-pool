/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleLevelSet

/-!
# Parameters for endpoint counterexamples

The paper's amplitude and exponent shifts satisfy the eventual positivity and scale-window
conditions needed for the modular counterexamples. The resulting height is expressed in terms of
these parameters.
-/

open Filter MeasureTheory Set

namespace QuadraticCarleson


/- The amplitude and logarithmic shift used in the paper's counterexample. -/
/-- The counterexample amplitude `log N / 2^40` used in the paper. -/
noncomputable def paperAmplitude (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / (2 : ℝ) ^ 40

/-- The base-two logarithm of the paper's counterexample amplitude. -/
noncomputable def paperExponentShift (N : ℕ) : ℝ :=
  Real.logb 2 (paperAmplitude N)

theorem paperAmplitude_pos_of_one_le {N : ℕ} (hN : 1 ≤ paperAmplitude N) :
    0 < paperAmplitude N := lt_of_lt_of_le zero_lt_one hN

theorem eventually_paperAmplitude_ge_one :
    ∀ᶠ N : ℕ in atTop, 1 ≤ paperAmplitude N := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ 40 := by positivity
  have hlog : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ 40 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlog] with N hN
  unfold paperAmplitude
  exact (le_div_iff₀ hden).mpr (by simpa [one_mul] using hN)

theorem eventually_paperAmplitude_pos :
    ∀ᶠ N : ℕ in atTop, 0 < paperAmplitude N := by
  filter_upwards [eventually_paperAmplitude_ge_one] with N hN
  exact paperAmplitude_pos_of_one_le hN

theorem paperExponentShift_rpow_eq_amplitude {N : ℕ}
    (hN : 0 < paperAmplitude N) :
    (2 : ℝ) ^ paperExponentShift N = paperAmplitude N := by
  unfold paperExponentShift
  exact Real.rpow_logb (by norm_num) (by norm_num) hN

theorem paperExponentShift_nonneg_of_amplitude_ge_one {N : ℕ}
    (hN : 1 ≤ paperAmplitude N) :
    0 ≤ paperExponentShift N := by
  unfold paperExponentShift
  exact Real.logb_nonneg (by norm_num) hN

theorem eventually_paperExponentShift_nonneg :
    ∀ᶠ N : ℕ in atTop, 0 ≤ paperExponentShift N := by
  filter_upwards [eventually_paperAmplitude_ge_one] with N hN
  exact paperExponentShift_nonneg_of_amplitude_ge_one hN

theorem eventually_paper_window_start :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ 3 * (N : ℝ) ^ 2 / 5 + paperExponentShift N := by
  filter_upwards [eventually_ge_atTop 2, eventually_paperExponentShift_nonneg]
    with N hN hL
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N : ℝ) - 2)]

/-- The fixed small constant used for the final counterexample level. -/
noncomputable def negativeEndpointHeightConstant : ℝ := 1 / 8

theorem negativeEndpointHeightConstant_pos :
    0 < negativeEndpointHeightConstant := by
  unfold negativeEndpointHeightConstant
  norm_num

/-- The negative-endpoint counterexample threshold, equal to `log N / (8 * N)`. -/
noncomputable def negativeEndpointCounterexampleHeight (N : ℕ) : ℝ :=
  counterexampleHeight negativeEndpointHeightConstant N

theorem negativeEndpointCounterexampleHeight_eq (N : ℕ) :
    negativeEndpointCounterexampleHeight N =
      Real.log (N : ℝ) / (8 * (N : ℝ)) := by
  unfold negativeEndpointCounterexampleHeight counterexampleHeight
  unfold negativeEndpointHeightConstant
  ring

theorem negativeEndpointCounterexampleHeight_eq_const_mul (N : ℕ) :
    negativeEndpointCounterexampleHeight N =
      (1 / 8 : ℝ) * (Real.log (N : ℝ) / (N : ℝ)) := by
  unfold negativeEndpointCounterexampleHeight counterexampleHeight
  unfold negativeEndpointHeightConstant
  ring

theorem eventually_negativeEndpointCounterexampleHeight_pos :
    ∀ᶠ N : ℕ in atTop, 0 < negativeEndpointCounterexampleHeight N := by
  simpa only [negativeEndpointCounterexampleHeight] using
    (eventually_counterexampleHeight_pos negativeEndpointHeightConstant_pos)

end QuadraticCarleson
