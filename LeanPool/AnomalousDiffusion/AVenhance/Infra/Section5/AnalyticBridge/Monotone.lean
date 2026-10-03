/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FourierDecay

/-! Monotonicity of the composed-analyticity hypothesis of `l.flow.averages`: a larger amplitude
and a smaller radius weaken it. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.AnalyticBridge

theorem hasCoordinateAnalyticL1Bounds_mono {d : ℕ} {f : Vec d → ℂ} {Cf r Cf' r' : ℝ}
    (h : Infra.Ergodic.HasCoordinateAnalyticL1Bounds f Cf r) (hC : Cf ≤ Cf') (hC' : 0 ≤ Cf')
    (hr' : 0 < r') (hr : r' ≤ r) :
    Infra.Ergodic.HasCoordinateAnalyticL1Bounds f Cf' r' := by
  intro i n hn
  have hr0 : 0 < r := lt_of_lt_of_le hr' hr
  refine (h i n hn).trans ?_
  have hfac : (0 : ℝ) ≤ n.factorial := by positivity
  calc Cf * (n.factorial : ℝ) / r ^ n ≤ Cf' * (n.factorial : ℝ) / r ^ n := by
        gcongr
    _ ≤ Cf' * (n.factorial : ℝ) / r' ^ n := by
        apply div_le_div_of_nonneg_left (mul_nonneg hC' hfac) (pow_pos hr' n)
        exact pow_le_pow_left₀ hr'.le hr n

end AVenhance.Infra.Section5.AnalyticBridge
