/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bennett / Bernstein sub-gamma concentration

Variance-sensitive (Bernstein/Freedman-style) concentration, which Mathlib currently lacks:
Mathlib has the sub-Gaussian MGF (`HasSubgaussianMGF`, the base of Azuma/Hoeffding) but not the
sub-gamma / Bernstein one. When the conditional variance `V` is much smaller than the squared range
`b²`, the sub-Gaussian tail `exp(−ε²/2b²)` is far too weak; the correct bound is the variance-based
`exp(−ε²/(2(V+cε)))`.

This file develops that from scratch, Mathlib-only:

* `Contrib.Bennett.HasSubgammaMGF X V c μ` — the sub-gamma MGF bound `mgf ≤ exp(V t²/(2(1−ct)))`
  (the variance-based analogue of `HasSubgaussianMGF`, recovered at `c = 0`).
* `Contrib.Bennett.subgamma_tail` — the Bernstein tail `P(X ≥ ε) ≤ exp(−ε²/(2(V+cε)))`, via the
  Chernoff bound at the optimal parameter `t* = ε/(V+cε)`.
* `Contrib.Bennett.exp_mul_le_bennett_quadratic` — the pointwise quadratic majorant
  `exp(tx) ≤ 1 + tx + x²(exp(tb)−1−tb)/b²` for `x ≤ b`.
* `Contrib.Bennett.exp_sub_one_sub_le_bernstein` — `exp(u) − 1 − u ≤ u²/(2(1−u/3))` for `0 ≤ u < 3`.
* `Contrib.Bennett.mgf_le_bennett` — Bennett's MGF inequality for a centered,
  upper-bounded variable.
* `Contrib.Bennett.hasSubgammaMGF_of_bounded_above` — a centered variable bounded above by `b` with
  second moment `≤ V` is sub-gamma with variance factor `V` and scale `b/3`.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory Real

namespace Contrib.Bennett

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sub-gamma MGF bound.** `X` has a sub-gamma MGF with variance factor `V` and scale `c` if
`mgf X μ t ≤ exp(V t²/(2(1−ct)))` for `0 ≤ t` and `ct < 1`. This is the variance-based
(Bernstein) analogue of `HasSubgaussianMGF`; when `c = 0`, every nonnegative parameter is in the
effective domain. It is the martingale-summable object underlying Freedman's inequality. -/
def HasSubgammaMGF (X : Ω → ℝ) (V c : ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t → c * t < 1 → mgf X μ t ≤ Real.exp (V * t ^ 2 / (2 * (1 - c * t)))

/-- **Bernstein tail from the sub-gamma MGF.** If `X` has a sub-gamma MGF with `V > 0`,
`c > 0`, then
`P(X ≥ ε) ≤ exp(−ε²/(2(V + cε)))`. The optimal Chernoff parameter is `t* = ε/(V+cε)`, at which the
exponent is exactly `−ε²/(2(V+cε))`. -/
theorem subgamma_tail [IsFiniteMeasure μ] {X : Ω → ℝ} {V c ε : ℝ}
    (h : HasSubgammaMGF X V c μ) (hV : 0 < V) (hc : 0 < c) (hε : 0 ≤ ε)
    (hint : Integrable (fun ω => Real.exp ((ε / (V + c * ε)) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * (V + c * ε))) := by
  have hVce : 0 < V + c * ε := by positivity
  set t : ℝ := ε / (V + c * ε) with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htc : t * c < 1 := by
    rw [ht, div_mul_eq_mul_div, div_lt_one hVce]
    nlinarith [hV, mul_nonneg hc.le hε]
  -- 1 - c*t = V/(V+cε) > 0
  have hden : (1 : ℝ) - c * t = V / (V + c * ε) := by
    rw [ht]; field_simp [hVce.ne']; ring
  have hden_pos : 0 < 1 - c * t := by rw [hden]; positivity
  -- Chernoff + sub-gamma MGF
  have hcher := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t := t) ε ht0 hint
  have hmgf := h t ht0 (by simpa [mul_comm] using htc)
  have hstep : μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-t * ε) * Real.exp (V * t ^ 2 / (2 * (1 - c * t))) :=
    le_trans hcher (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _))
  rw [← Real.exp_add] at hstep
  refine le_trans hstep (le_of_eq ?_)
  congr 1
  -- exponent: -t*ε + V t²/(2(1-ct)) = -ε²/(2(V+cε))
  rw [ht, hden]
  field_simp
  ring

/-- The pointwise quadratic majorant underlying Bennett's MGF inequality. -/
theorem exp_mul_le_bennett_quadratic {t b x : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hx : x ≤ b) :
    Real.exp (t * x) ≤
      1 + t * x + x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
  by_cases hx_nonpos : x ≤ 0
  · -- Case x ≤ 0: use convexity argument
    have htx_nonpos : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hx_nonpos
    -- Key: exp(tb) ≥ 1 + tb + (tb)²/2 for tb ≥ 0 (Taylor)
    have hbpos : 0 ≤ t * b := mul_nonneg ht (le_of_lt hb)
    -- Use that exp is convex and the second derivative bound
    -- Key lemma: exp(u) ≥ 1 + u + u²/2 for u ≥ 0
    have exp_lower_bound : ∀ u : ℝ, 0 ≤ u → Real.exp u ≥ 1 + u + u ^ 2 / 2 := by
      intro u hu
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
      -- Note: (n.factorial : ℝ)⁻¹ • u ^ n = u ^ n / (n.factorial : ℝ)
      have heq2 : ∀ n : ℕ, (n.factorial : ℝ)⁻¹ • u ^ n = u ^ n / (n.factorial : ℝ) := by
        intro n; simp [div_eq_mul_inv, mul_comm]
      simp_rw [heq2]
      have summable : Summable (fun n : ℕ => u ^ n / (n.factorial : ℝ)) :=
        Real.summable_pow_div_factorial u
      -- Partial sum up to n=2 is 1 + u + u²/2
      have hpartial : ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ) = 1 + u + u ^ 2 / 2 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      rw [← hpartial]
      -- Use that all terms are non-negative
      have term_nonneg : ∀ n : ℕ, 0 ≤ u ^ n / (n.factorial : ℝ) := fun n =>
        div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _)
      calc ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ)
          ≤ ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ) +
              ∑' n, u ^ (n + 3) / ((n + 3).factorial : ℝ) := by
            apply le_add_of_nonneg_right
            exact tsum_nonneg (fun n => div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _))
        _ = ∑' n, u ^ n / (n.factorial : ℝ) := by
            rw [Summable.sum_add_tsum_nat_add 3 summable]
    have tayl2 : Real.exp (t * b) ≥ 1 + t * b + (t * b) ^ 2 / 2 := exp_lower_bound (t * b) hbpos
    -- Let g = (exp(tb) - 1 - tb)/b². By tayl2, g ≥ t²/2.
    set g := (Real.exp (t * b) - 1 - t * b) / b ^ 2 with hg_def
    have hg_pos : g ≥ t ^ 2 / 2 := by
      have h1 : Real.exp (t * b) - 1 - t * b ≥ (t * b) ^ 2 / 2 := by linarith
      have h2 : (t * b) ^ 2 / 2 / b ^ 2 = t ^ 2 / 2 := by
        rw [div_eq_iff (by positivity : b ^ 2 ≠ 0)]
        ring
      have h3 : g ≥ (t * b) ^ 2 / 2 / b ^ 2 := div_le_div_of_nonneg_right h1 (sq_nonneg b)
      linarith
    -- Key: h(x) = 1 + tx + gx² - exp(tx) has h(0) = h'(0) = 0 and h''(x) ≥ 0 for x ≤ 0
    -- So h(x) ≥ 0 for x ≤ 0
    -- Rewrite goal in terms of g
    suffices h : Real.exp (t * x) ≤ 1 + t * x + x ^ 2 * g by
      convert h using 1
      rw [hg_def]
      ring
    -- Since g ≥ t²/2, we have x²*g ≥ x²*t²/2 = (tx)²/2
    -- So it suffices to show exp(tx) ≤ 1 + tx + (tx)²/2 for tx ≤ 0
    suffices h2 : Real.exp (t * x) ≤ 1 + t * x + (t * x) ^ 2 / 2 by
      have hxg : x ^ 2 * g ≥ (t * x) ^ 2 / 2 := by nlinarith [sq_nonneg x, sq_nonneg t]
      linarith
    -- Now prove exp(y) ≤ 1 + y + y²/2 for y ≤ 0
    have exp_le_quad : ∀ y : ℝ, y ≤ 0 → Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
      intro y hy
      -- Let z = -y ≥ 0. Need exp(-z) ≤ 1 - z + z²/2, equivalent to exp(z)(1 - z + z²/2) ≥ 1.
      set z := -y with hz_def
      have hz : z ≥ 0 := by simp [hz_def]; linarith
      have heq : Real.exp y = (Real.exp z)⁻¹ := by rw [hz_def]; simp [Real.exp_neg]
      rw [heq]
      -- Need: (exp z)⁻¹ ≤ 1 - z + z²/2, i.e., exp z * (1 - z + z²/2) ≥ 1
      have h_rhs_pos : 1 - z + z ^ 2 / 2 > 0 := by nlinarith [sq_nonneg (z - 1)]
      have h_eq : 1 + y + y ^ 2 / 2 = 1 - z + z ^ 2 / 2 := by rw [hz_def]; ring
      rw [h_eq]
      rw [inv_le_iff_one_le_mul₀ (Real.exp_pos z)]
      -- Need: 1 ≤ (1 - z + z²/2) * exp(z)
      -- Using exp(z) ≥ 1 + z + z²/2, we get:
      -- (1 - z + z²/2) * exp(z) ≥ (1 - z + z²/2) * (1 + z + z²/2) = z⁴/4 + 1 ≥ 1
      have h_exp_bound := exp_lower_bound z hz
      have h_prod : (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) = z ^ 4 / 4 + 1 := by ring
      have h_z4 : z ^ 4 / 4 + 1 ≥ 1 := by nlinarith [sq_nonneg (z ^ 2)]
      calc (1 - z + z ^ 2 / 2) * Real.exp z
          ≥ (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) := by nlinarith [h_exp_bound, h_rhs_pos]
        _ = z ^ 4 / 4 + 1 := h_prod
        _ ≥ 1 := h_z4
    exact exp_le_quad (t * x) htx_nonpos
  · -- Case 0 < x ≤ b
    push Not at hx_nonpos
    -- Key: h(u) = (exp(u) - 1 - u)/u² is increasing on (0, ∞).
    -- N(u) = exp(u)(u - 2) + 2 + 2u, N(0) = 0, N'(u) = exp(u)(u-1) + 2 > 0 for u ≥ 0.
    -- So N(u) ≥ 0, hence h'(u) ≥ 0, h is increasing.
    have h_mono : ∀ u v : ℝ, 0 < u → u ≤ v →
        (Real.exp u - 1 - u) / u ^ 2 ≤ (Real.exp v - 1 - v) / v ^ 2 := by
      -- N(u) = exp(u)(u-2) + u + 2, N(0) = 0, N'(u) = exp(u)(u-1) + 2 ≥ 1 > 0 for u ≥ 0
      -- So N(u) ≥ 0 for u ≥ 0, hence h'(u) = N(u)/u³ ≥ 0, h is increasing
      have hN_nonneg : ∀ u : ℝ, 0 ≤ u → Real.exp u * (u - 2) + u + 2 ≥ 0 := by
        -- N(u) = exp(u)(u-2) + u + 2, N(0) = 0
        -- N'(u) = exp(u)(u-1) + 2 ≥ 1 > 0 for u ≥ 0 (since exp(u) ≥ 1 and u + 1 ≥ 1)
        -- So N is increasing, N(u) ≥ N(0) = 0 for u ≥ 0
        intro u hu
        by_cases hu0 : u = 0
        · simp [hu0]
        · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
          -- Use that N is increasing: N(u) ≥ N(0) = 0
          -- N is differentiable with N'(x) = exp(x)(x-1) + 1 > 0 for x ≥ 0
          -- So N is strictly increasing on [0, ∞)
          have hN_deriv : ∀ x : ℝ, 0 < x → deriv (fun y => Real.exp y * (y - 2) + y + 2) x > 0 := by
            intro x hx
            have hderiv : HasDerivAt (fun y => Real.exp y * (y - 2) + y + 2)
                (Real.exp x * (x - 1) + 1) x := by
              have h1 : HasDerivAt (fun y => Real.exp y * (y - 2))
                  (Real.exp x * (x - 2) + Real.exp x * 1) x := by
                apply HasDerivAt.mul
                · exact Real.hasDerivAt_exp x
                · have := hasDerivAt_id x
                  simpa using this.sub_const 2
              have h2 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
              have h3 : HasDerivAt (fun y => (2 : ℝ)) 0 x := hasDerivAt_const x 2
              have h := h1.add h2 |>.add h3
              refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
              filter_upwards with y
              dsimp
            have hpos : Real.exp x * (x - 1) + 1 > 0 := by
              by_cases hx1 : x ≥ 1
              · nlinarith [Real.exp_pos x]
              · push Not at hx1
                -- For 0 < x < 1: need exp(x)(1-x) < 1 strictly
                have hexp_lt_geom : Real.exp x * (1 - x) < 1 := by
                  -- g(x) = exp(x)(1-x) is strictly decreasing for x > 0 since g'(x) = -x*exp(x) < 0
                  -- g(0) = 1, so g(x) < 1 for x > 0
                  have hg_deriv : ∀ y : ℝ, y > 0 → deriv (fun t => Real.exp t * (1 - t)) y < 0 := by
                    intro y hy
                    have h1 : HasDerivAt (fun t => Real.exp t) (Real.exp y) y :=
                      Real.hasDerivAt_exp y
                    have h2 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) y :=
                      (hasDerivAt_id y).const_sub 1
                    have h : HasDerivAt (fun t => Real.exp t * (1 - t))
                        (Real.exp y * (1 - y) + Real.exp y * -1) y := h1.mul h2
                    rw [h.deriv]
                    nlinarith [Real.exp_pos y]
                  have hg0 : (fun t => Real.exp t * (1 - t)) 0 = 1 := by norm_num
                  have hg_mono : StrictAntiOn (fun t => Real.exp t * (1 - t)) (Set.Ici 0) := by
                    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
                    · exact Continuous.continuousOn (by continuity)
                    · intro y hy
                      rw [interior_Ici] at hy
                      exact hg_deriv y hy
                  have hx_mem : x ∈ Set.Ici 0 := hx.le
                  have h0_mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
                  have : (fun t => Real.exp t * (1 - t)) x <
                      (fun t => Real.exp t * (1 - t)) 0 := hg_mono h0_mem hx_mem hx
                  linarith
                have heq : Real.exp x * (x - 1) + 1 = 1 - Real.exp x * (1 - x) := by ring
                linarith
            exact hderiv.deriv.symm ▸ hpos
          -- N(0) = 0 and N is strictly increasing on [0, ∞), so N(u) ≥ 0 for u ≥ 0
          have hN_strict_mono : StrictMonoOn
              (fun y => Real.exp y * (y - 2) + y + 2) (Set.Ici 0) := by
            apply strictMonoOn_of_deriv_pos (convex_Ici 0)
            · exact Continuous.continuousOn (by continuity)
            · intro x hx
              rw [interior_Ici] at hx
              exact hN_deriv x hx
          have hN0 : (fun y => Real.exp y * (y - 2) + y + 2) 0 = 0 := by norm_num
          have hNu_nonneg : (fun y => Real.exp y * (y - 2) + y + 2) 0 ≤
              (fun y => Real.exp y * (y - 2) + y + 2) u := by
            exact le_of_lt (hN_strict_mono (by norm_num) hu hu')
          linarith
      -- h(u) = (exp(u) - 1 - u)/u² is increasing since h'(u) = N(u)/u³ ≥ 0 for u > 0
      have h_deriv : ∀ u : ℝ, 0 < u →
          HasDerivAt (fun u => (Real.exp u - 1 - u) / u ^ 2)
            ((Real.exp u * (u - 2) + u + 2) / u ^ 3) u := by
        intro u hu
        have h1 : HasDerivAt (fun u => Real.exp u - 1 - u) (Real.exp u - 1) u := by
          have h := ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)
          refine h.congr_of_eventuallyEq ?_
          filter_upwards with z
          dsimp
        have h2 : HasDerivAt (fun u => u ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
        have hquot := h1.div h2 (pow_ne_zero 2 hu.ne')
        -- hquot gives derivative = ((exp(u) - 1) * u² - (exp(u) - 1 - u) * 2u) / u⁴
        -- We need to show this equals (exp(u)*(u-2) + u + 2) / u³
        have goal_eq :
            ((Real.exp u - 1) * u ^ 2 - (Real.exp u - 1 - u) * (2 * u)) / (u ^ 2) ^ 2 =
              (Real.exp u * (u - 2) + u + 2) / u ^ 3 := by
          have num_eq :
              (Real.exp u - 1) * u ^ 2 - (Real.exp u - 1 - u) * (2 * u) =
                u * (Real.exp u * (u - 2) + u + 2) := by
            ring
          rw [num_eq]
          rw [show (u ^ 2) ^ 2 = u ^ 4 by ring, show u ^ 4 = u ^ 3 * u by ring]
          rw [div_eq_div_iff (by positivity : u ^ 3 * u ≠ 0) (by positivity : u ^ 3 ≠ 0)]
          ring
        exact hquot.congr_deriv goal_eq
      have h_mono : ∀ u v : ℝ, 0 < u → u ≤ v →
          (Real.exp u - 1 - u) / u ^ 2 ≤ (Real.exp v - 1 - v) / v ^ 2 := by
        intro u v hu huv
        by_cases huv' : u = v
        · simp [huv']
        · have huv'' : u < v := lt_of_le_of_ne huv huv'
          have hdiff_inter : DifferentiableOn ℝ
              (fun u => (Real.exp u - 1 - u) / u ^ 2) (interior (Set.Icc u v)) := by
            rw [interior_Icc]
            exact DifferentiableOn.div
              (DifferentiableOn.sub (DifferentiableOn.sub (Real.differentiable_exp.differentiableOn)
                (differentiableOn_const 1)) differentiableOn_id)
              (differentiableOn_pow 2) (by intro x hx; nlinarith [hx.1])
          have hcont : ContinuousOn (fun u => (Real.exp u - 1 - u) / u ^ 2) (Set.Icc u v) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · exact Continuous.continuousOn (by continuity)
            · exact continuousOn_pow 2
            · intro x hx; nlinarith [hx.1]
          have hderiv_nonneg : ∀ x ∈ interior (Set.Icc u v),
              0 ≤ deriv (fun u => (Real.exp u - 1 - u) / u ^ 2) x := by
            rw [interior_Icc] at *
            intro x hx
            have hx_pos : 0 < x := lt_of_lt_of_le hu (le_of_lt hx.1)
            have := (h_deriv x hx_pos).deriv
            rw [this]
            apply div_nonneg
            · linarith [hN_nonneg x (le_of_lt hx_pos)]
            · exact pow_nonneg (le_of_lt hx_pos) 3
          have hmono := monotoneOn_of_deriv_nonneg (convex_Icc u v) hcont hdiff_inter hderiv_nonneg
          linarith [hmono (Set.left_mem_Icc.mpr (le_of_lt huv''))
            (Set.right_mem_Icc.mpr (le_of_lt huv'')) huv]
      exact h_mono
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htx_pos : 0 < t * x := mul_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hx_nonpos
      have htbb : t * x ≤ t * b := mul_le_mul_of_nonneg_left hx ht
      have := h_mono (t * x) (t * b) htx_pos htbb
      -- (exp(tx) - 1 - tx)/(tx)² ≤ (exp(tb) - 1 - tb)/(tb)²
      -- exp(tx) - 1 - tx ≤ x² * (exp(tb) - 1 - tb)/b² = x² * g
      have h1 : Real.exp (t * x) - 1 - t * x ≤
          (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) := by
        have := mul_le_mul_of_nonneg_left this (sq_nonneg (t * x))
        calc
          Real.exp (t * x) - 1 - t * x =
              (t * x) ^ 2 * ((Real.exp (t * x) - 1 - t * x) / (t * x) ^ 2) := by
            field_simp [ne_of_gt htx_pos]
          _ ≤ (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) := this
      have h2 : (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) =
          x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
        field_simp [ht0, hb.ne']
      linarith


/-- The elementary exponential remainder estimate which converts Bennett's bound to Bernstein's
sub-gamma bound. -/
theorem exp_sub_one_sub_le_bernstein {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  have hu2 : 0 < 1 - u / 3 := by linarith
  -- Rewrite as: (exp u - 1 - u) * 2 * (1 - u/3) ≤ u^2
  have key : (Real.exp u - 1 - u) * (2 * (1 - u / 3)) ≤ u ^ 2 := by
    -- This is equivalent to: (exp u - 1 - u) ≤ u^2 / (2(1-u/3))
    -- We prove by using norm-based bounds
    have h_bound : Real.exp u ≤ 1 + u + u^2 / (2 * (1 - u / 3)) := by
      -- Use Taylor series: exp u = ∑ u^n/n!
      -- Key: n! ≥ 2·3^{n-2} for n ≥ 2
      have fac_bound : ∀ n : ℕ, 2 ≤ n → (Nat.factorial n : ℝ) ≥ 2 * 3 ^ (n - 2) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ n hn ih =>
          have hfac : (Nat.factorial (n + 1) : ℝ) = (n + 1) * Nat.factorial n := by
            exact_mod_cast (Nat.factorial_succ n).symm
          have hpow : (3 : ℝ) ^ (n + 1 - 2) = 3 ^ (n - 1) := by
            congr 1
          rw [hpow]
          rw [hfac]
          have hp : (3 : ℝ) ^ (n - 1) = 3 * 3 ^ (n - 2) := by
            rw [show (n:ℕ) - 1 = (n - 2) + 1 by omega, pow_succ]; ring
          rw [hp]
          nlinarith [ih, show (n : ℝ) ≥ 2 by norm_cast]
      -- Now use fac_bound to prove the exponential bound
      -- We'll use the series expansion: exp u = ∑ u^n/n!
      have hsum := Real.summable_pow_div_factorial u
      -- Split: ∑_{n≥0} u^n/n! = 1 + u + ∑_{n≥2} u^n/n!
      -- Bound term by term: for n ≥ 2, u^n/n! ≤ u^n/(2·3^{n-2})
      -- So exp u = 1 + u + ∑_{n≥2} u^n/n! ≤ 1 + u + ∑_{n≥2} u^n/(2·3^{n-2})
      -- And ∑_{n≥2} u^n/(2·3^{n-2}) = u²/2 · ∑_{k≥0} (u/3)^k = u²/(2(1-u/3))
      have htail : ∀ n : ℕ, 2 ≤ n → u ^ n / ↑n.factorial ≤ u ^ n / (2 * 3 ^ (n - 2)) := by
        intro n hn
        have hfac := fac_bound n hn
        gcongr
      -- Use comparison with geometric series
      -- exp u - 1 - u = ∑_{n≥2} u^n/n! ≤ ∑_{n≥2} u^n/(2·3^{n-2}) = u²/(2(1-u/3))
      -- First, rewrite the geometric series: ∑_{n≥2} u^n/(2·3^{n-2}) = u²/2 · ∑_{k≥0} (u/3)^k
      -- The sum ∑_{k≥0} (u/3)^k = 1/(1-u/3) for u < 3
      have habs : |u / 3| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have hgeo_sum : ∑' k : ℕ, (u / 3) ^ k = 1 / (1 - u / 3) := by
        rw [tsum_geometric_of_abs_lt_one habs, one_div]
      -- Rewrite u²/(2(1-u/3)) = u²/2 · (1/(1-u/3)) = u²/2 · ∑_{k≥0} (u/3)^k
      have htail_sum : ∑' n : ℕ, u ^ (n + 2) / (2 * 3 ^ (n) : ℝ) = u ^ 2 / (2 * (1 - u / 3)) := by
        -- Rewrite: u^(n+2)/(2*3^n) = u²/2 * (u/3)^n
        have hfactor : ∀ n : ℕ, u ^ (n + 2) / (2 * 3 ^ n : ℝ) =
            u ^ 2 / 2 * (u / 3) ^ n := fun n => by
          rw [div_pow]; ring
        simp_rw [hfactor]
        rw [tsum_mul_left, hgeo_sum]
        field_simp
      -- Now prove the bound using tsum comparison
      -- exp u = ∑ u^n/n! = 1 + u + ∑' n, u^(n+2)/(n+2)!
      --       ≤ 1 + u + ∑' n, u^(n+2)/(2·3^n) = 1 + u + u²/(2(1-u/3))
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      -- Split off the first two terms: ∑ u^n/n! = 1 + u + ∑' n, u^(n+2)/(n+2)!
      change ∑' n : ℕ, u ^ n / ↑n.factorial ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3))
      have hsplit : ∑' n : ℕ, u ^ n / ↑n.factorial =
          1 + u + ∑' n : ℕ, u ^ (n + 2) / ↑(n + 2).factorial := by
        have h1 := hsum.tsum_eq_zero_add
        rw [h1]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
        -- Split the remaining sum once more to expose its first term.
        have h2 : ∑' n : ℕ, u ^ (n + 1) / ↑(n + 1).factorial =
            u + ∑' n : ℕ, u ^ (n + 2) / ↑(n + 2).factorial := by
          have := (hsum.comp_injective (Nat.succ_injective)).tsum_eq_zero_add
          simp only [Function.comp_apply] at this
          convert this using 2
          all_goals simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
        linarith [h2]
      rw [hsplit]
      -- Bound the tail using htail
      have htail_le : ∑' n : ℕ, u ^ (n + 2) / ↑(n + 2).factorial ≤
          ∑' n : ℕ, u ^ (n + 2) / (2 * 3 ^ (n) : ℝ) := by
        apply Summable.tsum_le_tsum _ _ _
        · intro n
          have := htail (n + 2) (by omega)
          simp only [ge_iff_le] at this ⊢
          exact this
        · exact hsum.comp_injective (add_left_injective 2)
        · have hgeo : Summable (fun n : ℕ => (u / 3) ^ n) := summable_geometric_of_abs_lt_one habs
          have heq : (fun n : ℕ => u ^ (n + 2) / (2 * 3 ^ n : ℝ)) =
                     (fun n : ℕ => u ^ 2 / 2 * (u / 3) ^ n) := by
            ext n; rw [div_pow]; ring
          rw [heq]
          exact Summable.mul_left _ hgeo
      rw [htail_sum] at htail_le
      linarith
    calc (Real.exp u - 1 - u) * (2 * (1 - u / 3))
        ≤ (1 + u + u^2 / (2 * (1 - u / 3)) - 1 - u) * (2 * (1 - u / 3)) := by nlinarith
      _ = u^2 := by
        have h3u : 3 - u ≠ 0 := by linarith
        field_simp [hu2.ne', h3u]
        ring
  rwa [le_div_iff₀ (mul_pos zero_lt_two hu2)]


/-- **Bennett's MGF inequality.** A centered random variable bounded above by `b > 0`, whose second
moment is at most `V`, has the Bennett exponential-moment bound. -/
theorem mgf_le_bennett [IsProbabilityMeasure μ] {X : Ω → ℝ} {V b t : ℝ}
    (hbpos : 0 < b) (ht : 0 ≤ t)
    (hX0 : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hvar : μ[fun ω => (X ω) ^ 2] ≤ V)
    (hXint : Integrable X μ) (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ)
    (hexpint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (V * (Real.exp (t * b) - 1 - t * b) / b ^ 2) := by
  -- Pointwise bound: exp(t * X ω) ≤ 1 + t * X ω + X ω² * (exp(tb) - 1 - tb) / b²
  have hptwise : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤
      1 + t * X ω + (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
    filter_upwards [hb] with ω hω
    exact exp_mul_le_bennett_quadratic ht hbpos hω
  -- Integrate both sides
  have hintegr : ∫ ω, Real.exp (t * X ω) ∂μ ≤
      ∫ ω, (1 + t * X ω +
        (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) ∂μ := by
    apply MeasureTheory.integral_mono_ae hexpint
    · have h1 : MeasureTheory.Integrable (fun _ => (1 : ℝ)) μ := MeasureTheory.integrable_const _
      have h2 : MeasureTheory.Integrable (fun ω => t * X ω) μ := hXint.const_mul t
      have h3 : MeasureTheory.Integrable
          (fun ω => (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) μ := by
        have := hXsqint.mul_const ((Real.exp (t * b) - 1 - t * b) / b ^ 2)
        convert this using 1
        ext ω
        ring
      exact h1.add h2 |> MeasureTheory.Integrable.add <| h3
    · exact hptwise
  -- Evaluate the RHS integral
  have heval : ∫ ω, (1 + t * X ω + (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) ∂μ =
      (∫ _ : Ω, (1 : ℝ) ∂μ) + (∫ ω, t * X ω ∂μ) +
        (∫ ω, (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 ∂μ) := by
    rw [MeasureTheory.integral_add, MeasureTheory.integral_add]
    · exact MeasureTheory.integrable_const _
    · exact hXint.const_mul t
    · exact MeasureTheory.Integrable.add (MeasureTheory.integrable_const _) (hXint.const_mul t)
    · have := hXsqint.mul_const ((Real.exp (t * b) - 1 - t * b) / b ^ 2)
      convert this using 1
      ext ω
      ring
  -- Simplify the constant integral
  have hconst : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp [MeasureTheory.integral_const]
  -- Simplify the X integral using E[X] = 0
  have hXint_zero : ∫ ω, t * X ω ∂μ = 0 := by
    simp [mul_comm t, MeasureTheory.integral_mul_const, hX0]
  -- Evaluate the X² integral
  have hXsqint_eval : ∫ ω, (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 ∂μ =
      (Real.exp (t * b) - 1 - t * b) / b ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
    have : (fun ω => (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) =
           fun ω => ((Real.exp (t * b) - 1 - t * b) / b ^ 2) * (X ω) ^ 2 := by
      ext ω; ring
    rw [this]
    simp_rw [mul_comm]
    rw [MeasureTheory.integral_mul_const]
    ring
  -- Now combine everything
  have hmgf : mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl
  rw [hmgf]
  calc ∫ ω, Real.exp (t * X ω) ∂μ
      ≤ ∫ ω, (1 + t * X ω + (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) ∂μ := hintegr
    _ = 1 + 0 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
      rw [heval, hconst, hXint_zero, hXsqint_eval]
    _ = 1 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by ring
    _ ≤ 1 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * V := by
        have hexp_ge : Real.exp (t * b) - 1 - t * b ≥ 0 := by linarith [Real.add_one_le_exp (t * b)]
        have hC_nonneg : (Real.exp (t * b) - 1 - t * b) / b ^ 2 ≥ 0 := by positivity
        gcongr
    _ = 1 + V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by ring
    _ ≤ Real.exp (V * (Real.exp (t * b) - 1 - t * b) / b ^ 2) := by
        have hexp_ge : Real.exp (t * b) - 1 - t * b ≥ 0 := by linarith [Real.add_one_le_exp (t * b)]
        have hX2_nonneg : (0 : ℝ) ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
          apply MeasureTheory.integral_nonneg
          intro ω
          positivity
        have hV_nonneg : (0 : ℝ) ≤ V := le_trans hX2_nonneg hvar
        have hy : V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 ≥ 0 := by positivity
        rw [add_comm]
        exact Real.add_one_le_exp _

/-- A bounded-above centered random variable with second moment at most `V` is sub-gamma with
variance factor `V` and scale `b / 3`. -/
theorem hasSubgammaMGF_of_bounded_above [IsProbabilityMeasure μ] {X : Ω → ℝ} {V b : ℝ}
    (hbpos : 0 < b)
    (hX0 : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hvar : μ[fun ω => (X ω) ^ 2] ≤ V)
    (hXint : Integrable X μ) (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ)
    (hexpint : ∀ t : ℝ, 0 ≤ t → t < 3 / b →
      Integrable (fun ω => Real.exp (t * X ω)) μ) :
    HasSubgammaMGF X V (b / 3) μ := by
  intro t ht htc
  have hb3 : t < 3 / b := by
    rw [lt_div_iff₀ hbpos]
    nlinarith [htc]
  have hbennett := mgf_le_bennett hbpos ht hX0 hb hvar hXint hXsqint (hexpint t ht hb3)
  have htbeq : t * b < 3 := by rwa [lt_div_iff₀ hbpos] at hb3
  have ubeqn : 0 ≤ t * b := mul_nonneg ht (le_of_lt hbpos)
  have berenstein := exp_sub_one_sub_le_bernstein ubeqn htbeq
  have hden : 0 < 1 - b / 3 * t := by linarith
  have hexp_ge : rexp (t * b) - 1 - t * b ≥ 0 := by
    have := Real.add_one_le_exp (t * b)
    linarith
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hbpos
  have hberenstein' : V * (rexp (t * b) - 1 - t * b) / b ^ 2 ≤
      V * t ^ 2 / (2 * (1 - b / 3 * t)) := by
    have hb3eq : 1 - b / 3 * t = 1 - t * b / 3 := by ring
    rw [hb3eq]
    have hineq : (t * b) ^ 2 / (2 * (1 - t * b / 3)) / b ^ 2 = t ^ 2 / (2 * (1 - t * b / 3)) := by
      field_simp [hbpos.ne']
    by_cases hV : V ≥ 0
    · calc V * (rexp (t * b) - 1 - t * b) / b ^ 2
        = V * ((rexp (t * b) - 1 - t * b) / b ^ 2) := by ring
      _ ≤ V * ((t * b) ^ 2 / (2 * (1 - t * b / 3)) / b ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hV
          exact div_le_div_of_nonneg_right berenstein hb2.le
      _ = V * (t ^ 2 / (2 * (1 - t * b / 3))) := by rw [hineq]
      _ = V * t ^ 2 / (2 * (1 - t * b / 3)) := by ring
    · -- V < 0 case is impossible: μ[X²] ≥ 0 and μ[X²] ≤ V, so V ≥ 0
      have hXsq_nonneg : 0 ≤ μ[fun ω => (X ω) ^ 2] := integral_nonneg_of_ae (by
        filter_upwards with ω
        exact sq_nonneg _)
      linarith
  exact le_trans hbennett (Real.exp_le_exp.mpr hberenstein')

end Contrib.Bennett
