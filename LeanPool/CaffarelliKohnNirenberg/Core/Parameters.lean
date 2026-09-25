/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The standing parameters of Section 5

This file records the numerical choices made once and for all at the start of
`paper/ckn.tex`, Section 5, in the convention `conv:step-params` with its
displayed equation `eq:standing`:

* the velocity exponent `τ₂ = 25/3`, the gradient exponent `τ₃` with
  `1/τ₃ = 1/τ₂ + 1/5` by arithmetic from the definitions, and the pressure
  exponent `τ_p = 25/8`;
* the integrability parameter `σ = 3 - 5/q` attached to the force exponent `q`;
* the Hölder exponent `γ₀(q) = min {2 - 5/q, 1/5}` of `eq:gamma-value`;
* the Morrey exponents `θ₀, θ₁` of `eq:q0q1`.

The exponent `ε = 2/5` of `eq:standing` is not redefined here: it is the
established constant `CKN.iterationEpsilon` from `CKN.Core.Iteration.Arithmetic`.
The file proves the numerical inequalities those constants are introduced to
supply: `5 < τ₂` and `τ₃ > 5/2` (the two inequalities Steps 3 and 4 consume),
the bootstrap condition `eq:bootstrap-cond` at the exponent `τ = τ₂` actually
used in Corollary `cor:one-round`, the positivity and upper bound
`0 < γ₀(q) ≤ 1/5` for `q > 5/2`, the lower bound `σ > 1` for `q > 5/2`, and
the exponent identities `2 - 5/θ₀ = 1 - 5/θ₁ = γ` of `eq:q0q1`.
-/

@[expose] public section

noncomputable section

namespace CKN

/-! ### The exponents `τ₂`, `τ₃`, `τ_p` of `eq:standing` -/

/-- The velocity Morrey exponent `τ₂ = 5/(1 - ε) = 25/3` of `eq:standing`; its
fixed value is given by `stepTau₂`, with `ε = 2/5` recorded in
`iterationEpsilon_eq`. -/
def stepTau₂ : ℝ := 25 / 3

/-- The gradient Morrey exponent `τ₃` of `eq:standing`, taken at the value
`τ₃ = 25/8` by `stepTau₃`; the bootstrap range using its reciprocal is
recorded in `bootstrap_condition_iff`. -/
def stepTau₃ : ℝ := 25 / 8

/-- The pressure Morrey exponent `τ_p = 25/8` of `eq:standing`, equal to `τ₃`;
see Remark `rem:LR-pressure` for why it is not consumed downstream. -/
def stepTauP : ℝ := 25 / 8







/-- The bootstrap gain `ϖ = 1/5 - 1/τ₂` of `eq:bootstrap-gain`. -/
def stepVarpi : ℝ := 1 / 5 - 1 / stepTau₂

/-- `eq:bootstrap-gain` states `ϖ = ε/5` with `ε = 2/5`. -/
theorem stepVarpi_eq : stepVarpi = iterationEpsilon / 5 := by
  norm_num [stepVarpi, stepTau₂, iterationEpsilon]

/-- The numerical value of the gain: `ϖ = 2/25`. -/
theorem stepVarpi_eq_two_twentyfifths : stepVarpi = 2 / 25 := by
  norm_num [stepVarpi, stepTau₂]



/-- The gain computation of Corollary `cor:one-round`: `1/τ₂ - ϖ = 1/25`
(the reciprocal of the exponent `τ₄ = 25` appearing there). -/
theorem bootstrap_gain_at_tau₂ : 1 / stepTau₂ - stepVarpi = 1 / 25 := by
  norm_num [stepVarpi, stepTau₂]

/-! ### The parameter `σ` of `eq:standing` -/

/-- The integrability parameter `σ = 3 - 5/q` of `eq:standing`, a function of
the force exponent `q`. -/
def stepSigma (q : ℝ) : ℝ := 3 - 5 / q

/-- `eq:standing` records `σ = 3 - 5/q > 1` under `q > 5/2`. -/
theorem one_lt_stepSigma {q : ℝ} (hq : (5 : ℝ) / 2 < q) : 1 < stepSigma q := by
  unfold stepSigma
  have hqpos : 0 < q := by linarith only [hq]
  have h : 5 / q < 2 := by
    rw [div_lt_iff₀ hqpos]
    linarith only [hq]
  linarith only [h]

/-- `conv:step-params` uses `ε < σ` with `ε = 2/5`; under `q > 5/2` this holds
for `σ = 3 - 5/q`. -/
theorem iterationEpsilon_lt_stepSigma {q : ℝ} (hq : (5 : ℝ) / 2 < q) :
    iterationEpsilon < stepSigma q := by
  unfold stepSigma
  have hqpos : 0 < q := by linarith only [hq]
  have h : 5 / q < 13 / 5 := by
    rw [div_lt_iff₀ hqpos]
    linarith only [hq]
  norm_num [iterationEpsilon]
  linarith only [h]

/-! ### The Hölder exponent `γ₀` of `eq:gamma-value` -/

/-- The Hölder exponent `γ₀(q) = min {2 - 5/q, 1/5}` of `eq:gamma-value` in
Theorem `thm:endgame`. -/
def stepGamma₀ (q : ℝ) : ℝ := min (2 - 5 / q) (1 / 5)

/-- `eq:gamma-value` records `γ₀ > 0` because `q > 5/2`. -/
theorem stepGamma₀_pos {q : ℝ} (hq : (5 : ℝ) / 2 < q) : 0 < stepGamma₀ q := by
  unfold stepGamma₀
  apply lt_min
  · have hqpos : 0 < q := by linarith only [hq]
    have h : 5 / q < 2 := by
      rw [div_lt_iff₀ hqpos]
      linarith only [hq]
    linarith only [h]
  · norm_num

/-- The upper bound `γ₀(q) ≤ 1/5` of `eq:gamma-value`. -/
theorem stepGamma₀_le_fifth (q : ℝ) : stepGamma₀ q ≤ 1 / 5 := by
  unfold stepGamma₀
  exact min_le_right _ _



/-- Since `γ₀(q) ≤ 1/5 < 1`, the Hölder exponent lies in `(0,1)` when
`q > 5/2`, as `prop:heat-morrey-hoelder` requires. -/
theorem stepGamma₀_lt_one (q : ℝ) : stepGamma₀ q < 1 := by
  have h := stepGamma₀_le_fifth q
  linarith only [h]

/-! ### The exponents `θ₀`, `θ₁` of `eq:q0q1` -/

/-- The Morrey exponent `θ₀ = 5/(2 - γ)` of `eq:q0q1`, as a function of the
Hölder exponent `γ`. -/
def stepTheta₀ (γ : ℝ) : ℝ := 5 / (2 - γ)

/-- The Morrey exponent `θ₁ = 5/(1 - γ)` of `eq:q0q1`, as a function of the
Hölder exponent `γ`. -/
def stepTheta₁ (γ : ℝ) : ℝ := 5 / (1 - γ)

/-- The first identity of `eq:q0q1`: `1/θ₀ = (2 - γ)/5`. -/
theorem stepTheta₀_inv (γ : ℝ) : 1 / stepTheta₀ γ = (2 - γ) / 5 := by
  rw [stepTheta₀, one_div, inv_div]

/-- The second identity of `eq:q0q1`: `1/θ₁ = (1 - γ)/5`. -/
theorem stepTheta₁_inv (γ : ℝ) : 1 / stepTheta₁ γ = (1 - γ) / 5 := by
  rw [stepTheta₁, one_div, inv_div]



/-- `eq:q0q1` records `θ₀ = 5/(2 - γ) > 5/2` for `γ ∈ (0,1)`. -/
theorem stepTheta₀_gt_half {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (5 : ℝ) / 2 < stepTheta₀ γ := by
  rw [stepTheta₀]
  have h : 0 < 2 - γ := by linarith only [hγ1]
  rw [lt_div_iff₀ h]
  linarith only [hγ0]

/-- `eq:q0q1` records `θ₁ = 5/(1 - γ) > 5` for `γ ∈ (0,1)`. -/
theorem stepTheta₁_gt_five {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (5 : ℝ) < stepTheta₁ γ := by
  rw [stepTheta₁]
  have h : 0 < 1 - γ := by linarith only [hγ1]
  rw [lt_div_iff₀ h]
  linarith only [hγ0]

end CKN
