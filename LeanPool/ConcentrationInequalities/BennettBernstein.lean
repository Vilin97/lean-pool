/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

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

@[expose] public section

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

/-- The second-order Taylor lower bound for the exponential on the nonnegative half-line. -/
private lemma exp_ge_one_add_add_sq_half {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 ≤ Real.exp u := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  have heq2 : ∀ n : ℕ, (n.factorial : ℝ)⁻¹ • u ^ n = u ^ n / (n.factorial : ℝ) := by
    intro n
    simp [div_eq_mul_inv, mul_comm]
  simp_rw [heq2]
  have summable : Summable (fun n : ℕ => u ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial u
  have hpartial : ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ) =
      1 + u + u ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [← hpartial]
  calc
    ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ) ≤
        ∑ n ∈ Finset.range 3, u ^ n / (n.factorial : ℝ) +
          ∑' n, u ^ (n + 3) / ((n + 3).factorial : ℝ) := by
      apply le_add_of_nonneg_right
      exact tsum_nonneg (fun n => div_nonneg (pow_nonneg hu _) (Nat.cast_nonneg _))
    _ = ∑' n, u ^ n / (n.factorial : ℝ) := by
      rw [Summable.sum_add_tsum_nat_add 3 summable]

/-- The matching second-order upper bound for the exponential on the nonpositive half-line. -/
private lemma exp_le_one_add_add_sq_half_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  set z := -y with hz_def
  have hz : 0 ≤ z := by simp [hz_def]; linarith
  have heq : Real.exp y = (Real.exp z)⁻¹ := by rw [hz_def]; simp [Real.exp_neg]
  rw [heq]
  have h_rhs_pos : 0 < 1 - z + z ^ 2 / 2 := by nlinarith [sq_nonneg (z - 1)]
  have h_eq : 1 + y + y ^ 2 / 2 = 1 - z + z ^ 2 / 2 := by rw [hz_def]; ring
  rw [h_eq, inv_le_iff_one_le_mul₀ (Real.exp_pos z)]
  have h_exp_bound := exp_ge_one_add_add_sq_half hz
  have h_prod : (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) = z ^ 4 / 4 + 1 := by
    ring
  calc
    1 ≤ z ^ 4 / 4 + 1 := by nlinarith [sq_nonneg (z ^ 2)]
    _ = (1 - z + z ^ 2 / 2) * (1 + z + z ^ 2 / 2) := h_prod.symm
    _ ≤ (1 - z + z ^ 2 / 2) * Real.exp z := by
      nlinarith [h_exp_bound, h_rhs_pos]

/-- For positive `x`, the auxiliary function `exp x * (1 - x)` is strictly below one. -/
private lemma exp_mul_one_sub_lt_one {x : ℝ} (hx : 0 < x) : Real.exp x * (1 - x) < 1 := by
  have hg_deriv : ∀ y : ℝ, 0 < y → deriv (fun t => Real.exp t * (1 - t)) y < 0 := by
    intro y hy
    have h1 : HasDerivAt (fun t => Real.exp t) (Real.exp y) y := Real.hasDerivAt_exp y
    have h2 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) y := (hasDerivAt_id y).const_sub 1
    have h := h1.mul h2
    change deriv ((fun t => Real.exp t) * fun t => 1 - t) y < 0
    rw [h.deriv]
    nlinarith [Real.exp_pos y]
  have hg_mono : StrictAntiOn (fun t => Real.exp t * (1 - t)) (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · exact Continuous.continuousOn (by continuity)
    · intro y hy
      rw [interior_Ici] at hy
      exact hg_deriv y hy
  have h := hg_mono (by norm_num : (0 : ℝ) ∈ Set.Ici 0) hx.le hx
  norm_num at h ⊢
  exact h

/-- Derivative formula for the numerator controlling the Bennett quotient. -/
private lemma hasDerivAt_bennett_numerator (x : ℝ) :
    HasDerivAt (fun y => Real.exp y * (y - 2) + y + 2)
      (Real.exp x * (x - 1) + 1) x := by
  have h1 : HasDerivAt (fun y => Real.exp y * (y - 2))
      (Real.exp x * (x - 2) + Real.exp x * 1) x := by
    exact (Real.hasDerivAt_exp x).mul ((hasDerivAt_id x).sub_const 2)
  have h := h1.add (hasDerivAt_id x) |>.add (hasDerivAt_const x 2)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  dsimp

/-- The Bennett numerator has positive derivative on the positive half-line. -/
private lemma bennett_numerator_deriv_pos {x : ℝ} (hx : 0 < x) :
    0 < deriv (fun y => Real.exp y * (y - 2) + y + 2) x := by
  rw [(hasDerivAt_bennett_numerator x).deriv]
  by_cases hx1 : 1 ≤ x
  · nlinarith [Real.exp_pos x]
  · have hgeom := exp_mul_one_sub_lt_one hx
    have heq : Real.exp x * (x - 1) + 1 = 1 - Real.exp x * (1 - x) := by ring
    linarith

/-- The numerator in the derivative of the Bennett quotient is nonnegative. -/
private lemma bennett_numerator_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Real.exp u * (u - 2) + u + 2 := by
  rcases hu.eq_or_lt with rfl | hu
  · norm_num
  · have hmono : StrictMonoOn (fun y => Real.exp y * (y - 2) + y + 2) (Set.Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact Continuous.continuousOn (by continuity)
      · intro x hx
        rw [interior_Ici] at hx
        exact bennett_numerator_deriv_pos hx
    have h := hmono (by norm_num : (0 : ℝ) ∈ Set.Ici 0) hu.le hu
    norm_num at h ⊢
    exact h.le

/-- Derivative formula for the normalized exponential remainder. -/
private lemma hasDerivAt_bennett_ratio {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => (Real.exp z - 1 - z) / z ^ 2)
      ((Real.exp u * (u - 2) + u + 2) / u ^ 3) u := by
  have h1 : HasDerivAt (fun z => Real.exp z - 1 - z) (Real.exp u - 1) u := by
    have h := ((Real.hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id u)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with z
    dsimp
  have h2 : HasDerivAt (fun z => z ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hquot := h1.div h2 (pow_ne_zero 2 hu.ne')
  have num_eq :
      (Real.exp u - 1) * u ^ 2 - (Real.exp u - 1 - u) * (2 * u) =
        u * (Real.exp u * (u - 2) + u + 2) := by
    ring
  have goal_eq :
      ((Real.exp u - 1) * u ^ 2 - (Real.exp u - 1 - u) * (2 * u)) / (u ^ 2) ^ 2 =
        (Real.exp u * (u - 2) + u + 2) / u ^ 3 := by
    rw [num_eq, show (u ^ 2) ^ 2 = u ^ 4 by ring, show u ^ 4 = u ^ 3 * u by ring]
    rw [div_eq_div_iff (by positivity : u ^ 3 * u ≠ 0) (by positivity : u ^ 3 ≠ 0)]
    ring
  exact hquot.congr_deriv goal_eq

/-- The normalized exponential remainder is monotone on the positive half-line. -/
private lemma bennett_ratio_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (Real.exp u - 1 - u) / u ^ 2 ≤ (Real.exp v - 1 - v) / v ^ 2 := by
  rcases huv.eq_or_lt with rfl | huv
  · rfl
  · have hdiff : DifferentiableOn ℝ (fun z => (Real.exp z - 1 - z) / z ^ 2)
        (interior (Set.Icc u v)) := by
      rw [interior_Icc]
      exact DifferentiableOn.div
        (DifferentiableOn.sub
          (DifferentiableOn.sub Real.differentiable_exp.differentiableOn
            (differentiableOn_const 1)) differentiableOn_id)
        (differentiableOn_pow 2) (by intro x hx; nlinarith [hx.1])
    have hcont : ContinuousOn (fun z => (Real.exp z - 1 - z) / z ^ 2) (Set.Icc u v) := by
      exact ContinuousOn.div (Continuous.continuousOn (by continuity)) (continuousOn_pow 2)
        (by intro x hx; nlinarith [hx.1])
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) hcont hdiff
      (fun x hx => ?_) (Set.left_mem_Icc.mpr huv.le) (Set.right_mem_Icc.mpr huv.le) huv.le
    rw [interior_Icc] at hx
    rw [(hasDerivAt_bennett_ratio (lt_of_lt_of_le hu hx.1.le)).deriv]
    exact div_nonneg (bennett_numerator_nonneg (le_of_lt (lt_of_lt_of_le hu hx.1.le)))
      (pow_nonneg (le_of_lt (lt_of_lt_of_le hu hx.1.le)) 3)

/-- The nonpositive branch of Bennett's pointwise quadratic majorant. -/
private lemma exp_mul_le_bennett_quadratic_of_nonpos {t b x : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hx : x ≤ 0) :
    Real.exp (t * x) ≤
      1 + t * x + x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
  have htx : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hx
  have hlower := exp_ge_one_add_add_sq_half (mul_nonneg ht hb.le)
  have hrem : t ^ 2 / 2 ≤ (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
    have h1 : (t * b) ^ 2 / 2 ≤ Real.exp (t * b) - 1 - t * b := by linarith
    have h2 : (t * b) ^ 2 / 2 / b ^ 2 = t ^ 2 / 2 := by
      rw [div_eq_iff (by positivity : b ^ 2 ≠ 0)]
      ring
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 (sq_nonneg b)
  have hquad := exp_le_one_add_add_sq_half_of_nonpos htx
  have hxg : (t * x) ^ 2 / 2 ≤
      x ^ 2 * ((Real.exp (t * b) - 1 - t * b) / b ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg t]
  calc
    Real.exp (t * x) ≤ 1 + t * x +
        x ^ 2 * ((Real.exp (t * b) - 1 - t * b) / b ^ 2) := by linarith
    _ = 1 + t * x + x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by ring

/-- The positive branch of Bennett's pointwise quadratic majorant. -/
private lemma exp_mul_le_bennett_quadratic_of_pos {t b x : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hx : 0 < x) (hxb : x ≤ b) :
    Real.exp (t * x) ≤
      1 + t * x + x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · have htx : 0 < t * x := mul_pos ht hx
    have hmono := bennett_ratio_mono htx (mul_le_mul_of_nonneg_left hxb ht.le)
    have h1 : Real.exp (t * x) - 1 - t * x ≤
        (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hmono (sq_nonneg (t * x))
      calc
        Real.exp (t * x) - 1 - t * x =
            (t * x) ^ 2 * ((Real.exp (t * x) - 1 - t * x) / (t * x) ^ 2) := by
          field_simp [htx.ne']
        _ ≤ (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) := hmul
    have h2 : (t * x) ^ 2 * ((Real.exp (t * b) - 1 - t * b) / (t * b) ^ 2) =
        x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
      field_simp [ht.ne', hb.ne']
    linarith

/-- The pointwise quadratic majorant underlying Bennett's MGF inequality. -/
theorem exp_mul_le_bennett_quadratic {t b x : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hx : x ≤ b) :
    Real.exp (t * x) ≤
      1 + t * x + x ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
  by_cases hx0 : x ≤ 0
  · exact exp_mul_le_bennett_quadratic_of_nonpos ht hb hx0
  · exact exp_mul_le_bennett_quadratic_of_pos ht hb (lt_of_not_ge hx0) hx

/-- A factorial lower bound used to compare the exponential tail with a geometric series. -/
private lemma factorial_cast_ge_two_mul_three_pow_sub_two {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) * 3 ^ (n - 2) ≤ Nat.factorial n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hfac : (Nat.factorial (n + 1) : ℝ) = (n + 1) * Nat.factorial n := by
      exact_mod_cast (Nat.factorial_succ n).symm
    have hpow : (3 : ℝ) ^ (n + 1 - 2) = 3 * 3 ^ (n - 2) := by
      rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ]
      ring
    rw [hfac, hpow]
    nlinarith [ih, show (2 : ℝ) ≤ n by norm_cast]

/-- The exponential series with its constant and linear terms split off. -/
private lemma exp_series_split_two (u : ℝ) :
    ∑' n : ℕ, u ^ n / (n.factorial : ℝ) =
      1 + u + ∑' n : ℕ, u ^ (n + 2) / ((n + 2).factorial : ℝ) := by
  have hsum := Real.summable_pow_div_factorial u
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have htail := (hsum.comp_injective Nat.succ_injective).tsum_eq_zero_add
  simp only [Function.comp_apply] at htail
  have htail' : ∑' n : ℕ, u ^ (n + 1) / ((n + 1).factorial : ℝ) =
      u + ∑' n : ℕ, u ^ (n + 2) / ((n + 2).factorial : ℝ) := by
    convert htail using 2
    all_goals simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  linarith

/-- Closed form of the geometric series used to dominate the exponential tail. -/
private lemma geometric_bennett_tail_sum {u : ℝ} (habs : |u / 3| < 1) :
    ∑' n : ℕ, u ^ (n + 2) / (2 * 3 ^ n : ℝ) = u ^ 2 / (2 * (1 - u / 3)) := by
  have hfactor : ∀ n : ℕ, u ^ (n + 2) / (2 * 3 ^ n : ℝ) =
      u ^ 2 / 2 * (u / 3) ^ n := fun n => by
    rw [div_pow]
    ring
  simp_rw [hfactor]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one habs]
  field_simp

/-- The factorial tail of the exponential series is bounded by the Bennett geometric tail. -/
private lemma exp_series_tail_le_geometric_bennett {u : ℝ} (hu : 0 ≤ u)
    (habs : |u / 3| < 1) :
    ∑' n : ℕ, u ^ (n + 2) / ((n + 2).factorial : ℝ) ≤
      ∑' n : ℕ, u ^ (n + 2) / (2 * 3 ^ n : ℝ) := by
  apply Summable.tsum_le_tsum
  · intro n
    have hfac := factorial_cast_ge_two_mul_three_pow_sub_two (n := n + 2) (by omega)
    gcongr
    simpa using hfac
  · exact (Real.summable_pow_div_factorial u).comp_injective (add_left_injective 2)
  · have hgeo : Summable (fun n : ℕ => (u / 3) ^ n) :=
      summable_geometric_of_abs_lt_one habs
    have heq : (fun n : ℕ => u ^ (n + 2) / (2 * 3 ^ n : ℝ)) =
        (fun n : ℕ => u ^ 2 / 2 * (u / 3) ^ n) := by
      ext n
      rw [div_pow]
      ring
    rw [heq]
    exact Summable.mul_left _ hgeo

/-- The exponential form of the Bennett-to-Bernstein comparison. -/
private lemma exp_le_bernstein_majorant {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3)) := by
  have habs : |u / 3| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change ∑' n : ℕ, u ^ n / (n.factorial : ℝ) ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3))
  rw [exp_series_split_two u]
  have htail := exp_series_tail_le_geometric_bennett hu0 habs
  rw [geometric_bennett_tail_sum habs] at htail
  linarith

/-- The elementary exponential remainder estimate which converts Bennett's bound to Bernstein's
sub-gamma bound. -/
theorem exp_sub_one_sub_le_bernstein {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u < 3) :
    Real.exp u - 1 - u ≤ u ^ 2 / (2 * (1 - u / 3)) := by
  linarith [exp_le_bernstein_majorant hu0 hu3]



/-- Integrability of the quadratic Bennett majorant. -/
private lemma integrable_bennett_majorant [IsFiniteMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hXint : Integrable X μ) (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ) :
    Integrable (fun ω =>
      1 + t * X ω + (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) μ := by
  have h1 : Integrable (fun _ => (1 : ℝ)) μ := MeasureTheory.integrable_const _
  have h2 : Integrable (fun ω => t * X ω) μ := hXint.const_mul t
  have h3 : Integrable
      (fun ω => (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) μ := by
    have h := hXsqint.mul_const ((Real.exp (t * b) - 1 - t * b) / b ^ 2)
    convert h using 1
    ext ω
    ring
  exact h1.add h2 |>.add h3

/-- Evaluation of the integral of the quadratic Bennett majorant. -/
private lemma integral_bennett_majorant [IsProbabilityMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hX0 : μ[X] = 0) (hXint : Integrable X μ)
    (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ) :
    ∫ ω, (1 + t * X ω +
        (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) ∂μ =
      1 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
  have hquad : ∫ ω, (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 ∂μ =
      (Real.exp (t * b) - 1 - t * b) / b ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
    have heq : (fun ω => (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2) =
        fun ω => ((Real.exp (t * b) - 1 - t * b) / b ^ 2) * (X ω) ^ 2 := by
      ext ω
      ring
    rw [heq]
    simp_rw [mul_comm]
    rw [MeasureTheory.integral_mul_const]
    ring
  have hconst : ∫ _ : Ω, (1 : ℝ) ∂μ = 1 := by simp [MeasureTheory.integral_const]
  have hlin : ∫ ω, t * X ω ∂μ = 0 := by
    simp [mul_comm t, MeasureTheory.integral_mul_const, hX0]
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add]
  · rw [hconst, hlin, hquad]
    ring
  · exact MeasureTheory.integrable_const _
  · exact hXint.const_mul t
  · exact (MeasureTheory.integrable_const _).add (hXint.const_mul t)
  · have h := hXsqint.mul_const ((Real.exp (t * b) - 1 - t * b) / b ^ 2)
    convert h using 1
    ext ω
    ring

/-- The integrated quadratic majorant before the final exponential comparison. -/
private lemma mgf_le_one_add_bennett [IsProbabilityMeasure μ] {X : Ω → ℝ} {V b t : ℝ}
    (hbpos : 0 < b) (ht : 0 ≤ t) (hX0 : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hvar : μ[fun ω => (X ω) ^ 2] ≤ V) (hXint : Integrable X μ)
    (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ)
    (hexpint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ 1 + V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
  have hptwise : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤
      1 + t * X ω + (X ω) ^ 2 * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
    filter_upwards [hb] with ω hω
    exact exp_mul_le_bennett_quadratic ht hbpos hω
  have hintegr := MeasureTheory.integral_mono_ae hexpint
    (integrable_bennett_majorant hXint hXsqint) hptwise
  rw [integral_bennett_majorant hX0 hXint hXsqint] at hintegr
  have hcoeff : 0 ≤ (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by
    have hrem : 0 ≤ Real.exp (t * b) - 1 - t * b := by
      linarith [Real.add_one_le_exp (t * b)]
    positivity
  calc
    mgf X μ t ≤ 1 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 *
        ∫ ω, (X ω) ^ 2 ∂μ := hintegr
    _ ≤ 1 + (Real.exp (t * b) - 1 - t * b) / b ^ 2 * V := by gcongr
    _ = 1 + V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by ring

/-- **Bennett's MGF inequality.** A centered random variable bounded above by `b > 0`, whose second
moment is at most `V`, has the Bennett exponential-moment bound. -/
theorem mgf_le_bennett [IsProbabilityMeasure μ] {X : Ω → ℝ} {V b t : ℝ}
    (hbpos : 0 < b) (ht : 0 ≤ t)
    (hX0 : μ[X] = 0) (hb : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hvar : μ[fun ω => (X ω) ^ 2] ≤ V)
    (hXint : Integrable X μ) (hXsqint : Integrable (fun ω => (X ω) ^ 2) μ)
    (hexpint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (V * (Real.exp (t * b) - 1 - t * b) / b ^ 2) := by
  refine (mgf_le_one_add_bennett hbpos ht hX0 hb hvar hXint hXsqint hexpint).trans ?_
  have hX2 : 0 ≤ ∫ ω, (X ω) ^ 2 ∂μ := MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have hV : 0 ≤ V := hX2.trans hvar
  have hrem : 0 ≤ Real.exp (t * b) - 1 - t * b := by
    linarith [Real.add_one_le_exp (t * b)]
  have harg : 0 ≤ V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 := by positivity
  simpa [add_comm] using Real.add_one_le_exp
    (V * (Real.exp (t * b) - 1 - t * b) / b ^ 2)


/-- Bennett's exponent is bounded by the corresponding sub-gamma exponent. -/
private lemma bennett_exponent_le_subgamma {V b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t)
    (htb : t * b < 3) (hV : 0 ≤ V) :
    V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 ≤
      V * t ^ 2 / (2 * (1 - b / 3 * t)) := by
  have hbernstein := exp_sub_one_sub_le_bernstein (mul_nonneg ht hb.le) htb
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hb3eq : 1 - b / 3 * t = 1 - t * b / 3 := by ring
  rw [hb3eq]
  have hineq : (t * b) ^ 2 / (2 * (1 - t * b / 3)) / b ^ 2 =
      t ^ 2 / (2 * (1 - t * b / 3)) := by
    field_simp [hb.ne']
  calc
    V * (Real.exp (t * b) - 1 - t * b) / b ^ 2 =
        V * ((Real.exp (t * b) - 1 - t * b) / b ^ 2) := by ring
    _ ≤ V * ((t * b) ^ 2 / (2 * (1 - t * b / 3)) / b ^ 2) := by
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbernstein hb2.le) hV
    _ = V * (t ^ 2 / (2 * (1 - t * b / 3))) := by rw [hineq]
    _ = V * t ^ 2 / (2 * (1 - t * b / 3)) := by ring

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
  have hXsq : 0 ≤ μ[fun ω => (X ω) ^ 2] := integral_nonneg_of_ae (by
    filter_upwards with ω
    exact sq_nonneg _)
  exact hbennett.trans (Real.exp_le_exp.mpr
    (bennett_exponent_le_subgamma hbpos ht htbeq (hXsq.trans hvar)))

end Contrib.Bennett
