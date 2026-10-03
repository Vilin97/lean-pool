/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Analytic.Polar

/-!
# The low-degree branch: degrees `2 ≤ n ≤ 5`

The high-degree argument relaxes the branch point `(⋆)`,

  `1 ≤ ∫₀¹ ∏ⱼ ‖a + t(1-a²)qⱼ‖ dt`,

by AM–GM to the raw polar inequality `(1Q)`, and then needs the origin channel as well.  In low
degree none of that is necessary: bounding each factor of `(⋆)` by the *scalar*
`X(t) = a + (1-a²)t` already contradicts itself.

Writing `m = n - 1` for the number of non-distinguished zeroes and `J_m(a) = ∫₀¹ X(t)^m dt`,
the branch point gives `1 ≤ J_m(a)` while a direct computation gives `J_m(a) < 1` for
`0 < a < 1` and `1 ≤ m ≤ 4`.  The computation is done once, at `m = 4`:

  `1 - J₄(a) = ((1-a)³(1+a)/5)(a⁴ - 3a³ + 3a + 4)`,

whose last factor is `2 + 3a + (1-a)(2 + 2a + a²(2-a)) > 0`; the smaller exponents are dominated
by `X^m ≤ 1 - m/4 + (m/4)X⁴`, four instances of weighted AM–GM that factor as squares.

Note the off-by-one: `m ≤ 4` is degree `n ≤ 5`, so this branch covers degree five as well.  All
strictness comes from `a < 1`; at `a = 1` one has `J_m(1) = 1`, matching the regular-polygon
equality examples.

## Main statements

* `Sendov.low_degree_contradiction`: `(⋆)` is contradictory for `2 ≤ n ≤ 5`;
* `Sendov.lowJ_lt_one`: `J_m(a) < 1` for `0 < a < 1` and `1 ≤ m ≤ 4`.
-/

public section

namespace Sendov

/-! ### The scalar chord and its moments -/

/-- `X(t) = a + (1-a²)t`, the pointwise majorant of `‖a + t(1-a²)qⱼ‖`. -/
noncomputable def lowX (a t : ℝ) : ℝ := a + (1 - a ^ 2) * t

/-- `J_m(a) = ∫₀¹ X(t)^m dt`. -/
noncomputable def lowJ (m : ℕ) (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, lowX a t ^ m

lemma lowX_nonneg {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) : 0 ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  simp only [lowX]
  positivity

lemma continuous_lowX_pow (a : ℝ) (m : ℕ) : Continuous fun t : ℝ => lowX a t ^ m := by
  simp only [lowX]
  fun_prop

/-! ### The branch point, bounded factor by factor -/

lemma norm_le_lowX {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hcast : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v
      = ((a : ℝ) : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * v := by push_cast; ring
  rw [hcast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg ht0 hb)]
  simp only [lowX]
  nlinarith [hv, norm_nonneg v, mul_nonneg ht0 hb]

lemma prod_norm_le_lowX_pow {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) :
    ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t ^ q.card := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v s ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v s)
    have hs : ∀ u ∈ s, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    have hX0 : 0 ≤ lowX a t := lowX_nonneg ha0 ha1 ht0
    have h3 : 0 ≤ (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod :=
      prod_map_norm_nonneg s _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖
          * (s.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
        ≤ lowX a t * lowX a t ^ s.card :=
          mul_le_mul (norm_le_lowX ha0 ha1 ht0 hv) (ih hs) h3 hX0
      _ = lowX a t ^ s.card * lowX a t := by ring

/-- The branch point `(⋆)`, with every factor replaced by the scalar `X(t)`. -/
theorem one_le_lowJ {n : ℕ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    1 ≤ lowJ (n - 1) a := by
  refine hstar.trans ?_
  rw [lowJ]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_prod_norm a q).intervalIntegrable _ _)
    ((continuous_lowX_pow a (n - 1)).intervalIntegrable _ _) ?_
  intro u hu
  have h := prod_norm_le_lowX_pow ha0 ha1 hu.1 q hq1
  rwa [hqcard] at h

/-! ### The fourth moment -/

/-- `J₄(a)`, by the fundamental theorem of calculus against an explicit antiderivative.  The
antiderivative is written without dividing by `1 - a²`, so no side condition on `a` appears. -/
lemma lowJ_four (a : ℝ) :
    lowJ 4 a = a ^ 4 + 2 * a ^ 3 * (1 - a ^ 2) + 2 * a ^ 2 * (1 - a ^ 2) ^ 2
      + a * (1 - a ^ 2) ^ 3 + (1 - a ^ 2) ^ 4 / 5 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ =>
      a ^ 4 * s + 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2 + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3
        + a * (1 - a ^ 2) ^ 3 * s ^ 4 + (1 - a ^ 2) ^ 4 / 5 * s ^ 5) (lowX a t ^ 4) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a ^ 4 * s) (a ^ 4 * 1) t :=
      (hasDerivAt_id' (x := t)).const_mul _
    have h2 : HasDerivAt (fun s : ℝ => 2 * a ^ 3 * (1 - a ^ 2) * s ^ 2)
        (2 * a ^ 3 * (1 - a ^ 2) * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (2 * a ^ 3 * (1 - a ^ 2))
    have h3 : HasDerivAt (fun s : ℝ => 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * s ^ 3)
        (2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2)) t := by
      simpa using (hasDerivAt_pow 3 t).const_mul (2 * a ^ 2 * (1 - a ^ 2) ^ 2)
    have h4 : HasDerivAt (fun s : ℝ => a * (1 - a ^ 2) ^ 3 * s ^ 4)
        (a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)) t := by
      simpa using (hasDerivAt_pow 4 t).const_mul (a * (1 - a ^ 2) ^ 3)
    have h5 : HasDerivAt (fun s : ℝ => (1 - a ^ 2) ^ 4 / 5 * s ^ 5)
        ((1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4)) t := by
      simpa using (hasDerivAt_pow 5 t).const_mul ((1 - a ^ 2) ^ 4 / 5)
    have hval : lowX a t ^ 4 = a ^ 4 * 1 + 2 * a ^ 3 * (1 - a ^ 2) * (2 * t)
        + 2 * a ^ 2 * (1 - a ^ 2) ^ 2 * (3 * t ^ 2) + a * (1 - a ^ 2) ^ 3 * (4 * t ^ 3)
        + (1 - a ^ 2) ^ 4 / 5 * (5 * t ^ 4) := by
      simp only [lowX]
      ring
    rw [hval]
    exact ((((h1.add h2).add h3).add h4).add h5)
  rw [lowJ, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((continuous_lowX_pow a 4).intervalIntegrable _ _)]
  norm_num

lemma lowJ_four_identity (a : ℝ) :
    1 - lowJ 4 a = ((1 - a) ^ 3 * (1 + a) / 5) * (a ^ 4 - 3 * a ^ 3 + 3 * a + 4) := by
  rw [lowJ_four]
  ring

lemma quartic_aux_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hfactor : a ^ 4 - 3 * a ^ 3 + 3 * a + 4
      = 2 + 3 * a + (1 - a) * (2 + 2 * a + a ^ 2 * (2 - a)) := by ring
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 2 - a := by linarith
  rw [hfactor]
  positivity

lemma lowJ_four_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : lowJ 4 a < 1 := by
  have haux := quartic_aux_pos ha0 ha1
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 1 + a := by linarith
  rw [← sub_pos, lowJ_four_identity]
  positivity

/-! ### Dominating exponents one through four by the fourth -/

/-- `X^m ≤ 1 - m/4 + (m/4)X⁴` for `0 ≤ X` and `1 ≤ m ≤ 4`: weighted AM–GM, but at these four
exponents each instance factors as a square times a positive quadratic. -/
lemma pow_le_quartic_average {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    x ^ m ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * x ^ 4 := by
  interval_cases m
  · -- `m = 1`:  `X⁴ - 4X + 3 = (X-1)²(X² + 2X + 3)`
    have hpos : (0 : ℝ) ≤ x ^ 2 + 2 * x + 3 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 2`:  `X⁴ - 2X² + 1 = (X² - 1)²`
    norm_num
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  · -- `m = 3`:  `3X⁴ - 4X³ + 1 = (X-1)²(3X² + 2X + 1)`
    have hpos : (0 : ℝ) ≤ 3 * x ^ 2 + 2 * x + 1 := by positivity
    norm_num
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) hpos]
  · -- `m = 4`: equality
    norm_num

theorem lowJ_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℕ} (hm0 : 1 ≤ m) (hm4 : m ≤ 4) :
    lowJ m a < 1 := by
  have hcont4 := continuous_lowX_pow a 4
  have hcontm := continuous_lowX_pow a m
  have hmaj : Continuous fun t : ℝ => 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4 :=
    continuous_const.add (hcont4.const_mul _)
  have hint : (∫ t in (0 : ℝ)..1, (1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowX a t ^ 4))
      = 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      ((hcont4.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul, lowJ]
    simp
  have hle : lowJ m a ≤ 1 - (m : ℝ) / 4 + (m : ℝ) / 4 * lowJ 4 a := by
    rw [lowJ, ← hint]
    refine intervalIntegral.integral_mono_on (by norm_num) (hcontm.intervalIntegrable _ _)
      (hmaj.intervalIntegrable _ _) ?_
    intro u hu
    exact pow_le_quartic_average (lowX_nonneg (le_of_lt ha0) (le_of_lt ha1) hu.1) hm0 hm4
  have h4 := lowJ_four_lt_one ha0 ha1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  nlinarith [hle, h4, hmpos]

/-! ### The contradiction -/

/-- **The low-degree branch.**  The branch point `(⋆)` is already contradictory for
`2 ≤ n ≤ 5`, with no recourse to the origin channel. -/
theorem low_degree_contradiction {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hstar : 1 ≤ ∫ t in (0 : ℝ)..1,
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod) :
    False := by
  have h1 := one_le_lowJ (n := n) (le_of_lt ha0) (le_of_lt ha1) hqcard hq1 hstar
  have h2 := lowJ_lt_one ha0 ha1 (m := n - 1) (by omega) (by omega)
  linarith

end Sendov
