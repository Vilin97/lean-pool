/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanPool.PebblingLean.FiniteProbability

/-!
# Finite concentration inequalities

The upper-bound proof only uses uniform probability on finite sample spaces.
This file proves the finite Markov/Chernoff mechanism in that setting, with
real-valued expectations so that exponential moment bounds can be stated
directly.
-/

namespace PebblingLean

namespace FiniteProbability

variable {Ω : Type*}

/-- Uniform probability of an event on a finite sample space, as a real number. -/
noncomputable def uniformProbabilityReal [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

/-- Uniform expectation of a real-valued random variable on a finite sample
space. -/
noncomputable def uniformExpectationReal [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

theorem uniformProbabilityReal_eq_coe_uniformProbability [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    uniformProbabilityReal P = (uniformProbability P : ℝ) := by
  simp [uniformProbabilityReal, uniformProbability]

theorem uniformProbability_le_of_uniformProbabilityReal_le [Fintype Ω]
    {P : Ω → Prop} [DecidablePred P] {eps : ℚ}
    (h : uniformProbabilityReal P ≤ (eps : ℝ)) :
    uniformProbability P ≤ eps := by
  have hcast : ((uniformProbability P : ℚ) : ℝ) ≤ (eps : ℝ) := by
    simpa [uniformProbabilityReal_eq_coe_uniformProbability] using h
  exact_mod_cast hcast

/-- Finite Markov inequality for uniform probability.  The event is allowed to
be any predicate implied by `a ≤ X`. -/
theorem uniformProbabilityReal_le_expect_div_of_event_le [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (X : Ω → ℝ) {a : ℝ}
    (ha : 0 < a) (hnonneg : ∀ ω : Ω, 0 ≤ X ω)
    (hP : ∀ ω : Ω, P ω → a ≤ X ω) :
    uniformProbabilityReal P ≤ uniformExpectationReal X / a := by
  classical
  let bad : Finset Ω := Finset.univ.filter P
  have hsum_a_le : (∑ ω ∈ bad, a) ≤ ∑ ω ∈ bad, X ω := by
    exact Finset.sum_le_sum fun ω hω =>
      hP ω (by simpa [bad] using (Finset.mem_filter.mp hω).2)
  have hsum_bad_le_univ : (∑ ω ∈ bad, X ω) ≤ ∑ ω : Ω, X ω := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [bad])
      (fun ω _hω _hnot => hnonneg ω)
  have hcard_mul_a_le_sum : (bad.card : ℝ) * a ≤ ∑ ω : Ω, X ω := by
    have hsum_const : (∑ _ω ∈ bad, a) = (bad.card : ℝ) * a := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← hsum_const]
    exact hsum_a_le.trans hsum_bad_le_univ
  have hcard_pos : 0 < (Fintype.card Ω : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hden_pos : 0 < (Fintype.card Ω : ℝ) * a := mul_pos hcard_pos ha
  have hrewrite : (bad.card : ℝ) / (Fintype.card Ω : ℝ) =
      ((bad.card : ℝ) * a) / ((Fintype.card Ω : ℝ) * a) := by
    field_simp [ha.ne', hcard_pos.ne']
  unfold uniformProbabilityReal uniformExpectationReal
  change (bad.card : ℝ) / (Fintype.card Ω : ℝ) ≤
    (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ) / a
  rw [hrewrite, div_div]
  exact div_le_div_of_nonneg_right hcard_mul_a_le_sum hden_pos.le

/-- Chernoff's exponential-moment step for a lower tail, proved here as
Markov's inequality applied to `exp(λ(T - X))`. -/
theorem uniformProbabilityReal_lt_le_exponentialMoment [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤
      uniformExpectationReal fun ω : Ω => Real.exp (lam * (T - X ω)) := by
  classical
  have hmarkov :=
    uniformProbabilityReal_le_expect_div_of_event_le
      (P := fun ω : Ω => X ω < T)
      (X := fun ω : Ω => Real.exp (lam * (T - X ω)))
      (a := 1)
      (by norm_num)
      (fun ω => Real.exp_nonneg _)
      (fun ω hlt => by
        have hdiff : 0 < T - X ω := sub_pos.mpr hlt
        have harg : 0 < lam * (T - X ω) := mul_pos hlam hdiff
        have hexp : Real.exp 0 < Real.exp (lam * (T - X ω)) :=
          Real.exp_lt_exp.mpr harg
        simpa using hexp.le)
  simpa using hmarkov

theorem uniformProbabilityReal_lt_le_of_exponentialMoment_le [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam B : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤ B) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ B :=
  (uniformProbabilityReal_lt_le_exponentialMoment X hlam).trans hmoment

theorem uniformProbabilityReal_lt_le_exp_neg_of_exponentialMoment_le [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam exponent : ℝ} (hlam : 0 < lam)
    (hmoment :
      uniformExpectationReal (fun ω : Ω => Real.exp (lam * (T - X ω))) ≤
        Real.exp (-exponent)) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤ Real.exp (-exponent) :=
  uniformProbabilityReal_lt_le_of_exponentialMoment_le X hlam hmoment

/-- Convexity of the exponential gives the chord bound used for bounded
nonnegative summands: on `0 ≤ z ≤ B`, `exp(-λ z)` is below the chord joining
`0` and `B`. -/
theorem exp_neg_mul_le_chord {lam B z : ℝ}
    (hB : 0 < B) (hz0 : 0 ≤ z) (hzB : z ≤ B) :
    Real.exp (-(lam * z)) ≤
      1 - (1 - Real.exp (-(lam * B))) * (z / B) := by
  let w : Fin 2 → ℝ := fun i => if i = 0 then 1 - z / B else z / B
  let p : Fin 2 → ℝ := fun i => if i = 0 then 0 else -(lam * B)
  have hw_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ w i := by
    intro i _hi
    fin_cases i
    · change 0 ≤ 1 - z / B
      exact sub_nonneg.mpr (div_le_one_of_le₀ hzB hB.le)
    · change 0 ≤ z / B
      exact div_nonneg hz0 hB.le
  have hw_sum : (∑ i : Fin 2, w i) = 1 := by
    simp [w]
  have hp_mem : ∀ i ∈ (Finset.univ : Finset (Fin 2)), p i ∈ Set.univ := by
    simp
  have hconv := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset (Fin 2))) (w := w) (p := p)
    hw_nonneg (by simpa using hw_sum) hp_mem
  have harg : (∑ i : Fin 2, w i • p i) = -(lam * z) := by
    simp [w, p]
    field_simp [hB.ne']
  have hrhs : (∑ i : Fin 2, w i • Real.exp (p i)) =
      1 - (1 - Real.exp (-(lam * B))) * (z / B) := by
    simp [w, p]
    ring
  rw [harg, hrhs] at hconv
  exact hconv

/-- A scalar lower bound for `1 - exp(-x)` that follows from `1 + x ≤ exp x`.
This is the elementary replacement for the usual Taylor estimate in the
bounded-nonnegative Chernoff optimization. -/
theorem one_sub_exp_neg_ge_sub_sq {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ 1 - Real.exp (-x) := by
  have hxden : 0 < 1 + x := by positivity
  have hexp_inv : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    have h := Real.add_one_le_exp x
    have hpos : 0 < Real.exp x := Real.exp_pos x
    have hinv := (inv_le_inv₀ hpos hxden).mpr (by simpa [add_comm] using h)
    simpa [Real.exp_neg] using hinv
  have hpoly : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
    rw [← one_div, div_le_iff₀ hxden]
    nlinarith [sq_nonneg x, mul_nonneg hx (sq_nonneg x)]
  linarith

theorem one_sub_le_exp_neg (u : ℝ) :
    1 - u ≤ Real.exp (-u) := by
  have h := Real.add_one_le_exp (-u)
  linarith

/-- If a nonnegative one-step moment is at most `1-u`, then its `N`-fold
product is at most `exp(-N u)`.  This is the product step in the
bounded-nonnegative Chernoff argument. -/
theorem pow_le_exp_neg_mul_of_le_one_sub {a u : ℝ} (N : ℕ)
    (ha_nonneg : 0 ≤ a) (ha_le : a ≤ 1 - u) :
    a ^ N ≤ Real.exp (-((N : ℝ) * u)) := by
  have ha_exp : a ≤ Real.exp (-u) := ha_le.trans (one_sub_le_exp_neg u)
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hexp_nonneg : 0 ≤ Real.exp (-((N : ℝ) * u)) := Real.exp_nonneg _
      calc
        a ^ (N + 1) = a ^ N * a := by
          rw [pow_succ]
        _ ≤ Real.exp (-((N : ℝ) * u)) * Real.exp (-u) := by
          exact mul_le_mul ih ha_exp ha_nonneg hexp_nonneg
        _ = Real.exp (-(((N + 1 : ℕ) : ℝ) * u)) := by
          rw [← Real.exp_add]
          norm_num
          ring_nf

/-- Algebraic optimization for the chord-based bounded-nonnegative Chernoff
bound.  If `mu` exceeds the threshold `T` by `gap`, then the choice
`λ = gap/(2 B mu)` gives the usual quadratic exponent. -/
theorem exp_chord_quadratic_optimized {T gap B mu lam : ℝ}
    (hB : 0 < B) (hmu : 0 < mu) (hgap : 0 ≤ gap)
    (hmean : T + gap ≤ mu)
    (hlam : lam = gap / (2 * B * mu)) :
    Real.exp (lam * T - (lam - lam ^ 2 * B) * mu) ≤
      Real.exp (-(gap ^ 2 / (4 * B * mu))) := by
  apply Real.exp_le_exp.mpr
  subst lam
  have hden_pos : 0 < 2 * B * mu := by positivity
  have hBmu_pos : 0 < B * mu := mul_pos hB hmu
  have hgap_le : gap ≤ mu - T := by linarith
  have hmain :
      gap * T ≤ gap * mu - gap ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hgap_le hgap]
  field_simp [hden_pos.ne', hB.ne', hmu.ne', hBmu_pos.ne']
  ring_nf
  nlinarith

/-- A convenient way to discharge the hypercube union bound: an exponent at
least `(n+1) log 2` makes the fixed-target failure probability at most
`2^-(n+1)`. -/
theorem exp_neg_le_inv_two_pow_succ_of_log_le (n : ℕ) {exponent : ℝ}
    (hlog : ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ exponent) :
    Real.exp (-exponent) ≤
      (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
  have hfirst :
      Real.exp (-exponent) ≤
        Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hlog)
  have heq :
      Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2)) =
        (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
    calc
      Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2))
          = (Real.exp ((((n + 1 : ℕ) : ℝ) * Real.log 2)))⁻¹ := by
            rw [Real.exp_neg]
      _ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
            have hcast :
                (((2 ^ (n + 1) : ℚ) : ℝ) = (2 : ℝ) ^ (n + 1)) := by
              norm_num
            simp only [Rat.cast_div, Rat.cast_one]
            rw [hcast]
            rw [one_div]
  exact hfirst.trans_eq heq

end FiniteProbability

end PebblingLean
