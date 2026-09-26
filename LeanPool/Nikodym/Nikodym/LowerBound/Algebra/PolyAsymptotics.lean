/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic

/-!
# Elementary asymptotics of rational polynomials along `ℕ`

This file implements the field-free polynomial lemmas of blueprint node **A04′** (consumed by
**B02** and **A04′** itself): comparing two polynomials `p, q : ℚ[X]` at all large natural
numbers controls their coefficients in degree `n` whenever both have `natDegree ≤ n`, and a
sandwich between two polynomials of `natDegree ≤ n` forces `natDegree ≤ n`. We also compute the
degree-`n` coefficient of the difference `p - p.comp (X - C e)` for `natDegree p ≤ n + 1`.

Main declarations (all in the `Polynomial` namespace, as named in the design document):

* `Polynomial.eventually_eval_natCast_neg_of_leadingCoeff_neg`: a polynomial with negative
  leading coefficient is eventually negative along `ℕ`.
* `Polynomial.coeff_nonneg_of_eventually_nonneg`: `natDegree p ≤ n` and `p(t) ≥ 0` for all large
  `t : ℕ` give `0 ≤ p.coeff n`.
* `Polynomial.coeff_le_coeff_of_eventually_le`: the two-polynomial version.
* `Polynomial.natDegree_le_of_eventually_between`: the sandwich degree bound.
* `Polynomial.coeff_sub_comp_X_sub_C`: `(p - p.comp (X - C e)).coeff n = (n + 1) e p.coeff (n+1)`.
* Conveniences `Polynomial.natDegree_comp_X_sub_C`, `Polynomial.leadingCoeff_comp_X_sub_C`,
  `Polynomial.eval_comp_X_sub_C`, `Polynomial.eval_comp_X_sub_C_natCast`.
-/

@[expose] public section

namespace Polynomial

open Filter

/-! ### Sign of a polynomial at large natural numbers -/

/-- Blueprint A04′ (polynomial lemmas): a rational polynomial with negative leading coefficient
is negative at all large natural numbers. -/
theorem eventually_eval_natCast_neg_of_leadingCoeff_neg {p : ℚ[X]} (hp : p.leadingCoeff < 0) :
    ∀ᶠ t : ℕ in atTop, p.eval (t : ℚ) < 0 := by
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · refine Eventually.of_forall fun t ↦ ?_
    rw [eq_C_of_natDegree_eq_zero h0, eval_C]
    simpa [leadingCoeff, h0] using hp
  · have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hpos
    have := (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hp.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))
    exact this.eventually_lt_atBot 0

/-- Blueprint A04′ (polynomial lemmas): if `natDegree p ≤ n` and `p (t) ≥ 0` for all large
`t : ℕ`, then `0 ≤ p.coeff n`. -/
theorem coeff_nonneg_of_eventually_nonneg {p : ℚ[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (h : ∀ᶠ t : ℕ in atTop, 0 ≤ p.eval (t : ℚ)) : 0 ≤ p.coeff n := by
  by_contra hneg
  rw [not_le] at hneg
  have hn : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hp hneg.ne
  have hlc : p.leadingCoeff < 0 := by rwa [leadingCoeff, hn]
  obtain ⟨t, ht₁, ht₂⟩ :=
    (h.and (eventually_eval_natCast_neg_of_leadingCoeff_neg hlc)).exists
  exact absurd (ht₁.trans_lt ht₂) (lt_irrefl _)

/-- Blueprint A04′ (polynomial lemmas): if `natDegree p, natDegree q ≤ n` and `p (t) ≤ q (t)`
for all large `t : ℕ`, then `p.coeff n ≤ q.coeff n`. -/
theorem coeff_le_coeff_of_eventually_le {p q : ℚ[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) (h : ∀ᶠ t : ℕ in atTop, p.eval (t : ℚ) ≤ q.eval (t : ℚ)) :
    p.coeff n ≤ q.coeff n := by
  have hd : (q - p).natDegree ≤ n := (natDegree_sub_le q p).trans (max_le hq hp)
  have := coeff_nonneg_of_eventually_nonneg hd (h.mono fun t ht ↦ by rw [eval_sub]; linarith)
  rw [coeff_sub] at this
  linarith

/-- Blueprint A04′ (polynomial lemmas): a polynomial eventually sandwiched (along `ℕ`) between
two polynomials of `natDegree ≤ n` has `natDegree ≤ n`. -/
theorem natDegree_le_of_eventually_between {p q₁ q₂ : ℚ[X]} {n : ℕ} (h₁ : q₁.natDegree ≤ n)
    (h₂ : q₂.natDegree ≤ n)
    (h : ∀ᶠ t : ℕ in atTop, q₁.eval (t : ℚ) ≤ p.eval (t : ℚ) ∧ p.eval (t : ℚ) ≤ q₂.eval (t : ℚ)) :
    p.natDegree ≤ n := by
  by_contra hlt
  rw [not_le] at hlt
  set m := p.natDegree with hm
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp [hm] at hlt
  have hq₁ : q₁.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (h₁.trans_lt hlt)
  have hq₂ : q₂.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (h₂.trans_lt hlt)
  have hlow := coeff_le_coeff_of_eventually_le (h₁.trans hlt.le) le_rfl (h.mono fun _ ht ↦ ht.1)
  have hupp := coeff_le_coeff_of_eventually_le le_rfl (h₂.trans hlt.le) (h.mono fun _ ht ↦ ht.2)
  have : p.coeff m = 0 := le_antisymm (hq₂ ▸ hupp) (hq₁ ▸ hlow)
  exact leadingCoeff_ne_zero.mpr hp0 this

/-! ### Shifting the variable by a constant -/

section Shift

variable {R : Type*} [CommRing R]

/-- Blueprint A04′ (polynomial lemmas): `(p.comp (X - C e)).eval x = p.eval (x - e)`. -/
theorem eval_comp_X_sub_C (p : R[X]) (e x : R) : (p.comp (X - C e)).eval x = p.eval (x - e) := by
  rw [eval_comp, eval_sub, eval_X, eval_C]

/-- Blueprint A04′ (polynomial lemmas): for `e ≤ t` in `ℕ`, `(p.comp (X - C e)).eval t` is the
value of `p` at the natural number `t - e`. -/
theorem eval_comp_X_sub_C_natCast (p : R[X]) {t e : ℕ} (h : e ≤ t) :
    (p.comp (X - C (e : R))).eval (t : R) = p.eval ((t - e : ℕ) : R) := by
  rw [eval_comp_X_sub_C, Nat.cast_sub h]

variable [IsDomain R]

/-- Blueprint A04′ (polynomial lemmas): shifting the variable preserves the degree. -/
theorem natDegree_comp_X_sub_C (p : R[X]) (e : R) : (p.comp (X - C e)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_sub_C, mul_one]

/-- Blueprint A04′ (polynomial lemmas): shifting the variable preserves the leading coefficient. -/
theorem leadingCoeff_comp_X_sub_C (p : R[X]) (e : R) :
    (p.comp (X - C e)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; exact one_ne_zero), leadingCoeff_X_sub_C,
    one_pow, mul_one]

end Shift

/-- Blueprint A04′ (polynomial lemmas): the coefficient of `X ^ n` in `(X - C e) ^ i`. -/
theorem coeff_X_sub_C_pow' {R : Type*} [CommRing R] (e : R) (i n : ℕ) :
    ((X - C e) ^ i).coeff n = (-e) ^ (i - n) * (i.choose n : R) := by
  rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]

/-- Blueprint A04′ (polynomial lemmas): for `natDegree p ≤ n + 1`, the coefficient of `X ^ n` in
`p - p.comp (X - C e)` is `(n + 1) * e * p.coeff (n + 1)`: only the top term
`p.coeff (n + 1) * X ^ (n + 1)` contributes, through the binomial expansion of
`(X - e) ^ (n + 1)`. -/
theorem coeff_sub_comp_X_sub_C {p : ℚ[X]} {n : ℕ} (hp : p.natDegree ≤ n + 1) (e : ℚ) :
    (p - p.comp (X - C e)).coeff n = (n + 1) * e * p.coeff (n + 1) := by
  have key : ∀ i ∈ Finset.range (n + 2),
      (C (p.coeff i) * X ^ i - (C (p.coeff i) * X ^ i).comp (X - C e)).coeff n =
        if i = n + 1 then (n + 1) * e * p.coeff (n + 1) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [mul_comp, C_comp, X_pow_comp, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow,
      coeff_X_sub_C_pow']
    rcases lt_trichotomy i n with hlt | rfl | hgt
    · rw [ite_eq_right hlt.ne', ite_eq_right (by omega), Nat.choose_eq_zero_of_lt hlt]
      simp
    · simp
    · have hi' : i = n + 1 := by omega
      subst hi'
      rw [ite_eq_left rfl, ite_eq_right (by omega), Nat.add_sub_cancel_left,
        Nat.choose_succ_self_right]
      push_cast
      ring
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)]
  rw [← coe_compRingHom_apply, map_sum, ← Finset.sum_sub_distrib, finsetSum_coeff]
  simp only [coe_compRingHom_apply]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (Finset.range (n + 2)) (n + 1),
    ite_eq_left (Finset.mem_range.mpr (by omega))]

end Polynomial

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
