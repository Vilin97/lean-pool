/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Counterexample.Factor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The centroid and second origin identities

Two of the four identities of the blog post's Lemma 1 come from comparing the two
factorizations of `Sendov.Counterexample.Factor` coefficient by coefficient, or by evaluating
them at a point.  Neither needs any integration.

* the **centroid identity**, from the coefficient of `X^{n-2}` in `p'`, equivalently from
  `p.coeff (n-1)` and `p'.coeff (n-2)`;
* the **second origin identity**, from `p'(0)`.

Everything is stated **division-free**.  The blog post writes the second origin identity as

  `(-1)^{n-1} (∏ zⱼ) (1 + a ∑ⱼ 1/zⱼ) = (n / ∏ qⱼ) F(1)`,

with a convention that singularities are removed when some `zⱼ` vanishes.  Multiplying out,
`(∏ zⱼ)(∑ⱼ 1/zⱼ)` is `∑ⱼ ∏_{k≠j} z_k`, which is defined whether or not any `zⱼ` is zero, and
`∏ qⱼ` clears the other denominator.  So the convention becomes unnecessary rather than being
formalized: no junk value of `0⁻¹` is ever evaluated.

## Main statements

* `Sendov.sumEraseProd`: `∑ⱼ ∏_{k≠j} sₖ`, the division-free form of `(∏ s)(∑ 1/sⱼ)`;
* `Sendov.centroid_identity`;
* `Sendov.second_origin_identity`.
-/

public section

namespace Sendov

open Polynomial Multiset

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} sₖ`.  This is `(∏ s) · (∑ⱼ 1/sⱼ)` with the denominators cleared, and unlike
that expression it is well defined when some `sⱼ` vanishes. -/
@[expose]
noncomputable def sumEraseProd (s : Multiset ℂ) : ℂ :=
  (s.map (fun j => (s.erase j).prod)).sum

variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}

/-! ### Two rewritings of the factorizations -/

/-- The factorization of `p`, with `a` put back into the multiset. -/
lemma prod_cons_eq (a : ℂ) (z : Multiset ℂ) :
    (X - C a) * (z.map (fun w => X - C w)).prod
      = ((a ::ₘ z).map (fun w => X - C w)).prod := by
  rw [Multiset.map_cons, Multiset.prod_cons]

/-! ### The centroid identity -/

/-- **The centroid identity.**  `(n-1)(a + ∑ zⱼ) = n ∑ⱼ (a - 1/qⱼ)`: the centroid of the
zeroes equals the centroid of the critical points. -/
theorem centroid_identity (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by
  have hcard1 : (a ::ₘ z).card = n := by
    simp only [Multiset.card_cons, hzcard]
    omega
  have hcard2 : (q.map (fun v => a - v⁻¹)).card = n - 1 := by
    rw [Multiset.card_map, hqcard]
  -- the coefficient of `X^{n-1}` in `p`
  have hp1 : p.coeff (n - 1) = c * (-(a + z.sum)) := by
    rw [hpz, prod_cons_eq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (a ::ₘ z) (by rw [hcard1]; omega)
    rw [hcard1] at this
    rw [this, Multiset.sum_cons]
  -- the coefficient of `X^{n-2}` in `p'`
  have hp2 : (derivative p).coeff (n - 2)
      = (n : ℂ) * c * (-((q.map (fun v => a - v⁻¹)).sum)) := by
    rw [hpq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (q.map (fun v => a - v⁻¹))
      (by rw [hcard2]; omega)
    rw [hcard2] at this
    have hn2 : n - 1 - 1 = n - 2 := by omega
    rwa [hn2] at this
  -- and `p'.coeff (n-2) = (n-1) p.coeff (n-1)`
  have hlink : (derivative p).coeff (n - 2) = p.coeff (n - 1) * ((n : ℂ) - 1) := by
    have hsucc : n - 2 + 1 = n - 1 := by omega
    have h1 : ((n - 2 : ℕ) : ℂ) + 1 = (n : ℂ) - 1 := by
      have h2 : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rw [coeff_derivative, hsucc, h1]
  rw [hp1, hp2] at hlink
  refine mul_left_cancel₀ hc0 ?_
  linear_combination hlink

/-! ### The second origin identity -/

@[simp] lemma sumEraseProd_zero : sumEraseProd 0 = 0 := by simp [sumEraseProd]

open scoped Classical in
/-- Splitting off one element, exactly as `Multiset.esymm` does at the top index. -/
lemma sumEraseProd_cons (v : ℂ) (t : Multiset ℂ) :
    sumEraseProd (v ::ₘ t) = t.prod + v * sumEraseProd t := by
  simp only [sumEraseProd, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.prod_cons]

/-- Negating a multiset before taking the product. -/
lemma prod_map_neg (s : Multiset ℂ) :
    (s.map (fun w => -w)).prod = (-1) ^ (Multiset.card s) * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

/-- `∏ⱼ (X - zⱼ)` at the origin. -/
lemma eval_prod_zero (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ (Multiset.card z) * z.prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  rw [show (z.map ((fun r : ℂ[X] => r.eval 0) ∘ (fun w => X - C w))).prod
      = (z.map (fun w => -w)).prod from
    congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)]
  exact prod_map_neg z

/-- The derivative of `∏ⱼ (X - zⱼ)` at the origin.  Proved by induction rather than through
`Polynomial.derivative_prod`, which would need the evaluation of a multiset sum. -/
lemma eval_deriv_prod_zero : ∀ (z : Multiset ℂ),
    (derivative (z.map (fun w => X - C w)).prod).eval 0
      = -((-1) ^ (Multiset.card z) * sumEraseProd z) := by
  intro z
  induction z using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, zero_sub, Multiset.card_cons]
    rw [ih, eval_prod_zero, sumEraseProd_cons]
    ring

/-- `∏ⱼ (1/vⱼ - a) · ∏ⱼ vⱼ = ∏ⱼ (1 - a vⱼ)`: clearing the denominators of the `q`-side. -/
lemma prod_inv_sub_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹ - a)).prod * q.prod = (q.map (fun v => 1 - a * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp

open scoped Classical in
/-- **The second origin identity**, division-free.  The blog post's form
`(-1)^{n-1}(∏ zⱼ)(1 + a ∑ 1/zⱼ) = (n/∏ qⱼ) F(1)` after clearing both denominators. -/
theorem second_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by
  -- `p'(0)` from the `q`-side
  have hev1 : (derivative p).eval 0 = (n : ℂ) * c * (q.map (fun v => v⁻¹ - a)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp
  -- `p'(0)` from the `z`-side
  have hev2 : (derivative p).eval 0
      = c * ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, zero_sub, one_mul]
    rw [eval_deriv_prod_zero, eval_prod_zero, hzcard]
    ring
  -- combine and clear the denominators
  have hcancel : (n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod
      = (-1) ^ (n - 1) * (z.prod + a * sumEraseProd z) := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev1.symm.trans hev2
  calc (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (n : ℂ) * ((q.map (fun v => v⁻¹ - a)).prod * q.prod) := by
        rw [prod_inv_sub_mul q hq0]
    _ = ((n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod) * q.prod := by ring
    _ = ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by ring

/-! ### The integral representation -/

open MeasureTheory in
/-- The integrand of the representation below is continuous. -/
lemma continuous_deriv_seg (p : ℂ[X]) (a w : ℂ) :
    Continuous fun t : ℝ => (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  fun_prop

open MeasureTheory in
/-- **The integral representation.**  `p(w) = (w-a) ∫₀¹ p'(a + t(w-a)) dt` when `a` is a root
of `p`.  This is the fundamental theorem of calculus along the segment from `a` to `w`,
parametrized by a real variable; it replaces the blog post's `p(z) = (z-a)∫₀¹ n ∏ⱼ (t(z-a) +
1/qⱼ) dt`, which is the same statement with `p'` already factored. -/
lemma eval_eq_integral {p : ℂ[X]} {a : ℂ} (hpa : p.eval a = 0) (w : ℂ) :
    p.eval w = (w - a) * ∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p.eval (a + (s : ℂ) * (w - a)))
      ((w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (w - a)) (w - a) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using (h0.mul_const (w - a)).const_add a
    have h2 : HasDerivAt (fun u : ℂ => p.eval u)
        ((derivative p).eval (a + (t : ℂ) * (w - a))) (a + (t : ℂ) * (w - a)) :=
      p.hasDerivAt _
    have h3 := h2.scomp t h1
    simp only [Function.comp_def] at h3
    exact h3
  have hint : IntervalIntegrable
      (fun t : ℝ => (w - a) * (derivative p).eval (a + (t : ℂ) * (w - a))) volume 0 1 :=
    ((continuous_deriv_seg p a w).const_smul (w - a)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hint
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero, one_mul] at hFTC
  rw [show a + (w - a) = w from by ring, hpa, sub_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_const_mul]

/-! ### The first origin identity -/

open MeasureTheory in
/-- **The first origin identity**, division-free.  The blog post's
`(-1)^{n-1} ∏ zⱼ = (n / ∏ qⱼ) ∫₀¹ F(t) dt` with the denominator cleared, where
`F(t) = ∏ⱼ (1 - a t qⱼ)`. -/
theorem first_origin_identity {p : ℂ[X]} (hc0 : c ≠ 0) (ha0 : a ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0) (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * z.prod := by
  -- `p(0)` through the integral representation
  have hint : p.eval 0
      = -a * ∫ t in (0 : ℝ)..1,
          (n : ℂ) * c * (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod := by
    rw [eval_eq_integral hpa 0]
    congr 1
    · ring
    refine intervalIntegral.integral_congr ?_
    intro t _
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  -- `p(0)` from the `z`-side
  have hev : p.eval 0 = c * (-a) * ((-1) ^ (n - 1) * z.prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, zero_sub]
    rw [eval_prod_zero, hzcard]
    ring
  -- cancel `-a c` and clear the remaining denominator
  rw [intervalIntegral.integral_const_mul] at hint
  have hcancel : (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod
      = (-1) ^ (n - 1) * z.prod := by
    have hne : -a * c ≠ 0 := by simp [ha0, hc0]
    refine mul_left_cancel₀ hne ?_
    linear_combination hint.symm.trans hev
  calc (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod * q.prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [prod_inv_sub_mul q hq0]
        refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
        intro v _
        ring
    _ = ((n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod) * q.prod := by
        rw [intervalIntegral.integral_mul_const]
        ring
    _ = ((-1) ^ (n - 1) * z.prod) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * z.prod := by ring

/-! ### The polar identity -/

/-- Pulling a constant out of a product over a multiset. -/
lemma prod_map_mul_const (b : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map (fun v => b * f v)).prod = b ^ (Multiset.card s) * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

/-- `∏ⱼ (1/vⱼ) · ∏ⱼ vⱼ = 1`. -/
lemma prod_inv_mul : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹)).prod * q.prod = 1 := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp

/-- **`p'(a)` two ways.**  `(∏ⱼ qⱼ) ∏ⱼ (a - zⱼ) = n`.  This is what makes the polar identity
usable without dividing: it is the denominator of the blog post's
`∏ⱼ (1-azⱼ)/(a-zⱼ)`, expressed as a product. -/
theorem prod_sub_mul_prod (hc0 : c ≠ 0) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => a - w)).prod = (n : ℂ) := by
  have hev1 : (derivative p).eval a = (n : ℂ) * c * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  have hev2 : (derivative p).eval a = c * (z.map (fun w => a - w)).prod := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, sub_self, zero_mul,
      add_zero, one_mul, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  have hcancel : (z.map (fun w => a - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev2.symm.trans hev1
  calc q.prod * (z.map (fun w => a - w)).prod
      = q.prod * ((n : ℂ) * (q.map (fun v => v⁻¹)).prod) := by rw [hcancel]
    _ = (n : ℂ) * ((q.map (fun v => v⁻¹)).prod * q.prod) := by ring
    _ = (n : ℂ) := by rw [prod_inv_mul q hq0]; ring

open MeasureTheory in
/-- **The polar identity**, division-free.  The blog post's
`∏ⱼ (1-azⱼ)/(a-zⱼ) = ∫₀¹ ∏ⱼ (t(1-a²)qⱼ + a) dt` with the denominator cleared using
`Sendov.prod_sub_mul_prod`. -/
theorem polar_identity (hc0 : c ≠ 0) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => 1 - a * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
  have hinv : a⁻¹ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply ha2
    field_simp at h
    linear_combination -h
  -- `p(1/a)` through the integral representation
  have hint : p.eval a⁻¹
      = (a⁻¹ - a) * ((n : ℂ) * c * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
    rw [eval_eq_integral hpa a⁻¹]
    congr 1
    have hcong : (∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (a⁻¹ - a)))
        = ∫ t in (0 : ℝ)..1,
            (n : ℂ) * c * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      simp only []
      rw [hpq]
      simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      congr 1
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v _
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      ring
    rw [hcong, intervalIntegral.integral_const_mul]
  -- `p(1/a)` from the `z`-side
  have hev : p.eval a⁻¹ = c * ((a⁻¹ - a) * (z.map (fun w => a⁻¹ - w)).prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  -- cancel `c (1/a - a)`
  have hcancel : (z.map (fun w => a⁻¹ - w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    have hne : c * (a⁻¹ - a) ≠ 0 := mul_ne_zero hc0 hinv
    refine mul_left_cancel₀ hne ?_
    linear_combination hev.symm.trans hint
  -- restore the two products
  have hLHS : (z.map (fun w => 1 - a * w)).prod
      = a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod := by
    rw [← hzcard, ← prod_map_mul_const a z (fun w => a⁻¹ - w)]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    field_simp
  have hRHS : ∀ t : ℝ, (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
      = a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    intro t
    have h1 : (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
        = (q.map (fun v => a * (v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)))).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v hv
      have hv0 : v ≠ 0 := hq0 v hv
      field_simp
      ring
    rw [h1, prod_map_mul_const a q (fun v => v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)),
      Multiset.prod_map_mul, hqcard]
    have : (q.map (fun v => v)).prod = q.prod := by rw [Multiset.map_id']
    rw [this]
    ring
  rw [hLHS]
  calc q.prod * (a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod)
      = a ^ (n - 1) * q.prod
          * ((n : ℂ) * ∫ t in (0 : ℝ)..1,
              (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
        rw [hcancel]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
        rw [intervalIntegral.integral_const_mul]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [hRHS t]

end Sendov
