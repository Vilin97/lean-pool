/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Counterexample.Factor
public import LeanPool.Sendov.Counterexample.Identities
public import LeanPool.Sendov.Analytic.Jsum

/-!
# Rubinstein's boundary theorem, at the zero `a = 1`

If `p` has degree `n ≥ 2`, all zeroes in the closed unit disk, and `p(1) = 0`, then `p'` has a
zero strictly inside `D(1,1)` **unless** `p = c(Xⁿ - 1)`.

The polar identity is useless here: at `a = 1` the reflected point `1/a` coincides with `a`,
`1 - a² = 0`, and the identity degenerates.  One elementary identity replaces it, obtained from
`p''(1)/p'(1)`.  Writing `p = c(X-1)Q` and `p' = ncR`, evaluation at `1` gives

  `Q(1) = n R(1)`  and  `2 Q'(1) = n R'(1)`

— the factor `2` coming from `p''(1) = 2Q'(1)` — whence the **boundary reciprocal identity**

  `∑ⱼ qⱼ = 2 ∑ⱼ 1/(1 - zⱼ)`,   `qⱼ = 1/(1 - wⱼ)`.

Both sides are then sandwiched.  On the left `Re qⱼ ≤ ‖qⱼ‖ ≤ 1`, so the real part is at most
`n-1`; on the right `Re 1/(1-z) ≥ 1/2` for `‖z‖ ≤ 1`, because
`Re 1/(1-z) - 1/2 = (1-‖z‖²)/(2‖1-z‖²)`, so the real part is at least `n-1`.  Equality forces
`Re qⱼ = 1` for every `j`, hence `qⱼ = 1`, hence every critical point is `0`, hence
`p' = n c Xⁿ⁻¹` and `p = c(Xⁿ - 1)`.

The repeated-root case is handled before any division: if `1` is a multiple zero then `p'(1) = 0`
and `ζ = 1` is a strict witness, so under the contradiction hypothesis `p'(1) ≠ 0` and every
`zⱼ ≠ 1`.

No polar integral, origin identity, defect lemma, numerical certificate or Gauss–Lucas theorem
is used.  Only the two factorizations of `Sendov.Counterexample.Factor` are shared with the
interior argument.

## Main statements

* `Sendov.rubinstein_one`: the strict-or-extremal alternative;
* `Sendov.sendov_boundary_one`: the closed-disk form, `‖ζ - 1‖ ≤ 1`;
* `Sendov.boundary_reciprocal`: `(BR)`, in division-free form.
-/

public section

namespace Sendov

open Polynomial

/-! ### Evaluating `∏ⱼ (X - zⱼ)` and its derivative at a point

The versions in `Sendov.Counterexample.Identities` are specialized to the origin; the boundary
argument needs them at `1`. -/

lemma eval_prod_at (u : ℂ) (s : Multiset ℂ) :
    ((s.map (fun w => X - C w)).prod).eval u = (s.map (fun w => u - w)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)

lemma eval_deriv_prod_at (u : ℂ) : ∀ (s : Multiset ℂ),
    (derivative (s.map (fun w => X - C w)).prod).eval u
      = sumEraseProd (s.map (fun w => u - w)) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C]
    rw [ih, eval_prod_at, sumEraseProd_cons]

/-! ### Scalar facts -/

/-- **The disk inequality.**  `Re 1/(1-z) ≥ 1/2` for `‖z‖ ≤ 1`, `z ≠ 1`; after clearing the
positive denominator this is exactly `1 - ‖z‖² ≥ 0`. -/
lemma half_le_re_inv_one_sub {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    (1 : ℝ) / 2 ≤ (((1 : ℂ) - z)⁻¹).re := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hd : 0 < Complex.normSq ((1 : ℂ) - z) := Complex.normSq_pos.2 hne
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [hz, norm_nonneg z, h]
  rw [Complex.inv_re, le_div_iff₀ hd, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [hsq]

/-- A point of the closed unit disk with real part `1` is `1`. -/
lemma eq_one_of_re_eq_one_of_norm_le_one {v : ℂ} (hre : v.re = 1) (hv : ‖v‖ ≤ 1) : v = 1 := by
  have hsq : v.re ^ 2 + v.im ^ 2 ≤ 1 := by
    have h := Complex.normSq_eq_norm_sq v
    rw [Complex.normSq_apply] at h
    nlinarith [hv, norm_nonneg v, h]
  have him : v.im = 0 := by nlinarith [hsq, hre, sq_nonneg v.im]
  apply Complex.ext <;> simp [hre, him]

/-- A multiset of nonnegative reals summing to zero is all zeroes. -/
lemma eq_zero_of_sum_eq_zero {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (h : s.sum = 0) :
    ∀ x ∈ s, x = 0 := by
  intro x hx
  have hsplit : s.sum = x + (s.erase x).sum := by
    conv_lhs => rw [← Multiset.cons_erase hx]
    rw [Multiset.sum_cons]
  have hrest : 0 ≤ (s.erase x).sum :=
    Multiset.sum_nonneg fun y hy => hs y (Multiset.mem_of_mem_erase hy)
  rw [hsplit] at h
  have := hs x hx
  linarith

lemma sum_le_card_mul (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, x ≤ c) →
    s.sum ≤ (s.card : ℝ) * c := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

lemma card_mul_le_sum (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, c ≤ x) →
    (s.card : ℝ) * c ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, c ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

lemma sum_map_one_sub_re (s : Multiset ℂ) :
    (s.map (fun v => 1 - v.re)).sum = (s.card : ℝ) - (s.map (fun v => v.re)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

/-! ### The boundary reciprocal identity -/

/-- **`(BR)`, in division-free form.**  From `∏ Zs = n ∏ Qi` and `2 ∑ₑ Zs = n ∑ₑ Qi` — the two
readings of `p'(1)` and `p''(1)` — one gets `∑ⱼ 1/Qiⱼ = 2 ∑ⱼ 1/Zsⱼ`.  Applied with
`Zsⱼ = 1 - zⱼ` and `Qiⱼ = 1/qⱼ` this is `∑ⱼ qⱼ = 2 ∑ⱼ 1/(1-zⱼ)`. -/
theorem boundary_reciprocal {n : ℕ} {Zs Qi : Multiset ℂ} (hn0 : (n : ℂ) ≠ 0)
    (hZ : ∀ u ∈ Zs, u ≠ 0) (hQ : ∀ u ∈ Qi, u ≠ 0)
    (hI : Zs.prod = (n : ℂ) * Qi.prod)
    (hII : 2 * sumEraseProd Zs = (n : ℂ) * sumEraseProd Qi) :
    (Qi.map (fun u => u⁻¹)).sum = 2 * (Zs.map (fun u => u⁻¹)).sum := by
  have hQ0 : Qi.prod ≠ 0 := Multiset.prod_ne_zero fun h => hQ 0 h rfl
  have h1 := prod_mul_sum_inv Zs hZ
  have h2 := prod_mul_sum_inv Qi hQ
  have h : (n : ℂ) * Qi.prod * (2 * (Zs.map (fun u => u⁻¹)).sum)
      = (n : ℂ) * Qi.prod * (Qi.map (fun u => u⁻¹)).sum := by
    linear_combination (-2 * (Zs.map (fun u => u⁻¹)).sum) * hI + 2 * h1 + hII - (n : ℂ) * h2
  exact (mul_left_cancel₀ (mul_ne_zero hn0 hQ0) h).symm

/-! ### The sandwich -/

/-- Both sides of `(BR)` are pinned: the left has real part at most `N`, the right at least `N`,
so every `qⱼ` has real part `1` and hence, lying in the closed unit disk, equals `1`. -/
theorem all_q_eq_one {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by
  have hupper : (qs.map (fun v => v.re)).sum ≤ (N : ℝ) := by
    have h := sum_le_card_mul 1 (qs.map (fun v => v.re)) (by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hr
      exact (Complex.re_le_norm v).trans (hq1 v hv))
    rwa [Multiset.card_map, hqcard, mul_one] at h
  have hlower : (N : ℝ) ≤ (qs.map (fun v => v.re)).sum := by
    have h := card_mul_le_sum (1 / 2) (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
      exact half_le_re_inv_one_sub (hz1 w hw) (hzne w hw))
    rw [Multiset.card_map, hzcard] at h
    have hmapre : (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum
        = (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum.re := by
      rw [← sum_map_re, Multiset.map_map]
      rfl
    have hre : (qs.map (fun v => v.re)).sum
        = 2 * (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum := by
      rw [sum_map_re, hBR, hmapre, Complex.mul_re]
      simp
    rw [hre]
    linarith
  have heq : (qs.map (fun v => 1 - v.re)).sum = 0 := by
    rw [sum_map_one_sub_re, hqcard]
    linarith
  intro v hv
  refine eq_one_of_re_eq_one_of_norm_le_one ?_ (hq1 v hv)
  have hzero := eq_zero_of_sum_eq_zero (s := qs.map (fun v => 1 - v.re)) (by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hr
    have := (Complex.re_le_norm u).trans (hq1 u hu)
    linarith) heq (1 - v.re) (Multiset.mem_map_of_mem _ hv)
  linarith

/-! ### Rubinstein's theorem at `a = 1` -/

/-- **Rubinstein's boundary theorem at `a = 1`**, with its equality case. -/
theorem rubinstein_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    (∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1)
      ∨ p = C p.leadingCoeff * (X ^ n - 1) := by
  by_cases hex : ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ < 1
  · exact Or.inl hex
  refine Or.inr ?_
  have hcrit : ∀ w : ℂ, (derivative p).eval w = 0 → 1 ≤ ‖w - 1‖ := by
    intro w hw
    by_contra hlt
    exact hex ⟨w, hw, not_le.1 hlt⟩
  have hpne : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hpne
  have hn0 : (n : ℂ) ≠ 0 := by
    intro h
    have h1 : n = 0 := by exact_mod_cast h
    omega
  obtain ⟨z, hzcard, hz1, hpz⟩ := exists_root_multiset (by omega : 1 ≤ n) hdeg hroots hp1
  obtain ⟨q, hqcard, hq1, hq0, hpq⟩ := exists_crit_multiset hn hdeg hcrit
  have hpq' : derivative p = C ((n : ℂ) * p.leadingCoeff)
      * ((q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => X - C u)).prod := by
    simp only [Multiset.map_map, Function.comp_def]
    exact hpq
  -- the repeated-root case is already excluded
  have hp'1 : (derivative p).eval 1 ≠ 0 := fun h => hex ⟨1, h, by simp⟩
  -- `p'` and `p''` from `p = c (X-1) Q`
  have hd1 : derivative p = C p.leadingCoeff
      * ((z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (z.map (fun w => X - C w)).prod) := by
    conv_lhs => rw [hpz]
    rw [derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul]
  have hd2 : derivative (derivative p) = C p.leadingCoeff
      * (2 * derivative (z.map (fun w => X - C w)).prod
        + (X - C 1) * derivative (derivative (z.map (fun w => X - C w)).prod)) := by
    rw [hd1, derivative_C_mul, derivative_add, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul]
    ring
  have hA : (derivative p).eval 1 = p.leadingCoeff * (z.map (fun w => (1 : ℂ) - w)).prod := by
    rw [hd1]
    simp [eval_prod_at]
  have hB : (derivative (derivative p)).eval 1
      = p.leadingCoeff * (2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))) := by
    rw [hd2]
    simp [eval_deriv_prod_at]
  -- `p'` and `p''` from `p' = n c R`
  have hmapq : (q.map (fun v => (1 : ℂ) - v⁻¹)).map (fun u => (1 : ℂ) - u)
      = q.map (fun v => v⁻¹) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun v _ => by simp
  have hC : (derivative p).eval 1
      = (n : ℂ) * p.leadingCoeff * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq', eval_mul, eval_C, eval_prod_at, hmapq]
  have hD : (derivative (derivative p)).eval 1
      = (n : ℂ) * p.leadingCoeff * sumEraseProd (q.map (fun v => v⁻¹)) := by
    rw [hpq', derivative_C_mul, eval_mul, eval_C, eval_deriv_prod_at, hmapq]
  -- the two relations, after cancelling the leading coefficient
  have hI : (z.map (fun w => (1 : ℂ) - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hA.symm.trans hC
    linear_combination h
  have hII : 2 * sumEraseProd (z.map (fun w => (1 : ℂ) - w))
      = (n : ℂ) * sumEraseProd (q.map (fun v => v⁻¹)) := by
    refine mul_left_cancel₀ hc0 ?_
    have h := hB.symm.trans hD
    linear_combination h
  -- no `zⱼ` equals `1`
  have hZ0 : (z.map (fun w => (1 : ℂ) - w)).prod ≠ 0 := by
    intro h
    exact hp'1 (by rw [hA, h, mul_zero])
  have hZne : ∀ u ∈ z.map (fun w => (1 : ℂ) - w), u ≠ 0 := by
    intro u hu hu0
    exact hZ0 (Multiset.prod_eq_zero (hu0 ▸ hu))
  have hzne : ∀ w ∈ z, w ≠ 1 := by
    intro w hw hw1
    exact hZne ((1 : ℂ) - w) (Multiset.mem_map_of_mem _ hw) (by rw [hw1]; ring)
  have hQne : ∀ u ∈ q.map (fun v => v⁻¹), u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hu
    exact inv_ne_zero (hq0 v hv)
  -- `(BR)`
  have hBRraw := boundary_reciprocal (n := n) hn0 hZne hQne hI hII
  have hQiinv : ((q.map (fun v => v⁻¹)).map (fun u => u⁻¹)).sum = q.sum := by
    rw [Multiset.map_map]
    simp
  have hZsinv : (z.map (fun w => (1 : ℂ) - w)).map (fun u => u⁻¹)
      = z.map (fun w => ((1 : ℂ) - w)⁻¹) := by
    rw [Multiset.map_map]
    rfl
  rw [hQiinv, hZsinv] at hBRraw
  -- every `qⱼ` is `1`, so every critical point is `0`
  have hqone := all_q_eq_one hqcard hzcard hq1 hz1 hzne hBRraw
  have hderivX : derivative p = C ((n : ℂ) * p.leadingCoeff) * X ^ (n - 1) := by
    rw [hpq]
    congr 1
    have hmap : q.map (fun v => X - C ((1 : ℂ) - v⁻¹))
        = Multiset.replicate q.card (X : ℂ[X]) := by
      rw [← Multiset.map_const']
      exact Multiset.map_congr rfl fun v hv => by rw [hqone v hv]; simp
    rw [hmap, Multiset.prod_replicate, hqcard]
  -- hence `p - c Xⁿ` is constant
  have hdz : derivative (p - C p.leadingCoeff * X ^ n) = 0 := by
    rw [derivative_sub, hderivX, derivative_C_mul, derivative_X_pow, map_mul]
    ring
  have hdeg0 : (p - C p.leadingCoeff * X ^ n).natDegree = 0 := derivative_eq_zero.1 hdz
  obtain ⟨d, hd⟩ := natDegree_eq_zero.1 hdeg0
  have hdval : d = -p.leadingCoeff := by
    have h := congrArg (Polynomial.eval (1 : ℂ)) hd
    simpa [hp1] using h
  have hCd : (C d : ℂ[X]) = -C p.leadingCoeff := by rw [hdval, map_neg]
  linear_combination -hd + hCd

/-- The closed-disk form.  In the extremal case `p = c(Xⁿ - 1)` the only critical point is `0`,
at distance exactly `1` from the zero `1`. -/
theorem sendov_boundary_one {n : ℕ} (hn : 2 ≤ n) {p : ℂ[X]} (hdeg : p.natDegree = n)
    (hroots : ∀ w ∈ p.roots, ‖w‖ ≤ 1) (hp1 : p.eval 1 = 0) :
    ∃ ζ : ℂ, (derivative p).eval ζ = 0 ∧ ‖ζ - 1‖ ≤ 1 := by
  rcases rubinstein_one hn hdeg hroots hp1 with ⟨ζ, hζ, hlt⟩ | hext
  · exact ⟨ζ, hζ, le_of_lt hlt⟩
  refine ⟨0, ?_, by norm_num⟩
  rw [hext, derivative_C_mul, derivative_sub, derivative_X_pow, derivative_one]
  simp [zero_pow (by omega : n - 1 ≠ 0)]

end Sendov
