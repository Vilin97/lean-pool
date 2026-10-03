/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Analytic.Origin
public import LeanPool.Sendov.Analytic.Jsum
public import LeanPool.Sendov.Reduction.Setup

/-!
# The origin inequality

This file closes the origin channel, deriving `(origin-exact)` — the hypothesis `horigin` of
`Sendov.polar_origin_incompatible` — from the triangle inequality `(tri)` of
`Sendov.Analytic.Origin`, the two origin identities, and the defect estimate of
`Sendov.Analytic.Jsum`.

The chain is:

* **(f1aq)**  The two origin identities express `F(1) + (n-1) a (x+iy) ∫₀¹F` exactly, in terms of
  `J = (∏ qⱼ)(∏ zⱼ)` and `∑ⱼ 1/zⱼ`.  Feeding in `Jsum_estimate` collapses this to `J·W/n` plus
  an error of size `a(1-|J|²)/(n-1)`, where `W = a²(n-1) + 1 - a(x+iy)`.
* **(grow)**  `‖W‖ ≥ 2an/(n-1)`, which makes `|J|·‖W‖/n + a(1-|J|²)/(n-1)` non-decreasing in
  `|J|` on `[0,1]`, so `|J|` may be replaced by `1`.  This reduces to the quadratic
  `(n-1)²a² - (3n-1)a + (n-1) > 0`, whose discriminant `(3n-1)² - 4(n-1)³` is negative exactly
  from `n ≥ 5` on.  **This is the only place the hypothesis `n ≥ 5` is used.**
* **Eliminating `y`.**  `|s + it| ≤ s + t²/(2s)` for `s > 0`, applied to `W`, whose real part
  `a²(n-1) + 1 - ax` is at least `a²(n-1)`, and whose imaginary part is `-ay` with
  `y² ≤ 1 - x²`.

## Main statements

* `Sendov.origin_exact`: `(origin-exact)`, in exactly the form `polar_origin_incompatible` wants;
* `Sendov.grow`: the lower bound `‖W‖ ≥ 2an/(n-1)`.
-/

public section

namespace Sendov

open Complex (I)

/-! ### Scalar lemmas -/

lemma sum_norm_le_card : ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
    (q.map (fun v => ‖v‖)).sum ≤ (q.card : ℝ) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]

/-- `|s + it| ≤ s + t²/(2s)` for `s > 0`, in cleared form.  Squaring both sides leaves
`t⁴ ≥ 0`. -/
lemma norm_mul_two_re_le {w : ℂ} (_hs : 0 < w.re) :
    ‖w‖ * (2 * w.re) ≤ 2 * w.re ^ 2 + w.im ^ 2 := by
  have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg w, h1, sq_nonneg (w.im ^ 2), sq_nonneg (w.re * w.im)]

/-! ### The quantity `W`, the growth bound `(grow)`, and the two real-arithmetic steps -/

/-- `W = a²(n-1) + 1 - a(x+iy)`; `n` times the bracket in the blog post's `(tri-2)`. -/
noncomputable def Worigin (n : ℕ) (a x y : ℝ) : ℂ :=
  (a : ℂ) ^ 2 * ((n : ℂ) - 1) + 1 - (a : ℂ) * ((x : ℂ) + (y : ℂ) * I)

lemma Worigin_eq (n : ℕ) (a x y : ℝ) :
    Worigin n a x y = ((a ^ 2 * ((n : ℝ) - 1) + 1 - a * x : ℝ) : ℂ)
      + ((-(a * y) : ℝ) : ℂ) * I := by
  simp only [Worigin]
  push_cast
  ring

lemma Worigin_re (n : ℕ) (a x y : ℝ) :
    (Worigin n a x y).re = a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by
  rw [Worigin_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

lemma Worigin_im (n : ℕ) (a x y : ℝ) : (Worigin n a x y).im = -(a * y) := by
  rw [Worigin_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **(grow).**  `‖W‖ ≥ 2an/(n-1)`.  Bounding `‖W‖` below by its real part reduces this to
`(n-1)²a² - (3n-1)a + (n-1) > 0`; completing the square turns that into
`4(n-1)³ - (3n-1)² > 0`, which is exactly where `n ≥ 5` is needed. -/
theorem grow {n : ℕ} (hn : 5 ≤ n) {a x y : ℝ} (ha0 : 0 < a) (hx : x ≤ 1) :
    2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ ‖Worigin n a x y‖ := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hu : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have hdisc : 0 < 4 * ((n : ℝ) - 1) ^ 3 - (3 * (n : ℝ) - 1) ^ 2 := by
    nlinarith [hu, sq_nonneg ((n : ℝ) - 5), mul_nonneg (mul_nonneg hu hu) hu]
  have hquad : 0 < ((n : ℝ) - 1) ^ 2 * a ^ 2 - (3 * (n : ℝ) - 1) * a + ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg (2 * ((n : ℝ) - 1) ^ 2 * a - (3 * (n : ℝ) - 1)), hdisc,
      mul_pos hn1 hn1]
  have hre : 2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ (Worigin n a x y).re := by
    rw [Worigin_re, div_le_iff₀ hn1]
    nlinarith [hquad, mul_nonneg (mul_nonneg (le_of_lt ha0) (sub_nonneg.2 hx)) (le_of_lt hn1)]
  exact hre.trans (Complex.re_le_norm _)

/-- Replacing `|J|` by `1`: `P K + c(1 - P²) ≤ K` on `0 ≤ P ≤ 1` once `K ≥ 2c ≥ 0`, since
`K - P K - c(1-P²) = (1-P)(K - c(1+P))`. -/
lemma collapse_J {K c P : ℝ} (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hcK : 2 * c ≤ K) :
    P * K + c * (1 - P ^ 2) ≤ K := by
  have hfac : 0 ≤ (1 - P) * (K - c * (1 + P)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hc0, hP1, hcK]
  nlinarith [hfac]

/-- Eliminating `y`: `‖W‖ ≤ Re W + (Im W)²/(2 Re W)`, then `Re W ≥ a²(n-1)` and `y² ≤ 1 - x²`. -/
lemma norm_Worigin_le {n : ℕ} {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hn1 : (0 : ℝ) < (n : ℝ) - 1) (hxle : x ≤ 1) (hy2 : y ^ 2 ≤ 1 - x ^ 2) :
    ‖Worigin n a x y‖
      ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x + (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
  have hax : a * x ≤ a := mul_le_of_le_one_right (le_of_lt ha0) hxle
  have ha2 : (0 : ℝ) < a ^ 2 * ((n : ℝ) - 1) := by positivity
  have hslow : a ^ 2 * ((n : ℝ) - 1) ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by linarith
  have hpos : 0 < (Worigin n a x y).re := by rw [Worigin_re]; linarith
  have hs : (0 : ℝ) < 2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x) := by linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have h := norm_mul_two_re_le hpos
  rw [Worigin_re, Worigin_im] at h
  have hmain : ‖Worigin n a x y‖
      ≤ (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)
        + a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hs]
    nlinarith [h]
  have htail : a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x))
      ≤ (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hs hden]
    nlinarith [hy2, hslow, ha2, sq_nonneg y, hn1]
  linarith [hmain, htail]

/-- `x` and `y` are determined by `q.sum`, and inherit two bounds from `‖qⱼ‖ ≤ 1`: the real
part is what the polar and origin estimates need, and `x² + y² ≤ 1` is what eliminates `y`. -/
lemma xy_bounds {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)) :
    (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x ∧ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnc : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
    have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
  have hqcardR : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  refine ⟨?_, ?_⟩
  · have hc : ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)
        = ((((n : ℝ) - 1) * x : ℝ) : ℂ) + ((((n : ℝ) - 1) * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [sum_map_re, hxy, hc]
    simp
  · have hxynorm : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have h2 : ‖q.sum‖ ≤ (q.map (fun v => ‖v‖)).sum := by
      have h := norm_sum_map_le q (fun v => v)
      simpa using h
    have h3 := sum_norm_le_card q hq1
    rw [hqcardR] at h3
    have h1 : ‖q.sum‖ ≤ (n : ℝ) - 1 := h2.trans h3
    rw [hxy, norm_mul, hnc] at h1
    have h4 : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [h1, hn1]
    nlinarith [hxynorm, h4, norm_nonneg ((x : ℂ) + (y : ℂ) * I)]

/-! ### The origin inequality -/

/-- **`(origin-exact)`.**  The origin channel, in the form the reduction consumes. -/
theorem origin_exact {n : ℕ} (hn : 5 ≤ n) {a x y α : ℝ} {z q : Multiset ℂ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I))
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hfirst : (n : ℂ) * ∫ t in (0 : ℝ)..1, Fprod a q t = (-1) ^ (n - 1) * q.prod * z.prod)
    (hsecond : (n : ℂ) * (q.map (fun v => 1 - (a : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z))
    (hα : α = M n * (1 - a ^ 2) / 2) :
    2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨hxre, hx2⟩ := xy_bounds hn2 hqcard hq1 hxy
  have hxle : x ≤ 1 := by nlinarith [hx2, sq_nonneg y]
  -- the triangle inequality `(tri)` and the defect estimate
  have htri := one_le_tri hn2 hqcard hq0 hq1 (le_of_lt ha0) hxre hxy
  have hJ := Jsum_estimate (n := n) hn2 (a := a) (x := x) (y := y) hqcard hz1 hq1 hcent hxy
  -- `(f1aq)`
  have hF1 : Fprod a q 1 = (q.map (fun v => 1 - (a : ℂ) * v)).prod := by
    simp only [Fprod, Complex.ofReal_one, mul_one]
  have hsecond' : (n : ℂ) * Fprod a q 1
      = (-1) ^ (n - 1) * q.prod * (z.prod + (a : ℂ) * sumEraseProd z) := by
    rw [hF1]; exact hsecond
  have hf1aq : (n : ℂ) * (Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t)
      = (-1) ^ (n - 1) * ((q.prod * z.prod) * Worigin n a x y
        + (a : ℂ) * (q.prod * sumEraseProd z
            - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * I))
              * (q.prod * z.prod))) := by
    simp only [Worigin]
    linear_combination hsecond' + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * hfirst
  -- `(tri-2)`
  have hsign : ‖((-1 : ℂ)) ^ (n - 1)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hnn : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hana : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ha0)]
  have hPJ0 : (0 : ℝ) ≤ ‖q.prod‖ * ‖z.prod‖ := by positivity
  have hPJ1 : ‖q.prod‖ * ‖z.prod‖ ≤ 1 := by
    have h1 : ‖q.prod‖ ≤ 1 := norm_prod_le_one q hq1
    have h2 : ‖z.prod‖ ≤ 1 := norm_prod_le_one z hz1
    nlinarith [norm_nonneg q.prod, norm_nonneg z.prod]
  have hstep1 : (n : ℝ) * ‖Fprod a q 1
        + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * I) * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      ≤ ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
        + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by
    have h := congrArg norm hf1aq
    rw [norm_mul, hnn, norm_mul, hsign, one_mul] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, hana]
    have hmul := mul_le_mul_of_nonneg_left hJ (le_of_lt ha0)
    linarith [hmul]
  -- `(grow)` collapses `|J|` to `1`, giving `(tri-3)`
  have hgrow := grow (n := n) hn (a := a) (x := x) (y := y) ha0 hxle
  have hcoll : ‖q.prod‖ * ‖z.prod‖ * ‖Worigin n a x y‖
      + a * ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2)
      ≤ ‖Worigin n a x y‖ := by
    have hc : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) ≤ ‖Worigin n a x y‖ := by
      have he : 2 * (a * ((n : ℝ) / ((n : ℝ) - 1))) = 2 * a * (n : ℝ) / ((n : ℝ) - 1) := by ring
      rw [he]; exact hgrow
    have hcnn : (0 : ℝ) ≤ a * ((n : ℝ) / ((n : ℝ) - 1)) := by positivity
    exact collapse_J hPJ1 hcnn hc
  have htri3 : (n : ℝ) ≤ ‖Worigin n a x y‖
      + (n : ℝ) * (a ^ 2 * ((n : ℝ) - 1)
        * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    have h := mul_le_mul_of_nonneg_left htri (le_of_lt hnpos)
    linarith [h, hstep1, hcoll]
  -- eliminate `y`, and assemble
  have hWle := norm_Worigin_le (n := n) (y := y) ha0 ha1 hn1 hxle (by linarith [hx2])
  simp only [M] at hα ⊢
  linarith [htri3, hWle, hα]

end Sendov
