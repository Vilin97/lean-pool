/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Reduction.Stat

/-!
# From the raw origin inequality to its `α`, `β(1)` form

This is `(origin-exact) + (beta-bound) ⟹ (1le)`.  The work is in replacing

  `∫₀¹ t β(t)^((n-2)/2) dt`

by a Beta value plus the `t³` integral that `stat` is stated with.  Writing `β` as a sum of
squares, `β(t) = (1-axt)² + a²t²(1-x²)`, the blog post applies the mean value theorem to
`s ↦ ((1-axt)² + s)^((n-2)/2)`.  Here that step is Bernoulli's inequality instead: dividing

  `(P+Q)^p ≤ P^p + p Q (P+Q)^(p-1)`

through by `(P+Q)^p` turns it into `1 ≤ θ^p + p(1-θ)` at `θ = P/(P+Q)`, which is exactly
`one_add_mul_self_le_rpow_one_add`.  No derivative and no mean value theorem is needed.

After that, `∫₀¹ t (1-axt)^(n-2) dt` is enlarged to `[0, 1/ax]` — legitimate since `ax ≤ 1` and
the integrand stays nonnegative — and evaluated by `Sendov.integral_chord_lin`, the `k = 1`
Beta integral of `Sendov.Common.Chord`.  What is left is algebra in `α` and `β(1)`, using
`1 - x² ≤ β(1)` (which is `(x-a)² ≥ 0`) and `ax = 1 - β(1)/2 - α/(n-1)`.

`(beta-bound)` enters only through `β(1) < 1`, which is what makes `x > a/2 > 0`, hence `1/x²`
finite and `1/(ax) ≥ 1`.

## Main statements

* `Sendov.rpow_add_le_of_one_le`: the Bernoulli form of the mean-value step;
* `Sendov.beta_split`: the pointwise consequence for `β`;
* `Sendov.one_le_of_origin`: `(origin-exact) + (beta-bound) ⟹ (1le)`.
-/

public section

namespace Sendov

open MeasureTheory

variable {n : ℕ} {a x t α : ℝ}

/-- `(P+Q)^p ≤ P^p + p Q (P+Q)^(p-1)` for `p ≥ 1`.  This is the blog post's mean-value step,
obtained from Bernoulli's inequality after dividing by `(P+Q)^p`. -/
lemma rpow_add_le_of_one_le {P Q p : ℝ} (hP : 0 ≤ P) (hPQ : 0 < P + Q) (hp : 1 ≤ p) :
    (P + Q) ^ p ≤ P ^ p + p * Q * (P + Q) ^ (p - 1) := by
  have hθ : (0 : ℝ) ≤ P / (P + Q) := div_nonneg hP hPQ.le
  have hb := one_add_mul_self_le_rpow_one_add (s := P / (P + Q) - 1) (by linarith) hp
  rw [show (1 : ℝ) + (P / (P + Q) - 1) = P / (P + Q) by ring] at hb
  have hpow : (0 : ℝ) < (P + Q) ^ p := Real.rpow_pos_of_pos hPQ p
  have hfrac : (P / (P + Q)) ^ p * (P + Q) ^ p = P ^ p := by
    rw [← Real.mul_rpow hθ hPQ.le]
    congr 1
    field_simp
  have hsub : (P + Q) ^ (p - 1) = (P + Q) ^ p / (P + Q) := by
    rw [Real.rpow_sub hPQ, Real.rpow_one]
  have key : (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q)) ≤ P ^ p := by
    calc (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q))
        = (1 + p * (P / (P + Q) - 1)) * (P + Q) ^ p := by
          field_simp
          ring
      _ ≤ (P / (P + Q)) ^ p * (P + Q) ^ p := mul_le_mul_of_nonneg_right hb hpow.le
      _ = P ^ p := hfrac
  rw [hsub]
  linarith

/-- `ax t < 1` on `[0,1]`, so the chord `1 - axt` is positive. -/
lemma one_sub_mul_pos (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < 1 - a * x * t := by
  rcases le_or_gt x 0 with h | h
  · nlinarith [mul_nonneg ht0 (mul_nonneg ha.le (neg_nonneg.2 h))]
  · have hx1 : x ≤ 1 := by nlinarith
    have h1 : a * x * t ≤ a * x * 1 :=
      mul_le_mul_of_nonneg_left ht1 (mul_pos ha h).le
    nlinarith [h1]

/-- The pointwise step: `β^((n-2)/2)` split into a chord power and a `β^((n-4)/2)` remainder. -/
lemma beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)
      ≤ (1 - a * x * t) ^ ((n : ℝ) - 2)
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * t ^ 2 * (1 - x ^ 2))
          * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < 1 - a * x * t := one_sub_mul_pos ha ha1 hx ht0 ht1
  have hP : (0 : ℝ) ≤ (1 - a * x * t) ^ 2 := sq_nonneg _
  have hQ : (0 : ℝ) ≤ a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    have : (0 : ℝ) ≤ 1 - x ^ 2 := by linarith
    positivity
  have hsum : QQ (a * x) (a ^ 2) t
      = (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by
    rw [QQ_eq]; ring
  have hPQ : (0 : ℝ) < (1 - a * x * t) ^ 2 + a ^ 2 * t ^ 2 * (1 - x ^ 2) := by positivity
  have hp : (1 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hb := rpow_add_le_of_one_le hP hPQ hp
  rw [← hsum] at hb
  -- `((1-axt)²)^((n-2)/2) = (1-axt)^(n-2)`
  have hchord : ((1 - a * x * t) ^ 2 : ℝ) ^ (((n : ℝ) - 2) / 2)
      = (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    rw [← Real.rpow_natCast (1 - a * x * t) 2, ← Real.rpow_mul hy.le]
    congr 1
    push_cast
    ring
  -- `(n-2)/2 - 1 = (n-4)/2`
  have hexp : ((n : ℝ) - 2) / 2 - 1 = ((n : ℝ) - 4) / 2 := by ring
  rw [hchord, hexp] at hb
  exact hb

/-- The integral form of the split, with the chord piece evaluated by the Beta integral. -/
lemma integral_beta_split (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hax : 0 < a * x) :
    (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))
        + ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
          * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hr2 : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by linarith
  have hr4 : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  have haxle : a * x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), ha.le]
  -- the three continuous integrands
  have hc1 : Continuous fun t : ℝ => t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    simpa using continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hr2
  have hc2 : Continuous fun t : ℝ => t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
    (by fun_prop : Continuous fun t : ℝ => t).mul
      ((continuous_rpow_const hs.le).comp (by fun_prop))
  have hc3 : Continuous fun t : ℝ =>
      ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
        * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) :=
    (continuous_pow_mul_QQ (a * x) (a ^ 2) 3 hr4).const_mul _
  -- integrate the pointwise bound
  have hstep : (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + ∫ t in (0 : ℝ)..1, ((n : ℝ) - 2) / 2 * (a ^ 2 * (1 - x ^ 2))
            * (t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2)) := by
    rw [← intervalIntegral.integral_add (hc2.intervalIntegrable _ _)
      (hc3.intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable _ _)
      ((hc2.add hc3).intervalIntegrable _ _) ?_
    intro u hu
    have h := beta_split hn ha ha1 hx hu.1 hu.2
    have hu0 : (0 : ℝ) ≤ u := hu.1
    nlinarith [h, hu0, Real.rpow_nonneg (QQ_nonneg (by nlinarith [sq_nonneg a] :
      (a * x) ^ 2 ≤ a ^ 2) u) (((n : ℝ) - 4) / 2)]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  gcongr
  -- the chord piece: enlarge to `[0, 1/(ax)]` and evaluate
  have hrest : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
      ≤ ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
    have hone : (1 : ℝ) ≤ 1 / (a * x) := by rw [le_div_iff₀ hax]; linarith
    have hadd : (∫ t in (0 : ℝ)..1, t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        + (∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2))
        = ∫ t in (0 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc2.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
    have hnn : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..1 / (a * x), t * (1 - a * x * t) ^ ((n : ℝ) - 2) := by
      refine intervalIntegral.integral_nonneg hone ?_
      intro u hu
      have : (0 : ℝ) ≤ 1 - a * x * u := by
        have := hu.2
        rw [le_div_iff₀ hax] at this
        linarith
      exact mul_nonneg (by linarith [hu.1]) (Real.rpow_nonneg this _)
    linarith
  refine hrest.trans_eq ?_
  rw [integral_chord_lin hs hax]
  congr 1
  ring

/-- **`(origin-exact) + (beta-bound) ⟹ (1le)`.**  `(beta-bound)` enters only as `β(1) < 1`. -/
theorem one_le_of_origin (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hB1lt : QQ (a * x) (a ^ 2) 1 < 1)
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    1 ≤ QQ (a * x) (a ^ 2) 1 / (2 * α * (1 - QQ (a * x) (a ^ 2) 1))
      + QQ (a * x) (a ^ 2) 1 / (4 * α)
      + 1 / (2 * M n)
      + QQ (a * x) (a ^ 2) 1 / (4 * α * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * QQ (a * x) (a ^ 2) 1 / (4 * α)
        * ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (0 : ℝ) < M n := M_pos hn2
  have hMn : M n = (n : ℝ) - 1 := rfl
  set B1 : ℝ := QQ (a * x) (a ^ 2) 1 with hB1def
  set I3 : ℝ := ∫ t in (0 : ℝ)..1, t ^ 3 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 4) / 2) with hI3def
  -- `1 - β(1) = 2ax - a²`, so `β(1) < 1` gives `ax > 0`
  have hB1eq : B1 = 1 - 2 * (a * x) + a ^ 2 := by rw [hB1def, QQ_one]
  have hax : 0 < a * x := by nlinarith [sq_nonneg a]
  have hxpos : 0 < x := by nlinarith [hax, ha]
  -- `x² ≥ 1 - β(1)`, which is `(x-a)² ≥ 0`
  have hxsq : 1 - B1 ≤ x ^ 2 := by rw [hB1eq]; nlinarith [sq_nonneg (x - a)]
  have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
  have hinv : 1 / x ^ 2 ≤ 1 / (1 - B1) := by
    apply one_div_le_one_div_of_le (by linarith) hxsq
  have hone_sub : 1 - x ^ 2 ≤ B1 := by linarith
  -- the integral bound
  have hsplit := integral_beta_split hn ha ha1 hx hax
  have hI3nn : (0 : ℝ) ≤ I3 := by
    rw [hI3def]
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro u hu
    have hfe : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    exact mul_nonneg (pow_nonneg hu.1 3) (Real.rpow_nonneg (QQ_nonneg hfe u) _)
  -- multiply the split by `a² n M` and simplify the Beta term to `1/x²`
  have hcoef : (0 : ℝ) ≤ a ^ 2 * n * M n := by positivity
  have hbeta_simp : a ^ 2 * (n : ℝ) * M n
      * (1 / ((a * x) ^ 2 * (((n : ℝ) - 1) * (n : ℝ)))) = 1 / x ^ 2 := by
    have hane : (a : ℝ) ≠ 0 := ha.ne'
    have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
    have hn1 : ((n : ℝ) - 1) ≠ 0 := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    rw [hMn]
    field_simp
  have hkey : a ^ 2 * n * M n
        * (∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2))
      ≤ 1 / x ^ 2 + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3 := by
    refine (mul_le_mul_of_nonneg_left hsplit hcoef).trans_eq ?_
    rw [mul_add, hbeta_simp]
    congr 1
    ring
  -- assemble
  have hax_eq : a * x = 1 - B1 / 2 - α / M n := mul_eq_c hn2 hα
  have hmain : 2 * α ≤ B1 / (1 - B1) + B1 / 2 + α / M n + B1 / (2 * M n)
      + (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    have hlast : (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * (1 - x ^ 2) / 2 * I3
        ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
      have hc : (0 : ℝ) ≤ (a ^ 2) ^ 2 * n * M n * ((n : ℝ) - 2) / 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
        positivity
      nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.2 hone_sub)) hI3nn]
    have hfirst : (1 - x ^ 2) / (2 * M n) ≤ B1 / (2 * M n) := by
      apply div_le_div_of_nonneg_right hone_sub (by positivity)
    have hne1 : (1 : ℝ) - B1 ≠ 0 := by linarith
    have hrec : 1 / (1 - B1) = 1 + B1 / (1 - B1) := by
      field_simp
      ring
    have hinv' : 1 / x ^ 2 ≤ 1 + B1 / (1 - B1) := by rw [← hrec]; exact hinv
    -- do NOT rewrite `hax_eq` into `horigin`: it would also rewrite the `a * x` inside the
    -- integral, and the resulting atom would no longer match `hkey`
    linarith [horigin, hkey, hinv', hfirst, hlast, hax_eq]
  -- divide by `2α`
  have h2α : (0 : ℝ) < 2 * α := by linarith
  have hne : (1 : ℝ) - B1 ≠ 0 := by linarith
  have h1 : 2 * α * (B1 / (2 * α * (1 - B1))) = B1 / (1 - B1) := by
    field_simp
  have h2 : 2 * α * (B1 / (4 * α)) = B1 / 2 := by
    field_simp
    ring
  have h3 : 2 * α * (1 / (2 * M n)) = α / M n := by
    field_simp
  have h4 : 2 * α * (B1 / (4 * α * M n)) = B1 / (2 * M n) := by
    field_simp
    ring
  have h5 : 2 * α * ((a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / (4 * α) * I3)
      = (a ^ 2) ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) * B1 / 2 * I3 := by
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ h2α
  rw [mul_one, mul_add, mul_add, mul_add, mul_add, h1, h2, h3, h4, h5]
  exact hmain

end Sendov
