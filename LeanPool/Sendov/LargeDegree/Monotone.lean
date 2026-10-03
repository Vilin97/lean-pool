/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.LargeDegree.Tail

/-!
# Monotonicity of the elementary bound in the degree

`Sendov.U` bounds `Sendov.R` for every `n ≥ 5`.  Here it is reduced to a single inequality
in `α` alone, by showing that `U n α` is essentially decreasing in `n` on `n ≥ 101`.

Two features of the bound make this cheaper than it looks.

First, the sharp Beta constant collapses.  The exponent is `r = (n-4)/2`, so

  `(r+1)(r+2)(r+3)(r+4) = (n-2) n (n+2) (n+4) / 16`,

and the `n (n-2)` in it cancels the `n (n-2)` in the prefactor of `Sendov.R` exactly.  The
first tail term is therefore the *rational function*

  `T1 n α = 24 (n-1-2α)² / ((3+α) c⁴ (n-1)(n+2)(n+4))`,

with no factorial-like growth left to control.  (Had the cruder constant `6/r⁴` of the
informal write-up been used, no such cancellation would occur and the corresponding step
would need the degree-8 positivity certificate recorded there.)

Second, the surviving real power is a square: writing `b = √B`, the second tail term is
`T2 n α = A² n (n-1)(n-2)/(16(3+α)) · b ^ (n-4)` with a *natural* exponent, so the geometric
decay can be run as an ordinary induction on `n` rather than as an estimate on `rpow`.

## The two certificates

`T1` is not monotone in `n` by itself — at `α = 17` the factor
`(n-1-2α)²/((n-1)(n+2)(n+4))` increases up to `n ≈ 108` — so it is bounded by its value at
`n = 101` only after a `1%` allowance, which the `c⁴` in the denominator more than pays for.
That allowance is `Sendov.tail1_poly`, a Bernstein certificate on `0 ≤ α ≤ 17`.  Its top
coefficient is the only one in this development that is *not* a positive combination of
powers of the degree offset; it is handled by completing the square, its quadratic part
having negative discriminant.

`Sendov.tail2_poly` is the geometric step, and is an ordinary all-positive certificate.

## Main statements

* `Sendov.U_eq`: `U` in closed form, `T1 + T2` plus four elementary terms;
* `Sendov.T1_le`, `Sendov.T2_le`: the two tail bounds at `n = 101`;
* `Sendov.U_le_Ut`: `U n α ≤ Ut α` for `n ≥ 101`, where `Ut` involves no `n` and no `rpow`.
-/

public section

namespace Sendov

variable {n : ℕ} {α : ℝ}

/-- The first tail term of `Sendov.U`, in closed form. -/
@[expose]
noncomputable def T1 (n : ℕ) (α : ℝ) : ℝ :=
  24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
    ((3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4))

/-- The second tail term of `Sendov.U`, with the real power of `B` replaced by a natural
power of `√B`. -/
noncomputable def T2 (n : ℕ) (α : ℝ) : ℝ :=
  A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (16 * (3 + α)) * Real.sqrt (α / (3 + α)) ^ (n - 4)

/-! ### The two polynomial certificates -/

/-- The allowance for the first tail term: on `0 ≤ α ≤ 17` and `N = 100 + j ≥ 100`,

  `(N-2α)² / (N (N+3)(N+5)) ≤ (101/100) (100-2α)² / (100 · 103 · 105)`.

A Bernstein certificate in `α` on `[0,17]`, whose coefficients are polynomials in `j`.  The
top one, `439956 j³ + 27356448 j² - 366591060 j + 4711014000`, has a negative linear
coefficient; it is nonnegative because its quadratic part has negative discriminant. -/
lemma tail1_poly {j α : ℝ} (hj : 0 ≤ j) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    108150000 * (100 + j - 2 * α) ^ 2
      ≤ 101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j)) := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hj2 : (0 : ℝ) ≤ j ^ 2 := sq_nonneg j
  have hj3 : (0 : ℝ) ≤ j ^ 3 := pow_nonneg hj 3
  have h0 : (0 : ℝ) ≤ 1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000 := by
    linarith
  have h1 : (0 : ℝ) ≤ 1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000 := by
    linarith
  have h2 : (0 : ℝ) ≤ 439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000 := by
    nlinarith [sq_nonneg (4559408 * j - 30549255), hj3]
  have hid : (17 : ℝ) ^ 2 *
      (101 * (100 - 2 * α) ^ 2 * ((100 + j) * (103 + j) * (105 + j))
        - 108150000 * (100 + j - 2 * α) ^ 2)
      = (1010000 * j ^ 3 + 202930000 * j ^ 2 + 10301150000 * j + 10815000000) * (17 - α) ^ 2
        + (1333200 * j ^ 3 + 194325600 * j ^ 2 + 6243318000 * j + 14275800000)
            * (α * (17 - α))
        + (439956 * j ^ 3 + 27356448 * j ^ 2 - 366591060 * j + 4711014000) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]

/-- The geometric step for the second tail term: on `0 ≤ α ≤ 17` and `n = 101 + k ≥ 101`,

  `12 A_{n+1}² (n+1) n (n-1) ≤ 13 A_n² n (n-1)(n-2)`,

after clearing the denominators `n²` and `(n-1)²` of `A_{n+1}` and `A_n`.  Together with
`√B ≤ 12/13` this makes the step ratio less than one.  A Bernstein certificate in `α` on
`[0,17]` with all coefficients positive combinations of powers of `k`. -/
lemma tail2_poly {k α : ℝ} (hk : 0 ≤ k) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2
      ≤ 13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2 := by
  have hu : (0 : ℝ) ≤ 17 - α := by linarith
  have hk2 : (0 : ℝ) ≤ k ^ 2 := sq_nonneg k
  have hk3 : (0 : ℝ) ≤ k ^ 3 := pow_nonneg hk 3
  have hk4 : (0 : ℝ) ≤ k ^ 4 := pow_nonneg hk 4
  have hk5 : (0 : ℝ) ≤ k ^ 5 := pow_nonneg hk 5
  have h0 : (0 : ℝ) ≤ k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2
      + 357802600 * k + 6426630000 := by linarith
  have h1 : (0 : ℝ) ≤ 2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2
      + 491029284 * k + 7642508400 := by linarith
  have h2 : (0 : ℝ) ≤ k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2
      + 165348456 * k + 2243200572 := by linarith
  have hid : (17 : ℝ) ^ 2 *
      (13 * (100 + k - 2 * α) ^ 2 * (99 + k) * (101 + k) ^ 2
        - 12 * (101 + k - 2 * α) ^ 2 * (102 + k) * (100 + k) ^ 2)
      = (k ^ 5 + 465 * k ^ 4 + 85927 * k ^ 3 + 7878063 * k ^ 2 + 357802600 * k + 6426630000)
          * (17 - α) ^ 2
        + (2 * k ^ 5 + 862 * k ^ 4 + 146218 * k ^ 3 + 12147842 * k ^ 2 + 491029284 * k
            + 7642508400) * (α * (17 - α))
        + (k ^ 5 + 397 * k ^ 4 + 61447 * k ^ 3 + 4603863 * k ^ 2 + 165348456 * k
            + 2243200572) * α ^ 2 := by
    ring
  nlinarith [mul_nonneg h0 (sq_nonneg (17 - α)), mul_nonneg h1 (mul_nonneg hα hu),
    mul_nonneg h2 (sq_nonneg α)]

/-! ### The closed form of `U` -/

/-- `c` increases with `n`: raising the degree moves `c` towards `1 - B/2`. -/
lemma c_mono {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α) : c m α ≤ c n α := by
  have hMm : 0 < M m := M_pos hm
  have hMle : M m ≤ M n := by
    simp only [M]
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  have : α / M n ≤ α / M m := div_le_div_of_nonneg_left hα hMm hMle
  simp only [c]
  linarith

/-- The real power of `B` in `Sendov.U` is a natural power of `√B`. -/
lemma rpow_B_eq (hn : 4 ≤ n) (hα : 0 ≤ α) :
    (α / (3 + α)) ^ (((n : ℝ) - 4) / 2) = Real.sqrt (α / (3 + α)) ^ (n - 4) := by
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hcast : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    push_cast [Nat.cast_sub hn]
    ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((α / (3 + α)) ^ ((1 : ℝ) / 2)) (n - 4),
    ← Real.rpow_mul hB, hcast]
  congr 1
  ring

/-- The sharp Beta constant, factored.  This is the cancellation that makes `T1` rational:
`(r+1)(r+2)(r+3)(r+4) = (n-2) n (n+2)(n+4)/16` at `r = (n-4)/2`. -/
lemma beta_prod (n : ℕ) :
    (((n : ℝ) - 4) / 2 + 1) * (((n : ℝ) - 4) / 2 + 2) * (((n : ℝ) - 4) / 2 + 3)
        * (((n : ℝ) - 4) / 2 + 4)
      = ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) + 2) * ((n : ℝ) + 4) / 16 := by
  ring

/-- **`U` in closed form.**  The `n (n-2)` of the prefactor cancels against the same factor
in the sharp Beta constant, leaving a rational function plus a natural power of `√B`. -/
lemma U_eq (hn : 5 ≤ n) (hα : 0 ≤ α) (hc : c n α ≠ 0) :
    U n α = 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + T1 n α + T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (n : ℝ) ≠ 0 := by linarith
  have hp2 : (n : ℝ) + 2 ≠ 0 := by linarith
  have hp4 : (n : ℝ) + 4 ≠ 0 := by linarith
  simp only [U, beta_prod, T1, T2, M, A, rpow_B_eq (show 4 ≤ n by omega) hα]
  field_simp
  ring

/-! ### The first tail term -/

/-- `T1` is bounded by its value at `n = 101`, up to `1%`. -/
lemma T1_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    T1 n α ≤ 101 / 100 * T1 101 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc1 : (0 : ℝ) < c 101 α := by
    have := c_ge_of_large (n := 101) le_rfl hα hα'
    linarith
  have hcn : c 101 α ≤ c n α := c_mono (by omega) hn hα
  have hcnp : (0 : ℝ) < c n α := lt_of_lt_of_le hc1 hcn
  have hc4 : c 101 α ^ 4 ≤ c n α ^ 4 := by
    exact pow_le_pow_left₀ hc1.le hcn 4
  have hN : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hN4 : (0 : ℝ) < (n : ℝ) + 4 := by linarith
  have hprod : (0 : ℝ) ≤ ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_nonneg (mul_nonneg hN.le hN2.le) hN4.le
  have hD1 : (0 : ℝ) < (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_pos (mul_pos (mul_pos (mul_pos h3 (pow_pos hc1 4)) hN) hN2) hN4
  have hDle : (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)
      ≤ (3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) := by
    have hd : (0 : ℝ) ≤ (3 + α) * (c n α ^ 4 - c 101 α ^ 4) *
        (((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) :=
      mul_nonneg (mul_nonneg h3.le (by linarith)) hprod
    nlinarith [hd]
  -- step A: enlarge the denominator's `c` from `c n` down to `c 101`
  have stepA : T1 n α
      ≤ 24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
          ((3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
    rw [T1]
    exact div_le_div_of_nonneg_left (by positivity) hD1 hDle
  refine stepA.trans ?_
  -- step B: the certificate, with the same `c 101` on both sides
  have hT101 : T1 101 α = 24 * (100 - 2 * α) ^ 2 / ((3 + α) * c 101 α ^ 4 * 1081500) := by
    simp only [T1]
    norm_num
    ring_nf
  have hD2 : (0 : ℝ) < 100 * ((3 + α) * c 101 α ^ 4 * 1081500) := by
    have h4 := pow_pos hc1 4
    positivity
  have hRHS : 101 / 100 * T1 101 α
      = 101 * (24 * (100 - 2 * α) ^ 2) / (100 * ((3 + α) * c 101 α ^ 4 * 1081500)) := by
    rw [hT101]
    field_simp
  rw [hRHS, div_le_div_iff₀ hD1 hD2]
  have hj : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail1_poly (j := (n : ℝ) - 101) hj hα hα'
  have hscale : (0 : ℝ) ≤ 24 * (3 + α) * c 101 α ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcert hscale]

/-! ### The second tail term -/

/-- `√B ≤ 12/13` on `0 ≤ α ≤ 17`, since `B ≤ 17/20 ≤ (12/13)²`.  A rational bound is enough
here, and avoids carrying a square root into the step ratio. -/
lemma sqrtB_le (hα : 0 ≤ α) (hα' : α ≤ 17) : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hB : α / (3 + α) ≤ 144 / 169 := by
    rw [div_le_div_iff₀ h3 (by norm_num)]
    linarith
  calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt (144 / 169) := Real.sqrt_le_sqrt hB
    _ = 12 / 13 := by
        rw [show (144 : ℝ) / 169 = (12 / 13) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12 / 13)]

/-- One step of the geometric decay: `T2` decreases with `n` on `n ≥ 101`. -/
lemma T2_step (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 (n + 1) α ≤ T2 n α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := sqrtB_le hα hα'
  have hA1 : A (n + 1) α = ((n : ℝ) - 2 * α) / (n : ℝ) := by
    simp only [A, M]
    push_cast
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) from by ring]
    field_simp
  have hA2 : A n α = ((n : ℝ) - 1 - 2 * α) / ((n : ℝ) - 1) := by
    simp only [A, M]
    field_simp
  have hk : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail2_poly (k := (n : ℝ) - 101) hk hα hα'
  have hCn1 : (0 : ℝ) ≤ A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1)
      * (((n + 1 : ℕ) : ℝ) - 2) / (16 * (3 + α)) := by
    have hM : (0 : ℝ) ≤ M (n + 1) := by simp only [M]; push_cast; linarith
    have h2 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
    have h1 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    positivity
  -- the coefficient inequality
  have hstep : A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
        / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
      ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α)) := by
    refine le_trans (mul_le_mul_of_nonneg_left hb1 hCn1) ?_
    rw [← sub_nonneg]
    have key : A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          - A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
              / (16 * (3 + α)) * (12 / 13)
        = (13 * ((n : ℝ) - 1 - 2 * α) ^ 2 * ((n : ℝ) - 2) * (n : ℝ) ^ 2
            - 12 * ((n : ℝ) - 2 * α) ^ 2 * ((n : ℝ) + 1) * ((n : ℝ) - 1) ^ 2)
          / (208 * (3 + α) * (n : ℝ) * ((n : ℝ) - 1)) := by
      simp only [hA1, hA2, M]
      push_cast
      field_simp
      ring
    rw [key]
    refine div_nonneg ?_ (by positivity)
    nlinarith [hcert]
  have hexp : n + 1 - 4 = (n - 4) + 1 := by omega
  calc T2 (n + 1) α
      = A (n + 1) α ^ 2 * ((n + 1 : ℕ) : ℝ) * M (n + 1) * (((n + 1 : ℕ) : ℝ) - 2)
            / (16 * (3 + α)) * Real.sqrt (α / (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) := by
        rw [T2, hexp, pow_succ]
        ring
    _ ≤ A n α ^ 2 * (n : ℝ) * M n * ((n : ℝ) - 2) / (16 * (3 + α))
          * Real.sqrt (α / (3 + α)) ^ (n - 4) :=
        mul_le_mul_of_nonneg_right hstep (pow_nonneg hb0 _)
    _ = T2 n α := by rw [T2]

/-- `T2` is bounded by its value at `n = 101`. -/
lemma T2_le (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : T2 n α ≤ T2 101 α := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (T2_step hm hα hα').trans ih

/-! ### The bound with no degree left in it -/

/-- The elementary bound at `n = 101`, with `√B` removed and `α` the only variable. -/
@[expose]
noncomputable def Ut (α : ℝ) : ℝ :=
  1 / 6 + 1 / (4 * (3 + α)) + 1 / 200 + 1 / (400 * (3 + α)) + 101 / 100 * T1 101 α
    + (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48

/-- **`U` is bounded by an expression in `α` alone**, for every `n ≥ 101`.  This is where the
degree leaves the argument. -/
theorem U_le_Ut (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) : U n α ≤ Ut α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM : (100 : ℝ) ≤ M n := by simp only [M]; linarith
  have hcpos : (0 : ℝ) < c n α := by
    have := c_ge_of_large hn hα hα'
    linarith
  rw [U_eq (by omega) hα (ne_of_gt hcpos), Ut]
  have e1 : 1 / (2 * M n) ≤ 1 / 200 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have e2 : 1 / (4 * M n * (3 + α)) ≤ 1 / (400 * (3 + α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e3 := T1_le hn hα hα'
  have hB : (0 : ℝ) ≤ α / (3 + α) := div_nonneg hα (by linarith)
  have hb0 : (0 : ℝ) ≤ Real.sqrt (α / (3 + α)) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (α / (3 + α)) ≤ 1 := by
    have hle : α / (3 + α) ≤ 1 := by rw [div_le_one h3]; linarith
    calc Real.sqrt (α / (3 + α)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hpow : Real.sqrt (α / (3 + α)) ^ (101 - 4) ≤ (α / (3 + α)) ^ 48 := by
    have h97 : Real.sqrt (α / (3 + α)) ^ (101 - 4)
        = (α / (3 + α)) ^ 48 * Real.sqrt (α / (3 + α)) := by
      rw [show (101 : ℕ) - 4 = 2 * 48 + 1 by norm_num, pow_succ, pow_mul, Real.sq_sqrt hB]
    rw [h97]
    nlinarith [pow_nonneg hB 48]
  have e4 : T2 101 α
      ≤ (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α)) * (α / (3 + α)) ^ 48 := by
    have hA101 : A 101 α = (100 - 2 * α) / 100 := by
      simp only [A, M]
      norm_num
      ring
    have hT2 : T2 101 α = (100 - 2 * α) ^ 2 / 100 * 101 * 99 / (16 * (3 + α))
        * Real.sqrt (α / (3 + α)) ^ (101 - 4) := by
      simp only [T2, hA101, M]
      norm_num
      ring_nf
      tauto
    rw [hT2]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have e5 := (T2_le hn hα hα').trans e4
  linarith

end Sendov
