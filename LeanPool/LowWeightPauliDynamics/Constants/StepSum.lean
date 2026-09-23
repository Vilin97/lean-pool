/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Constants.Entry

/-!
# The step-sum slot count and the rung-weight product

This file provides two elementary estimates used by the summed truncation bound
`apd:eq:total_high_weight_norm` in the proof of `apd:thm:one_step_truncation_error`: the sum over
Trotter steps of the layer-slot binomials, and the closed form of the rung-weight product
`∏ w_j`.

## Main results

* `sum_pow_le`: `Σ_{d=1}^{r} d^m ≤ (r+1)^{m+1}/(m+1)`.
* `sum_choose_mul_le`: the slot count `Σ_{d=1}^{r} C(dΓ, K) ≤ ((r+1)Γ)^{K+1} / (Γ · (K+1)!)`.
* `prod_rungW_eq`: `∏_{j=2}^{n+1} w_j = (k_h−1)^n ∏_{i=1}^{n} (i+c)`.
* `prod_shift_le`, `prod_shift_ratio`: comparison of `∏_{i=1}^{n}(i+c)` with the shifted product
  `∏_{i=2}^{n+1}(i+c)`.

## The slot count

Summing the per-step bound over the `r` Trotter steps uses

  `Σ_{d=1}^{r} C(dΓ, K) ≤ ((r+1)Γ)^{K+1} / (Γ · (K+1)!)`,

which is `sum_choose_mul_le` below. The paper uses it with `K = m*` for the leading sector; the
ladder assembly (`Lean4LPD.Ladder.ChainBound`) applies it once per sector `K = k`. Two remarks.

**The right-hand side is reproduced exactly.** The proof has two steps, `C(n,k) ≤ n^k/k!` and
`Σ_{d=1}^{r} d^K ≤ (r+1)^{K+1}/(K+1)`, and their composition is *identically* the right-hand side
above; nothing further is discarded.

**`Γ` is a positive layer count.** It is a natural number because it counts the layers of the
decomposition `H = ∑_{γ=1}^{Γ} H_γ` in `apd:thm:one_step_truncation_error`, and `C(dΓ, K)` counts
layer slots, so the natural-number type is not an extra restriction relative to the paper's
theorem.

## The rung-weight product

With `w_j = (k_h−1)(j−1+c)` the rung product has the closed form

  `∏_{j=2}^{m*+2} w_j = (k_h−1)^{m*+1} ∏_{i=1}^{m*+1} (i+c)`,

which is `prod_rungW_eq`. The estimate displayed with `apd:eq:total_high_weight_norm` is written
in terms of the shifted product `∏_{j=2}^{m*+2} (j+c)`. `prod_shift_le` shows that the shifted
product is the *larger* of the two, and `prod_shift_ratio` that their ratio is exactly
`(m*+2+c)/(1+c)`. Bounds built on the exact product are therefore stronger than the paper's
statement and imply it.

The companion estimate `∏_{i=1}^{n}(i+c) ≤ n!·(e·n)^c` is **not** in this file: it needs real
powers and a harmonic-sum bound, and is proved in `Lean4LPD.Constants.AssemblyBound` as
`prod_add_one_le_factorial_exp_rpow` (with `prod_shifted_le_factorial_exp_rpow` for the shifted
product).
-/

namespace Lean4LPD

open Finset

/-- `d^m ≤ ((d+1)^{m+1} − d^{m+1})/(m+1)` for `d ≥ 1`, the integral comparison behind the slot
count, in the form Bernoulli's inequality supplies it. -/
lemma pow_le_sub_pow {d : ℝ} (hd : 1 ≤ d) (m : ℕ) :
    ((m : ℝ) + 1) * d ^ m ≤ (d + 1) ^ (m + 1) - d ^ (m + 1) := by
  have hdpos : (0 : ℝ) < d := by linarith
  have hinv : (-2 : ℝ) ≤ 1 / d := by
    have : (0 : ℝ) ≤ 1 / d := by positivity
    linarith
  have hb : (1 : ℝ) + ((m : ℝ) + 1) * (1 / d) ≤ (1 + 1 / d) ^ (m + 1) := by
    have h := one_add_mul_le_pow hinv (m + 1)
    push_cast at h
    linarith [h]
  have hsplit : (d + 1) ^ (m + 1) = d ^ (m + 1) * (1 + 1 / d) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hdm : (0 : ℝ) < d ^ (m + 1) := pow_pos hdpos _
  rw [hsplit]
  have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hdm)
  have hcancel : d ^ (m + 1) * (1 + ((m : ℝ) + 1) * (1 / d))
      = d ^ (m + 1) + ((m : ℝ) + 1) * d ^ m := by
    rw [pow_succ]
    field_simp
  rw [hcancel] at hmul
  linarith [hmul]

/-- **`Σ_{d=1}^{r} d^m ≤ (r+1)^{m+1}/(m+1)`**, the integral comparison, by telescoping
`pow_le_sub_pow`. Written over `range r` with body `(i+1)^m` so that no `ℕ` subtraction appears. -/
theorem sum_pow_le (m r : ℕ) :
    ∑ i ∈ range r, ((i : ℝ) + 1) ^ m ≤ ((r : ℝ) + 1) ^ (m + 1) / ((m : ℝ) + 1) := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hterm : ∀ i ∈ range r, ((m : ℝ) + 1) * (((i : ℝ) + 1) ^ m)
      ≤ (((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1) := by
    intro i _
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    exact pow_le_sub_pow hi m
  have hsum : ((m : ℝ) + 1) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ m
      ≤ ∑ i ∈ range r, ((((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have htel : ∑ i ∈ range r, ((((i : ℝ) + 1) + 1) ^ (m + 1) - ((i : ℝ) + 1) ^ (m + 1))
      = ((r : ℝ) + 1) ^ (m + 1) - 1 := by
    have := Finset.sum_range_sub (f := fun i : ℕ => ((i : ℝ) + 1) ^ (m + 1)) r
    simpa using this
  rw [le_div_iff₀ hm1, mul_comm]
  rw [htel] at hsum
  linarith [hsum]

/-- **The slot count.** The sum over Trotter steps of the layer-slot binomials, the step that
leads to `apd:eq:total_high_weight_norm` in the proof of `apd:thm:one_step_truncation_error`:

  `Σ_{d=1}^{r} C(dΓ, K) ≤ ((r+1)Γ)^{K+1} / (Γ · (K+1)!)`.

`Γ` is a positive **natural** number, because it is a layer count and `C(dΓ, K)` counts layer
slots (see the module docstring). The two steps — `C(n,k) ≤ n^k/k!` and `sum_pow_le` — reproduce
the right-hand side exactly, so nothing is thrown away. -/
theorem sum_choose_mul_le (K r G : ℕ) (hG : 1 ≤ G) :
    ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := by
  have hGpos : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
  have hKfac : (0 : ℝ) < (Nat.factorial K : ℝ) := by exact_mod_cast Nat.factorial_pos K
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  -- bound each binomial
  have hbin : ∀ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((i : ℝ) + 1) ^ K) := by
    intro i _
    have h := Nat.choose_le_pow_div (α := ℝ) K ((i + 1) * G)
    have hcast : (((i + 1) * G : ℕ) : ℝ) = ((i : ℝ) + 1) * (G : ℝ) := by push_cast; ring
    rw [hcast] at h
    calc (((i + 1) * G).choose K : ℝ)
        ≤ (((i : ℝ) + 1) * (G : ℝ)) ^ K / (Nat.factorial K : ℝ) := h
      _ = (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((i : ℝ) + 1) ^ K) := by
          rw [mul_pow]; ring
  have hstep : ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ K := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hbin
  have hpow := sum_pow_le K r
  have hcoef : (0 : ℝ) ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) := by positivity
  have hfac1 : (Nat.factorial (K + 1) : ℝ) = ((K : ℝ) + 1) * (Nat.factorial K : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfinal : (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((r : ℝ) + 1) ^ (K + 1) / ((K : ℝ) + 1))
      = (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := by
    rw [hfac1, mul_pow]
    field_simp
    ring
  calc ∑ i ∈ range r, (((i + 1) * G).choose K : ℝ)
      ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * ∑ i ∈ range r, ((i : ℝ) + 1) ^ K := hstep
    _ ≤ (G : ℝ) ^ K / (Nat.factorial K : ℝ) * (((r : ℝ) + 1) ^ (K + 1) / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hpow hcoef
    _ = (((r : ℝ) + 1) * G) ^ (K + 1) / ((G : ℝ) * (Nat.factorial (K + 1) : ℝ)) := hfinal

/-- **The rung product in closed form.** `∏_{j=2}^{n+1} w_j = (k_h−1)^n ∏_{i=1}^{n} (i+c)`,
written over `range n`. The second factor is smaller than the shifted product
`∏_{j=2}^{n+1}(j+c)` in which the estimate of `apd:eq:total_high_weight_norm` is displayed — see
`prod_shift_le` and `prod_shift_ratio`. -/
lemma prod_rungW_eq (kh1 c : ℝ) (n : ℕ) :
    ∏ i ∈ range n, rungW kh1 c (i + 2) = kh1 ^ n * ∏ i ∈ range n, ((i : ℝ) + 1 + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
    have hr : rungW kh1 c (n + 2) = kh1 * ((n : ℝ) + 1 + c) := by
      unfold rungW; push_cast; ring
    rw [hr, pow_succ]
    ring

/-- The exact product is dominated by the shifted one: `∏_{i=1}^{n}(i+c) ≤ ∏_{i=2}^{n+1}(i+c)`
for `c ≥ 0`, termwise. Hence a bound proved with the exact product of `prod_rungW_eq` implies the
same bound with the shifted product, the form displayed in the paper. -/
lemma prod_shift_le {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∏ i ∈ range n, ((i : ℝ) + 1 + c) ≤ ∏ i ∈ range n, ((i : ℝ) + 2 + c) := by
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  · linarith

/-- The shifted product exceeds the exact one by exactly the factor `(n+1+c)/(1+c)`:
`(∏_{i<n}(i+2+c)) · (1+c) = (∏_{i<n}(i+1+c)) · (n+1+c)`. Both products telescope against each
other, so the gap between them is a single ratio rather than a factor accumulating with `n`. -/
lemma prod_shift_ratio (c : ℝ) (n : ℕ) :
    (∏ i ∈ range n, ((i : ℝ) + 2 + c)) * (1 + c)
      = (∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast
    calc (∏ i ∈ range n, ((i : ℝ) + 2 + c)) * ((n : ℝ) + 2 + c) * (1 + c)
        = ((∏ i ∈ range n, ((i : ℝ) + 2 + c)) * (1 + c)) * ((n : ℝ) + 2 + c) := by ring
      _ = ((∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c)) * ((n : ℝ) + 2 + c) := by
          rw [ih]
      _ = (∏ i ∈ range n, ((i : ℝ) + 1 + c)) * ((n : ℝ) + 1 + c) * ((n : ℝ) + 1 + 1 + c) := by
          ring

end Lean4LPD
