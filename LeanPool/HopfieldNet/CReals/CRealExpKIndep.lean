/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealExpSmall

/-!
# `exp`: cross-`k` independence (range reduction)

This file is organized so that the only hard step is the **halving lemma**
for the small-input (|x| ≤ 1/2) exponential approximation:

`exp(x) = (exp(x/2))^2`.

The proof is done by:
1. explicit coefficient algebra on the truncated Taylor polynomials, and
2. explicit tail bounds, reusing `exp_tail_bound_core`.

Once the halving lemma is in place, the cross-`k` independence lemma is a
short iteration argument.
-/

namespace Computable
namespace CReal

open scoped BigOperators

open CReal.Pre

/-- Helper: `|x/2| ≤ 1/2` whenever `|x| ≤ 1/2`. -/
lemma abs_div_two_le_half {x : ℚ} (hx : |x| ≤ (1/2 : ℚ)) : |x / 2| ≤ (1/2 : ℚ) := by
  -- `|x/2| = |x|/2 ≤ (1/2)/2 ≤ 1/2`
  have h₁ : |x / 2| = |x| / 2 := by
    simp [abs_div]
  have h₂ : |x| / 2 ≤ (1/2 : ℚ) / 2 := by
    nlinarith [hx]
  have h₃ : (1/2 : ℚ) / 2 ≤ (1/2 : ℚ) := by
    nlinarith
  nlinarith [h₁, h₂, h₃]

/-!
## Coefficient algebra

The key identity is:

`∑ i=0..k 1/(i!(k-i)!) = 2^k / k!`.

This yields the exact diagonal/cauchy-product identity needed to match
the first `N` coefficients of `P_N(x)` and `P_N(x/2)^2`.
-/

/-- Binomial-coefficient sum in `ℚ`: `∑ choose k i = 2^k`. -/
lemma sum_choose_eq_two_pow (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℚ)) = (2 : ℚ) ^ k := by
  have hnat : (∑ i ∈ Finset.range (k + 1), Nat.choose k i) = 2 ^ k := by
    simpa using (Nat.sum_range_choose k) --Nat.sum_choose_eq_two_pow k
  exact_mod_cast hnat

/-- Convert `1/(i!(k-i)!)` into a binomial coefficient over `k!`. -/
lemma inv_factorial_mul_inv_factorial_eq_choose_div (k i : ℕ) (hi : i ≤ k) :
    (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))
      = (Nat.choose k i : ℚ) / Nat.factorial k := by
  -- In ℕ: `choose k i * i! * (k-i)! = k!`.
  have hnat :
      Nat.choose k i * Nat.factorial i * Nat.factorial (k - i) = Nat.factorial k := by
    simpa [Nat.mul_assoc] using (Nat.choose_mul_factorial_mul_factorial hi)
  -- Cast to `ℚ`.
  have hq :
      (Nat.choose k i : ℚ) * (Nat.factorial i : ℚ) * (Nat.factorial (k - i) : ℚ)
        = (Nat.factorial k : ℚ) := by
    exact_mod_cast hnat
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero k)
  have hi : (Nat.factorial i : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero i)
  have hki : (Nat.factorial (k - i) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (k - i))
  -- Rearrange in `ℚ` and divide by `k!`.
  -- `field_simp` clears denominators; the remaining goal is the factorial identity in `ℚ`,
  -- which is exactly `hq` up to commutativity/associativity.
  field_simp [hk, hi, hki]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hq.symm

/-- The classical diagonal factorial identity, stated in `ℚ`. -/
lemma sum_inv_factorial_mul_inv_factorial (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i)))
      = (2 : ℚ) ^ k / Nat.factorial k := by
  calc
    (∑ i ∈ Finset.range (k + 1),
        (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i)))
        =
      (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℚ) / Nat.factorial k) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact inv_factorial_mul_inv_factorial_eq_choose_div k i hik
    _ =
      (1 / Nat.factorial k) * (∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℚ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
    _ =
      (1 / Nat.factorial k) * (2 : ℚ) ^ k := by
        simp [sum_choose_eq_two_pow]
    _ = (2 : ℚ) ^ k / Nat.factorial k := by
        ring

/-- Exact diagonal (Cauchy-product) identity for exp coefficients:
`∑_{i=0..k} expCoeff(x/2,i) * expCoeff(x/2,k-i) = expCoeff(x,k)`. -/
lemma diag_sum_expCoeff_half (x : ℚ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        expCoeff (x / 2) i * expCoeff (x / 2) (k - i))
      = expCoeff x k := by
  have hsum :
      (∑ i ∈ Finset.range (k + 1),
          expCoeff (x / 2) i * expCoeff (x / 2) (k - i))
        = ((x / 2) ^ k) *
          (∑ i ∈ Finset.range (k + 1),
            (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))) := by
    -- First compute the summand pointwise, then factor out the constant `((x/2)^k)`.
    calc
      (∑ i ∈ Finset.range (k + 1),
          expCoeff (x / 2) i * expCoeff (x / 2) (k - i))
          =
        ∑ i ∈ Finset.range (k + 1),
          ((x / 2) ^ k) *
            ((1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hadd : i + (k - i) = k := Nat.add_sub_of_le hik
          have hi0 : (Nat.factorial i : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_ne_zero i)
          have hki0 : (Nat.factorial (k - i) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_ne_zero (k - i))
          -- Expand `expCoeff` so the factorial denominators are visible, then clear them.
          dsimp [expCoeff]
          field_simp [hi0, hki0]
          -- Remaining goal is `((x/2)^i) * ((x/2)^(k-i)) = (x/2)^k`.
          simpa [hadd] using (pow_add (x / 2) i (k - i)).symm
      _ = ((x / 2) ^ k) *
            (∑ i ∈ Finset.range (k + 1),
              (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))) := by
          -- `Finset.mul_sum` is the forward direction; we use it backwards.
          simpa using
            (Finset.mul_sum (s := Finset.range (k + 1))
              (f := fun i => (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i)))
              (a := (x / 2) ^ k)).symm
  calc
    (∑ i ∈ Finset.range (k + 1), expCoeff (x / 2) i * expCoeff (x / 2) (k - i))
        = ((x / 2) ^ k) *
            (∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))) := by
          simpa using hsum
    _ = ((x / 2) ^ k) * ((2 : ℚ) ^ k / Nat.factorial k) := by
          -- Avoid `simp` cancelling the common factor `((x/2)^k)` and producing disjunction goals.
          rw [sum_inv_factorial_mul_inv_factorial k]
    _ = x ^ k / Nat.factorial k := by
          have h2 : (2 : ℚ) ≠ 0 := by norm_num
          field_simp [div_eq_mul_inv, h2]
          -- Now it suffices to simplify `(x/2)^k * 2^k = x^k`.
          have hmul : ((1 / 2 : ℚ) * (2 : ℚ)) = 1 := by norm_num
          calc
            (x / 2) ^ k * 2 ^ k
                = (x ^ k * (1 / 2 : ℚ) ^ k) * 2 ^ k := by
                    simp [div_eq_mul_inv, mul_pow]
            _ = x ^ k * ((1 / 2 : ℚ) ^ k * 2 ^ k) := by
                    exact mul_assoc (x ^ k) ((1 / 2 : ℚ) ^ k) (2 ^ k)
            _ = x ^ k * (((1 / 2 : ℚ) * (2 : ℚ)) ^ k) := by
                    exact congrArg (fun t => x ^ k * t) (mul_pow (1 / 2 : ℚ) (2 : ℚ) k).symm
            _ = x ^ k := by
                    rw [hmul]
                    simp
    _ = expCoeff x k := by
          simp [expCoeff]

/-!
## Halving lemma: tail control

The remaining step is purely a finite-sum reindexing for the Cauchy product,
followed by triangle inequality and the existing tail bound `exp_tail_bound_core`.

The key bound (for any `N`) is:

`|P_N(x) - P_N(x/2)^2| ≤ ∑_{k=N+1..2N} |expCoeff x k|`.

This lemma is the only place where the Cauchy-product reindexing occurs.
-/

/-- Technical tail bound for the halving identity (finite-degree mismatch). -/
lemma expPartial_half_sq_le_tail (x : ℚ) (N : ℕ) :
    |expPartial x N - (expPartial (x / 2) N) * (expPartial (x / 2) N)|
      ≤ (Finset.Icc (N + 1) (2 * N)).sum (fun k => |expCoeff x k|) := by
  -- The proof is a direct coefficient computation:
  --   * Expand the square as a Cauchy product of finite sums.
  --   * Reindex by total degree `k = i+j` (via `Nat.antidiagonal`).
  --   * For `k ≤ N`, the diagonal sum matches exactly using `diag_sum_expCoeff_half`.
  --   * The remaining `k>N` terms are bounded by summing absolute values.
  --
  -- In Mathlib, the standard reindexing lemma is:
  --   `∑ i∈range(N+1) ∑ j∈range(N+1) f i j
  --      = ∑ k∈range(2N+1) ∑ p∈natAntidiagonal k, f p.1 p.2`
  --
  -- The following `simp` proof relies on that lemma and `abs_sum_le_sum_abs`.
  --
  -- If your local Mathlib uses a different lemma name for the antidiagonal reindexing,
  -- adjust the single rewrite line marked `-- REINDEX`.
  --
  -- REINDEX:
  -- (This is the only reindexing site in the file.)
  have hsq :
      (expPartial (x / 2) N) * (expPartial (x / 2) N)
        =
      (∑ k ∈ Finset.range (2 * N + 1),
        ∑ p ∈ Finset.antidiagonal k,
          (if p.1 ≤ N ∧ p.2 ≤ N then expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 else 0)) := by
    -- expand the product and reindex by `Nat.antidiagonal`
    -- Rewrite the RHS `if` as a filtered sum, so we can reindex by a genuine bijection.
    let cond : (ℕ × ℕ) → Prop := fun p => p.1 ≤ N ∧ p.2 ≤ N
    let term : (ℕ × ℕ) → ℚ := fun p => expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2
    have hR :
        (∑ k ∈ Finset.range (2 * N + 1),
          ∑ p ∈ Finset.antidiagonal k,
            (if cond p then term p else 0))
          =
        ∑ z ∈ (Finset.range (2 * N + 1)).sigma (fun k => (Finset.antidiagonal k).filter cond),
          term z.snd := by
      -- convert the inner sums using `Finset.sum_filter`, then pack them as a sigma sum
      calc
        (∑ k ∈ Finset.range (2 * N + 1),
            ∑ p ∈ Finset.antidiagonal k, (if cond p then term p else 0))
            =
          (∑ k ∈ Finset.range (2 * N + 1),
            ∑ p ∈ Finset.antidiagonal k with cond p, term p) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simpa [term, cond] using
                (Finset.sum_filter (s := Finset.antidiagonal k) (p := cond) (f := term)).symm
        _ =
          ∑ z ∈ (Finset.range (2 * N + 1)).sigma (fun k => (Finset.antidiagonal k).filter cond),
            term z.snd := by
              -- `sum_sigma'` is the forward direction: iterated sum → sigma sum.
              simpa [term] using
                (Finset.sum_sigma' (s := Finset.range (2 * N + 1))
                  (t := fun k => (Finset.antidiagonal k).filter cond)
                  (f := fun _ p => term p))

    -- Expand the product as a sum over the cartesian product `range(N+1) × range(N+1)`.
    have hL :
        (expPartial (x / 2) N) * (expPartial (x / 2) N)
          =
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)), term p := by
      -- `sum_mul_sum` expands the product into a double sum, then `sum_product'` packages it.
      simp [expPartial, term, Finset.sum_mul_sum]
      -- remaining goal is the `range×range` packaging
      simpa using
        (Finset.sum_product' (s := Finset.range (N + 1)) (t := Finset.range (N + 1))
          (f := fun i j => expCoeff (x / 2) i * expCoeff (x / 2) j)).symm

    -- Bijection between the product square and the filtered antidiagonal sigma.
    have hBij :
        (∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)), term p)
          =
        ∑ z ∈ (Finset.range (2 * N + 1)).sigma (fun k => (Finset.antidiagonal k).filter cond),
          term z.snd := by
      -- Use `sum_bij'` with the map `(i,j) ↦ (i+j, (i,j))`.
      refine Finset.sum_bij'
        (i := fun p hp => (⟨p.1 + p.2, p⟩ : (k : ℕ) × (ℕ × ℕ)))
        (j := fun z hz => z.snd)
        ?_ ?_ ?_ ?_ ?_
      · -- map lands in the sigma finset
        intro p hp
        rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
        have hp1' : p.1 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hp1)
        have hp2' : p.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hp2)
        have hk : p.1 + p.2 < 2 * N + 1 := by
          exact Nat.lt_succ_of_le (by nlinarith)
        refine Finset.mem_sigma.mpr ?_
        refine ⟨Finset.mem_range.mpr hk, ?_⟩
        refine Finset.mem_filter.mpr ?_
        refine ⟨?_, ⟨hp1', hp2'⟩⟩
        -- membership in the antidiagonal at `p.1+p.2`
        simp [Finset.mem_antidiagonal]
      · -- inverse map lands in the product finset
        intro z hz
        rcases Finset.mem_sigma.mp hz with ⟨hz1, hz2⟩
        have hz2' := Finset.mem_filter.mp hz2
        have hcond : cond z.snd := hz2'.2
        refine Finset.mem_product.mpr ?_
        refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hcond.1),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hcond.2)⟩
      · -- left inverse
        intro p hp
        rfl
      · -- right inverse
        intro z hz
        -- `z ∈ sigma` gives `z.2 ∈ antidiagonal z.1`, hence `z.2.1+z.2.2=z.1`.
        rcases Finset.mem_sigma.mp hz with ⟨hz1, hz2⟩
        have hz2' := (Finset.mem_filter.mp hz2).1
        -- `mem_antidiagonal` is `p.1 + p.2 = k`.
        have : z.snd.1 + z.snd.2 = z.fst := by
          simpa [Finset.mem_antidiagonal] using (Finset.mem_antidiagonal.mp hz2')
        -- now the dependent pair is determined by the first component and the second is `z.snd`
        cases z with
        | mk k p =>
            -- after cases, `this : p.1 + p.2 = k`
            simp [this]
      · -- pointwise equality of summands
        intro p hp
        rfl

    -- Assemble, and unfold `cond`/`term` back into the original RHS.
    have hR' :
        (∑ k ∈ Finset.range (2 * N + 1),
          ∑ p ∈ Finset.antidiagonal k,
            (if p.1 ≤ N ∧ p.2 ≤ N then expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 else 0))
          =
        (∑ k ∈ Finset.range (2 * N + 1),
          ∑ p ∈ Finset.antidiagonal k,
            (if cond p then term p else 0)) := by
      -- just unfold the local definitions in the `if`
      simp [cond, term]

    -- Finish by rewriting via `hR`, `hL`, `hBij`.
    -- (We go through the sigma form because it is the one in bijection with the square.)
    calc
      (expPartial (x / 2) N) * (expPartial (x / 2) N)
          = ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)), term p := hL
      _ = ∑ z ∈ (Finset.range (2 * N + 1)).sigma (fun k => (Finset.antidiagonal k).filter cond),
            term z.2 := hBij
      _ = (∑ k ∈ Finset.range (2 * N + 1),
            ∑ p ∈ Finset.antidiagonal k, if cond p then term p else 0) := by
            simpa using hR.symm
      _ = (∑ k ∈ Finset.range (2 * N + 1),
            ∑ p ∈ Finset.antidiagonal k,
              (if p.1 ≤ N ∧ p.2 ≤ N then expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 else 0)) := by
            simp [hR']
  -- Split into `k ≤ N` (exact cancellation) and `k > N` (tail).
  -- After cancellation, apply `abs_sum_le_sum_abs` and the diagonal identity.
  -- The end result is the explicit tail sum in the statement.
  --
  -- NOTE: this is the only lemma that may require small adjustments to match
  -- your Mathlib's antidiagonal API.
  --classical
  -- Abbreviation for the degree-`k` contribution in the truncated square.
  let a : ℕ → ℚ := fun k =>
    ∑ p ∈ Finset.antidiagonal k,
      (if p.1 ≤ N ∧ p.2 ≤ N then expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 else 0)

  have hsq' :
      (expPartial (x / 2) N) * (expPartial (x / 2) N)
        = ∑ k ∈ Finset.range (2 * N + 1), a k := by
    simpa [a] using hsq

  -- For `k ≤ N`, the truncation is vacuous and the diagonal sum is exact.
  have ha_eq (k : ℕ) (hk : k ≤ N) : a k = expCoeff x k := by
    have htrue : ∀ p ∈ Finset.antidiagonal k, p.1 ≤ N ∧ p.2 ≤ N := by
      intro p hp
      exact ⟨(Finset.antidiagonal.fst_le hp).trans hk, (Finset.antidiagonal.snd_le hp).trans hk⟩
    have hak :
        a k = ∑ p ∈ Finset.antidiagonal k, expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 := by
      dsimp [a]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hp' := htrue p hp
      simp [hp']
    -- Rewrite the antidiagonal sum to the standard `range (k+1)` form and use the diagonal identity.
    have hr :
        (∑ p ∈ Finset.antidiagonal k, expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2)
          =
        (∑ i ∈ Finset.range (k + 1), expCoeff (x / 2) i * expCoeff (x / 2) (k - i)) := by
      simpa using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
          (f := fun p : ℕ × ℕ => expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2) k)
    -- put together
    simpa [hak, hr] using (diag_sum_expCoeff_half x k)

  have hlow : (∑ k ∈ Finset.range (N + 1), a k) = expPartial x N := by
    have :
        (∑ k ∈ Finset.range (N + 1), a k) = ∑ k ∈ Finset.range (N + 1), expCoeff x k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      simp [ha_eq k hk']
    simpa [expPartial] using this

  have hsplit :
      (∑ k ∈ Finset.range (2 * N + 1), a k)
        =
      (∑ k ∈ Finset.range (N + 1), a k) + ∑ t ∈ Finset.range N, a (N + 1 + t) := by
    -- `2*N+1 = (N+1) + N`
    simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_add (f := a) (n := N + 1) (m := N))

  have hdiff :
      expPartial x N - (∑ k ∈ Finset.range (2 * N + 1), a k)
        = - ∑ t ∈ Finset.range N, a (N + 1 + t) := by
    calc
      expPartial x N - (∑ k ∈ Finset.range (2 * N + 1), a k)
          = expPartial x N - ((∑ k ∈ Finset.range (N + 1), a k) + ∑ t ∈ Finset.range N, a (N + 1 + t)) := by
              simp [hsplit]
      _ = expPartial x N - (∑ k ∈ Finset.range (N + 1), a k) - ∑ t ∈ Finset.range N, a (N + 1 + t) := by
              ring
      _ = - ∑ t ∈ Finset.range N, a (N + 1 + t) := by
              simp [hlow]

  -- Pointwise bound: the truncated diagonal coefficient is bounded by the full coefficient.
  have ha_le (k : ℕ) : |a k| ≤ |expCoeff x k| := by
    let f : (ℕ × ℕ) → ℚ := fun p =>
      if p.1 ≤ N ∧ p.2 ≤ N then expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2 else 0
    have h1 : |a k| ≤ ∑ p ∈ Finset.antidiagonal k, |f p| := by
      simpa [a, f] using
        (Finset.abs_sum_le_sum_abs (f := f) (s := Finset.antidiagonal k))
    have h2 :
        (∑ p ∈ Finset.antidiagonal k, |f p|)
          ≤
        (∑ p ∈ Finset.antidiagonal k,
            |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2|) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      by_cases hcond : p.1 ≤ N ∧ p.2 ≤ N
      · simp [f, hcond]
      · have : (0 : ℚ) ≤ |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2| := abs_nonneg _
        simpa [f, hcond] using this
    have h3 :
        (∑ p ∈ Finset.antidiagonal k,
            |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2|)
          = |expCoeff x k| := by
      -- rewrite the antidiagonal sum to a range sum
      have hrange :
          (∑ p ∈ Finset.antidiagonal k,
              |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2|)
            =
          ∑ i ∈ Finset.range (k + 1),
            |expCoeff (x / 2) i * expCoeff (x / 2) (k - i)| := by
        simpa using
          (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
            (f := fun p : ℕ × ℕ => |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2|) k)
      -- simplify each term in the range sum
      have hterm :
          ∀ i ∈ Finset.range (k + 1),
            |expCoeff (x / 2) i * expCoeff (x / 2) (k - i)|
              = |x / 2| ^ k / (Nat.factorial i * Nat.factorial (k - i)) := by
        intro i hi
        have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        -- proven pattern: clear factorial denominators and use `pow_add`.
        have hadd : i + (k - i) = k := Nat.add_sub_of_le hik
        dsimp [expCoeff]
        simp [abs_mul, abs_div, abs_pow]
        field_simp
        have : (|x| / 2) ^ i * (|x| / 2) ^ (k - i) = (|x| / 2) ^ k := by
          simpa [hadd] using (pow_add (|x| / 2) i (k - i)).symm
        simpa using this
      -- factor out `|x/2|^k` and use the factorial identity
      calc
        (∑ p ∈ Finset.antidiagonal k,
              |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2|)
            = ∑ i ∈ Finset.range (k + 1),
                |x / 2| ^ k / (Nat.factorial i * Nat.factorial (k - i)) := by
                -- via `hrange` and `hterm`
                refine hrange.trans ?_
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [hterm i hi]
        _ = |x / 2| ^ k *
              (∑ i ∈ Finset.range (k + 1), (1 : ℚ) / (Nat.factorial i * Nat.factorial (k - i))) := by
                simp [div_eq_mul_inv, Finset.mul_sum]
        _ = |x / 2| ^ k * ((2 : ℚ) ^ k / Nat.factorial k) := by
                rw [sum_inv_factorial_mul_inv_factorial k]
        _ = |expCoeff x k| := by
                -- simplify to `|x|^k / k!`
                have hk0 : (Nat.factorial k : ℚ) ≠ 0 := by
                  exact_mod_cast (Nat.factorial_ne_zero k)
                -- move to a common denominator and use `(a/2)^k * 2^k = a^k`
                have hx2 :
                    |x / 2| ^ k * ((2 : ℚ) ^ k / Nat.factorial k) = |x| ^ k / Nat.factorial k := by
                  simp [abs_div]
                  field_simp [hk0]
                  simp [div_eq_mul_inv, mul_pow]
                -- finish
                simpa [expCoeff, abs_pow, abs_div] using hx2
    -- assemble the bounds (avoid `le_trans` ambiguity in the `CReal` namespace)
    calc
      |a k| ≤ ∑ p ∈ Finset.antidiagonal k, |f p| := h1
      _ ≤ ∑ p ∈ Finset.antidiagonal k, |expCoeff (x / 2) p.1 * expCoeff (x / 2) p.2| := h2
      _ = |expCoeff x k| := h3

  -- Now rewrite the difference as a tail sum and bound it termwise.
  calc
    |expPartial x N - (expPartial (x / 2) N) * (expPartial (x / 2) N)|
        = |expPartial x N - ∑ k ∈ Finset.range (2 * N + 1), a k| := by
            simp [hsq']
    _ = |∑ t ∈ Finset.range N, a (N + 1 + t)| := by
            simp [hdiff]
    _ ≤ ∑ t ∈ Finset.range N, |a (N + 1 + t)| := by
            simpa using
              (Finset.abs_sum_le_sum_abs (f := fun t => a (N + 1 + t)) (s := Finset.range N))
    _ ≤ ∑ t ∈ Finset.range N, |expCoeff x (N + 1 + t)| := by
            refine Finset.sum_le_sum ?_
            intro t ht
            simpa using ha_le (N + 1 + t)
    _ = ∑ k ∈ Finset.Icc (N + 1) (2 * N), |expCoeff x k| := by
            -- shift `range N` to `Icc (N+1) (2N)` via `Ico` and `sum_Ico_add'`
            have :
                (∑ t ∈ Finset.range N, |expCoeff x (N + 1 + t)|)
                  =
                ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), |expCoeff x k| := by
              -- `range N = Ico 0 N` and shift by `N+1`
              -- (write it in small steps to avoid simp recursion)
              have hIco :
                  (∑ t ∈ Finset.Ico 0 N, |expCoeff x (t + (N + 1))|)
                    =
                  ∑ k ∈ Finset.Ico (0 + (N + 1)) (N + (N + 1)), |expCoeff x k| :=
                (Finset.sum_Ico_add' (f := fun k : ℕ => |expCoeff x k|) (a := 0) (b := N) (c := N + 1))
              -- rewrite the left endpoint `0 + (N+1)` and the right endpoint `N + (N+1)`
              have hIco' :
                  (∑ t ∈ Finset.Ico 0 N, |expCoeff x (t + (N + 1))|)
                    =
                  ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), |expCoeff x k| := by
                simp only [zero_add] at hIco
                convert hIco using 2
                · ring_nf
              -- rewrite `range N` as `Ico 0 N`
              convert hIco' using 1
              · congr 1
                ext t
                simp only [Finset.mem_range, Finset.mem_Ico, Nat.zero_le, true_and]
                ring_nf
            convert this using 1


/-- Tail bound specialized to `|x| ≤ 1/2`: the mismatch is `≤ 1/2^(N-2)`. -/
lemma expPartial_half_sq_bound (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (N : ℕ) :
    |expPartial x N - (expPartial (x / 2) N) * (expPartial (x / 2) N)|
      ≤ (1 : ℚ) / 2 ^ (N - 2) := by
  -- First reduce to the explicit tail sum from `expPartial_half_sq_le_tail`,
  -- then discharge by `exp_tail_bound_core` on `|x|`.
  have h₁ := expPartial_half_sq_le_tail x N
  -- Bound the Icc-sum by the absolute tail of `expPartial |x|`.
  -- Finally apply `exp_tail_bound_core` at indices `n := N-2`, `m := 2N-2`.
  --
  -- (This lemma is intentionally phrased so the last step is a direct application of
  -- `exp_tail_bound_core`.)
  --
  -- A conservative bound is enough for the downstream equivalence proof.
  -- `x : ℚ`, so use absolute value `|x|` (not `||x||`, which is parsed as `||`).
  have hx_abs : |x| ≤ (1/2 : ℚ) := by simpa using hx
  have hcore :
      |expPartial |x| (2 * N) - expPartial |x| N|
        ≤ (1 : ℚ) / 2 ^ (N - 2) := by
    -- `exp_tail_bound_core` is stated for truncation levels `expTruncLevel n = n+2`,
    -- so we split on whether `N ≥ 2` to rewrite `expTruncLevel (N-2) = N`.
    by_cases hN2 : 2 ≤ N
    · -- Main case: `N ≥ 2`, so `N-2+2 = N` and similarly for `2N`.
      have hle : (N - 2) ≤ (2 * N - 2) := by
        -- `N ≤ 2*N`, hence `N-2 ≤ 2*N-2`.
        have hN : N ≤ 2 * N := by
          -- `N ≤ N + N = 2*N`
          simp [two_mul]
        exact Nat.sub_le_sub_right hN 2
      -- `exp_tail_bound_core` expects `| |x| | ≤ 1/2`; use `abs_abs`.
      have hx_abs' : |(|x|)| ≤ (1/2 : ℚ) := by
        simpa [abs_abs] using hx_abs
      have h :=
        exp_tail_bound_core |x| hx_abs' (N - 2) (2 * N - 2) hle
      -- Rewrite `expTruncLevel (N-2) = N` and `expTruncLevel (2N-2) = 2N`.
      have h2N : 2 ≤ 2 * N := by
        -- `2 ≤ 4` and `4 ≤ 2*N` (since `N ≥ 2`)
        have h4 : 4 ≤ 2 * N := by
          simpa [two_mul] using (Nat.mul_le_mul_left 2 hN2)
        exact _root_.le_trans (by decide : 2 ≤ 4) h4
      simpa [expTruncLevel, Nat.sub_add_cancel hN2, Nat.sub_add_cancel h2N] using h
    · -- Small cases `N = 0` or `N = 1`: RHS is `1` (since `N-2 = 0`), and LHS is easily bounded.
      have hNle1 : N ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hN2)
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hNle1) with rfl | rfl
      · -- `N = 0`
        simp [expPartial]
      · -- `N = 1`
        have hdiff : expPartial |x| 2 - expPartial |x| 1 = expCoeff |x| 2 := by
          simp [expPartial, Finset.sum_range_succ]
        have habs : |expPartial |x| 2 - expPartial |x| 1| = |expCoeff |x| 2| := by
          simp [hdiff]
        -- Bound the single coefficient by `1`.
        have hx0 : 0 ≤ |x| := abs_nonneg x
        have hhalf0 : 0 ≤ (1/2 : ℚ) := by positivity
        have hx_sq : |x| ^ 2 ≤ (1/2 : ℚ) ^ 2 := by
          have hmul : |x| * |x| ≤ (1/2 : ℚ) * (1/2 : ℚ) :=
            mul_le_mul hx_abs hx_abs hx0 hhalf0
          simpa [pow_two] using hmul
        -- `|expCoeff |x| 2| = |x|^2 / 2`
        have hcoeff : |expCoeff |x| 2| = |x| ^ 2 / 2 := by
          -- factorial 2 = 2
          simp [expCoeff, pow_two, abs_div]
        -- Here `N-2 = 0`, so RHS is `1`.
        have : |expCoeff |x| 2| ≤ (1 : ℚ) := by
          -- `|x|^2 ≤ 1/4` hence `|x|^2/2 ≤ 1` (crude bound is fine)
          nlinarith [hx_sq]
        simpa [habs, hcoeff] using this
  -- Combine (tail sum ≤ expPartial difference ≤ bound).
  -- (If needed, insert a lemma rewriting the Icc tail sum into the expPartial difference.)
  -- Rewrite the tail sum as the absolute `expPartial` difference (all coefficients are nonnegative),
  -- then use `hcore`.
  have htail :
      (∑ k ∈ Finset.Icc (N + 1) (2 * N), |expCoeff x k|) ≤ (1 : ℚ) / 2 ^ (N - 2) := by
    -- First express the tail sum as a difference of partial sums at `|x|`.
    have hsum :
        (∑ k ∈ Finset.Icc (N + 1) (2 * N), |expCoeff x k|)
          = |expPartial |x| (2 * N) - expPartial |x| N| := by
      -- Step 1: `|expCoeff x k| = expCoeff |x| k`.
      have habsCoeff (k : ℕ) : |expCoeff x k| = expCoeff |x| k := by
        simp [expCoeff, abs_div, abs_pow]
      -- Step 2: rewrite the Icc-sum as an Ico-sum and identify it with the difference of partial sums.
      have hmono : (N + 1) ≤ (2 * N + 1) := by
        have hN : N ≤ 2 * N := by
          simp [two_mul]
        exact Nat.succ_le_succ hN
      have hdecomp :
          (∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), expCoeff |x| k)
            = expPartial |x| (2 * N) - expPartial |x| N := by
        -- Use `sum_range_add_sum_Ico` and rearrange.
        have hsum' :=
          (Finset.sum_range_add_sum_Ico (f := fun k : ℕ => expCoeff |x| k) (m := N + 1) (n := 2 * N + 1) hmono)
        -- Rewrite the range sums as `expPartial`.
        have hsum'' :
            expPartial |x| N + (∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), expCoeff |x| k)
              = expPartial |x| (2 * N) := by
          -- `expPartial y N = ∑ k∈range (N+1), ...`
          simpa [expPartial, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul] using hsum'
        -- Solve for the Ico-sum.
        have := _root_.eq_sub_of_add_eq (by simpa [add_comm] using hsum'')
        -- `eq_sub_of_add_eq` gives: `(∑ Ico ...) = expPartial(2N) - expPartial(N)`
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- Nonnegativity of the difference, so `abs` disappears.
      have hnonneg : 0 ≤ expPartial |x| (2 * N) - expPartial |x| N := by
        -- It is a sum of nonnegative coefficients.
        have : 0 ≤ ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), expCoeff |x| k := by
          refine Finset.sum_nonneg ?_
          intro k hk
          -- `expCoeff |x| k = |x|^k / k!` is nonnegative
          dsimp [expCoeff]
          have : 0 ≤ (|x| : ℚ) ^ k := by positivity
          have : 0 ≤ (|x| : ℚ) ^ k / (Nat.factorial k : ℚ) := by
            have hk0 : 0 < (Nat.factorial k : ℚ) := by
              exact_mod_cast (Nat.factorial_pos k)
            exact div_nonneg this (le_of_lt hk0)
          simpa [abs_pow] using this
        -- rewrite the difference as that sum
        simpa [hdecomp] using this
      -- Put the pieces together.
      calc
        (∑ k ∈ Finset.Icc (N + 1) (2 * N), |expCoeff x k|)
            = ∑ k ∈ Finset.Icc (N + 1) (2 * N), expCoeff |x| k := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simp [habsCoeff k]
        _ = ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), expCoeff |x| k := by
                simp [Finset.Ico_add_one_right_eq_Icc]
        _ = |expPartial |x| (2 * N) - expPartial |x| N| := by
                -- use `hdecomp` and `hnonneg`
                simp [hdecomp, abs_of_nonneg hnonneg]
    -- Now apply `hcore`.
    simpa [hsum] using hcore
  exact _root_.le_trans h₁ htail

/-!
## Pre-level halving equivalence

We now convert the halving tail bound into a `Pre.Equiv`, and then into
a `CReal` equality for `expRatSmall`.
-/

/-- Pre-level equivalence: `small_exp x ≈ (small_exp (x/2))^2` (with the canonical shift). -/
theorem small_exp_halve_mul_equiv (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) :
    CReal.Pre.Equiv (small_exp x hx)
      (let y := small_exp (x / 2) (abs_div_two_le_half hx); y.mul y) := by
  intro n
  let y : CReal.Pre := small_exp (x / 2) (abs_div_two_le_half hx)
  let S : ℕ := y.mulShift y
  -- Compare at truncation level `expTruncLevel (n+1)` and align multiplication via the shift.
  have hx_abs : |x| ≤ (1/2 : ℚ) := hx
  -- Tail in `x` from `n+1` to `n+1+S`.
  have htail1 :
      |expPartial x (expTruncLevel (n + 1 + S)) - expPartial x (expTruncLevel (n + 1))|
        ≤ (1 : ℚ) / 2 ^ (n + 1) := by
    have hle : (n + 1) ≤ (n + 1 + S) := Nat.le_add_right _ _
    simpa [expTruncLevel] using (exp_tail_bound_core x hx_abs (n + 1) (n + 1 + S) hle)
  -- Halving mismatch at the shared truncation height `expTruncLevel (n+1+S)`.
  have hhalf :
      |expPartial x (expTruncLevel (n + 1 + S)) -
        (expPartial (x / 2) (expTruncLevel (n + 1 + S))) *
        (expPartial (x / 2) (expTruncLevel (n + 1 + S)))|
        ≤ (1 : ℚ) / 2 ^ (n + 1) := by
    -- Use the bound at `N := expTruncLevel (n+1+S)`, then weaken the exponent.
    have := expPartial_half_sq_bound x hx_abs (expTruncLevel (n + 1 + S))
    -- `expTruncLevel (n+1+S) - 2 = n+1+S`.
    have hweak :
        (1 : ℚ) / 2 ^ (expTruncLevel (n + 1 + S) - 2) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
      simp [expTruncLevel]
      -- `1/2^(n+1+S) ≤ 1/2^(n+1)`
      have : n + 1 ≤ n + 1 + S := Nat.le_add_right _ _
      have hp : (2 : ℚ) ^ (n + 1) ≤ (2 : ℚ) ^ (n + 1 + S) := by
        exact (pow_le_pow_iff_right₀ rfl).mpr this-- pow_le_pow_of_le_left (by nlinarith : (0 : ℚ) ≤ 2) (by norm_num : (1 : ℚ) ≤ 2) this
      have hpos : (0 : ℚ) < (2 : ℚ) ^ (n + 1) := by
        have : (0 : ℚ) < (2 : ℚ) := by norm_num
        exact pow_pos this _
      have := one_div_le_one_div_of_le hpos hp
      simpa using this
    exact _root_.le_trans this hweak
  -- Triangle budget: `≤ 2 * (1/2^(n+1)) = 1/2^n`.
  have hbudget :
      |expPartial x (expTruncLevel (n + 1)) -
        (expPartial (x / 2) (expTruncLevel (n + 1 + S))) *
        (expPartial (x / 2) (expTruncLevel (n + 1 + S)))|
        ≤ (1 : ℚ) / 2 ^ n := by
    have htri :=
      abs_sub_le
        (expPartial x (expTruncLevel (n + 1)))
        (expPartial x (expTruncLevel (n + 1 + S)))
        ((expPartial (x / 2) (expTruncLevel (n + 1 + S))) *
          (expPartial (x / 2) (expTruncLevel (n + 1 + S))))
    have h1' :
        |expPartial x (expTruncLevel (n + 1)) - expPartial x (expTruncLevel (n + 1 + S))|
          ≤ (1 : ℚ) / 2 ^ (n + 1) := by
      simpa [abs_sub_comm] using htail1
    have h2' := hhalf
    calc
      |expPartial x (expTruncLevel (n + 1)) -
        (expPartial (x / 2) (expTruncLevel (n + 1 + S))) *
        (expPartial (x / 2) (expTruncLevel (n + 1 + S)))|
          ≤
        |expPartial x (expTruncLevel (n + 1)) - expPartial x (expTruncLevel (n + 1 + S))|
        + |expPartial x (expTruncLevel (n + 1 + S)) -
          (expPartial (x / 2) (expTruncLevel (n + 1 + S))) *
          (expPartial (x / 2) (expTruncLevel (n + 1 + S)))| := by
            simpa using htri
      _ ≤ (1 : ℚ) / 2 ^ (n + 1) + (1 : ℚ) / 2 ^ (n + 1) := by
            exact add_le_add h1' h2'
      _ = (1 : ℚ) / 2 ^ n := by
            field_simp [pow_succ]; ring
  -- Rewrite in terms of `small_exp` and `mul` approximants.
  -- LHS: `(small_exp x hx).approx (n+1) = expPartial x (expTruncLevel (n+1))`.
  -- RHS: `(y.mul y).approx (n+1) = expPartial (x/2) (expTruncLevel (n+1+S)) ^2`.
  simpa [small_exp, CReal.Pre.mul, y, S, expTruncLevel] using hbudget

/-- Spec-side halving identity in `CReal` for small rationals: `exp(x) = (exp(x/2))^2`. -/
theorem expRatSmall_halve_sq (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) :
    expRatSmall x hx =
      (expRatSmall (x / 2) (abs_div_two_le_half hx)) *
      (expRatSmall (x / 2) (abs_div_two_le_half hx)) := by
  have hy : |x / 2| ≤ (1/2 : ℚ) := abs_div_two_le_half hx
  have hpre :
      CReal.Pre.Equiv (small_exp x hx) (let y := small_exp (x / 2) hy; y.mul y) := by
    simpa [hy] using small_exp_halve_mul_equiv x hx
  have hq :
      (⟦small_exp x hx⟧ : CReal) = ⟦(small_exp (x / 2) hy).mul (small_exp (x / 2) hy)⟧ := by
    simpa using (Quotient.sound hpre)
  -- Convert quotient-of-mul to `CReal` multiplication.
  -- `mul_def : ⟦a⟧ * ⟦b⟧ = ⟦a.mul b⟧`.
  simpa [expRatSmall, hy, mul_def] using hq

/-!
## Cross-`k` independence: short iteration

With the halving lemma, `k`-independence becomes an iteration argument.
-/

namespace ExpKIndep

/-- Scaling a rational by `2^k` in the denominator. -/
@[inline] def scalePow2 (x : ℚ) (k : ℕ) : ℚ := x / (2 : ℚ) ^ k

/-- The range-reduced auxiliary exponential (spec-side) on small rationals:
`expAuxRat x k = (exp(x / 2^k))^(2^k)`. -/
def expAuxRat (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (k : ℕ) : CReal :=
  let y : ℚ := scalePow2 x k
  have hy : |y| ≤ (1/2 : ℚ) := by
    -- `|x| / 2^k ≤ |x| ≤ 1/2`
    have hy' : |y| = |x| / (2 : ℚ) ^ k := by
      -- `simp` doesn't unfold the `let y := ...` unless we expose the definitional equality.
      have hy0 : y = scalePow2 x k := rfl
      simp [hy0, scalePow2, abs_div, abs_pow]
    have hk : (1 : ℚ) ≤ (2 : ℚ) ^ k := by
      -- Avoid lemmas that require a `MulLeftMono ℚ` instance; reduce to the Nat fact `1 ≤ 2^k`.
      have hk_nat : (1 : ℕ) ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by norm_num)
      exact_mod_cast hk_nat
    have hle : |x| / (2 : ℚ) ^ k ≤ |x| := by
      -- `a / d ≤ a` for `a ≥ 0` and `d ≥ 1`
      have hkpos : (0 : ℚ) < (2 : ℚ) ^ k := by
        exact pow_pos (by norm_num : (0 : ℚ) < (2 : ℚ)) k
      refine (div_le_iff₀ hkpos).2 ?_
      -- `|x| ≤ |x| * (2^k)` from `1 ≤ 2^k`
      have := mul_le_mul_of_nonneg_left hk (abs_nonneg x)
      simpa [mul_one] using this
    nlinarith [hy', hle, hx]
  (expRatSmall y hy) ^ ((2 : ℕ) ^ k)

/-- One-step `k`-shift: `expAuxRat x (k+1) = expAuxRat x k`. -/
theorem expAuxRat_succ (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (k : ℕ) :
    expAuxRat x hx (k + 1) = expAuxRat x hx k := by
  -- Let `y = x / 2^k`; then `y/2 = x / 2^(k+1)` and apply the halving lemma.
  set y : ℚ := scalePow2 x k
  have hy : |y| ≤ (1/2 : ℚ) := by
    have hy' : |y| = |x| / (2 : ℚ) ^ k := by
      have hy0 : y = scalePow2 x k := by rfl
      simp [hy0, scalePow2, abs_div, abs_pow]
    have hk : (1 : ℚ) ≤ (2 : ℚ) ^ k := by
      have hk_nat : (1 : ℕ) ≤ (2 : ℕ) ^ k := by
        exact Nat.one_le_two_pow
      exact_mod_cast hk_nat
    have hle : |x| / (2 : ℚ) ^ k ≤ |x| := by
      have hkpos : (0 : ℚ) < (2 : ℚ) ^ k := by
        exact pow_pos (by norm_num : (0 : ℚ) < (2 : ℚ)) k
      refine (div_le_iff₀  hkpos).2 ?_
      have := mul_le_mul_of_nonneg_left hk (abs_nonneg x)
      simpa [mul_one] using this
    nlinarith [hy', hle, hx]
  have hy2 : |y / 2| ≤ (1/2 : ℚ) := abs_div_two_le_half hy
  have hhalve :
      expRatSmall y hy =
        (expRatSmall (y / 2) hy2) * (expRatSmall (y / 2) hy2) :=
    expRatSmall_halve_sq y hy
  -- Now raise both sides to `2^k` and use `2^(k+1) = 2 * 2^k`.
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * ((2 : ℕ) ^ k) := by
    simp [Nat.pow_succ]; exact Eq.symm (Nat.mul_comm 2 (2 ^ k))
  -- Unfold `expAuxRat` and compute.
  simp [expAuxRat, scalePow2, hpow, pow_mul]
  -- `simp` reduces us to a pure power identity; rewrite the rational arguments via `y = x / 2^k`.
  have hyk : x / (2 : ℚ) ^ k = y := by
    simp [y, scalePow2]
  have hyk1 : x / (2 : ℚ) ^ (k + 1) = y / 2 := by
    -- `(x / 2^(k+1)) = (x / 2^k) / 2 = y / 2`
    simp [y, scalePow2, pow_succ, div_div]
  -- Now the goal matches `hhalve` after raising to `2^k`.
  simp [hyk, hyk1]
  have hpoweq := congrArg (fun t : CReal => t ^ ((2 : ℕ) ^ k)) hhalve
  -- Turn `a*a` into `a^2` on the LHS.
  simpa [pow_two] using hpoweq.symm

end ExpKIndep

end CReal
end Computable
