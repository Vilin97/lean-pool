/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2
import Mathlib.Algebra.Order.Field.GeomSum

namespace Computable
namespace CReal

open scoped BigOperators

namespace Pre

/-!
## `log(1+x)` for small rationals

For `|x| ≤ 1/2` we define `log(1+x)` by the alternating power series

`log(1+x) = ∑_{i=1}^∞ (-1)^(i+1) * x^i / i`.

We package the partial sums into a `CReal.Pre` using a dyadic modulus.
-/

/-- Coefficient for `log(1+x)` series (with the `i = 0` term set to `0`). -/
def log1pCoeff (x : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then 0 else ((-1 : ℚ) ^ (i + 1)) * x ^ i / i

/-- Partial sum `∑_{i=0..N} log1pCoeff x i`. -/
def log1pPartial (x : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (N + 1), log1pCoeff x i

/-- Truncation level for the dyadic modulus (constant slack `+2`). -/
@[inline] def logTruncLevel (n : ℕ) : ℕ := n + 2

lemma abs_log1pCoeff_le (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) :
    ∀ i, 1 ≤ i → |log1pCoeff x i| ≤ (1/2 : ℚ) ^ i := by
  intro i hi
  have hi0 : i ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hi)
  have hiQ : (1 : ℚ) ≤ (i : ℚ) := by
    exact_mod_cast hi
  -- unfold and drop the sign and the `/ i` factor
  have h1 :
      |log1pCoeff x i| = |x| ^ i / (i : ℚ) := by
    have : (log1pCoeff x i) = ((-1 : ℚ) ^ (i + 1)) * x ^ i / i := by
      simp [log1pCoeff, hi0]
    -- `|(-1)^(i+1)| = 1`
    simp [this, abs_mul, abs_div, abs_pow]
  have hdiv : |x| ^ i / (i : ℚ) ≤ |x| ^ i := by
    exact div_le_self (pow_nonneg (abs_nonneg x) i) hiQ
  have hpow : |x| ^ i ≤ (1/2 : ℚ) ^ i := by
    simpa [abs_pow] using (pow_le_pow_left₀ (abs_nonneg x) hx i)
  exact _root_.le_trans (by simpa [h1] using hdiv) hpow

/--
Small-input `log(1+x)` as a pre-real: uses partial sums at level `logTruncLevel n`.
-/
def small_log1p (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal.Pre where
  approx := fun n => log1pPartial x (logTruncLevel n)
  is_regular := by
    intro n m hnm
    -- abbreviate truncation bounds
    set Nn : ℕ := logTruncLevel n
    set Nm : ℕ := logTruncLevel m
    have hN : Nn + 1 ≤ Nm + 1 := by
      dsimp [Nn, Nm, logTruncLevel]
      exact Nat.add_le_add_right hnm 2 |> Nat.succ_le_succ
    -- rewrite the difference as an `Ico` tail sum
    have hsub :
        (∑ i ∈ Finset.range (Nm + 1), log1pCoeff x i) -
          (∑ i ∈ Finset.range (Nn + 1), log1pCoeff x i)
          =
        ∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), log1pCoeff x i := by
      -- `sum_Ico_eq_sub` is stated as `∑_{Ico} = ∑ range - ∑ range`
      simpa using (Finset.sum_Ico_eq_sub (f := fun i => log1pCoeff x i) hN).symm
    have habs :
        |(∑ i ∈ Finset.range (Nn + 1), log1pCoeff x i) -
            (∑ i ∈ Finset.range (Nm + 1), log1pCoeff x i)|
          =
        |∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), log1pCoeff x i| := by
      -- swap and use the `Ico`-tail identity
      rw [abs_sub_comm]
      -- now `|sum_range(Nm+1) - sum_range(Nn+1)|`
      simp [hsub]
    -- bound by the sum of absolute values, then compare to a geometric tail
    have hterm :
        ∀ i ∈ Finset.Ico (Nn + 1) (Nm + 1), |log1pCoeff x i| ≤ (1/2 : ℚ) ^ i := by
      intro i hiI
      have hi' : 1 ≤ i := by
        -- `i ∈ Ico (Nn+1) ...` implies `Nn+1 ≤ i`, and `Nn = n+2 ≥ 2`
        have hNi : Nn + 1 ≤ i := (Finset.mem_Ico.mp hiI).1
        have : 1 ≤ Nn + 1 := by
          dsimp [Nn, logTruncLevel]
          omega
        exact _root_.le_trans this hNi
      exact abs_log1pCoeff_le x hx i hi'
    have hgeom :
        (∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), (1/2 : ℚ) ^ i)
          ≤ (1/2 : ℚ) ^ (Nn + 1) / (1 - (1/2 : ℚ)) := by
      -- this is a standard bound on geometric tails in an ordered field
      have hx0 : (0 : ℚ) ≤ (1/2 : ℚ) := by norm_num
      have hx1 : (1/2 : ℚ) < 1 := by norm_num
      convert geom_sum_Ico_le_of_lt_one (K := ℚ) (m := Nn + 1) (n := Nm + 1) hx0 hx1 using 2
    have hgeom' :
        (∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), (1/2 : ℚ) ^ i) ≤ (1/2 : ℚ) ^ n := by
      -- simplify the closed form: dividing by `1-1/2 = 1/2` multiplies by `2`
      have : (1/2 : ℚ) ^ (Nn + 1) / (1 - (1/2 : ℚ)) = (1/2 : ℚ) ^ Nn := by
        have hden : (1 - (1/2 : ℚ)) = (1/2 : ℚ) := by norm_num
        rw [hden]
        -- `(1/2)^(Nn+1) / (1/2) = (1/2)^Nn`
        simp [pow_succ, div_eq_mul_inv]
      -- `Nn = n+2` so `(1/2)^Nn ≤ (1/2)^n`
      have hmono : (1/2 : ℚ) ^ Nn ≤ (1/2 : ℚ) ^ n := by
        -- `0 ≤ 1/2 < 1` so powers are antitone
        have hx0 : (0 : ℚ) ≤ (1/2 : ℚ) := by norm_num
        have hx1 : (1/2 : ℚ) ≤ 1 := by norm_num
        -- use `pow_le_pow_of_le_left` with `x ≤ 1` in reverse direction via exponent order
        -- since `0 ≤ x ≤ 1`, `x^(n+2) ≤ x^n`.
        have hn : n ≤ Nn := by dsimp [Nn, logTruncLevel]; omega
        -- `pow_le_pow_of_le_left` is monotone in exponent when base ≥ 1; here base ≤ 1,
        -- so use `pow_le_pow_of_le_one` (antitone).
        exact pow_le_pow_of_le_one hx0 hx1 hn
      calc
        (∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), (1/2 : ℚ) ^ i)
          ≤ (1/2 : ℚ) ^ (Nn + 1) / (1 - (1/2 : ℚ)) := hgeom
        _ = (1/2 : ℚ) ^ Nn := this
        _ ≤ (1/2 : ℚ) ^ n := hmono
    -- final assembly
    calc
      |(∑ i ∈ Finset.range (Nn + 1), log1pCoeff x i) -
          (∑ i ∈ Finset.range (Nm + 1), log1pCoeff x i)|
          = |∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), log1pCoeff x i| := habs
      _ ≤ ∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), |log1pCoeff x i| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := Finset.Ico (Nn + 1) (Nm + 1))
              (f := fun i => log1pCoeff x i))
      _ ≤ ∑ i ∈ Finset.Ico (Nn + 1) (Nm + 1), (1/2 : ℚ) ^ i := by
            refine Finset.sum_le_sum ?_
            intro i hiI
            exact hterm i hiI
      _ ≤ (1/2 : ℚ) ^ n := hgeom'
      _ = (1 : ℚ) / (2 ^ n) := by
            -- ` (1/2)^n = 1/2^n `
            simp [div_eq_mul_inv]

end Pre

/-! ### `CReal` wrapper -/

/-- `log(1+x)` on rationals for `|x| ≤ 1/2`. -/
def log1pRatSmall (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal :=
  ⟦Pre.small_log1p x hx⟧

end CReal
end Computable
