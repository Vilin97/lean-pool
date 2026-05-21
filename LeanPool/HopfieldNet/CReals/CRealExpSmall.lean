/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2

namespace Computable
namespace CReal

open scoped BigOperators

namespace Pre

/-!
# Bounded exponential (`expSmall`) and continuity modulus

This file provides the bounded-exponential layer used by total `exp` via
range-reduction.

Deliverable (this step): a proved continuity modulus (`SmallExpModulus`) for the
rational bounded exponential constructor `Pre.small_exp` defined in `CRealPre.lean`.
-/

/-- A quantitative continuity modulus for `Pre.small_exp` on `[-1/2, 1/2] ⊆ ℚ`. -/
class SmallExpModulus : Prop where
  /--
  If `|x - y| ≤ 2^{-(n+2)}` and both inputs are in `[-1/2,1/2]`,
  then the `n`-th comparison approximants of `small_exp` differ by at most `2^{-(n+1)}`.
  -/
  approx_cauchy :
    ∀ (x y : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (hy : |y| ≤ (1/2 : ℚ)) (n : ℕ),
      |x - y| ≤ (1 : ℚ) / 2 ^ (n + 2) →
        |(small_exp x hx).approx (n + 2) - (small_exp y hy).approx (n + 2)| ≤ (1 : ℚ) / 2 ^ (n + 1)

/-!
## Elementary bounds used for the modulus
-/

/-- Helper: `n ≤ n!` in `ℕ`. -/
lemma le_factorial (n : ℕ) : n ≤ Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfac1 : 1 ≤ Nat.factorial n := Nat.succ_le_of_lt (Nat.factorial_pos n)
      have hmul : n.succ * 1 ≤ n.succ * Nat.factorial n := Nat.mul_le_mul_left _ hfac1
      simpa [Nat.factorial_succ] using hmul

set_option maxHeartbeats 0 in
/--
Power-difference estimate on `[-1/2,1/2]`:

`|x^(k+1) - y^(k+1)| ≤ (k+1) * (1/2)^k * |x - y|`.
-/
lemma abs_pow_succ_sub_pow_succ_le
    (x y : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (hy : |y| ≤ (1/2 : ℚ)) :
    ∀ k : ℕ,
      |x^(k+1) - y^(k+1)| ≤ (k+1 : ℚ) * ((1/2 : ℚ)^k) * |x - y| := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Decompose `x^(k+2) - y^(k+2)` to expose `x - y` and the induction hypothesis.
      have hdecomp :
          x^(k+2) - y^(k+2)
            = x^(k+1) * (x - y) + (x^(k+1) - y^(k+1)) * y := by
        -- expand `pow_succ`, then rearrange (commutative ring)
        simp [pow_succ]
        ring
      have hxpow :
          |x^(k+1)| ≤ (1/2 : ℚ)^(k+1) := by
        have : |x|^(k+1) ≤ (1/2 : ℚ)^(k+1) :=
          pow_le_pow_left₀ (abs_nonneg x) hx (k+1)
        simpa [abs_pow] using this
      have hy_nonneg : 0 ≤ |y| := abs_nonneg y
      have hxy_nonneg : 0 ≤ |x - y| := abs_nonneg (x - y)
      have hA_nonneg :
          0 ≤ (k+1 : ℚ) * (1/2 : ℚ)^k * |x - y| := by
        -- Disambiguate from `Computable.CReal.mul_nonneg`; here we are in `ℚ`.
        exact _root_.mul_nonneg (_root_.mul_nonneg (by positivity) (by positivity)) hxy_nonneg
      calc
        |x^(k+2) - y^(k+2)|
            = |x^(k+1) * (x - y) + (x^(k+1) - y^(k+1)) * y| := by
                simp [hdecomp]
        _ ≤ |x^(k+1) * (x - y)| + |(x^(k+1) - y^(k+1)) * y| := abs_add_le _ _
        _ = |x^(k+1)| * |x - y| + |x^(k+1) - y^(k+1)| * |y| := by
              simp [abs_mul, mul_comm]
        _ ≤ (1/2 : ℚ)^(k+1) * |x - y| +
              ((k+1 : ℚ) * (1/2 : ℚ)^k * |x - y|) * |y| := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_right hxpow hxy_nonneg
              · exact mul_le_mul_of_nonneg_right ih hy_nonneg
        _ ≤ (1/2 : ℚ)^(k+1) * |x - y| +
              ((k+1 : ℚ) * (1/2 : ℚ)^k * |x - y|) * (1/2 : ℚ) := by
              -- `add_le_add_left` in this file's namespace is for `CReal`; use the root lemma for `ℚ`.
              refine Rat.add_le_add_left.mpr ?_
              -- use `|y| ≤ 1/2` and nonnegativity of the other factor
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (mul_le_mul_of_nonneg_left hy hA_nonneg)
        -- Match the induction-goal normal form `↑(k+1)+1`.
        _ = ((k + 1 : ℚ) + 1) * (1/2 : ℚ)^(k+1) * |x - y| := by
              -- simplify `... + (k+1)*...` with common factor `(1/2)^(k+1) * |x-y|`
              -- note `(1/2)^k * (1/2) = (1/2)^(k+1)`
              ring_nf -- [pow_succ, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        _ ≤ (↑(k + 1) + 1) * (1/2 : ℚ)^(k+1) * |x - y| := by
              -- Just a cast-reassociation: `↑(k+1) = ↑k + 1`.
              simp [Nat.cast_add]
      -- no remaining goals

/--
Taylor-coefficient difference bound on `[-1/2,1/2]`:

`|x^(k+1)/(k+1)! - y^(k+1)/(k+1)!| ≤ (1/2)^k * |x - y|`.
-/
lemma abs_expCoeff_succ_sub_le
    (x y : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (hy : |y| ≤ (1/2 : ℚ))
    (k : ℕ) :
    |expCoeff x (k+1) - expCoeff y (k+1)| ≤ (1/2 : ℚ)^k * |x - y| := by
  have hsub :
      expCoeff x (k+1) - expCoeff y (k+1)
        = (x^(k+1) - y^(k+1)) / (Nat.factorial (k+1) : ℚ) := by
    -- `(a/c - b/c) = (a-b)/c`
    simpa [expCoeff] using
      (sub_div (x^(k+1) : ℚ) (y^(k+1) : ℚ) ((Nat.factorial (k+1) : ℚ))).symm
  have hfacpos : 0 < (Nat.factorial (k+1) : ℚ) := by
    exact_mod_cast Nat.factorial_pos (k+1)
  have hfac_ge : (k+1 : ℚ) ≤ (Nat.factorial (k+1) : ℚ) := by
    exact_mod_cast le_factorial (k+1)
  have hratio : (k+1 : ℚ) / (Nat.factorial (k+1) : ℚ) ≤ (1 : ℚ) := by
    exact (div_le_one₀ hfacpos).2 hfac_ge
  have hpow :
      |x^(k+1) - y^(k+1)| ≤ (k+1 : ℚ) * (1/2 : ℚ)^k * |x - y| :=
    abs_pow_succ_sub_pow_succ_le x y hx hy k
  have hnonneg : 0 ≤ (1/2 : ℚ)^k * |x - y| := by
    -- Disambiguate from `Computable.CReal.mul_nonneg`; here we are in `ℚ`.
    exact _root_.mul_nonneg (by positivity) (abs_nonneg _)
  -- take absolute values and divide by `factorial (k+1)`
  calc
    |expCoeff x (k+1) - expCoeff y (k+1)|
        = |(x^(k+1) - y^(k+1)) / (Nat.factorial (k+1) : ℚ)| := by
            simp [hsub]
    _ = |x^(k+1) - y^(k+1)| / (Nat.factorial (k+1) : ℚ) := by
            simp [abs_div, abs_of_pos hfacpos]
    _ ≤ ((k+1 : ℚ) * (1/2 : ℚ)^k * |x - y|) / (Nat.factorial (k+1) : ℚ) := by
            exact div_le_div_of_nonneg_right hpow (le_of_lt hfacpos)
    _ = ((k+1 : ℚ) / (Nat.factorial (k+1) : ℚ)) * ((1/2 : ℚ)^k * |x - y|) := by
            -- rearrange as `(k+1)/fact * ...`
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (1 : ℚ) * ((1/2 : ℚ)^k * |x - y|) := by
            exact mul_le_mul_of_nonneg_right hratio hnonneg
    _ = (1/2 : ℚ)^k * |x - y| := by simp

/--
Lipschitz bound for the Taylor partial sums on `[-1/2,1/2]`:

`|expPartial x N - expPartial y N| ≤ 2 * |x - y|`.
-/
lemma expPartial_lipschitz_two
    (x y : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (hy : |y| ≤ (1/2 : ℚ)) (N : ℕ) :
    |expPartial x N - expPartial y N| ≤ (2 : ℚ) * |x - y| := by
  have hsum :
      expPartial x N - expPartial y N
        = (Finset.range (N+1)).sum (fun k => expCoeff x k - expCoeff y k) := by
    simp [expPartial, Finset.sum_sub_distrib]
  have habs :
      |expPartial x N - expPartial y N|
        ≤ (Finset.range (N+1)).sum (fun k => |expCoeff x k - expCoeff y k|) := by
    -- apply `abs_sum_le_sum_abs` on the range sum representation
    simpa [hsum] using
      (Finset.abs_sum_le_sum_abs (s := Finset.range (N+1))
        (f := fun k => expCoeff x k - expCoeff y k))
  -- split off `k = 0`
  have hsplit :
      (Finset.range (N+1)).sum (fun k => |expCoeff x k - expCoeff y k|)
        = |expCoeff x 0 - expCoeff y 0| +
            (Finset.range N).sum (fun j => |expCoeff x (j+1) - expCoeff y (j+1)|) := by
    -- `sum_range_succ` splits off the *last* term; we need to split off `k = 0`,
    -- so use the primed variant and commute the final `+`.
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_range_succ' (fun k => |expCoeff x k - expCoeff y k|) N)
  have hcoeff0 : |expCoeff x 0 - expCoeff y 0| = 0 := by
    simp [expCoeff]
  -- geometric sum bound
  have hgeom : (Finset.range N).sum (fun j => (1/2 : ℚ)^j) ≤ (2 : ℚ) := by
    have hclosed := geom_closed N
    have hsuble : (2 : ℚ) - 2 * (1/2 : ℚ)^N ≤ (2 : ℚ) := by
      have : 0 ≤ 2 * (1/2 : ℚ)^N := by positivity
      linarith
    calc
      (Finset.range N).sum (fun j => (1/2 : ℚ)^j)
          = 2 - 2 * (1/2 : ℚ)^N := hclosed
      _ ≤ 2 := hsuble
  -- termwise bound after splitting
  have hterm :
      (Finset.range N).sum (fun j => |expCoeff x (j+1) - expCoeff y (j+1)|)
        ≤ (Finset.range N).sum (fun j => (1/2 : ℚ)^j * |x - y|) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have := abs_expCoeff_succ_sub_le x y hx hy j
    -- commute factors to match `(...)^j * |x-y|`
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  -- factor out `|x-y|` from the sum
  have hfactor :
      (Finset.range N).sum (fun j => (1/2 : ℚ)^j * |x - y|)
        = ((Finset.range N).sum (fun j => (1/2 : ℚ)^j)) * |x - y| := by
    -- `∑ (f j * a) = (∑ f j) * a`
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_mul (s := Finset.range N) (f := fun j => (1/2 : ℚ)^j) (a := |x - y|)).symm
  have hnonneg : 0 ≤ |x - y| := abs_nonneg _
  calc
    |expPartial x N - expPartial y N|
        ≤ (Finset.range (N+1)).sum (fun k => |expCoeff x k - expCoeff y k|) := habs
    _ = |expCoeff x 0 - expCoeff y 0| +
          (Finset.range N).sum (fun j => |expCoeff x (j+1) - expCoeff y (j+1)|) := hsplit
    _ ≤ 0 + (Finset.range N).sum (fun j => (1/2 : ℚ)^j * |x - y|) := by
          refine add_le_add ?_ hterm
          simp [hcoeff0]
    _ = ((Finset.range N).sum (fun j => (1/2 : ℚ)^j)) * |x - y| := by
          simp; exact
            Eq.symm (Finset.sum_mul (Finset.range N) (fun i ↦ (2 ^ i)⁻¹) |x - y|)
    _ ≤ (2 : ℚ) * |x - y| := by
          exact mul_le_mul_of_nonneg_right hgeom hnonneg

/-- Algebra: `2 * (1/2^(n+2)) = 1/2^(n+1)` in `ℚ`. -/
lemma two_mul_inv_pow (n : ℕ) :
    (2 : ℚ) * ((1 : ℚ) / 2 ^ (n + 2)) = (1 : ℚ) / 2 ^ (n + 1) := by
  field_simp [pow_succ, pow_add]
  ring

/-- Concrete `SmallExpModulus` instance derived from the Taylor polynomial API. -/
instance : SmallExpModulus where
  approx_cauchy := by
    intro x y hx hy n hxy
    have hLip :
        |expPartial x (expTruncLevel (n+2)) - expPartial y (expTruncLevel (n+2))|
          ≤ (2 : ℚ) * |x - y| :=
      expPartial_lipschitz_two x y hx hy (expTruncLevel (n+2))
    have happrox :
        |(small_exp x hx).approx (n+2) - (small_exp y hy).approx (n+2)|
          ≤ (2 : ℚ) * |x - y| := by
      simpa [small_exp, expTruncLevel] using hLip
    have hmul :
        (2 : ℚ) * |x - y| ≤ (1 : ℚ) / 2 ^ (n + 1) := by
      have h2 : 0 ≤ (2 : ℚ) := by norm_num
      calc (2 : ℚ) * |x - y| ≤ (2 : ℚ) * ((1 : ℚ) / 2 ^ (n + 2)) :=
              mul_le_mul_of_nonneg_left hxy h2
        _ = (1 : ℚ) / 2 ^ (n + 1) := two_mul_inv_pow n
    exact happrox.trans hmul

end Pre

/-!
## Lift `expSmall` to bounded `CReal`
-/

open Pre

/-- A bounded-input package for `expSmall`. -/
structure ExpSmallInput where
  pre : CReal.Pre
  bound : ∀ n, |pre.approx n| ≤ (1/2 : ℚ)

/-- Rational bounded exp as a `CReal`. -/
def expRatSmall (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) : CReal :=
  ⟦Pre.small_exp x hx⟧

/-- The Cauchy sequence used to define `expSmall` on bounded inputs. -/
def expSmallSeq (x : ExpSmallInput) [Pre.SmallExpModulus] : CReal.RCauSeq :=
{ seq := fun n => expRatSmall (x.pre.approx (n + 3)) (x.bound (n + 3))
  pre := fun n => Pre.small_exp (x.pre.approx (n + 3)) (x.bound (n + 3))
  seq_spec := by intro n; rfl
  is_cauchy := by
    intro n m hnm
    have hnm' : n + 5 ≤ m + 5 := Nat.add_le_add_right hnm 5
    have hin_raw :
        |x.pre.approx (n + 5) - x.pre.approx (m + 5)| ≤ (1 : ℚ) / 2 ^ (n + 5) :=
      x.pre.is_regular (n + 5) (m + 5) hnm'
    -- weaken to `2^{-(n+2)}`
    have hmono1 : (1 : ℚ) / 2 ^ (n + 5) ≤ (1 : ℚ) / 2 ^ (n + 4) := by
      simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 4)
    have hmono2 : (1 : ℚ) / 2 ^ (n + 4) ≤ (1 : ℚ) / 2 ^ (n + 3) := by
      simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 3)
    have hmono3 : (1 : ℚ) / 2 ^ (n + 3) ≤ (1 : ℚ) / 2 ^ (n + 2) := by
      simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 2)
    have hin :
        |x.pre.approx (n + 5) - x.pre.approx (m + 5)| ≤ (1 : ℚ) / 2 ^ (n + 2) :=
      hin_raw.trans (hmono1.trans (hmono2.trans hmono3))
    have hout :=
      Pre.SmallExpModulus.approx_cauchy
        (x := x.pre.approx (n + 5)) (y := x.pre.approx (m + 5))
        (hx := x.bound (n + 5)) (hy := x.bound (m + 5)) n hin
    aesop --simpa [expSmallSeq, expRatSmall] using hout
}

/-- Bounded exponential as a `CReal`. -/
def expSmall (x : ExpSmallInput) [Pre.SmallExpModulus] : CReal :=
  CReal.lim (expSmallSeq x)

/-- Congruence: `expSmall` depends only on the denotation of the bounded input. -/
theorem expSmall_congr [Pre.SmallExpModulus]
    {x y : ExpSmallInput} (hxy : CReal.Pre.Equiv x.pre y.pre) :
    expSmall x = expSmall y := by
  change (⟦CReal.lim_pre (expSmallSeq x)⟧ : CReal) = ⟦CReal.lim_pre (expSmallSeq y)⟧
  apply Quotient.sound
  intro n
  -- use the modulus at parameter `n+1` (comparison index `n+3`)
  have hin_raw :
      |x.pre.approx (n + 6) - y.pre.approx (n + 6)| ≤ (1 : ℚ) / 2 ^ (n + 5) := by
    simpa [Nat.add_assoc] using hxy (n + 5)
  have hmono1 : (1 : ℚ) / 2 ^ (n + 5) ≤ (1 : ℚ) / 2 ^ (n + 4) := by
    simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 4)
  have hmono2 : (1 : ℚ) / 2 ^ (n + 4) ≤ (1 : ℚ) / 2 ^ (n + 3) := by
    simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 3)
  have hin :
      |x.pre.approx (n + 6) - y.pre.approx (n + 6)| ≤ (1 : ℚ) / 2 ^ ((n + 1) + 2) :=
    hin_raw.trans (hmono1.trans hmono2)
  have hout :=
    Pre.SmallExpModulus.approx_cauchy
      (x := x.pre.approx (n + 6)) (y := y.pre.approx (n + 6))
      (hx := x.bound (n + 6)) (hy := y.bound (n + 6)) (n := n + 1) hin
  -- weaken `2^{-(n+2)}` to `2^{-n}` for `Pre.Equiv`
  have hmono3 : (1 : ℚ) / 2 ^ (n + 2) ≤ (1 : ℚ) / 2 ^ (n + 1) := by
    simpa [Nat.add_assoc] using inv_pow_antitone_succ (n + 1)
  have hmono4 : (1 : ℚ) / 2 ^ (n + 1) ≤ (1 : ℚ) / 2 ^ n := by
    simpa [Nat.add_assoc] using inv_pow_antitone_succ n
  have hout' :
      |(Pre.small_exp (x.pre.approx (n + 6)) (x.bound (n + 6))).approx (n + 3) -
        (Pre.small_exp (y.pre.approx (n + 6)) (y.bound (n + 6))).approx (n + 3)| ≤ (1 : ℚ) / 2 ^ n :=
    hout.trans (hmono3.trans hmono4)
  simpa [CReal.lim_pre, expSmallSeq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hout'

end CReal
end Computable
