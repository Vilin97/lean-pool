/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealPre2
import Mathlib.Data.Real.Basic

namespace Computable
namespace CReal

open CauSeq
open CauSeq.Completion

-- `abs` is already taken by `Computable.CReal.abs`; use the rational absolute value explicitly.
local notation "absℚ" => (_root_.abs : ℚ → ℚ)

namespace Pre

/-- View a regular pre-real as a Mathlib Cauchy sequence of rationals. -/
def toCauSeq (x : CReal.Pre) : CauSeq ℚ absℚ :=
  ⟨x.approx, by
    intro ε hε
    -- pick `N` with `1/2^N < ε`
    have hpos : 0 < (1 : ℚ) / ε := one_div_pos.mpr hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℚ) / ε < (2 : ℚ) ^ N := exists_pow_gt (x := (1 : ℚ) / ε) hpos
    have hpowpos : 0 < (2 : ℚ) ^ N := pow_pos (by norm_num) N
    have hN' : (1 : ℚ) / (2 : ℚ) ^ N < ε := (one_div_lt hpowpos hε).mpr hN
    refine ⟨N, ?_⟩
    intro j hj
    -- unfold `absℚ` (definally `|·|`) for the goal
    change |x.approx j - x.approx N| < ε
    have hreg : |x.approx j - x.approx N| ≤ (1 : ℚ) / (2 ^ N) := by
      -- regularity gives a bound on `|x_N - x_j|`
      have := x.is_regular N j hj
      simpa [abs_sub_comm, div_eq_mul_inv] using this
    exact lt_of_le_of_lt hreg (by simpa [div_eq_mul_inv] using hN')⟩

/-- Embed a regular pre-real into Mathlib's `ℝ` via the Cauchy completion. -/
def toReal (x : CReal.Pre) : ℝ :=
  ⟨CauSeq.Completion.mk (abv := absℚ) (toCauSeq x)⟩

theorem toReal_zero : toReal (CReal.Pre.zero) = 0 := by
  apply Real.ext_cauchy
  -- compare in the Cauchy completion
  rw [Real.cauchy_zero]
  change (CauSeq.Completion.mk (abv := absℚ) (toCauSeq CReal.Pre.zero)) = 0
  have : toCauSeq (CReal.Pre.zero) = (0 : CauSeq ℚ absℚ) := by
    ext n
    rfl
  rw [this]
  rfl

theorem toReal_one : toReal (CReal.Pre.one) = 1 := by
  apply Real.ext_cauchy
  rw [Real.cauchy_one]
  change (CauSeq.Completion.mk (abv := absℚ) (toCauSeq CReal.Pre.one)) = 1
  have : toCauSeq (CReal.Pre.one) = (1 : CauSeq ℚ absℚ) := by
    ext n
    rfl
  rw [this]
  rfl

theorem toReal_congr {x y : CReal.Pre} (hxy : CReal.Pre.Equiv x y) : toReal x = toReal y := by
  -- reduce to equality of the underlying Cauchy completion elements
  apply Real.ext_cauchy
  -- show the Cauchy sequences are equivalent, i.e. their difference tends to 0
  change (CauSeq.Completion.mk (abv := absℚ) (toCauSeq x)) =
    (CauSeq.Completion.mk (abv := absℚ) (toCauSeq y))
  apply (CauSeq.Completion.mk_eq (abv := absℚ)).2
  -- `LimZero (toCauSeq x - toCauSeq y)`
  intro ε hε
  have hpos : 0 < (1 : ℚ) / ε := one_div_pos.mpr hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℚ) / ε < (2 : ℚ) ^ N := exists_pow_gt (x := (1 : ℚ) / ε) hpos
  have hpowpos : 0 < (2 : ℚ) ^ N := pow_pos (by norm_num) N
  have hN' : (1 : ℚ) / (2 : ℚ) ^ N < ε := (one_div_lt hpowpos hε).mpr hN
  refine ⟨N + 1, ?_⟩
  intro j hj
  change |(((toCauSeq x - toCauSeq y) : CauSeq ℚ absℚ) j)| < ε
  have hj1 : 1 ≤ j := by
    have : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    exact _root_.le_trans this hj
  have hj' : (j - 1) + 1 = j := Nat.sub_add_cancel hj1
  have hxy_j : |x.approx j - y.approx j| ≤ (1 : ℚ) / 2 ^ (j - 1) := by
    -- specialize the ≈-bound at index `j-1`, and rewrite `(j-1)+1 = j`
    simpa [hj'] using hxy (j - 1)
  have hNj : N ≤ j - 1 := Nat.le_sub_of_add_le hj
  have hpow : (2 : ℚ) ^ N ≤ (2 : ℚ) ^ (j - 1) :=
    pow_le_pow_right₀ (a := (2 : ℚ)) (by norm_num) hNj
  have hdiv : (1 : ℚ) / (2 : ℚ) ^ (j - 1) ≤ (1 : ℚ) / (2 : ℚ) ^ N := by
    -- larger denominator gives smaller reciprocal
    simpa [one_div, div_eq_mul_inv] using (one_div_le_one_div_of_le (pow_pos (by norm_num) N) hpow)
  have hle : |x.approx j - y.approx j| ≤ (1 : ℚ) / (2 : ℚ) ^ N :=
    _root_.le_trans (by
      -- rewrite `(1/2)^(j-1)` as `1/(2^(j-1))`
      simpa [div_eq_mul_inv] using hxy_j) hdiv
  have : |(((toCauSeq x - toCauSeq y) : CauSeq ℚ absℚ) j)| ≤ (1 : ℚ) / (2 : ℚ) ^ N := by
    -- pointwise: `(toCauSeq x - toCauSeq y) j = x_j - y_j`
    simpa [toCauSeq] using hle
  exact lt_of_le_of_lt this (by simpa [div_eq_mul_inv] using hN')

/-
Compatibility of our shifted operations with Mathlib's pointwise operations
in the Cauchy completion (proved via `CauSeq` equivalence).
-/

theorem toReal_add (x y : CReal.Pre) : toReal (CReal.Pre.add x y) = toReal x + toReal y := by
  -- rewrite everything through `Real.mk`
  -- (definally) `toReal z = Real.mk (toCauSeq z)`
  -- so it suffices to show the Cauchy sequences are equivalent.
  -- `mk` respects addition on `CauSeq`.
  have hx : toReal x = Real.mk (toCauSeq x) := rfl
  have hy : toReal y = Real.mk (toCauSeq y) := rfl
  have hxy' : toReal (CReal.Pre.add x y) = Real.mk (toCauSeq (CReal.Pre.add x y)) := rfl
  -- move to a `Real.mk` equality
  rw [hx, hy, hxy']
  -- rewrite `mk f + mk g` as `mk (f+g)`
  rw [← Real.mk_add]
  -- now use `Real.mk_eq`
  apply (Real.mk_eq).2
  -- show `LimZero` of the difference sequence
  intro ε hε
  obtain ⟨K, hK⟩ := find_index_for_bound (B := (2 : ℚ)) (ε := ε) (by norm_num) hε
  refine ⟨K, ?_⟩
  intro n hn
  -- goal: `|((x_{n+1}+y_{n+1}) - (x_n+y_n))| < ε`
  change
    |(x.approx (n + 1) + y.approx (n + 1)) - (x.approx n + y.approx n)| < ε
  have hx_step : |x.approx (n + 1) - x.approx n| ≤ (1 : ℚ) / 2 ^ n := by
    -- from regularity at indices `n ≤ n+1`
    have := x.is_regular n (n + 1) (Nat.le_succ n)
    simpa [abs_sub_comm] using this
  have hy_step : |y.approx (n + 1) - y.approx n| ≤ (1 : ℚ) / 2 ^ n := by
    have := y.is_regular n (n + 1) (Nat.le_succ n)
    simpa [abs_sub_comm] using this
  have hdiff :
      |(x.approx (n + 1) + y.approx (n + 1)) - (x.approx n + y.approx n)|
        ≤ (2 : ℚ) / 2 ^ n := by
    -- `= (x_{n+1}-x_n) + (y_{n+1}-y_n)` and bound by triangle inequality
    calc
      |(x.approx (n + 1) + y.approx (n + 1)) - (x.approx n + y.approx n)|
          = |(x.approx (n + 1) - x.approx n) + (y.approx (n + 1) - y.approx n)| := by ring_nf
      _ ≤ |x.approx (n + 1) - x.approx n| + |y.approx (n + 1) - y.approx n| :=
          abs_add_le _ _
      _ ≤ (1 : ℚ) / 2 ^ n + (1 : ℚ) / 2 ^ n := by gcongr
      _ = (2 : ℚ) / 2 ^ n := by ring
  -- compare `2/2^n ≤ 2/2^K` for `K ≤ n`
  have hmono : (2 : ℚ) / 2 ^ n ≤ (2 : ℚ) / 2 ^ K := by
    have hpow : (2 : ℚ) ^ K ≤ (2 : ℚ) ^ n :=
      pow_le_pow_right₀ (a := (2 : ℚ)) (by norm_num) hn
    have hpos : (0 : ℚ) < (2 : ℚ) ^ K := pow_pos (by norm_num) K
    have hrecip : (1 : ℚ) / (2 : ℚ) ^ n ≤ (1 : ℚ) / (2 : ℚ) ^ K := by
      simpa [one_div, div_eq_mul_inv] using (one_div_le_one_div_of_le hpos hpow)
    -- multiply by 2≥0
    have h2 : (0 : ℚ) ≤ (2 : ℚ) := by norm_num
    -- `2 / 2^n = 2 * (1/2^n)`
    simpa [div_eq_mul_inv, mul_assoc] using (mul_le_mul_of_nonneg_left hrecip h2)
  exact lt_of_le_of_lt (hdiff.trans hmono) hK

theorem toReal_neg (x : CReal.Pre) : toReal (CReal.Pre.neg x) = -toReal x := by
  -- reduce to an equality of `Real.mk` terms
  have hx : toReal x = Real.mk (toCauSeq x) := rfl
  have hnx : toReal (CReal.Pre.neg x) = Real.mk (toCauSeq (CReal.Pre.neg x)) := rfl
  rw [hx, hnx]
  -- `-mk f = mk (-f)`
  rw [← Real.mk_neg]
  -- and the underlying Cauchy sequences coincide pointwise
  have hseq : toCauSeq (CReal.Pre.neg x) = -toCauSeq x := by
    ext n
    rfl
  simp [hseq]

theorem toReal_mul (x y : CReal.Pre) : toReal (CReal.Pre.mul x y) = toReal x * toReal y := by
  have hx : toReal x = Real.mk (toCauSeq x) := rfl
  have hy : toReal y = Real.mk (toCauSeq y) := rfl
  have hxy' : toReal (CReal.Pre.mul x y) = Real.mk (toCauSeq (CReal.Pre.mul x y)) := rfl
  rw [hx, hy, hxy']
  -- rewrite `mk f * mk g` as `mk (f*g)`
  rw [← Real.mk_mul]
  apply (Real.mk_eq).2
  -- show `LimZero` of the difference between shifted- and pointwise-products
  intro ε hε
  let S : ℕ := CReal.Pre.mulShift x y
  let B : ℚ := (x.cBound + y.cBound : ℚ)
  have hxpos : (0 : ℚ) < (x.cBound : ℚ) := by
    exact_mod_cast (CReal.Pre.cBound_pos x)
  have hypos : (0 : ℚ) < (y.cBound : ℚ) := by
    exact_mod_cast (CReal.Pre.cBound_pos y)
  have hBpos : 0 < B := by
    dsimp [B]
    linarith
  obtain ⟨K, hK⟩ := find_index_for_bound (B := B) (ε := ε) hBpos hε
  refine ⟨K, ?_⟩
  intro n hn
  -- goal: `|x_{n+S}*y_{n+S} - x_n*y_n| < ε`
  change
    |(x.approx (n + S) * y.approx (n + S)) - (x.approx n * y.approx n)| < ε
  have hx_bound : |x.approx (n + S)| ≤ (x.cBound : ℚ) :=
    CReal.Pre.abs_approx_le_cBound x (n + S)
  have hy_bound : |y.approx n| ≤ (y.cBound : ℚ) :=
    CReal.Pre.abs_approx_le_cBound y n
  have hx_diff : |x.approx (n + S) - x.approx n| ≤ (1 : ℚ) / 2 ^ n := by
    have := x.is_regular n (n + S) (Nat.le_add_right n S)
    simpa [abs_sub_comm] using this
  have hy_diff : |y.approx (n + S) - y.approx n| ≤ (1 : ℚ) / 2 ^ n := by
    have := y.is_regular n (n + S) (Nat.le_add_right n S)
    simpa [abs_sub_comm] using this
  have hx_nonneg : (0 : ℚ) ≤ (x.cBound : ℚ) := by exact_mod_cast (Nat.zero_le x.cBound)
  have hy_nonneg : (0 : ℚ) ≤ (y.cBound : ℚ) := by exact_mod_cast (Nat.zero_le y.cBound)
  have hdiff :
      |(x.approx (n + S) * y.approx (n + S)) - (x.approx n * y.approx n)|
        ≤ B / 2 ^ n := by
    -- `xS*yS - x*y = xS*(yS-y) + y*(xS-x)`
    have hx1 :
        |x.approx (n + S)| * |y.approx (n + S) - y.approx n|
          ≤ (x.cBound : ℚ) * ((1 : ℚ) / 2 ^ n) := by
      exact mul_le_mul hx_bound hy_diff (abs_nonneg _) hx_nonneg
    have hy1 :
        |y.approx n| * |x.approx (n + S) - x.approx n|
          ≤ (y.cBound : ℚ) * ((1 : ℚ) / 2 ^ n) := by
      exact mul_le_mul hy_bound hx_diff (abs_nonneg _) hy_nonneg
    calc
      |(x.approx (n + S) * y.approx (n + S)) - (x.approx n * y.approx n)|
          = |x.approx (n + S) * (y.approx (n + S) - y.approx n) +
              y.approx n * (x.approx (n + S) - x.approx n)| := by ring_nf
      _ ≤ |x.approx (n + S) * (y.approx (n + S) - y.approx n)| +
            |y.approx n * (x.approx (n + S) - x.approx n)| := abs_add_le _ _
      _ = |x.approx (n + S)| * |y.approx (n + S) - y.approx n| +
            |y.approx n| * |x.approx (n + S) - x.approx n| := by simp [abs_mul]
      _ ≤ (x.cBound : ℚ) * ((1 : ℚ) / 2 ^ n) + (y.cBound : ℚ) * ((1 : ℚ) / 2 ^ n) := by
            exact add_le_add hx1 hy1
      _ = B / 2 ^ n := by
            dsimp [B]
            ring
  have hmono : B / 2 ^ n ≤ B / 2 ^ K := by
    have hpow : (2 : ℚ) ^ K ≤ (2 : ℚ) ^ n :=
      pow_le_pow_right₀ (a := (2 : ℚ)) (by norm_num) hn
    have hpos : (0 : ℚ) < (2 : ℚ) ^ K := pow_pos (by norm_num) K
    have hrecip : (1 : ℚ) / (2 : ℚ) ^ n ≤ (1 : ℚ) / (2 : ℚ) ^ K := by
      simpa [one_div, div_eq_mul_inv] using (one_div_le_one_div_of_le hpos hpow)
    have hBnonneg : (0 : ℚ) ≤ B := le_of_lt hBpos
    simpa [div_eq_mul_inv, mul_assoc] using (mul_le_mul_of_nonneg_left hrecip hBnonneg)
  exact lt_of_le_of_lt (hdiff.trans hmono) hK

end Pre

/-! ### Bridge on quotients -/

/-- Interpret a computable real as a Mathlib real. -/
def toReal : CReal → ℝ :=
  Quotient.lift (fun x : CReal.Pre => Pre.toReal x) (by
    intro a b hab
    exact Pre.toReal_congr (x := a) (y := b) hab)

@[simp] theorem toReal_mk (x : CReal.Pre) : toReal (⟦x⟧ : CReal) = Pre.toReal x := rfl

@[simp] theorem toReal_zero : toReal (0 : CReal) = (0 : ℝ) := by
  -- `0 : CReal` is `⟦Pre.zero⟧`
  change toReal (⟦CReal.Pre.zero⟧ : CReal) = (0 : ℝ)
  simp [Pre.toReal_zero]

@[simp] theorem toReal_one : toReal (1 : CReal) = (1 : ℝ) := by
  change toReal (⟦CReal.Pre.one⟧ : CReal) = (1 : ℝ)
  simp [Pre.toReal_one]

theorem toReal_add (x y : CReal) : toReal (x + y) = toReal x + toReal y := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  -- reduce to the pre-level lemma
  simpa using (Pre.toReal_add a b)

theorem toReal_neg (x : CReal) : toReal (-x) = -toReal x := by
  refine Quotient.inductionOn x (fun a => ?_)
  simpa using (Pre.toReal_neg a)

theorem toReal_mul (x y : CReal) : toReal (x * y) = toReal x * toReal y := by
  refine Quotient.inductionOn₂ x y (fun a b => ?_)
  simpa using (Pre.toReal_mul a b)

/-- `toReal` as a bundled ring homomorphism. -/
def toRealRingHom : CReal →+* ℝ where
  toFun := toReal
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intro x y; simpa using toReal_add x y
  map_mul' := by intro x y; simpa using toReal_mul x y

/-! ### Noncomputable inverse `ℝ → CReal` (for theorem transfer) -/

open Classical

namespace FromReal

open CauSeq
open CauSeq.Completion

/-- A (noncomputable) modulus index for a Cauchy sequence at precision `2^{-n}`. -/
noncomputable def idx (f : CauSeq ℚ absℚ) (n : ℕ) : ℕ :=
  Nat.find (f.cauchy₂ (ε := (1 : ℚ) / (2 ^ n)) (by
    have hpow : (0 : ℚ) < (2 : ℚ) ^ n := pow_pos (by norm_num) n
    exact one_div_pos.mpr hpow))

theorem idx_spec (f : CauSeq ℚ absℚ) (n : ℕ) :
    ∀ j ≥ idx f n, ∀ k ≥ idx f n, |f j - f k| < (1 : ℚ) / (2 ^ n) := by
  simpa [idx] using (Nat.find_spec (f.cauchy₂ (ε := (1 : ℚ) / (2 ^ n)) (by
    have hpow : (0 : ℚ) < (2 : ℚ) ^ n := pow_pos (by norm_num) n
    exact one_div_pos.mpr hpow)))

/-- Monotone index sequence built from `idx` (so later approximants are taken further in the tail). -/
noncomputable def idxMono (f : CauSeq ℚ absℚ) : ℕ → ℕ
  | 0 => idx f 0
  | n + 1 => max (idxMono f n) (idx f (n + 1))

theorem idxMono_le_succ (f : CauSeq ℚ absℚ) (n : ℕ) : idxMono f n ≤ idxMono f (n + 1) := by
  simp [idxMono]

theorem idx_le_idxMono (f : CauSeq ℚ absℚ) : ∀ n, idx f n ≤ idxMono f n := by
  intro n
  cases n with
  | zero =>
      simp [idxMono]
  | succ n =>
      simp [idxMono]

theorem idxMono_mono (f : CauSeq ℚ absℚ) : Monotone (idxMono f) := by
  intro a b hab
  induction hab with
  | refl =>
      exact le_rfl
  | step hab ih =>
      exact _root_.le_trans ih (idxMono_le_succ f _)

/--
Regularize a Mathlib Cauchy sequence into a `CReal.Pre` (noncomputably).

This is the standard “regular subsequence” construction.
-/
noncomputable def preOfCauSeq (f : CauSeq ℚ absℚ) : CReal.Pre where
  -- extra slack `+2` (helps in well-definedness under `CauSeq` equivalence)
  approx := fun n => f (idxMono f (n + 2))
  is_regular := by
    intro n m hnm
    -- work at precision `n+2`
    have hnm' : n + 2 ≤ m + 2 := Nat.add_le_add_right hnm 2
    have hn_le : idx f (n + 2) ≤ idxMono f (n + 2) := idx_le_idxMono f (n + 2)
    have hm_le : idx f (n + 2) ≤ idxMono f (m + 2) := by
      have : idxMono f (n + 2) ≤ idxMono f (m + 2) := idxMono_mono f hnm'
      exact _root_.le_trans hn_le this
    have hlt :=
      idx_spec f (n + 2) (idxMono f (n + 2)) hn_le (idxMono f (m + 2)) hm_le
    have hle : |f (idxMono f (n + 2)) - f (idxMono f (m + 2))| ≤ (1 : ℚ) / (2 ^ (n + 2)) :=
      le_of_lt (by simpa [abs_sub_comm] using hlt)
    have hmono : (1 : ℚ) / (2 ^ (n + 2)) ≤ (1 : ℚ) / (2 ^ n) := by
      have hpow : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ (n + 2) :=
        pow_le_pow_right₀ (a := (2 : ℚ)) (by norm_num) (Nat.le_add_right n 2)
      have hpos : (0 : ℚ) < (2 : ℚ) ^ n := pow_pos (by norm_num) n
      have h := one_div_le_one_div_of_le hpos hpow
      simpa [pow_add, pow_two, one_div] using h
    exact _root_.le_trans hle hmono

/-- Map an element of the Cauchy completion into `CReal` by regularization. -/
noncomputable def ofCauchy : CauSeq.Completion.Cauchy (_root_.abs : ℚ → ℚ) → CReal :=
  Quotient.lift (fun f : CauSeq ℚ absℚ => (⟦preOfCauSeq f⟧ : CReal)) (by
    intro f g hfg
    apply Quotient.sound
    intro n
    -- use the `LimZero` witness at precision `2^{-(n+3)}`
    have hlim : LimZero (f - g) := hfg
    have hpos : (0 : ℚ) < (1 : ℚ) / (2 ^ (n + 3)) := by
      have hpow : (0 : ℚ) < (2 : ℚ) ^ (n + 3) := pow_pos (by norm_num) _
      exact one_div_pos.mpr hpow
    obtain ⟨N, hN⟩ := hlim ((1 : ℚ) / (2 ^ (n + 3))) hpos
    -- synchronize at a common large index `T`
    let i : ℕ := idxMono f (n + 3)
    let j : ℕ := idxMono g (n + 3)
    let T : ℕ := max i (max j N)
    have hiT : i ≤ T := le_max_left _ _
    have hjT : j ≤ T := by
      exact _root_.le_trans (le_max_left _ _) (le_max_right _ _)
    have hNT : N ≤ T := by
      exact _root_.le_trans (le_max_right _ _) (le_max_right _ _)
    -- tails of `f` and `g` are Cauchy at scale `2^{-(n+3)}`
    have hfi : idx f (n + 3) ≤ i := idx_le_idxMono f (n + 3)
    have hfj : idx g (n + 3) ≤ j := idx_le_idxMono g (n + 3)
    have hfT : idx f (n + 3) ≤ T := _root_.le_trans hfi hiT
    have hgT : idx g (n + 3) ≤ T := _root_.le_trans hfj hjT
    have hf_tail : |f i - f T| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
      exact le_of_lt (idx_spec f (n + 3) i hfi T hfT)
    have hg_tail : |g T - g j| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
      exact le_of_lt (by
        -- `idx_spec` gives `|g T - g j| < ...` once both indices are beyond the modulus
        have := idx_spec g (n + 3) T hgT j hfj
        simpa [abs_sub_comm] using this)
    have hfgT : |f T - g T| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
      -- apply `LimZero` at `T ≥ N`
      have := hN T hNT
      -- `(f - g) T = f T - g T`
      simpa [CauSeq.sub_apply] using le_of_lt this
    -- now bound the difference of the regularized approximants at index `n+1`
    have habs :
        |(preOfCauSeq f).approx (n + 1) - (preOfCauSeq g).approx (n + 1)|
          ≤ |f i - f T| + |f T - g T| + |g T - g j| := by
      -- unfold the approximants at index `n+1` (since `preOfCauSeq` uses slack `+2`)
      have : (preOfCauSeq f).approx (n + 1) = f i := by
        simp [preOfCauSeq, i, idxMono, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have : (preOfCauSeq g).approx (n + 1) = g j := by
        simp [preOfCauSeq, j, idxMono, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      -- triangle inequality on three terms
      -- `f i - g j = (f i - f T) + (f T - g T) + (g T - g j)`
      have hsplit : f i - g j = (f i - f T) + (f T - g T) + (g T - g j) := by ring
      -- apply `abs_add_le` twice
      calc
        |f i - g j|
            = |(f i - f T) + (f T - g T) + (g T - g j)| := by
                simp
        _ = |((f i - f T) + (f T - g T)) + (g T - g j)| := by ring_nf
        _ ≤ |(f i - f T) + (f T - g T)| + |g T - g j| := abs_add_le _ _
        _ ≤ (|f i - f T| + |f T - g T|) + |g T - g j| := by
              gcongr
              exact abs_add_le _ _
        _ = |f i - f T| + |f T - g T| + |g T - g j| := by ring
    have hsum :
        |(preOfCauSeq f).approx (n + 1) - (preOfCauSeq g).approx (n + 1)|
          ≤ (3 : ℚ) / (2 ^ (n + 3)) := by
      -- use the three bounds
      have hf_tail' : |f i - f T| ≤ (1 : ℚ) / (2 ^ (n + 3)) := hf_tail
      have hfgT' : |f T - g T| ≤ (1 : ℚ) / (2 ^ (n + 3)) := hfgT
      have hg_tail' : |g T - g j| ≤ (1 : ℚ) / (2 ^ (n + 3)) := by
        simpa [abs_sub_comm] using hg_tail
      -- combine
      calc
        |(preOfCauSeq f).approx (n + 1) - (preOfCauSeq g).approx (n + 1)|
            ≤ |f i - f T| + |f T - g T| + |g T - g j| := by
                  simpa [preOfCauSeq, i, j] using habs
        _ ≤ (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 3)) + (1 : ℚ) / (2 ^ (n + 3)) := by
              gcongr
        _ = (3 : ℚ) / (2 ^ (n + 3)) := by ring
    have hbound : (3 : ℚ) / (2 ^ (n + 3)) ≤ (1 : ℚ) / (2 ^ n) := by
      have hcoeff : (3 : ℚ) / 8 ≤ 1 := by norm_num
      have hpos' : 0 ≤ (1 : ℚ) / (2 ^ n) := by positivity
      have h1 : (1 : ℚ) / (2 ^ (n + 3)) = (1 : ℚ) / (2 ^ n) / 8 := by
        simp [pow_add, div_eq_mul_inv]
        ring
      -- rewrite and compare the coefficients
      calc
        (3 : ℚ) / (2 ^ (n + 3))
            = (3 : ℚ) * ((1 : ℚ) / (2 ^ (n + 3))) := by
                simp [div_eq_mul_inv]
        _ = (3 : ℚ) * ((1 : ℚ) / (2 ^ n) / 8) := by
                simp [h1]
        _ = ((3 : ℚ) / 8) * ((1 : ℚ) / (2 ^ n)) := by
                ring
        _ ≤ (1 : ℚ) * ((1 : ℚ) / (2 ^ n)) := by
                gcongr
        _ = (1 : ℚ) / (2 ^ n) := by ring
    exact _root_.le_trans hsum hbound)

/-- Map `ℝ` to `CReal` using `Real.ringEquivCauchy`. -/
noncomputable def ofReal (x : ℝ) : CReal :=
  ofCauchy (Real.ringEquivCauchy x)

end FromReal

end CReal
end Computable
