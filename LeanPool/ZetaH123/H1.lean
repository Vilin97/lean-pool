/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# H1 for Thakur's hypotheses on power sums
-/

namespace ZetaH123.H1

/-
# Problem Description

Throughout, fix a prime `q` and nonnegative integers `d ≥ 0` and `k ≥ 0`.

## Definition 1 (The coefficient `b(i,d)`).
For each integer `i` with `0 ≤ i ≤ d`, define
  `b(i,d) := -((q ^ (d + 1) - q ^ (i+1))/(q - 1) + i * q ^ i)`.
Here `(q ^ (d + 1) - q ^ (i+1))/(q - 1) = q ^ (i+1) + q ^ (i+2) + ... + q ^ d` is an integer,
so `b(i,d) ∈ ℤ`, and `b(i,d) ≤ 0` with equality only when `i = d = 0`.

## Definition 2 (Carry-free addition in base `q`).
Let `x_0, ..., x_d` be nonnegative integers, written in base `q` as
`x_i = ∑_n a_{i,n} q ^ n` with `0 ≤ a_{i,n} ≤ q-1`. The addition
`x_0 + ... + x_d` has no carries in base `q` (is carry-free) if for every digit
position `n ≥ 0`, `∑_{i=0} ^ d a_{i,n} ≤ q-1`.

## Definition 3 (Admissible tuple).
A `(d + 1)`-tuple `(k_0, ..., k_d)` of nonnegative integers is admissible (for the
given `q`, `d`, `k`) if:
1. (Representation) `k = ∑_{i=0} ^ d k_i q ^ i`;
2. (Carry-free) the addition `k_0 + ... + k_d` has no carries in base `q`.

## Definition 4 (Objective function).
For an admissible tuple, `F(k_0, ..., k_d) := b(0,d) + ∑_{i=0} ^ d k_i b(i,d)`.

## Main Statement (Unique maximizer).
Let `q` be prime and `d, k ≥ 0`. Among all admissible `(d + 1)`-tuples, the value
`F` attains its maximum at exactly one admissible tuple.

## Notes
- The feasible set is nonempty: the tuple `(k, 0, ..., 0)` is admissible.
- The numbering uses 0-indexing throughout (`Fin (d + 1)`), matching the math.
-/

open Finset

/-- The `n`-th digit of `x` in base `q`, i.e. `a_{i,n}` for `x = ∑_n a_{i,n} q ^ n`. -/
def digit (q x n : ℕ) : ℕ := (x / q ^ n) % q

/-- The coefficient `b(i,d)`. The geometric sum `∑_{j=i+1} ^ d q ^ j` equals the integer
`(q ^ (d + 1) - q ^ (i+1))/(q - 1)`, so this matches the informal definition exactly. -/
def bCoeff (q i d : ℕ) : ℤ :=
  -((∑ j ∈ Finset.Ico (i + 1) (d + 1), (q : ℤ) ^ j) + (i : ℤ) * (q : ℤ) ^ i)

/-- Carry-free condition (Definition 2): in every digit position `n`, the sum of the
`n`-th base-`q` digits of the entries is at most `q - 1`. -/
def CarryFree (q d : ℕ) (kk : Fin (d + 1) → ℕ) : Prop :=
  ∀ n : ℕ, (∑ i : Fin (d + 1), digit q (kk i) n) ≤ q - 1

/-- Admissible tuple (Definition 3): satisfies the representation and carry-free
conditions. -/
def Admissible (q d k : ℕ) (kk : Fin (d + 1) → ℕ) : Prop :=
  (k = ∑ i : Fin (d + 1), kk i * q ^ (i : ℕ)) ∧ CarryFree q d kk

/-- The objective function `F` (Definition 4). -/
def F (q d : ℕ) (kk : Fin (d + 1) → ℕ) : ℤ :=
  bCoeff q 0 d + ∑ i : Fin (d + 1), (kk i : ℤ) * bCoeff q (i : ℕ) d

/-! ## Supporting lemmas

Elementary structural facts: every component of an admissible tuple is `≤ k`,
base-`q` digits are `≤ q-1`, the "all in slot 0" tuple is admissible, and the
admissible set is finite. -/

/-- Each component of an admissible tuple is at most `k`. -/
lemma admissible_le (q d k : ℕ) (hq : 1 ≤ q) (kk : Fin (d + 1) → ℕ)
    (h : Admissible q d k kk) (i : Fin (d + 1)) : kk i ≤ k := by
  obtain ⟨hrep, _⟩ := h
  rw [hrep]
  have hpow : 1 ≤ q ^ (i : ℕ) := Nat.one_le_pow _ _ hq
  calc kk i ≤ kk i * q ^ (i : ℕ) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ ∑ j : Fin (d + 1), kk j * q ^ (j : ℕ) :=
        Finset.single_le_sum (f := fun j => kk j * q ^ (j : ℕ))
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- `digit q x n ≤ q - 1` whenever `q ≥ 1`. -/
lemma digit_le (q x n : ℕ) (hq : 1 ≤ q) : digit q x n ≤ q - 1 := by
  unfold digit
  have := Nat.mod_lt (x / q ^ n) (show 0 < q from hq)
  omega

/-- The "all in slot 0" tuple `(k, 0, ..., 0)`. -/
def k0tuple (d k : ℕ) : Fin (d + 1) → ℕ := fun i => if (i : ℕ) = 0 then k else 0

lemma k0tuple_admissible (q d k : ℕ) (hq : 1 ≤ q) :
    Admissible q d k (k0tuple d k) := by
  constructor
  · -- representation
    rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · simp [k0tuple]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := by
        intro h; apply hb; exact Fin.ext h
      simp [k0tuple, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- carry-free
    intro n
    have heq : (∑ i : Fin (d + 1), digit q (k0tuple d k i) n)
        = digit q k n := by
      rw [Finset.sum_eq_single (0 : Fin (d + 1))]
      · simp [k0tuple]
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := by
          intro h; apply hb; exact Fin.ext h
        simp [k0tuple, this, digit]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [heq]
    exact digit_le q k n hq

/-- The set of admissible tuples is finite. -/
lemma admissible_finite (q d k : ℕ) (hq : 1 ≤ q) :
    {kk : Fin (d + 1) → ℕ | Admissible q d k kk}.Finite := by
  apply Set.Finite.subset
    (s := ↑(Fintype.piFinset (fun _ : Fin (d + 1) => Finset.range (k + 1))))
  · exact (Fintype.piFinset _).finite_toSet
  · intro kk hkk
    simp only [Set.mem_setOf_eq] at hkk
    simp only [Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_range]
    intro i
    have := admissible_le q d k hq kk hkk i
    omega

/-! ## The crux: uniqueness of the maximizer

Maximizing `F` is equivalent to minimizing the linear functional
`Φ(kk) = q ^ {d+1}·∑ᵢ kkᵢ + (q - 1)·∑ᵢ i·qⁱ·kkᵢ`, in which each "stone" in cell
`(i,n)` (one unit of the digit `a_{i,n}`) carries weight `q ^ {n+i}·g_i` with
`g_i = q ^ {d+1-i} + (q - 1)·i` strictly decreasing in `i` (informal.tex
`eq:Phi-H1`, `eq:g-decreasing-H1`). Two pillars: carry elimination
(`carry_elimination`: a maximizer's column sums are exactly the base-`q`
digits of `k`) and uniqueness of the greedy allocation via exchange arguments
(`move_down`, `move_parallelogram`). -/

/-! ### Digit bookkeeping for the single-column exchange -/

/-- **Digit no-cascade, target position.** Subtracting `r * q ^ n` from `x`, where
`r ≤ digit q x n`, decreases the `n`-th digit by exactly `r`. -/
lemma digit_sub_self (q x n r : ℕ) (hq : 1 ≤ q) (hr : r ≤ digit q x n) :
    digit q (x - r * q ^ n) n = digit q x n - r := by
  unfold digit at *
  have hpos : 0 < q ^ n := pow_pos (by omega) n
  have hrle : r ≤ x / q ^ n := le_trans hr (Nat.mod_le _ _)
  have hdiv : (x - r * q ^ n) / q ^ n = x / q ^ n - r := by
    have hle : r * q ^ n ≤ x := by
      calc r * q ^ n ≤ (x / q ^ n) * q ^ n := Nat.mul_le_mul_right _ hrle
        _ ≤ x := Nat.div_mul_le_self x (q ^ n)
    have key : (x - r * q ^ n) / q ^ n + r = x / q ^ n := by
      rw [← Nat.add_mul_div_right _ r hpos]
      congr 1; omega
    omega
  rw [hdiv]
  set y := x / q ^ n with hy
  conv_lhs => rw [← Nat.div_add_mod y q]
  rw [Nat.mul_comm, Nat.add_sub_assoc hr, Nat.add_comm, Nat.add_mul_mod_self_right]
  have hlt : y % q - r < q := by
    have := Nat.mod_lt y (show 0 < q by omega); omega
  exact Nat.mod_eq_of_lt hlt

/-- **Digit no-cascade, other positions.** Subtracting `r * q ^ n` from `x`, where
`r ≤ digit q x n`, leaves every digit at a position `m ≠ n` unchanged. -/
lemma digit_sub_other (q x n r m : ℕ) (hq : 1 ≤ q) (hr : r ≤ digit q x n) (hmn : m ≠ n) :
    digit q (x - r * q ^ n) m = digit q x m := by
  have hq0 : 0 < q := by omega
  unfold digit at *
  -- Global no-borrow fact: r * q ^ n ≤ x
  have hle : r * q ^ n ≤ x := by
    have hpos : 0 < q ^ n := pow_pos hq0 n
    have hrle : r ≤ x / q ^ n := le_trans hr (Nat.mod_le _ _)
    calc r * q ^ n ≤ (x / q ^ n) * q ^ n := Nat.mul_le_mul_right _ hrle
      _ ≤ x := Nat.div_mul_le_self x (q ^ n)
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- Case m < n: q ^ (m + 1) ∣ r*q ^ n, subtraction invisible mod q ^ (m + 1)
    have hdvd : q ^ (m + 1) ∣ r * q ^ n := by
      have hpd : q ^ (m + 1) ∣ q ^ n := pow_dvd_pow q (by omega)
      exact hpd.mul_left r
    have hmod : (x - r * q ^ n) % q ^ (m + 1) = x % q ^ (m + 1) := by
      have h : (x - r * q ^ n) ≡ x [MOD q ^ (m + 1)] := by
        rw [Nat.modEq_iff_dvd' (by omega : x - r * q ^ n ≤ x)]
        have hsub : x - (x - r * q ^ n) = r * q ^ n := by omega
        rw [hsub]; exact hdvd
      exact h
    -- relate digit to mod: y / q ^ m % q = (y % q ^ (m + 1)) / q ^ m
    have key : ∀ y : ℕ, y / q ^ m % q = (y % q ^ (m + 1)) / q ^ m := by
      intro y; rw [pow_succ]; exact (Nat.mod_mul_right_div_self y (q ^ m) q).symm
    rw [key (x - r * q ^ n), key x, hmod]
  · -- Case m > n: subtraction does not affect division by q ^ (n+1) ≤ q ^ m
    have hpos1 : 0 < q ^ (n + 1) := pow_pos hq0 (n + 1)
    -- r * q ^ n ≤ x % q ^ (n+1)
    have hrbound : r * q ^ n ≤ x % q ^ (n + 1) := by
      have hh : x % q ^ (n + 1) / q ^ n = (x / q ^ n) % q := by
        rw [pow_succ]; exact Nat.mod_mul_right_div_self x (q ^ n) q
      have hr2 : r ≤ x % q ^ (n + 1) / q ^ n := by rw [hh]; exact hr
      calc r * q ^ n ≤ (x % q ^ (n + 1) / q ^ n) * q ^ n := Nat.mul_le_mul_right _ hr2
        _ ≤ x % q ^ (n + 1) := Nat.div_mul_le_self _ _
    -- (x - r*q ^ n) / q ^ (n+1) = x / q ^ (n+1)
    have hdiv : (x - r * q ^ n) / q ^ (n + 1) = x / q ^ (n + 1) := by
      have hdm := Nat.div_add_mod x (q ^ (n + 1))
      have heq : x - r * q ^ n
          = (x % q ^ (n + 1) - r * q ^ n) + q ^ (n + 1) * (x / q ^ (n + 1)) := by omega
      rw [heq, Nat.add_mul_div_left _ _ hpos1]
      have hltt : x % q ^ (n + 1) - r * q ^ n < q ^ (n + 1) := by
        have := Nat.mod_lt x hpos1; omega
      rw [Nat.div_eq_of_lt hltt]; simp
    -- relate y / q ^ m to y / q ^ (n+1) via q ^ (n+1) * q ^ (m-n-1) = q ^ m
    have hpow : q ^ (n + 1) * q ^ (m - n - 1) = q ^ m := by
      rw [← pow_add]; congr 1; omega
    have key : ∀ y : ℕ, y / q ^ m = (y / q ^ (n + 1)) / q ^ (m - n - 1) := by
      intro y; rw [Nat.div_div_eq_div_mul, hpow]
    rw [key (x - r * q ^ n), key x, hdiv]

/-- **Digit add, target position.** Adding `q ^ n` to `x`, when `digit q x n < q-1`
(no carry triggered), increases the `n`-th digit by one. -/
lemma digit_add_self (q x n : ℕ) (hq : 1 ≤ q) (hlt : digit q x n + 1 < q) :
    digit q (x + q ^ n) n = digit q x n + 1 := by
  unfold digit at *
  have hpos : 0 < q ^ n := pow_pos (by omega) n
  have hdiv : (x + q ^ n) / q ^ n = x / q ^ n + 1 := by
    rw [Nat.add_div_right _ hpos]
  rw [hdiv]
  set y := x / q ^ n with hy
  conv_lhs => rw [← Nat.div_add_mod y q]
  rw [Nat.add_assoc, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hlt

/-- **Digit add, other positions.** Adding `q ^ n` to `x`, when `digit q x n < q-1`,
leaves every digit at a position `m ≠ n` unchanged. -/
lemma digit_add_other (q x n m : ℕ) (hq : 1 ≤ q) (hlt : digit q x n + 1 < q) (hmn : m ≠ n) :
    digit q (x + q ^ n) m = digit q x m := by
  have hq0 : 0 < q := by omega
  unfold digit at *
  rcases lt_or_gt_of_ne hmn with hmlt | hgt
  · have hdvd : q ^ (m + 1) ∣ q ^ n := pow_dvd_pow q (by omega)
    have hmod : (x + q ^ n) % q ^ (m + 1) = x % q ^ (m + 1) := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, Nat.add_mul_mod_self_left]
    have key : ∀ y : ℕ, y / q ^ m % q = (y % q ^ (m + 1)) / q ^ m := by
      intro y; rw [pow_succ]; exact (Nat.mod_mul_right_div_self y (q ^ m) q).symm
    rw [key (x + q ^ n), key x, hmod]
  · have hpos1 : 0 < q ^ (n + 1) := pow_pos hq0 (n + 1)
    have hposn : 0 < q ^ n := pow_pos hq0 n
    have hbound : x % q ^ (n + 1) + q ^ n < q ^ (n + 1) := by
      have hw : x % q ^ (n + 1) / q ^ n = (x / q ^ n) % q := by
        rw [pow_succ]; exact Nat.mod_mul_right_div_self x (q ^ n) q
      have hdm2 := Nat.div_add_mod (x % q ^ (n + 1)) (q ^ n)
      have hmod2 := Nat.mod_lt (x % q ^ (n + 1)) hposn
      rw [hw] at hdm2
      have h2 : (x / q ^ n % q + 2) * q ^ n ≤ q ^ (n + 1) := by
        rw [pow_succ]
        calc (x / q ^ n % q + 2) * q ^ n ≤ q * q ^ n := by
              apply Nat.mul_le_mul_right; omega
          _ = q ^ n * q := by ring
      nlinarith [hdm2, hmod2, h2]
    have hdiv : (x + q ^ n) / q ^ (n + 1) = x / q ^ (n + 1) := by
      have hdm := Nat.div_add_mod x (q ^ (n + 1))
      have heq : x + q ^ n
          = (x % q ^ (n + 1) + q ^ n) + q ^ (n + 1) * (x / q ^ (n + 1)) := by omega
      rw [heq, Nat.add_mul_div_left _ _ hpos1, Nat.div_eq_of_lt hbound]
      simp
    have hpow : q ^ (n + 1) * q ^ (m - n - 1) = q ^ m := by
      rw [← pow_add]; congr 1; omega
    have key : ∀ y : ℕ, y / q ^ m = (y / q ^ (n + 1)) / q ^ (m - n - 1) := by
      intro y; rw [Nat.div_div_eq_div_mul, hpow]
    rw [key (x + q ^ n), key x, hdiv]

/-- The "stone weight" `gᵢ = q ^ {d+1-i} + (q - 1)·i` (informal.tex `eq:Phi-H1`). -/
def gWeight (q d i : ℕ) : ℕ := q ^ (d + 1 - i) + (q - 1) * i

/-- **The strict Φ-decrease arithmetic.** The key identity
`q·g_{j+1} + (q - 1) ^ 2·(d-j) = g_j + (q - 1)·g_d`, i.e.
`g_j + (q - 1)·g_d - q·g_{j+1} = (q - 1) ^ 2·(d-j) > 0` for `j < d`, `q ≥ 2`
(informal.tex `lem:H1-carry-elimination`). -/
lemma gWeight_exchange_pos (q d j : ℕ) (hq : 2 ≤ q) (hj : j < d) :
    q * gWeight q d (j + 1) + (q - 1) ^ 2 * (d - j) =
      gWeight q d j + (q - 1) * gWeight q d d := by
  unfold gWeight
  obtain ⟨t, rfl⟩ : ∃ t, d = j + 1 + t := ⟨d - j - 1, by omega⟩
  have e1 : j + 1 + t + 1 - (j + 1) = t + 1 := by omega
  have e2 : j + 1 + t + 1 - j = t + 2 := by omega
  have e3 : j + 1 + t + 1 - (j + 1 + t) = 1 := by omega
  have e4 : j + 1 + t - j = t + 1 := by omega
  rw [e1, e2, e3, e4]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  have e5 : p + 2 - 1 = p + 1 := by omega
  rw [e5]
  ring

/-- **The `F ↔ Φ` reduction.** Comparing `F` of two admissible tuples with the
**same** `k` reduces to comparing their `Φ`, where
`Φ(kk) = q ^ {d+1}·∑ᵢ kkᵢ + (q - 1)·∑ᵢ i·qⁱ·kkᵢ`: a strict `Φ`-decrease (from `kk` to `kk'`)
gives a strict `F`-increase. (Identity `(q - 1)·(-(∑ᵢ kkᵢ·b(i,d))) + q·k = Φ(kk)`.) -/
lemma F_lt_of_Phi_lt (q d _k : ℕ) (hq : 2 ≤ q)
    (kk kk' : Fin (d + 1) → ℕ)
    (hk : (∑ i : Fin (d + 1), kk i * q ^ (i : ℕ)) = (∑ i : Fin (d + 1), kk' i * q ^ (i : ℕ)))
    (hPhi : (q ^ (d + 1) * ∑ i : Fin (d + 1), kk' i
              + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk' i)
          < (q ^ (d + 1) * ∑ i : Fin (d + 1), kk i
              + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk i)) :
    F q d kk < F q d kk' := by
  have hq1 : (1 : ℕ) ≤ q := by omega
  -- per-index geometric identity
  have geo : ∀ i : Fin (d + 1),
      ((q : ℤ) - 1) * (∑ j ∈ Finset.Ico ((i : ℕ) + 1) (d + 1), (q : ℤ) ^ j)
        = (q : ℤ) ^ (d + 1) - (q : ℤ) ^ ((i : ℕ) + 1) := by
    intro i
    have hile : (i : ℕ) + 1 ≤ d + 1 := by
      have := i.2; omega
    rw [Finset.sum_Ico_eq_sub _ hile, mul_sub, mul_comm ((q : ℤ) - 1), mul_comm ((q : ℤ) - 1),
      geom_sum_mul, geom_sum_mul]
    ring
  -- key identity for any tuple
  have key : ∀ (tt : Fin (d + 1) → ℕ),
      ((q : ℤ) - 1) * (∑ i : Fin (d + 1), (tt i : ℤ) * bCoeff q (i : ℕ) d)
        = (q : ℤ) * (∑ i : Fin (d + 1), (tt i : ℤ) * (q : ℤ) ^ (i : ℕ))
          - ((q : ℤ) ^ (d + 1) * (∑ i : Fin (d + 1), (tt i : ℤ))
            + ((q : ℤ) - 1) * ∑ i : Fin (d + 1),
              (i : ℤ) * (q : ℤ) ^ (i : ℕ) * (tt i)) := by
    intro tt
    rw [Finset.mul_sum]
    rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i => (tt i : ℤ) * (q : ℤ) ^ (i : ℕ))]
    rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin (d + 1)))) (f := fun i => (tt i : ℤ))]
    rw [Finset.mul_sum (s := (Finset.univ : Finset (Fin (d + 1))))
      (f := fun i => (i : ℤ) * (q : ℤ) ^ (i : ℕ) * (tt i))]
    rw [show (∑ i : Fin (d + 1), (q : ℤ) * ((tt i : ℤ) * (q : ℤ) ^ (i : ℕ)))
          - ((∑ i : Fin (d + 1), (q : ℤ) ^ (d + 1) * (tt i : ℤ))
            + ∑ i : Fin (d + 1), ((q : ℤ) - 1) * ((i : ℤ) * (q : ℤ) ^ (i : ℕ) * (tt i)))
        = ∑ i : Fin (d + 1), ((q : ℤ) * ((tt i : ℤ) * (q : ℤ) ^ (i : ℕ))
            - ((q : ℤ) ^ (d + 1) * (tt i : ℤ)
              + ((q : ℤ) - 1) * ((i : ℤ) * (q : ℤ) ^ (i : ℕ) * (tt i)))) by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]]
    apply Finset.sum_congr rfl
    intro i _
    unfold bCoeff
    have hg := geo i
    have hexp : (q : ℤ) ^ ((i : ℕ) + 1) = (q : ℤ) * (q : ℤ) ^ (i : ℕ) := by
      rw [pow_succ]; ring
    -- LHS = (q - 1) * (tt i) * (-(S + i*q ^ i)) where (q - 1)*S = q ^ {d+1} - q ^ {i+1}
    have : ((q : ℤ) - 1) * ((tt i : ℤ) *
        -((∑ j ∈ Finset.Ico ((i : ℕ) + 1) (d + 1), (q : ℤ) ^ j) + (i : ℤ) * (q : ℤ) ^ (i : ℕ)))
        = (tt i : ℤ) * (- (((q : ℤ) - 1) * (∑ j ∈ Finset.Ico ((i : ℕ) + 1) (d + 1), (q : ℤ) ^ j))
            - ((q : ℤ) - 1) * ((i : ℤ) * (q : ℤ) ^ (i : ℕ))) := by ring
    rw [this, hg, hexp]
    ring
  have kkey := key kk
  have kkey' := key kk'
  -- cast hk to ℤ
  have hkZ : (∑ i : Fin (d + 1), (kk i : ℤ) * (q : ℤ) ^ (i : ℕ))
      = (∑ i : Fin (d + 1), (kk' i : ℤ) * (q : ℤ) ^ (i : ℕ)) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hk
    push_cast at this ⊢
    convert this using 2
  -- cast hPhi to ℤ
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub hq1]; simp
  have hPhiZ : ((q : ℤ) ^ (d + 1) * ∑ i : Fin (d + 1), (kk' i : ℤ)
        + ((q : ℤ) - 1) * ∑ i : Fin (d + 1), (i : ℤ) * (q : ℤ) ^ (i : ℕ) * (kk' i))
      < ((q : ℤ) ^ (d + 1) * ∑ i : Fin (d + 1), (kk i : ℤ)
        + ((q : ℤ) - 1) * ∑ i : Fin (d + 1), (i : ℤ) * (q : ℤ) ^ (i : ℕ) * (kk i)) := by
    have := hPhi
    have hcastineq := (Nat.cast_lt (α := ℤ)).mpr this
    push_cast [hcast] at hcastineq
    simpa only using hcastineq
  -- now finish
  unfold F
  have hqpos : (0 : ℤ) < (q : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
    linarith
  -- (q - 1)*(F kk' - F kk) = Φ kk - Φ kk' > 0
  rw [← sub_pos]
  -- goal: 0 < (bCoeff q 0 d + ∑ kk' ...) - (bCoeff q 0 d + ∑ kk ...)
  have hdiff : ((q : ℤ) - 1) *
      ((bCoeff q 0 d + ∑ i : Fin (d + 1), (kk' i : ℤ) * bCoeff q (i : ℕ) d)
        - (bCoeff q 0 d + ∑ i : Fin (d + 1), (kk i : ℤ) * bCoeff q (i : ℕ) d)) > 0 := by
    have expand : ((q : ℤ) - 1) *
        ((bCoeff q 0 d + ∑ i : Fin (d + 1), (kk' i : ℤ) * bCoeff q (i : ℕ) d)
          - (bCoeff q 0 d + ∑ i : Fin (d + 1), (kk i : ℤ) * bCoeff q (i : ℕ) d))
        = (((q : ℤ) - 1) * (∑ i : Fin (d + 1), (kk' i : ℤ) * bCoeff q (i : ℕ) d))
          - (((q : ℤ) - 1) * (∑ i : Fin (d + 1), (kk i : ℤ) * bCoeff q (i : ℕ) d)) := by ring
    rw [expand, kkey, kkey', hkZ]
    linarith [hPhiZ]
  nlinarith [hdiff, hqpos]

/-- **Row selection (take-from-top).** Given nonnegative row-counts `a` on `Fin (d + 1)`
and a target `c` with `1 ≤ c ≤ ∑ a`, there is a removal function `r ≤ a` removing
exactly `c` stones, taken greedily from the *top* rows: there is a maximal removed row
`J` (`r J > 0`) above which nothing is removed (`r i = 0` for `i > J`). -/
theorem row_take_top : ∀ (d : ℕ) (a : Fin (d + 1) → ℕ) (c : ℕ),
    1 ≤ c → c ≤ ∑ i, a i →
    ∃ (r : Fin (d + 1) → ℕ),
      (∀ i, r i ≤ a i) ∧ (∑ i, r i) = c ∧
      (∃ J : Fin (d + 1), 0 < r J ∧ ∀ i : Fin (d + 1), (J:ℕ) < (i : ℕ) → r i = 0) := by
  intro d
  induction d with
  | zero =>
    intro a c hc hcsum
    refine ⟨fun _ => c, ?_, ?_, ⟨0, ?_, ?_⟩⟩
    · intro i; fin_cases i; simpa [Fin.sum_univ_one] using hcsum
    · simp
    · exact Nat.lt_of_lt_of_le Nat.zero_lt_one hc
    · intro i hi; exact absurd i.2 (by omega)
  | succ d ih =>
    intro a c hc hcsum
    rw [Fin.sum_univ_castSucc] at hcsum
    set aL := a (Fin.last (d + 1)) with haL
    set a' : Fin (d + 1) → ℕ := fun i => a i.castSucc with ha'
    by_cases hcase : c ≤ ∑ i, a' i
    · obtain ⟨r', hr'le, hr'sum, J', hJ'pos, hJ'top⟩ := ih a' c hc hcase
      refine ⟨Fin.lastCases 0 r', ?_, ?_, ⟨J'.castSucc, ?_, ?_⟩⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp
        · intro i'; simpa using hr'le i'
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        rw [hr'sum]; ring
      · simpa using hJ'pos
      · refine Fin.lastCases ?_ (fun i' hi => ?_)
        · intro hi; simp
        · simp only [Fin.lastCases_castSucc]
          apply hJ'top i'
          simpa using hi
    · push Not at hcase
      set s := ∑ i, a' i with hs
      have hrem : 1 ≤ c - s := by omega
      have hremle : c - s ≤ aL := by omega
      refine ⟨Fin.lastCases (c - s) a', ?_, ?_, ⟨Fin.last (d + 1), ?_, ?_⟩⟩
      · intro i
        refine Fin.lastCases ?_ (fun i' => ?_) i
        · simpa using hremle
        · simp only [Fin.lastCases_castSucc, ha', le_refl]
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        rw [← hs]; omega
      · simp only [Fin.lastCases_last]; omega
      · intro i hi
        exfalso
        have := i.2
        simp only [Fin.val_last] at hi
        omega

/-- `digit q x n` times its place value `q ^ n` is at most `x`. -/
theorem digit_place_le (q x n : ℕ) : digit q x n * q ^ n ≤ x := by
  unfold digit
  calc ((x / q ^ n) % q) * q ^ n ≤ (x / q ^ n) * q ^ n := by
        apply Nat.mul_le_mul_right; exact Nat.mod_le _ _
    _ ≤ x := Nat.div_mul_le_self _ _

/-- A small per-index algebraic identity used in representation preservation. -/
theorem peridx (a x b p : ℕ) (hx : x ≤ a) :
    (a - x + b) * p + x * p = a * p + b * p := by
  obtain ⟨t, ht⟩ := Nat.le.dest hx; subst ht; rw [Nat.add_sub_cancel_left]; ring

/-- **Representation preservation for the single-column exchange.** Removing `r i`
stones at cell `(i, m-i)` (`r i ≤ a_{i,m-i}`, `r i = 0` for `i > m`, `∑ r = q`) and
adding one stone at cell `(j+1, m-j)` (`jj = j+1`, `j ≤ m`) leaves `∑ kk_i q ^ i`
unchanged. -/
theorem repr_preserved (q d m : ℕ) (_hq : 1 ≤ q) (kk : Fin (d + 1) → ℕ)
    (r : Fin (d + 1) → ℕ) (jj : Fin (d + 1)) (j : ℕ)
    (hjj : (jj : ℕ) = j + 1) (hjm : j ≤ m)
    (hrle : ∀ i : Fin (d + 1), r i ≤ digit q (kk i) (m - (i : ℕ)))
    (hr0 : ∀ i : Fin (d + 1), m < (i : ℕ) → r i = 0)
    (hrsum : (∑ i, r i) = q) :
    (∑ i : Fin (d + 1),
      (kk i - r i * q ^ (m - (i : ℕ)) + (if i = jj then q ^ (m - j) else 0))
        * q ^ (i : ℕ))
      = ∑ i : Fin (d + 1), kk i * q ^ (i : ℕ) := by
  have hno : ∀ i : Fin (d + 1), r i * q ^ (m - (i : ℕ)) ≤ kk i := by
    intro i
    calc r i * q ^ (m - (i : ℕ)) ≤ digit q (kk i) (m - (i : ℕ)) * q ^ (m-(i : ℕ)) :=
          Nat.mul_le_mul_right _ (hrle i)
      _ ≤ kk i := digit_place_le _ _ _
  have hkey : (∑ i : Fin (d + 1),
        (kk i - r i * q ^ (m - (i : ℕ)) + (if i = jj then q ^ (m - j) else 0))
          * q ^ (i : ℕ))
        + ∑ i : Fin (d + 1), (r i * q ^ (m - (i : ℕ))) * q ^ (i : ℕ)
      = (∑ i : Fin (d + 1), kk i * q ^ (i : ℕ))
        + ∑ i : Fin (d + 1), (if i = jj then q ^ (m - j) else 0) * q ^ (i : ℕ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact peridx (kk i) (r i * q ^ (m - (i : ℕ)))
      (if i = jj then q ^ (m - j) else 0) (q ^ (i : ℕ)) (hno i)
  have hsum1 :
      (∑ i : Fin (d + 1), (r i * q ^ (m - (i : ℕ))) * q ^ (i : ℕ))
        = q ^ (m + 1) := by
    have heq : ∑ i : Fin (d + 1), (r i * q ^ (m - (i : ℕ))) * q ^ (i : ℕ)
        = q ^ m * ∑ i, r i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : ℕ) ≤ m
      · have hpp : q ^ (m - (i : ℕ)) * q ^ (i : ℕ) = q ^ m := by
          rw [← pow_add]
          congr 1
          omega
        rw [mul_assoc, hpp, Nat.mul_comm]
      · push Not at hi; simp [hr0 i hi]
    rw [heq, hrsum, pow_succ]
  have hsum2 :
      (∑ i : Fin (d + 1), (if i = jj then q ^ (m - j) else 0) * q ^ (i : ℕ))
        = q ^ (m + 1) := by
    rw [Finset.sum_eq_single jj]
    · rw [if_pos rfl, hjj, ← pow_add]; congr 1; omega
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum1, hsum2] at hkey
  omega

/-- **Maximal removed non-top row.** From a removal `r` with `∑ r = q` whose top-row
value is `≤ q-1`, there is a maximal row `j < d` that loses a stone, with no removed
rows strictly between `j` and `d`. -/
theorem row_select_j (q d : ℕ) (hq : 2 ≤ q) (r : Fin (d + 1) → ℕ)
    (hrsum : (∑ i, r i) = q) (hrlast : r (Fin.last d) ≤ q - 1) :
    ∃ j : Fin (d + 1), (j : ℕ) < d ∧ 0 < r j ∧
      (∀ i : Fin (d + 1), (j : ℕ) < (i : ℕ) → (i : ℕ) < d → r i = 0) := by
  set S : Finset (Fin (d + 1)) := Finset.univ.filter (fun i => (i : ℕ) < d ∧ 0 < r i) with hS
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ i : Fin (d + 1), (i : ℕ) < d → r i = 0 := by
      intro i hi
      by_contra hr
      have : i ∈ S := by
        rw [hS]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, Nat.pos_of_ne_zero hr⟩
      rw [hempty] at this; exact absurd this (Finset.notMem_empty _)
    have hsplit : (∑ i, r i) = r (Fin.last d) := by
      rw [← Finset.sum_subset (Finset.subset_univ {Fin.last d})]
      · simp
      · intro i _ hi
        simp only [Finset.mem_singleton] at hi
        apply hall
        have := i.2
        rcases Nat.lt_or_ge (i : ℕ) d with h | h
        · exact h
        · exfalso; apply hi; apply Fin.ext; simp only [Fin.val_last]; omega
    rw [hsplit] at hrsum; omega
  set j := S.max' hSne with hj
  have hjS : j ∈ S := S.max'_mem hSne
  rw [hS] at hjS; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS
  refine ⟨j, hjS.1, hjS.2, ?_⟩
  intro i hlt hid
  by_contra hr
  have hiS : i ∈ S := by
    rw [hS]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hid, Nat.pos_of_ne_zero hr⟩
  have hle := S.le_max' i hiS
  rw [← hj] at hle
  have : (i : ℕ) ≤ (j : ℕ) := hle
  omega

/-- **Carry-free preservation for the single-column exchange.** The exchanged tuple
`kk'` (remove `r i` stones at cell `(i,m-i)`, add one at `(jj,m-jv)`, `jj = jv+1`)
stays carry-free. `jrow` is the maximal removed non-top row, `jv = jrow`. -/
lemma exchange_carryfree (q d m : ℕ) (hq2 : 2 ≤ q) (kk : Fin (d + 1) → ℕ)
    (hcf : CarryFree q d kk)
    (r : Fin (d + 1) → ℕ) (jrow jj : Fin (d + 1)) (jv : ℕ)
    (hjv : jv = (jrow : ℕ)) (hjjval : (jj : ℕ) = jv + 1) (_hjm : jv ≤ m)
    (hrdig : ∀ i : Fin (d + 1), r i ≤ digit q (kk i) (m - (i : ℕ)))
    (_hr0 : ∀ i : Fin (d + 1), m < (i : ℕ) → r i = 0)
    (hjpos : 0 < r jrow)
    (kk' : Fin (d + 1) → ℕ)
    (hkk' : ∀ i, kk' i = kk i - r i * q ^ (m - (i : ℕ)) + (if i = jj then q ^ (m - jv) else 0)) :
    CarryFree q d kk' := by
  have hq1 : 1 ≤ q := by omega
  -- the subtracted value at each row
  set x : Fin (d + 1) → ℕ := fun i => kk i - r i * q ^ (m - (i : ℕ)) with hx
  -- per-row: subtraction never increases any digit
  have hsub_le : ∀ (i : Fin (d + 1)) (n : ℕ), digit q (x i) n ≤ digit q (kk i) n := by
    intro i n
    by_cases hn : n = m - (i : ℕ)
    · subst hn
      rw [hx, digit_sub_self q (kk i) (m - (i : ℕ)) (r i) hq1 (hrdig i)]
      omega
    · rw [hx, digit_sub_other q (kk i) (m - (i : ℕ)) (r i) n hq1 (hrdig i) hn]
  -- jj ≠ jrow since their values differ
  have hjj_ne_jrow : jj ≠ jrow := by
    intro h
    rw [h] at hjjval
    omega
  -- digit of kk jrow at m-jv is ≥ r jrow ≥ 1
  have hjrow_pos_pos : m - (jrow : ℕ) = m - jv := by rw [hjv]
  have hjrow_dig : r jrow ≤ digit q (kk jrow) (m - jv) := by
    have := hrdig jrow; rw [hjrow_pos_pos] at this; exact this
  -- the two summands jrow and jj are distinct; combined with hcf gives the no-overflow bound
  have hkk_jj_bound : digit q (kk jj) (m - jv) + 1 < q := by
    have hsum := hcf (m - jv)
    -- split off jj and jrow from the sum
    have hpair : digit q (kk jj) (m - jv) + digit q (kk jrow) (m - jv)
        ≤ ∑ i : Fin (d + 1), digit q (kk i) (m - jv) := by
      have hsub : ({jj, jrow} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset (f := fun i => digit q (kk i) (m - jv)) hsub
      rw [Finset.sum_pair hjj_ne_jrow] at this
      exact this
    omega
  -- precondition for digit_add_self / digit_add_other at jj
  have hadd_pre : digit q (x jj) (m - jv) + 1 < q := by
    have := hsub_le jj (m - jv)
    omega
  -- rewrite kk' via hkk'
  intro n
  -- We'll do two cases on n.
  by_cases hn : n = m - jv
  · -- the addition-affected position
    subst hn
    -- Need: ∑ i, digit q (kk' i) (m - jv) ≤ q - 1
    -- precondition for digit_add_self at jj
    -- digit q (x jj) (m-jv) ≤ digit q (kk jj) (m-jv), and the latter +1 < q
    -- jj's digit: digit q (kk' jj)(m-jv) = digit q (x jj)(m-jv) + 1
    have hjj_val : digit q (kk' jj) (m - jv) = digit q (x jj) (m - jv) + 1 := by
      rw [hkk' jj, if_pos rfl]
      exact digit_add_self q (x jj) (m - jv) hq1 hadd_pre
    -- jrow's digit: digit q (kk' jrow)(m-jv) = digit q (x jrow)(m-jv)
    have hjrow_val_eq : digit q (x jrow) (m - jv) = digit q (kk jrow) (m - jv) - r jrow := by
      rw [hx, ← hjrow_pos_pos]
      exact digit_sub_self q (kk jrow) (m - (jrow : ℕ)) (r jrow) hq1
        (by rw [hjrow_pos_pos]; exact hjrow_dig)
    have hjrow_val : digit q (kk' jrow) (m - jv) = digit q (kk jrow) (m - jv) - r jrow := by
      rw [hkk' jrow, if_neg (Ne.symm hjj_ne_jrow), add_zero, ← hjrow_val_eq]
    -- It suffices to show ∑ i, digit q (kk' i)(m-jv) ≤ ∑ i, digit q (kk i)(m-jv) ≤ q-1
    refine le_trans ?_ (hcf (m - jv))
    -- split off {jj, jrow}
    have hpair_mem : ({jj, jrow} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_sdiff hpair_mem (f := fun i => digit q (kk' i) (m - jv)),
        ← Finset.sum_sdiff hpair_mem (f := fun i => digit q (kk i) (m - jv))]
    apply Nat.add_le_add
    · -- the rest: pointwise ≤
      apply Finset.sum_le_sum
      intro i hi
      rw [hkk' i]
      have hi' : i ≠ jj ∧ i ≠ jrow := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hi
        exact hi
      rw [if_neg hi'.1, add_zero]
      exact hsub_le i (m - jv)
    · -- the pair {jj, jrow}
      rw [Finset.sum_pair hjj_ne_jrow, Finset.sum_pair hjj_ne_jrow]
      rw [hjj_val, hjrow_val]
      have h1 := hsub_le jj (m - jv)
      omega
  · -- n ≠ m - jv: the addition does not touch digit n, so every row is ≤ kk i
    have hle : ∀ i : Fin (d + 1), digit q (kk' i) n ≤ digit q (kk i) n := by
      intro i
      rw [hkk' i]
      by_cases hij : i = jj
      · subst hij
        -- kk' i = x i + q ^ (m-jv); digit at n ≠ m-jv unaffected by add
        rw [if_pos rfl]
        -- need precondition digit q (x i) (m-jv) + 1 < q
        rw [digit_add_other q (x i) (m - jv) n hq1 hadd_pre hn]
        exact hsub_le i n
      · rw [if_neg hij, add_zero]
        exact hsub_le i n
    calc ∑ i, digit q (kk' i) n ≤ ∑ i : Fin (d + 1), digit q (kk i) n :=
          Finset.sum_le_sum (fun i _ => hle i)
      _ ≤ q - 1 := hcf n

/-- **Strict `F`-increase for the single-column exchange.** The exchanged tuple `kk'`
has strictly larger `F`, since `Φ` drops by `q ^ m·(q - 1) ^ 2·(d-jv) > 0`. -/
lemma exchange_phi_gain (q d k m : ℕ) (hq2 : 2 ≤ q) (kk : Fin (d + 1) → ℕ)
    (hrep : k = ∑ i : Fin (d + 1), kk i * q ^ (i : ℕ))
    (r : Fin (d + 1) → ℕ) (jrow jj : Fin (d + 1)) (jv : ℕ)
    (hjv : jv = (jrow : ℕ)) (hjjval : (jj : ℕ) = jv + 1) (hjm : jv ≤ m) (hjd : jv < d)
    (hrdig : ∀ i : Fin (d + 1), r i ≤ digit q (kk i) (m - (i : ℕ)))
    (hr0 : ∀ i : Fin (d + 1), m < (i : ℕ) → r i = 0)
    (hrsum : (∑ i, r i) = q)
    (hjpos : 0 < r jrow)
    (_hjtop : ∀ i : Fin (d + 1), jv < (i : ℕ) → (i : ℕ) < d → r i = 0)
    (kk' : Fin (d + 1) → ℕ)
    (hkk' : ∀ i, kk' i = kk i - r i * q ^ (m - (i : ℕ)) + (if i = jj then q ^ (m - jv) else 0)) :
    F q d kk < F q d kk' := by
  have hq1 : 1 ≤ q := by omega
  -- weight per row in Φ
  set w : Fin (d + 1) → ℕ := fun i => q ^ (d + 1) + (q - 1) * ((i : ℕ) * q ^ (i : ℕ)) with hw
  -- Φ written as ∑ w_i tt_i
  have hPhiEq : ∀ tt : Fin (d + 1) → ℕ,
      q ^ (d + 1) * ∑ i : Fin (d + 1), tt i
        + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * tt i
      = ∑ i : Fin (d + 1), w i * tt i := by
    intro tt
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hw]
    ring
  -- no-borrow fact
  have hno : ∀ i : Fin (d + 1), r i * q ^ (m - (i : ℕ)) ≤ kk i := by
    intro i
    calc r i * q ^ (m - (i : ℕ)) ≤ digit q (kk i) (m - (i : ℕ)) * q ^ (m - (i : ℕ)) :=
          Nat.mul_le_mul_right _ (hrdig i)
      _ ≤ kk i := digit_place_le _ _ _
  -- the central additive identity:  Φ kk' + ∑ w_i r_i q ^ (m-i) = Φ kk + w_jj q ^ (m-jv)
  have hbal : (∑ i : Fin (d + 1), w i * kk' i)
        + ∑ i : Fin (d + 1), w i * (r i * q ^ (m - (i : ℕ)))
      = (∑ i : Fin (d + 1), w i * kk i)
        + ∑ i : Fin (d + 1), w i * (if i = jj then q ^ (m - jv) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hkk' i]
    have hnoi := hno i
    have hle : w i * (r i * q ^ (m - (i : ℕ))) ≤ w i * kk i := Nat.mul_le_mul_left _ hnoi
    set c := (if i = jj then q ^ (m - jv) else 0) with hc
    rw [Nat.mul_add, Nat.mul_sub]
    have hsub : w i * kk i - w i * (r i * q ^ (m - (i : ℕ))) + w i * c
        + w i * (r i * q ^ (m - (i : ℕ))) = w i * kk i + w i * c := by omega
    exact hsub
  -- compute  ∑ w_i r_i q ^ (m-i) = q ^ m * ∑ g_i r_i
  have hwq : ∀ i : Fin (d + 1), (i : ℕ) ≤ m →
      w i * q ^ (m - (i : ℕ)) = q ^ m * gWeight q d (i : ℕ) := by
    intro i hi
    simp only [hw, gWeight]
    have h1 : q ^ (d + 1) * q ^ (m - (i : ℕ)) = q ^ m * q ^ (d + 1 - (i : ℕ)) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hpp : q ^ (i : ℕ) * q ^ (m - (i : ℕ)) = q ^ m := by
      rw [← pow_add]; congr 1; omega
    calc (q ^ (d + 1) + (q - 1) * ((i : ℕ) * q ^ (i : ℕ))) * q ^ (m - (i : ℕ))
        = q ^ (d + 1) * q ^ (m - (i : ℕ))
          + (q - 1) * (i : ℕ) * (q ^ (i : ℕ) * q ^ (m - (i : ℕ))) := by ring
      _ = q ^ m * q ^ (d + 1 - (i : ℕ)) + (q - 1) * (i : ℕ) * q ^ m := by rw [h1, hpp]
      _ = q ^ m * (q ^ (d + 1 - (i : ℕ)) + (q - 1) * (i : ℕ)) := by ring
  have hsumr : (∑ i : Fin (d + 1), w i * (r i * q ^ (m - (i : ℕ))))
      = q ^ m * ∑ i : Fin (d + 1), gWeight q d (i : ℕ) * r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) ≤ m
    · have := hwq i hi
      calc w i * (r i * q ^ (m - (i : ℕ))) = (w i * q ^ (m - (i : ℕ))) * r i := by ring
        _ = (q ^ m * gWeight q d (i : ℕ)) * r i := by rw [this]
        _ = q ^ m * (gWeight q d (i : ℕ) * r i) := by ring
    · push Not at hi
      rw [hr0 i hi]; ring
  -- compute  w_jj q ^ (m-jv) = q ^ m * (q * g_{jv+1})
  have hwjj : (∑ i : Fin (d + 1), w i * (if i = jj then q ^ (m - jv) else 0))
      = q ^ m * (q * gWeight q d (jv + 1)) := by
    rw [Finset.sum_eq_single jj]
    · rw [if_pos rfl]
      simp only [hw, gWeight]
      have hjjexp : (jj : ℕ) = jv + 1 := hjjval
      rw [hjjexp]
      have h1 : q ^ (d + 1) * q ^ (m - jv) = q ^ m * q ^ (d + 1 - jv) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have hpp : q ^ (jv + 1) * q ^ (m - jv) = q ^ m * q := by
        rw [← pow_add, ← pow_succ]; congr 1; omega
      have hpd : q ^ (d + 1 - jv) = q * q ^ (d + 1 - (jv + 1)) := by
        rw [← pow_succ']; congr 1; omega
      calc (q ^ (d + 1) + (q - 1) * ((jv + 1) * q ^ (jv + 1))) * q ^ (m - jv)
          = q ^ (d + 1) * q ^ (m - jv)
            + (q - 1) * (jv + 1) * (q ^ (jv + 1) * q ^ (m - jv)) := by ring
        _ = q ^ m * q ^ (d + 1 - jv) + (q - 1) * (jv + 1) * (q ^ m * q) := by rw [h1, hpp]
        _ = q ^ m * (q * q ^ (d + 1 - (jv + 1)) + q * ((q - 1) * (jv + 1))) := by
              rw [hpd]; ring
        _ = q ^ m * (q * (q ^ (d + 1 - (jv + 1)) + (q - 1) * (jv + 1))) := by ring
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  -- g_d is the minimum weight
  have hgmin : ∀ i : Fin (d + 1), gWeight q d d ≤ gWeight q d (i : ℕ) := by
    -- helper power inequality
    have hpow : ∀ e : ℕ, q + (q - 1) * e ≤ q ^ (e + 1) := by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
      have he1 : p + 2 - 1 = p + 1 := by omega
      rw [he1]
      intro e
      induction e with
      | zero => simp
      | succ n ih =>
        have hexp : (p + 2) ^ (n + 1 + 1) = (p + 2) ^ (n + 1) * (p + 2) := by rw [pow_succ]
        have hge : (p + 2) ≤ (p + 2) ^ (n + 1) := by nlinarith [ih]
        have hmul : ((p + 2) + (p + 1) * n) * (p + 2)
            ≤ (p + 2) ^ (n + 1) * (p + 2) := Nat.mul_le_mul_right _ ih
        rw [hexp]
        nlinarith [hmul, hge]
    intro i
    have hile : (i : ℕ) ≤ d := by have := i.2; omega
    simp only [gWeight]
    have hexp3 : d + 1 - d = 1 := by omega
    rw [hexp3, pow_one]
    -- goal: q + (q - 1)*d ≤ q ^ (d+1-i) + (q - 1)*i
    have he := hpow (d - (i : ℕ))
    have hexp2 : d - (i : ℕ) + 1 = d + 1 - (i : ℕ) := by omega
    rw [hexp2] at he
    have hsum : (q - 1) * (i : ℕ) + (q - 1) * (d - (i : ℕ)) = (q - 1) * d := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  -- lower bound: g_jv + (q - 1)*g_d ≤ ∑ g_i r_i
  have hrjv_le : r jrow ≤ q := by
    rw [← hrsum]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ jrow)
  have hlb : gWeight q d jv + (q - 1) * gWeight q d d
      ≤ ∑ i : Fin (d + 1), gWeight q d (i : ℕ) * r i := by
    -- pointwise: g_i r_i ≥ g_d r_i. Isolate the jrow term
    have hsplit : (∑ i : Fin (d + 1), gWeight q d (i : ℕ) * r i)
        = gWeight q d jv * r jrow + ∑ i ∈ Finset.univ.erase jrow, gWeight q d (i : ℕ) * r i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ jrow)]
      rw [hjv]; ring
    have hrest : gWeight q d d * ∑ i ∈ Finset.univ.erase jrow, r i
        ≤ ∑ i ∈ Finset.univ.erase jrow, gWeight q d (i : ℕ) * r i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right _ (hgmin i)
    have hsumrest : ∑ i ∈ Finset.univ.erase jrow, r i = q - r jrow := by
      have hh := Finset.sum_erase_add (Finset.univ) r (Finset.mem_univ jrow)
      rw [hrsum] at hh
      omega
    have hgd_le_gjv : gWeight q d d ≤ gWeight q d jv := by
      have hh := hgmin jrow; rw [← hjv] at hh; exact hh
    -- g_jv * r_jrow + g_d * (q - r_jrow) ≥ g_jv + (q - 1)*g_d
    have hkey2 : gWeight q d jv + (q - 1) * gWeight q d d
        ≤ gWeight q d jv * r jrow + gWeight q d d * (q - r jrow) := by
      obtain ⟨s, hs⟩ : ∃ s, r jrow = 1 + s := ⟨r jrow - 1, by omega⟩
      have hsle : s ≤ q - 1 := by omega
      have hsmul : gWeight q d d * s ≤ gWeight q d jv * s := Nat.mul_le_mul_right _ hgd_le_gjv
      rw [hs]
      have hqs : q - (1 + s) = (q - 1) - s := by omega
      rw [hqs]
      have hexpand1 : gWeight q d jv * (1 + s) = gWeight q d jv + gWeight q d jv * s := by ring
      have hexpand2 : gWeight q d d * ((q - 1) - s) + gWeight q d d * s
          = gWeight q d d * (q - 1) := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [hexpand1]
      -- goal: g_jv + (q - 1)g_d ≤ g_jv + g_jv*s + g_d*((q - 1)-s)
      have hgd_q1 : (q - 1) * gWeight q d d = gWeight q d d * (q - 1) := by ring
      omega
    rw [hsplit]
    -- hrest : g_d * (∑_{erase} r) ≤ ∑_{erase} g_i r_i.
    -- hsumrest : ∑_{erase} r = q - r jrow
    rw [hsumrest] at hrest
    -- hrest : g_d * (q - r jrow) ≤ ∑_{erase} g_i r_i. hkey2 gives the bound
    omega
  -- the exchange identity
  have hgex := gWeight_exchange_pos q d jv hq2 hjd
  -- Now assemble: Φ kk' < Φ kk
  have hPhilt : q ^ (d + 1) * ∑ i : Fin (d + 1), kk' i
        + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk' i
      < q ^ (d + 1) * ∑ i : Fin (d + 1), kk i
        + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk i := by
    rw [hPhiEq kk', hPhiEq kk]
    -- from hbal : Φ' + S = Φ + T, with S = q ^ m ∑ g r, T = q ^ m (q g_{jv+1})
    rw [hsumr, hwjj] at hbal
    -- hbal : Φ' + q ^ m ∑ g r = Φ + q ^ m (q g_{jv+1})
    -- lower bound on ∑ g r
    have hmono : q ^ m * (gWeight q d jv + (q - 1) * gWeight q d d)
        ≤ q ^ m * ∑ i : Fin (d + 1), gWeight q d (i : ℕ) * r i :=
      Nat.mul_le_mul_left _ hlb
    have hqmpos : 0 < q ^ m := pow_pos (by omega) m
    have hdpos : 0 < (q - 1) ^ 2 * (d - jv) := by
      have : 0 < q - 1 := by omega
      have : 0 < d - jv := by omega
      positivity
    -- g_jv + (q - 1) g_d = q*g_{jv+1} + (q - 1) ^ 2(d-jv)
    nlinarith [hbal, hmono, hgex, hqmpos, hdpos,
      Nat.mul_le_mul_left (q ^ m) hlb]
  -- representation preserved
  have hk : (∑ i : Fin (d + 1), kk i * q ^ (i : ℕ))
      = (∑ i : Fin (d + 1), kk' i * q ^ (i : ℕ)) := by
    have := repr_preserved q d m hq1 kk r jj jv hjjval hjm hrdig hr0 hrsum
    rw [← this]
    apply Finset.sum_congr rfl
    intro i _
    rw [hkk' i]
  exact F_lt_of_Phi_lt q d k hq2 kk kk' hk hPhilt

/-- **Carry-exchange improvement.** If an admissible `kk` has a *shifted carry* at
some column `m` (shifted column sum `∑_i a_{i,m-i} ≥ q`), there is an admissible
`kk'` with strictly larger `F`: remove `q` stones from `Col_m`, add one at
`(j+1, m-j)` for `j < d` the maximal occupied non-top row
(informal.tex `lem:H1-carry-elimination`). -/
lemma carry_exchange_improves (q d k : ℕ) (hq : q.Prime) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk) (m : ℕ)
    (hcarry : q ≤ ∑ i : Fin (d + 1),
        (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0)) :
    ∃ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' ∧ F q d kk < F q d kk' := by
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hq2 : 2 ≤ q := hq.two_le
  obtain ⟨hrep, hcf⟩ := hadm
  -- diagonal counts
  set a : Fin (d + 1) → ℕ := fun i =>
    if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0 with ha
  -- STEP A: choose exactly q stones from the top
  obtain ⟨r, hrle, hrsum, _Jdummy⟩ := row_take_top d a q hq1 hcarry
  -- r i ≤ digit; r i = 0 for i > m
  have hrdig : ∀ i : Fin (d + 1), r i ≤ digit q (kk i) (m - (i : ℕ)) := by
    intro i
    have := hrle i
    rw [ha] at this
    by_cases hi : (i : ℕ) ≤ m
    · simpa [hi] using this
    · simp only [hi, if_false] at this; omega
  have hr0 : ∀ i : Fin (d + 1), m < (i : ℕ) → r i = 0 := by
    intro i hi
    have := hrle i
    rw [ha] at this
    simp only [Nat.not_le.mpr hi, if_false] at this; omega
  -- top row r ≤ q-1
  have hrlast : r (Fin.last d) ≤ q - 1 := by
    have := hrdig (Fin.last d)
    have hd := digit_le q (kk (Fin.last d)) (m - (Fin.last d : ℕ)) hq1
    omega
  -- STEP A': maximal removed non-top row j < d
  obtain ⟨jrow, hjd, hjpos, hjtop⟩ := row_select_j q d hq2 r hrsum hrlast
  set jv : ℕ := (jrow : ℕ) with hjv
  -- jj := j+1 as a Fin (d + 1)
  have hjjlt : jv + 1 < d + 1 := by omega
  set jj : Fin (d + 1) := ⟨jv + 1, hjjlt⟩ with hjjdef
  have hjjval : (jj : ℕ) = jv + 1 := rfl
  -- j ≤ m (since row j is occupied on the diagonal)
  have hjm : jv ≤ m := by
    by_contra hc
    push Not at hc
    have := hr0 jrow (by rw [← hjv]; exact hc)
    omega
  -- STEP B: the exchanged tuple
  set kk' : Fin (d + 1) → ℕ :=
    fun i => kk i - r i * q ^ (m - (i : ℕ)) + (if i = jj then q ^ (m - jv) else 0) with hkk'
  refine ⟨kk', ⟨?_, ?_⟩, ?_⟩
  · -- representation
    rw [hrep]
    simp only [hkk']
    exact (repr_preserved q d m hq1 kk r jj jv hjjval hjm hrdig hr0 hrsum).symm
  · -- carry-free preservation
    exact exchange_carryfree q d m hq2 kk hcf r jrow jj jv hjv hjjval hjm hrdig hr0 hjpos kk'
      (fun i => by rw [hkk'])
  · -- strict F-increase
    exact exchange_phi_gain q d k m hq2 kk hrep r jrow jj jv hjv hjjval hjm hjd hrdig hr0 hrsum
      hjpos hjtop kk' (fun i => by rw [hkk'])

/-- **Carry elimination.** An admissible `F`-maximizer has no shifted carries: for
every `m`, `∑_i a_{i,m-i} ≤ q-1`. Otherwise `carry_exchange_improves` would give an
admissible tuple with strictly larger `F` (informal.tex `lem:H1-carry-elimination`). -/
lemma carry_elimination (q d k : ℕ) (hq : q.Prime) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk)
    (hmax : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk) :
    ∀ m : ℕ, (∑ i : Fin (d + 1),
        (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0)) ≤ q - 1 := by
  intro m
  by_contra hbig
  -- `hbig : ¬ (∑ … ≤ q - 1)`, i.e. the shifted column sum is `≥ q` (since q ≥ 1).
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hcarry : q ≤ ∑ i : Fin (d + 1),
      (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0) := by
    omega
  obtain ⟨kk', hadm', hlt⟩ := carry_exchange_improves q d k hq kk hadm m hcarry
  exact absurd (hmax kk' hadm') (not_le.mpr hlt)

/-- Two naturals with all base-`q` digits equal to `0` are `0` (`q ≥ 2`). -/
theorem digit_zero (q : ℕ) (hq : 2 ≤ q) : ∀ y : ℕ, (∀ n, digit q y n = 0) → y = 0 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro h
    have h0 := h 0
    simp only [digit, pow_zero, Nat.div_one] at h0
    have hrec : ∀ n, digit q (y / q) n = 0 := by
      intro n
      have hh := h (n + 1)
      simp only [digit, pow_succ] at hh
      rw [show q ^ n * q = q * q ^ n by ring, ← Nat.div_div_eq_div_mul] at hh
      simpa [digit] using hh
    by_cases hy : y = 0
    · exact hy
    · have hyq : y / q < y := Nat.div_lt_self (by omega) hq
      have := ih (y / q) hyq hrec
      have hh := Nat.div_add_mod y q
      rw [this] at hh
      omega

/-- Two naturals with all equal base-`q` digits are equal (`q ≥ 2`). -/
theorem digit_ext (q : ℕ) (hq : 2 ≤ q) : ∀ x y : ℕ, (∀ n, digit q x n = digit q y n) → x = y := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y h
    have h0 := h 0
    simp only [digit, pow_zero, Nat.div_one] at h0
    have hq0 : 0 < q := by omega
    have hrec : ∀ n, digit q (x / q) n = digit q (y / q) n := by
      intro n
      have hh := h (n + 1)
      simp only [digit, pow_succ] at hh
      rw [show q ^ n * q = q * q ^ n by ring, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul] at hh
      simpa [digit] using hh
    by_cases hx : x = 0
    · subst hx
      have hyq : y / q = 0 := by
        apply digit_zero q hq (y / q)
        intro n
        have := hrec n
        simp only [Nat.zero_div, digit, Nat.zero_div, Nat.zero_mod] at this ⊢
        omega
      have hh := Nat.div_add_mod y q
      rw [hyq] at hh
      simp only [Nat.mul_zero, Nat.zero_add] at hh
      simp only [Nat.zero_mod] at h0
      omega
    · have hxq : x / q < x := Nat.div_lt_self (by omega) hq
      have hkey := ih (x / q) hxq (y / q) hrec
      have hx2 := Nat.div_add_mod x q
      have hy2 := Nat.div_add_mod y q
      rw [hkey] at hx2
      omega

/-- The potential `Φ(kk) = q ^ {d+1}·∑ᵢ kkᵢ + (q - 1)·∑ᵢ i·qⁱ·kkᵢ` (matches the form used by
`F_lt_of_Phi_lt`). Minimizing `Φ` over equal-representation admissible tuples is equivalent
to maximizing `F`. -/
def Phi (q d : ℕ) (kk : Fin (d + 1) → ℕ) : ℕ :=
  q ^ (d + 1) * (∑ i : Fin (d + 1), kk i)
    + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk i

/-- **`g` is strictly decreasing in the row index** (for `q ≥ 2`): the stone weight
`gWeight q d i = q ^ {d+1-i} + (q - 1)·i` strictly decreases as `i` increases within
`0..d` (informal.tex `eq:g-decreasing-H1`). -/
lemma gWeight_anti (q d i j : ℕ) (hq : 2 ≤ q) (hij : i < j) (hjd : j ≤ d) :
    gWeight q d j < gWeight q d i := by
  -- Single downward step: for e < d, g_{e+1} < g_e.
  have step : ∀ e : ℕ, e < d → gWeight q d (e + 1) < gWeight q d e := by
    intro e he
    unfold gWeight
    have he1 : d + 1 - e = (d - e) + 1 := by omega
    have he2 : d + 1 - (e + 1) = d - e := by omega
    rw [he1, he2, pow_succ]
    -- Need: q ^ (d-e) + (q - 1)*(e + 1) < q ^ (d-e)*q + (q - 1)*e
    have hb : 2 ≤ q ^ (d - e) := by
      calc 2 ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (d - e) := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    have hp1 : p + 2 - 1 = p + 1 := by omega
    rw [hp1]
    nlinarith [hb]
  -- Chain from i to j using strong induction on the gap.
  have chain : ∀ n : ℕ, ∀ e : ℕ, e + n ≤ d → 0 < n →
      gWeight q d (e + n) < gWeight q d e := by
    intro n
    induction n with
    | zero => omega
    | succ m ih =>
      intro e hle hpos
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : e + (0 + 1) = e + 1 := by omega
        rw [this]
        exact step e (by omega)
      · have h1 : gWeight q d (e + (m + 1)) < gWeight q d (e + m) := by
          have hlt : e + m < d := by omega
          have hs := step (e + m) hlt
          have heq : e + m + 1 = e + (m + 1) := by omega
          rw [heq] at hs
          exact hs
        have h2 : gWeight q d (e + m) < gWeight q d e := ih e (by omega) hm
        exact lt_trans h1 h2
  have hj : j = i + (j - i) := by omega
  rw [hj]
  exact chain (j - i) i (by omega) (by omega)

/-- **Single downward move within a column.** Move one stone from cell `(i, m-i)` down
to cell `(j, m-j)` (same column, rows `i < j ≤ d`), when the source cell is occupied
and the target diagonal `m-j` has slack (`≤ q-2` stones). The result is admissible
and has strictly smaller `Φ` (by `q ^ m (g_j - g_i) < 0`). -/
lemma move_down (q d k m i j : ℕ) (hq : 2 ≤ q) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk)
    (hi : i ≤ m) (hj : j ≤ m) (hjd : j ≤ d) (hij : i < j)
    (hsrc : 1 ≤ digit q (kk ⟨i, by omega⟩) (m - i))
    (hslack : (∑ r : Fin (d + 1), digit q (kk r) (m - j)) ≤ q - 2) :
    ∃ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' ∧ Phi q d kk' < Phi q d kk := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨hrep, hcf⟩ := hadm
  -- the two distinct indices
  set I : Fin (d + 1) := ⟨i, by omega⟩ with hI
  set J : Fin (d + 1) := ⟨j, by omega⟩ with hJ
  have hIval : (I : ℕ) = i := rfl
  have hJval : (J : ℕ) = j := rfl
  have hIJ : I ≠ J := by
    intro h; apply absurd (congrArg (Fin.val) h); rw [hIval, hJval]; omega
  -- no-borrow at I
  have hborrow : q ^ (m - i) ≤ kk I := by
    calc q ^ (m - i) = 1 * q ^ (m - i) := (one_mul _).symm
      _ ≤ digit q (kk I) (m - i) * q ^ (m - i) := Nat.mul_le_mul_right _ hsrc
      _ ≤ kk I := digit_place_le _ _ _
  -- the new tuple
  set kk' : Fin (d + 1) → ℕ :=
    fun r => kk r - (if r = I then q ^ (m - i) else 0) + (if r = J then q ^ (m - j) else 0)
    with hkk'def
  -- pointwise characterization
  have hkkI : kk' I = kk I - q ^ (m - i) := by
    simp only [hkk'def, if_neg hIJ, add_zero, if_true]
  have hkkJ : kk' J = kk J + q ^ (m - j) := by
    simp only [hkk'def, if_neg (Ne.symm hIJ), tsub_zero, if_true]
  have hkkO : ∀ r : Fin (d + 1), r ≠ I → r ≠ J → kk' r = kk r := by
    intro r hrI hrJ
    simp only [hkk'def, if_neg hrI, if_neg hrJ, tsub_zero, add_zero]
  -- m - i ≠ m - j
  have hmimj : m - i ≠ m - j := by omega
  -- precondition for the addition at J
  have hJdig : digit q (kk J) (m - j) ≤ q - 2 := by
    have hle : digit q (kk J) (m - j) ≤ ∑ r : Fin (d + 1), digit q (kk r) (m - j) :=
      Finset.single_le_sum (f := fun r => digit q (kk r) (m - j))
        (fun r _ => Nat.zero_le _) (Finset.mem_univ J)
    omega
  have hJadd : digit q (kk J) (m - j) + 1 < q := by omega
  -- digit of kk' at each row/position
  -- weight per row in Φ
  set w : Fin (d + 1) → ℕ := fun r => q ^ (d + 1) + (q - 1) * ((r : ℕ) * q ^ (r : ℕ)) with hw
  refine ⟨kk', ⟨?_, ?_⟩, ?_⟩
  · -- representation
    rw [hrep]
    -- ∑ kk' r * q ^ r = ∑ kk r * q ^ r
    -- pull out I and J
    have hsubset : ({I, J} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_sdiff hsubset (f := fun r => kk' r * q ^ (r : ℕ)),
        ← Finset.sum_sdiff hsubset (f := fun r => kk r * q ^ (r : ℕ))]
    -- the I,J powers cancel: q ^ (m-i)*q ^ i = q ^ m = q ^ (m-j)*q ^ j
    have hpi : q ^ (m - i) * q ^ i = q ^ m := by rw [← pow_add]; congr 1; omega
    have hpj : q ^ (m - j) * q ^ j = q ^ m := by rw [← pow_add]; congr 1; omega
    have hrest : (∑ r ∈ Finset.univ \ {I, J}, kk' r * q ^ (r : ℕ))
        = ∑ r ∈ Finset.univ \ {I, J}, kk r * q ^ (r : ℕ) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hr
      rw [hkkO r hr.1 hr.2]
    rw [hrest]
    apply Nat.add_left_cancel (n := q ^ m)
    -- LHS: q ^ m + ∑_{IJ} kk' * q ^ r. RHS: q ^ m + ∑_{IJ} kk * q ^ r
    rw [Finset.sum_pair hIJ, Finset.sum_pair hIJ, hkkI, hkkJ, hIval, hJval]
    rw [Nat.sub_mul, Nat.add_mul, hpi, hpj]
    -- (kk I * q ^ i - q ^ m) + (kk J * q ^ j + q ^ m): need q ^ m ≤ kk I * q ^ i
    have hbi : q ^ m ≤ kk I * q ^ i := by
      calc q ^ m = q ^ (m - i) * q ^ i := hpi.symm
        _ ≤ kk I * q ^ i := Nat.mul_le_mul_right _ hborrow
    omega
  · -- carry-free
    intro n
    by_cases hnj : n = m - j
    · -- the addition position: sum increases by 1 at J, unchanged at I, ≤ (q-2)+1 = q-1
      subst hnj
      -- digit at J: +1
      have hdJ : digit q (kk' J) (m - j) = digit q (kk J) (m - j) + 1 := by
        rw [hkkJ]; exact digit_add_self q (kk J) (m - j) hq1 hJadd
      -- digit at I: unchanged (since m-i ≠ m-j)
      have hdI : digit q (kk' I) (m - j) = digit q (kk I) (m - j) := by
        rw [hkkI]
        have : kk I - q ^ (m - i) = kk I - 1 * q ^ (m - i) := by rw [one_mul]
        rw [this]
        exact digit_sub_other q (kk I) (m - i) 1 (m - j) hq1 (by omega) (Ne.symm hmimj)
      -- now split off {I, J}
      have hsubset : ({I, J} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_sdiff hsubset (f := fun r => digit q (kk' r) (m - j))]
      have hrest : (∑ r ∈ Finset.univ \ {I, J}, digit q (kk' r) (m - j))
          = ∑ r ∈ Finset.univ \ {I, J}, digit q (kk r) (m - j) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hr
        rw [hkkO r hr.1 hr.2]
      rw [hrest, Finset.sum_pair hIJ, hdI, hdJ]
      -- compare with the original full sum
      have horig : (∑ r ∈ Finset.univ \ {I, J}, digit q (kk r) (m - j))
          + (digit q (kk I) (m - j) + digit q (kk J) (m - j))
          = ∑ r : Fin (d + 1), digit q (kk r) (m - j) := by
        rw [← Finset.sum_pair hIJ (f := fun r => digit q (kk r) (m - j))]
        exact Finset.sum_sdiff hsubset
      have hsum := hcf (m - j)
      omega
    · -- other positions: sum does not increase
      have hle : ∀ r : Fin (d + 1), digit q (kk' r) n ≤ digit q (kk r) n := by
        intro r
        by_cases hrI : r = I
        · subst hrI
          rw [hkkI]
          by_cases hni : n = m - i
          · subst hni
            have : kk I - q ^ (m - i) = kk I - 1 * q ^ (m - i) := by rw [one_mul]
            rw [this, digit_sub_self q (kk I) (m - i) 1 hq1 (by omega)]
            omega
          · have : kk I - q ^ (m - i) = kk I - 1 * q ^ (m - i) := by rw [one_mul]
            rw [this, digit_sub_other q (kk I) (m - i) 1 n hq1 (by omega) hni]
        · by_cases hrJ : r = J
          · subst hrJ
            rw [hkkJ, digit_add_other q (kk J) (m - j) n hq1 hJadd hnj]
          · rw [hkkO r hrI hrJ]
      calc (∑ r : Fin (d + 1), digit q (kk' r) n)
          ≤ ∑ r : Fin (d + 1), digit q (kk r) n := Finset.sum_le_sum (fun r _ => hle r)
        _ ≤ q - 1 := hcf n
  · -- Phi q d kk' < Phi q d kk
    -- Φ written as ∑ w_r tt_r
    have hPhiEq : ∀ tt : Fin (d + 1) → ℕ,
        q ^ (d + 1) * ∑ r : Fin (d + 1), tt r
          + (q - 1) * ∑ r : Fin (d + 1), (r : ℕ) * q ^ (r : ℕ) * tt r
        = ∑ r : Fin (d + 1), w r * tt r := by
      intro tt
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      simp only [hw]
      ring
    -- the identity w r * q ^ (m-r) = q ^ m * gWeight q d r for (r:ℕ) ≤ m
    have hwq : ∀ r : Fin (d + 1), (r : ℕ) ≤ m →
        w r * q ^ (m - (r : ℕ)) = q ^ m * gWeight q d (r : ℕ) := by
      intro r hr
      simp only [hw, gWeight]
      have h1 : q ^ (d + 1) * q ^ (m - (r : ℕ)) = q ^ m * q ^ (d + 1 - (r : ℕ)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have hpp : q ^ (r : ℕ) * q ^ (m - (r : ℕ)) = q ^ m := by
        rw [← pow_add]; congr 1; omega
      calc (q ^ (d + 1) + (q - 1) * ((r : ℕ) * q ^ (r : ℕ))) * q ^ (m - (r : ℕ))
          = q ^ (d + 1) * q ^ (m - (r : ℕ))
            + (q - 1) * (r : ℕ) * (q ^ (r : ℕ) * q ^ (m - (r : ℕ))) := by ring
        _ = q ^ m * q ^ (d + 1 - (r : ℕ)) + (q - 1) * (r : ℕ) * q ^ m := by rw [h1, hpp]
        _ = q ^ m * (q ^ (d + 1 - (r : ℕ)) + (q - 1) * (r : ℕ)) := by ring
    -- the balance identity (in ℕ):  Φ' + w I * q ^ (m-i) = Φ + w J * q ^ (m-j)
    have hbal : (∑ r : Fin (d + 1), w r * kk' r) + w I * q ^ (m - i)
        = (∑ r : Fin (d + 1), w r * kk r) + w J * q ^ (m - j) := by
      have hsubset : ({I, J} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_sdiff hsubset (f := fun r => w r * kk' r),
          ← Finset.sum_sdiff hsubset (f := fun r => w r * kk r)]
      have hrest : (∑ r ∈ Finset.univ \ {I, J}, w r * kk' r)
          = ∑ r ∈ Finset.univ \ {I, J}, w r * kk r := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hr
        rw [hkkO r hr.1 hr.2]
      rw [hrest, Finset.sum_pair hIJ, Finset.sum_pair hIJ, hkkI, hkkJ]
      -- w I * (kk I - q ^ (m-i)) + w J * (kk J + q ^ (m-j)) + w I * q ^ (m-i)
      --   = w I * kk I + w J * kk J + w J * q ^ (m-j)
      have hwle : w I * q ^ (m - i) ≤ w I * kk I := Nat.mul_le_mul_left _ hborrow
      rw [Nat.mul_sub, Nat.mul_add]
      omega
    -- w I * q ^ (m-i) = q ^ m * g_i,  w J * q ^ (m-j) = q ^ m * g_j
    have hwI : w I * q ^ (m - i) = q ^ m * gWeight q d i := by
      have := hwq I (by rw [hIval]; exact hi); rw [hIval] at this; exact this
    have hwJ : w J * q ^ (m - j) = q ^ m * gWeight q d j := by
      have := hwq J (by rw [hJval]; exact hj); rw [hJval] at this; exact this
    -- g_j < g_i
    have hganti : gWeight q d j < gWeight q d i := gWeight_anti q d i j hq hij hjd
    have hqmpos : 0 < q ^ m := pow_pos (by omega) m
    have hstrict : w J * q ^ (m - j) < w I * q ^ (m - i) := by
      rw [hwI, hwJ]; exact (Nat.mul_lt_mul_left hqmpos).2 hganti
    -- conclude via Phi unfolding
    change Phi q d kk' < Phi q d kk
    unfold Phi
    rw [hPhiEq kk', hPhiEq kk]
    omega

lemma move_parallelogram_representation (q d k m i j t : ℕ)
    (kk kk' : Fin (d + 1) → ℕ) (I J IT JT : Fin (d + 1)) (hi : i ≤ m)
    (hj : j ≤ m) (hrep : k = ∑ r : Fin (d + 1), kk r * q ^ (r : ℕ))
    (hborrowP : q ^ (m - i) ≤ kk I) (hborrowS : q ^ (m - j) ≤ kk JT)
    (hIval : (I : ℕ) = i) (hJval : (J : ℕ) = j)
    (hITval : (IT : ℕ) = i + t) (hJTval : (JT : ℕ) = j + t) (hIJT : I ≠ JT)
    (hkk'def : kk' =
      fun r => kk r - (if r = I then q ^ (m - i) else 0)
        - (if r = JT then q ^ (m - j) else 0)
        + (if r = IT then q ^ (m - i) else 0) + (if r = J then q ^ (m - j) else 0)) :
    k = ∑ r : Fin (d + 1), kk' r * q ^ (r : ℕ) := by
  rw [hrep]
  have hPS : ∀ r : Fin (d + 1),
      (if r = I then q ^ (m - i) else 0) + (if r = JT then q ^ (m - j) else 0) ≤
        kk r := by
    intro r
    by_cases hrI : r = I
    · subst hrI; rw [if_pos rfl, if_neg hIJT, add_zero]; exact hborrowP
    · by_cases hrJT : r = JT
      · subst hrJT; rw [if_neg hIJT.symm, if_pos rfl, zero_add]; exact hborrowS
      · rw [if_neg hrI, if_neg hrJT]; exact Nat.zero_le _
  have hbal : (∑ r : Fin (d + 1), kk' r * q ^ (r : ℕ))
        + ∑ r : Fin (d + 1), ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0)) * q ^ (r : ℕ)
      = (∑ r : Fin (d + 1), kk r * q ^ (r : ℕ))
        + ∑ r : Fin (d + 1), ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0)) * q ^ (r : ℕ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hkk'def]
    have hps := hPS r
    set P := (if r = I then q ^ (m - i) else 0) with hP
    set S := (if r = JT then q ^ (m - j) else 0) with hS
    set Q := (if r = IT then q ^ (m - i) else 0) with hQ
    set R := (if r = J then q ^ (m - j) else 0) with hR
    have hsub : kk r - P - S + Q + R = kk r - (P + S) + (Q + R) := by omega
    rw [hsub]
    have e1 : (kk r - (P + S) + (Q + R)) * q ^ (r : ℕ)
        = (kk r - (P + S)) * q ^ (r : ℕ) + (Q + R) * q ^ (r : ℕ) := by
      rw [Nat.add_mul]
    have e2 : (kk r - (P + S)) * q ^ (r : ℕ)
        = kk r * q ^ (r : ℕ) - (P + S) * q ^ (r : ℕ) := by
      rw [Nat.sub_mul]
    rw [e1, e2]
    have hle : (P + S) * q ^ (r : ℕ) ≤ kk r * q ^ (r : ℕ) :=
      Nat.mul_le_mul_right _ hps
    omega
  have hsumI :
      (∑ r : Fin (d + 1), (if r = I then q ^ (m - i) else 0) * q ^ (r : ℕ)) =
        q ^ m := by
    rw [Finset.sum_eq_single I]
    · rw [if_pos rfl, hIval, ← pow_add]; congr 1; omega
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsumJT :
      (∑ r : Fin (d + 1), (if r = JT then q ^ (m - j) else 0) * q ^ (r : ℕ)) =
        q ^ (m + t) := by
    rw [Finset.sum_eq_single JT]
    · rw [if_pos rfl, hJTval, ← pow_add]; congr 1; omega
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsumIT :
      (∑ r : Fin (d + 1), (if r = IT then q ^ (m - i) else 0) * q ^ (r : ℕ)) =
        q ^ (m + t) := by
    rw [Finset.sum_eq_single IT]
    · rw [if_pos rfl, hITval, ← pow_add]; congr 1; omega
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsumJ :
      (∑ r : Fin (d + 1), (if r = J then q ^ (m - j) else 0) * q ^ (r : ℕ)) =
        q ^ m := by
    rw [Finset.sum_eq_single J]
    · rw [if_pos rfl, hJval, ← pow_add]; congr 1; omega
    · intro b _ hb; rw [if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hL : (∑ r : Fin (d + 1), ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0)) * q ^ (r : ℕ)) =
      q ^ m + q ^ (m + t) := by
    rw [show (∑ r : Fin (d + 1), ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0)) * q ^ (r : ℕ))
          = (∑ r : Fin (d + 1), (if r = I then q ^ (m - i) else 0) * q ^ (r : ℕ))
            + ∑ r : Fin (d + 1),
                (if r = JT then q ^ (m - j) else 0) * q ^ (r : ℕ) from by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            rw [Nat.add_mul]]
    rw [hsumI, hsumJT]
  have hRR : (∑ r : Fin (d + 1), ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0)) * q ^ (r : ℕ)) =
      q ^ (m + t) + q ^ m := by
    rw [show (∑ r : Fin (d + 1), ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0)) * q ^ (r : ℕ))
          = (∑ r : Fin (d + 1), (if r = IT then q ^ (m - i) else 0) * q ^ (r : ℕ))
            + ∑ r : Fin (d + 1),
                (if r = J then q ^ (m - j) else 0) * q ^ (r : ℕ) from by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            rw [Nat.add_mul]]
    rw [hsumIT, hsumJ]
  rw [hL, hRR] at hbal
  omega

lemma move_parallelogram_carry_free (q d m i j t : ℕ)
    (kk kk' : Fin (d + 1) → ℕ) (I J IT JT : Fin (d + 1)) (hq1 : 1 ≤ q)
    (hcf : CarryFree q d kk) (hsrcP : 1 ≤ digit q (kk I) (m - i))
    (hsrcS : 1 ≤ digit q (kk JT) (m - j)) (hJval : (J : ℕ) = j)
    (hITval : (IT : ℕ) = i + t)
    (hJTval : (JT : ℕ) = j + t) (hIJ : I ≠ J) (hIIT : I ≠ IT) (hIJT : I ≠ JT)
    (hJJT : J ≠ JT) (hITJT : IT ≠ JT) (hmimj : m - i ≠ m - j)
    (hkk'def : kk' =
      fun r => kk r - (if r = I then q ^ (m - i) else 0)
        - (if r = JT then q ^ (m - j) else 0)
        + (if r = IT then q ^ (m - i) else 0) + (if r = J then q ^ (m - j) else 0))
    (hkkI : kk' I = kk I - q ^ (m - i))
    (hkkJT : kk' JT = kk JT - q ^ (m - j)) :
    CarryFree q d kk' := by
  have hcfI : ∀ r : Fin (d + 1), r ≠ I → digit q (kk r) (m - i) + 1 < q := by
    intro r hr
    have hsum := hcf (m - i)
    have hpair : digit q (kk r) (m - i) + digit q (kk I) (m - i)
        ≤ ∑ s : Fin (d + 1), digit q (kk s) (m - i) := by
      have hsub : ({r, I} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset (f := fun s => digit q (kk s) (m - i)) hsub
      rwa [Finset.sum_pair hr] at this
    omega
  have hcfJ : ∀ r : Fin (d + 1), r ≠ JT → digit q (kk r) (m - j) + 1 < q := by
    intro r hr
    have hsum := hcf (m - j)
    have hpair : digit q (kk r) (m - j) + digit q (kk JT) (m - j)
        ≤ ∑ s : Fin (d + 1), digit q (kk s) (m - j) := by
      have hsub : ({r, JT} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset (f := fun s => digit q (kk s) (m - j)) hsub
      rwa [Finset.sum_pair hr] at this
    omega
  have hdigI : ∀ n : ℕ, digit q (kk' I) n =
      if n = m - i then digit q (kk I) n - 1 else digit q (kk I) n := by
    intro n
    rw [hkkI]
    have h1 : kk I - q ^ (m - i) = kk I - 1 * q ^ (m - i) := by rw [one_mul]
    rw [h1]
    by_cases hn : n = m - i
    · subst hn; rw [if_pos rfl, digit_sub_self q (kk I) (m - i) 1 hq1 (by omega)]
    · rw [if_neg hn, digit_sub_other q (kk I) (m - i) 1 n hq1 (by omega) hn]
  have hdigJT : ∀ n : ℕ, digit q (kk' JT) n =
      if n = m - j then digit q (kk JT) n - 1 else digit q (kk JT) n := by
    intro n
    rw [hkkJT]
    have h1 : kk JT - q ^ (m - j) = kk JT - 1 * q ^ (m - j) := by rw [one_mul]
    rw [h1]
    by_cases hn : n = m - j
    · subst hn; rw [if_pos rfl, digit_sub_self q (kk JT) (m - j) 1 hq1 (by omega)]
    · rw [if_neg hn, digit_sub_other q (kk JT) (m - j) 1 n hq1 (by omega) hn]
  by_cases hcol : i + t = j
  · have hITJ : IT = J := by apply Fin.ext; rw [hITval, hJval]; omega
    have hkkJcol : kk' J = kk J + q ^ (m - i) + q ^ (m - j) := by
      have e : kk' J = kk J - (if J = I then q ^ (m - i) else 0)
            - (if J = JT then q ^ (m - j) else 0)
            + (if J = IT then q ^ (m - i) else 0) + (if J = J then q ^ (m - j) else 0) :=
        by rw [hkk'def]
      rw [e, if_neg hIJ.symm, if_neg hJJT, if_pos hITJ.symm, if_pos rfl,
        Nat.sub_zero, Nat.sub_zero]
    have hdigJ : ∀ n : ℕ, digit q (kk' J) n =
        if n = m - i then digit q (kk J) n + 1
        else if n = m - j then digit q (kk J) n + 1 else digit q (kk J) n := by
      intro n
      rw [hkkJcol]
      have hpre_i : digit q (kk J) (m - i) + 1 < q :=
        hcfI J (by rw [← hITJ]; exact hIIT.symm)
      have hpre_j : digit q (kk J) (m - j) + 1 < q := hcfJ J hJJT
      have hmid_j : digit q (kk J + q ^ (m - i)) (m - j) + 1 < q := by
        rw [digit_add_other q (kk J) (m - i) (m - j) hq1 hpre_i hmimj.symm]
        exact hpre_j
      by_cases hni : n = m - i
      · subst hni
        rw [if_pos rfl, digit_add_other q (kk J + q ^ (m - i)) (m - j) (m - i)
          hq1 hmid_j hmimj, digit_add_self q (kk J) (m - i) hq1 hpre_i]
      · by_cases hnj : n = m - j
        · subst hnj
          rw [if_neg hni, if_pos rfl, digit_add_self q (kk J + q ^ (m - i)) (m - j)
            hq1 hmid_j, digit_add_other q (kk J) (m - i) (m - j) hq1 hpre_i hni]
        · rw [if_neg hni, if_neg hnj,
            digit_add_other q (kk J + q ^ (m - i)) (m - j) n hq1 hmid_j hnj,
            digit_add_other q (kk J) (m - i) n hq1 hpre_i hni]
    have hkkO : ∀ r : Fin (d + 1), r ≠ I → r ≠ J → r ≠ JT → kk' r = kk r := by
      intro r hrI hrJ hrJT
      have hrIT : r ≠ IT := by rw [hITJ]; exact hrJ
      simp only [hkk'def, if_neg hrI, if_neg hrJ, if_neg hrJT, if_neg hrIT,
        Nat.sub_zero, add_zero]
    intro n
    have h3sub : ({I, J, JT} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
    have heq : (∑ r : Fin (d + 1), digit q (kk' r) n) =
        ∑ r : Fin (d + 1), digit q (kk r) n := by
      rw [← Finset.sum_sdiff h3sub (f := fun r => digit q (kk' r) n),
          ← Finset.sum_sdiff h3sub (f := fun r => digit q (kk r) n)]
      have hrest : (∑ r ∈ Finset.univ \ {I, J, JT}, digit q (kk' r) n) =
          ∑ r ∈ Finset.univ \ {I, J, JT}, digit q (kk r) n := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hr
        rw [hkkO r hr.1 hr.2.1 hr.2.2]
      rw [hrest]
      congr 1
      rw [Finset.sum_insert (by simp [hIJ, hIJT]),
          Finset.sum_insert (by simp [hJJT]), Finset.sum_singleton,
          Finset.sum_insert (by simp [hIJ, hIJT]),
          Finset.sum_insert (by simp [hJJT]), Finset.sum_singleton]
      rw [hdigI n, hdigJ n, hdigJT n]
      by_cases hni : n = m - i
      · subst hni
        rw [if_pos rfl, if_pos rfl, if_neg hmimj]
        have hI1 : 1 ≤ digit q (kk I) (m - i) := hsrcP
        omega
      · by_cases hnj : n = m - j
        · subst hnj
          rw [if_neg hni, if_neg hni, if_pos rfl, if_pos rfl]
          have hJT1 : 1 ≤ digit q (kk JT) (m - j) := hsrcS
          omega
        · rw [if_neg hni, if_neg hni, if_neg hnj, if_neg hnj]
    rw [heq]; exact hcf n
  · have hITJ : IT ≠ J := by
      intro h
      have := congrArg Fin.val h
      simp [hITval, hJval] at this
      omega
    have hkkIT : kk' IT = kk IT + q ^ (m - i) := by
      have e : kk' IT = kk IT - (if IT = I then q ^ (m - i) else 0)
            - (if IT = JT then q ^ (m - j) else 0)
            + (if IT = IT then q ^ (m - i) else 0) + (if IT = J then q ^ (m - j) else 0) :=
        by rw [hkk'def]
      rw [e, if_neg hIIT.symm, if_neg hITJT, if_pos rfl, if_neg hITJ,
        Nat.sub_zero, Nat.sub_zero, add_zero]
    have hkkJ : kk' J = kk J + q ^ (m - j) := by
      have e : kk' J = kk J - (if J = I then q ^ (m - i) else 0)
            - (if J = JT then q ^ (m - j) else 0)
            + (if J = IT then q ^ (m - i) else 0) + (if J = J then q ^ (m - j) else 0) :=
        by rw [hkk'def]
      rw [e, if_neg hIJ.symm, if_neg hJJT, if_neg (Ne.symm hITJ), if_pos rfl,
        Nat.sub_zero, Nat.sub_zero, add_zero]
    have hdigIT : ∀ n : ℕ, digit q (kk' IT) n =
        if n = m - i then digit q (kk IT) n + 1 else digit q (kk IT) n := by
      intro n
      rw [hkkIT]
      have hpre : digit q (kk IT) (m - i) + 1 < q := hcfI IT hIIT.symm
      by_cases hn : n = m - i
      · subst hn; rw [if_pos rfl, digit_add_self q (kk IT) (m - i) hq1 hpre]
      · rw [if_neg hn, digit_add_other q (kk IT) (m - i) n hq1 hpre hn]
    have hdigJ : ∀ n : ℕ, digit q (kk' J) n =
        if n = m - j then digit q (kk J) n + 1 else digit q (kk J) n := by
      intro n
      rw [hkkJ]
      have hpre : digit q (kk J) (m - j) + 1 < q := hcfJ J hJJT
      by_cases hn : n = m - j
      · subst hn; rw [if_pos rfl, digit_add_self q (kk J) (m - j) hq1 hpre]
      · rw [if_neg hn, digit_add_other q (kk J) (m - j) n hq1 hpre hn]
    have hkkO : ∀ r : Fin (d + 1), r ≠ I → r ≠ J → r ≠ IT → r ≠ JT → kk' r = kk r := by
      intro r hrI hrJ hrIT hrJT
      simp only [hkk'def, if_neg hrI, if_neg hrJ, if_neg hrJT, if_neg hrIT,
        Nat.sub_zero, add_zero]
    intro n
    have h4sub : ({I, J, IT, JT} : Finset (Fin (d + 1))) ⊆ Finset.univ := Finset.subset_univ _
    have heq : (∑ r : Fin (d + 1), digit q (kk' r) n) =
        ∑ r : Fin (d + 1), digit q (kk r) n := by
      rw [← Finset.sum_sdiff h4sub (f := fun r => digit q (kk' r) n),
          ← Finset.sum_sdiff h4sub (f := fun r => digit q (kk r) n)]
      have hrest : (∑ r ∈ Finset.univ \ {I, J, IT, JT}, digit q (kk' r) n) =
          ∑ r ∈ Finset.univ \ {I, J, IT, JT}, digit q (kk r) n := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hr
        rw [hkkO r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2]
      rw [hrest]
      congr 1
      rw [Finset.sum_insert (by simp [hIJ, hIIT, hIJT]),
          Finset.sum_insert (by simp [hITJ.symm, hJJT]),
          Finset.sum_insert (by simp [hITJT]), Finset.sum_singleton,
          Finset.sum_insert (by simp [hIJ, hIIT, hIJT]),
          Finset.sum_insert (by simp [hITJ.symm, hJJT]),
          Finset.sum_insert (by simp [hITJT]), Finset.sum_singleton]
      rw [hdigI n, hdigJ n, hdigIT n, hdigJT n]
      by_cases hni : n = m - i
      · subst hni
        rw [if_pos rfl, if_neg hmimj, if_pos rfl, if_neg hmimj]
        have hI1 : 1 ≤ digit q (kk I) (m - i) := hsrcP
        omega
      · by_cases hnj : n = m - j
        · subst hnj
          rw [if_neg hni, if_pos rfl, if_neg hni, if_pos rfl]
          have hJT1 : 1 ≤ digit q (kk JT) (m - j) := hsrcS
          omega
        · rw [if_neg hni, if_neg hnj, if_neg hni, if_neg hnj]
    rw [heq]; exact hcf n

lemma move_parallelogram_phi_lt (q d m i j t : ℕ) (hq : 2 ≤ q)
    (kk kk' : Fin (d + 1) → ℕ) (I J IT JT : Fin (d + 1)) (hi : i ≤ m)
    (hj : j ≤ m) (hij : i < j) (ht : 1 ≤ t)
    (hborrowP : q ^ (m - i) ≤ kk I) (hborrowS : q ^ (m - j) ≤ kk JT)
    (hIval : (I : ℕ) = i) (hJval : (J : ℕ) = j)
    (hITval : (IT : ℕ) = i + t) (hJTval : (JT : ℕ) = j + t) (hIJT : I ≠ JT)
    (hkk'def : kk' =
      fun r => kk r - (if r = I then q ^ (m - i) else 0)
        - (if r = JT then q ^ (m - j) else 0)
        + (if r = IT then q ^ (m - i) else 0) + (if r = J then q ^ (m - j) else 0)) :
    Phi q d kk' < Phi q d kk := by
  set w : Fin (d + 1) → ℕ := fun r => q ^ (d + 1) + (q - 1) * ((r : ℕ) * q ^ (r : ℕ)) with hw
  have hPhiEq : ∀ tt : Fin (d + 1) → ℕ,
      q ^ (d + 1) * ∑ r : Fin (d + 1), tt r
        + (q - 1) * ∑ r : Fin (d + 1), (r : ℕ) * q ^ (r : ℕ) * tt r
      = ∑ r : Fin (d + 1), w r * tt r := by
    intro tt
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hw]; ring
  have hPS : ∀ r : Fin (d + 1),
      (if r = I then q ^ (m - i) else 0) + (if r = JT then q ^ (m - j) else 0) ≤
        kk r := by
    intro r
    by_cases hrI : r = I
    · subst hrI; rw [if_pos rfl, if_neg hIJT, add_zero]; exact hborrowP
    · by_cases hrJT : r = JT
      · subst hrJT; rw [if_neg hIJT.symm, if_pos rfl, zero_add]; exact hborrowS
      · rw [if_neg hrI, if_neg hrJT]; exact Nat.zero_le _
  have hbal : (∑ r : Fin (d + 1), w r * kk' r)
        + ∑ r : Fin (d + 1), w r * ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0))
      = (∑ r : Fin (d + 1), w r * kk r)
        + ∑ r : Fin (d + 1), w r * ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hkk'def]
    have hps := hPS r
    set P := (if r = I then q ^ (m - i) else 0) with hP
    set S := (if r = JT then q ^ (m - j) else 0) with hS
    set Q := (if r = IT then q ^ (m - i) else 0) with hQ
    set R := (if r = J then q ^ (m - j) else 0) with hR
    have hsub : kk r - P - S + Q + R = kk r - (P + S) + (Q + R) := by omega
    rw [hsub]
    have e1 : w r * (kk r - (P + S) + (Q + R)) =
        w r * (kk r - (P + S)) + w r * (Q + R) := by
      rw [Nat.mul_add]
    have e2 : w r * (kk r - (P + S)) = w r * kk r - w r * (P + S) := by
      rw [Nat.mul_sub]
    rw [e1, e2]
    have hle : w r * (P + S) ≤ w r * kk r := Nat.mul_le_mul_left _ hps
    omega
  have hswI : (∑ r : Fin (d + 1), w r * (if r = I then q ^ (m - i) else 0)) =
      w I * q ^ (m - i) := by
    rw [Finset.sum_eq_single I]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, Nat.mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hswJT : (∑ r : Fin (d + 1), w r * (if r = JT then q ^ (m - j) else 0)) =
      w JT * q ^ (m - j) := by
    rw [Finset.sum_eq_single JT]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, Nat.mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hswIT : (∑ r : Fin (d + 1), w r * (if r = IT then q ^ (m - i) else 0)) =
      w IT * q ^ (m - i) := by
    rw [Finset.sum_eq_single IT]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, Nat.mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hswJ : (∑ r : Fin (d + 1), w r * (if r = J then q ^ (m - j) else 0)) =
      w J * q ^ (m - j) := by
    rw [Finset.sum_eq_single J]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb, Nat.mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hLb : (∑ r : Fin (d + 1), w r * ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0))) =
      w I * q ^ (m - i) + w JT * q ^ (m - j) := by
    rw [show (∑ r : Fin (d + 1), w r * ((if r = I then q ^ (m - i) else 0)
            + (if r = JT then q ^ (m - j) else 0)))
          = (∑ r : Fin (d + 1), w r * (if r = I then q ^ (m - i) else 0))
            + ∑ r : Fin (d + 1), w r * (if r = JT then q ^ (m - j) else 0) from by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            rw [Nat.mul_add]]
    rw [hswI, hswJT]
  have hRb : (∑ r : Fin (d + 1), w r * ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0))) =
      w IT * q ^ (m - i) + w J * q ^ (m - j) := by
    rw [show (∑ r : Fin (d + 1), w r * ((if r = IT then q ^ (m - i) else 0)
            + (if r = J then q ^ (m - j) else 0)))
          = (∑ r : Fin (d + 1), w r * (if r = IT then q ^ (m - i) else 0))
            + ∑ r : Fin (d + 1), w r * (if r = J then q ^ (m - j) else 0) from by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r _
            rw [Nat.mul_add]]
    rw [hswIT, hswJ]
  rw [hLb, hRb] at hbal
  have hppi : q ^ i * q ^ (m - i) = q ^ m := by rw [← pow_add]; congr 1; omega
  have hppit : q ^ (i + t) * q ^ (m - i) = q ^ (m + t) := by
    rw [← pow_add]; congr 1; omega
  have hppj : q ^ j * q ^ (m - j) = q ^ m := by rw [← pow_add]; congr 1; omega
  have hppjt : q ^ (j + t) * q ^ (m - j) = q ^ (m + t) := by
    rw [← pow_add]; congr 1; omega
  have hwIv : w I * q ^ (m - i) =
      q ^ (d + 1) * q ^ (m - i) + (q - 1) * i * q ^ m := by
    simp only [hw, hIval]
    calc (q ^ (d + 1) + (q - 1) * (i * q ^ i)) * q ^ (m - i)
        = q ^ (d + 1) * q ^ (m - i) + (q - 1) * i * (q ^ i * q ^ (m - i)) := by ring
      _ = q ^ (d + 1) * q ^ (m - i) + (q - 1) * i * q ^ m := by rw [hppi]
  have hwITv : w IT * q ^ (m - i) =
      q ^ (d + 1) * q ^ (m - i) + (q - 1) * (i + t) * q ^ (m + t) := by
    simp only [hw, hITval]
    calc (q ^ (d + 1) + (q - 1) * ((i + t) * q ^ (i + t))) * q ^ (m - i)
        = q ^ (d + 1) * q ^ (m - i)
          + (q - 1) * (i + t) * (q ^ (i + t) * q ^ (m - i)) := by ring
      _ = q ^ (d + 1) * q ^ (m - i) + (q - 1) * (i + t) * q ^ (m + t) := by
        rw [hppit]
  have hwJv : w J * q ^ (m - j) =
      q ^ (d + 1) * q ^ (m - j) + (q - 1) * j * q ^ m := by
    simp only [hw, hJval]
    calc (q ^ (d + 1) + (q - 1) * (j * q ^ j)) * q ^ (m - j)
        = q ^ (d + 1) * q ^ (m - j) + (q - 1) * j * (q ^ j * q ^ (m - j)) := by ring
      _ = q ^ (d + 1) * q ^ (m - j) + (q - 1) * j * q ^ m := by rw [hppj]
  have hwJTv : w JT * q ^ (m - j) =
      q ^ (d + 1) * q ^ (m - j) + (q - 1) * (j + t) * q ^ (m + t) := by
    simp only [hw, hJTval]
    calc (q ^ (d + 1) + (q - 1) * ((j + t) * q ^ (j + t))) * q ^ (m - j)
        = q ^ (d + 1) * q ^ (m - j)
          + (q - 1) * (j + t) * (q ^ (j + t) * q ^ (m - j)) := by ring
      _ = q ^ (d + 1) * q ^ (m - j) + (q - 1) * (j + t) * q ^ (m + t) := by
        rw [hppjt]
  have hpowlt : q ^ m < q ^ (m + t) := by
    apply Nat.pow_lt_pow_right (by omega); omega
  have hred : (q - 1) * (i + t) * q ^ (m + t) + (q - 1) * j * q ^ m
      < (q - 1) * i * q ^ m + (q - 1) * (j + t) * q ^ (m + t) := by
    set c := q - 1 with hc
    set Pm := q ^ m with hPm
    set Pt := q ^ (m + t) with hPt
    have hcpos : 0 < c := by omega
    have hbase : (i + t) * Pt + j * Pm < i * Pm + (j + t) * Pt := by
      obtain ⟨s, hs, hspos⟩ : ∃ s, j = i + s ∧ 0 < s := ⟨j - i, by omega, by omega⟩
      subst hs
      have hsP : s * Pm < s * Pt := Nat.mul_lt_mul_of_pos_left hpowlt hspos
      have hLe : (i + t) * Pt + (i + s) * Pm = (i * Pt + t * Pt + i * Pm) + s * Pm := by
        ring
      have hRe : i * Pm + (i + s + t) * Pt = (i * Pt + t * Pt + i * Pm) + s * Pt := by
        ring
      rw [hLe, hRe]
      exact Nat.add_lt_add_left hsP _
    calc c * (i + t) * Pt + c * j * Pm
        = c * ((i + t) * Pt + j * Pm) := by ring
      _ < c * (i * Pm + (j + t) * Pt) := Nat.mul_lt_mul_of_pos_left hbase hcpos
      _ = c * i * Pm + c * (j + t) * Pt := by ring
  have hstrict : w IT * q ^ (m - i) + w J * q ^ (m - j) <
      w I * q ^ (m - i) + w JT * q ^ (m - j) := by
    rw [hwIv, hwITv, hwJv, hwJTv]
    have hL : q ^ (d + 1) * q ^ (m - i) + (q - 1) * (i + t) * q ^ (m + t)
          + (q ^ (d + 1) * q ^ (m - j) + (q - 1) * j * q ^ m)
        = (q ^ (d + 1) * q ^ (m - i) + q ^ (d + 1) * q ^ (m - j))
          + ((q - 1) * (i + t) * q ^ (m + t) + (q - 1) * j * q ^ m) := by
      ring
    have hR : q ^ (d + 1) * q ^ (m - i) + (q - 1) * i * q ^ m
          + (q ^ (d + 1) * q ^ (m - j) + (q - 1) * (j + t) * q ^ (m + t))
        = (q ^ (d + 1) * q ^ (m - i) + q ^ (d + 1) * q ^ (m - j))
          + ((q - 1) * i * q ^ m + (q - 1) * (j + t) * q ^ (m + t)) := by
      ring
    rw [hL, hR]
    exact Nat.add_lt_add_left hred _
  change Phi q d kk' < Phi q d kk
  unfold Phi
  rw [hPhiEq kk', hPhiEq kk]
  omega

/-- **Parallelogram double move.** When the target diagonal `m-j` is full, swap two
stones around a parallelogram with corners `P=(i,m-i)`, `S=(j+t,m-j)`, `Q=(i+t,m-i)`,
`R=(j,m-j)` (rows `i<j`, shift `t ≥ 1`, all rows `≤ d`): remove one from `P` and `S`,
add one to `Q` and `R`. This preserves every column and diagonal sum (so admissibility
needs no slack hypothesis) and strictly lowers `Φ` by `(q - 1)(j-i)(q ^ m - q ^ {m+t}) < 0`. -/
lemma move_parallelogram (q d k m i j t : ℕ) (hq : 2 ≤ q) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk)
    (hi : i ≤ m) (hj : j ≤ m) (hij : i < j) (ht : 1 ≤ t)
    (hjt : j + t ≤ d)
    (hsrcP : 1 ≤ digit q (kk ⟨i, by omega⟩) (m - i))
    (hsrcS : 1 ≤ digit q (kk ⟨j + t, by omega⟩) (m - j)) :
    ∃ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' ∧ Phi q d kk' < Phi q d kk := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨hrep, hcf⟩ := hadm
  -- the four indices
  set I : Fin (d + 1) := ⟨i, by omega⟩ with hI
  set J : Fin (d + 1) := ⟨j, by omega⟩ with hJ
  set IT : Fin (d + 1) := ⟨i + t, by omega⟩ with hIT
  set JT : Fin (d + 1) := ⟨j + t, by omega⟩ with hJT
  have hIval : (I : ℕ) = i := rfl
  have hJval : (J : ℕ) = j := rfl
  have hITval : (IT : ℕ) = i + t := rfl
  have hJTval : (JT : ℕ) = j + t := rfl
  -- pairwise relations (all but IT = J are guaranteed distinct)
  have hIJ : I ≠ J := by
    intro h
    have := congrArg Fin.val h
    simp [hIval, hJval] at this
    omega
  have hIIT : I ≠ IT := by
    intro h
    have := congrArg Fin.val h
    simp [hIval, hITval] at this
    omega
  have hIJT : I ≠ JT := by
    intro h
    have := congrArg Fin.val h
    simp [hIval, hJTval] at this
    omega
  have hJJT : J ≠ JT := by
    intro h
    have := congrArg Fin.val h
    simp [hJval, hJTval] at this
    omega
  have hITJT : IT ≠ JT := by
    intro h
    have := congrArg Fin.val h
    simp [hITval, hJTval] at this
    omega
  -- no-borrow at I (source P) and JT (source S)
  have hborrowP : q ^ (m - i) ≤ kk I := by
    calc q ^ (m - i) = 1 * q ^ (m - i) := (one_mul _).symm
      _ ≤ digit q (kk I) (m - i) * q ^ (m - i) := Nat.mul_le_mul_right _ hsrcP
      _ ≤ kk I := digit_place_le _ _ _
  have hborrowS : q ^ (m - j) ≤ kk JT := by
    calc q ^ (m - j) = 1 * q ^ (m - j) := (one_mul _).symm
      _ ≤ digit q (kk JT) (m - j) * q ^ (m - j) := Nat.mul_le_mul_right _ hsrcS
      _ ≤ kk JT := digit_place_le _ _ _
  -- m - i ≠ m - j
  have hmimj : m - i ≠ m - j := by omega
  -- the new tuple
  set kk' : Fin (d + 1) → ℕ :=
    fun r => kk r - (if r = I then q ^ (m - i) else 0) - (if r = JT then q ^ (m - j) else 0)
              + (if r = IT then q ^ (m - i) else 0) + (if r = J then q ^ (m - j) else 0)
    with hkk'def
  -- pointwise characterization on the always-distinct rows I and JT
  have hkkI : kk' I = kk I - q ^ (m - i) := by
    simp only [hkk'def, if_neg hIJT, if_neg hIIT, if_neg hIJ, if_true, add_zero,
      Nat.sub_zero]
  have hkkJT : kk' JT = kk JT - q ^ (m - j) := by
    simp only [hkk'def, if_neg hIJT.symm, if_neg hITJT.symm, if_neg hJJT.symm, if_true,
      add_zero, Nat.sub_zero]
  refine ⟨kk', ⟨?_, ?_⟩, ?_⟩
  · exact
      move_parallelogram_representation q d k m i j t kk kk' I J IT JT hi hj hrep
        hborrowP hborrowS hIval hJval hITval hJTval hIJT hkk'def
  · exact
      move_parallelogram_carry_free q d m i j t kk kk' I J IT JT hq1 hcf hsrcP hsrcS
        hJval hITval hJTval hIJ hIIT hIJT hJJT hITJT hmimj hkk'def hkkI hkkJT
  · exact
      move_parallelogram_phi_lt q d m i j t hq kk kk' I J IT JT hi hj hij ht
        hborrowP hborrowS hIval hJval hITval hJTval hIJT hkk'def

/-! ### No two distinct maximizers -/

/-- **A maximizer minimizes `Φ`.** For an admissible `F`-maximizer `kk`, every
admissible tuple `kk'` with the same `k` has `Φ kk ≤ Φ kk'` (via `F_lt_of_Phi_lt`). -/
lemma maximizer_min_Phi (q d k : ℕ) (hq : 2 ≤ q) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk)
    (hmax : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk)
    (kk' : Fin (d + 1) → ℕ) (hadm' : Admissible q d k kk') :
    Phi q d kk ≤ Phi q d kk' := by
  by_contra h
  push Not at h
  -- h : Phi q d kk' < Phi q d kk
  have hrep : (∑ i : Fin (d + 1), kk i * q ^ (i : ℕ))
      = (∑ i : Fin (d + 1), kk' i * q ^ (i : ℕ)) := by
    rw [← hadm.1, ← hadm'.1]
  have hPhi : (q ^ (d + 1) * ∑ i : Fin (d + 1), kk' i
              + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk' i)
          < (q ^ (d + 1) * ∑ i : Fin (d + 1), kk i
              + (q - 1) * ∑ i : Fin (d + 1), (i : ℕ) * q ^ (i : ℕ) * kk i) := by
    simpa [Phi] using h
  have hF : F q d kk < F q d kk' := F_lt_of_Phi_lt q d k hq kk kk' hrep hPhi
  have hle : F q d kk' ≤ F q d kk := hmax kk' hadm'
  exact absurd hF (not_lt.mpr hle)

/-- A natural `x` with `x < q ^ N` equals the sum of its first `N` base-`q` digits
weighted by place value. -/
theorem digit_sum_repr (q : ℕ) :
    ∀ (N x : ℕ), x < q ^ N → x = ∑ n ∈ Finset.range N, digit q x n * q ^ n := by
  intro N
  induction N with
  | zero =>
    intro x hx
    simp only [pow_zero] at hx
    simp only [Finset.range_zero, Finset.sum_empty]; omega
  | succ N ih =>
    intro x hx
    rw [Finset.sum_range_succ']
    have hxq : x / q < q ^ N := by
      rw [pow_succ] at hx
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hx)
    have hih := ih (x / q) hxq
    have hdshift : ∀ n, digit q x (n+1) = digit q (x / q) n := by
      intro n; simp only [digit, pow_succ]
      rw [show q ^ n * q = q * q ^ n by ring, ← Nat.div_div_eq_div_mul]
    calc x = digit q x 0 + q * (x / q) := by
            have := Nat.div_add_mod x q
            simp only [digit, pow_zero, Nat.div_one]; omega
      _ = digit q x 0 + q * (∑ n ∈ Finset.range N, digit q (x/q) n * q ^ n) := by rw [← hih]
      _ = digit q x 0 + ∑ n ∈ Finset.range N, digit q (x/q) n * q ^ (n+1) := by
            rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intro n _; rw [pow_succ]; ring
      _ = (∑ n ∈ Finset.range N, digit q x (n+1) * q ^ (n+1)) + digit q x 0 * q ^ 0 := by
            simp only [pow_zero, mul_one]; rw [add_comm]; congr 1
            apply Finset.sum_congr rfl; intro n _; rw [hdshift]

/-- Reindex a "column" sum (terms with `i ≤ m`, weighted by `q ^ m`) as a place-shifted
digit sum: substitute `n = m - i`. -/
theorem reindex_col (q i M : ℕ) (f : ℕ → ℕ) :
    (∑ m ∈ Finset.range M, (if i ≤ m then f (m - i) * q ^ m else 0))
      = q ^ i * ∑ n ∈ Finset.range (M - i), f n * q ^ n := by
  rw [Finset.mul_sum, ← Finset.sum_filter]
  rw [show (Finset.range M).filter (fun m => i ≤ m) = Finset.Ico i M by
        ext x; simp [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.add_sub_cancel_left, pow_add]; ring

/-- **Uniqueness of finite base-`q` representations.** If `k = ∑_{i<M} c i · q ^ i` with
every coefficient `c n ≤ q - 1` and `c` vanishing past `M`, then `c m` is exactly the
`m`-th base-`q` digit of `k`. -/
theorem digit_eq_of_repr' (q : ℕ) (hq : 2 ≤ q) :
    ∀ (m : ℕ) (c : ℕ → ℕ) (k : ℕ),
      (∀ n, c n ≤ q - 1) →
      (∃ M, (∀ n, M ≤ n → c n = 0) ∧ k = ∑ i ∈ Finset.range M, c i * q ^ i) →
      c m = digit q k m := by
  intro m
  induction m with
  | zero =>
    intro c k hc ⟨M, hMvanish, hrep⟩
    have hc0 : c 0 < q := by have := hc 0; omega
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      simp at hrep
      have : c 0 = 0 := hMvanish 0 (by omega)
      simp [digit, hrep, this]
    · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have hdec : (∑ i ∈ Finset.range (M'+1), c i * q ^ i)
          = c 0 + q * ∑ i ∈ Finset.range M', c (i+1) * q ^ i := by
        rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
        simp only [pow_zero, mul_one]; congr 1
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hdec] at hrep
      simp only [digit, pow_zero, Nat.div_one]
      rw [hrep, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0]
  | succ m ih =>
    intro c k hc ⟨M, hMvanish, hrep⟩
    have hc0 : c 0 < q := by have := hc 0; omega
    set c' : ℕ → ℕ := fun n => c (n + 1) with hc'def
    have hdigrec : digit q k (m + 1) = digit q (k / q) m := by
      simp only [digit, pow_succ]
      rw [show q ^ m * q = q * q ^ m by ring, ← Nat.div_div_eq_div_mul]
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have hkzero : k = 0 := by
        simpa using hrep
      have hcm : c (m + 1) = 0 := hMvanish (m + 1) (by omega)
      rw [hcm, hdigrec, hkzero]; simp [digit]
    · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have hdec : (∑ i ∈ Finset.range (M'+1), c i * q ^ i)
          = c 0 + q * ∑ i ∈ Finset.range M', c (i+1) * q ^ i := by
        rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
        simp only [pow_zero, mul_one]; congr 1
        apply Finset.sum_congr rfl; intro i _; ring
      have hkq : k / q = ∑ i ∈ Finset.range M', c' i * q ^ i := by
        rw [hrep, hdec, Nat.add_mul_div_left _ _ (by omega : 0 < q),
            Nat.div_eq_of_lt hc0, zero_add]
      rw [hdigrec, show c (m + 1) = c' m from rfl]
      apply ih c' (k / q)
      · intro n; exact hc (n + 1)
      · refine ⟨M', ?_, hkq⟩
        intro n hn; simp only [hc'def]; exact hMvanish (n + 1) (by omega)

/-- **Exact column sums.** A maximizer `kk` has exactly `digit q k m` stones in
column `m` (`∑_{i ≤ m} digit q (kk i) (m-i) = digit q k m`): by `carry_elimination`
the column sums are `≤ q-1`, so they form the unique base-`q` digit string of `k`. -/
lemma column_sum_eq (q d k : ℕ) (hq : q.Prime) (kk : Fin (d + 1) → ℕ)
    (hadm : Admissible q d k kk)
    (hmax : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk)
    (m : ℕ) :
    (∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0))
      = digit q k m := by
  have hq2 : 2 ≤ q := hq.two_le
  have hrepk : k = ∑ i : Fin (d + 1), kk i * q ^ (i : ℕ) := hadm.1
  have hkkle : ∀ i : Fin (d + 1), kk i ≤ k := admissible_le q d k (by omega) kk hadm
  have hce : ∀ m : ℕ, (∑ i : Fin (d + 1),
      (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0)) ≤ q - 1 :=
    carry_elimination q d k hq kk hadm hmax
  -- pick N with k < q ^ N
  obtain ⟨N, hkN⟩ : ∃ N, k < q ^ N := by
    refine ⟨k + 1, ?_⟩
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ q ^ (k + 1) := Nat.pow_le_pow_left hq2 _
  set M := N + d + 1 with hMdef
  set colSum : ℕ → ℕ := fun m =>
    ∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (kk i) (m - (i : ℕ)) else 0) with hcsdef
  change colSum m = digit q k m
  -- column sums vanish past column M
  have hvanish : ∀ mm, M ≤ mm → colSum mm = 0 := by
    intro mm hmm
    simp only [hcsdef]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : (i : ℕ) ≤ mm
    · rw [if_pos hi]
      have hbig : kk i < q ^ (mm - (i : ℕ)) := by
        have hile : (i : ℕ) ≤ d := by have := i.2; omega
        calc kk i ≤ k := hkkle i
          _ < q ^ N := hkN
          _ ≤ q ^ (mm - (i : ℕ)) := Nat.pow_le_pow_right (by omega) (by omega)
      simp only [digit]
      rw [Nat.div_eq_of_lt hbig]; simp
    · rw [if_neg hi]
  -- the finite base-q expansion: k = ∑_{mm<M} colSum mm * q ^ mm
  have hcolrep : k = ∑ mm ∈ Finset.range M, colSum mm * q ^ mm := by
    have step1 : (∑ mm ∈ Finset.range M, colSum mm * q ^ mm)
        = ∑ i : Fin (d + 1), ∑ mm ∈ Finset.range M,
            (if (i : ℕ) ≤ mm then digit q (kk i) (mm - (i : ℕ)) * q ^ mm else 0) := by
      simp only [hcsdef]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro mm _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [step1]
    have step2 : ∀ i : Fin (d + 1),
        (∑ mm ∈ Finset.range M,
          (if (i : ℕ) ≤ mm then digit q (kk i) (mm - (i : ℕ)) * q ^ mm else 0))
          = kk i * q ^ (i : ℕ) := by
      intro i
      rw [reindex_col q (i : ℕ) M (fun n => digit q (kk i) n)]
      have hMiN : N ≤ M - (i : ℕ) := by have := i.2; omega
      have hkkN : kk i < q ^ (M - (i : ℕ)) := by
        calc kk i ≤ k := hkkle i
          _ < q ^ N := hkN
          _ ≤ q ^ (M - (i : ℕ)) := Nat.pow_le_pow_right (by omega) hMiN
      rw [← digit_sum_repr q (M - (i : ℕ)) (kk i) hkkN]; ring
    rw [hrepk]
    apply Finset.sum_congr rfl
    intro i _
    rw [step2 i]
  -- conclude by uniqueness of base-q representation
  exact digit_eq_of_repr' q hq2 m colSum k (fun mm => hce mm) ⟨M, hvanish, hcolrep⟩

/-- **Extremal differing-cell selection.** Given admissible `a ≠ b` with equal column
sums in every column, there are a column `m₀` and rows `i₀ < j₀` (`i₀, j₀ ≤ m₀`,
`j₀ ≤ d`) such that `a` and `b` agree on every cell in columns `< m₀`, and either
`a` has a surplus at `(i₀, m₀-i₀)` and a deficit at `(j₀, m₀-j₀)`, or the mirror
image with `a` and `b` swapped. In both cases the surplus row lies strictly above
the deficit row, so a downward move on the surplus array is possible. -/
lemma differing_cell_select (q d k : ℕ) (hq : q.Prime)
    (a b : Fin (d + 1) → ℕ) (hadma : Admissible q d k a) (hadmb : Admissible q d k b)
    (hcol : ∀ m : ℕ,
      (∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (a i) (m - (i : ℕ)) else 0))
        = (∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (b i) (m - (i : ℕ)) else 0)))
    (hne : a ≠ b) :
    ∃ (m₀ i₀ j₀ : ℕ) (_hi₀ : i₀ ≤ m₀) (_hj₀ : j₀ ≤ m₀) (hj₀d : j₀ ≤ d)
      (hij : i₀ < j₀),
      (∀ (r : Fin (d + 1)) (nn : ℕ), (r : ℕ) + nn < m₀ →
          digit q (a r) nn = digit q (b r) nn) ∧
      -- surplus on `a` (left disjunct) or on `b` (right disjunct)
      ((1 ≤ digit q (a ⟨i₀, by omega⟩) (m₀ - i₀) ∧
          digit q (b ⟨i₀, by omega⟩) (m₀ - i₀) < digit q (a ⟨i₀, by omega⟩) (m₀ - i₀) ∧
          digit q (a ⟨j₀, by omega⟩) (m₀ - j₀) < digit q (b ⟨j₀, by omega⟩) (m₀ - j₀))
        ∨
       (1 ≤ digit q (b ⟨i₀, by omega⟩) (m₀ - i₀) ∧
          digit q (a ⟨i₀, by omega⟩) (m₀ - i₀) < digit q (b ⟨i₀, by omega⟩) (m₀ - i₀) ∧
           digit q (b ⟨j₀, by omega⟩) (m₀ - j₀) < digit q (a ⟨j₀, by omega⟩) (m₀ - j₀))) := by
  classical
  have hq2 : 2 ≤ q := hq.two_le
  -- STEP 1: support bound. Pick N with a r, b r < q ^ N for all r.
  have hale : ∀ i : Fin (d + 1), a i ≤ k := admissible_le q d k (by omega) a hadma
  have hble : ∀ i : Fin (d + 1), b i ≤ k := admissible_le q d k (by omega) b hadmb
  obtain ⟨N, hkN⟩ : ∃ N, k < q ^ N := by
    refine ⟨k + 1, ?_⟩
    calc k < 2 ^ k := Nat.lt_two_pow_self
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ q ^ (k + 1) := Nat.pow_le_pow_left hq2 _
  -- digits vanish above N
  have hzero : ∀ (x : ℕ), x ≤ k → ∀ n, N ≤ n → digit q x n = 0 := by
    intro x hx n hn
    have hxq : x < q ^ n := by
      calc x ≤ k := hx
        _ < q ^ N := hkN
        _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
    unfold digit
    rw [Nat.div_eq_of_lt hxq]
    simp
  have hazero : ∀ (r : Fin (d + 1)) n, N ≤ n → digit q (a r) n = 0 :=
    fun r n hn => hzero (a r) (hale r) n hn
  have hbzero : ∀ (r : Fin (d + 1)) n, N ≤ n → digit q (b r) n = 0 :=
    fun r n hn => hzero (b r) (hble r) n hn
  -- STEP 2 & 3: define the differing-cell finset D, prove nonempty, select extremal cell.
  set D : Finset (Fin (d + 1) × ℕ) :=
    (Finset.univ ×ˢ Finset.range N).filter
      (fun p => digit q (a p.1) p.2 ≠ digit q (b p.1) p.2) with hDdef
  -- membership characterization
  have hDmem : ∀ p : Fin (d + 1) × ℕ, p ∈ D ↔
      (p.2 < N ∧ digit q (a p.1) p.2 ≠ digit q (b p.1) p.2) := by
    intro p
    simp only [hDdef, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      Finset.mem_range, true_and]
  -- nonempty: a ≠ b gives a differing digit
  have hDne : D.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    funext r
    apply digit_ext q hq2
    intro n
    by_cases hn : n < N
    · by_contra hcontra
      have : (r, n) ∈ D := by
        rw [hDmem]; exact ⟨hn, hcontra⟩
      rw [hempty] at this
      simp at this
    · push Not at hn
      rw [hazero r n hn, hbzero r n hn]
  -- lex key: column primary, row tiebreak
  set key : Fin (d + 1) × ℕ → ℕ := fun p => ((p.1 : ℕ) + p.2) * (d + 1) + (p.1 : ℕ) with hkeydef
  obtain ⟨p₀, hp₀mem, hp₀min⟩ := Finset.exists_min_image D key hDne
  set i₀ := (p₀.1 : ℕ) with hi₀def
  set n₀ := p₀.2 with hn₀def
  set m₀ := i₀ + n₀ with hm₀def
  have hi₀lt : i₀ < d + 1 := p₀.1.2
  have hi₀m₀ : i₀ ≤ m₀ := by omega
  have hn₀N : n₀ < N := (hDmem p₀).mp hp₀mem |>.1
  have hdiff₀ : digit q (a p₀.1) n₀ ≠ digit q (b p₀.1) n₀ := (hDmem p₀).mp hp₀mem |>.2
  -- key value at p₀
  have hkeyp₀ : key p₀ = m₀ * (d + 1) + i₀ := by
    simp only [hkeydef, hi₀def, hn₀def, hm₀def]
  -- STEP 4: agreement strictly below column m₀.
  have hagree : ∀ (r : Fin (d + 1)) (nn : ℕ), (r : ℕ) + nn < m₀ →
      digit q (a r) nn = digit q (b r) nn := by
    intro r nn hlt
    by_contra hcontra
    -- (r, nn) is a differing cell, with nn < N
    have hnnN : nn < N := by
      by_contra hge
      push Not at hge
      rw [hazero r nn hge, hbzero r nn hge] at hcontra
      exact hcontra rfl
    have hmem : (r, nn) ∈ D := by rw [hDmem]; exact ⟨hnnN, hcontra⟩
    have hmin := hp₀min (r, nn) hmem
    -- key (r,nn) = (r+nn)*(d + 1)+r. key p₀ = m₀*(d + 1)+i₀
    have hrlt : (r : ℕ) < d + 1 := r.2
    rw [hkeyp₀] at hmin
    simp only [hkeydef] at hmin
    -- (r+nn) < m₀ so (r+nn)*(d + 1)+r < m₀*(d + 1) ≤ m₀*(d + 1)+i₀
    have : ((r : ℕ) + nn) * (d + 1) + (r : ℕ) < m₀ * (d + 1) + i₀ := by
      have h1 : ((r : ℕ) + nn + 1) * (d + 1) ≤ m₀ * (d + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith [hrlt]
    omega
  -- tiebreak: any differing cell (r, n) in column m₀ has i₀ ≤ r
  have htiebreak : ∀ (r : Fin (d + 1)), (r : ℕ) ≤ m₀ →
      digit q (a r) (m₀ - (r:ℕ)) ≠ digit q (b r) (m₀ - (r:ℕ)) → i₀ ≤ (r : ℕ) := by
    intro r hrm hdiffr
    set nn := m₀ - (r : ℕ) with hnndef
    have hcolr : (r : ℕ) + nn = m₀ := by omega
    have hnnN : nn < N := by
      by_contra hge
      push Not at hge
      rw [hazero r nn hge, hbzero r nn hge] at hdiffr
      exact hdiffr rfl
    have hmem : (r, nn) ∈ D := by rw [hDmem]; exact ⟨hnnN, hdiffr⟩
    have hmin := hp₀min (r, nn) hmem
    rw [hkeyp₀] at hmin
    simp only [hkeydef] at hmin
    -- (r+nn) = m₀, so key = m₀*(d + 1) + r ≥ m₀*(d + 1)+i₀ ⟹ i₀ ≤ r
    have hrr : ((r : ℕ) + nn) * (d + 1) + (r : ℕ) = m₀ * (d + 1) + (r : ℕ) := by
      rw [hcolr]
    omega
  -- STEP 5: column functions
  set fa : Fin (d + 1) → ℕ := fun i => if (i : ℕ) ≤ m₀ then digit q (a i) (m₀ - (i : ℕ)) else 0
    with hfadef
  set fb : Fin (d + 1) → ℕ := fun i => if (i : ℕ) ≤ m₀ then digit q (b i) (m₀ - (i : ℕ)) else 0
    with hfbdef
  have hsumeq : (∑ i : Fin (d + 1), fa i) = ∑ i : Fin (d + 1), fb i := hcol m₀
  -- value of fa, fb at p₀.1 : position m₀ - i₀ = n₀
  have hpos₀ : m₀ - i₀ = n₀ := by omega
  have hfaI : fa p₀.1 = digit q (a p₀.1) n₀ := by
    simp only [hfadef, ← hi₀def]; rw [if_pos hi₀m₀, hpos₀]
  have hfbI : fb p₀.1 = digit q (b p₀.1) n₀ := by
    simp only [hfbdef, ← hi₀def]; rw [if_pos hi₀m₀, hpos₀]
  have hfdiffI : fa p₀.1 ≠ fb p₀.1 := by rw [hfaI, hfbI]; exact hdiff₀
  -- helper: given a strict surplus f₁ I < f₂ I within equal-sum columns, find J with f₂ J < f₁ J
  have findJ : ∀ (f₁ f₂ : Fin (d + 1) → ℕ),
      (∑ i : Fin (d + 1), f₁ i) = (∑ i : Fin (d + 1), f₂ i) →
      f₁ p₀.1 < f₂ p₀.1 → ∃ J : Fin (d + 1), f₂ J < f₁ J := by
    intro f₁ f₂ heq hlt
    by_contra hcon
    push Not at hcon  -- ∀ J, f₁ J ≤ f₂ J
    have hstrict : (∑ i : Fin (d + 1), f₁ i) < ∑ i : Fin (d + 1), f₂ i := by
      apply Finset.sum_lt_sum (fun i _ => hcon i)
      exact ⟨p₀.1, Finset.mem_univ _, hlt⟩
    omega
  -- a row J with `fa J < fb J` (a-deficit) lies in column m₀ and is below i₀.
  -- (in the position-form: digit q (a J)(m₀-J) < digit q (b J)(m₀-J))
  have JfromFa : ∀ (J : Fin (d + 1)), fa J < fb J →
      ((J : ℕ) ≤ m₀ ∧ digit q (a J) (m₀ - (J:ℕ)) < digit q (b J) (m₀ - (J:ℕ))) := by
    intro J hJlt
    by_cases hJm : (J : ℕ) ≤ m₀
    · refine ⟨hJm, ?_⟩
      simp only [hfadef, hfbdef, if_pos hJm] at hJlt
      exact hJlt
    · exfalso; simp only [hfadef, hfbdef, if_neg hJm] at hJlt; omega
  have JfromFb : ∀ (J : Fin (d + 1)), fb J < fa J →
      ((J : ℕ) ≤ m₀ ∧ digit q (b J) (m₀ - (J:ℕ)) < digit q (a J) (m₀ - (J:ℕ))) := by
    intro J hJlt
    by_cases hJm : (J : ℕ) ≤ m₀
    · refine ⟨hJm, ?_⟩
      simp only [hfadef, hfbdef, if_pos hJm] at hJlt
      exact hJlt
    · exfalso; simp only [hfadef, hfbdef, if_neg hJm] at hJlt; omega
  -- the Fin ⟨i₀, _⟩ equals p₀.1
  have hI₀eq : (⟨i₀, by omega⟩ : Fin (d + 1)) = p₀.1 := by
    apply Fin.ext; simp [hi₀def]
  -- STEP 6: assemble. Case split on the sign at the upper cell i₀.
  rcases lt_or_gt_of_ne hfdiffI with hsign | hsign
  · -- fa I < fb I : b-surplus at i₀ ⟹ RIGHT disjunct
    obtain ⟨J, hJ⟩ := findJ fa fb hsumeq hsign  -- fb J < fa J  (b-deficit, a-surplus at J)
    obtain ⟨hJm, hJpos⟩ := JfromFb J hJ
    -- hJpos : digit q (b J)(m₀-J) < digit q (a J)(m₀-J)
    have hge := htiebreak J hJm (ne_of_lt hJpos).symm
    have hJne : i₀ ≠ (J : ℕ) := by
      intro heq
      have : J = p₀.1 := by apply Fin.ext; simp [← heq, hi₀def]
      rw [this] at hJpos
      rw [hpos₀] at hJpos
      -- hsign : fa p₀.1 < fb p₀.1, i.e. digit a < digit b. hJpos : digit b < digit a
      rw [hfaI, hfbI] at hsign
      omega
    have hij : i₀ < (J : ℕ) := by omega
    have hjd : (J : ℕ) ≤ d := by have := J.2; omega
    refine ⟨m₀, i₀, (J:ℕ), hi₀m₀, hJm, hjd, hij, hagree, Or.inr ⟨?_, ?_, ?_⟩⟩
    · -- 1 ≤ digit q (b ⟨i₀⟩)(m₀-i₀)
      rw [hpos₀, hI₀eq]
      rw [hfaI, hfbI] at hsign; omega
    · -- digit q (a ⟨i₀⟩)(m₀-i₀) < digit q (b ⟨i₀⟩)(m₀-i₀)
      rw [hpos₀, hI₀eq]
      rw [hfaI, hfbI] at hsign; exact hsign
    · -- digit q (b ⟨J⟩)(m₀-J) < digit q (a ⟨J⟩)(m₀-J)
      have : (⟨(J:ℕ), by omega⟩ : Fin (d + 1)) = J := by apply Fin.ext; simp
      rw [this]; exact hJpos
  · -- fb I < fa I : a-surplus at i₀ ⟹ LEFT disjunct
    obtain ⟨J, hJ⟩ := findJ fb fa hsumeq.symm hsign  -- fa J < fb J  (a-deficit at J)
    obtain ⟨hJm, hJpos⟩ := JfromFa J hJ
    -- hJpos : digit q (a J)(m₀-J) < digit q (b J)(m₀-J)
    have hge := htiebreak J hJm (ne_of_lt hJpos)
    have hJne : i₀ ≠ (J : ℕ) := by
      intro heq
      have : J = p₀.1 := by apply Fin.ext; simp [← heq, hi₀def]
      rw [this] at hJpos
      rw [hpos₀] at hJpos
      rw [hfaI, hfbI] at hsign
      omega
    have hij : i₀ < (J : ℕ) := by omega
    have hjd : (J : ℕ) ≤ d := by have := J.2; omega
    refine ⟨m₀, i₀, (J:ℕ), hi₀m₀, hJm, hjd, hij, hagree, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rw [hpos₀, hI₀eq]
      rw [hfaI, hfbI] at hsign; omega
    · rw [hpos₀, hI₀eq]
      rw [hfaI, hfbI] at hsign; exact hsign
    · have : (⟨(J:ℕ), by omega⟩ : Fin (d + 1)) = J := by apply Fin.ext; simp
      rw [this]; exact hJpos

/-- **Surplus row exists in the full-diagonal case.** In the configuration produced by
`differing_cell_select` (rows `i₀ < j₀ ≤ m₀`, `a,b` agree below column `m₀`, `a`
deficit at `(j₀, m₀-j₀)`), if the target diagonal `m₀-j₀` is full in `a`
(`∑_r digit q (a r) (m₀-j₀) = q-1`), then there is a shift `t ≥ 1` with
`j₀ + t ≤ d` and a stone at `(j₀+t, m₀-j₀)`. -/
lemma parallelogram_exists (q d k : ℕ) (hq : q.Prime)
    (a b : Fin (d + 1) → ℕ) (_hadma : Admissible q d k a) (hadmb : Admissible q d k b)
    (m₀ i₀ j₀ : ℕ) (_hi₀ : i₀ ≤ m₀) (hj₀ : j₀ ≤ m₀) (hj₀d : j₀ ≤ d)
    (_hij : i₀ < j₀)
    (hagree : ∀ (r : Fin (d + 1)) (nn : ℕ), (r : ℕ) + nn < m₀ →
        digit q (a r) nn = digit q (b r) nn)
    (hdef : digit q (a ⟨j₀, by omega⟩) (m₀ - j₀) < digit q (b ⟨j₀, by omega⟩) (m₀ - j₀))
    (hfull : (∑ r : Fin (d + 1), digit q (a r) (m₀ - j₀)) = q - 1) :
    ∃ (t : ℕ) (hjtd : j₀ + t ≤ d), 1 ≤ t ∧
      1 ≤ digit q (a ⟨j₀ + t, by omega⟩) (m₀ - j₀) := by
  set nT := m₀ - j₀ with hnT
  set f : Fin (d + 1) → ℕ := fun r => digit q (a r) nT with hf
  set g : Fin (d + 1) → ℕ := fun r => digit q (b r) nT with hg
  -- The specific index `j₀`.
  set J : Fin (d + 1) := ⟨j₀, by omega⟩ with hJ
  by_contra hcon
  push Not at hcon
  -- `hcon`: for every `t` with `j₀ + t ≤ d` and `1 ≤ t`, `digit q (a ⟨j₀+t,_⟩) nT < 1`.
  -- We show that all rows `r > j₀` have `f r = 0`.
  have hzero : ∀ r : Fin (d + 1), j₀ < (r : ℕ) → f r = 0 := by
    intro r hr
    have hrd : (r : ℕ) ≤ d := by have := r.2; omega
    set t := (r : ℕ) - j₀ with ht
    have ht1 : 1 ≤ t := by omega
    have htjd : j₀ + t ≤ d := by omega
    have hcell := hcon t htjd ht1
    have hidx : (⟨j₀ + t, by omega⟩ : Fin (d + 1)) = r := by
      apply Fin.ext; simp [ht]; omega
    rw [hidx] at hcell
    simp only [hf]
    omega
  -- Carry-free for `b` at column `nT`.
  have hbcf : (∑ r : Fin (d + 1), g r) ≤ q - 1 := hadmb.2 nT
  -- The full diagonal for `a`.
  have haf : (∑ r : Fin (d + 1), f r) = q - 1 := hfull
  -- The subset of rows `r ≤ j₀`.
  set Sle : Finset (Fin (d + 1)) := univ.filter (fun r => (r : ℕ) ≤ j₀) with hSle
  -- `J ∈ Sle`.
  have hJSle : J ∈ Sle := by
    simp only [hSle, mem_filter, mem_univ, true_and, hJ]
    exact le_refl j₀
  -- Sum over `Sle` of `g` is `≤` total sum of `g`.
  have hsubset : Sle ⊆ univ := filter_subset _ _
  have hgle : (∑ r ∈ Sle, g r) ≤ ∑ r : Fin (d + 1), g r :=
    sum_le_sum_of_subset hsubset
  -- Peel `J` off the `Sle` sum for `g`.
  have hgpeel : (∑ r ∈ Sle, g r) = (∑ r ∈ Sle.erase J, g r) + g J := by
    rw [Finset.sum_erase_add _ _ hJSle]
  -- For `a`: sum over `Sle` equals total sum minus rows `> j₀` (which are zero).
  -- Equivalently, sum over `Sle` of `f` = total sum of `f`, since rows not in `Sle` are zero.
  have hafle : (∑ r ∈ Sle, f r) = ∑ r : Fin (d + 1), f r := by
    apply Finset.sum_subset hsubset
    intro r _ hrnotin
    simp only [hSle, mem_filter, mem_univ, true_and, not_le] at hrnotin
    exact hzero r hrnotin
  -- Peel `J` off the `Sle` sum for `f`.
  have hfpeel : (∑ r ∈ Sle, f r) = (∑ r ∈ Sle.erase J, f r) + f J := by
    rw [Finset.sum_erase_add _ _ hJSle]
  -- On `Sle.erase J`, rows have `(r:ℕ) < j₀`, where `a` and `b` agree.
  have hagree_erase : ∀ r ∈ Sle.erase J, f r = g r := by
    intro r hrmem
    rw [mem_erase] at hrmem
    obtain ⟨hrne, hrle⟩ := hrmem
    simp only [hSle, mem_filter, mem_univ, true_and] at hrle
    have hrlt : (r : ℕ) < j₀ := by
      rcases lt_or_eq_of_le hrle with h | h
      · exact h
      · exfalso; apply hrne; apply Fin.ext; simp [hJ, h]
    -- column `(r:ℕ) + nT < m₀`.
    have hcol : (r : ℕ) + nT < m₀ := by omega
    have := hagree r nT hcol
    simp only [hf, hg]
    exact this
  have hsumeq : (∑ r ∈ Sle.erase J, f r) = (∑ r ∈ Sle.erase J, g r) :=
    Finset.sum_congr rfl hagree_erase
  -- `hdef` says `f J < g J`.
  have hdefJ : f J < g J := by
    simp only [hf, hg, hJ]; exact hdef
  -- Now derive the contradiction.
  -- ∑ g ≥ ∑_{Sle} g = (∑_{erase} g) + g J = (∑_{erase} f) + g J
  --       ≥ (∑_{erase} f) + (f J + 1) = (∑_{Sle} f) + 1 = (∑ f) + 1 = (q - 1)+1 = q
  -- but ∑ g ≤ q-1, contradiction.
  have hq2 := hq.two_le
  omega

/-- **No two distinct admissible maximizers.** Two admissible `F`-maximizers agree in
every base-`q` digit of every row: both have column sums `digit q k m`
(`column_sum_eq`), so if they differed, `differing_cell_select` plus an improving
step (`move_down` or, via `parallelogram_exists`, `move_parallelogram`) on the
surplus array would strictly lower `Φ`, contradicting `maximizer_min_Phi`. -/
lemma no_two_distinct_maximizers (q d k : ℕ) (hq : q.Prime)
    (kk₁ : Fin (d + 1) → ℕ) (hadm₁ : Admissible q d k kk₁)
    (hmax₁ : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk₁)
    (kk₂ : Fin (d + 1) → ℕ) (hadm₂ : Admissible q d k kk₂)
    (hmax₂ : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk₂)
    (ii : Fin (d + 1) ) (n : ℕ) :
    digit q (kk₁ ii) n = digit q (kk₂ ii) n := by
  -- The whole content is the array-equality `kk₁ = kk₂`; the per-cell goal follows.
  suffices hEq : kk₁ = kk₂ by rw [hEq]
  by_contra hne
  -- Equal column sums: each equals `digit q k m`.
  have hcol : ∀ m : ℕ,
      (∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (kk₁ i) (m - (i : ℕ)) else 0))
        = (∑ i : Fin (d + 1), (if (i : ℕ) ≤ m then digit q (kk₂ i) (m - (i : ℕ)) else 0)) := by
    intro m
    rw [column_sum_eq q d k hq kk₁ hadm₁ hmax₁ m, column_sum_eq q d k hq kk₂ hadm₂ hmax₂ m]
  -- A symmetric key lemma: given a maximizer `a` and another admissible `b` with the
  -- selected differing-cell configuration (surplus on `a`), derive a contradiction.
  have key : ∀ (a b : Fin (d + 1) → ℕ),
      Admissible q d k a → Admissible q d k b →
      (∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d a) →
      ∀ (m₀ i₀ j₀ : ℕ) (hi₀ : i₀ ≤ m₀) (hj₀ : j₀ ≤ m₀) (hj₀d : j₀ ≤ d) (hij : i₀ < j₀),
      (∀ (r : Fin (d + 1)) (nn : ℕ), (r : ℕ) + nn < m₀ →
          digit q (a r) nn = digit q (b r) nn) →
      1 ≤ digit q (a ⟨i₀, by omega⟩) (m₀ - i₀) →
      digit q (a ⟨j₀, by omega⟩) (m₀ - j₀) < digit q (b ⟨j₀, by omega⟩) (m₀ - j₀) →
      False := by
    intro a b hadma hadmb hmaxa m₀ i₀ j₀ hi₀ hj₀ hj₀d hij hagree hsrc hdef
    by_cases hslack : (∑ r : Fin (d + 1), digit q (a r) (m₀ - j₀)) ≤ q - 2
    · -- slack case: move_down strictly decreases Phi
      obtain ⟨a', hadm', hlt⟩ :=
        move_down q d k m₀ i₀ j₀ hq.two_le a hadma hi₀ hj₀ hj₀d hij hsrc hslack
      have := maximizer_min_Phi q d k hq.two_le a hadma hmaxa a' hadm'
      omega
    · -- full case: ∑ = q-1, then parallelogram_exists + move_parallelogram
      push Not at hslack
      have hcap : (∑ r : Fin (d + 1), digit q (a r) (m₀ - j₀)) ≤ q - 1 := hadma.2 (m₀ - j₀)
      have hq2 := hq.two_le
      have hfull : (∑ r : Fin (d + 1), digit q (a r) (m₀ - j₀)) = q - 1 := by omega
      obtain ⟨t, hjtd, ht, hsrcS⟩ :=
        parallelogram_exists q d k hq a b hadma hadmb m₀ i₀ j₀ hi₀ hj₀ hj₀d hij hagree hdef hfull
      obtain ⟨a', hadm', hlt⟩ :=
        move_parallelogram q d k m₀ i₀ j₀ t hq.two_le a hadma hi₀ hj₀ hij ht hjtd hsrc hsrcS
      have := maximizer_min_Phi q d k hq.two_le a hadma hmaxa a' hadm'
      omega
  -- select the differing cell
  obtain ⟨m₀, i₀, j₀, hi₀, hj₀, hj₀d, hij, hagree, hdisj⟩ :=
    differing_cell_select q d k hq kk₁ kk₂ hadm₁ hadm₂ hcol hne
  rcases hdisj with ⟨hsrc, _, hdef⟩ | ⟨hsrc, _, hdef⟩
  · -- surplus on kk₁ = a, kk₂ = b
    exact key kk₁ kk₂ hadm₁ hadm₂ hmax₁ m₀ i₀ j₀ hi₀ hj₀ hj₀d hij hagree hsrc hdef
  · -- surplus on kk₂ = a, kk₁ = b
    exact key kk₂ kk₁ hadm₂ hadm₁ hmax₂ m₀ i₀ j₀ hi₀ hj₀ hj₀d hij
      (fun r nn h => (hagree r nn h).symm) hsrc hdef

/-- **Greedy uniqueness.** Any two admissible tuples that both maximize `F` over the
admissible set are equal: by `digit_ext` it suffices that all base-`q` digits agree,
which is `no_two_distinct_maximizers` (informal.tex `alg:H1-greedy`). -/
lemma maximizer_unique (q d k : ℕ) (hq : q.Prime)
    (kk₁ : Fin (d + 1) → ℕ) (hadm₁ : Admissible q d k kk₁)
    (hmax₁ : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk₁)
    (kk₂ : Fin (d + 1) → ℕ) (hadm₂ : Admissible q d k kk₂)
    (hmax₂ : ∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk₂) :
    kk₁ = kk₂ := by
  have hq2 : 2 ≤ q := hq.two_le
  funext ii
  apply digit_ext q hq2
  intro n
  exact no_two_distinct_maximizers q d k hq kk₁ hadm₁ hmax₁ kk₂ hadm₂ hmax₂ ii n

-- Main Statement(s)

/-- **Theorem (Unique maximizer).** Let `q` be a prime and `d, k ≥ 0`. Among all
admissible `(d + 1)`-tuples, the value `F` attains its maximum at exactly one admissible
tuple: there exists an admissible `kstar` that maximizes `F`, and any admissible tuple
that itself maximizes `F` over all admissible tuples must equal `kstar`. -/
theorem main_theorem (q d k : ℕ) (hq : q.Prime) :
    ∃ kstar : Fin (d + 1) → ℕ, Admissible q d k kstar ∧
      (∀ kk : Fin (d + 1) → ℕ, Admissible q d k kk → F q d kk ≤ F q d kstar) ∧
      (∀ kk : Fin (d + 1) → ℕ, Admissible q d k kk →
        (∀ kk' : Fin (d + 1) → ℕ, Admissible q d k kk' → F q d kk' ≤ F q d kk) →
        kk = kstar) := by
  have hq1 : 1 ≤ q := hq.one_lt.le
  -- Existence + optimality: the admissible set is finite and nonempty, so `F`
  -- attains a maximum on it.
  have hfin := admissible_finite q d k hq1
  set T := hfin.toFinset with hT
  have hk0mem : k0tuple d k ∈ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact k0tuple_admissible q d k hq1
  have hne : T.Nonempty := ⟨_, hk0mem⟩
  obtain ⟨kstar, hkstarMem, hkstarMax⟩ := T.exists_max_image (F q d) hne
  have hkstarAdm : Admissible q d k kstar := by
    rw [hT, Set.Finite.mem_toFinset] at hkstarMem; exact hkstarMem
  have hkstarDom : ∀ kk : Fin (d + 1) → ℕ, Admissible q d k kk → F q d kk ≤ F q d kstar := by
    intro kk hkk
    apply hkstarMax
    rw [hT, Set.Finite.mem_toFinset]; exact hkk
  refine ⟨kstar, hkstarAdm, hkstarDom, ?_⟩
  -- Uniqueness: any admissible maximizer `kk` and `kstar` are both maximizers, so
  -- `maximizer_unique` gives `kk = kstar`.
  intro kk hkk hkkMax
  exact maximizer_unique q d k hq kk hkk hkkMax kstar hkstarAdm hkstarDom

end ZetaH123.H1
