/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Base
import LeanPool.Erdos137.TaoPoint

/-!
# Erdős Problem #137: the deterministic squarefree-capacity reduction

This file isolates the **deterministic** half of the squarefree-counting argument for very bad
intervals.  It contains **no analytic number theory** — no Pandey squarefree-counting theorem,
no Baker–Harman–Pintz prime-in-interval input, no Mertens estimate.  Everything below is a
finite valuation computation checked on the standard Mathlib axioms, building on the elementary
`TaoPoint` mechanism.

## The mechanism

Suppose the block `[n, n+k-1]` is *very bad*, i.e. `F k n = ∏_{i<k} (n+i)` is **powerful**.
Consider the squarefree terms of the block, those `n + i` with `Squarefree (n + i)`.  We claim:

* **(no large prime)** A squarefree term `n + i` has **no** prime factor `p ≥ k`.  Indeed, if
  `p ∣ n + i` with `p ≥ k` prime, then `veryBad_large_prime_sq` forces `p^2 ∣ n + i`, i.e.
  `(n+i).factorization p ≥ 2`, contradicting `Squarefree.natFactorization_le_one`.
  (`sqfree_term_no_large_prime`.)

So every squarefree term is `(k-1)`-smooth: its prime support lies in `Nat.primesBelow k`.

* **(per-prime capacity)** For a fixed prime `p < k`, the number of block terms `n + i`
  (`i < k`) divisible by `p` is at most `⌊k/p⌋ + 1`, by the interval-count `Ioc_dvd_le` (the
  same `i ↦ n+i` bijection idiom as `div_le_factorization_F` in `Base`).  Each squarefree term
  contributes valuation `≤ 1` at `p`, so `v_p(∏ squarefree terms) ≤ ⌊k/p⌋ + 1`.

Hence pointwise on factorizations the squarefree product divides the **small-prime capacity**
`∏_{p < k} p^{⌊k/p⌋+1}`, and `Nat.le_of_dvd` yields the size form.

## Note on the exponent

We use `k/p + 1` (= `⌊k/p⌋ + 1`), **not** a ceiling, because `Ioc_dvd_le` proves exactly the
bound `⌊L/p⌋ + 1` on the number of multiples of `p` in an interval of length `L = k`.

## Deterministic companion

This is the deterministic companion to an **external, unformalized** squarefree-counting
theorem (Pandey) bounding the number of squarefree terms in a block.  That analytic input is
*not* formalized here; only the deterministic capacity bound for the product of the squarefree
terms is.

## Counting obstruction

Bounding each squarefree term below by `n` turns the product bound into a *count* bound.  With
`SqfreeBlockCount k n := #{i < k | Squarefree (n+i)}` we have
`n ^ SqfreeBlockCount k n ≤ SqfreeBlockProduct k n ≤ SmoothCapacity k`, and the capacity factors
as `SmoothCapacity k = L k * P k ≤ k! · 4^k ≤ (4k)^k` (Legendre's first layer `L ∣ k!` plus the
primorial bound `P ≤ 4^k`).  Hence *enough* squarefree terms forces non-powerfulness:
`not_powerful_of_sqfree_count_beats_fourk` says `(4k)^k < n ^ SqfreeBlockCount k n ⟹ ¬ Powerful`.
This is the deterministic interface to an **external** squarefree-count lower bound (Pandey, not
formalized here): supply any `n` and a count exceeding `log_n ((4k)^k)` and the block cannot be
powerful.

## Main results (Mathlib's three axioms only)

* `sqfree_term_no_large_prime` : a squarefree block term has no prime factor `≥ k`.
* `powerful_sqfree_product_dvd_smooth_capacity` : the squarefree product divides the capacity.
* `powerful_sqfree_product_le_smooth_capacity` : the size form (via `Nat.le_of_dvd`).
* `powerful_sqfree_count_capacity_bound` : the counting form `n^count ≤ SmoothCapacity`.
* `smoothCapacity_eq_L_mul_P`, `smoothCapacity_le_four_mul_pow` : capacity `= L·P ≤ (4k)^k`.
* `not_powerful_of_sqfree_count_beats_fourk` : explicit count ⟹ non-powerful obstruction.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## The squarefree-term index set, its product, and the smooth capacity -/

/-- The indices `i < k` whose block term `n + i` is squarefree. -/
def SqfreeBlockIndices (k n : ℕ) : Finset ℕ :=
  (Finset.range k).filter (fun i => Squarefree (n + i))

/-- The product of the squarefree block terms `∏_{i : Squarefree (n+i)} (n + i)`. -/
def SqfreeBlockProduct (k n : ℕ) : ℕ := ∏ i ∈ SqfreeBlockIndices k n, (n + i)

/-- The **small-prime capacity** `∏_{p < k} p^{⌊k/p⌋+1}`. The exponent is `k/p + 1`
(not a ceiling), matching exactly what `Ioc_dvd_le` proves about the count of multiples of `p`
in a length-`k` interval. -/
def SmoothCapacity (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p ^ (k / p + 1)

lemma sqfreeBlockProduct_ne_zero {k n : ℕ} (hn : 1 ≤ n) : SqfreeBlockProduct k n ≠ 0 := by
  unfold SqfreeBlockProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro i _; omega

lemma smoothCapacity_pos (k : ℕ) : 1 ≤ SmoothCapacity k :=
  Finset.one_le_prod' fun _p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos

lemma smoothCapacity_ne_zero (k : ℕ) : SmoothCapacity k ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (smoothCapacity_pos k)

/-! ## The deterministic obstruction: squarefree terms have no large prime -/

/-- **No large prime in a squarefree term.** If `F k n` is powerful, `i < k`, `n + i` is
squarefree, and `p ≥ k` is prime, then `p ∤ n + i`. Otherwise `veryBad_large_prime_sq` forces
`p^2 ∣ n + i`, contradicting squarefreeness (`Squarefree.natFactorization_le_one`). -/
lemma sqfree_term_no_large_prime {k n i p : ℕ} (hn : 1 ≤ n) (hPow : Powerful (F k n))
    (hi : i < k) (hsq : Squarefree (n + i)) (hp : p.Prime) (hkp : k ≤ p) : ¬ p ∣ n + i := by
  intro hpi
  -- `VeryBad k n` is definitionally `Powerful (F k n)`.
  have hbad : VeryBad k n := hPow
  have hsq2 : p ^ 2 ∣ (n + i) := veryBad_large_prime_sq hp hkp hi hn hbad hpi
  have hni : n + i ≠ 0 := by omega
  have hge2 : 2 ≤ (n + i).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hni).mp hsq2
  have hle1 : (n + i).factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
  omega

/-! ## Per-prime valuation bound -/

/-- The set of squarefree-term indices whose term is divisible by `p`. -/
def BlockDvdIndices (k n p : ℕ) : Finset ℕ :=
  (SqfreeBlockIndices k n).filter (fun i => p ∣ (n + i))

/-- **Per-prime capacity count.** For `p ≥ 1`, the number of squarefree-term indices `i` with
`p ∣ n + i` is at most `⌊k/p⌋ + 1`. The squarefree-divisible index set is a subset of *all*
indices `i < k` with `p ∣ n + i`, which biject (via `i ↦ n + i`) onto `{x ∈ (n-1, n-1+k] | p ∣ x}`,
counted by `Ioc_dvd_le` (the same idiom as `div_le_factorization_F`). -/
lemma blockDvdIndices_card_le {k n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    #(BlockDvdIndices k n p) ≤ k / p + 1 := by
  -- Drop the squarefreeness condition: bound by the count of *all* divisible indices.
  set D : Finset ℕ := (Finset.range k).filter (fun i => p ∣ (n + i)) with hD
  have hsub : BlockDvdIndices k n p ⊆ D := by
    intro i hi
    unfold BlockDvdIndices SqfreeBlockIndices at hi
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
    rw [hD, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi.1.1, hi.2⟩
  have hcardle : #(BlockDvdIndices k n p) ≤ #D := Finset.card_le_card hsub
  -- `#D = #{x ∈ (n-1, n-1+k] | p ∣ x}` via the bijection `i ↦ n + i`.
  have hbij : #D = #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} := by
    apply Finset.card_bij (fun i _ => n + i)
    · intro i hi
      rw [hD, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hi.2⟩
    · intro i _ j _ h; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxdvd⟩ := hx
      refine ⟨x - n, ?_, by omega⟩
      rw [hD, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show n + (x - n) = x by omega]; exact hxdvd
  -- `Ioc_dvd_le` with `a = n-1`, `L = k`: `(n-1)+k = n-1+k` is the upper endpoint.
  have hIoc : #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} ≤ k / p + 1 :=
    Ioc_dvd_le (n - 1) k p hp
  omega

/-- **Valuation of the squarefree product at `p` is bounded by the count.** Each squarefree term
contributes valuation `≤ 1` at `p` (and `0` if `p ∤ n+i`), so summing over the squarefree
indices gives `v_p(∏) ≤ #{i : Squarefree ∧ p ∣ n+i} = #(BlockDvdIndices k n p)`. -/
lemma sqfreeBlockProduct_factorization_le_count {k n p : ℕ} (hn : 1 ≤ n) :
    (SqfreeBlockProduct k n).factorization p ≤ #(BlockDvdIndices k n p) := by
  unfold SqfreeBlockProduct
  rw [Nat.factorization_prod (by intro i _; omega), Finset.sum_apply']
  -- Each summand: `≤ if p ∣ n+i then 1 else 0`, since the term is squarefree.
  calc ∑ i ∈ SqfreeBlockIndices k n, (n + i).factorization p
      ≤ ∑ i ∈ SqfreeBlockIndices k n, (if p ∣ (n + i) then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        unfold SqfreeBlockIndices at hi
        rw [Finset.mem_filter] at hi
        by_cases hpi : p ∣ (n + i)
        · rw [if_pos hpi]; exact Squarefree.natFactorization_le_one p hi.2
        · rw [if_neg hpi, Nat.factorization_eq_zero_of_not_dvd hpi]
    _ = #(BlockDvdIndices k n p) := by
        unfold BlockDvdIndices
        rw [Finset.sum_boole]
        simp

/-- **Factorization of the capacity.** For prime `p < k`, `v_p(SmoothCapacity k) = ⌊k/p⌋ + 1`;
for `p ∉ primesBelow k`, it is `0`. -/
lemma smoothCapacity_factorization (k p : ℕ) :
    (SmoothCapacity k).factorization p
      = if p ∈ Nat.primesBelow k then k / p + 1 else 0 := by
  unfold SmoothCapacity
  rw [Nat.factorization_prod (fun q hq => by
    have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow k
  · rw [if_pos hp]
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    rw [Finset.sum_eq_single p
          (fun q hq hqp => by
            have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
            rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hqp])
          (fun h => absurd hp h)]
    rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
    have hne : q ≠ p := by rintro rfl; exact hp hq
    rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]

/-! ## Main results -/

/-- **The squarefree product divides the small-prime capacity.** If `F k n` is powerful, then
`∏_{i : Squarefree (n+i)} (n+i)` divides `∏_{p < k} p^{⌊k/p⌋+1}`. Pointwise on factorizations:
a prime `p ≥ k` cannot divide any squarefree term (`sqfree_term_no_large_prime`), so its
valuation in the product is `0 ≤` the capacity's; a prime `p < k` has valuation `≤ #(divisible
squarefree terms) ≤ ⌊k/p⌋ + 1` (`sqfreeBlockProduct_factorization_le_count`,
`blockDvdIndices_card_le`); a non-prime contributes `0`. -/
theorem powerful_sqfree_product_dvd_smooth_capacity {k n : ℕ} (hn : 1 ≤ n)
    (hPow : Powerful (F k n)) : SqfreeBlockProduct k n ∣ SmoothCapacity k := by
  rw [← Nat.factorization_le_iff_dvd (sqfreeBlockProduct_ne_zero hn) (smoothCapacity_ne_zero k)]
  intro p
  rw [smoothCapacity_factorization k p]
  by_cases hp : p ∈ Nat.primesBelow k
  · -- small prime: valuation ≤ count ≤ ⌊k/p⌋+1.
    rw [if_pos hp]
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have h1 : (SqfreeBlockProduct k n).factorization p ≤ #(BlockDvdIndices k n p) :=
      sqfreeBlockProduct_factorization_le_count hn
    have h2 : #(BlockDvdIndices k n p) ≤ k / p + 1 := blockDvdIndices_card_le hn hpp.pos
    exact le_trans h1 h2
  · -- non-small prime ⟹ valuation 0 (either non-prime, or prime ≥ k dividing no sqfree term).
    rw [if_neg hp]
    -- It suffices that `(SqfreeBlockProduct k n).factorization p = 0`.
    by_cases hpp : p.Prime
    · -- prime but `p ∉ primesBelow k` ⟹ `k ≤ p`; no squarefree term is divisible by `p`.
      have hkp : k ≤ p := by
        by_contra hlt
        push Not at hlt
        exact hp (Nat.mem_primesBelow.mpr ⟨hlt, hpp⟩)
      have hcount0 : #(BlockDvdIndices k n p) = 0 := by
        rw [Finset.card_eq_zero]
        unfold BlockDvdIndices
        rw [Finset.filter_eq_empty_iff]
        intro i hi
        unfold SqfreeBlockIndices at hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        exact sqfree_term_no_large_prime hn hPow hi.1 hi.2 hpp hkp
      have := sqfreeBlockProduct_factorization_le_count (k := k) (n := n) (p := p) hn
      rw [hcount0] at this
      omega
    · -- non-prime ⟹ valuation 0.
      rw [Nat.factorization_eq_zero_of_not_prime _ hpp]

/-- **Size form.** If `F k n` is powerful, the product of the squarefree block terms is at most
the small-prime capacity `∏_{p < k} p^{⌊k/p⌋+1}`. Immediate from the divisibility form via
`Nat.le_of_dvd`. -/
theorem powerful_sqfree_product_le_smooth_capacity {k n : ℕ} (hn : 1 ≤ n)
    (hPow : Powerful (F k n)) : SqfreeBlockProduct k n ≤ SmoothCapacity k :=
  Nat.le_of_dvd (smoothCapacity_pos k) (powerful_sqfree_product_dvd_smooth_capacity hn hPow)

/-! ## Counting form of the obstruction and explicit capacity bound -/

/-- Number of squarefree terms in the block. -/
def SqfreeBlockCount (k n : ℕ) : ℕ := (SqfreeBlockIndices k n).card

/-- The product of the squarefree block terms is at least `n ^ SqfreeBlockCount`. -/
lemma sqfreeBlockProduct_ge_pow {k n : ℕ} :
    n ^ SqfreeBlockCount k n ≤ SqfreeBlockProduct k n := by
  unfold SqfreeBlockCount SqfreeBlockProduct
  calc n ^ (SqfreeBlockIndices k n).card
        = ∏ _i ∈ SqfreeBlockIndices k n, n := by rw [Finset.prod_const]
    _ ≤ ∏ i ∈ SqfreeBlockIndices k n, (n + i) :=
        Finset.prod_le_prod' (fun i _ => Nat.le_add_right n i)

/-- Counting form of the squarefree-capacity obstruction. -/
theorem powerful_sqfree_count_capacity_bound {k n : ℕ}
    (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    n ^ SqfreeBlockCount k n ≤ SmoothCapacity k :=
  le_trans sqfreeBlockProduct_ge_pow (powerful_sqfree_product_le_smooth_capacity hn hPow)

/-- If the squarefree count is large enough to beat capacity, the block is not powerful. -/
theorem not_powerful_of_sqfree_capacity_exceeded {k n : ℕ}
    (hn : 1 ≤ n) (hcap : SmoothCapacity k < n ^ SqfreeBlockCount k n) :
    ¬ Powerful (F k n) := by
  intro hPow; have h := powerful_sqfree_count_capacity_bound hn hPow; omega

/-- The squarefree-capacity product is exactly `L k * P k`. -/
lemma smoothCapacity_eq_L_mul_P (k : ℕ) : SmoothCapacity k = L k * P k := by
  unfold SmoothCapacity L P
  calc ∏ p ∈ Nat.primesBelow k, p ^ (k / p + 1)
        = ∏ p ∈ Nat.primesBelow k, (p ^ (k / p) * p) := by
          apply Finset.prod_congr rfl; intro p _; rw [pow_succ]
    _ = (∏ p ∈ Nat.primesBelow k, p ^ (k / p)) * (∏ p ∈ Nat.primesBelow k, p) := by
          rw [Finset.prod_mul_distrib]

/-- `L k` divides `k!` (Legendre's first layer). -/
lemma L_dvd_factorial (k : ℕ) : L k ∣ Nat.factorial k := by
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (Nat.factorial_ne_zero k)]
  intro p
  unfold L
  rw [Nat.factorization_prod (fun q hq => by
    have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    rw [Finset.sum_eq_single p
      (fun q hq hqp => by
        have hqprime : q.Prime := Nat.prime_of_mem_primesBelow hq
        rw [Nat.Prime.factorization_pow hqprime, Finsupp.single_apply, if_neg hqp])
      (fun h => absurd hp h)]
    rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
    exact div_le_factorization_factorial hpp
  · rw [Finset.sum_eq_zero (fun q hq => by
      have hqprime : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqprime, Finsupp.single_apply, if_neg hne])]
    exact Nat.zero_le _

lemma L_le_factorial (k : ℕ) : L k ≤ Nat.factorial k :=
  Nat.le_of_dvd (Nat.factorial_pos k) (L_dvd_factorial k)

/-- Coarse explicit capacity bound: `SmoothCapacity k ≤ (4*k)^k`. -/
theorem smoothCapacity_le_four_mul_pow (k : ℕ) : SmoothCapacity k ≤ (4 * k) ^ k := by
  calc SmoothCapacity k = L k * P k := smoothCapacity_eq_L_mul_P k
    _ ≤ Nat.factorial k * P k := Nat.mul_le_mul_right _ (L_le_factorial k)
    _ ≤ k ^ k * 4 ^ k := Nat.mul_le_mul (Nat.factorial_le_pow k) (P_le_4_pow k)
    _ = (4 * k) ^ k := by rw [← Nat.mul_pow]; ring

/-- Fully explicit squarefree-count obstruction. -/
theorem not_powerful_of_sqfree_count_beats_fourk {k n : ℕ}
    (hn : 1 ≤ n) (hbeat : (4 * k) ^ k < n ^ SqfreeBlockCount k n) :
    ¬ Powerful (F k n) := by
  intro hPow
  have h1 := powerful_sqfree_count_capacity_bound hn hPow
  have h2 := smoothCapacity_le_four_mul_pow k
  omega

/-- A squarefree term with a prime factor `p ≥ k` rules out powerfulness. -/
theorem not_powerful_of_sqfree_term_large_prime {k n i p : ℕ}
    (hn : 1 ≤ n) (hi : i < k) (hsq : Squarefree (n + i))
    (hp : p.Prime) (hkp : k ≤ p) (hpdvd : p ∣ n + i) : ¬ Powerful (F k n) := by
  intro hPow
  exact sqfree_term_no_large_prime hn hPow hi hsq hp hkp hpdvd

/-- Existential version. -/
theorem not_powerful_of_exists_sqfree_term_large_prime {k n : ℕ}
    (hn : 1 ≤ n)
    (h : ∃ i < k, Squarefree (n + i) ∧ ∃ p, p.Prime ∧ k ≤ p ∧ p ∣ n + i) :
    ¬ Powerful (F k n) := by
  rcases h with ⟨i, hi, hsq, p, hp, hkp, hpdvd⟩
  exact not_powerful_of_sqfree_term_large_prime hn hi hsq hp hkp hpdvd

/-! ## Abstract squarefree-splice template -/

/-- A range predicate on which the squarefree count beats the deterministic capacity. This is the
external interface for a squarefree-counting input (e.g. Pandey's): it is **not** proved here, only
consumed. Mirrors the `PrimeInBlockOnRange` pattern of the abstract BHP splice. -/
def SqfreeCapacityBeatenOnRange (Range : ℕ → ℕ → Prop) : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n → Range k n →
    SmoothCapacity k < n ^ SqfreeBlockCount k n

/-- **Abstract squarefree splice.** On any range where the squarefree count beats the capacity, no
powerful block exists. The external squarefree-counting input enters only as the premise `hRange`;
no analytic number theory is formalized here. -/
theorem squarefree_range_not_powerful {Range : ℕ → ℕ → Prop}
    (hRange : SqfreeCapacityBeatenOnRange Range) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hR : Range k n) : ¬ Powerful (F k n) :=
  not_powerful_of_sqfree_capacity_exceeded hn (hRange k n hk hn hR)

end  -- noncomputable section

end Erdos137
