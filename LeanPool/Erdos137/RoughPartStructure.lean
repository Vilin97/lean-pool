/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Base
import LeanPool.Erdos137.TaoPoint

/-!
# Erdős Problem #137: term-level rough-part structure in a very bad interval

If the block product `F k n = n(n+1)⋯(n+k-1)` is powerful, then for each individual term `n+i`,
the part supported on primes `p ≥ k` is itself powerful. A prime `p ≥ k` divides at most one of the
`k` block factors, so powerfulness of the whole product forces `p^2 ∣ n+i`. This is the local
anatomy behind Tao's "very bad interval" language. No abc, no radical lower bound, no analytic
number theory.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-- The part of `m` supported on primes `< k`. -/
def SmoothPartBelow (k m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => p < k), p ^ m.factorization p

/-- The part of `m` supported on primes `p ≥ k` (written `¬ p < k` to pair with
`Finset.prod_filter_mul_prod_filter_not`). -/
def RoughPartAbove (k m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => ¬ p < k), p ^ m.factorization p

lemma smoothPartBelow_pos (k m : ℕ) : 1 ≤ SmoothPartBelow k m := by
  unfold SmoothPartBelow
  exact Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

lemma roughPartAbove_pos (k m : ℕ) : 1 ≤ RoughPartAbove k m := by
  unfold RoughPartAbove
  exact Finset.one_le_prod' fun p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

lemma roughPartAbove_ne_zero (k m : ℕ) : RoughPartAbove k m ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (roughPartAbove_pos k m)

/-- Term-level smooth/rough factorization: `SmoothPartBelow k m * RoughPartAbove k m = m`. -/
lemma smoothPartBelow_mul_roughPartAbove {k m : ℕ} (hm : m ≠ 0) :
    SmoothPartBelow k m * RoughPartAbove k m = m := by
  unfold SmoothPartBelow RoughPartAbove
  rw [Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

lemma roughPartAbove_dvd_self {k m : ℕ} (hm : m ≠ 0) : RoughPartAbove k m ∣ m := by
  conv_rhs => rw [← smoothPartBelow_mul_roughPartAbove (k := k) hm]
  exact dvd_mul_left _ _

/-- Factorization of the term-level rough part. -/
lemma factorization_roughPartAbove (k m p : ℕ) :
    (RoughPartAbove k m).factorization p =
      if p ∈ m.primeFactors.filter (fun q => ¬ q < k) then m.factorization p else 0 := by
  unfold RoughPartAbove
  rw [Nat.factorization_prod (by
    intro q hq
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)).ne_zero)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ m.primeFactors.filter (fun q => ¬ q < k)
  · rw [if_pos hp]
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)
    rw [Finset.sum_eq_single p]
    · rw [Nat.Prime.factorization_pow hpprime, Finsupp.single_apply, if_pos rfl]
    · intro q hq hqp
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)
      rw [Nat.Prime.factorization_pow hqprime, Finsupp.single_apply, if_neg hqp]
    · intro h; exact absurd hp h
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)
    have hqp : q ≠ p := by rintro rfl; exact hp hq
    rw [Nat.Prime.factorization_pow hqprime, Finsupp.single_apply, if_neg hqp]

/-- If a prime divides the rough part, it is a prime factor of `m` and is `≥ k`. -/
lemma prime_dvd_roughPartAbove_imp {k m p : ℕ} (hp : p.Prime) (hpdvd : p ∣ RoughPartAbove k m) :
    p ∈ m.primeFactors ∧ k ≤ p := by
  have hRne : RoughPartAbove k m ≠ 0 := roughPartAbove_ne_zero k m
  have hval_pos : 1 ≤ (RoughPartAbove k m).factorization p := by
    have hp1 : p ^ 1 ∣ RoughPartAbove k m := by simpa [pow_one] using hpdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp hRne).mp hp1
  by_contra hbad
  push Not at hbad
  have hnot : p ∉ m.primeFactors.filter (fun q => ¬ q < k) := by
    intro hmem
    have hpmem : p ∈ m.primeFactors := (Finset.mem_filter.mp hmem).1
    have hnotlt : ¬ p < k := (Finset.mem_filter.mp hmem).2
    exact hnotlt (hbad hpmem)
  have hfac := factorization_roughPartAbove k m p
  rw [if_neg hnot] at hfac
  omega

/-- **Rough part of each term is powerful in a very bad interval.** -/
theorem roughPartAbove_powerful_of_block_powerful {k n i : ℕ}
    (hn : 1 ≤ n) (hPow : Powerful (F k n)) (hi : i < k) :
    Powerful (RoughPartAbove k (n + i)) := by
  intro p hp hpdvdR
  have hsupport : p ∈ (n + i).primeFactors ∧ k ≤ p :=
    prime_dvd_roughPartAbove_imp (k := k) (m := n + i) hp hpdvdR
  have hpmem : p ∈ (n + i).primeFactors := hsupport.1
  have hkp : k ≤ p := hsupport.2
  have hpdvd_term : p ∣ n + i := Nat.dvd_of_mem_primeFactors hpmem
  have hbad : VeryBad k n := hPow
  have hp2_term : p ^ 2 ∣ n + i := veryBad_large_prime_sq hp hkp hi hn hbad hpdvd_term
  have hterm_ne : n + i ≠ 0 := by omega
  have hval_term : 2 ≤ (n + i).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hterm_ne).mp hp2_term
  have hrough_mem : p ∈ (n + i).primeFactors.filter (fun q => ¬ q < k) := by
    rw [Finset.mem_filter]; exact ⟨hpmem, by omega⟩
  have hval_rough : 2 ≤ (RoughPartAbove k (n + i)).factorization p := by
    rw [factorization_roughPartAbove k (n + i) p, if_pos hrough_mem]; exact hval_term
  have hRne : RoughPartAbove k (n + i) ≠ 0 := roughPartAbove_ne_zero k (n + i)
  exact (Nat.Prime.pow_dvd_iff_le_factorization hp hRne).mpr hval_rough

/-- Every term in a very bad interval = (`k`-smooth part) · (powerful `k`-rough part). -/
theorem term_decomposes_smooth_times_powerful_rough {k n i : ℕ}
    (hn : 1 ≤ n) (hPow : Powerful (F k n)) (hi : i < k) :
    SmoothPartBelow k (n + i) * RoughPartAbove k (n + i) = n + i
      ∧ Powerful (RoughPartAbove k (n + i)) := by
  have hterm_ne : n + i ≠ 0 := by omega
  exact ⟨smoothPartBelow_mul_roughPartAbove (k := k) hterm_ne,
    roughPartAbove_powerful_of_block_powerful hn hPow hi⟩

/-! ## Squarefree terms have trivial rough part -/

/-- A nonzero powerful divisor of a nonzero squarefree number is `1`.
A small reusable helper: if `d ∣ m`, `m` is squarefree, and `d` is powerful, then every prime
valuation of `d` is both `≥ 2` if nonzero (powerfulness) and `≤ 1` (since `d ∣ m` squarefree), so
all valuations of `d` vanish. -/
lemma powerful_dvd_squarefree_eq_one {d m : ℕ}
    (hdne : d ≠ 0) (hmne : m ≠ 0) (hdvd : d ∣ m) (hsq : Squarefree m) (hPow : Powerful d) :
    d = 1 := by
  apply Nat.eq_of_factorization_eq hdne (by decide : (1 : ℕ) ≠ 0)
  intro p
  have hzero : d.factorization p = 0 := by
    by_cases hp : p.Prime
    · by_contra hnonzero
      have hpos : 1 ≤ d.factorization p := by omega
      have hpdvd : p ∣ d := by
        have hp1 : p ^ 1 ∣ d := (Nat.Prime.pow_dvd_iff_le_factorization hp hdne).mpr hpos
        simpa [pow_one] using hp1
      have hp2d : p ^ 2 ∣ d := hPow p hp hpdvd
      have hge2 : 2 ≤ d.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hdne).mp hp2d
      have hd_le_m : d.factorization p ≤ m.factorization p :=
        (Nat.factorization_le_iff_dvd hdne hmne).mpr hdvd p
      have hm_le1 : m.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
      omega
    · exact Nat.factorization_eq_zero_of_not_prime d hp
  simpa using hzero

/-- **Squarefree term corollary.** In a powerful block, the `k`-rough part of a squarefree term is
trivial: if `F k n` is powerful and `n+i` is squarefree, then `n+i` has no prime factor `p ≥ k`, so
all of its prime support lies below `k`. -/
theorem roughPartAbove_eq_one_of_squarefree_term {k n i : ℕ}
    (hn : 1 ≤ n) (hPow : Powerful (F k n)) (hi : i < k) (hsq : Squarefree (n + i)) :
    RoughPartAbove k (n + i) = 1 := by
  have hterm_ne : n + i ≠ 0 := by omega
  exact powerful_dvd_squarefree_eq_one
    (roughPartAbove_ne_zero k (n + i)) hterm_ne
    (roughPartAbove_dvd_self (k := k) hterm_ne) hsq
    (roughPartAbove_powerful_of_block_powerful hn hPow hi)

end -- noncomputable section
end Erdos137
