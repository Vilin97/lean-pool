/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness

/-!
# Erdős Problem #137: shared `g`-independent base layer

This file collects the low-level, **`g`-independent** helpers shared by every block route
(`JointFiniteness` `g = 3`, `SpliceFiniteness` `g = 5`, and the parametric `BlockFramework`).
It sits directly above `Finiteness` and below `BlockFramework`, so the generic framework and the
concrete `g = 3, 5` instances all derive from one base.

Two groups of helpers live here:

* **Block-tiling / radical algebra** (from the old `JointFiniteness`): the multiplicativity of `F`
  (`F_add`, `F_dvd_F_add`), the radical's prime support and factorization (`rad_dvd_self`,
  `primeFactors_rad`, `factorization_rad`, `rad_dvd_rad_of_dvd`), the elementary size bounds
  `le_F`, `le_F'`, `pow_le_F`, the interval-divisor counts (`Ioc_dvd_count`, `Ioc_dvd_le`), and the
  Legendre `i = 1` term `div_le_factorization_factorial`.
* **The smooth/rough split** (from the old `SmoothRefinement`): the primorial-type quantities
  `P`, `L`, the split `Ssmooth`/`Rrough`, and the smooth refinement
  `rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2` (`smooth_refinement`).

None of these mentions any block length `g` (or the concrete `B`/`W`/`overlap` of a route), so they
are proved once here and reused verbatim downstream.
-/

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## Basic facts about `F` and block tilings -/

/-- `F` splits as a product of an initial block and a shifted tail:
`F (a + b) n = F a n * F b (n + a)`. -/
lemma F_add (a b n : ℕ) : F (a + b) n = F a n * F b (n + a) := by
  unfold F
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  ring_nf

/-- `F a n` divides `F (a + b) n`. -/
lemma F_dvd_F_add (a b n : ℕ) : F a n ∣ F (a + b) n := by
  rw [F_add]; exact Dvd.intro _ rfl

/-! ## The radical's prime support and factorization (general facts) -/

/-- `rad m ∣ m` for `m ≠ 0`. -/
lemma rad_dvd_self {m : ℕ} (_hm : m ≠ 0) : rad m ∣ m := by
  unfold rad; rw [Nat.support_factorization]; exact Nat.prod_primeFactors_dvd _

/-- The prime support of `rad m` is exactly `m.primeFactors` (for `m ≠ 0`). -/
lemma primeFactors_rad {m : ℕ} (hm : m ≠ 0) : (rad m).primeFactors = m.primeFactors := by
  apply Finset.Subset.antisymm
  · exact Nat.primeFactors_mono (rad_dvd_self hm) hm
  · intro p hp
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    -- p ∈ support of rad m since p ∈ m.primeFactors = support of the product
    have : p ∣ rad m := by
      unfold rad; rw [Nat.support_factorization]
      exact Finset.dvd_prod_of_mem _ hp
    exact Nat.mem_primeFactors.mpr ⟨hpprime, this, Nat.one_le_iff_ne_zero.mp (rad_pos m)⟩

/-- **General fact:** `rad m` is squarefree, so `(rad m).factorization p = 1` if
`p ∈ m.primeFactors`, else `0`. -/
lemma factorization_rad {m : ℕ} (hm : m ≠ 0) (p : ℕ) :
    (rad m).factorization p = if p ∈ m.primeFactors then 1 else 0 := by
  by_cases hp : p ∈ m.primeFactors
  · simp only [hp, if_true]
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    unfold rad
    rw [Nat.support_factorization]
    rw [Nat.factorization_prod_apply (by
      intro q hq; exact (Nat.prime_of_mem_primeFactors hq).ne_zero)]
    rw [Finset.sum_eq_single p]
    · exact Nat.Prime.factorization_self hpprime
    · simp_all
    · intro h; exact absurd hp h
  · simp only [hp, if_false]
    by_cases hpp : p.Prime
    · rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      apply hp
      exact Nat.mem_primeFactors.mpr
        ⟨hpp, dvd_trans hdvd (rad_dvd_self hm), hm⟩
    · exact Nat.factorization_eq_zero_of_not_prime _ hpp

/-- `rad` is monotone under divisibility: `a ∣ b`, `b ≠ 0` ⟹ `rad a ∣ rad b`
(their prime supports are nested). -/
lemma rad_dvd_rad_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : rad a ∣ rad b := by
  unfold rad
  rw [Nat.support_factorization, Nat.support_factorization]
  apply Finset.prod_dvd_prod_of_subset
  exact Nat.primeFactors_mono hab hb

/-! ## Elementary size bounds on `F k n` -/

/-- `n ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the first factor is `n`, the rest are `≥ 1`). -/
lemma le_F {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : n ≤ F k n := by
  have hmem : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + 0) ∣ F k n := by
    rw [F]; exact Finset.dvd_prod_of_mem _ hmem
  simpa using Nat.le_of_dvd (F_pos hn) hdvd

/-- `k ≤ F k n` for `k ≥ 1`, `n ≥ 1` (the last factor `n+k-1 ≥ k` divides the product). -/
lemma le_F' {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : k ≤ F k n := by
  have hmem : (k - 1) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hdvd : (n + (k - 1)) ∣ F k n := by
    rw [F]; exact Finset.dvd_prod_of_mem _ hmem
  have : k ≤ n + (k - 1) := by omega
  exact le_trans this (Nat.le_of_dvd (F_pos hn) hdvd)

/-- **Elementary lower bound `n^k ≤ F k n`.** Each of the `k` factors of `F k n` is `≥ n`. This is
the size input (`log F ≥ k log n`) that turns `W ≤ k^k` into the clean `n > k^6` threshold. -/
theorem pow_le_F {k n : ℕ} : n ^ k ≤ F k n := by
  unfold F
  calc n ^ k = ∏ _i ∈ Finset.range k, n := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range k, (n + i) :=
        Finset.prod_le_prod' (fun i _ => Nat.le_add_right n i)

/-! ## Counting multiples of a prime in an interval (for the overlap bound) -/

/-- **Exact count** of multiples of `p` in `(a, b]`: `#{x ∈ Ioc a b | p ∣ x} = b/p − a/p`. -/
theorem Ioc_dvd_count (a b p : ℕ) (hab : a ≤ b) :
    #{x ∈ Finset.Ioc a b | p ∣ x} = b / p - a / p := by
  have h1 : #{x ∈ Finset.Ioc 0 b | p ∣ x} = b / p := Nat.Ioc_filter_dvd_card_eq_div b p
  have h2 : #{x ∈ Finset.Ioc 0 a | p ∣ x} = a / p := Nat.Ioc_filter_dvd_card_eq_div a p
  have hsplit : #{x ∈ Finset.Ioc 0 b | p ∣ x}
      = #{x ∈ Finset.Ioc 0 a | p ∣ x} + #{x ∈ Finset.Ioc a b | p ∣ x} := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab]
    · apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]; simp
  omega

/-- The number of multiples of `p` in an interval of length `L` is at most `⌊L/p⌋ + 1`. -/
theorem Ioc_dvd_le (a L p : ℕ) (hp : 1 ≤ p) :
    #{x ∈ Finset.Ioc a (a + L) | p ∣ x} ≤ L / p + 1 := by
  rw [Ioc_dvd_count a (a + L) p (Nat.le_add_right a L)]
  have hpp : 0 < p := hp
  have h6 : (a + L) / p = (a / p + L / p) + (a % p + L % p) / p := by
    have h5 : (a + L) = p * (a / p + L / p) + (a % p + L % p) := by
      have hma : p * (a / p + L / p) = p * (a / p) + p * (L / p) := by ring
      have h1 : p * (a / p) + a % p = a := Nat.div_add_mod a p
      have h2 : p * (L / p) + L % p = L := Nat.div_add_mod L p
      rw [hma]; omega
    rw [h5, Nat.mul_add_div hpp]
  have h7 : (a % p + L % p) / p ≤ 1 := by
    have h3 : a % p < p := Nat.mod_lt _ hpp
    have h4 : L % p < p := Nat.mod_lt _ hpp
    rw [Nat.div_le_iff_le_mul_add_pred hpp]; omega
  rw [Nat.sub_le_iff_le_add, h6]; omega

/-- For a prime `p`, `⌊k/p⌋ ≤ (k!).factorization p` (the `i = 1` term of Legendre's formula). -/
lemma div_le_factorization_factorial {k p : ℕ} (hp : p.Prime) :
    k / p ≤ (Nat.factorial k).factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p k))]
  by_cases hpk : 1 ≤ Nat.log p k
  · have hmem : 1 ∈ Finset.Ico 1 (Nat.log p k + 1) := by
      simp only [Finset.mem_Ico]; omega
    calc k / p = k / p ^ 1 := by rw [pow_one]
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p k + 1), k / p ^ i :=
          Finset.single_le_sum (f := fun i => k / p ^ i) (by intro i _; positivity) hmem
  · have hlt : k < p := by
      by_contra hc; push Not at hc
      exact absurd (Nat.log_pos hp.one_lt hc) (by omega)
    rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _

/-! ## The primorial-type quantities `P k` and `L k` -/

/-- `P k = ∏_{p ∈ primesBelow k} p` — the product of the primes `< k` (the primorial of `k`). -/
def P (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p

/-- `L k = ∏_{p ∈ primesBelow k} p ^ (k / p)` — the smooth-part lower bound (`L ∣ k!` by Legendre,
`L = (k!)^{1-o(1)}`). -/
def L (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow k, p ^ (k / p)

lemma P_pos (k : ℕ) : 1 ≤ P k :=
  Finset.one_le_prod' fun _p hp => (Nat.prime_of_mem_primesBelow hp).one_le

lemma L_pos (k : ℕ) : 1 ≤ L k :=
  Finset.one_le_prod' fun _p hp => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos

lemma L_ne_zero (k : ℕ) : L k ≠ 0 := Nat.one_le_iff_ne_zero.mp (L_pos k)

/-- `P k ≤ 4 ^ k` (Mathlib's `primorial_le_four_pow`; `primesBelow k` are the primes `≤ k - 1`,
a subset of the primes counted by `primorial k`). -/
lemma P_le_4_pow (k : ℕ) : P k ≤ 4 ^ k := by
  have hsub : Nat.primesBelow k ⊆ {p ∈ Finset.range (k + 1) | p.Prime} := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.2⟩
  have hdvd : P k ∣ primorial k := by
    unfold P primorial
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  calc P k ≤ primorial k := Nat.le_of_dvd (primorial_pos k) hdvd
    _ ≤ 4 ^ k := primorial_le_four_pow k

/-! ## The smooth/rough split of `F k n` -/

/-- The smooth part `S k n = ∏_{p | F, p < k} p ^ v_p(F)`. -/
def Ssmooth (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (· < k), p ^ (F k n).factorization p

/-- The rough part `R k n = ∏_{p | F, ¬ p < k} p ^ v_p(F)`. -/
def Rrough (k n : ℕ) : ℕ :=
  ∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p ^ (F k n).factorization p

/-- `S · R = F` for `n ≥ 1`. -/
lemma Ssmooth_mul_Rrough {k n : ℕ} (hn : 1 ≤ n) : Ssmooth k n * Rrough k n = F k n := by
  unfold Ssmooth Rrough
  rw [Finset.prod_filter_mul_prod_filter_not]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self (F_ne_zero hn)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]

lemma Ssmooth_pos {k n : ℕ} (_hn : 1 ≤ n) : 1 ≤ Ssmooth k n :=
  Finset.one_le_prod' fun _p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

lemma Rrough_pos {k n : ℕ} (_hn : 1 ≤ n) : 1 ≤ Rrough k n :=
  Finset.one_le_prod' fun _p hp =>
    Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hp)).pos

/-! ## Bound on the smooth radical: `rad(S)^2 ≤ P^2` -/

/-- `∏_{p | F, p < k} p ∣ P k`: the smooth prime factors are a subset of `primesBelow k`. -/
lemma smooth_rad_dvd_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ∣ P k := by
  unfold P
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [Nat.mem_primesBelow]
  exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩

/-- `∏_{p | F, p < k} p ≤ P k`. -/
lemma smooth_rad_le_P {k n : ℕ} :
    (∏ p ∈ (F k n).primeFactors.filter (· < k), p) ≤ P k :=
  Nat.le_of_dvd (P_pos k) smooth_rad_dvd_P

/-! ## Bound on the rough part: `∏_{p | F, ¬ p<k} p^2 ≤ R` (powerful) -/

/-- For powerful `F` (`≠ 0`), `∏_{p|F, ¬p<k} p^2 ≤ R k n`: each such prime has `v_p(F) ≥ 2`. -/
lemma rough_sq_le {k n : ℕ} (hF : F k n ≠ 0) (hP : Powerful (F k n)) :
    (∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p) ^ 2 ≤ Rrough k n := by
  unfold Rrough
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  have hpdvd : p ∣ F k n := Nat.dvd_of_mem_primeFactors hp.1
  have h2 : p ^ 2 ∣ F k n := hP p hpp hpdvd
  have hle : 2 ≤ (F k n).factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hpp hF).mp h2
  exact Nat.pow_le_pow_right hpp.pos hle

/-! ## The smooth lower bound: `L ∣ S` and `L ≤ S`

We need `v_p(F) ≥ ⌊k/p⌋` for every prime `p < k`. Among the `k` consecutive integers
`n, …, n+k-1` (the multiset `(n-1, n-1+k]` shifted), at least `⌊k/p⌋` are divisible by `p`, and
each such factor contributes at least `1` to `v_p(F)`. -/

/-- The count of multiples of `p` among the `k` consecutive integers `n, …, n+k-1` is at least
`⌊k/p⌋`. Stated via the exact `Ioc` count:
`#{x ∈ (n-1, n-1+k] | p ∣ x} = (n-1+k)/p − (n-1)/p ≥ k/p`. -/
lemma div_le_factorization_F {k n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) :
    k / p ≤ (F k n).factorization p := by
  -- v_p(F) = ∑_{i<k} v_p(n+i) ≥ #{i<k | p ∣ n+i} = #{x ∈ (n-1, n-1+k] | p∣x} ≥ k/p.
  set D : Finset ℕ := (Finset.range k).filter (fun i => p ∣ (n + i)) with hD
  -- Lower bound: each multiple contributes ≥ 1.
  have hfac : (F k n).factorization p = ∑ i ∈ Finset.range k, (n + i).factorization p := by
    unfold F
    rw [Nat.factorization_prod (by intro i _; omega)]
    rw [Finset.sum_apply']
  have hcount_le : #D ≤ (F k n).factorization p := by
    rw [hfac]
    calc #D = ∑ i ∈ D, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ D, (n + i).factorization p := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hD, Finset.mem_filter] at hi
          have hne : n + i ≠ 0 := by omega
          exact (Nat.Prime.pow_dvd_iff_le_factorization hp hne).mp (by simpa using hi.2)
      _ ≤ ∑ i ∈ Finset.range k, (n + i).factorization p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (by intro i _ _; positivity)
  -- Relate #D to the Ioc count of multiples.
  have hbij : #D = #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} := by
    apply Finset.card_bij (fun i _ => n + i)
    · intro i hi
      rw [hD, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hi.2⟩
    · intro i hi j hj h; omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx
      obtain ⟨⟨hx1, hx2⟩, hxdvd⟩ := hx
      refine ⟨x - n, ?_, ?_⟩
      · rw [hD, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [show n + (x - n) = x by omega]; exact hxdvd
      · omega
  have hcount : #{x ∈ Finset.Ioc (n - 1) (n - 1 + k) | p ∣ x} = (n - 1 + k) / p - (n - 1) / p :=
    Ioc_dvd_count (n - 1) (n - 1 + k) p (by omega)
  -- ⌊(a+k)/p⌋ − ⌊a/p⌋ ≥ ⌊k/p⌋.
  have hkey : k / p ≤ (n - 1 + k) / p - (n - 1) / p := by
    have h1 : (n - 1) / p + k / p ≤ (n - 1 + k) / p := Nat.add_div_le_add_div (n - 1) k p
    omega
  omega

/-- `L k ∣ F k n` for `n ≥ 1`: `v_p(L) = ⌊k/p⌋ ≤ v_p(F)` for every prime `p < k`. -/
lemma L_dvd_F {k n : ℕ} (hn : 1 ≤ n) : L k ∣ F k n := by
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)]
  intro p
  rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
  rw [Nat.factorization_prod (fun q hq => by
    simp_all)]
  rw [Finset.sum_apply']
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hsingle : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p)
        = (p ^ (k / p)).factorization p :=
      Finset.sum_eq_single p
        (fun q hq hqp => by
          have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
          rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hqp])
        (fun h => absurd hp h)
    rw [hsingle, Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
    exact div_le_factorization_F hn hpp
  · have hzero : (∑ q ∈ Nat.primesBelow k, (q ^ (k / q)).factorization p) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]
    rw [hzero]; exact Nat.zero_le _

/-- `L k ≤ S k n` (the smooth part): `L ∣ F` and `L`'s primes are exactly the smooth primes, so in
fact `L ∣ S`; we only need `L ≤ S`. -/
lemma L_le_smooth {k n : ℕ} (hn : 1 ≤ n) : L k ∣ Ssmooth k n := by
  -- L ∣ F and all prime factors of L are < k, so L ∣ S (the < k part of F).
  rw [← Nat.factorization_le_iff_dvd (L_ne_zero k) (Nat.one_le_iff_ne_zero.mp (Ssmooth_pos hn))]
  intro p
  have hLdvdF : L k ∣ F k n := L_dvd_F hn
  by_cases hp : p ∈ Nat.primesBelow k
  · have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hplt : p < k := Nat.lt_of_mem_primesBelow hp
    -- v_p(L) ≤ v_p(F) = v_p(S) since p < k.
    have hvLF : (L k).factorization p ≤ (F k n).factorization p :=
      (Nat.factorization_le_iff_dvd (L_ne_zero k) (F_ne_zero hn)).mpr hLdvdF p
    have hvFS : (F k n).factorization p ≤ (Ssmooth k n).factorization p := by
      by_cases hpdvd : p ∈ (F k n).primeFactors
      · unfold Ssmooth
        rw [Nat.factorization_prod (fun q hq => by
          have := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter _ hq)).pos; positivity)]
        rw [Finset.sum_apply']
        have hmem : p ∈ (F k n).primeFactors.filter (· < k) := by
          rw [Finset.mem_filter]; exact ⟨hpdvd, hplt⟩
        rw [Finset.sum_eq_single p
              (fun q hq hqp => by
                simp_all)
              (fun h => absurd hmem h)]
        rw [Nat.Prime.factorization_pow hpp, Finsupp.single_apply, if_pos rfl]
      · -- p ∤ F ⇒ v_p(F) = 0
        rw [Nat.factorization_eq_zero_of_not_dvd]
        · exact Nat.zero_le _
        · intro hdvd; exact hpdvd (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, F_ne_zero hn⟩)
    exact le_trans hvLF hvFS
  · have hzero : (L k).factorization p = 0 := by
      rw [show L k = ∏ q ∈ Nat.primesBelow k, q ^ (k / q) from rfl]
      rw [Nat.factorization_prod (fun q hq => by
        have := (Nat.prime_of_mem_primesBelow hq).pos; positivity)]
      rw [Finset.sum_apply']
      apply Finset.sum_eq_zero
      intro q hq
      have hqp' : q.Prime := Nat.prime_of_mem_primesBelow hq
      have hne : q ≠ p := by rintro rfl; exact hp hq
      rw [Nat.Prime.factorization_pow hqp', Finsupp.single_apply, if_neg hne]
    rw [hzero]; exact Nat.zero_le _

/-! ## `rad (F k n)` factored through the smooth/rough split -/

/-- `rad (F k n) = (∏_{p|F, p<k} p) · (∏_{p|F, ¬p<k} p)`. -/
lemma rad_smooth_rough_split (k n : ℕ) :
    rad (F k n)
      = (∏ p ∈ (F k n).primeFactors.filter (· < k), p)
        * (∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p) := by
  unfold rad
  rw [Nat.support_factorization]
  rw [Finset.prod_filter_mul_prod_filter_not]

/-! ## The smooth refinement -/

/-- **Smooth-part radical refinement.** For `n ≥ 1` and a **powerful** `F k n`,
`rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2`. Equivalently `rad(F)^2 ≤ (P^2 / L) · F`; this sharpens
the crude `rad(F)^2 ≤ F` (`powerful_rad_sq_le`) by the smooth gain `L`. -/
theorem smooth_refinement {k n : ℕ} (hn : 1 ≤ n) (hP : Powerful (F k n)) :
    rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2 := by
  have hF : F k n ≠ 0 := F_ne_zero hn
  set sm : ℕ := ∏ p ∈ (F k n).primeFactors.filter (· < k), p with hsm
  set rg : ℕ := ∏ p ∈ (F k n).primeFactors.filter (fun p => ¬ p < k), p with hrg
  -- rad(F)^2 = sm^2 * rg^2
  have hradsq : rad (F k n) ^ 2 = sm ^ 2 * rg ^ 2 := by
    rw [rad_smooth_rough_split, mul_pow]
  -- sm^2 ≤ P^2
  have hsmP : sm ^ 2 ≤ P k ^ 2 := Nat.pow_le_pow_left smooth_rad_le_P 2
  -- rg^2 ≤ R
  have hrgR : rg ^ 2 ≤ Rrough k n := rough_sq_le hF hP
  -- L ∣ S, so L ≤ S
  have hLS : L k ≤ Ssmooth k n := Nat.le_of_dvd (Ssmooth_pos hn) (L_le_smooth hn)
  -- L * R ≤ S * R = F
  have hLR_F : L k * Rrough k n ≤ F k n := by
    calc L k * Rrough k n ≤ Ssmooth k n * Rrough k n :=
            Nat.mul_le_mul_right _ hLS
      _ = F k n := Ssmooth_mul_Rrough hn
  -- Assemble:  rad(F)^2 * L = sm^2 * (rg^2 * L) ≤ P^2 * (R * L) ≤ P^2 * F.
  calc rad (F k n) ^ 2 * L k
      = sm ^ 2 * (rg ^ 2 * L k) := by rw [hradsq]; ring
    _ ≤ P k ^ 2 * (Rrough k n * L k) := by
        apply Nat.mul_le_mul hsmP
        exact Nat.mul_le_mul_right _ hrgR
    _ = P k ^ 2 * (L k * Rrough k n) := by ring
    _ ≤ P k ^ 2 * F k n := Nat.mul_le_mul_left _ hLR_F
    _ = F k n * P k ^ 2 := by ring

end  -- noncomputable section

end Erdos137
