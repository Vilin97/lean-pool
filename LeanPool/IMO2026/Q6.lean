/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2026 Question 6 solution

This file proves the eventual translation-periodicity theorem for the
common-factor sequence from Question 6.
-/

namespace IMO2026Q6

/-- The predicate stating that `a : ℕ → ℕ` (0-indexed) is a sequence satisfying Definition 1:
each term exceeds `1`, and each subsequent term is the smallest integer strictly larger than the
previous one that shares a common factor with every earlier term. -/
def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

/-- `Good a n b` says that the integer `b` shares a common factor (gcd > 1) with every
term `a 0, a 1, …, a n` produced so far. This is the "admissibility" predicate: `a (n+1)`
is the *least* integer `> a n` that is `n`-good. -/
def Good (a : ℕ → ℕ) (n : ℕ) (b : ℕ) : Prop := ∀ i ≤ n, 1 < Nat.gcd b (a i)

/-- The sequence is strictly increasing (immediate from the validity condition
`a n < a (n+1)`). Consequently it is unbounded on `ℕ`. -/
theorem IsValidSeq.strictMono {a : ℕ → ℕ} (ha : IsValidSeq a) : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (ha.2 n).1

/-- Goodness is monotone decreasing in the index `n`: if `b` shares a factor with all of
`a 0, …, a (n+1)`, then in particular it does with all of `a 0, …, a n`. Directly from the
definition (fewer constraints). -/
theorem Good.mono {a : ℕ → ℕ} {n : ℕ} {b : ℕ} (h : Good a (n + 1) b) : Good a n b := by
  intro i hi
  exact h i (Nat.le_succ_of_le hi)

/-- Characterization of the successor as the least good integer above `a n`:
`a (n+1)` is `n`-good, is `> a n`, and no integer strictly between `a n` and `a (n+1)`
is `n`-good. This just repackages the definition of `IsValidSeq` in terms of `Good`. -/
theorem IsValidSeq.succ_least_good {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) :
    a n < a (n + 1) ∧ Good a n (a (n + 1)) ∧
      (∀ b, a n < b → b < a (n + 1) → ¬ Good a n b) := by
  obtain ⟨hlt, hgcd, hmin⟩ := ha.2 n
  refine ⟨hlt, hgcd, ?_⟩
  intro b hb1 hb2 hgood
  obtain ⟨i, hi, hcop⟩ := hmin b hb1 hb2
  have := hgood i hi
  rw [hcop] at this
  exact (lt_irrefl 1) this

/-- `1 < gcd b x` iff some prime divides both `b` and `x`. -/
lemma one_lt_gcd_iff_exists_prime_dvd {b x : ℕ} (hx : 0 < x) :
    1 < Nat.gcd b x ↔ ∃ p, Nat.Prime p ∧ p ∣ b ∧ p ∣ x := by
  have hgpos : 0 < Nat.gcd b x := Nat.gcd_pos_of_pos_right b hx
  constructor
  · intro h
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (n := Nat.gcd b x) (by omega)
    exact ⟨p, hp, hpg.trans (Nat.gcd_dvd_left b x), hpg.trans (Nat.gcd_dvd_right b x)⟩
  · rintro ⟨p, hp, hpb, hpx⟩
    have hdvd : p ∣ Nat.gcd b x := Nat.dvd_gcd hpb hpx
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hdvd)

/-- If every prime divisor of `x` divides `M` and `M ∣ L`, then the gcd constraint at
`x` is invariant under translation by `L`. -/
lemma gcd_constraint_periodic {M L x b : ℕ} (hxpos : 0 < x) (hML : M ∣ L)
    (hx : ∀ p, Nat.Prime p → p ∣ x → p ∣ M) :
    1 < Nat.gcd (b + L) x ↔ 1 < Nat.gcd b x := by
  rw [one_lt_gcd_iff_exists_prime_dvd hxpos, one_lt_gcd_iff_exists_prime_dvd hxpos]
  constructor
  · rintro ⟨p, hp, hpbL, hpx⟩
    refine ⟨p, hp, ?_, hpx⟩
    have hpL : p ∣ L := (hx p hp hpx).trans hML
    have : p ∣ (b + L) - L := Nat.dvd_sub hpbL hpL
    simpa using this
  · rintro ⟨p, hp, hpb, hpx⟩
    have hpL : p ∣ L := (hx p hp hpx).trans hML
    exact ⟨p, hp, Nat.dvd_add hpb hpL, hpx⟩

/-- Every term of a valid sequence is `n`-good for every `n` (pairwise gcd > 1). -/
lemma pairwise_gcd {a : ℕ → ℕ} (ha : IsValidSeq a) :
    ∀ i j, 1 < Nat.gcd (a i) (a j) := by
  -- symmetric; prove for i ≤ j then symmetrize
  have key : ∀ j i, i ≤ j → 1 < Nat.gcd (a i) (a j) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      interval_cases i
      have := ha.1 0
      rw [Nat.gcd_self]; exact this
    | succ m ih =>
      intro i hi
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · -- i ≤ m, use validity: 1 < gcd (a (m+1)) (a i), then gcd_comm
        have hle : i ≤ m := Nat.lt_succ_iff.mp h
        have := (ha.2 m).2.1 i hle
        rwa [Nat.gcd_comm] at this
      · -- i = m+1
        have : i = m + 1 := le_antisymm hi h
        subst this
        rw [Nat.gcd_self]; exact ha.1 (m + 1)
  intro i j
  rcases le_total i j with h | h
  · exact key j i h
  · rw [Nat.gcd_comm]; exact key i j h

lemma term_good_all {a : ℕ → ℕ} (ha : IsValidSeq a) :
    ∀ k n, Good a n (a k) := by
  intro k n i _
  exact pairwise_gcd ha k i

/-- The prefix product `∏_{i≤N} a i`, used as a translation modulus. -/
def prefixMod (a : ℕ → ℕ) (N : ℕ) : ℕ := ∏ i ∈ Finset.range (N + 1), a i

lemma prime_dvd_prefixMod {a : ℕ → ℕ} {N i p : ℕ} (hi : i ≤ N)
    (_hp : Nat.Prime p) (hpa : p ∣ a i) : p ∣ prefixMod a N := by
  unfold prefixMod
  have hmem : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  exact hpa.trans (Finset.dvd_prod_of_mem a hmem)

lemma prefixMod_pos {a : ℕ → ℕ} (ha : IsValidSeq a) (N : ℕ) : 0 < prefixMod a N := by
  unfold prefixMod
  apply Finset.prod_pos
  intro i _
  have := ha.1 i; omega

/-- Every prime dividing a prefix term divides the prefix modulus. -/
lemma prefixMod_absorbs {a : ℕ → ℕ} (N : ℕ) :
    ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ prefixMod a N := by
  intro i hi p hp hpa
  exact prime_dvd_prefixMod hi hp hpa

/-- If `M ∣ L` and `M` absorbs all prefix primes, `Good a N` is invariant under `+L`. -/
lemma Good_periodic_of_modulus {a : ℕ → ℕ} (ha : IsValidSeq a) {N M L : ℕ} (hML : M ∣ L)
    (hM : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M) :
    ∀ b, Good a N (b + L) ↔ Good a N b := by
  intro b
  unfold Good
  constructor
  · intro h i hi
    exact (gcd_constraint_periodic (by have := ha.1 i; omega) hML (hM i hi)).mp (h i hi)
  · intro h i hi
    exact (gcd_constraint_periodic (by have := ha.1 i; omega) hML (hM i hi)).mpr (h i hi)

/-- Translation invariance of `Good a j` for EVERY index `j`, given stabilisation and a
modulus `M ∣ L` that absorbs all prefix primes.  For `j ≥ N` we use the stabilisation to
`Good a N`; for `j < N` all clauses `i ≤ j < N` are absorbed by `hM` directly. -/
lemma Good_periodic_all {a : ℕ → ℕ} (ha : IsValidSeq a) {N M L : ℕ} (hML : M ∣ L)
    (hstab : ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b)
    (hM : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M) :
    ∀ j b, Good a j (b + L) ↔ Good a j b := by
  intro j b
  rcases Nat.lt_or_ge j N with hj | hj
  · constructor
    · intro h i hi
      have hiN : i ≤ N := le_of_lt (lt_of_le_of_lt hi hj)
      exact (gcd_constraint_periodic (by have := ha.1 i; omega) hML (hM i hiN)).mp (h i hi)
    · intro h i hi
      have hiN : i ≤ N := le_of_lt (lt_of_le_of_lt hi hj)
      exact (gcd_constraint_periodic (by have := ha.1 i; omega) hML (hM i hiN)).mpr (h i hi)
  · rw [hstab j hj (b + L), hstab j hj b]
    exact Good_periodic_of_modulus ha hML hM b

/-- Every positive multiple of `a 0` is `n`-good.  Because each `a i` (`i ≤ n`) shares a
prime with `a 0` (pairwise gcd > 1), any multiple of `a 0` shares that prime with `a i`. -/
lemma mul_a0_good {a : ℕ → ℕ} (ha : IsValidSeq a) (n k : ℕ) :
    Good a n (k * a 0) := by
  intro i _
  have hpos0 : 0 < a 0 := by have := ha.1 0; omega
  have hposi : 0 < a i := by have := ha.1 i; omega
  -- some prime p divides both a i and a 0 (pairwise gcd > 1)
  have hgcd : 1 < Nat.gcd (a i) (a 0) := pairwise_gcd ha i 0
  obtain ⟨p, hp, hpai, hpa0⟩ := (one_lt_gcd_iff_exists_prime_dvd hpos0).mp hgcd
  -- p ∣ a i, p ∣ a 0 ⟹ p ∣ k * a 0, so gcd (k*a0) (a i) > 1
  refine (one_lt_gcd_iff_exists_prime_dvd hposi).mpr ⟨p, hp, ?_, hpai⟩
  exact Dvd.dvd.mul_left hpa0 k

/-- **Bounded gaps.**  The consecutive differences are bounded by `a 0`. -/
lemma gaps_bounded {a : ℕ → ℕ} (ha : IsValidSeq a) (n : ℕ) : a (n + 1) - a n ≤ a 0 := by
  have hpos0 : 0 < a 0 := by have := ha.1 0; omega
  obtain ⟨hlt, hgood, hmin⟩ := ha.succ_least_good n
  -- least multiple of a 0 exceeding a n : k = a n / a 0 + 1
  set k := a n / a 0 + 1 with hk
  have hdivle : a 0 * (a n / a 0) ≤ a n := Nat.mul_div_le (a n) (a 0)
  have hdivlt : a n < a 0 * (a n / a 0) + a 0 := by
    have hmod := Nat.div_add_mod (a n) (a 0)
    have hmodlt : a n % a 0 < a 0 := Nat.mod_lt _ hpos0
    omega
  have hgt : a n < k * a 0 := by
    rw [hk]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a n / a 0) (a 0)]; omega
  have hle : k * a 0 ≤ a n + a 0 := by
    rw [hk, Nat.add_mul, Nat.one_mul, Nat.mul_comm (a n / a 0) (a 0)]; omega
  have hgood' : Good a n (k * a 0) := mul_a0_good ha n k
  have hbound : a (n + 1) ≤ k * a 0 := by
    by_contra hcon
    push Not at hcon
    exact hmin (k * a 0) hgt hcon hgood'
  omega

/-- The finite set of primes `≤ a 0`. -/
def smallPrimes (a : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (a 0 + 1)).filter Nat.Prime

/-- The "small support" of `a i`: the primes `≤ a 0` dividing `a i`. -/
def ssupp (a : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  (a i).primeFactors ∩ smallPrimes a

lemma mem_smallPrimes {a : ℕ → ℕ} {p : ℕ} :
    p ∈ smallPrimes a ↔ p ≤ a 0 ∧ Nat.Prime p := by
  unfold smallPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma mem_ssupp {a : ℕ → ℕ} {i : ℕ} (hai : a i ≠ 0) {p : ℕ} :
    p ∈ ssupp a i ↔ (p ≤ a 0 ∧ Nat.Prime p ∧ p ∣ a i) := by
  unfold ssupp
  rw [Finset.mem_inter, mem_smallPrimes, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hd, _⟩, hle, _⟩; exact ⟨hle, hp, hd⟩
  · rintro ⟨hle, hp, hd⟩
    exact ⟨⟨hp, hd, hai⟩, hle, hp⟩

/-- `ssupp a i` is a subset of the fixed finite set `smallPrimes a`, hence the map
`ssupp a` has finite range in the finite lattice `(smallPrimes a).powerset`. -/
lemma ssupp_subset {a : ℕ → ℕ} (i : ℕ) : ssupp a i ⊆ smallPrimes a := by
  unfold ssupp; exact Finset.inter_subset_right

/-- **Small-support cover (finite-range pigeonhole).** Because `ssupp a` takes values in
the finite set `(smallPrimes a).powerset`, its range is finite, so there is a threshold `N`
past which every value `ssupp a j` has already been attained at some index `i ≤ N`. -/
lemma ssupp_cover (a : ℕ → ℕ) :
    ∃ N, ∀ j, ∃ i ≤ N, ssupp a i = ssupp a j := by
  classical
  -- The finite set of possible values of `ssupp a`.
  set T : Finset (Finset ℕ) := (smallPrimes a).powerset with hT
  -- Every value `ssupp a j` lies in `T`.
  have hmem : ∀ j, ssupp a j ∈ T := by
    intro j
    rw [hT, Finset.mem_powerset]
    exact ssupp_subset j
  -- For each `s ∈ T`, if it is attained, pick an index; else pick `0`.
  let ι : Finset ℕ → ℕ := fun s =>
    if h : ∃ i, ssupp a i = s then Classical.choose h else 0
  have hι : ∀ s, (∃ i, ssupp a i = s) → ssupp a (ι s) = s := by
    intro s h
    simp only [ι, dite_eq_left h]
    exact Classical.choose_spec h
  refine ⟨T.sup ι, ?_⟩
  intro j
  refine ⟨ι (ssupp a j), ?_, ?_⟩
  · exact Finset.le_sup (hmem j)
  · exact hι (ssupp a j) ⟨j, rfl⟩

/-- **Piece 1 (finite descent, routine).**  Within the finite family of prime supports
`{P(a j) : j ≤ k}` there is a `⊆`-minimal element contained in `P(a k)`: an index `i ≤ k`
with `P(a i) ⊆ P(a k)` such that no `j ≤ k` has `P(a j) ⊊ P(a i)` (equivalently every
`j ≤ k` with `P(a j) ⊆ P(a i)` in fact has `P(a i) ⊆ P(a j)`). -/
lemma subsupport_min_le {a : ℕ → ℕ} (_ha : IsValidSeq a) (k : ℕ) :
    ∃ i ≤ k, (a i).primeFactors ⊆ (a k).primeFactors ∧
      ∀ j ≤ k, (a j).primeFactors ⊆ (a i).primeFactors →
        (a i).primeFactors ⊆ (a j).primeFactors := by
  classical
  set S : Finset ℕ :=
    (Finset.range (k + 1)).filter (fun j => (a j).primeFactors ⊆ (a k).primeFactors) with hS
  have hkS : k ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Finset.Subset.refl _⟩
  have hne : S.Nonempty := ⟨k, hkS⟩
  obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image S (fun j => (a j).primeFactors.card) hne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hiS
  obtain ⟨hik1, hsub⟩ := hiS
  have hik : i ≤ k := by omega
  refine ⟨i, hik, hsub, ?_⟩
  intro j hjk hjsub
  -- j ∈ S via transitivity
  have hjS : j ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Finset.Subset.trans hjsub hsub⟩
  -- minimality: card (a i) ≤ card (a j)
  have hcardle : (a i).primeFactors.card ≤ (a j).primeFactors.card := hmin j hjS
  -- from hjsub : a j ⊆ a i and hcardle, get a j = a i
  have heq : (a j).primeFactors = (a i).primeFactors :=
    Finset.eq_of_subset_of_card_le hjsub hcardle
  rw [heq]

/-- **Enumeration lemma.** Every `n`-good integer `c` in the window `[a 0, a n]` is a term
`a j` with `j ≤ n`. -/
lemma good_in_range_is_term {a : ℕ → ℕ} (ha : IsValidSeq a) :
    ∀ n c, Good a n c → a 0 ≤ c → c ≤ a n → ∃ j ≤ n, a j = c := by
  intro n
  induction n with
  | zero =>
    intro c _ hlo hhi
    exact ⟨0, le_refl 0, by omega⟩
  | succ m IH =>
    intro c hgood hlo hhi
    rcases lt_or_ge (a m) c with hcm | hcm
    · -- a m < c ≤ a (m+1) : must equal a (m+1) by greedy minimality
      obtain ⟨hlt, hgm, hmin⟩ := ha.succ_least_good m
      rcases lt_or_eq_of_le hhi with hlt' | heq
      · exact absurd hgood.mono (hmin c hcm hlt')
      · exact ⟨m + 1, le_refl _, heq.symm⟩
    · -- c ≤ a m : use IH with the m-good restriction
      obtain ⟨j, hj, hje⟩ := IH c hgood.mono hlo hcm
      exact ⟨j, Nat.le_succ_of_le hj, hje⟩

/-- **Piece 2 (arithmetic core), unified proof.**  If a prime `P > a 0` divides `a i`, then
`a i` is not `⊆`-minimal: some `j < i` has `P(a j) ⊊ P(a i)`. -/
lemma large_prime_not_min_support {a : ℕ → ℕ} (ha : IsValidSeq a) {i P : ℕ}
    (IH : ∀ m < i, ∃ i' ≤ m, (a i').primeFactors ⊆ (a m).primeFactors ∧
      ∀ q ∈ (a i').primeFactors, q ≤ a 0)
    (hP : Nat.Prime P) (hbig : a 0 < P) (hPi : P ∣ a i) :
    ∃ j < i, (a j).primeFactors ⊆ (a i).primeFactors ∧
      (a j).primeFactors ≠ (a i).primeFactors := by
  classical
  -- Basic positivity.
  have hai_pos : 0 < a i := by have := ha.1 i; omega
  have hai_ne : a i ≠ 0 := by omega
  have hPpos : 0 < P := hP.pos
  -- i ≥ 1: else P ∣ a 0 with P > a 0, impossible.
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have : P ≤ a 0 := Nat.le_of_dvd (by have := ha.1 0; omega) hPi
      omega
    · exact h0
  -- b₀ = the P-free part of a i.
  set b0 : ℕ := ordCompl[P] (a i) with hb0
  -- b₀ ∣ a i, and P ∤ b₀.
  have hb0_dvd : b0 ∣ a i := Nat.ordCompl_dvd (a i) P
  have hb0_pos : 0 < b0 := Nat.ordCompl_pos P hai_ne
  have hPnb0 : ¬ P ∣ b0 := Nat.not_dvd_ordCompl hP hai_ne
  -- primeFactors of b₀ = primeFactors of a i with P erased.
  have hb0_pf : (b0).primeFactors = (a i).primeFactors.erase P := by
    rw [hb0, ← Nat.support_factorization, Nat.factorization_ordCompl,
      Finsupp.support_erase, Nat.support_factorization]
  -- there is a small prime q ≤ a 0 dividing a i (a i shares a factor with a 0), hence q ∣ b₀.
  have hq : ∃ q, Nat.Prime q ∧ q ≤ a 0 ∧ q ∣ b0 := by
    have hgcd : 1 < Nat.gcd (a i) (a 0) := pairwise_gcd ha i 0
    obtain ⟨q, hqp, hqai, hqa0⟩ :=
      (one_lt_gcd_iff_exists_prime_dvd (by have := ha.1 0; omega)).mp hgcd
    have hqle : q ≤ a 0 := Nat.le_of_dvd (by have := ha.1 0; omega) hqa0
    have hqneP : q ≠ P := by intro h; subst h; omega
    -- q ∣ a i, q prime, q ≠ P, so q ∈ P(a i).erase P = P(b₀), so q ∣ b₀.
    have hqmem : q ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqai, hai_ne⟩
    have hqmem2 : q ∈ (b0).primeFactors := by
      rw [hb0_pf]; exact Finset.mem_erase.mpr ⟨hqneP, hqmem⟩
    exact ⟨q, hqp, hqle, Nat.dvd_of_mem_primeFactors hqmem2⟩
  obtain ⟨q, hqp, hqle, hqb0⟩ := hq
  -- b₀ ≥ 2.
  have hb0_ge2 : 2 ≤ b0 := by
    have := Nat.le_of_dvd hb0_pos hqb0
    have := hqp.two_le
    omega
  -- P * b₀ ∣ a i  (b₀ is P-free part, so P^{v_P} · b₀ = a i and v_P ≥ 1).
  have hPb0_dvd : P * b0 ∣ a i := by
    have hPop : P ∣ ordProj[P] (a i) := Nat.dvd_ordProj_of_dvd hai_ne hP hPi
    have hself : ordProj[P] (a i) * b0 = a i := Nat.ordProj_mul_ordCompl_eq_self (a i) P
    calc P * b0 ∣ ordProj[P] (a i) * b0 := Nat.mul_dvd_mul_right hPop b0
      _ = a i := hself
  -- b₀ < a i (since P ∣ a i, P > 1, and P·b₀ ∣ a i).
  have hb0_lt : b0 < a i := by
    have hle : P * b0 ≤ a i := Nat.le_of_dvd hai_pos hPb0_dvd
    nlinarith [hb0_pos, hPpos, hbig, hqp.two_le, hqle]
  -- Step 1: every multiple of b₀ (with multiplier ≥ 1) is (i-1)-good.
  --   For l ≤ i-1: use IH to get a small sub-support a l' ⊆ P(a l) (l' ≤ l < i); a i shares a
  --   prime with a l' (pairwise), that prime ≤ a 0 < P so ≠ P, so divides b₀; and it divides
  --   a l via P(a l')⊆P(a l).  Hence b₀ shares a prime with a l; a multiple too.
  have hmul_good : ∀ t, 1 ≤ t → Good a (i - 1) (b0 * t) := by
    intro t ht l hl
    -- l ≤ i-1 < i
    have hli : l < i := by omega
    obtain ⟨l', hl'l, hl'sub, hl'small⟩ := IH l hli
    have hal'_pos : 0 < a l' := by have := ha.1 l'; omega
    -- a i shares a prime with a l' (pairwise gcd)
    have hgcd : 1 < Nat.gcd (a i) (a l') := pairwise_gcd ha i l'
    obtain ⟨r, hr, hrai, hral'⟩ :=
      (one_lt_gcd_iff_exists_prime_dvd hal'_pos).mp hgcd
    -- r ∈ P(a l'), so r ≤ a 0
    have hal'_ne : a l' ≠ 0 := by omega
    have hrmem' : r ∈ (a l').primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hral', hal'_ne⟩
    have hrle : r ≤ a 0 := hl'small r hrmem'
    have hrneP : r ≠ P := by intro h; subst h; omega
    -- r ∈ P(a i).erase P = P(b₀), so r ∣ b₀
    have hrmemi : r ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrai, hai_ne⟩
    have hrb0 : r ∣ b0 := by
      have : r ∈ (b0).primeFactors := by
        rw [hb0_pf]; exact Finset.mem_erase.mpr ⟨hrneP, hrmemi⟩
      exact Nat.dvd_of_mem_primeFactors this
    -- r ∣ a l via P(a l') ⊆ P(a l)
    have hral : r ∣ a l := by
      have : r ∈ (a l).primeFactors := hl'sub hrmem'
      exact Nat.dvd_of_mem_primeFactors this
    -- r ∣ b₀ * t and r ∣ a l, so gcd (b₀*t) (a l) > 1
    have hal_pos : 0 < a l := by have := ha.1 l; omega
    exact (one_lt_gcd_iff_exists_prime_dvd hal_pos).mpr
      ⟨r, hr, Dvd.dvd.mul_right hrb0 t, hral⟩
  -- The geometric candidates g t = b₀ * q^t, all with support P(b₀).
  set g : ℕ → ℕ := fun t => b0 * q ^ t with hg
  have hg0 : g 0 = b0 := by simp [hg]
  have hqge2 : 2 ≤ q := hqp.two_le
  -- g is unbounded: pick t large.
  have hg_unbounded : ∃ t, a i ≤ g t := by
    -- b₀ * q^t ≥ q^t ≥ t+1 (since q ≥ 2), pick t = a i.
    refine ⟨a i, ?_⟩
    have h1 : a i + 1 ≤ 2 ^ (a i) := by
      have := Nat.lt_two_pow_self (n := a i); omega
    have h2 : (2:ℕ) ^ (a i) ≤ q ^ (a i) := Nat.pow_le_pow_left hqge2 (a i)
    have h3 : q ^ (a i) ≤ b0 * q ^ (a i) := Nat.le_mul_of_pos_left _ hb0_pos
    calc a i ≤ 2 ^ (a i) := by omega
      _ ≤ q ^ (a i) := h2
      _ ≤ b0 * q ^ (a i) := h3
      _ = g (a i) := by simp [hg]
  set Tfind := Nat.find hg_unbounded with hTfind
  have hTspec : a i ≤ g Tfind := Nat.find_spec hg_unbounded
  have hTpos : 1 ≤ Tfind := by
    rcases Nat.eq_zero_or_pos Tfind with h0 | h0
    · exfalso; rw [h0, hg0] at hTspec; omega
    · exact h0
  -- c := g (Tfind-1) is the largest with c < a i
  set c := g (Tfind - 1) with hc
  have hc_lt : c < a i := by
    have hnot : ¬ (a i ≤ g (Tfind - 1)) := Nat.find_min hg_unbounded (by omega)
    omega
  have hTeq : Tfind - 1 + 1 = Tfind := by omega
  have hgT : g Tfind = c * q := by
    have e1 : g Tfind = b0 * q ^ Tfind := by simp [hg]
    have e2 : c = b0 * q ^ (Tfind - 1) := by simp [hc, hg]
    have e3 : q ^ Tfind = q ^ (Tfind - 1) * q := by
      conv_lhs => rw [← hTeq]
      rw [pow_succ]
    rw [e1, e2, e3, mul_assoc]
  -- c is (i-1)-good (multiple of b₀ with multiplier q^(Tfind-1) ≥ 1).
  have hc_good : Good a (i - 1) c := by
    have hce : c = b0 * q ^ (Tfind - 1) := by simp [hc, hg]
    rw [hce]
    exact hmul_good (q ^ (Tfind - 1)) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  -- greedy minimality: c < a i = a ((i-1)+1), c is (i-1)-good ⇒ c ≤ a (i-1).
  have hsucc : (i - 1) + 1 = i := by omega
  have hc_le : c ≤ a (i - 1) := by
    obtain ⟨hlt, hgood, hmin⟩ := ha.succ_least_good (i - 1)
    rw [hsucc] at hlt hmin
    by_contra hcon
    push Not at hcon  -- a (i-1) < c
    exact hmin c hcon hc_lt hc_good
  -- c ≥ a 0 : c * q = g Tfind ≥ a i ≥ P * b₀ ≥ P * q, and q > 0 ⇒ c ≥ P > a 0.
  have hc_ge : a 0 ≤ c := by
    have hPb0_le : P * b0 ≤ a i := Nat.le_of_dvd hai_pos hPb0_dvd
    have hb0geq : q ≤ b0 := Nat.le_of_dvd hb0_pos hqb0
    have h1 : P * q ≤ P * b0 := Nat.mul_le_mul_left P hb0geq
    have h2 : a i ≤ c * q := by rw [← hgT]; exact hTspec
    have hqpos : 0 < q := hqp.pos
    have hPqcq : P * q ≤ c * q := by omega
    have hcP : P ≤ c := Nat.le_of_mul_le_mul_right hPqcq hqpos
    omega
  -- support of c equals support of b₀ (c = b₀ * q^(Tfind-1), q ∈ P(b₀)).
  have hPc : (c).primeFactors = (b0).primeFactors := by
    have hce : c = b0 * q ^ (Tfind - 1) := by simp [hc, hg]
    have hqmemb0 : q ∈ (b0).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hqb0, by omega⟩
    rcases Nat.eq_zero_or_pos (Tfind - 1) with he | he
    · rw [hce, he]; simp
    · have hb0ne : b0 ≠ 0 := by omega
      have hpowne : q ^ (Tfind - 1) ≠ 0 := pow_ne_zero _ (by omega)
      rw [hce, Nat.primeFactors_mul hb0ne hpowne,
        Nat.primeFactors_prime_pow (by omega) hqp]
      rw [Finset.union_eq_left]
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]; exact hqmemb0
  -- c is (i-1)-good, a 0 ≤ c ≤ a (i-1), so c = a j for some j ≤ i-1.
  obtain ⟨j, hj, hje⟩ := good_in_range_is_term ha (i - 1) c hc_good hc_ge hc_le
  refine ⟨j, by omega, ?_, ?_⟩
  · -- P(a j) = P(c) = P(b₀) ⊆ P(a i)
    rw [hje, hPc, hb0_pf]
    exact Finset.erase_subset P (a i).primeFactors
  · -- P(a j) ≠ P(a i) because P ∈ P(a i) but P ∉ P(a j) = P(b₀).
    rw [hje, hPc, hb0_pf]
    intro hcontra
    have hPmem : P ∈ (a i).primeFactors := Nat.mem_primeFactors.mpr ⟨hP, hPi, hai_ne⟩
    rw [← hcontra] at hPmem
    exact (Finset.mem_erase.mp hPmem).1 rfl

lemma term_has_small_subsupport {a : ℕ → ℕ} (ha : IsValidSeq a) (k : ℕ) :
    ∃ i ≤ k, (a i).primeFactors ⊆ (a k).primeFactors ∧
      ∀ p ∈ (a i).primeFactors, p ≤ a 0 := by
  -- Strong induction on k so the arithmetic core may use the statement at smaller indices.
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    -- Descend to a ⊆-minimal support i ≤ k inside P(a k).
    obtain ⟨i, hik, hsub, hmin⟩ := subsupport_min_le ha k
    refine ⟨i, hik, hsub, ?_⟩
    -- Show P(a i) has no prime > a 0.
    intro p hp
    by_contra hbig
    push Not at hbig  -- hbig : a 0 < p
    have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpi : p ∣ a i := Nat.dvd_of_mem_primeFactors hp
    have IHi : ∀ m < i, ∃ i' ≤ m, (a i').primeFactors ⊆ (a m).primeFactors ∧
        ∀ q ∈ (a i').primeFactors, q ≤ a 0 := by
      intro m hm
      exact IH m (lt_of_lt_of_le hm hik)
    obtain ⟨j, hji, hjsub, hjne⟩ := large_prime_not_min_support ha IHi hpP hbig hpi
    have hjk : j ≤ k := le_trans (le_of_lt hji) hik
    have := hmin j hjk hjsub
    exact hjne (Finset.Subset.antisymm hjsub this)

/-- **Lemma A.** If `b` is `n`-good, then it shares a prime `≤ a 0` with every `a i`
(`i ≤ n`).  Routine consequence of `term_has_small_subsupport`:  for `i ≤ n`, take the
small-only sub-support term `a i'` with `i' ≤ i ≤ n` and `P(a i') ⊆ P(a i)`.  Since `b` is
`n`-good and `i' ≤ n`, `gcd b (a i') > 1`, so `b` shares a prime `p` with `a i'`; that
`p ∈ P(a i') ⊆ P(a i)` is small (`≤ a 0`) and divides `a i`, and `p ∣ b`. -/
lemma good_small_witness {a : ℕ → ℕ} (ha : IsValidSeq a) {n b : ℕ}
    (hb : Good a n b) :
    ∀ i ≤ n, ∃ p, Nat.Prime p ∧ p ≤ a 0 ∧ p ∣ b ∧ p ∣ a i := by
  intro i hi
  obtain ⟨i', hi'i, hsub, hsmall⟩ := term_has_small_subsupport ha i
  have hi'n : i' ≤ n := le_trans hi'i hi
  have hai'pos : 0 < a i' := by have := ha.1 i'; omega
  have hgcd : 1 < Nat.gcd b (a i') := hb i' hi'n
  obtain ⟨p, hp, hpb, hpai'⟩ := (one_lt_gcd_iff_exists_prime_dvd hai'pos).mp hgcd
  have hai'ne : a i' ≠ 0 := by omega
  have hpmem' : p ∈ (a i').primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpai', hai'ne⟩
  have hpmem : p ∈ (a i).primeFactors := hsub hpmem'
  have hple : p ≤ a 0 := hsmall p hpmem'
  have hpai : p ∣ a i := Nat.dvd_of_mem_primeFactors hpmem
  exact ⟨p, hp, hple, hpb, hpai⟩

/-- **Goodness stabilisation.**  There is a threshold `N` past which the goodness
predicate no longer changes with the index.  This is the number-theoretic heart. -/
theorem good_stabilizes_core (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N, ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b := by
  obtain ⟨N, hcov⟩ := ssupp_cover a
  refine ⟨N, ?_⟩
  intro n hn b
  constructor
  · -- (→) monotone: constraints of Good a N are a subset of those of Good a n.
    intro h i hi
    exact h i (le_trans hi hn)
  · -- (←) the content: Good a N b → Good a n b.
    intro h j hj
    -- get a matching prefix index i ≤ N with the same small support
    obtain ⟨i, hiN, hss⟩ := hcov j
    -- b good for prefix N shares a small prime with a i
    obtain ⟨p, hp, hple, hpb, hpai⟩ := good_small_witness ha h i hiN
    -- p ∈ ssupp a i = ssupp a j ⇒ p ∣ a j
    have hai0 : a i ≠ 0 := by have := ha.1 i; omega
    have haj0 : a j ≠ 0 := by have := ha.1 j; omega
    have hpi : p ∈ ssupp a i := (mem_ssupp hai0).mpr ⟨hple, hp, hpai⟩
    have hpj : p ∈ ssupp a j := hss ▸ hpi
    have hpaj : p ∣ a j := ((mem_ssupp haj0).mp hpj).2.2
    -- conclude 1 < gcd b (a j)
    have hajpos : 0 < a j := by have := ha.1 j; omega
    exact (one_lt_gcd_iff_exists_prime_dvd hajpos).mpr ⟨p, hp, hpb, hpaj⟩

theorem eventual_periodicity_from_stable (a : ℕ → ℕ) (ha : IsValidSeq a)
    {N M : ℕ} (hMpos : 0 < M)
    (hstab : ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b)
    (hM : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M) :
    ∃ N' T L : ℕ, 0 < T ∧ 0 < L ∧ M ∣ L ∧
      ∀ n, N' ≤ n → a (n + T) = a n + L := by
  have hgreedy : ∀ n, N ≤ n →
      a n < a (n + 1) ∧ Good a N (a (n + 1)) ∧
        (∀ b, a n < b → b < a (n + 1) → ¬ Good a N b) := by
    intro n hn
    obtain ⟨hlt, hgood, hmin⟩ := ha.succ_least_good n
    refine ⟨hlt, (hstab n hn (a (n + 1))).mp hgood, ?_⟩
    intro b hb1 hb2 hgb
    exact hmin b hb1 hb2 ((hstab n hn b).mpr hgb)
  -- Pigeonhole on residues mod M over the M+1 indices in [N, N+M].
  have hmaps : Set.MapsTo (fun n => a n % M) ↑(Finset.Icc N (N + M)) ↑(Finset.range M) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hMpos
  have hcard : (Finset.range M).card < (Finset.Icc N (N + M)).card := by
    rw [Finset.card_range, Nat.card_Icc]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_Icc] at hx hy
  -- Order the two indices: u < v.
  wlog hlt : x < y generalizing x y
  · exact this y x (Ne.symm hxy) hfxy.symm hy hx (by omega)
  set u := x with hu
  set v := y with hv
  have hNu : N ≤ u := hx.1
  have huv : u < v := hlt
  -- The period and translation length.
  refine ⟨u, v - u, a v - a u, by omega, ?_, ?_, ?_⟩
  · -- 0 < a v - a u  (strict monotonicity)
    have : a u < a v := ha.strictMono huv
    omega
  · -- M ∣ (a v - a u)  from equal residues
    have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
    have hmod : a u ≡ a v [MOD M] := hfxy
    exact (Nat.modEq_iff_dvd' hle).mp hmod
  · -- the periodicity: ∀ n ≥ u, a (n + (v-u)) = a n + (a v - a u)
    -- Abbreviations
    set T := v - u with hTdef
    set L := a v - a u with hLdef
    have hML : M ∣ L := by
      have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
      have hmod : a u ≡ a v [MOD M] := hfxy
      exact (Nat.modEq_iff_dvd' hle).mp hmod
    have hTpos : 0 < T := by omega
    -- Translation invariance of `Good a N` by +L.
    have hperN : ∀ b, Good a N (b + L) ↔ Good a N b :=
      Good_periodic_of_modulus ha hML hM
    -- Induction from u upward.  Claim Q n : a (n + T) = a n + L for n ≥ u.
    have hLval : a v = a u + L := by
      have hle : a u ≤ a v := le_of_lt (ha.strictMono huv)
      omega
    have key : ∀ d, a (u + d + T) = a (u + d) + L := by
      intro d
      induction d with
      | zero =>
        -- a (u + T) = a v = a u + L
        have hvu : u + T = v := by omega
        simpa [hvu] using hLval
      | succ e ih =>
        -- from Q(u+e) derive Q(u+e+1)
        set n := u + e with hn
        have hnN : N ≤ n := by omega
        -- greedy at n and at n+T (both ≥ N)
        obtain ⟨hlt1, hgood1, hmin1⟩ := hgreedy n hnN
        obtain ⟨hlt2, hgood2, hmin2⟩ := hgreedy (n + T) (by omega)
        -- ih : a (n + T) = a n + L
        have hnT : a (n + T) = a n + L := by simpa [hn] using ih
        -- a (n+1) + L is Good a N and > a n + L = a(n+T)
        have hgoodShift : Good a N (a (n + 1) + L) := (hperN (a (n + 1))).mpr hgood1
        have hgt : a (n + T) < a (n + 1) + L := by
          rw [hnT]; have := hlt1; omega
        -- No good strictly between a(n+T) and a(n+1)+L
        have hbetween : ∀ b, a (n + T) < b → b < a (n + 1) + L → ¬ Good a N b := by
          intro b hb1 hb2 hgb
          -- shift down by L: a n < b - L < a (n+1), Good a N (b-L)
          have hbL : L ≤ b := by rw [hnT] at hb1; omega
          have hbeq : b - L + L = b := by omega
          have hgbL : Good a N (b - L) := by
            have := (hperN (b - L)).mpr
            rw [hbeq] at this
            -- this : Good a N b → Good a N (b - L)? No: (hperN (b-L)).mp : Good a N ((b-L)+L) ↔..
            exact (hbeq ▸ (hperN (b - L))).mp hgb
          have hlb : a n < b - L := by rw [hnT] at hb1; omega
          have hub : b - L < a (n + 1) := by omega
          exact hmin1 (b - L) hlb hub hgbL
        -- a (n+T+1) is the least good above a(n+T); compare with a(n+1)+L
        -- n + 1 + T = n + T + 1
        have hidx : n + 1 + T = n + T + 1 := by ring
        -- greedy2 gives: a(n+T) < a(n+T+1), Good a N (a(n+T+1)), min
        -- Show a (n + T + 1) = a (n+1) + L by antisymmetry.
        have hle1 : a (n + T + 1) ≤ a (n + 1) + L := by
          by_contra hc
          push Not at hc
          -- a(n+1)+L strictly between a(n+T) and a(n+T+1), and it's good ⇒ contra with hmin2
          exact hmin2 (a (n + 1) + L) hgt hc hgoodShift
        have hle2 : a (n + 1) + L ≤ a (n + T + 1) := by
          by_contra hc
          push Not at hc
          -- a(n+T+1) strictly between a(n+T) and a(n+1)+L, good ⇒ contra hbetween
          exact hbetween (a (n + T + 1)) hlt2 hc hgood2
        have : a (n + T + 1) = a (n + 1) + L := le_antisymm hle1 hle2
        -- conclude Q(u+e+1)
        have : a (u + e + 1 + T) = a (u + e + 1) + L := by
          have h1 : u + e + 1 + T = n + T + 1 := by rw [hn]; ring
          have h2 : u + e + 1 = n + 1 := by rw [hn]
          rw [h1, h2]; exact this
        exact this
    -- Rewrite: for n ≥ u, n = u + (n - u)
    intro n hn
    have hd := key (n - u)
    have heq : u + (n - u) = n := by omega
    rw [heq] at hd
    exact hd

-- LAYER 6: pure upgrade with modulus divisibility (provable now, from 1b/3/4)
theorem pure_periodicity_from_stable (a : ℕ → ℕ) (ha : IsValidSeq a)
    {N N' T L M : ℕ} (_hT : 0 < T) (_hL : 0 < L) (hML : M ∣ L)
    (hstab : ∀ n, N ≤ n → ∀ b, Good a n b ↔ Good a N b)
    (hM : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M)
    (hper : ∀ n, N' ≤ n → a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  -- Translation invariance of `Good a j` for every index j.
  have hper_all : ∀ j b, Good a j (b + L) ↔ Good a j b :=
    Good_periodic_all ha hML hstab hM
  -- The downward step: Q (k+1) → Q k, where Q k : a (k+T) = a k + L.
  have step : ∀ k, a (k + 1 + T) = a (k + 1) + L → a (k + T) = a k + L := by
    intro k hk1
    -- j = k + T; note a (j+1) = a (k+1+T) = a (k+1) + L.
    have hsucc : a (k + T + 1) = a (k + 1) + L := by
      have : k + 1 + T = k + T + 1 := by ring
      rwa [this] at hk1
    obtain ⟨hlt, hgood, hmin⟩ := ha.succ_least_good (k + T)
    -- a k + L is Good a (k+T)
    have hgoodkL : Good a (k + T) (a k + L) :=
      (hper_all (k + T) (a k)).mpr (term_good_all ha k (k + T))
    -- a k + L < a (k+T+1)
    have hkL_lt : a k + L < a (k + T + 1) := by
      rw [hsucc]
      have : a k < a (k + 1) := ha.strictMono (Nat.lt_succ_self k)
      omega
    -- Direction 1: a k + L ≤ a (k+T).
    have hle1 : a k + L ≤ a (k + T) := by
      by_contra hcon
      push Not at hcon
      -- a (k+T) < a k + L < a (k+T+1), a k + L good ⇒ contradiction with minimality
      exact hmin (a k + L) hcon hkL_lt hgoodkL
    -- Direction 2: a (k+T) ≤ a k + L.
    have hle2 : a (k + T) ≤ a k + L := by
      by_contra hcon
      push Not at hcon
      -- a k + L < a (k+T). Consider a(k+T) - L.
      have hLle : L ≤ a (k + T) := by omega
      -- a(k+T) is good a (k+T), hence good a k.
      have hgoodj : Good a (k + T) (a (k + T)) := term_good_all ha (k + T) (k + T)
      have hgoodk : Good a k (a (k + T)) := by
        intro i hi
        exact hgoodj i (le_trans hi (Nat.le_add_right k T))
      -- a(k+T) - L good a k, via translation invariance for Good a k.
      have hgoodkm : Good a k (a (k + T) - L) := by
        have hbeq : a (k + T) - L + L = a (k + T) := by omega
        rw [← hbeq] at hgoodk
        exact (hper_all k (a (k + T) - L)).mp hgoodk
      -- a k < a(k+T) - L < a(k+1), contradicting minimality of a(k+1).
      obtain ⟨hlt', hgood', hmin'⟩ := ha.succ_least_good k
      have hlb : a k < a (k + T) - L := by omega
      have hub : a (k + T) - L < a (k + 1) := by
        have : a (k + T) < a (k + 1) + L := by rw [← hsucc]; exact hlt
        omega
      exact hmin' (a (k + T) - L) hlb hub hgoodkm
    omega
  have hQ : ∀ n, a (n + T) = a n + L := by
    have hdown : ∀ d, a ((N' - d) + T) = a (N' - d) + L := by
      intro d
      induction d with
      | zero => simpa using hper N' (le_refl N')
      | succ e ih =>
        rcases Nat.lt_or_ge e N' with he | he
        · have heq : N' - (e + 1) + 1 = N' - e := by omega
          have := step (N' - (e + 1))
          rw [heq] at this
          exact this ih
        · have h1 : N' - (e + 1) = N' - e := by omega
          rw [h1]; exact ih
    intro n
    rcases Nat.lt_or_ge n N' with hn | hn
    · have heq : N' - (N' - n) = n := by omega
      have hd := hdown (N' - n)
      rwa [heq] at hd
    · exact hper n hn
  exact hQ

/-- **Eventual periodicity (number-theoretic core).**  There exist a threshold `N` and
positive integers `T, L` such that the difference sequence is periodic beyond `N`:
`a (n + T) = a n + L` for all `n ≥ N`. -/
theorem eventual_periodicity (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ N T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, N ≤ n → a (n + T) = a n + L := by
  obtain ⟨N, hstab⟩ := good_stabilizes_core a ha
  obtain ⟨N', T, L, hT, hL, _hML, hper⟩ :=
    eventual_periodicity_from_stable a ha (prefixMod_pos ha N) hstab (prefixMod_absorbs N)
  exact ⟨N', T, L, hT, hL, hper⟩

/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨N, hstab⟩ := good_stabilizes_core a ha
  set M := prefixMod a N with hMdef
  have hMpos : 0 < M := prefixMod_pos ha N
  have hMabs : ∀ i ≤ N, ∀ p, Nat.Prime p → p ∣ a i → p ∣ M := prefixMod_absorbs N
  obtain ⟨N', T, L, hT, hL, hML, hper⟩ :=
    eventual_periodicity_from_stable a ha hMpos hstab hMabs
  refine ⟨T, L, hT, hL, ?_⟩
  exact pure_periodicity_from_stable a ha hT hL hML hstab hMabs hper

end IMO2026Q6
