/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
import LeanPool.Leansieve.PrimeGen.PrimeGen

/-!
# Generic prime sieve correctness (`PrimeSieve`)

This module proves, abstractly, that a sieve is correct. A `PrimeSieveState`
exposes the current prime `P`, the next candidate `C`, and a `next` step; a
`PrimeSieveDriver` asserts that `C` is the minimum of the residue set `R (P g)`.
From these, `c_prime`, `no_skipped_prime`, and `hs_suffice` show each step yields
the next consecutive prime, skipping none.
-/

namespace Leansieve

/-- `nosk' P C`: there is no prime strictly between `P` and the candidate `C`. -/
abbrev nosk' P C := (¬∃ q : Nat, Nat.Prime q ∧ P < q ∧ q < C) -- no skipped prime

/-- The observable state of a prime sieve: the current prime, the next
candidate, and a step taking proofs that the candidate is prime and skips none. -/
class PrimeSieveState (α : Type) where
  /-- The current prime. -/
  P (s : α) : NPrime
  /-- The candidate for the next prime. -/
  C (s : α) : Nat
  /-- Advance the sieve, given the candidate is prime and skips no prime. -/
  next (s : α) (hC : Nat.Prime (C s)) (hN : nosk' (P s) (C s)) : α
  /-- After stepping, the new prime is the old candidate and the candidate grows. -/
  hNext (s : α) (hC : Nat.Prime (C s)) (hN : nosk' (P s) (C s)) {s' : α}
    : (s' = (next s hC hN) → P s' = C s ∧ C s' > C s)
open PrimeSieveState

/-- The "residue" set: naturals `≥ 2` that are coprime to every prime `≤ P`. In
a sieve these are the numbers not yet sifted out at stage `P`. -/
def R (P : Nat) : Set Nat := { n | n ≥ 2 ∧ ∀ q ≤ P, Nat.Prime q → ¬q ∣ n }

/-- everything in R is greater than P. we use this to show C > P later. -/
lemma r_gt_p (p : Nat) : (∀ r ∈ R p, r > p) := by
  -- argument: R and S together say ∀ p:prime ≤ P, ¬ p∣r
  intro r hrr;  unfold R at hrr
  -- if r is ≤ P, there is a contradiction.
  by_contra h; simp at h
  -- r (like all natural numbers) has a minimum prime factor f
  have : r ≠ 1 := by aesop -- R say r ≥ 2
  obtain ⟨f, hf', hfr⟩ : ∃ f, Nat.Prime f ∧ f ∣ r :=
      Nat.exists_prime_and_dvd ‹r ≠ 1›
  -- from a chain of relationships we can conclude that f≤P...
  have : 0 < r := by exact Nat.zero_lt_of_lt hrr.left
  have : f ≤ r := Nat.le_of_dvd this hfr
  have : f ≤ p := by omega
  aesop

/- if p₁ is the next consecutive prime after p₀ then
  R p₁ = { n:(R p₀) | ¬ p₁∣n }
  This corresponds to the idea that each time you identify
  the next prime in a sieve, you sift out all its multiples. -/
theorem r_next (p₀ : Nat) (m : MinPrimeGt p₀) {n : Nat}
  : (n ∈ R p₀ ∧ ¬↑m.p ∣ n) ↔ (n ∈ R m.p) := by
    let ⟨h₁, hinc⟩ := m.hpgt; let hmin := m.hmin; set p₁ := m.p
    unfold R; simp only [ge_iff_le, Set.mem_setOf_eq]; apply Iff.intro
    all_goals intro hn; apply And.intro; simp_all only [not_and, not_lt, true_and]
    · show ∀ q ≤ p₁, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      by_cases hq₀ : q ≤ p₀
      case pos => simp_all
      case neg =>
        by_contra hqn
        simp only [not_le] at hq₀
        have : q ≠ 1 := by aesop
        obtain ⟨f, hf', hfq⟩ := Nat.exists_prime_and_dvd ‹q ≠ 1›
        have hmin := m.hmin
        absurd hmin
        simp only [not_and, not_lt, not_forall, not_le]
        refine ⟨f, ?_, hf', ?_⟩
        · -- goal: f < p₁
          have : 0 < q := by omega
          have : f ≤ q := by exact Nat.le_of_dvd this hfq
          have : q ≠ p₁ := by aesop
          omega
        · -- goal: p₀ < f
          simp_all only [not_and, not_lt, ne_eq]
          by_contra h
          have : f ≤ p₀ := by omega
          have : 2 ≤ f := by exact Nat.Prime.two_le hf'
          simp_all only [not_lt]
          have : ¬ f ∣ n := by aesop
          have : f ∣ n := by exact Nat.dvd_trans hfq hqn
          contradiction
    · show ∀ q ≤ p₀, Nat.Prime q → ¬q ∣ n
      intro q hq hq2
      have : q ≤ p₁ := by omega
      exact (hn.right q this) hq2
    · show ¬p₁ ∣ n
      simp_all

/- A prime sieve implementation can model `R p` by providing
a bijection between `R p` and its internal data structures.

For RakeSieve, this is exposed to the type system by attaching
a predicate to the internal data structure.

Whatever the sieve does to "sift out" multiples of the next
prime `p₁` is equivalent to the expression  `∧ ¬(p₁∣n)`.

The following theorem allows us to construct a predicate for
membership in `R pₙ` by induction using predicates of this
form at each step. -/
theorem r_next_prop {p₀ n : Nat} {h₀ h₁ : Nat → Prop} {m : MinPrimeGt p₀}
  (hh₀ : h₀ n ↔ n ∈ R p₀) (hh₁ : h₁ n ↔ h₀ n ∧ ¬(m.p ∣ n))
  : (h₁ n ↔ n ∈ R m.p) := by
  simp only [hh₁, hh₀]
  exact r_next p₀ m

/--
PrimeSieveDriver provides the generic proof that a
A PrimeSieve is a PrimeGen that uses a SieveState to generate primes.
In practice, this means that it somehow models the set of natural
numbers greater than 1 that are coprime to a list of known primes,
and then repeatedly:
  - obtains the minimum of this set as the next prime
  - eliminates multiples of the new prime. -/
class PrimeSieveDriver (α : Type) [PrimeSieveState α] where
  /-- The candidate `C` lies in the residue set `R (P g)`. -/
  hCinR (g : α) : C g ∈ R (P g)            -- C is an element of R
  /-- The candidate `C` is the minimum of the residue set `R (P g)`. -/
  hRmin (g : α) : ∀ n ∈ R (P g), C g ≤ n   -- C is min of R
open PrimeSieveDriver

theorem c_gt_p (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g : α) : C g > P g := by
  have := hCinR g
  exact r_gt_p (↑(P g)) (C g) this

theorem no_skipped_prime (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g : α)
  : ¬ ∃ q : Nat, Nat.Prime q ∧ P g < q ∧ q < C g := by
    intro ⟨q, ⟨hQ', hPltQ, hQltC⟩⟩ -- `intro q` on a ¬∃ goal requires we find a contradiction.
    -- hRmin tells us that that C is the min of the set R.
    have hRmin : ∀ n ∈ R (P g), C g ≤ n := hRmin <| g
    -- demonstrating `q ∈ R` would show the contradiction since `q<P` and `P` is min of `R`
    suffices hQinR : q ∈ R (P g) from by apply hRmin at hQinR; omega
    -- so now we just show hQinR. q∈R means q≥2 ∧ (¬∃p∈ S g, p∣q)
    -- both of these facts follow immediately from the fact that q is prime,
    -- provided we can *also* show that q itself is not an element of s.
    unfold R; constructor
    · show q ≥ 2; exact Nat.Prime.two_le hQ'
    · show ∀ p ≤ ↑(P g), Nat.Prime p → ¬(p ∣ q)
      intro p hp hp' -- assume p exists and p|q. show a contradiction.
      -- since that p|q and both are prime, it follows that p=q.
      have := Nat.prime_dvd_prime_iff_eq hp' hQ'
      omega

lemma no_prime_factors_im_no_factors {c : Nat} -- c is a candidate prime
  (h2lc : 2 ≤ c) -- c is at least 2
  (hnpf : ∀ p < c, Nat.Prime p → ¬(p ∣ c)) -- c has no prime factors
  : Nat.Prime c := by
    have : ∀ m < c, m ∣ c → m = 1 := by  -- c has no divisors but 1 and c
      intro m hmc hmdc  -- give names to the above assumptions
      by_contra         -- assume ¬(m=1) and show contradiction
      obtain ⟨p, hp', hpm⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
        Nat.exists_prime_and_dvd ‹m ≠ 1›
      have : p ∣ c := Nat.dvd_trans hpm hmdc
      have : ¬(p ∣ c) := by
        have : 0 < c := by omega
        have : 0 < m := Nat.pos_of_dvd_of_pos hmdc this
        have : p ≤ m := Nat.le_of_dvd this hpm
        have : p < c := by omega
        exact hnpf p this hp'
      contradiction
    exact Nat.prime_def_lt.mpr ⟨‹2 ≤ c›, this⟩

theorem c_prime (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g : α)
  : Nat.Prime (C g) := by
    set c := C g
    have hfac : ∀ q < C g, Nat.Prime q → ¬ q ∣ c := by
      intro q₀ hqc hPq
      set q : NPrime := ⟨q₀, hPq⟩
      by_cases hq : q ≤ (P g)
      case pos => -- ¬p∣C because C∈R and that's how R is defined
        have hCinR := hCinR g
        unfold R at hCinR; simp at hCinR
        aesop
      case neg => -- we have P < q and q < C but this can't happen
        have : (P g) < q := by exact Nat.gt_of_not_le hq
        have := no_skipped_prime α g
        absurd this; use q; aesop
    have h2c : 2 ≤ C g := by
      set p := P g
      have : p.val ≥ 2 := by exact Nat.Prime.two_le p.prop
      have : c > p.val := c_gt_p α g
      omega
    exact no_prime_factors_im_no_factors h2c hfac

-- demonstrate that a sieve generates the next consecutive prime at each step.
-- "we have a new, bigger prime, and there is no prime between them".
theorem hs_suffice (α : Type) [PrimeSieveState α] [PrimeSieveDriver α] (g : α)
  : (Nat.Prime (C g)) ∧ (C g > P g) ∧ (¬∃ q, Nat.Prime q ∧ P g < q ∧ q < C g) := by
    split_ands
    · exact c_prime α g
    · exact c_gt_p α g
    · exact no_skipped_prime α g

/-- Advance a sieve state by one step, discharging the primality and
no-skipped-prime obligations from the generic proofs above. -/
def nextState {α : Type} [PrimeSieveState α] [PrimeSieveDriver α] (s : α) : α :=
  let c' := c_prime α s
  let ns := no_skipped_prime α s
  PrimeSieveState.next s c' ns

variable (α : Type) [PrimeSieveState α] [PrimeSieveDriver α]

/-- A prime sieve: a wrapper carrying a single sieve state. -/
structure PrimeSieve where
  /-- The underlying sieve state. -/
  state : α

/-- Advance a `PrimeSieve` by one step. -/
def PrimeSieve.next (x : PrimeSieve α) : PrimeSieve α :=
  { state := nextState x.state }

end Leansieve
