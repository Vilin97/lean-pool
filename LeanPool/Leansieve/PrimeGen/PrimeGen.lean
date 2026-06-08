/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
-- PrimeGen: a specification for algorithms that generate prime numbers.
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith.Frontend

/-!
# Prime generators (`PrimeGen`)

This module specifies what it means for an algorithm to enumerate the primes in
order. `NPrime` is the subtype of prime naturals; `PrimeGen` is the class of
state machines that, starting from `init` and stepping with `next`, never skip a
prime. `SimpleGen` is the trivial reference implementation, and `primes` reads a
finite prefix of any generator's output.
-/

namespace Leansieve

/-- The subtype of natural numbers that are prime. -/
def NPrime : Type := { n : Nat // Nat.Prime n } deriving Repr, Ord, LT, LE

@[simp] theorem NPrime.eq_iff (a b : NPrime) : a = b ↔ a.val = b.val := Subtype.ext_iff
instance : ToString NPrime where toString s := s!"{s.val}"
instance : Dvd NPrime where dvd a b := a.val ∣ b.val
instance : Coe NPrime Nat where coe n := n.val
-- interestingly, the following seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s

/-- A `PrimeGen` is a state machine over `α` that enumerates the primes in
order: starting from `init` and stepping with `next`, it never skips a prime. -/
class PrimeGen (α : Type) where
  /-- The prime currently held by a state. -/
  P : α → NPrime
  /-- The initial state. -/
  init : α
  /-- Step to the next state. -/
  next : α → α
  /-- Stepping skips no prime between the current and next primes. -/
  hP' (g : α) : (¬∃ q, Nat.Prime q ∧ P g < q ∧ q < P (next g))
open PrimeGen

/-- `PrimeGt n p` holds when `p` is a prime strictly greater than `n`. -/
abbrev PrimeGt (n p : Nat) := Nat.Prime p ∧ n < p

/-- The least prime strictly greater than `n`, together with proofs that it is
prime, exceeds `n`, and is minimal among such primes. -/
structure MinPrimeGt (n : Nat) where
  /-- The witnessing prime. -/
  p : Nat
  /-- `p` is a prime greater than `n`. -/
  hpgt : PrimeGt n p
  /-- No smaller number is a prime greater than `n`. -/
  hmin : ∀ q : Nat, q < p → (¬ PrimeGt n q)

/-- The primality half of `MinPrimeGt.hpgt`: the witnessing prime is prime. -/
lemma MinPrimeGt.p' (m : MinPrimeGt n) : Nat.Prime m.p := m.hpgt.left

section simpleGen

theorem ex_prime_gt (c : Nat) : ∃ p, PrimeGt c p := by
  let d := c + 1 -- because the line below has ≤ and we need <
  let ⟨p, hcp, hprime⟩ : ∃ (p : ℕ), d ≤ p ∧ Nat.Prime p :=
    Nat.exists_infinite_primes d
  use p; constructor
  · exact hprime
  · omega

/-- The least prime greater than `n`, packaged as a `MinPrimeGt`. -/
def minPrimeGt (n : Nat) : MinPrimeGt n :=
  let e := ex_prime_gt n
  { p := Nat.find e,
    hpgt := Nat.find_spec e,
    hmin := by exact fun {q} a => Nat.find_min e a }

/-- A reference prime generator carrying the current prime and the next one. -/
structure SimpleGen where
  /-- The current prime. -/
  p : NPrime
  /-- The least prime greater than the current one. -/
  c : MinPrimeGt p.val

/-- Advance a `SimpleGen` to the next prime. -/
def SimpleGen.next (g : SimpleGen) : SimpleGen :=
  { p := ⟨g.c.p, g.c.hpgt.left⟩, c := minPrimeGt g.c.p }

instance : PrimeGen SimpleGen where
  P g := g.p
  init := { p := ⟨2, Nat.prime_two⟩, c := minPrimeGt 2 }
  next := .next
  hP' g := by  -- goal: no prime q between g.p and (g.next.p = g.c.p)
    -- why? that would imply prime_gt (g.p) q, but hmin contradicts this
    intro h
    rcases h with ⟨q, hq, hgt, hlt⟩
    exact (g.c.hmin q hlt) ⟨hq, hgt⟩

end simpleGen

/-- Function power: apply `f` recursively `n` times to `x₀`, collecting every
intermediate result (`f^[n] x` only returns the last value). -/
def fpow (f : α → α) (n : Nat) (x₀ : α) : List α :=
  aux (n-1) x₀ [] |>.reverse
where
  /-- Accumulate `n` iterates of `f` starting from `x`, prepending each onto `acc`. -/
  aux (n : Nat) (x : α) (acc : List α) :=
    if n = 0 then x::acc
    else aux (n-1) (f x) (x::acc)

/-- Read the first `n` primes produced by a `PrimeGen`. -/
def primes (α : Type) [pg : PrimeGen α] (n : Nat) : List NPrime :=
  fpow (fun g => pg.next g) n pg.init |>.map fun g => pg.P g

end Leansieve
