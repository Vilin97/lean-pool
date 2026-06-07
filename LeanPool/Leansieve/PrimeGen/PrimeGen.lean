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

def NPrime : Type := { n: Nat // Nat.Prime n } deriving Repr, Ord, LT, LE

@[simp] theorem NPrime.eq_iff (a b : NPrime) : a = b ↔ a.val = b.val := Subtype.ext_iff
instance : ToString NPrime where toString s := s!"{s.val}"
instance : Dvd NPrime where dvd a b := a.val ∣ b.val
instance : Coe NPrime Nat where coe n := n.val
-- interestingly, the following seems to shadow normal Nat ∈ Set Nat operations.
-- instance : Membership NPrime (Set Nat) where mem n s := n.val ∈ s

class PrimeGen (α : Type) where
  P : α → NPrime
  init : α
  next : α → α
  hP' (g:α) : (¬∃ q, Nat.Prime q ∧ P g < q ∧  q < P (next g))
open PrimeGen

abbrev PrimeGt (n p:Nat) := Nat.Prime p ∧ n < p

structure MinPrimeGt (n:Nat) where
  p : Nat
  hpgt : PrimeGt n p
  hmin : ∀q:Nat, q < p → (¬ PrimeGt n q)
def MinPrimeGt.p' (m:MinPrimeGt n) := m.hpgt.left

section simple_gen

  theorem ex_prime_gt (c:Nat) : ∃ p, PrimeGt c p := by
    let d := c + 1 -- because the line below has ≤ and we need <
    let ⟨p, hcp, hprime⟩ : ∃ (p : ℕ), d ≤ p ∧ Nat.Prime p :=
      Nat.exists_infinite_primes d
    use p; constructor
    · exact hprime
    · omega

  def min_prime_gt (n: Nat) : MinPrimeGt n :=
    let e := ex_prime_gt n
    { p:=Nat.find e,
      hpgt:=Nat.find_spec e,
      hmin:= by exact fun {q} a => Nat.find_min e a}

  structure SimpleGen where
    p : NPrime
    c : MinPrimeGt p.val

  def SimpleGen.next (g:SimpleGen) : SimpleGen :=
    { p:=⟨g.c.p, g.c.hpgt.left⟩, c:=min_prime_gt g.c.p }

  instance : PrimeGen SimpleGen where
    P g := g.p
    init := {p := ⟨2, Nat.prime_two⟩, c := min_prime_gt 2 }
    next := .next
    hP' g := by  -- goal: no prime q between g.p and (g.next.p = g.c.p)
      -- why? that would imply prime_gt (g.p) q, but hmin contradicts this
      intro h
      rcases h with ⟨q, hq, hgt, hlt⟩
      exact (g.c.hmin q hlt) ⟨hq, hgt⟩

  open PrimeGen

end simple_gen

/- function power. apply f recursively n times to x₀ and collect the results.
  (!! lean has `f^[n] x` but this doesn't collect intermediate results. maybe
  another version exists?) -/
def fpow (f : α → α) (n:Nat) (x₀ : α) : List α :=
  let rec aux (n:Nat) (x:α) (acc:List α) :=
    if n = 0 then x::acc
    else aux (n-1) (f x) (x::acc)
  aux (n-1) x₀ [] |>.reverse



def primes (α : Type) [pg: PrimeGen α] (n : Nat) : List NPrime :=
  fpow (fun g => pg.next g) n pg.init |>.map fun g => pg.P g

