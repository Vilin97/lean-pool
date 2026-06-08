/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Aesop
import LeanPool.SelbergSieve4.Tactic.AesopInit
import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# LeanPool.SelbergSieve4.Tactic.AesopDiv
-/

namespace Sieve
open Finset

/-- Wrapper predicate for divisibility used by the `Divisibility` Aesop rule set. -/
protected def MyDvd (a b : ℕ) : Prop := a ∣ b
open Sieve (MyDvd)

@[simp]
theorem myDvd_iff (a b : ℕ) : MyDvd a b ↔ a ∣ b := by
  exact Iff.rfl

/-- Run `aesop` using the local divisibility rule set with simplification disabled. -/
macro (name := aesopDiv) "aesopDiv" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Divisibility):ident]))

/-- Run `aesop?` using the local divisibility rule set with simplification disabled. -/
macro (name := aesopDiv?) "aesopDiv?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Divisibility):ident]))


@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_of_myDvd (a b : ℕ) : MyDvd a b → a ∣ b := (myDvd_iff a b).mp

@[aesop destruct safe (rule_sets := [Divisibility])]
theorem myDvd_of_dvd (a b : ℕ) : a ∣ b → MyDvd a b := (myDvd_iff a b).mpr

@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_trans {a b c : ℕ} : MyDvd a b → MyDvd b c → MyDvd a c := by
  intro hab hbc
  exact (myDvd_iff a c).mpr (Nat.dvd_trans ((myDvd_iff a b).mp hab) ((myDvd_iff b c).mp hbc))

@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_of_mem_divisors {a b : ℕ} : a ∈ b.divisors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_divisors

@[aesop safe forward (rule_sets := [Divisibility])]
theorem myDvd_of_mem_primeFactors {a b : ℕ} : a ∈ b.primeFactors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_primeFactors

attribute [aesop safe forward (rule_sets := [Divisibility])] not_squarefree_zero

@[aesop forward safe (rule_sets := [Divisibility])]
theorem eq_zero_of_zero_myDvd (a : ℕ) : MyDvd 0 a → a = 0 := by
  intro h
  exact eq_zero_of_zero_dvd ((myDvd_iff 0 a).mp h)

attribute [aesop safe (rule_sets := [Divisibility])] Nat.pos_of_ne_zero

@[aesop forward safe (rule_sets := [Divisibility])]
theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : False := by simp at h

@[aesop forward safe (rule_sets := [Divisibility])]
theorem mem_zero_divisors (a : ℕ) (h : a ∈ Nat.divisors 0) : False := by simp at h

@[aesop forward safe (rule_sets := [Divisibility])]
theorem zero_lt_zero (h : 0 < 0) : False := by linarith

@[aesop safe (rule_sets := [Divisibility])]
theorem test {n m : ℕ} : n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr

@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c a :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b)

@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c b :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b)

@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : MyDvd a c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b) h

@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : MyDvd b c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b) h

@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_myDvd_left (a b : ℕ) : MyDvd (a.gcd b) a :=
  myDvd_of_dvd _ _ (gcd_dvd_left a b)

@[aesop safe (rule_sets := [Divisibility])]
theorem gcd_myDvd_right (a b : ℕ) : MyDvd (a.gcd b) b :=
  myDvd_of_dvd _ _ (gcd_dvd_right a b)

@[aesop forward safe (rule_sets := [Divisibility])]
theorem gcd_eq_zero_left (a b : ℕ) (h : a.gcd b = 0) : a = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.1
@[aesop forward safe (rule_sets := [Divisibility])]
theorem gcd_eq_zero_right (a b : ℕ) (h : a.gcd b = 0) : b = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.2

@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd a c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b) h

@[aesop forward safe (rule_sets := [Divisibility])]
theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd b c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b) h

@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : MyDvd c a) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b)

@[aesop safe (rule_sets := [Divisibility])]
theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : MyDvd c b) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b)

@[aesop safe (rule_sets := [Divisibility])]
theorem myDvd_lcm_left (a b : ℕ) : MyDvd a (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_left a b)

@[aesop safe (rule_sets := [Divisibility])]
theorem myDvd_lcm_right (a b : ℕ) : MyDvd b (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_right a b)

@[aesop forward safe (rule_sets := [Divisibility])]
theorem lcm_eq_zero_left (a b : ℕ) (h : a.lcm b = 0) : a = 0 ∨ b = 0 := by
  rw [←lcm_eq_nat_lcm, _root_.lcm_eq_zero_iff] at h; exact h

attribute [aesop forward safe (rule_sets := [Divisibility])] Squarefree.squarefree_of_dvd

@[aesop forward safe (rule_sets := [Divisibility])]
theorem squarefree_of_myDvd (a b : ℕ) (hb : Squarefree b) (h : MyDvd a b) :
    Squarefree a := by
  rw[myDvd_iff] at h
  exact Squarefree.squarefree_of_dvd h hb
end Sieve
