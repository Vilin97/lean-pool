/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zou Wenrong, Prowler99
-/

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.RingTheory.PowerSeries.WellKnown

variable {p : ℕ} [Fact p.Prime]

-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. 
#check  PadicInt
#check  ℤ_[p]
#check  ℚ_[p]

-- The ring homomorphism from `ℤ_[p]` to `ℤ⧸p^nℤ`.
#check PadicInt.toZMod
#check PadicInt.toZModPow

-- The universal property of `ℤ_[p]` as projective limit. (Commutative Diagram)
#check PadicInt.lift_unique
#check PadicInt.lift_spec


-- Prop 1.4
theorem prop1_4_weaker
    (F : Polynomial ℤ) : 
  ∀ν : ℕ, ∃x : ℤ, F.eval x = (0 : ZMod (p ^ ν)) ↔ ∃x : ℤ_[p], (F.map (Int.castRingHom ℤ_[p])).eval x = 0 := by sorry 


-- variable {F : MvPolynomial (Fin p) ℤ} {x : Fin p → ℤ_[p]}
-- #check MvPolynomial.map (Int.castRingHom ℤ_[p]) F
-- #check MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℤ_[p]) F)

-- A polynomial with integer coefficients has a solution in `ℤ_[p]` if and only if it has a solution in `ℤ ⧸ p^m` for every positive integer `m`
theorem prop1_4
    (F : MvPolynomial (Fin n) ℤ) :
  (∀m : ℕ, m > 0 → ∃x : Fin n → ℤ, MvPolynomial.eval x F = (0 : ZMod (p ^ m))) ↔ ∃x : Fin n → ℤ_[p], MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℤ_[p]) F) = 0 := by sorry
-- Here `n` is automorphically implicitly given

-- It seems that the following thm covers this prop.
#check PadicInt.toZModPow_eq_iff_ext


-- Prop 2.1
-- The set of primes at which the rational number `a` has nonzero valuation
def Rat.places (a : ℚ) := {p : ℕ | p.Prime ∧ padicValRat p a ≠ 0}

-- The above set is finite for a nozero rational
instance (a : ℚ) [NeZero a] :
  Fintype a.places := by sorry

variable (b : ℚ) [NeZero b]
#check b.places.toFinset
#check Set.toFinset

open BigOperators

-- The product of valuations at all primes for a nonzero rational number is `1`
theorem prop2_1
    (a : ℚ) [NeZero a] :
  ∏ p in a.places.toFinset, padicValRat p a = 1 := by sorry
-- why CANT i use Fintype.elems directly?


-- Prop 2.3
#check PadicInt

-- Prop 2.4
#check PadicInt.ideal_eq_span_pow_p
#check PadicInt.toZModPow
#check PadicInt.ker_toZModPow

-- Prop 2.5
#check PadicInt.lift_unique
#check PadicInt.lift_spec

-- Prop 2.6

-- There is a canonical isomorphism `ℤ_[p] ≅ ℤ⟦X⟧ ⧸ (X - p)`
#check PowerSeries.X
def PadicInt.toPowerSeriesZ : PowerSeries ℤ →+* ℤ_[p] :=
  by sorry

theorem PadicInt.ker_toPowerSeries :
  RingHom.ker (PadicInt.toPowerSeriesZ : PowerSeries ℤ →+* ℤ_[p]) = Ideal.span {(PowerSeries.X : PowerSeries ℤ) - ↑p} := by sorry

