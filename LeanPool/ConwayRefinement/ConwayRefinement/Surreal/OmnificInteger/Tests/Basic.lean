/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Ordinal

import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Ordinal
import Mathlib.Algebra.Order.Ring.Cast

/-!
# API checks for omnific integers

This file checks the public fixed-point and subring interfaces from a separate module. The ordinary
integer `2` is only an interface smoke test. The semantic checks prove that `ω - 1` belongs to the
carrier but is not the image of an ordinary integer, and that `2⁻¹` does not belong to the
carrier. Together, the latter checks distinguish Conway's carrier from both the ordinary integers
and all surreal numbers.
-/

universe u

public noncomputable section

namespace Tests

open Surreal

/-- Interface smoke test: addition in the predicate proves that `2` is an omnific integer. -/
theorem two_mem_omnificIntegers :
    (2 : Surreal.{u}) ∈ omnificIntegers := by
  apply mem_omnificIntegers.mpr
  rw [← one_add_one_eq_two]
  exact isOmnificInteger_one.add isOmnificInteger_one

/-- For `2`, subring membership reduces to Conway's fixed-point equation. -/
theorem two_mem_omnificIntegers_iff_cut :
    (2 : Surreal.{u}) ∈ omnificIntegers ↔
      (2 : Surreal.{u}) = omnificIntegerCut 2 :=
  mem_omnificIntegers.trans isOmnificInteger_iff

/-- The ordinal `ω`, embedded in the surreal numbers, is an omnific integer. -/
theorem omega_mem_omnificIntegers :
    (NatOrdinal.of Ordinal.omega0).toSurreal ∈ omnificIntegers :=
  NatOrdinal.toSurreal_mem_omnificIntegers _

/-- The omnific integer `ω - 1` is larger than every embedded natural number. -/
theorem natCast_lt_omega_sub_one (n : ℕ) :
    (n : Surreal.{u}) < (NatOrdinal.of Ordinal.omega0).toSurreal - 1 := by
  rw [lt_sub_iff_add_lt]
  rw [← NatOrdinal.toSurreal_natCast n, ← NatOrdinal.toSurreal_one,
    ← NatOrdinal.toSurreal_add]
  apply NatOrdinal.toSurreal.strictMono
  simpa using NatOrdinal.natCast_lt_omega0 (n + 1)

/-- The omnific integer `ω - 1` is larger than every embedded ordinary integer. -/
theorem intCast_lt_omega_sub_one (z : ℤ) :
    (z : Surreal.{u}) < (NatOrdinal.of Ordinal.omega0).toSurreal - 1 := by
  apply lt_of_le_of_lt (b := (z.natAbs : Surreal.{u}))
  · simpa using
      (Int.cast_mono (R := Surreal.{u}) (Int.le_natAbs : z ≤ z.natAbs))
  · exact natCast_lt_omega_sub_one z.natAbs

/-- The surreal number `ω - 1` belongs to the omnific-integer subring. -/
theorem omega_sub_one_mem_omnificIntegers :
    (NatOrdinal.of Ordinal.omega0).toSurreal - 1 ∈ omnificIntegers := by
  apply mem_omnificIntegers.mpr
  exact (NatOrdinal.isOmnificInteger_toSurreal _).add isOmnificInteger_one.neg

/-- The omnific integer `ω - 1` is not the image of an ordinary integer. -/
theorem omega_sub_one_ne_intCast (z : ℤ) :
    (NatOrdinal.of Ordinal.omega0).toSurreal - 1 ≠ (z : Surreal.{u}) :=
  (intCast_lt_omega_sub_one z).ne'

/-- The surreal number `2⁻¹` does not belong to the omnific-integer subring. -/
theorem two_inv_not_mem_omnificIntegers :
    (2 : Surreal.{u})⁻¹ ∉ omnificIntegers :=
  Surreal.two_inv_not_mem_omnificIntegers

/-- The refinement conjecture includes product equalities involving zero. -/
theorem conwayRefinementConjecture_zero_product
    (hC : ConwayRefinementConjecture.{u}) {a b : OmnificInteger.{u}} (hab : a * b = 0) :
    ∃ e f g h : OmnificInteger.{u},
      a = e * f ∧ b = g * h ∧ (0 : OmnificInteger.{u}) = e * g ∧ 0 = f * h := by
  apply conwayRefinementConjecture_def.mp hC a b 0 0
  simpa using hab

end Tests
