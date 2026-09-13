/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import LeanPool.SelbergSieve4.Selberg
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanPool.SelbergSieve4.Applications.BrunTitchmarsh
import LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound
import LeanPool.SelbergSieve4.Tactic.AesopInit
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Positivity.Finset

/-!
# LeanPool.SelbergSieve4.MainResults
-/

@[expose] public section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  Sieve Nat Nat.Prime

theorem fundamental_theorem_simple (s : SelbergSieve) :
    s.siftedSum ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.rem d| else 0 :=
  s.selberg_bound_simple

theorem primeCounting_isBigO_atTop :
    (fun N => (π N:ℝ)) =O[Filter.atTop] (fun N => N / Real.log N) :=
  PrimeUpperBound.pi_ll

theorem primeCounting_le_mul : ∃ N C, ∀ n ≥ N, π n ≤ C*n/Real.log n :=
  PrimeUpperBound.pi_le_mul

theorem primesBetween_le (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    Set.ncard {p : ℕ | x ≤ p ∧ p ≤ (x+y) ∧ p.Prime}
      ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  rw [← BrunTitchmarsh.primesBetween_eq_ncard (by linarith)]
  exact BrunTitchmarsh.primesBetween_le _ _ _ hx hy hz
