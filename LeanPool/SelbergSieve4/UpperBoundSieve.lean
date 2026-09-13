/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# LeanPool.SelbergSieve4.UpperBoundSieve
-/

@[expose] public section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace Sieve

/-- A real-valued divisor weight majorizing the delta function at `1`. -/
def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d ∈ n.divisors, μ_plus d

/-- Upper-bound sieve weights with their majorization property. -/
structure UpperBoundSieve where mk ::
  /-- Upper-bound Moebius weight. -/
  μPlus : ℕ → ℝ
  hμPlus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

/-- A real-valued divisor weight minorizing the delta function at `1`. -/
def LowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

/-- Lower-bound sieve weights with their minorization property. -/
structure LowerBoundSieve where mk ::
  /-- Lower-bound Moebius weight. -/
  μMinus : ℕ → ℝ
  hμMinus : LowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end Sieve
