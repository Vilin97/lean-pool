/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalAwayProduct
/-!
# The ramified prime factor of a rational cyclotomic principal idele

The level-zero factor is trivial.  At every positive level, the finite-place
character specification reduces the claim to the ramified chosen-Artin formula
proved in `RationalCyclotomicFinitePlaceArtin`.
-/

@[expose] public section



noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalCyclotomicPrincipalPrimeFactorPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalCyclotomicPrincipalPrimeFactorPrimeFact

open scoped Classical in
/-- The chosen finite-place factor at the ramified prime `p` is the direct
reduction of the rational `p`-adic unit. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  cases k with
  | zero =>
      apply Units.ext
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
  | succ n =>
      exact
        rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula
          p n x

end Reciprocity
end GlobalClassFieldTheory
