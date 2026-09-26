/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicPrincipalIdele
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCharacterRigidity
/-!
# Prime-power detection for the rational cyclotomic `ZHat`-Artin map

Prime-power reductions of the genuine cyclotomic character detect the
full rational cyclotomic automorphism.  Restricting that automorphism
through actual finite cyclotomic levels then detects every finite
coordinate of the rational cyclotomic `ZHat`-extension.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField ClassFormation

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalCyclotomicZHatRigidityPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalCyclotomicZHatRigidityPrimeFact

open scoped Classical in
/-- If all prime-power character reductions of the full cyclotomic
global Artin symbol have square one, then the corresponding Artin symbol
in the actual rational `ZHat`-extension has square one. -/
theorem
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 := by
  let σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  have hσ : σ ^ 2 = 1 :=
    rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
      σ h
  rw [rationalCyclotomicZHatGlobalArtin_eq_fullRestriction]
  change (rationalCyclotomicFullRestrictionToZHat σ) ^ 2 = 1
  rw [← map_pow, hσ, map_one]
open scoped Classical in
/-- Prime-power square-one identities force the rational cyclotomic
idele value itself to be trivial.  Torsion-freeness of `ZHat` removes
the residual order-two ambiguity. -/
theorem
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatIdeleValue a = 1 := by
  have hArtin :
      rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 :=
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
      a h
  have hValue :
      rationalCyclotomicZHatIdeleValue a ^ 2 = 1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      ← map_pow, hArtin, map_one]
  exact
    (pow_left_injective
      (M := Multiplicative ZHat)
      (n := 2) (by norm_num))
        (by simpa using hValue)

end Reciprocity
end GlobalClassFieldTheory
