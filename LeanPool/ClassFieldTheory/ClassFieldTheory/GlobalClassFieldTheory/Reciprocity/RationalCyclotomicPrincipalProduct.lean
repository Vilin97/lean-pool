/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalPrimeFactor
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicZHatRigidity
/-!
# The rational cyclotomic principal-idele product formula

The ramified local factor at `p` is the direct `p`-adic unit character.
Every other finite local factor is the inverse Frobenius power prescribed
by the rational prime factorization.  Their product is the image of the
rational sign and therefore has square one.  Prime-power detection in the
torsion-free rational `ZHat`-extension removes this final sign ambiguity
and proves that every rational principal idele has trivial value.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalCyclotomicPrincipalProductPrimeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

attribute [local instance] rationalCyclotomicPrincipalProductPrimeFact

open scoped Classical in
local instance rationalCyclotomicPrincipalProductPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalProductPrimePowerNumberField

open scoped Classical in
local instance rationalCyclotomicPrincipalProductPrimePowerFiniteDimensional
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalProductPrimePowerFiniteDimensional

open scoped Classical in
local instance rationalCyclotomicPrincipalProductPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalProductPrimePowerIsAbelianGalois

open scoped Classical in
noncomputable local instance
    rationalCyclotomicPrincipalProductLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m

attribute [local instance] rationalCyclotomicPrincipalProductLevelFiniteDimensional

open scoped Classical in
noncomputable local instance
    rationalCyclotomicPrincipalProductLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois m

attribute [local instance] rationalCyclotomicPrincipalProductLevelIsAbelianGalois

open scoped Classical in
/-- The finite product of the genuine chosen local Artin characters of a
rational principal idele is the reduction of its rational sign. -/
theorem rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (chosenFinitePlaceArtinMonoidHom
            (K := ℚ)
            (L :=
              KummerTheory.rationalCyclotomicLevel
                ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x)))) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    (rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_factorizationProduct
      p k x).symm.trans
      ((congrArg (fun u => u * _)
        (rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime
          p k x)).trans
        (rationalPrimeUnitCharacter_mul_principalAwayFactorizationProduct_eq_sign
          p k x))

open scoped Classical in
/-- At every prime-power cyclotomic coordinate, the global Artin
character of the finite part of a rational principal idele is exactly the
reduced rational sign. -/
theorem
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (KummerTheory.rationalCyclotomicCharacterPrimeProduct
          (infiniteGlobalArtinMonoidHom
            ℚ KummerTheory.rationalCyclotomicField
            (rationalIdeleFinitePart
              (IdeleGroup.principalIdele ℚ x))) p) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    (rationalCyclotomicGlobalArtin_character_toZModPow_finitePart_eq_finprod
      (IdeleGroup.principalIdele ℚ x) p k).trans
      (rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign p k x)

open scoped Classical in
/-- Every prime-power reduction of the finite principal cyclotomic
character has square one. -/
theorem
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_sq
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct
            (infiniteGlobalArtinMonoidHom
              ℚ KummerTheory.rationalCyclotomicField
              (rationalIdeleFinitePart
                (IdeleGroup.principalIdele ℚ x))) p) ^ 2 =
      1 := by
  exact
    (congrArg (fun u => u ^ 2)
      (rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_eq_sign
        p k x)).trans
      (rationalSignPadicUnit_toZModPow_sq x p k)

open scoped Classical in
/-- The finite part of every rational principal idele has trivial value
in the actual rational cyclotomic `ZHat`-extension. -/
theorem rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (rationalIdeleFinitePart
          (IdeleGroup.principalIdele ℚ x)) =
      1 := by
  apply
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions
  intro p k
  exact
    rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_sq
      p k x

open scoped Classical in
/-- The rational cyclotomic value kills every rational principal idele. -/
theorem rationalCyclotomicZHatIdeleValue_principalIdele_eq_one
    (x : ℚˣ) :
    rationalCyclotomicZHatIdeleValue
        (IdeleGroup.principalIdele ℚ x) =
      1 := by
  exact
    (rationalCyclotomicZHatIdeleValue_principalIdele_eq_finitePart x).trans
      (rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one x)

open scoped Classical in
/-- The normalized cyclotomic `ZHat`-valuation kills principal ideles over
every number field.  This is the unconditional principal-idele endpoint
needed for descent to the idele class group. -/
@[simp]
theorem normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero
    (K : Type) [Field K] [NumberField K] (x : Kˣ) :
    normalizedCyclotomicZHatIdeleValue K
        (Additive.ofMul
          (IdeleGroup.principalIdele K x)) =
      0 := by
  exact
    (normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero_iff_finitePart
      K x).2
      (rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one
        (Units.map (Algebra.norm ℚ) x))

end Reciprocity
end GlobalClassFieldTheory
