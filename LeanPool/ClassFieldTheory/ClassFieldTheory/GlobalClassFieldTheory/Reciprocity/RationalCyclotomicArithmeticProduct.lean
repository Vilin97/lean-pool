/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalProduct
/-!
# The rational cyclotomic product formula in arithmetic normalization

The arithmetic norm-residue symbol sends an ordinary unramified
uniformizer to arithmetic Frobenius.  At the ramified prime of a
prime-power cyclotomic layer, a local unit `u` therefore acts by
`u⁻¹`.  This file records those two signs on the actual chosen local
Artin maps and proves the finite principal-idèle product formula in
that normalization.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

local instance (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

section ArbitraryCyclotomicLevel

noncomputable local instance
    rationalCyclotomicArithmeticLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  IsCyclotomicExtension.finiteDimensional
    {(m : ℕ)} ℚ (KummerTheory.rationalCyclotomicLevel m)

noncomputable local instance
    rationalCyclotomicArithmeticLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m

/-- Mapping an arithmetic chosen local symbol to a cyclotomic
coordinate only inverts the corresponding geometric coordinate.  This
small opaque boundary keeps the full chosen-Artin expressions out of
the finite-product congruence below. -/
private theorem
    galEquivZMod_arithmeticChosenFinitePlaceArtinMonoidHom_eq_inv
    (m : ℕ+) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : (v.adicCompletion ℚ)ˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
        (arithmeticChosenFinitePlaceArtinMonoidHom
          ℚ (KummerTheory.rationalCyclotomicLevel m) v x) =
      (IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          v x))⁻¹ := by
  rw [arithmeticChosenFinitePlaceArtinMonoidHom_apply, map_inv]

/-- For an arbitrary chosen local input away from the conductor, the
arithmetic cyclotomic character is `q` raised to the negative of the
absolute-value logarithmic valuation.  Thus an ordinary DVR
uniformizer, whose logarithmic value is `-1`, maps to `q`. -/
theorem
    galEquivZMod_arithmeticChosenFinitePlaceArtinMonoidHom_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (arithmeticChosenFinitePlaceArtinMonoidHom
          ℚ (KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q) x) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
        (-
          LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (Additive.ofMul
              ((finitePlaceCompletionUnitsContinuousMulEquiv
                (RayClass.rationalPrime q)).symm x))) := by
  rw [arithmeticChosenFinitePlaceArtinMonoidHom_apply,
    map_inv,
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      m q hq x,
    ← zpow_neg]

/-- Away from the conductor, the arithmetic local Artin character of
a rational principal component is the usual positive valuation power
of arithmetic Frobenius. -/
theorem
    galEquivZMod_arithmeticChosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (arithmeticChosenFinitePlaceArtinMonoidHom
          ℚ (KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime q)
            (IdeleGroup.principalIdele ℚ x))) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
          padicValRat q.1 (x : ℚ) := by
  rw [arithmeticChosenFinitePlaceArtinMonoidHom_apply,
    map_inv,
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
      m q hq x]
  rw [← zpow_neg, neg_neg]

end ArbitraryCyclotomicLevel

/-- The arithmetic chosen finite-place character of a rational
principal idèle at the prime `q`. -/
noncomputable def
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    (ZMod (p.1 ^ k))ˣ :=
  (rationalCyclotomicPrincipalFinitePlaceCharacter p k x q)⁻¹

/-- Arithmetic and geometric finite-place characters differ exactly
by inversion. -/
@[simp]
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_inv
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x q =
      (rationalCyclotomicPrincipalFinitePlaceCharacter
        p k x q)⁻¹ := by
  rfl

/-- Outside the ordinary rational prime-factorization support, the
arithmetic local factor is trivial. -/
@[simp]
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes)
    (hq :
      q ∉ rationalPrimeFactorizationPrimeSupport x p) :
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x q =
      1 := by
  rw [
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_inv,
    rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
      p k x q hq,
    inv_one]

/-- The arithmetic rational principal finite-place characters have
finite multiplicative support. -/
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacters_hasFiniteMulSupport
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Function.HasFiniteMulSupport
      (rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x) := by
  rw [Function.HasFiniteMulSupport]
  apply
    (rationalPrimeFactorizationPrimeSupport x p).finite_toSet.subset
  intro q hq
  by_contra hqSupport
  exact hq
    (rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
      p k x q hqSupport)

/-- At a prime away from `p`, the arithmetic character is the direct
Frobenius power `q ^ v_q(x)`. -/
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_of_ne
    (p q : Nat.Primes) (hqp : q ≠ p)
    (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x q =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr
          (rationalPrime_not_dvd_pow_of_ne q p hqp k))) ^
        padicValRat q.1 (x : ℚ) := by
  rw [
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_inv,
    rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne p q hqp k x,
    zpow_neg,
    inv_inv]

/-- At the ramified prime `p`, the arithmetic character is the inverse
of the actual reduced `p`-adic unit. -/
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_at_prime
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter
        p k x p =
      (Units.map (PadicInt.toZModPow k).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)))⁻¹ := by
  rw [
    rationalCyclotomicArithmeticPrincipalFinitePlaceCharacter_eq_inv,
    rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime]

local instance (p : Nat.Primes) (k : ℕ) :
    NumberField
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

local instance (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

/-- Pointwise inversion of the chosen local characters, assembled before
the public product formula so that its proof does not unfold the full
finite-product expressions during definitional equality checking. -/
private theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceProduct_eq_inv_geometric
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (arithmeticChosenFinitePlaceArtinMonoidHom
            ℚ
            (KummerTheory.rationalCyclotomicLevel
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x)))) =
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
              (IdeleGroup.principalIdele ℚ x))))⁻¹ := by
  calc
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (arithmeticChosenFinitePlaceArtinMonoidHom
            ℚ
            (KummerTheory.rationalCyclotomicLevel
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x)))) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          (IsCyclotomicExtension.Rat.galEquivZMod
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
                (IdeleGroup.principalIdele ℚ x))))⁻¹ := by
      apply finprod_congr
      intro v
      exact
        galEquivZMod_arithmeticChosenFinitePlaceArtinMonoidHom_eq_inv
          ⟨p.1 ^ k, pow_pos p.2.pos k⟩ v
          (IdeleGroup.finiteComponent v
            (IdeleGroup.principalIdele ℚ x))
    _ =
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
                (IdeleGroup.principalIdele ℚ x))))⁻¹ := by
      rw [finprod_inv_distrib]

/-- The reduction of a rational sign is fixed by inversion. -/
private theorem rationalSignPadicUnit_toZModPow_inv_eq_self
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p))⁻¹ =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  have hs :
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) *
        Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p) = 1 := by
    simpa only [pow_two] using
      rationalSignPadicUnit_toZModPow_sq x p k
  calc
    (Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p))⁻¹ =
        (Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p))⁻¹ * 1 := by
      rw [mul_one]
    _ =
        (Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p))⁻¹ *
          (Units.map (PadicInt.toZModPow k).toMonoidHom
            (rationalSignPadicUnit x p) *
            Units.map (PadicInt.toZModPow k).toMonoidHom
              (rationalSignPadicUnit x p)) := by
      rw [hs]
    _ =
        ((Units.map (PadicInt.toZModPow k).toMonoidHom
          (rationalSignPadicUnit x p))⁻¹ *
          Units.map (PadicInt.toZModPow k).toMonoidHom
            (rationalSignPadicUnit x p)) *
          Units.map (PadicInt.toZModPow k).toMonoidHom
            (rationalSignPadicUnit x p) := by
      rw [mul_assoc]
    _ = Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
      rw [inv_mul_cancel, one_mul]

/-- At every prime-power cyclotomic level, the product of the actual
arithmetic finite-place characters of a rational principal idèle is
the reduction of its sign. -/
theorem
    rationalCyclotomicArithmeticPrincipalFinitePlaceProduct_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        IsCyclotomicExtension.Rat.galEquivZMod
          (p.1 ^ k)
          (KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (hK :=
            KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
          (arithmeticChosenFinitePlaceArtinMonoidHom
            ℚ
            (KummerTheory.rationalCyclotomicLevel
              ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
            v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele ℚ x)))) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    (rationalCyclotomicArithmeticPrincipalFinitePlaceProduct_eq_inv_geometric
      p k x).trans
      ((congrArg (fun u => u⁻¹)
        (rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign p k x)).trans
        (rationalSignPadicUnit_toZModPow_inv_eq_self p k x))

end Reciprocity
end GlobalClassFieldTheory
