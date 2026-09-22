/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtin
import Mathlib.Algebra.BigOperators.Finprod
/-!
# Away-from-p factors of a rational cyclotomic principal idele

For the cyclotomic level `p ^ k`, this file reindexes the actual chosen
finite-place Artin characters over rational primes.  Away from `p`, the
unramified formula makes the multiplicative support lie in the ordinary
finite prime factorization support of the principal rational number.

The final theorem separates the genuine `p`-factor from the explicit
away-from-`p` finite product.  The construction also applies to `k = 0`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open Function

open scoped Classical in
/-- The prime subtype supplies the primality instance used at this local factor. -/
local instance rationalCyclotomicPrincipalAwayProductPrimeFact (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

attribute [local instance] rationalCyclotomicPrincipalAwayProductPrimeFact

open scoped Classical in
/-- The positive cyclotomic level has nonzero underlying natural number. -/
local instance rationalCyclotomicPrincipalAwayProductPositiveLevelNeZero
    (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

attribute [local instance] rationalCyclotomicPrincipalAwayProductPositiveLevelNeZero

open scoped Classical in
local instance rationalCyclotomicPrincipalPrimePowerNumberField
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalPrimePowerNumberField

open scoped Classical in
local instance rationalCyclotomicPrincipalPrimePowerFiniteDimensional
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalPrimePowerFiniteDimensional

open scoped Classical in
local instance rationalCyclotomicPrincipalPrimePowerIsGalois
    (p : Nat.Primes) (k : ℕ) :
    IsGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_isGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩

attribute [local instance] rationalCyclotomicPrincipalPrimePowerIsGalois

open scoped Classical in
local instance rationalCyclotomicPrincipalPrimePowerIsAbelianGalois
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  IsAbelianGalois.of_algHom
    (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩).val

attribute [local instance] rationalCyclotomicPrincipalPrimePowerIsAbelianGalois

open scoped Classical in
noncomputable local instance
    rationalCyclotomicPrincipalLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m

attribute [local instance] rationalCyclotomicPrincipalLevelFiniteDimensional

open scoped Classical in
noncomputable local instance
    rationalCyclotomicPrincipalLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois m

attribute [local instance] rationalCyclotomicPrincipalLevelIsAbelianGalois

open scoped Classical in
private noncomputable def rationalCyclotomicPrincipalHeightOneArtinInput
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩ ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩ :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L :=
      KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    v
    (IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x))

open scoped Classical in
private theorem rationalCyclotomicPrincipalHeightOneArtinInput_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicPrincipalHeightOneArtinInput p k x v =
      chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L :=
          KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
        v
        (IdeleGroup.finiteComponent v
          (IdeleGroup.principalIdele ℚ x)) := by
  rfl

open scoped Classical in
private noncomputable def rationalCyclotomicPrincipalHeightOneCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (ZMod (p.1 ^ k))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod
    (p.1 ^ k)
    (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    (hK :=
      KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
        ⟨p.1 ^ k, pow_pos p.2.pos k⟩)
    (rationalCyclotomicPrincipalHeightOneArtinInput p k x v)

open scoped Classical in
/-- The named height-one character is the cyclotomic coordinate of the
chosen finite-place Artin symbol. -/
theorem rationalCyclotomicPrincipalHeightOneCharacter_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalCyclotomicPrincipalHeightOneCharacter p k x v =
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
            (IdeleGroup.principalIdele ℚ x))) := by
  rw [rationalCyclotomicPrincipalHeightOneCharacter,
    rationalCyclotomicPrincipalHeightOneArtinInput_spec]

open scoped Classical in
/-- The genuine chosen finite-place Artin character of the rational
principal idele at the prime `q`, evaluated in the `p ^ k` cyclotomic
coordinate. -/
noncomputable def rationalCyclotomicPrincipalFinitePlaceCharacter
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    (ZMod (p.1 ^ k))ˣ :=
  rationalCyclotomicPrincipalHeightOneCharacter p k x
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ)).symm q)

open scoped Classical in
private theorem rationalCyclotomicPrincipalFinitePlaceCharacter_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q =
      rationalCyclotomicPrincipalHeightOneCharacter p k x
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q) := by
  rfl

open scoped Classical in
/-- The named rational-prime character is exactly the cyclotomic
coordinate of the chosen finite-place Artin symbol. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_chosenArtin_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q =
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
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm q)
          (IdeleGroup.finiteComponent
            ((Rat.HeightOneSpectrum.primesEquiv
              (R := 𝓞 ℚ)).symm q)
            (IdeleGroup.principalIdele ℚ x))) := by
  rw [rationalCyclotomicPrincipalFinitePlaceCharacter_spec]
  exact
    rationalCyclotomicPrincipalHeightOneCharacter_spec p k x
      ((Rat.HeightOneSpectrum.primesEquiv
        (R := 𝓞 ℚ)).symm q)

open scoped Classical in
/-- At every positive `p`-power level, the finite-place character at `p`
is the direct reduction of the rational `p`-adic unit. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_at_prime_succ_formula
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p (n + 1) x p =
      Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  have hwChosen :
      chosenFinitePlaceExtension
          (L := KummerTheory.rationalCyclotomicLevel
            ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) =
        rationalCyclotomicChosenFinitePlaceExtension
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) := rfl
  let localArtin : Gal(KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) :=
    finitePlaceLocalToGlobalMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (rationalCyclotomicChosenFinitePlaceExtension
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
      (finitePlaceLocalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (rationalCyclotomicChosenFinitePlaceExtension
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
        (IdeleGroup.finiteComponent
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
          (IdeleGroup.principalIdele ℚ x)))
  let chosenArtin : Gal(KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) :=
    chosenFinitePlaceArtinMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (IdeleGroup.finiteComponent
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (IdeleGroup.principalIdele ℚ x))
  have hSpec :
      rationalCyclotomicPrincipalHeightOneArtinInput
          p (n + 1) x
          ((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ)).symm p) =
        chosenArtin := by
    dsimp only [chosenArtin]
    exact rationalCyclotomicPrincipalHeightOneArtinInput_spec
      p (n + 1) x
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
  have hFactor : chosenArtin = localArtin := by
    dsimp only [chosenArtin, localArtin]
    exact chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
      (rationalCyclotomicChosenFinitePlaceExtension
        ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
      hwChosen
      (IdeleGroup.finiteComponent
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p)
        (IdeleGroup.principalIdele ℚ x))
  have hLocal :
      localArtin = rationalCyclotomicPrincipalPrimeChosenArtin p n x := by
    dsimp only [localArtin]
    simp only [rationalCyclotomicPrincipalPrimeChosenArtin,
      rationalCyclotomicPrincipalPrimeModulus, RayClass.rationalPrime]
    rfl
  have hInput := hSpec.trans (hFactor.trans hLocal)
  have hCharacter := congrArg
    (fun sigma : Gal(
        KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩ / ℚ) =>
      IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (KummerTheory.rationalCyclotomicLevel
          ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩)
        sigma)
    hInput
  calc
    rationalCyclotomicPrincipalFinitePlaceCharacter p (n + 1) x p = _ := by
      rw [rationalCyclotomicPrincipalFinitePlaceCharacter_spec,
        rationalCyclotomicPrincipalHeightOneCharacter]
    _ = _ := hCharacter
    _ = Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) :=
      galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime p n x

open scoped Classical in
/-- A rational prime distinct from `p` does not divide any power
`p ^ k`.  This includes the level-one case `k = 0`. -/
theorem rationalPrime_not_dvd_pow_of_ne
    (q p : Nat.Primes) (hqp : q ≠ p) (k : ℕ) :
    ¬ q.1 ∣ p.1 ^ k := by
  intro hdiv
  apply hqp
  apply Subtype.ext
  exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hdiv

open scoped Classical in
/-- Away from `p`, the chosen finite-place character is the inverse
Frobenius power determined by the rational `q`-adic valuation. -/
theorem rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
    (p q : Nat.Primes) (hqp : q ≠ p)
    (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr
          (rationalPrime_not_dvd_pow_of_ne q p hqp k))) ^
        (-padicValRat q.1 (x : ℚ)) := by
  have hprime :
      RayClass.rationalPrime q =
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q) := by
    change
      (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q =
        (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm q
    rfl
  rw [rationalCyclotomicPrincipalFinitePlaceCharacter_spec,
    rationalCyclotomicPrincipalHeightOneCharacter_spec, ← hprime]
  exact
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩ q
      (rationalPrime_not_dvd_pow_of_ne q p hqp k) x

open scoped Classical in
/-- Outside the finite rational prime-factorization support, the
`q`-adic valuation of the nonzero rational number is zero. -/
theorem
    padicValRat_eq_zero_of_not_mem_rationalPrimeFactorizationPrimeSupport
    (x : ℚˣ) (p q : Nat.Primes)
    (hq :
      q ∉ rationalPrimeFactorizationPrimeSupport x p) :
    padicValRat q.1 (x : ℚ) = 0 := by
  have hqNat :
      q.1 ∉ rationalPrimeFactorizationSupport x p := by
    intro hmem
    exact hq
      ((mem_rationalPrimeFactorizationPrimeSupport_iff
        x p q).2 hmem)
  have hqNotLt :
      ¬ q.1 <
        max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1 := by
    intro hlt
    apply hqNat
    rw [rationalPrimeFactorizationSupport,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, q.2⟩
  have hbound :
      max (max (x : ℚ).num.natAbs (x : ℚ).den) p.1 + 1 ≤
        q.1 :=
    Nat.le_of_not_gt hqNotLt
  have hnumLt :
      (x : ℚ).num.natAbs < q.1 := by
    apply lt_of_lt_of_le _ hbound
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_left (x : ℚ).num.natAbs (x : ℚ).den)
          (le_max_left
            (max (x : ℚ).num.natAbs (x : ℚ).den) p.1))
  have hdenLt :
      (x : ℚ).den < q.1 := by
    apply lt_of_lt_of_le _ hbound
    exact
      Nat.lt_succ_of_le
        (le_trans
          (le_max_right (x : ℚ).num.natAbs (x : ℚ).den)
          (le_max_left
            (max (x : ℚ).num.natAbs (x : ℚ).den) p.1))
  have hnumPos :
      0 < (x : ℚ).num.natAbs :=
    Nat.pos_of_ne_zero
      (Int.natAbs_ne_zero.mpr
        (Rat.num_ne_zero.mpr x.ne_zero))
  have hdenPos :
      0 < (x : ℚ).den :=
    Nat.pos_of_ne_zero (x : ℚ).den_ne_zero
  have hqNum :
      ¬ q.1 ∣ (x : ℚ).num.natAbs :=
    Nat.not_dvd_of_pos_of_lt hnumPos hnumLt
  have hqDen :
      ¬ q.1 ∣ (x : ℚ).den :=
    Nat.not_dvd_of_pos_of_lt hdenPos hdenLt
  rw [padicValRat_def, padicValInt,
    padicValNat.eq_zero_of_not_dvd hqNum,
    padicValNat.eq_zero_of_not_dvd hqDen]
  norm_num

open scoped Classical in
/-- A chosen finite-place Artin character outside the rational
prime-factorization support is genuinely trivial. -/
@[simp]
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) (q : Nat.Primes)
    (hq :
      q ∉ rationalPrimeFactorizationPrimeSupport x p) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x q = 1 := by
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hq
      (mem_rationalPrimeFactorizationPrimeSupport x p)
  rw [rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
      p q hqp k x,
    padicValRat_eq_zero_of_not_mem_rationalPrimeFactorizationPrimeSupport
      x p q hq]
  simp only [neg_zero, zpow_zero]

open scoped Classical in
/-- The actual rational principal finite-place characters have finite
multiplicative support, contained in the ordinary rational prime
factorization support. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacters_hasFiniteMulSupport
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    HasFiniteMulSupport
      (rationalCyclotomicPrincipalFinitePlaceCharacter p k x) := by
  rw [HasFiniteMulSupport]
  apply
    (rationalPrimeFactorizationPrimeSupport x p).finite_toSet.subset
  intro q hq
  by_contra hqSupport
  exact hq
    (rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
      p k x q hqSupport)

open scoped Classical in
/-- The off-`p` finprod of the genuine chosen Artin characters is the
explicit finite product over the erased rational prime-factorization
support. -/
theorem
    rationalCyclotomicPrincipalAwayFinitePlaceCharacter_finprod_eq_factorizationProduct
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
      rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      ∏ q :
          ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
        (ZMod.unitOfCoprime q.1.1
          (q.1.2.coprime_iff_not_dvd.mpr
            (rationalPrime_not_dvd_pow_of_ne
              q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
          (-padicValRat q.1.1 (x : ℚ)) := by
  let f : Nat.Primes → (ZMod (p.1 ^ k))ˣ :=
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x
  have hfinprod :
      (∏ᶠ (q : Nat.Primes) (_ : q ≠ p), f q) =
        ∏ q ∈
            (rationalPrimeFactorizationPrimeSupport x p).erase p,
          f q := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro q hq
    constructor
    · intro hqp
      rw [Finset.mem_erase]
      refine ⟨hqp, ?_⟩
      by_contra hqSupport
      exact hq
        (rationalCyclotomicPrincipalFinitePlaceCharacter_eq_one_of_not_mem_support
          p k x q hqSupport)
    · intro hqSupport
      exact (Finset.mem_erase.mp hqSupport).1
  calc
    (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
        rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
        ∏ q ∈
            (rationalPrimeFactorizationPrimeSupport x p).erase p,
          f q := hfinprod
    _ =
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          f q.1 := by
      exact
        (Finset.prod_coe_sort
          ((rationalPrimeFactorizationPrimeSupport x p).erase p)
          f).symm
    _ =
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ)) := by
      apply Finset.prod_congr rfl
      intro q _
      change rationalCyclotomicPrincipalFinitePlaceCharacter p k x q.1 = _
      exact rationalCyclotomicPrincipalFinitePlaceCharacter_of_ne
        p q.1 (Finset.ne_of_mem_erase q.2) k x

open scoped Classical in
/-- The direct rational `p`-unit character times the explicit inverse
away-from-`p` factorization product is the reduced rational sign. -/
theorem
    rationalPrimeUnitCharacter_mul_principalAwayFactorizationProduct_eq_sign
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
          (padicIntUnitOfRat p (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p)) *
        ∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ)) =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalSignPadicUnit x p) := by
  exact
    padicIntUnitOfRat_rationalPrimeUnit_mul_primeSupportInverseFactors_toZModPow
      x p k

open scoped Classical in
private noncomputable def rationalCyclotomicPrincipalHeightOneCharacterFinprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    (ZMod (p.1 ^ k))ˣ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
    rationalCyclotomicPrincipalHeightOneCharacter p k x v

open scoped Classical in
private theorem
    rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        rationalCyclotomicPrincipalHeightOneCharacter p k x v := by
  rfl

open scoped Classical in
private theorem rationalCyclotomicPrincipalHeightOneCharacterFinprod_spec
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
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
              (IdeleGroup.principalIdele ℚ x))) := by
  calc
    rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x =
        ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          rationalCyclotomicPrincipalHeightOneCharacter p k x v :=
      rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod p k x
    _ = _ := by
      apply finprod_congr
      intro v
      exact rationalCyclotomicPrincipalHeightOneCharacter_spec p k x v

open scoped Classical in
private theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_eq_namedFinprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
          rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x := by
  rw [mul_finprod_cond_ne p
    (rationalCyclotomicPrincipalFinitePlaceCharacters_hasFiniteMulSupport
      p k x)]
  calc
    (∏ᶠ q : Nat.Primes,
        rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
        ∏ᶠ q : Nat.Primes,
          rationalCyclotomicPrincipalHeightOneCharacter p k x
            ((Rat.HeightOneSpectrum.primesEquiv
              (R := 𝓞 ℚ)).symm q) := by
      apply finprod_congr
      intro q
      exact rationalCyclotomicPrincipalFinitePlaceCharacter_spec p k x q
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
          rationalCyclotomicPrincipalHeightOneCharacter p k x v :=
      finprod_comp_equiv
        (Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ)).symm
    _ = rationalCyclotomicPrincipalHeightOneCharacterFinprod p k x :=
      (rationalCyclotomicPrincipalHeightOneCharacterFinprod_eq_finprod
        p k x).symm

open scoped Classical in
/-- Reindexing by `Rat.HeightOneSpectrum.primesEquiv` and separating the
distinguished prime identifies the height-one finprod with its genuine
`p`-factor times the off-`p` prime finprod. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_finprod
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ᶠ (q : Nat.Primes) (_ : q ≠ p),
          rationalCyclotomicPrincipalFinitePlaceCharacter p k x q) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
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
              (IdeleGroup.principalIdele ℚ x))) := by
  exact
    (rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_eq_namedFinprod
      p k x).trans
      (rationalCyclotomicPrincipalHeightOneCharacterFinprod_spec p k x)

open scoped Classical in
/-- Exact source for the final principal-product calculation: the
height-one chosen Artin finprod is the genuine `p`-factor times the
explicit away-from-`p` rational factorization product. -/
theorem
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_factorizationProduct
    (p : Nat.Primes) (k : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalFinitePlaceCharacter p k x p *
        (∏ q :
            ↥((rationalPrimeFactorizationPrimeSupport x p).erase p),
          (ZMod.unitOfCoprime q.1.1
            (q.1.2.coprime_iff_not_dvd.mpr
              (rationalPrime_not_dvd_pow_of_ne
                q.1 p (Finset.ne_of_mem_erase q.2) k))) ^
            (-padicValRat q.1.1 (x : ℚ))) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
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
              (IdeleGroup.principalIdele ℚ x))) := by
  rw [
    ←
      rationalCyclotomicPrincipalAwayFinitePlaceCharacter_finprod_eq_factorizationProduct
        p k x]
  exact
    rationalCyclotomicPrincipalFinitePlaceCharacter_prime_mul_away_finprod
      p k x

end Reciprocity
end GlobalClassFieldTheory
