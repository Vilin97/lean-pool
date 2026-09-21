/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.RationalPrime
import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.Setup
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
/-!
# Ramification support of the auxiliary compositum

Let `S` be the finite set of rational primes ramified in `L`, let
`n = ∏ p∈S, p ^ e_p`, and put `M = L(μ_n)`.  This file proves the
global ramification assertion used in the inertia count: every finite prime
of `M` outside `S` is unramified over `ℤ`.

The two factors are unramified outside `S` for different reasons.  For `L`
this is the definition of `S`; for the cyclotomic factor it is the standard
formula saying that a rational prime not dividing the conductor has
ramification index one.  An inertia automorphism of the compositum restricts
to inertia automorphisms of both factors.  Since the factors generate the
compositum, triviality of both restrictions implies triviality of the
original inertia automorphism.
-/

noncomputable section

namespace KroneckerWeber

open NumberField
open HilbertRamification.Dedekind
open AlgebraicNumberTheory.Ramification
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

section ConductorSupport

variable (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L]

/-- A rational prime outside `S` does not divide the conductor candidate,
whose prime-power factors are supported exactly on `S`. -/
theorem kroneckerWeber_prime_not_dvd_conductorCandidate
    (p : Nat.Primes)
    (hp : p ∉ kroneckerWeberRamifiedPrimes (L := L)) :
    ¬ p.1 ∣ kroneckerWeberConductorCandidate (L := L) := by
  classical
  apply p.2.coprime_iff_not_dvd.mp
  rw [kroneckerWeberConductorCandidate,
    Nat.coprime_prod_right_iff]
  intro q hq
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes p.2 q.2).2
    (Subtype.coe_ne_coe.mpr fun hpq => hp (hpq ▸ hq))

end ConductorSupport

section FactorRamification

variable (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L]

omit [IsAbelianGalois ℚ L] in
/-- The copy of `L` in any isomorphic realization has ramification index
one above a rational prime outside the defining support `S`. -/
theorem kroneckerWeber_leftFactor_ramificationIdx_eq_one
    {A : Type*} [Field A] [NumberField A]
    (eLA : L ≃ₐ[ℚ] A)
    (p : Nat.Primes)
    (hpS : p ∉ kroneckerWeberRamifiedPrimes (L := L))
    (PA : Ideal (𝓞 A)) [PA.IsPrime]
    [PA.LiesOver (rationalPrimeIdeal p)] :
    PA.ramificationIdx ℤ = 1 := by
  let eLAₒ : (𝓞 L) ≃ₐ[ℤ] (𝓞 A) :=
    (RingOfIntegers.mapAlgEquiv eLA).restrictScalars ℤ
  let PL : Ideal (𝓞 L) := PA.comap eLAₒ
  let : PL.LiesOver (rationalPrimeIdeal p) :=
    Ideal.comap_liesOver PA (rationalPrimeIdeal p) eLAₒ
  have hp0 : rationalPrimeIdeal p ≠ ⊥ :=
    (Rat.HeightOneSpectrum.primesEquiv.symm p).ne_bot
  have hPL0 : PL ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 PL
  have hPLunramified : Algebra.IsUnramifiedAt ℤ PL := by
    by_contra hram
    apply hpS
    apply (mem_kroneckerWeberRamifiedPrimes_iff
      (L := L) p).2
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
      ⟨PL, inferInstance, hPL0⟩
    exact ⟨w, inferInstance, hram⟩
  have hPLramification :
      PL.ramificationIdx ℤ = 1 :=
    Ideal.ramificationIdx_eq_one_iff.mpr hPLunramified
  calc
    PA.ramificationIdx ℤ =
        (rationalPrimeIdeal p).ramificationIdx' PA :=
      (Ideal.ramificationIdx'_eq_ramificationIdx
        (rationalPrimeIdeal p) PA hp0).symm
    _ = (rationalPrimeIdeal p).ramificationIdx' PL :=
      (Ideal.ramificationIdx'_comap_eq
        (rationalPrimeIdeal p) eLAₒ PA).symm
    _ = PL.ramificationIdx ℤ :=
      Ideal.ramificationIdx'_eq_ramificationIdx
        (rationalPrimeIdeal p) PL hp0
    _ = 1 := hPLramification

/-- The conductor cyclotomic factor has ramification index one outside
`S`, since primes outside `S` do not divide the conductor candidate. -/
theorem kroneckerWeber_cyclotomicFactor_ramificationIdx_eq_one
    {B : Type*} [Field B] [NumberField B]
    (eCB :
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ
        ≃ₐ[ℚ] B)
    (p : Nat.Primes)
    (hpS : p ∉ kroneckerWeberRamifiedPrimes (L := L))
    (PB : Ideal (𝓞 B)) [PB.IsPrime]
    [PB.LiesOver (rationalPrimeIdeal p)] :
    PB.ramificationIdx ℤ = 1 := by
  let C : Type :=
    CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ
  let : IsCyclotomicExtension
      {kroneckerWeberConductorCandidate (L := L)} ℚ C := by
    dsimp only [C]
    exact CyclotomicField.isCyclotomicExtension
      (kroneckerWeberConductorCandidate (L := L)) ℚ
  let eCBₒ : (𝓞 C) ≃ₐ[ℤ] (𝓞 B) :=
    (RingOfIntegers.mapAlgEquiv eCB).restrictScalars ℤ
  let PC : Ideal (𝓞 C) := PB.comap eCBₒ
  let : PC.LiesOver (rationalPrimeIdeal p) :=
    Ideal.comap_liesOver PB (rationalPrimeIdeal p) eCBₒ
  let : Fact (Nat.Prime p.1) := ⟨p.2⟩
  let : PC.LiesOver (Ideal.span {(p.1 : ℤ)}) := by
    rw [← rationalPrimeIdeal_eq_span p]
    infer_instance
  have hpndvd :
      ¬ p.1 ∣ kroneckerWeberConductorCandidate (L := L) :=
    kroneckerWeber_prime_not_dvd_conductorCandidate (L := L) p hpS
  have hp0 : rationalPrimeIdeal p ≠ ⊥ :=
    (Rat.HeightOneSpectrum.primesEquiv.symm p).ne_bot
  have hPCramification :
      PC.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      p.1 C PC hpndvd
  calc
    PB.ramificationIdx ℤ =
        (rationalPrimeIdeal p).ramificationIdx' PB :=
      (Ideal.ramificationIdx'_eq_ramificationIdx
        (rationalPrimeIdeal p) PB hp0).symm
    _ = (rationalPrimeIdeal p).ramificationIdx' PC :=
      (Ideal.ramificationIdx'_comap_eq
        (rationalPrimeIdeal p) eCBₒ PB).symm
    _ = PC.ramificationIdx ℤ :=
      Ideal.ramificationIdx'_eq_ramificationIdx
        (rationalPrimeIdeal p) PC hp0
    _ = 1 := hPCramification

end FactorRamification

section CompositumSupport

variable (L : Type) [Field L]
variable [hNF : NumberField L] [hLab : IsAbelianGalois ℚ L]

/-- Ramification support of a realization of the auxiliary compositum.  If
the copies of `L` and the conductor cyclotomic field generate
`M`, every finite prime of `M` outside the ramification support of `L` is
unramified over `ℤ`. -/
theorem kroneckerWeberCompositum_isUnramifiedAt_of_not_mem
    {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M]
    (A B : IntermediateField ℚ M) [Normal ℚ A] [Normal ℚ B]
    (eLA : L ≃ₐ[ℚ] A)
    (eCB :
      CyclotomicField (kroneckerWeberConductorCandidate (L := L)) ℚ
        ≃ₐ[ℚ] B)
    (hsup : A ⊔ B = ⊤)
    (Q : Ideal (𝓞 M))
    [Q.IsPrime] [Q.IsMaximal]
    (hQoutside :
      ¬ ∃ p ∈ kroneckerWeberRamifiedPrimes (L := L),
        rationalPrimeIdeal p = Q.under ℤ) :
    Algebra.IsUnramifiedAt ℤ Q := by
  classical
  let q : Ideal ℤ := Q.under ℤ
  have hQ0 : Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := Q) inferInstance (RingOfIntegers.not_isField M)
  let : q.IsPrime := inferInstance
  have hq0 : q ≠ ⊥ :=
    Ideal.under_ne_bot ℤ hQ0
  let v : IsDedekindDomain.HeightOneSpectrum ℤ :=
    ⟨q, inferInstance, hq0⟩
  let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  have hpq : rationalPrimeIdeal p = q := by
    change
      (Rat.HeightOneSpectrum.primesEquiv.symm p).asIdeal = v.asIdeal
    rw [Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply]
  have hpS : p ∉ kroneckerWeberRamifiedPrimes (L := L) := by
    intro hp
    exact hQoutside ⟨p, hp, hpq⟩

  let : Q.LiesOver (rationalPrimeIdeal p) := ⟨hpq⟩
  have hp0 : rationalPrimeIdeal p ≠ ⊥ :=
    (Rat.HeightOneSpectrum.primesEquiv.symm p).ne_bot

  let PA : Ideal (𝓞 A) := Q.under (𝓞 A)
  let PB : Ideal (𝓞 B) := Q.under (𝓞 B)
  let : Q.LiesOver PA := ⟨rfl⟩
  let : Q.LiesOver PB := ⟨rfl⟩
  let : PA.LiesOver (rationalPrimeIdeal p) :=
    Ideal.LiesOver.tower_bot Q PA (rationalPrimeIdeal p)
  let : PB.LiesOver (rationalPrimeIdeal p) :=
    Ideal.LiesOver.tower_bot Q PB (rationalPrimeIdeal p)
  have hPA0 : PA ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 PA
  have hPB0 : PB ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 PB
  let : PA.IsMaximal :=
    (inferInstance : PA.IsPrime).isMaximal hPA0
  let : PB.IsMaximal :=
    (inferInstance : PB.IsPrime).isMaximal hPB0

  have hPAramification :
      PA.ramificationIdx ℤ = 1 :=
    kroneckerWeber_leftFactor_ramificationIdx_eq_one
      (L := L) eLA p hpS PA
  have hPBramification :
      PB.ramificationIdx ℤ = 1 :=
    kroneckerWeber_cyclotomicFactor_ramificationIdx_eq_one
      (L := L) eCB p hpS PB

  let aAlg : Algebra ℚ A := inferInstance
  let hANormal : @Normal ℚ A _ _ aAlg := inferInstance
  let hAAlg : Algebra ℚ A := A.algebra'
  have hAAlg_eq : aAlg = hAAlg := Subsingleton.elim _ _
  cases hAAlg_eq
  let : Normal ℚ A := hANormal
  let bAlg : Algebra ℚ B := inferInstance
  let hBNormal : @Normal ℚ B _ _ bAlg := inferInstance
  let hBAlg : Algebra ℚ B := B.algebra'
  have hBAlg_eq : bAlg = hBAlg := Subsingleton.elim _ _
  cases hBAlg_eq
  let : Normal ℚ B := hBNormal
  let hAGalois : IsGalois ℚ A :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let hBGalois : IsGalois ℚ B :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hIA : inertiaGroup PA Gal(A/ℚ) = ⊥ :=
    @inertiaGroup_eq_bot_of_ramificationIdx_eq_one_int A _ _ hAGalois
      (rationalPrimeIdeal p) PA _ _ _ _ hp0 hPAramification
  have hIB : inertiaGroup PB Gal(B/ℚ) = ⊥ :=
    @inertiaGroup_eq_bot_of_ramificationIdx_eq_one_int B _ _ hBGalois
      (rationalPrimeIdeal p) PB _ _ _ _ hp0 hPBramification

  have hIM : inertiaGroup Q Gal(M/ℚ) = ⊥ :=
    inertiaGroup_eq_bot_of_restrictNormal_of_sup_eq_top
      A B Q hsup (by simpa only [PA] using hIA)
      (by simpa only [PB] using hIB)
  exact isUnramifiedAt_int_of_inertiaGroup_eq_bot Q hIM

end CompositumSupport

end KroneckerWeber

end
