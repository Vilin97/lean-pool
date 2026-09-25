/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms
/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


namespace RayClass

open scoped Classical in
local instance rationalRingOfIntegersIsPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

attribute [local instance] rationalRingOfIntegersIsPrincipalIdealRing

open scoped Classical in
local instance rationalNatGeneratorPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩

attribute [local instance] rationalNatGeneratorPrimeFact

open scoped Classical in
local instance rationalPrimesEquivPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩

attribute [local instance] rationalPrimesEquivPrimeFact

open scoped Classical in
/-- The height-one prime of `𝓞 ℚ` associated with a natural prime. -/
noncomputable abbrev rationalPrime (p : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

open scoped Classical in
@[simp]
theorem natGenerator_rationalPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrime p) = p := by
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

open scoped Classical in
theorem rational_natGenerator_injective :
    Function.Injective
      (Rat.HeightOneSpectrum.natGenerator :
        HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v w hvw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext hvw

open scoped Classical in
/-- The finite part of the modulus `(m)` of `ℚ`.  At the prime over `p` it has
exponent `m.factorization p`. The later equivalences use the hypothesis
`0 < m`; the definition itself is harmless at `m = 0`.
-/
noncomputable def rationalFiniteModulus (m : ℕ) : FiniteModulus ℚ :=
  Finsupp.comapDomain
    Rat.HeightOneSpectrum.natGenerator
    m.factorization
    rational_natGenerator_injective.injOn

open scoped Classical in
@[simp]
theorem rationalFiniteModulus_apply
    (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalFiniteModulus m v =
      m.factorization (Rat.HeightOneSpectrum.natGenerator v) := by
  rw [rationalFiniteModulus, Finsupp.comapDomain_apply]

open scoped Classical in
/-- The full rational ray modulus has the finite part `(m)` and positivity
at the unique real place. -/
noncomputable def rationalModulus (m : ℕ) : Modulus ℚ :=
  Modulus.narrowOfFinite (rationalFiniteModulus m)

open scoped Classical in
@[simp]
theorem rationalModulus_finitePart_apply
    (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (rationalModulus m).finitePart v =
      m.factorization (Rat.HeightOneSpectrum.natGenerator v) := by
  rw [rationalModulus, Modulus.finitePart_narrowOfFinite,
    rationalFiniteModulus_apply]

open scoped Classical in
theorem mem_rationalFiniteModulus_support_iff
    {m : ℕ} (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ (rationalFiniteModulus m).support ↔
      Rat.HeightOneSpectrum.natGenerator v ∣ m := by
  rw [Finsupp.mem_support_iff, rationalFiniteModulus_apply]
  constructor
  · exact Nat.dvd_of_factorization_pos
  · intro hdiv
    exact (Rat.HeightOneSpectrum.prime_natGenerator v).factorization_pos_of_dvd hm hdiv |>.ne'

open scoped Classical in
/-- The fractional ideal underlying a rational fractional-ideal unit. -/
abbrev rationalFractionalIdeal (I : FractionalIdealGroup ℚ) :
    FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ :=
  I

open scoped Classical in
/-- An arbitrary principal generator of a nonzero rational fractional
ideal, before choosing its sign. -/
private noncomputable def rawRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  Submodule.IsPrincipal.generator
    ((rationalFractionalIdeal I : FractionalIdeal
      (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)

open scoped Classical in
private theorem rawRationalIdealGenerator_ne_zero
    (I : FractionalIdealGroup ℚ) :
    rawRationalIdealGenerator I ≠ 0 := by
  apply mt
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      ((rationalFractionalIdeal I : FractionalIdeal
        (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)).2
  exact FractionalIdeal.coeToSubmodule_ne_bot.mpr (Units.ne_zero I)

open scoped Classical in
/-- The unique positive generator of a nonzero rational fractional ideal. -/
noncomputable def positiveRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  if 0 < rawRationalIdealGenerator I then
    rawRationalIdealGenerator I
  else
    -rawRationalIdealGenerator I

open scoped Classical in
theorem positiveRationalIdealGenerator_pos
    (I : FractionalIdealGroup ℚ) :
    0 < positiveRationalIdealGenerator I := by
  rw [positiveRationalIdealGenerator]
  split_ifs with h
  · exact h
  · exact neg_pos.mpr
      (lt_of_le_of_ne (not_lt.mp h)
        (rawRationalIdealGenerator_ne_zero I))

open scoped Classical in
theorem rationalFractionalIdeal_eq_span_positiveGenerator
    (I : FractionalIdealGroup ℚ) :
    rationalFractionalIdeal I =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) := by
  calc
    rationalFractionalIdeal I =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (rawRationalIdealGenerator I) :=
      FractionalIdeal.eq_spanSingleton_of_principal _
    _ = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (positiveRationalIdealGenerator I) := by
      rw [positiveRationalIdealGenerator]
      split_ifs with h
      · rfl
      · apply
          (FractionalIdeal.spanSingleton_eq_spanSingleton
            (S := nonZeroDivisors (𝓞 ℚ))).2
        refine ⟨-1, ?_⟩
        simp

open scoped Classical in
/-- Positive rational generators of the same principal fractional ideal
are equal. -/
theorem eq_of_spanSingleton_eq_of_pos
    {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) x =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) y) :
    x = y := by
  obtain ⟨u, hu⟩ :=
    (FractionalIdeal.spanSingleton_eq_spanSingleton
      (S := nonZeroDivisors (𝓞 ℚ))).1 h
  rcases Rat.RingOfIntegers.isUnit_iff.mp u.isUnit with hu1 | hu1
  · simpa [Units.smul_def, Algebra.smul_def, hu1] using hu
  · have hxy : -x = y := by
      simpa [Units.smul_def, Algebra.smul_def, hu1] using hu
    linarith

open scoped Classical in
@[simp]
theorem positiveRationalIdealGenerator_one :
    positiveRationalIdealGenerator (1 : FractionalIdealGroup ℚ) = 1 := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos 1) zero_lt_one
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator]
  exact FractionalIdeal.spanSingleton_one.symm

open scoped Classical in
theorem positiveRationalIdealGenerator_mul
    (I J : FractionalIdealGroup ℚ) :
    positiveRationalIdealGenerator (I * J) =
      positiveRationalIdealGenerator I *
        positiveRationalIdealGenerator J := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos (I * J))
    (mul_pos (positiveRationalIdealGenerator_pos I)
      (positiveRationalIdealGenerator_pos J))
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← rationalFractionalIdeal_eq_span_positiveGenerator]
  rfl

open scoped Classical in
/-- The positive generator, regarded as a nonzero rational number. -/
noncomputable def positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) : ℚˣ :=
  Units.mk0 (positiveRationalIdealGenerator I)
    (ne_of_gt (positiveRationalIdealGenerator_pos I))

open scoped Classical in
@[simp]
theorem positiveRationalIdealGeneratorUnit_val
    (I : FractionalIdealGroup ℚ) :
    (positiveRationalIdealGeneratorUnit I : ℚ) =
      positiveRationalIdealGenerator I :=
  rfl

open scoped Classical in
theorem toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) :
    toPrincipalIdeal (𝓞 ℚ) ℚ
        (positiveRationalIdealGeneratorUnit I) = I := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) =
      rationalFractionalIdeal I
  exact (rationalFractionalIdeal_eq_span_positiveGenerator I).symm

open scoped Classical in
@[simp]
theorem positiveRationalIdealGeneratorUnit_one :
    positiveRationalIdealGeneratorUnit
      (1 : FractionalIdealGroup ℚ) = 1 := by
  apply Units.ext
  exact positiveRationalIdealGenerator_one

open scoped Classical in
theorem positiveRationalIdealGeneratorUnit_mul
    (I J : FractionalIdealGroup ℚ) :
    positiveRationalIdealGeneratorUnit (I * J) =
      positiveRationalIdealGeneratorUnit I *
        positiveRationalIdealGeneratorUnit J := by
  apply Units.ext
  exact positiveRationalIdealGenerator_mul I J

open scoped Classical in
/-- An element of `WithZero (Multiplicative ℤ)` with logarithm zero is
one. -/
theorem withZero_eq_one_of_log_eq_zero
    {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hlog : WithZero.log x = 0) :
    x = 1 := by
  calc
    x = WithZero.exp (WithZero.log x) :=
      (WithZero.exp_log hx).symm
    _ = WithZero.exp 0 := congrArg WithZero.exp hlog
    _ = 1 := rfl

open scoped Classical in
/-- Zero principal-ideal exponent at a rational finite place forces
valuation one. -/
theorem valuation_eq_one_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    v.valuation ℚ (x : ℚ) = 1 := by
  rw [IdeleGroup.count_toPrincipalIdeal] at hcount
  have hlog :
      WithZero.log (v.valuation ℚ (x : ℚ)) = 0 :=
    neg_eq_zero.mp hcount
  have hvne : v.valuation ℚ (x : ℚ) ≠ 0 :=
    (v.valuation ℚ).ne_zero_of_unit x
  exact withZero_eq_one_of_log_eq_zero hvne hlog

open scoped Classical in
/-- A rational prime with zero principal-ideal exponent does not divide
the denominator. -/
theorem not_dvd_den_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).den := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hequiv :=
    Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hpval : Rat.padicValuation p (x : ℚ) = 1 :=
    hequiv.eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  apply Rat.padicValuation_le_one_iff.mp
  exact le_of_eq hpval

open scoped Classical in
/-- A rational prime with zero principal-ideal exponent does not divide
the numerator. -/
theorem not_dvd_num_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).num.natAbs := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpval :
      Rat.padicValuation p (x : ℚ) = 1 :=
    (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  have hden : ¬ p ∣ (x : ℚ).den :=
    not_dvd_den_of_principal_count_eq_zero x v hcount
  have hdenval :
      Int.padicValuation p ((x : ℚ).den : ℤ) = 1 :=
    Int.padicValuation_eq_one_iff.mpr
      (by simpa only [Int.natCast_dvd_natCast] using hden)
  rw [← (x : ℚ).num_div_den, map_div₀,
    Rat.padicValuation_cast, ← Int.cast_natCast,
    Rat.padicValuation_cast, hdenval, div_one] at hpval
  exact fun hpdiv =>
    (Int.padicValuation_eq_one_iff.mp hpval)
      (Int.natCast_dvd.mpr hpdiv)

open scoped Classical in
theorem positiveGenerator_den_coprime
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    Nat.Coprime
      (positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ)).den m := by
  rw [Nat.coprime_comm]
  by_contra hcop
  obtain ⟨p, hp, hpm, hpden⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  let v := rationalPrime ⟨p, hp⟩
  have hvgen : Rat.HeightOneSpectrum.natGenerator v = p :=
    natGenerator_rationalPrime ⟨p, hp⟩
  have hv : v ∈ (rationalModulus m).finitePart.support := by
    rw [rationalModulus, Modulus.finitePart_narrowOfFinite]
    rw [mem_rationalFiniteModulus_support_iff hm]
    rw [hvgen]
    exact hpm
  have hcount := I.property v hv
  rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ)] at hcount
  exact
    (not_dvd_den_of_principal_count_eq_zero
      (positiveRationalIdealGeneratorUnit
        (I : FractionalIdealGroup ℚ)) v hcount)
      (by
        rw [hvgen]
        exact hpden)

open scoped Classical in
theorem positiveGenerator_num_coprime
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    Nat.Coprime
      (positiveRationalIdealGenerator
        (I : FractionalIdealGroup ℚ)).num.natAbs m := by
  rw [Nat.coprime_comm]
  by_contra hcop
  obtain ⟨p, hp, hpm, hpnum⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  let v := rationalPrime ⟨p, hp⟩
  have hvgen : Rat.HeightOneSpectrum.natGenerator v = p :=
    natGenerator_rationalPrime ⟨p, hp⟩
  have hv : v ∈ (rationalModulus m).finitePart.support := by
    rw [rationalModulus, Modulus.finitePart_narrowOfFinite]
    rw [mem_rationalFiniteModulus_support_iff hm]
    rw [hvgen]
    exact hpm
  have hcount := I.property v hv
  rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ)] at hcount
  exact
    (not_dvd_num_of_principal_count_eq_zero
      (positiveRationalIdealGeneratorUnit
        (I : FractionalIdealGroup ℚ)) v hcount)
      (by
        rw [hvgen]
        exact hpnum)

open scoped Classical in
/-- The numerator of a rational number as a residue-class unit. -/
def rationalNumeratorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.num.natAbs m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime q.num <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

open scoped Classical in
/-- The denominator of a rational number as a residue-class unit. -/
def rationalDenominatorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime (q.den : ℤ) <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

open scoped Classical in
/-- Reduction of a rational number whose numerator and denominator are
both prime to `m`. -/
def rationalResidueUnit
    (m : ℕ) (q : ℚ)
    (hnum : Nat.Coprime q.num.natAbs m)
    (hden : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  rationalNumeratorResidueUnit m q hnum *
    (rationalDenominatorResidueUnit m q hden)⁻¹

open scoped Classical in
/-- Rational residue units are independent of the chosen equality proof. -/
theorem rationalResidueUnit_congr
    (m : ℕ) {q r : ℚ} (hqr : q = r)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m) :
    rationalResidueUnit m q hqnum hqden =
      rationalResidueUnit m r hrnum hrden := by
  subst r
  rfl

open scoped Classical in
/-- Reduction of rational numbers prime to a modulus is multiplicative. -/
theorem rationalResidueUnit_mul
    (m : ℕ) (q r : ℚ)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m)
    (hqrnum : Nat.Coprime (q * r).num.natAbs m)
    (hqrden : Nat.Coprime (q * r).den m) :
    rationalResidueUnit m (q * r) hqrnum hqrden =
      rationalResidueUnit m q hqnum hqden *
        rationalResidueUnit m r hrnum hrden := by
  let Nq := rationalNumeratorResidueUnit m q hqnum
  let Dq := rationalDenominatorResidueUnit m q hqden
  let Nr := rationalNumeratorResidueUnit m r hrnum
  let Dr := rationalDenominatorResidueUnit m r hrden
  let Nqr := rationalNumeratorResidueUnit m (q * r) hqrnum
  let Dqr := rationalDenominatorResidueUnit m (q * r) hqrden
  have hcross : Nqr * Dq * Dr = Nq * Nr * Dqr := by
    apply Units.ext
    have h :=
      congrArg (Int.castRingHom (ZMod m)) (Rat.mul_num_den' q r)
    simpa [Nq, Dq, Nr, Dr, Nqr, Dqr,
      rationalNumeratorResidueUnit,
      rationalDenominatorResidueUnit, map_mul] using h
  change Nqr * Dqr⁻¹ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹)
  calc
    Nqr * Dqr⁻¹ =
        (Nqr * Dq * Dr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (Nq * Nr * Dqr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      rw [hcross]
    _ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]

open scoped Classical in
/-- The rational residue unit of one is one. -/
theorem rationalResidueUnit_one (m : ℕ) :
    rationalResidueUnit m 1 (by simp) (by simp) = 1 := by
  apply Units.ext
  simp [rationalResidueUnit, rationalNumeratorResidueUnit,
    rationalDenominatorResidueUnit]

open scoped Classical in
/-- A rational residue unit is one exactly when its numerator and
denominator are congruent modulo the modulus. -/
theorem rationalResidueUnit_eq_one_iff_modEq
    (m : ℕ) (q : ℚ)
    (hnum : Nat.Coprime q.num.natAbs m)
    (hden : Nat.Coprime q.den m) :
    rationalResidueUnit m q hnum hden = 1 ↔
      q.num ≡ (q.den : ℤ) [ZMOD m] := by
  let N := rationalNumeratorResidueUnit m q hnum
  let D := rationalDenominatorResidueUnit m q hden
  rw [← ZMod.intCast_eq_intCast_iff]
  constructor
  · intro h
    have hND : N = D := by
      calc
        N = (N * D⁻¹) * D := by simp
        _ = (1 : (ZMod m)ˣ) * D := by
          rw [show N * D⁻¹ = 1 by
            simpa only [N, D, rationalResidueUnit] using h]
        _ = D := one_mul D
    exact congrArg Units.val hND
  · intro hND
    have hND' : N = D := by
      apply Units.ext
      exact hND
    change N * D⁻¹ = 1
    rw [hND']
    exact mul_inv_cancel D

open scoped Classical in
/-- Send an ideal prime to `(m)` to the residue class of its positive
generator. -/
noncomputable def primeToIdealResidueHom
    (m : ℕ) (hm : m ≠ 0) :
    primeToModulusIdeals (rationalModulus m) →* (ZMod m)ˣ where
  toFun I :=
    rationalResidueUnit m
      (positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ))
      (positiveGenerator_num_coprime hm I)
      (positiveGenerator_den_coprime hm I)
  map_one' := by
    change rationalResidueUnit m
      (positiveRationalIdealGenerator
        (1 : FractionalIdealGroup ℚ)) _ _ = 1
    calc
      rationalResidueUnit m
          (positiveRationalIdealGenerator
            (1 : FractionalIdealGroup ℚ)) _ _ =
        rationalResidueUnit m 1 (by simp) (by simp) :=
          rationalResidueUnit_congr m
            positiveRationalIdealGenerator_one _ _ _ _
      _ = 1 := rationalResidueUnit_one m
  map_mul' I J := by
    let q :=
      positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ)
    let r :=
      positiveRationalIdealGenerator (J : FractionalIdealGroup ℚ)
    have hprodnum : Nat.Coprime (q * r).num.natAbs m := by
      rw [← positiveRationalIdealGenerator_mul]
      exact positiveGenerator_num_coprime hm (I * J)
    have hprodden : Nat.Coprime (q * r).den m := by
      rw [← positiveRationalIdealGenerator_mul]
      exact positiveGenerator_den_coprime hm (I * J)
    change rationalResidueUnit m
        (positiveRationalIdealGenerator
          ((I : FractionalIdealGroup ℚ) *
            (J : FractionalIdealGroup ℚ))) _ _ =
      rationalResidueUnit m q _ _ * rationalResidueUnit m r _ _
    calc
      rationalResidueUnit m
          (positiveRationalIdealGenerator
            ((I : FractionalIdealGroup ℚ) *
              (J : FractionalIdealGroup ℚ))) _ _ =
        rationalResidueUnit m (q * r) hprodnum hprodden :=
          rationalResidueUnit_congr m
            (positiveRationalIdealGenerator_mul I J) _ _ _ _
      _ = rationalResidueUnit m q
              (positiveGenerator_num_coprime hm I)
              (positiveGenerator_den_coprime hm I) *
            rationalResidueUnit m r
              (positiveGenerator_num_coprime hm J)
              (positiveGenerator_den_coprime hm J) :=
        rationalResidueUnit_mul m q r
          (positiveGenerator_num_coprime hm I)
          (positiveGenerator_den_coprime hm I)
          (positiveGenerator_num_coprime hm J)
          (positiveGenerator_den_coprime hm J)
          hprodnum hprodden

open scoped Classical in
@[simp]
theorem primeToIdealResidueHom_apply
    (m : ℕ) (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    primeToIdealResidueHom m hm I =
      rationalResidueUnit m
        (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ))
        (positiveGenerator_num_coprime hm I)
        (positiveGenerator_den_coprime hm I) :=
  rfl

open scoped Classical in
/-- A positive integer prime to the modulus defines a principal ideal in
the prime-to-modulus ideal group. -/
theorem principalNat_mem_primeToModulusIdeals
    {m a : ℕ} (hm : m ≠ 0) (ha : a ≠ 0)
    (hcop : Nat.Coprime a m) :
    toPrincipalIdeal (𝓞 ℚ) ℚ
        (Units.mk0 (a : ℚ) (by exact_mod_cast ha)) ∈
      primeToModulusIdeals (rationalModulus m) := by
  intro v hv
  let p := Rat.HeightOneSpectrum.natGenerator v
  have hp : p.Prime :=
    Rat.HeightOneSpectrum.prime_natGenerator v
  have hpm : p ∣ m :=
    (by
      rw [rationalModulus, Modulus.finitePart_narrowOfFinite] at hv
      exact (mem_rationalFiniteModulus_support_iff hm v).mp hv)
  have hpa : ¬ p ∣ a :=
    hp.coprime_iff_not_dvd.mp
      (hcop.coprime_dvd_right hpm).symm
  let : Fact p.Prime := ⟨hp⟩
  have hpval : Rat.padicValuation p (a : ℚ) = 1 := by
    rw [← Int.cast_natCast, Rat.padicValuation_cast]
    exact Int.padicValuation_eq_one_iff.mpr
      (by simpa only [Int.natCast_dvd_natCast] using hpa)
  have hequiv :=
    Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hvval : v.valuation ℚ (a : ℚ) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr hpval
  rw [IdeleGroup.count_toPrincipalIdeal]
  change -WithZero.log (v.valuation ℚ (a : ℚ)) = 0
  rw [hvval]
  rfl

open scoped Classical in
/-- The positive generator of the principal ideal of a positive integer is
that integer. -/
theorem positiveGenerator_toPrincipalIdeal_nat
    {a : ℕ} (ha : 0 < a) :
    positiveRationalIdealGenerator
        (toPrincipalIdeal (𝓞 ℚ) ℚ
          (Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne'))) =
      (a : ℚ) := by
  let x : ℚˣ :=
    Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne')
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos _)
    (by exact_mod_cast ha)
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator]
  calc
    rationalFractionalIdeal
        (toPrincipalIdeal (𝓞 ℚ) ℚ x) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (x : ℚ) := by
          simpa only [rationalFractionalIdeal] using
            (coe_toPrincipalIdeal (R := 𝓞 ℚ) (K := ℚ) x)
    _ = FractionalIdeal.spanSingleton
        (nonZeroDivisors (𝓞 ℚ)) (a : ℚ) := rfl

open scoped Classical in
/-- The numerator residue unit of a positive natural cast is its residue
unit. -/
theorem rationalNumeratorResidueUnit_natCast
    (m a : ℕ) (hcop : Nat.Coprime a m) :
    (rationalNumeratorResidueUnit m (a : ℚ)
        (by simpa using hcop) : ZMod m) =
      (a : ZMod m) := by
  simp [rationalNumeratorResidueUnit]

open scoped Classical in
/-- The denominator residue unit of a positive natural cast is one. -/
theorem rationalDenominatorResidueUnit_natCast
    (m a : ℕ) (hden : Nat.Coprime ((a : ℚ).den) m) :
    rationalDenominatorResidueUnit m (a : ℚ) hden = 1 := by
  apply Units.ext
  simp [rationalDenominatorResidueUnit]

open scoped Classical in
/-- Rational reduction of a positive natural cast agrees with ordinary
residue reduction. -/
theorem rationalResidueUnit_natCast
    (m a : ℕ) (hcop : Nat.Coprime a m) :
    (rationalResidueUnit m (a : ℚ)
        (by simpa using hcop) (by simp) : ZMod m) =
      (a : ZMod m) := by
  have hden :
      rationalDenominatorResidueUnit m (a : ℚ) (by simp) = 1 :=
    rationalDenominatorResidueUnit_natCast m a (by simp)
  change
    (rationalNumeratorResidueUnit m (a : ℚ) _ *
      (rationalDenominatorResidueUnit m (a : ℚ) _)⁻¹ :
        (ZMod m)ˣ) =
      (a : ZMod m)
  rw [hden, inv_one, mul_one]
  exact rationalNumeratorResidueUnit_natCast m a hcop

open scoped Classical in
theorem primeToIdealResidueHom_surjective
    (m : ℕ) (hm : m ≠ 0) :
    Function.Surjective (primeToIdealResidueHom m hm) := by
  intro u
  let a : ℕ := (u : ZMod m).val + m
  have ha : 0 < a :=
    Nat.add_pos_right _ (Nat.pos_of_ne_zero hm)
  have hcop : Nat.Coprime a m := by
    change Nat.Coprime ((u : ZMod m).val + m) m
    rw [Nat.coprime_add_self_left]
    exact ZMod.val_coe_unit_coprime u
  let x : ℚˣ :=
    Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne')
  let I : primeToModulusIdeals (rationalModulus m) :=
    ⟨toPrincipalIdeal (𝓞 ℚ) ℚ x,
      principalNat_mem_primeToModulusIdeals hm ha.ne' hcop⟩
  refine ⟨I, ?_⟩
  have hgen :
      positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ) = (a : ℚ) := by
    exact positiveGenerator_toPrincipalIdeal_nat ha
  have hanum :
      Nat.Coprime ((a : ℚ).num.natAbs) m := by
    simpa using hcop
  have haden : Nat.Coprime ((a : ℚ).den) m := by
    simp
  apply Units.ext
  change
    (rationalResidueUnit m
      (positiveRationalIdealGenerator
        (I : FractionalIdealGroup ℚ)) _ _ : ZMod m) =
      (u : ZMod m)
  calc
    (rationalResidueUnit m
        (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ)) _ _ : ZMod m) =
      (rationalResidueUnit m (a : ℚ) hanum haden : ZMod m) :=
        congrArg Units.val
          (rationalResidueUnit_congr m hgen _ _ hanum haden)
    _ = (a : ZMod m) := rationalResidueUnit_natCast m a hcop
    _ = (u : ZMod m) := by
      let : NeZero m := ⟨hm⟩
      change (((u : ZMod m).val + m : ℕ) : ZMod m) =
        (u : ZMod m)
      rw [Nat.cast_add, ZMod.natCast_self, add_zero,
        ZMod.natCast_zmod_val]

/-! ### The local congruence condition over `ℚ` -/

open scoped Classical in
/-- The integral local unit attached to a rational principal idele
component. -/
def principalLocalIntegralUnit
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    (v.adicCompletionIntegers ℚ).units :=
  ⟨(IdeleGroup.principalIdele ℚ x).2 v, by
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    have hcomp :=
      IdeleGroup.finiteComponent_principalIdele x v
    rw [IdeleGroup.finiteComponent_apply] at hcomp
    rw [hcomp]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]⟩

open scoped Classical in
/-- The integral value underlying a rational principal local unit. -/
def rationalLocalIntegralValue
    (v : HeightOneSpectrum (𝓞 ℚ))
    (y : (v.adicCompletionIntegers ℚ).units) :
    v.adicCompletionIntegers ℚ :=
  ((v.adicCompletionIntegers ℚ).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers ℚ)ˣ).1

open scoped Classical in
/-- The residue criterion for a rational principal local unit to lie in a
higher-unit group. -/
theorem rationalLocalHigherUnitMap_eq_one_iff
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (y : (v.adicCompletionIntegers ℚ).units) :
    localHigherUnitMap v n y = 1 ↔
      rationalLocalIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers ℚ)) ^ n := by
  let M :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) ^ n
  change
    Units.map (Ideal.Quotient.mk M).toMonoidHom
        ((v.adicCompletionIntegers ℚ).toSubmonoid.unitsEquivUnitsType y) =
      1 ↔ _
  rw [Units.ext_iff]
  change
    Ideal.Quotient.mk M (rationalLocalIntegralValue v y) =
      Ideal.Quotient.mk M 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := M) (rationalLocalIntegralValue v y) 1

open scoped Classical in
/-- Coercing the integral local value recovers the principal finite
component. -/
theorem principalLocalIntegralValue_coe
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    (rationalLocalIntegralValue v
      (principalLocalIntegralUnit v x hx) :
        v.adicCompletion ℚ) =
      NumberField.FinitePlace.embedding v (x : ℚ) := by
  change
    ((((IdeleGroup.principalIdele ℚ x).2 v :
      (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      NumberField.FinitePlace.embedding v (x : ℚ)
  have hcomp :=
    IdeleGroup.finiteComponent_principalIdele x v
  rw [IdeleGroup.finiteComponent_apply] at hcomp
  exact hcomp

open scoped Classical in
/-- The rational adic-completion equivalence maps powers of maximal
ideals to the corresponding powers in the padic integers. -/
theorem map_maximalIdeal_pow_padicIntEquiv
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((IsLocalRing.maximalIdeal
        (v.adicCompletionIntegers ℚ)) ^ n).map
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv =
      Ideal.span
        {(((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) :
          ℤ_[((Rat.HeightOneSpectrum.primesEquiv
            (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)]) ^ n} := by
  rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]

open scoped Classical in
/-- Membership of the local integral difference in a maximal-ideal power
is equivalent to the corresponding padic divisibility condition. -/
theorem rationalLocalIntegralValue_sub_mem_iff
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (z : v.adicCompletionIntegers ℚ) :
    z - 1 ∈
        (IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers ℚ)) ^ n ↔
      PadicInt.toZModPow n
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v z) =
        1 := by
  let e :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let M :=
    (IsLocalRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) ^ n
  constructor
  · intro hz
    have hez : e (z - 1) ∈ M.map e.toRingEquiv :=
      (Ideal.apply_mem_of_equiv_iff
        (I := M) (f := e.toRingEquiv) (x := z - 1)).2 hz
    rw [map_maximalIdeal_pow_padicIntEquiv,
      ← PadicInt.ker_toZModPow n] at hez
    have hzero :
        PadicInt.toZModPow n (e (z - 1)) = 0 :=
      (RingHom.mem_ker).1 hez
    simpa only [map_sub, map_one, sub_eq_zero] using hzero
  · intro hz
    have hzero :
        PadicInt.toZModPow n (e (z - 1)) = 0 := by
      simpa only [map_sub, map_one, sub_eq_zero] using hz
    have hez :
        e (z - 1) ∈ RingHom.ker (PadicInt.toZModPow n) :=
      (RingHom.mem_ker).2 hzero
    rw [PadicInt.ker_toZModPow,
      ← map_maximalIdeal_pow_padicIntEquiv] at hez
    exact
      (Ideal.apply_mem_of_equiv_iff
        (I := M) (f := e.toRingEquiv) (x := z - 1)).1 hez

open scoped Classical in
/-- The rational-prime equivalence identifies the local prime value with
the natural prime generator. -/
@[simp]
theorem primesEquiv_val_eq_natGenerator
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) =
      Rat.HeightOneSpectrum.natGenerator v :=
  rfl

open scoped Classical in
/-- A rational principal finite component lies in a higher-unit group
exactly when its numerator and denominator satisfy the local congruence. -/
theorem principalFiniteComponent_mem_localHigherUnitGroup_iff
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    (IdeleGroup.principalIdele ℚ x).2 v ∈
        localHigherUnitGroup v n ↔
      localHigherUnitMap v n
        (principalLocalIntegralUnit v x hx) = 1 := by
  rw [mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, hy, hymap⟩
    have hy' :
        y = principalLocalIntegralUnit v x hx := by
      apply Subtype.ext
      exact hy
    simpa only [hy'] using hymap
  · intro hmap
    exact ⟨principalLocalIntegralUnit v x hx, rfl, hmap⟩

open scoped Classical in
/-- Multiplying a rational number by its denominator gives its numerator. -/
theorem rational_den_mul_self_eq_num (q : ℚ) :
    (q.den : ℚ) * q = q.num := by
  have hden : (q.den : ℚ) ≠ 0 := by
    exact_mod_cast q.den_ne_zero
  have h := (div_eq_iff hden).mp q.num_div_den
  simpa only [mul_comm] using h.symm

open scoped Classical in
/-- Multiplying the principal local integral value by the denominator
gives the numerator in the completion. -/
theorem principalLocalIntegralValue_den_mul
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    algebraMap ℤ (v.adicCompletionIntegers ℚ) (x : ℚ).den *
        rationalLocalIntegralValue v
          (principalLocalIntegralUnit v x hx) =
      algebraMap ℤ (v.adicCompletionIntegers ℚ) (x : ℚ).num := by
  apply Subtype.ext
  simp only [algebraMap_int_eq, map_natCast, MulMemClass.coe_mul,
    SubringClass.coe_natCast, principalLocalIntegralValue_coe,
    eq_ratCast, eq_intCast, SubringClass.coe_intCast]
  simpa only [map_mul, map_natCast, map_intCast,
    NumberField.FinitePlace.embedding_apply, eq_ratCast] using
    congrArg (NumberField.FinitePlace.embedding v)
      (rational_den_mul_self_eq_num (x : ℚ))

open scoped Classical in
/-- The positive rational prime attached to a finite place. -/
abbrev rationalPadicPrime
    (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  ((Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)

open scoped Classical in
/-- In the local residue ring, the denominator times the principal value
equals the numerator. -/
theorem principalLocalResidue_den_mul
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    ((x : ℚ).den : ZMod (rationalPadicPrime v ^ n)) *
        PadicInt.toZModPow n
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
            (rationalLocalIntegralValue v
              (principalLocalIntegralUnit v x hx))) =
      ((x : ℚ).num : ZMod (rationalPadicPrime v ^ n)) := by
  let e :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  have he :=
    congrArg e
      (principalLocalIntegralValue_den_mul v x hx)
  have hden :
      e (algebraMap ℤ (v.adicCompletionIntegers ℚ)
          ((x : ℚ).den : ℤ)) =
        algebraMap ℤ _ ((x : ℚ).den : ℤ) := by
    change e.toAlgEquiv
        (algebraMap ℤ (v.adicCompletionIntegers ℚ)
          ((x : ℚ).den : ℤ)) =
      algebraMap ℤ _ ((x : ℚ).den : ℤ)
    exact e.commutes ((x : ℚ).den : ℤ)
  have hnum :
      e (algebraMap ℤ (v.adicCompletionIntegers ℚ)
          (x : ℚ).num) =
        algebraMap ℤ _ (x : ℚ).num := by
    change e.toAlgEquiv
        (algebraMap ℤ (v.adicCompletionIntegers ℚ)
          (x : ℚ).num) =
      algebraMap ℤ _ (x : ℚ).num
    exact e.commutes (x : ℚ).num
  have he' := he
  rw [map_mul, hden, hnum] at he'
  have hz :=
    congrArg (PadicInt.toZModPow n) he'
  have hnumZ :
      PadicInt.toZModPow n
          (algebraMap ℤ ℤ_[rationalPadicPrime v] (x : ℚ).num) =
        ((x : ℚ).num : ZMod (rationalPadicPrime v ^ n)) := by
    have hcomp :
        (PadicInt.toZModPow n).comp
            (algebraMap ℤ ℤ_[rationalPadicPrime v]) =
          algebraMap ℤ (ZMod (rationalPadicPrime v ^ n)) :=
      RingHom.ext_int _ _
    exact DFunLike.congr_fun hcomp (x : ℚ).num
  rw [hnumZ] at hz
  dsimp only [e] at hz
  simpa only [algebraMap_int_eq, map_mul, map_natCast, map_intCast,
    Int.cast_natCast] using hz

open scoped Classical in
/-- Valuation one at a rational finite place implies that its prime does
not divide the denominator. -/
theorem not_dvd_den_of_valuation_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).den := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpval : Rat.padicValuation p (x : ℚ) = 1 :=
    (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp hx
  exact Rat.padicValuation_le_one_iff.mp (le_of_eq hpval)

open scoped Classical in
/-- Rational principal higher-unit membership is equivalent to a
prime-power congruence of numerator and denominator. -/
theorem principalLocalHigherUnit_iff_modEq
    (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (x : ℚˣ)
    (hx : v.valuation ℚ (x : ℚ) = 1) :
    (IdeleGroup.principalIdele ℚ x).2 v ∈
        localHigherUnitGroup v n ↔
      (x : ℚ).num ≡ ((x : ℚ).den : ℤ)
        [ZMOD (Rat.HeightOneSpectrum.natGenerator v) ^ n] := by
  rw [principalFiniteComponent_mem_localHigherUnitGroup_iff v n x hx,
    rationalLocalHigherUnitMap_eq_one_iff,
    rationalLocalIntegralValue_sub_mem_iff]
  have hp : Nat.Prime (rationalPadicPrime v) :=
    (Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v).property
  have hnot :
      ¬ rationalPadicPrime v ∣ (x : ℚ).den := by
    simpa only [primesEquiv_val_eq_natGenerator] using
      not_dvd_den_of_valuation_eq_one v x hx
  have hcop :
      Nat.Coprime (x : ℚ).den (rationalPadicPrime v ^ n) :=
    Nat.Coprime.pow_right n
      (hp.coprime_iff_not_dvd.mpr hnot).symm
  have hunit :
      IsUnit
        ((x : ℚ).den :
          ZMod (rationalPadicPrime v ^ n)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hrel :=
    principalLocalResidue_den_mul v n x hx
  rw [← primesEquiv_val_eq_natGenerator v,
    ← Int.natCast_pow, ← ZMod.intCast_eq_intCast_iff]
  constructor
  · intro hw
    calc
      ((x : ℚ).num :
          ZMod (rationalPadicPrime v ^ n)) =
          ((x : ℚ).den :
            ZMod (rationalPadicPrime v ^ n)) := by
        rw [← hrel, hw, mul_one]
      _ = (((x : ℚ).den : ℤ) :
          ZMod (rationalPadicPrime v ^ n)) := by
        simp only [Int.cast_natCast]
  · intro hnd
    apply hunit.mul_left_cancel
    rw [hrel, mul_one]
    simpa only [Int.cast_natCast] using hnd

open scoped Classical in
/-- Congruences modulo pairwise coprime moduli combine to a congruence
modulo their finite product. -/
theorem intModEq_finset_prod_of_pairwise_coprime
    {ι : Type*}
    (s : Finset ι) (f : ι → ℕ)
    (hpair :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Nat.Coprime (f i) (f j))
    {a b : ℤ}
    (hmod : ∀ i ∈ s, a ≡ b [ZMOD f i]) :
    a ≡ b [ZMOD ∏ i ∈ s, f i] := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  induction s using Finset.induction_on with
  | empty =>
      exact Int.modEq_of_dvd (one_dvd (b - a))
  | @insert i s hi ih =>
      have hcop :
          Nat.Coprime (f i) (∏ j ∈ s, f j) := by
        apply Nat.Coprime.prod_right
        intro j hj
        exact hpair i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj)
          (fun hij => hi (hij ▸ hj))
      have hcopInt :
          ((f i : ℤ).natAbs).Coprime
            ((∏ j ∈ s, (f j : ℤ)).natAbs) := by
        rw [show (∏ j ∈ s, (f j : ℤ)) =
          ((∏ j ∈ s, f j : ℕ) : ℤ) by norm_cast]
        simpa only [Int.natAbs_natCast] using hcop
      rw [Finset.prod_insert hi]
      apply
        (Int.modEq_and_modEq_iff_modEq_mul hcopInt).mp
      constructor
      · exact hmod i (Finset.mem_insert_self i s)
      · apply ih
        · intro j hj k hk hjk
          exact hpair j (Finset.mem_insert_of_mem hj) k
            (Finset.mem_insert_of_mem hk) hjk
        · intro j hj
          exact hmod j (Finset.mem_insert_of_mem hj)

open scoped Classical in
/-- Congruences modulo every prime-power factor of a natural number
combine to a congruence modulo that number. -/
theorem intModEq_of_primePower_modEq
    {m : ℕ} (hm : m ≠ 0) {a b : ℤ}
    (h :
      ∀ p : m.primeFactors,
        a ≡ b [ZMOD (p : ℕ) ^ m.factorization p]) :
    a ≡ b [ZMOD m] := by
  let f : m.primeFactors → ℕ :=
    fun p => (p : ℕ) ^ m.factorization p
  have hprod :
      a ≡ b [ZMOD ∏ p : m.primeFactors, f p] := by
    apply intModEq_finset_prod_of_pairwise_coprime
      (Finset.univ : Finset m.primeFactors) f
    · intro p _ q _ hpq
      exact
        Nat.pairwise_coprime_pow_primeFactors_factorization hpq
    · intro p _
      exact h p
  have hmprod :
      (m : ℤ) = ∏ p : m.primeFactors, (f p : ℤ) := by
    exact_mod_cast
      Nat.prod_primeFactors_coe_pow_factorization hm
  rw [hmprod]
  exact hprod

open scoped Classical in
/-- Every prime-power factor determined by a factorization divides the
original natural number. -/
theorem primePower_factorization_dvd
    {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) :
    p ^ m.factorization p ∣ m :=
  (hp.pow_dvd_iff_le_factorization hm).2 le_rfl

open scoped Classical in
/-- The infinite component of a rational principal idele is positive
exactly when the rational number is positive. -/
theorem principalIdele_infinite_mem_iff_pos
    (x : ℚˣ) :
    (IdeleGroup.principalIdele ℚ x).1 ∈
        narrowInfiniteCongruenceSubgroup (K := ℚ) ↔
      0 < (x : ℚ) := by
  rw [mem_narrowInfiniteCongruenceSubgroup_iff]
  constructor
  · intro hx
    have hpos :=
      (mem_infinitePositiveSubgroup_iff
        Rat.infinitePlace
        (ContinuousMulEquiv.piUnits
          (IdeleGroup.principalIdele ℚ x).1
          Rat.infinitePlace)).1
        (hx Rat.infinitePlace)
        Rat.isReal_infinitePlace
    change
      0 <
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          Rat.isReal_infinitePlace
          ((WithAbs.toAbs Rat.infinitePlace.1 (x : ℚ) :
            WithAbs Rat.infinitePlace.1) :
              Rat.infinitePlace.Completion) at hpos
    rw [NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
      at hpos
    have hpos' : (0 : ℝ) < ((x : ℚ) : ℝ) := by
      simpa only [WithAbs.equiv_apply, WithAbs.ofAbs_toAbs,
        eq_ratCast] using hpos
    exact_mod_cast hpos'
  · intro hx v
    rw [mem_infinitePositiveSubgroup_iff]
    intro hv
    change
      0 <
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hv
          ((WithAbs.toAbs v.1 (x : ℚ) : WithAbs v.1) :
            v.Completion)
    rw [NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    simpa only [WithAbs.equiv_apply, WithAbs.ofAbs_toAbs,
      eq_ratCast] using (show
      (0 : ℝ) < ((x : ℚ) : ℝ) by exact_mod_cast hx)

open scoped Classical in
/-- The principal idele of the positive generator satisfies the
prime-to-modulus congruence condition exactly when its rational residue is
one. -/
theorem principalIdele_positiveGenerator_mem_primeTo_iff_modEq
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    IdeleGroup.principalIdele ℚ
        (positiveRationalIdealGeneratorUnit
          (I : FractionalIdealGroup ℚ)) ∈
        idelePrimeToModulusSubgroup (rationalModulus m) ↔
      (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ)).num ≡
        (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ)).den
        [ZMOD m] := by
  let x :=
    positiveRationalIdealGeneratorUnit
      (I : FractionalIdealGroup ℚ)
  constructor
  · intro hx
    apply intModEq_of_primePower_modEq hm
    intro p
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      rationalPrime
        ⟨p, (Nat.mem_primeFactors.mp p.2).1⟩
    have hvgen : Rat.HeightOneSpectrum.natGenerator v = (p : ℕ) :=
      natGenerator_rationalPrime
        ⟨p, (Nat.mem_primeFactors.mp p.2).1⟩
    have hv : v ∈ (rationalModulus m).finitePart.support := by
      rw [rationalModulus, Modulus.finitePart_narrowOfFinite]
      rw [mem_rationalFiniteModulus_support_iff hm]
      rw [hvgen]
      exact (Nat.mem_primeFactors.mp p.2).2.1
    have hcount := I.property v hv
    rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
      (I : FractionalIdealGroup ℚ)] at hcount
    have hxval : v.valuation ℚ (x : ℚ) = 1 :=
      valuation_eq_one_of_principal_count_eq_zero x v hcount
    have hlocal :=
      (principalLocalHigherUnit_iff_modEq v
        ((rationalModulus m).finitePart v) x hxval).1
        (hx.2 v hv)
    rw [rationalModulus_finitePart_apply, hvgen] at hlocal
    simpa only [x, positiveRationalIdealGeneratorUnit_val] using hlocal
  · intro hmod
    constructor
    · change
        (IdeleGroup.principalIdele ℚ x).1 ∈
          (Modulus.narrowOfFinite
            (rationalFiniteModulus m)).infiniteCongruenceSubgroup
      rw [Modulus.infiniteCongruenceSubgroup_narrowOfFinite]
      exact
        (principalIdele_infinite_mem_iff_pos x).2
          (positiveRationalIdealGenerator_pos
            (I : FractionalIdealGroup ℚ))
    · intro v hv
      have hcount := I.property v hv
      rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
        (I : FractionalIdealGroup ℚ)] at hcount
      have hxval : v.valuation ℚ (x : ℚ) = 1 :=
        valuation_eq_one_of_principal_count_eq_zero x v hcount
      apply
        (principalLocalHigherUnit_iff_modEq v
          ((rationalModulus m).finitePart v) x hxval).2
      rw [rationalModulus_finitePart_apply]
      have hpow :
          Rat.HeightOneSpectrum.natGenerator v ^
              m.factorization
                (Rat.HeightOneSpectrum.natGenerator v) ∣
            m :=
        primePower_factorization_dvd hm
          (Rat.HeightOneSpectrum.prime_natGenerator v)
      simpa only [x, positiveRationalIdealGeneratorUnit_val,
        Int.natCast_pow] using
        hmod.of_dvd (Int.natCast_dvd_natCast.mpr hpow)

open scoped Classical in
/-- Over `ℚ`, the ideal-theoretic ray subgroup consists precisely of the
positive principal generators congruent to one modulo `m`. -/
theorem mem_principalRayIdealSubgroup_iff_modEq
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    I ∈ principalRayIdealSubgroup (rationalModulus m) ↔
      (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ)).num ≡
        (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ)).den
        [ZMOD m] := by
  constructor
  · intro hI
    obtain ⟨x, hx, hideal⟩ :=
      (mem_principalRayIdealSubgroup_iff
        (rationalModulus m) I).1 hI
    have hxinf :
        (IdeleGroup.principalIdele ℚ x).1 ∈
          narrowInfiniteCongruenceSubgroup (K := ℚ) := by
      have hxinf' := hx.1
      change
        (IdeleGroup.principalIdele ℚ x).1 ∈
          (Modulus.narrowOfFinite
            (rationalFiniteModulus m)).infiniteCongruenceSubgroup at hxinf'
      rw [Modulus.infiniteCongruenceSubgroup_narrowOfFinite] at hxinf'
      exact hxinf'
    have hxpos : 0 < (x : ℚ) :=
      (principalIdele_infinite_mem_iff_pos x).1 hxinf
    have hxgen :
        (x : ℚ) =
          positiveRationalIdealGenerator
            (I : FractionalIdealGroup ℚ) := by
      apply eq_of_spanSingleton_eq_of_pos hxpos
        (positiveRationalIdealGenerator_pos
          (I : FractionalIdealGroup ℚ))
      calc
        FractionalIdeal.spanSingleton
            (nonZeroDivisors (𝓞 ℚ)) (x : ℚ) =
          rationalFractionalIdeal
            (toPrincipalIdeal (𝓞 ℚ) ℚ x) := by
              exact
                (coe_toPrincipalIdeal
                  (R := 𝓞 ℚ) (K := ℚ) x).symm
        _ = rationalFractionalIdeal
            (I : FractionalIdealGroup ℚ) :=
          congrArg rationalFractionalIdeal hideal
        _ = FractionalIdeal.spanSingleton
            (nonZeroDivisors (𝓞 ℚ))
            (positiveRationalIdealGenerator
              (I : FractionalIdealGroup ℚ)) :=
          rationalFractionalIdeal_eq_span_positiveGenerator
            (I : FractionalIdealGroup ℚ)
    have hxu :
        x = positiveRationalIdealGeneratorUnit
          (I : FractionalIdealGroup ℚ) := by
      apply Units.ext
      exact hxgen
    apply
      (principalIdele_positiveGenerator_mem_primeTo_iff_modEq
        hm I).1
    simpa only [← hxu] using hx
  · intro hmod
    apply
      (mem_principalRayIdealSubgroup_iff
        (rationalModulus m) I).2
    exact
      ⟨positiveRationalIdealGeneratorUnit
          (I : FractionalIdealGroup ℚ),
        (principalIdele_positiveGenerator_mem_primeTo_iff_modEq
          hm I).2 hmod,
        toPrincipalIdeal_positiveRationalIdealGeneratorUnit
          (I : FractionalIdealGroup ℚ)⟩

open scoped Classical in
/-- The residue map on ideals prime to `(m)` has exactly the ray-principal
ideals as its kernel. -/
theorem primeToIdealResidueHom_ker
    (m : ℕ) (hm : m ≠ 0) :
    (primeToIdealResidueHom m hm).ker =
      principalRayIdealSubgroup (rationalModulus m) := by
  ext I
  rw [MonoidHom.mem_ker,
    mem_principalRayIdealSubgroup_iff_modEq hm I,
    primeToIdealResidueHom_apply]
  exact
    rationalResidueUnit_eq_one_iff_modEq m
      (positiveRationalIdealGenerator
        (I : FractionalIdealGroup ℚ))
      (positiveGenerator_num_coprime hm I)
      (positiveGenerator_den_coprime hm I)

open scoped Classical in
/-- In ideal-theoretic form,
the ray ideal class group of `ℚ` modulo `(m)` is `(ℤ/mℤ)ˣ`. -/
noncomputable def idealRayClassGroupEquivZModUnits
    (m : ℕ) (hm : m ≠ 0) :
    IdealRayClassGroup (rationalModulus m) ≃*
      (ZMod m)ˣ := by
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (primeToIdealResidueHom_ker m hm).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (primeToIdealResidueHom m hm)
        (primeToIdealResidueHom_surjective m hm))

open scoped Classical in
/-- In idelic form,
the idelic ray class group of `ℚ` modulo `(m)` is `(ℤ/mℤ)ˣ`. -/
noncomputable def rationalRayClassGroupEquivZModUnits
    (m : ℕ) (hm : m ≠ 0) :
    RayClassGroup (rationalModulus m) ≃*
      (ZMod m)ˣ :=
  (rayClassGroupEquivIdealRayClassGroup
      (rationalModulus m)).trans
    (idealRayClassGroupEquivZModUnits m hm)

end RayClass
