/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionAffineIdealDegree
import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldConstantField
import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindDifferentDivisor
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor

/-!
# Nonzero affine ideals as effective finite divisors

In a Dedekind domain, a nonzero ideal is uniquely determined by the
multiplicity of every height-one prime in its factorization.  This file
packages that factorization as an equivalence between nonzero ideals and
effective, finitely supported divisors.

Specializing to the normalization of `K[X]` in a finite separable extension
of `K(X)` identifies nonzero affine ideals with effective divisors on the
finite places of the function field.  The equivalence is purely Dedekind
factorization: it does not use Riemann--Roch or a zeta-function argument.
-/

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

section DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The ideal represented by an effective divisor on the height-one primes of
a Dedekind domain. -/
def effectiveDivisorIdeal (D : HeightOneSpectrum R →₀ ℕ) : Ideal R :=
  D.prod fun v e => v.asIdeal ^ e

@[simp]
theorem effectiveDivisorIdeal_zero :
    effectiveDivisorIdeal (0 : HeightOneSpectrum R →₀ ℕ) = ⊤ := by
  simp [effectiveDivisorIdeal]

@[simp]
theorem effectiveDivisorIdeal_single
    (v : HeightOneSpectrum R) (e : ℕ) :
    effectiveDivisorIdeal (Finsupp.single v e) = v.asIdeal ^ e := by
  classical
  simp [effectiveDivisorIdeal, Finsupp.prod_single_index]

theorem effectiveDivisorIdeal_add
    (D E : HeightOneSpectrum R →₀ ℕ) :
    effectiveDivisorIdeal (D + E) =
      effectiveDivisorIdeal D * effectiveDivisorIdeal E := by
  classical
  unfold effectiveDivisorIdeal
  apply Finsupp.prod_add_index
  · intro v _
    exact pow_zero v.asIdeal
  · intro v _ a b
    exact pow_add v.asIdeal a b

/-- A height-one prime outside the support of an effective divisor is
coprime to the ideal represented by that divisor. -/
theorem isCoprime_effectiveDivisorIdeal_of_not_mem_support
    (v : HeightOneSpectrum R) (D : HeightOneSpectrum R →₀ ℕ)
    (hv : v ∉ D.support) : IsCoprime v.asIdeal (effectiveDivisorIdeal D) := by
  classical
  induction D using Finsupp.induction with
  | zero =>
      rw [effectiveDivisorIdeal_zero, ← Ideal.one_eq_top]
      exact isCoprime_one_right
  | single_add a b E ha hb ih =>
      rw [effectiveDivisorIdeal_add, effectiveDivisorIdeal_single]
      apply IsCoprime.mul_right
      · have hva : v ≠ a := by
          intro hva
          apply hv
          rw [Finsupp.support_single_add ha hb]
          simp [hva]
        exact (HeightOneSpectrum.isCoprime_of_ne v a hva).pow_right
      · apply ih
        intro hvE
        apply hv
        rw [Finsupp.support_single_add ha hb]
        simp [hvE]

/-- The quotient cardinality of the ideal represented by an effective divisor
is the product of the quotient cardinalities of its prime powers. -/
theorem cardQuot_effectiveDivisorIdeal_eq_prod
    (D : HeightOneSpectrum R →₀ ℕ) :
    (effectiveDivisorIdeal D).cardQuot =
      D.prod fun v e => v.asIdeal.cardQuot ^ e := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | single_add a b E ha hb ih =>
      calc
        (effectiveDivisorIdeal (Finsupp.single a b + E)).cardQuot =
            (a.asIdeal ^ b).cardQuot *
              (effectiveDivisorIdeal E).cardQuot := by
          rw [effectiveDivisorIdeal_add, effectiveDivisorIdeal_single,
            cardQuot_mul_of_coprime
              ((isCoprime_effectiveDivisorIdeal_of_not_mem_support
                a E ha).pow_left)]
        _ = (a.asIdeal ^ b).cardQuot *
              E.prod (fun v e => v.asIdeal.cardQuot ^ e) := by rw [ih]
        _ = a.asIdeal.cardQuot ^ b *
              E.prod (fun v e => v.asIdeal.cardQuot ^ e) := by
          rw [cardQuot_pow_of_prime a.ne_bot]
        _ = (Finsupp.single a b).prod
              (fun v e => v.asIdeal.cardQuot ^ e) *
              E.prod (fun v e => v.asIdeal.cardQuot ^ e) := by
          rw [Finsupp.prod_single_index]
          simp
        _ = (Finsupp.single a b + E).prod
              (fun v e => v.asIdeal.cardQuot ^ e) := by
          symm
          apply Finsupp.prod_add_index
          · intro v _
            simp
          · intro v _ m n
            exact pow_add v.asIdeal.cardQuot m n

/-- A product of powers of height-one primes is a nonzero ideal. -/
theorem effectiveDivisorIdeal_ne_bot (D : HeightOneSpectrum R →₀ ℕ) :
    effectiveDivisorIdeal D ≠ ⊥ := by
  rw [effectiveDivisorIdeal, ← Ideal.zero_eq_bot,
    Finsupp.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ v.ne_bot

/-- Reconstructing a nonzero ideal from its prime multiplicities returns the
original ideal. -/
theorem effectiveDivisorIdeal_idealMultiplicityDivisor
    (I : Ideal R) (hI : I ≠ ⊥) :
    effectiveDivisorIdeal
      (BGS.CorvajaZannier.idealMultiplicityDivisor I hI) = I := by
  change
    (BGS.CorvajaZannier.idealMultiplicityDivisor I hI).prod
        (fun v e => v.asIdeal ^ e) = I
  calc
    _ = ∏ᶠ v : HeightOneSpectrum R,
        v.asIdeal ^ multiplicity v.asIdeal I := by
      apply (finprod_eq_prod_of_mulSupport_subset
        (fun v : HeightOneSpectrum R =>
          v.asIdeal ^ multiplicity v.asIdeal I)
        (s := (BGS.CorvajaZannier.idealMultiplicityDivisor I hI).support)
        ?_).symm
      intro v hv
      simp only [Function.mem_mulSupport, ne_eq] at hv
      apply Finsupp.mem_support_iff.mpr
      rw [BGS.CorvajaZannier.idealMultiplicityDivisor_apply]
      exact fun hzero => hv (by simp [hzero])
    _ = I := Ideal.finprod_heightOneSpectrum_pow_multiplicity hI

/-- The multiplicity of a prime in the ideal represented by an effective
divisor is its coefficient in that divisor. -/
theorem multiplicity_effectiveDivisorIdeal
    (D : HeightOneSpectrum R →₀ ℕ) (v : HeightOneSpectrum R) :
    multiplicity v.asIdeal (effectiveDivisorIdeal D) = D v := by
  let DInt : HeightOneSpectrum R →₀ ℤ :=
    D.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
  let F := FractionalIdeal R⁰ (FractionRing R)
  have hcoe :
      ((effectiveDivisorIdeal D : Ideal R) : F) =
        D.prod (fun w e => (w.asIdeal : F) ^ e) := by
    change
      (FractionalIdeal.coeIdealHom R⁰ (FractionRing R))
          (D.prod fun w e => w.asIdeal ^ e) = _
    rw [map_finsuppProd]
    apply Finsupp.prod_congr
    intro w _
    exact FractionalIdeal.coeIdeal_pow R⁰ (FractionRing R) w.asIdeal (D w)
  have hcast :
      DInt.prod (fun w e => (w.asIdeal : F) ^ e) =
        D.prod (fun w e => (w.asIdeal : F) ^ e) := by
    dsimp [DInt]
    rw [Finsupp.prod_mapRange_index]
    · apply Finsupp.prod_congr
      intro w _
      exact zpow_natCast (w.asIdeal : F) (D w)
    · intro w
      exact zpow_zero (w.asIdeal : F)
  have hcount := FractionalIdeal.count_finsuppProd
    (FractionRing R) v DInt
  rw [hcast, ← hcoe,
    FractionalIdeal.count_coe (FractionRing R) v
      (effectiveDivisorIdeal_ne_bot D)] at hcount
  rw [Ideal.count_associates_factors_eq
      (effectiveDivisorIdeal_ne_bot D) v.isPrime v.ne_bot,
    IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
      (effectiveDivisorIdeal_ne_bot D), Finsupp.mapRange_apply] at hcount
  exact Int.ofNat_injective hcount

/-- Taking prime multiplicities after constructing the ideal represented by
an effective divisor recovers the divisor. -/
theorem idealMultiplicityDivisor_effectiveDivisorIdeal
    (D : HeightOneSpectrum R →₀ ℕ) :
    BGS.CorvajaZannier.idealMultiplicityDivisor
        (effectiveDivisorIdeal D) (effectiveDivisorIdeal_ne_bot D) = D := by
  ext v
  rw [BGS.CorvajaZannier.idealMultiplicityDivisor_apply,
    multiplicity_effectiveDivisorIdeal]

/-- A nonzero ideal, regarded as an element of the non-zero-divisors
submonoid, is not the bottom ideal. -/
theorem nonzeroIdeal_ne_bot (I : (Ideal R)⁰) : (I : Ideal R) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact mem_nonZeroDivisors_iff_ne_zero.mp I.property

/-- Dedekind factorization as an equivalence between nonzero ideals and
effective finitely supported divisors on height-one primes. -/
def nonzeroIdealEffectiveDivisorEquiv :
    (Ideal R)⁰ ≃ (HeightOneSpectrum R →₀ ℕ) where
  toFun I := BGS.CorvajaZannier.idealMultiplicityDivisor
    (I : Ideal R) (nonzeroIdeal_ne_bot I)
  invFun D := ⟨effectiveDivisorIdeal D, by
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa only [Ideal.zero_eq_bot] using effectiveDivisorIdeal_ne_bot D⟩
  left_inv I := by
    apply Subtype.ext
    exact effectiveDivisorIdeal_idealMultiplicityDivisor
      (I : Ideal R) (nonzeroIdeal_ne_bot I)
  right_inv D := idealMultiplicityDivisor_effectiveDivisorIdeal D

@[simp]
theorem nonzeroIdealEffectiveDivisorEquiv_apply
    (I : (Ideal R)⁰) (v : HeightOneSpectrum R) :
    nonzeroIdealEffectiveDivisorEquiv I v =
      multiplicity v.asIdeal (I : Ideal R) := by
  simp [nonzeroIdealEffectiveDivisorEquiv,
    BGS.CorvajaZannier.idealMultiplicityDivisor_apply]

@[simp]
theorem nonzeroIdealEffectiveDivisorEquiv_symm_coe
    (D : HeightOneSpectrum R →₀ ℕ) :
    ((nonzeroIdealEffectiveDivisorEquiv.symm D : (Ideal R)⁰) : Ideal R) =
      effectiveDivisorIdeal D := rfl

end DedekindDomain

section FunctionField

variable (K : Type*) [Field K] [Fintype K]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) affineDivisorPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance affineDivisorPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance affineDivisorFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance affineDivisorFiniteClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap K[X] (RatFuncFiniteIntegralClosure K L)).comp
      (algebraMap K K[X]))

local instance affineDivisorFiniteClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance affineDivisorFiniteClosureIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance affineDivisorPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance affineDivisorFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance affineDivisorFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) L
    (RatFuncFiniteIntegralClosure K L)

/-- The degree of an effective finite divisor is the sum of its
multiplicities weighted by the dimensions of the residue fields over the
constant field. -/
def finiteExtensionEffectiveFiniteDivisorDegree
    (D : FiniteExtensionFinitePlace K L →₀ ℕ) : ℕ :=
  D.sum fun v e => e * Module.finrank K v.asIdeal.ResidueField

/-- The quotient cardinality of a finite-place prime is the cardinality of
the constant field raised to the residue-field degree. -/
theorem finiteExtensionFinitePlace_cardQuot_eq_card_pow_degree
    (v : FiniteExtensionFinitePlace K L) :
    v.asIdeal.cardQuot = Fintype.card K ^
      Module.finrank K v.asIdeal.ResidueField := by
  let : DecidableEq K := Classical.decEq K
  let : Finite v.asIdeal.ResidueField :=
    finiteExtensionFinitePlaceResidueField_finite K L v
  let : Module.Finite K v.asIdeal.ResidueField :=
    Module.Finite.of_finite
  calc
    v.asIdeal.cardQuot =
        Nat.card (RatFuncFiniteIntegralClosure K L ⧸ v.asIdeal) :=
      Submodule.cardQuot_apply v.asIdeal
    _ = Nat.card v.asIdeal.ResidueField :=
      Nat.card_congr
        (RingEquiv.ofBijective
          (algebraMap
            (RatFuncFiniteIntegralClosure K L ⧸ v.asIdeal)
            v.asIdeal.ResidueField)
          v.asIdeal.bijective_algebraMap_quotient_residueField).toEquiv
    _ = Nat.card K ^ Module.finrank K v.asIdeal.ResidueField :=
      Module.natCard_eq_pow_finrank
    _ = Fintype.card K ^ Module.finrank K v.asIdeal.ResidueField := by
      rw [Nat.card_eq_fintype_card]

/-- Quotient cardinality is the constant-field cardinality raised to the
degree of the represented effective finite divisor. -/
theorem effectiveDivisorIdeal_cardQuot_eq_card_pow_degree
    (D : FiniteExtensionFinitePlace K L →₀ ℕ) :
    (effectiveDivisorIdeal D).cardQuot = Fintype.card K ^
      finiteExtensionEffectiveFiniteDivisorDegree K L D := by
  rw [cardQuot_effectiveDivisorIdeal_eq_prod]
  unfold finiteExtensionEffectiveFiniteDivisorDegree Finsupp.prod Finsupp.sum
  calc
    D.support.prod (fun v => v.asIdeal.cardQuot ^ D v) =
        D.support.prod (fun v =>
          Fintype.card K ^
            (D v * Module.finrank K v.asIdeal.ResidueField)) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [finiteExtensionFinitePlace_cardQuot_eq_card_pow_degree]
      calc
        (Fintype.card K ^ Module.finrank K v.asIdeal.ResidueField) ^ D v =
            Fintype.card K ^
              (Module.finrank K v.asIdeal.ResidueField * D v) :=
          (pow_mul (Fintype.card K)
            (Module.finrank K v.asIdeal.ResidueField) (D v)).symm
        _ = Fintype.card K ^
              (D v * Module.finrank K v.asIdeal.ResidueField) := by
          rw [Nat.mul_comm]
    _ = Fintype.card K ^
        D.support.sum (fun v =>
          D v * Module.finrank K v.asIdeal.ResidueField) :=
      Finset.prod_pow_eq_pow_sum D.support
        (fun v => D v * Module.finrank K v.asIdeal.ResidueField)
        (Fintype.card K)

/-- Nonzero affine ideals in the normalization of `K[X]` are exactly
effective divisors on the finite places of the function field. -/
def finiteExtensionAffineIdealEffectiveDivisorEquiv :
    FiniteExtensionAffineIdeal K L ≃
      (FiniteExtensionFinitePlace K L →₀ ℕ) :=
  nonzeroIdealEffectiveDivisorEquiv

@[simp]
theorem finiteExtensionAffineIdealEffectiveDivisorEquiv_apply
    (I : FiniteExtensionAffineIdeal K L)
    (v : FiniteExtensionFinitePlace K L) :
    finiteExtensionAffineIdealEffectiveDivisorEquiv K L I v =
      multiplicity v.asIdeal
        (I : Ideal (RatFuncFiniteIntegralClosure K L)) := by
  simpa [finiteExtensionAffineIdealEffectiveDivisorEquiv] using
    (nonzeroIdealEffectiveDivisorEquiv_apply I v)

@[simp]
theorem finiteExtensionAffineIdealEffectiveDivisorEquiv_symm_coe
    (D : FiniteExtensionFinitePlace K L →₀ ℕ) :
    (((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D :
        FiniteExtensionAffineIdeal K L) :
          Ideal (RatFuncFiniteIntegralClosure K L)) =
      effectiveDivisorIdeal D := by
  simpa [finiteExtensionAffineIdealEffectiveDivisorEquiv] using
    (nonzeroIdealEffectiveDivisorEquiv_symm_coe D)

/-- The affine ideal degree of the ideal represented by an effective finite
divisor is its residue-degree-weighted divisor degree. -/
theorem finiteExtensionAffineIdealDegree_equiv_symm
    (D : FiniteExtensionFinitePlace K L →₀ ℕ) :
    finiteExtensionAffineIdealDegree K L
        ((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D) =
      finiteExtensionEffectiveFiniteDivisorDegree K L D := by
  apply Nat.pow_right_injective (by
    simpa [Nat.succ_le_iff] using Fintype.one_lt_card (α := K))
  calc
    Fintype.card K ^ finiteExtensionAffineIdealDegree K L
        ((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D) =
        (((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D :
            FiniteExtensionAffineIdeal K L) :
          Ideal (RatFuncFiniteIntegralClosure K L)).cardQuot :=
      (finiteExtensionAffineIdeal_cardQuot_eq_card_pow_degree K L
        ((finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D)).symm
    _ = (effectiveDivisorIdeal D).cardQuot := by
      rw [finiteExtensionAffineIdealEffectiveDivisorEquiv_symm_coe]
    _ = Fintype.card K ^
        finiteExtensionEffectiveFiniteDivisorDegree K L D :=
      effectiveDivisorIdeal_cardQuot_eq_card_pow_degree K L D

/-- The degree of a nonzero affine ideal is the residue-degree-weighted sum of
its finite-place prime multiplicities. -/
theorem finiteExtensionAffineIdealDegree_eq_divisorDegree
    (I : FiniteExtensionAffineIdeal K L) :
    finiteExtensionAffineIdealDegree K L I =
      finiteExtensionEffectiveFiniteDivisorDegree K L
        (finiteExtensionAffineIdealEffectiveDivisorEquiv K L I) := by
  simpa using finiteExtensionAffineIdealDegree_equiv_symm K L
    (finiteExtensionAffineIdealEffectiveDivisorEquiv K L I)

/-- Expanded pointwise form of the affine ideal degree formula. -/
theorem finiteExtensionAffineIdealDegree_eq_sum_multiplicity_mul_residueDegree
    (I : FiniteExtensionAffineIdeal K L) :
    finiteExtensionAffineIdealDegree K L I =
      (finiteExtensionAffineIdealEffectiveDivisorEquiv K L I).sum
        (fun v e => e * Module.finrank K v.asIdeal.ResidueField) := by
  exact finiteExtensionAffineIdealDegree_eq_divisorDegree K L I

/-- The ideal/divisor equivalence restricts to each degree. -/
def finiteExtensionAffineIdealsOfDegreeEquivEffectiveFiniteDivisorsOfDegree
    (n : ℕ) :
    {I : FiniteExtensionAffineIdeal K L //
      finiteExtensionAffineIdealDegree K L I = n} ≃
      {D : FiniteExtensionFinitePlace K L →₀ ℕ //
        finiteExtensionEffectiveFiniteDivisorDegree K L D = n} where
  toFun I := ⟨finiteExtensionAffineIdealEffectiveDivisorEquiv K L I.1, by
    rw [← finiteExtensionAffineIdealDegree_eq_divisorDegree K L I.1]
    exact I.2⟩
  invFun D := ⟨(finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm D.1, by
    rw [finiteExtensionAffineIdealDegree_equiv_symm K L D.1]
    exact D.2⟩
  left_inv I := by
    apply Subtype.ext
    exact (finiteExtensionAffineIdealEffectiveDivisorEquiv K L).symm_apply_apply I.1
  right_inv D := by
    apply Subtype.ext
    exact (finiteExtensionAffineIdealEffectiveDivisorEquiv K L).apply_symm_apply D.1

/-- Effective finite divisors of a fixed degree form a finite type, transported
from the already-finite type of affine ideals of that degree. -/
noncomputable instance finiteExtensionEffectiveFiniteDivisorsOfDegree_fintype
    (n : ℕ) :
    Fintype {D : FiniteExtensionFinitePlace K L →₀ ℕ //
      finiteExtensionEffectiveFiniteDivisorDegree K L D = n} :=
  Fintype.ofEquiv
    {I : FiniteExtensionAffineIdeal K L //
      finiteExtensionAffineIdealDegree K L I = n}
    (finiteExtensionAffineIdealsOfDegreeEquivEffectiveFiniteDivisorsOfDegree
      K L n)

/-- The effective-finite-divisor coefficient of degree `n`. -/
noncomputable def finiteExtensionEffectiveFiniteDivisorCount (n : ℕ) : ℕ :=
  Fintype.card {D : FiniteExtensionFinitePlace K L →₀ ℕ //
    finiteExtensionEffectiveFiniteDivisorDegree K L D = n}

/-- The affine ideal coefficient sequence is exactly the effective
finite-divisor coefficient sequence. -/
theorem finiteExtensionAffineIdealCount_eq_effectiveFiniteDivisorCount
    (n : ℕ) :
    finiteExtensionAffineIdealCount K L n =
      finiteExtensionEffectiveFiniteDivisorCount K L n := by
  exact Fintype.card_congr
    (finiteExtensionAffineIdealsOfDegreeEquivEffectiveFiniteDivisorsOfDegree
      K L n)

end FunctionField

end

end BGS.HasseWeil
