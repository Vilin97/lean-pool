/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityInertiaDegree
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# The infinity valuation ring as a reciprocal localization

Writing `Y = X⁻¹`, a rational function is regular at infinity exactly when
it belongs to the local ring `K[Y]_(Y)`.  This file proves that statement for
the repository's valuation-ring model `RatFuncInfinityIntegers K`.

The proof is explicit: a function of nonpositive integer degree is written
using the reversed numerator and denominator.  This localization model is
the bridge needed to transport polynomial normalization under finite constant
extension to places above infinity.
-/

open scoped Polynomial nonZeroDivisors

open IsDedekindDomain Multiplicative WithZero

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

local instance : Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

/-- Evaluate a polynomial in the reciprocal coordinate `X⁻¹`. -/
noncomputable def reciprocalPolynomialRingHom :
    K[X] →+* RatFuncInfinityIntegers K :=
  Polynomial.eval₂RingHom (ratFuncInfinityConstantRingHom K)
    (ratFuncInfinityUniformizer K)

/-- The polynomial algebra structure on the infinity valuation ring in the
reciprocal coordinate.  Its variable is the uniformizer `X⁻¹`. -/
@[reducible]
noncomputable def ratFuncInfinityReciprocalPolynomialAlgebra :
    Algebra K[X] (RatFuncInfinityIntegers K) :=
  (reciprocalPolynomialRingHom K).toAlgebra

local instance reciprocalPolynomialAlgebra :
    Algebra K[X] (RatFuncInfinityIntegers K) :=
  ratFuncInfinityReciprocalPolynomialAlgebra K

local instance reciprocalSpanXPrime :
    (Ideal.span ({Polynomial.X} : Set K[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

@[simp] theorem reciprocalPolynomialRingHom_X :
    reciprocalPolynomialRingHom K Polynomial.X =
      ratFuncInfinityUniformizer K := by
  simp [reciprocalPolynomialRingHom]

@[simp] theorem reciprocalPolynomialRingHom_C (c : K) :
    reciprocalPolynomialRingHom K (Polynomial.C c) =
      algebraMap K (RatFuncInfinityIntegers K) c := by
  unfold reciprocalPolynomialRingHom
  change Polynomial.eval₂ (ratFuncInfinityConstantRingHom K)
    (ratFuncInfinityUniformizer K) (Polynomial.C c) = _
  rw [Polynomial.eval₂_C]
  rfl

@[simp] theorem reciprocalPolynomialAlgebraMap_eq (p : K[X]) :
    algebraMap K[X] (RatFuncInfinityIntegers K) p =
      reciprocalPolynomialRingHom K p := rfl

@[simp] theorem reciprocalPolynomialRingHom_coe (p : K[X]) :
    ((reciprocalPolynomialRingHom K p :
      RatFuncInfinityIntegers K) : RatFunc K) =
      Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Polynomial.eval₂_add]
      change ((reciprocalPolynomialRingHom K p :
          RatFuncInfinityIntegers K) : RatFunc K) +
        ((reciprocalPolynomialRingHom K q :
          RatFuncInfinityIntegers K) : RatFunc K) = _
      rw [hp, hq]
  | monomial n c =>
      simp [reciprocalPolynomialRingHom, ratFuncInfinityUniformizer,
        ratFuncInfinityConstantRingHom]

theorem reciprocalPolynomialRingHom_isUnit_of_coeff_zero_ne_zero
    (p : K[X]) (hp : p.coeff 0 ≠ 0) :
    IsUnit (reciprocalPolynomialRingHom K p) := by
  by_contra hunit
  have hmap : reciprocalPolynomialRingHom K p ∈
      (ratFuncInfinityPlace K).asIdeal := by
    change reciprocalPolynomialRingHom K p ∈
      IsLocalRing.maximalIdeal (RatFuncInfinityIntegers K)
    rw [IsLocalRing.mem_maximalIdeal]
    exact hunit
  obtain ⟨r, hr⟩ := (Polynomial.X_dvd_sub_C (p := p))
  have hdiff : reciprocalPolynomialRingHom K
      (p - Polynomial.C (p.coeff 0)) ∈
      (ratFuncInfinityPlace K).asIdeal := by
    rw [hr, map_mul, reciprocalPolynomialRingHom_X]
    rw [ratFuncInfinityPlace_span_uniformizer]
    rw [mul_comm]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hconst : reciprocalPolynomialRingHom K
      (Polynomial.C (p.coeff 0)) ∈ (ratFuncInfinityPlace K).asIdeal := by
    have := (ratFuncInfinityPlace K).asIdeal.sub_mem hmap hdiff
    simpa only [map_sub, sub_sub_cancel] using this
  have hunit : IsUnit (reciprocalPolynomialRingHom K
      (Polynomial.C (p.coeff 0))) := by
    rw [reciprocalPolynomialRingHom_C]
    exact (isUnit_iff_ne_zero.mpr hp).map
      (algebraMap K (RatFuncInfinityIntegers K))
  change reciprocalPolynomialRingHom K (Polynomial.C (p.coeff 0)) ∈
    IsLocalRing.maximalIdeal (RatFuncInfinityIntegers K) at hconst
  rw [IsLocalRing.mem_maximalIdeal] at hconst
  exact hconst hunit

theorem reciprocalPolynomialRingHom_injective :
    Function.Injective (reciprocalPolynomialRingHom K) := by
  intro p q hpq
  apply sub_eq_zero.mp
  have heval : Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) (p - q) = 0 := by
    have hzero : reciprocalPolynomialRingHom K (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hzeroVal :
        ((reciprocalPolynomialRingHom K (p - q) :
          RatFuncInfinityIntegers K) : RatFunc K) = 0 := by
      simpa using congrArg Subtype.val hzero
    rw [reciprocalPolynomialRingHom_coe] at hzeroVal
    exact hzeroVal
  have htrans : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
    rw [Transcendental, IsAlgebraic.inv_iff]
    exact RatFunc.transcendental_X
  rw [one_div] at heval
  exact (transcendental_iff.mp htrans (p - q)) (by
    simpa [Polynomial.aeval_def] using heval)

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
@[simp] theorem polynomialEvalRatFuncX_eq_algebraMap (p : K[X]) :
    Polynomial.eval₂ RatFunc.C RatFunc.X p =
      algebraMap K[X] (RatFunc K) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp

omit [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem eval_reciprocal_reverse_mul_X_pow (p : K[X]) :
    Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) p.reverse *
        RatFunc.X ^ p.natDegree =
      algebraMap K[X] (RatFunc K) p := by
  letI : Invertible (RatFunc.X : RatFunc K) :=
    invertibleOfNonzero RatFunc.X_ne_zero
  simpa [invOf_eq_inv, one_div] using
    (Polynomial.eval₂_reverse_mul_pow RatFunc.C
      (RatFunc.X : RatFunc K) p)

theorem reciprocalPolynomialRingHom_surj
    (z : RatFuncInfinityIntegers K) :
    ∃ x : K[X] × (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl,
      z * algebraMap K[X] (RatFuncInfinityIntegers K) x.2 =
        algebraMap K[X] (RatFuncInfinityIntegers K) x.1 := by
  let f : RatFunc K := z
  by_cases hf : f = 0
  · refine ⟨⟨0, ⟨1, ?_⟩⟩, ?_⟩
    · simp
    · apply Subtype.ext
      change f * _ = _
      simp [hf]
  have hdegree : f.intDegree ≤ 0 := by
    have hz := z.property
    change RatFunc.inftyValuation K f ≤ 1 at hz
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K hf,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    exact hz
  have hnd : f.num.natDegree ≤ f.denom.natDegree := by
    rw [RatFunc.intDegree] at hdegree
    omega
  let a : K[X] := f.num.reverse *
    Polynomial.X ^ (f.denom.natDegree - f.num.natDegree)
  let b : K[X] := f.denom.reverse
  have hbcoeff : b.coeff 0 ≠ 0 := by
    change f.denom.reverse.coeff 0 ≠ 0
    rw [Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero
  have hb : b ∈ (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl := by
    change b ∉ Ideal.span ({Polynomial.X} : Set K[X])
    intro hspan
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at hspan
    exact hbcoeff hspan
  refine ⟨⟨a, ⟨b, hb⟩⟩, ?_⟩
  apply Subtype.ext
  change f *
      ((algebraMap K[X] (RatFuncInfinityIntegers K) b :
        RatFuncInfinityIntegers K) : RatFunc K) =
    ((algebraMap K[X] (RatFuncInfinityIntegers K) a :
      RatFuncInfinityIntegers K) : RatFunc K)
  rw [reciprocalPolynomialAlgebraMap_eq,
    reciprocalPolynomialAlgebraMap_eq,
    reciprocalPolynomialRingHom_coe,
    reciprocalPolynomialRingHom_coe]
  apply (mul_right_cancel₀ (pow_ne_zero f.denom.natDegree
    RatFunc.X_ne_zero))
  rw [mul_assoc]
  have hden := eval_reciprocal_reverse_mul_X_pow K f.denom
  have hnum := eval_reciprocal_reverse_mul_X_pow K f.num
  change f * (Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) b *
      RatFunc.X ^ f.denom.natDegree) =
    Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) a *
      RatFunc.X ^ f.denom.natDegree
  rw [show Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) b *
      RatFunc.X ^ f.denom.natDegree =
        algebraMap K[X] (RatFunc K) f.denom by exact hden]
  have hleft : f * algebraMap K[X] (RatFunc K) f.denom =
      algebraMap K[X] (RatFunc K) f.num := by
    calc
      f * algebraMap K[X] (RatFunc K) f.denom =
          (algebraMap K[X] (RatFunc K) f.num /
              algebraMap K[X] (RatFunc K) f.denom) *
            algebraMap K[X] (RatFunc K) f.denom := by
        congr 1
        exact (RatFunc.num_div_denom f).symm
      _ = algebraMap K[X] (RatFunc K) f.num :=
        div_mul_cancel₀ _
          (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
  rw [hleft, ← hnum]
  change Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) f.num.reverse *
      RatFunc.X ^ f.num.natDegree =
    Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) a *
      RatFunc.X ^ f.denom.natDegree
  rw [show Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) a =
      Polynomial.eval₂ RatFunc.C (1 / RatFunc.X) f.num.reverse *
        (1 / RatFunc.X) ^
          (f.denom.natDegree - f.num.natDegree) by
    simp [a]]
  rw [mul_assoc]
  congr 1
  rw [one_div, inv_pow]
  rw [show RatFunc.X ^ f.denom.natDegree =
      RatFunc.X ^ (f.denom.natDegree - f.num.natDegree) *
        RatFunc.X ^ f.num.natDegree by
    exact (pow_sub_mul_pow RatFunc.X hnd).symm]
  rw [← mul_assoc, inv_mul_cancel₀]
  · simp
  · exact pow_ne_zero _ RatFunc.X_ne_zero

/-- The infinity valuation ring is the localization of the reciprocal
polynomial coordinate ring at the origin. -/
theorem ratFuncInfinityIntegers_isLocalization_reciprocal :
    IsLocalization
      (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl
      (RatFuncInfinityIntegers K) := by
  rw [isLocalization_iff]
  constructor
  · intro y
    apply reciprocalPolynomialRingHom_isUnit_of_coeff_zero_ne_zero K
    intro hy0
    apply y.2
    change (y : K[X]) ∈ Ideal.span ({Polynomial.X} : Set K[X])
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
    exact hy0
  constructor
  · exact reciprocalPolynomialRingHom_surj K
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    exact reciprocalPolynomialRingHom_injective K hxy

local instance ratFuncInfinityIntegersReciprocalLocalization :
    IsLocalization
      (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl
      (RatFuncInfinityIntegers K) :=
  ratFuncInfinityIntegers_isLocalization_reciprocal K

/-- Canonical localization model for the infinity valuation ring, with the
polynomial variable corresponding to `X⁻¹`. -/
noncomputable def reciprocalPolynomialAtOriginAlgEquivInfinityIntegers :
    Localization.AtPrime (Ideal.span ({Polynomial.X} : Set K[X])) ≃ₐ[K[X]]
      RatFuncInfinityIntegers K :=
  IsLocalization.algEquiv
    (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl
    (Localization.AtPrime (Ideal.span ({Polynomial.X} : Set K[X])))
    (RatFuncInfinityIntegers K)

section Extension

variable (N : Type*) [Field N] [Algebra (RatFunc K) N]

local instance infinityLocalizationConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance infinityLocalizationReciprocalPolynomialAlgebra :
    Algebra K[X] (RatFuncInfinityIntegers K) :=
  ratFuncInfinityReciprocalPolynomialAlgebra K

local instance infinityLocalizationSpanXPrime :
    (Ideal.span ({Polynomial.X} : Set K[X])).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- Reciprocal polynomial structure on an extension of `K(X)`.  The variable
acts as the image of `X⁻¹`. -/
@[reducible]
noncomputable def ratFuncExtensionReciprocalPolynomialAlgebra :
    Algebra K[X] N :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K) N).comp
      (reciprocalPolynomialRingHom K))

local instance infinityLocalizationExtensionPolynomialAlgebra :
    Algebra K[X] N :=
  ratFuncExtensionReciprocalPolynomialAlgebra K N

local instance infinityLocalizationPolynomialTower :
    IsScalarTower K[X] (RatFuncInfinityIntegers K) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityLocalizationBase :
    IsLocalization
      (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl
      (RatFuncInfinityIntegers K) :=
  ratFuncInfinityIntegers_isLocalization_reciprocal K

private theorem extensionReciprocalPolynomialAlgMap_injective :
    Function.Injective (algebraMap K[X] N) := by
  intro p q hpq
  apply reciprocalPolynomialRingHom_injective K
  apply Subtype.ext
  apply (algebraMap (RatFunc K) N).injective
  exact hpq

local instance infinityLocalizationExtensionPolynomialFaithful :
    FaithfulSMul K[X] N := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact extensionReciprocalPolynomialAlgMap_injective K N

private theorem extensionReciprocalPrimeCompl_maps_nonzero :
    (0 : N) ∉ Algebra.algebraMapSubmonoid N
      (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl := by
  intro h0
  have hle := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    N (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl_le_nonZeroDivisors
  exact (nonZeroDivisors.ne_zero (hle h0)) rfl

private theorem fieldSelf_isLocalization (M : Submonoid N)
    (hM : (0 : N) ∉ M) : IsLocalization M N := by
  rw [isLocalization_iff]
  constructor
  · intro y
    exact isUnit_iff_ne_zero.mpr (fun hy ↦ hM (hy ▸ y.2))
  constructor
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

local instance infinityLocalizationExtensionSelf :
    IsLocalization
      (Algebra.algebraMapSubmonoid N
        (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl) N :=
  fieldSelf_isLocalization N _
    (extensionReciprocalPrimeCompl_maps_nonzero K N)

local instance reciprocalPolynomialInfinityIntegralClosureAlgebra :
    Algebra K[X] (RatFuncInfinityIntegralClosure K N) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K N)).comp
        (algebraMap K[X] (RatFuncInfinityIntegers K)))

local instance reciprocalPolynomialInfinityIntegralClosureTower :
    IsScalarTower K[X] (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K N) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Inclusion of the reciprocal affine normalization into its localization
at infinity. -/
noncomputable def reciprocalIntegralClosureToInfinityAlgHom :
    integralClosure K[X] N →ₐ[K[X]] RatFuncInfinityIntegralClosure K N :=
  { toFun := fun x ↦ ⟨x.1, x.2.tower_top⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

/-- Algebra structure on the infinity normalization induced by localizing the
reciprocal affine normalization. -/
@[reducible]
noncomputable def ratFuncInfinityReciprocalIntegralClosureAlgebra :
    Algebra (integralClosure K[X] N)
      (RatFuncInfinityIntegralClosure K N) :=
  (reciprocalIntegralClosureToInfinityAlgHom K N).toAlgebra

local instance reciprocalIntegralClosureInfinityAlgebra :
    Algebra (integralClosure K[X] N)
      (RatFuncInfinityIntegralClosure K N) :=
  ratFuncInfinityReciprocalIntegralClosureAlgebra K N

local instance reciprocalIntegralClosureInfinityAmbientTower :
    IsScalarTower (integralClosure K[X] N)
      (RatFuncInfinityIntegralClosure K N) N :=
  ⟨fun r s x ↦ by
    simp only [Algebra.smul_def, map_mul]
    change (r : N) * (s : N) * x = (r : N) * ((s : N) * x)
    ring⟩

local instance reciprocalPolynomialIntegralClosuresTower :
    IsScalarTower K[X] (integralClosure K[X] N)
      (RatFuncInfinityIntegralClosure K N) :=
  IsScalarTower.of_algebraMap_eq fun p ↦ by
    apply Subtype.ext
    change algebraMap K[X] N p = algebraMap K[X] N p
    rfl

/-- The infinity integral closure is the localization of the reciprocal
affine normalization away from the origin. -/
theorem ratFuncInfinityIntegralClosure_isLocalization_reciprocal :
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure K[X] N)
        (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl)
      (RatFuncInfinityIntegralClosure K N) := by
  letI : IsScalarTower K[X] (integralClosure K[X] N)
      (RatFuncInfinityIntegralClosure K N) :=
    reciprocalPolynomialIntegralClosuresTower K N
  exact @IsLocalization.integralClosure
    K[X] _ N _ (ratFuncExtensionReciprocalPolynomialAlgebra K N)
    (RatFuncInfinityIntegers K) N _ _
    (ratFuncInfinityReciprocalPolynomialAlgebra K)
    (inferInstance : Algebra N N)
    (inferInstance : Algebra (RatFuncInfinityIntegers K) N)
    (ratFuncExtensionReciprocalPolynomialAlgebra K N)
    (inferInstance : IsScalarTower K[X] N N)
    (infinityLocalizationPolynomialTower K N)
    (Ideal.span ({Polynomial.X} : Set K[X])).primeCompl
    (infinityLocalizationBase K)
    (infinityLocalizationExtensionSelf K N)
    (ratFuncInfinityReciprocalIntegralClosureAlgebra K N)
    (reciprocalIntegralClosureInfinityAmbientTower K N)
    (reciprocalPolynomialIntegralClosuresTower K N)

end Extension

end

end BGS.HasseWeil
