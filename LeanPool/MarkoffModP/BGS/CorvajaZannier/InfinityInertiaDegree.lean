/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.InfinityPlace
public import Mathlib.Tactic

/-!
# Residue degree one above the rational-function place at infinity

For the infinity valuation ring of `K(X)`, every integral rational function is
congruent modulo the maximal ideal to a constant.  Consequently its residue
field is canonically a copy of `K`.  When `K` is algebraically closed, the
residue field at every prime above infinity in a finite separable extension of
`K(X)` is therefore the same field, so the corresponding inertia degree is
one.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

/-- Embed the constant field into the infinity valuation ring. -/
noncomputable def ratFuncInfinityConstantRingHom :
    K →+* RatFuncInfinityIntegers K :=
  (RatFunc.C : K →+* RatFunc K).codRestrict (RatFuncInfinityIntegers K) (fun c => by
    by_cases hc : c = 0
    · simp [hc]
    · change RatFunc.inftyValuation K (RatFunc.C c) ≤ 1
      rw [RatFunc.inftyValuation.C (F := K) hc])

local instance ratFuncInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

/-- The constant-field algebra map has underlying rational function `RatFunc.C c`. -/
@[simp] theorem ratFuncInfinityConstantAlgebra_coe (c : K) :
    ((algebraMap K (RatFuncInfinityIntegers K) c :
      RatFuncInfinityIntegers K) : RatFunc K) = RatFunc.C c := by
  rfl

local instance ratFuncInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  .of_algebraMap_eq' rfl

/-- Every rational function integral at infinity is congruent to a constant
modulo the maximal ideal at infinity. -/
theorem ratFuncInfinityIntegers_exists_constant_mod_maximalIdeal
    (r : RatFuncInfinityIntegers K) :
    ∃ c : K, r - algebraMap K (RatFuncInfinityIntegers K) c ∈
      (ratFuncInfinityPlace K).asIdeal := by
  let f : RatFunc K := r
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    have hr : r = 0 := by
      apply Subtype.ext
      exact hf
    simp [hr]
  have hdegree : f.intDegree ≤ 0 := by
    have hmem := r.property
    change RatFunc.inftyValuation K f ≤ 1 at hmem
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K hf, ← exp_zero, exp_le_exp] at hmem
    exact hmem
  rcases lt_or_eq_of_le hdegree with hdegree | hdegree
  · refine ⟨0, ?_⟩
    simp only [map_zero, sub_zero]
    change r ∈ IsLocalRing.maximalIdeal (RatFuncInfinityIntegers K)
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit r
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change RatFunc.inftyValuation K f < 1
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K hf, ← exp_zero, exp_lt_exp]
    exact hdegree
  · let c : K := f.num.leadingCoeff / f.denom.leadingCoeff
    refine ⟨c, ?_⟩
    let P : K[X] := f.num - Polynomial.C c * f.denom
    have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
    have hdenom : f.denom ≠ 0 := f.denom_ne_zero
    have hlcnum : f.num.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hnum
    have hlcdenom : f.denom.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hdenom
    have hc : c ≠ 0 := div_ne_zero hlcnum hlcdenom
    have hnatDegree : f.num.natDegree = f.denom.natDegree := by
      rw [RatFunc.intDegree] at hdegree
      omega
    have hdegreeEq : f.num.degree = (Polynomial.C c * f.denom).degree := by
      rw [Polynomial.degree_C_mul hc,
        Polynomial.degree_eq_natDegree hnum,
        Polynomial.degree_eq_natDegree hdenom,
        hnatDegree]
    have hleadingCoeff :
        f.num.leadingCoeff = (Polynomial.C c * f.denom).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact (div_mul_cancel₀ f.num.leadingCoeff hlcdenom).symm
    have hdegreeP : P.degree < f.num.degree := by
      exact Polynomial.degree_sub_lt_left hdegreeEq hnum hleadingCoeff
    have hrepr : f - RatFunc.C c =
        algebraMap K[X] (RatFunc K) P /
          algebraMap K[X] (RatFunc K) f.denom := by
      calc
        f - RatFunc.C c =
            algebraMap K[X] (RatFunc K) f.num /
                algebraMap K[X] (RatFunc K) f.denom - RatFunc.C c := by
          rw [RatFunc.num_div_denom]
        _ = (algebraMap K[X] (RatFunc K) f.num -
              RatFunc.C c * algebraMap K[X] (RatFunc K) f.denom) /
                algebraMap K[X] (RatFunc K) f.denom := by
          field_simp [RatFunc.algebraMap_ne_zero hdenom]
        _ = _ := by simp [P]
    by_cases hP : P = 0
    · have hdiff : f - RatFunc.C c = 0 := by simp [hrepr, hP]
      have hrEq : r = algebraMap K (RatFuncInfinityIntegers K) c := by
        apply Subtype.ext
        simpa [f] using sub_eq_zero.mp hdiff
      simp [hrEq]
    · have hnatDegreeP : P.natDegree < f.denom.natDegree := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hP]
        calc
          P.degree < f.num.degree := hdegreeP
          _ = (f.num.natDegree : WithBot ℕ) :=
            Polynomial.degree_eq_natDegree hnum
          _ = (f.denom.natDegree : WithBot ℕ) := by rw [hnatDegree]
      have hdiff : f - RatFunc.C c ≠ 0 := by
        rw [hrepr]
        exact div_ne_zero
          (RatFunc.algebraMap_ne_zero hP)
          (RatFunc.algebraMap_ne_zero hdenom)
      change r - algebraMap K (RatFuncInfinityIntegers K) c ∈
        IsLocalRing.maximalIdeal (RatFuncInfinityIntegers K)
      rw [IsLocalRing.mem_maximalIdeal]
      change ¬ IsUnit (r - algebraMap K (RatFuncInfinityIntegers K) c)
      rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      change RatFunc.inftyValuation K (f - RatFunc.C c) < 1
      rw [RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation_of_nonzero K hdiff, ← exp_zero, exp_lt_exp,
        hrepr, RatFunc.intDegree_div
          (RatFunc.algebraMap_ne_zero hP)
          (RatFunc.algebraMap_ne_zero hdenom),
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      omega

/-- The residue field of the rational-function place at infinity is the
constant field. -/
noncomputable def ratFuncInfinityPlaceResidueEquiv :
    (ratFuncInfinityPlace K).asIdeal.ResidueField ≃ₐ[K] K := by
  let p := (ratFuncInfinityPlace K).asIdeal
  have hsurjective :
      Function.Surjective (algebraMap K p.ResidueField) := by
    intro z
    obtain ⟨r, hr⟩ := p.algebraMap_residueField_surjective z
    obtain ⟨c, hc⟩ :=
      ratFuncInfinityIntegers_exists_constant_mod_maximalIdeal K r
    have hzero :
        algebraMap (RatFuncInfinityIntegers K) p.ResidueField
            (r - algebraMap K (RatFuncInfinityIntegers K) c) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hc
    have heq :
        algebraMap (RatFuncInfinityIntegers K) p.ResidueField r =
          algebraMap (RatFuncInfinityIntegers K) p.ResidueField
            (algebraMap K (RatFuncInfinityIntegers K) c) := by
      exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
    refine ⟨c, ?_⟩
    calc
      algebraMap K p.ResidueField c =
          algebraMap (RatFuncInfinityIntegers K) p.ResidueField
            (algebraMap K (RatFuncInfinityIntegers K) c) := by
        rw [IsScalarTower.algebraMap_apply K
          (RatFuncInfinityIntegers K) p.ResidueField]
      _ = algebraMap (RatFuncInfinityIntegers K) p.ResidueField r := heq.symm
      _ = z := hr
  exact (AlgEquiv.ofBijective (Algebra.ofId K _)
    ⟨RingHom.injective _, hsurjective⟩).symm

section Extension

variable [IsAlgClosed K]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance infinityInertiaIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance infinityInertiaIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

/-- Over an algebraically closed constant field, every prime above the place at
infinity has residue degree (inertia degree) one. -/
theorem finiteExtensionInfinityPlace_inertiaDeg_eq_one
    (P : (ratFuncInfinityPlace K).asIdeal.primesOver
      (RatFuncInfinityIntegralClosure K L)) :
    P.1.inertiaDeg (RatFuncInfinityIntegers K) = 1 := by
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver
      (ratFuncInfinityPlace K).asIdeal P.1
  let : IsScalarTower (RatFuncInfinityIntegers K)
      (Localization.AtPrime (ratFuncInfinityPlace K).asIdeal) (Localization.AtPrime P.1) :=
    inferInstance
  let : IsAlgClosed (ratFuncInfinityPlace K).asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv K
      (ratFuncInfinityPlace K).asIdeal.ResidueField
      (ratFuncInfinityPlaceResidueEquiv K).symm.toRingEquiv
  let : Algebra (ratFuncInfinityPlace K).asIdeal.ResidueField
      P.1.ResidueField := IsLocalRing.ResidueField.instAlgebra
  let : Algebra.QuasiFiniteAt (RatFuncInfinityIntegers K) P.1 :=
    inferInstance
  let : Module.Finite
      (ratFuncInfinityPlace K).asIdeal.ResidueField
      P.1.ResidueField := inferInstance
  let : Algebra.IsIntegral
      (ratFuncInfinityPlace K).asIdeal.ResidueField
      P.1.ResidueField := Algebra.IsIntegral.of_finite _ _
  rw [Ideal.inertiaDeg_eq (ratFuncInfinityPlace K).asIdeal P.1,
    Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Extension

end
end BGS.CorvajaZannier
