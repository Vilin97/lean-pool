/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionGenusBound
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannRoch
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneConstantField
public import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneFinitePlaceRiemannLower

/-!
# Automatic bidegree genus bound for plane curves

For an absolutely irreducible plane curve with both coordinate projections
separating, the intrinsic genus of its function field is bounded by the bidegree
monomial budget.  The proof combines three already formalized ingredients:

* exactness of the constant field;
* Riemann--Roch for the exhaustive finite-extension divisor model;
* the finite-place bidegree form of Riemann's inequality.

The finite place needed by the one-point comparison is constructed above the
prime `(X)` of `K[X]`, so it is not an additional hypothesis.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain
open scoped Polynomial

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) automaticGenusPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance automaticGenusPolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance automaticGenusFiniteClosureIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance automaticGenusPolynomialTorsionFree :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
omit [FiniteDimensional (RatFunc K) L] in
/-- A finite separable extension of `K(X)` has an exhaustive finite place.
We select a prime of the finite integral closure lying above `(X)`. -/
theorem finiteExtensionFinitePlace_nonempty :
    Nonempty (FiniteExtensionFinitePlace K L) := by
  let p : HeightOneSpectrum K[X] := Polynomial.idealX K
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := RatFuncFiniteIntegralClosure K L) p.asIdeal (by
        intro x hx
        have hxA : algebraMap K[X] (RatFuncFiniteIntegralClosure K L) x = 0 :=
          (RingHom.mem_ker).mp hx
        have hxL : algebraMap K[X] L x = 0 := congrArg Subtype.val hxA
        have hx0 : x = 0 := by
          exact FaithfulSMul.algebraMap_injective K[X] L (by simpa using hxL)
        subst x
        exact p.asIdeal.zero_mem)
  let P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K L) :=
    ⟨Q, hQprime, ⟨hQcomap.symm⟩⟩
  exact ⟨primeOverHeightOne p P⟩

variable {K}

/-- The function-field genus of an absolutely irreducible plane curve is at
most its bidegree monomial budget

`(degreeOf 0 f - 1) * (degreeOf 1 f - 1)`.

This theorem has no Riemann--Roch, constant-field, or place hypothesis: all
three are discharged by the existing formalized theory. -/
theorem planeCurve_genus_le_bidegreeGenusBudget
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    FunctionField.genus K (PlaneCurveFunctionField f) ≤
      planeCurveBidegreeGenusBudget f := by
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let canonicalAlg : Algebra K L := inferInstance
  let : Algebra K L := canonicalAlg
  let ratAlg : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (RatFunc K) L := ratAlg
  let : SMul (RatFunc K) L := ratAlg.toSMul
  let : Module (RatFunc K) L := ratAlg.toModule
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let inducedAlg : Algebra K L :=
    RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
      (algebraMap K (RatFunc K)))
  have hinducedAlg : inducedAlg = canonicalAlg := by
    apply Algebra.algebra_ext
    intro c
    change (@ratFuncSpecialization K L _ _ canonicalAlg
      (planeCurveFunction f 0) hx) (RatFunc.C c) =
        @algebraMap K L _ _ canonicalAlg c
    have h := DFunLike.congr_fun
      (@ratFuncSpecialization_comp_polynomial_algebraMap
        K L _ _ canonicalAlg (planeCurveFunction f 0) hx)
      (Polynomial.C c)
    simpa using h
  let : Algebra K L := inducedAlg
  let : SMul K L := inducedAlg.toSMul
  let : Module K L := inducedAlg.toModule
  let : IsScalarTower K (RatFunc K) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K K[X] L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hconstantsCanonical :
      @algebraicClosure K L _ _ canonicalAlg = ⊥ := by
    simpa only [L] using
      planeCurveFunctionField_algebraicClosure_eq_bot
        f habsolute hpartialSecond
  have hconstants : algebraicClosure K L = ⊥ := by
    change @algebraicClosure K L _ _ inducedAlg = ⊥
    rw [hinducedAlg]
    exact hconstantsCanonical
  let : FunctionField.IsFullConstantField K L :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot K L).2
      hconstants
  let q : FiniteExtensionFinitePlace K L :=
    Classical.choice (finiteExtensionFinitePlace_nonempty K L)
  have hchart : FunctionField.Chart.genus K L ≤
      planeCurveBidegreeGenusBudget f := by
    apply genus_le_budget_of_uniformRiemann_onePoint K L
      (FunctionField.Chart.genus K L)
      (2 * FunctionField.Chart.genus K L)
      (planeCurveBidegreeGenusBudget f) (.inl q)
      (hasFiniteExtensionUniformEventualRiemannFormula_of_fullConstantField K L)
    intro N
    simpa only [L] using
      planeCurve_finitePlace_riemann_lower
        hf hpartialFirst hpartialSecond q N
  have hintrinsic : FunctionField.genus K L ≤
      planeCurveBidegreeGenusBudget f := by
    rw [FunctionField.genus_eq_genusChart K L]
    exact hchart
  change @FunctionField.genus K L _ _ canonicalAlg ≤
    planeCurveBidegreeGenusBudget f
  change @FunctionField.genus K L _ _ inducedAlg ≤
    planeCurveBidegreeGenusBudget f at hintrinsic
  rw [hinducedAlg] at hintrinsic
  exact hintrinsic

end

end BGS.HasseWeil
