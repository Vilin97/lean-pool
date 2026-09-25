/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosure
public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The algebraic constant field of a finite function field

For a finite separable extension `N / K(t)`, define its algebraic constant
field to be the relative algebraic closure of `K` in `N`.  When `K` is finite,
this constant field is finite-dimensional over `K`.

The finiteness proof is place-theoretic.  Algebraic constants are integral over
`K[X]`, hence map into the finite integral closure.  Reduction modulo any
height-one prime is injective on the constant field, because it is a field.
Choosing a prime above `(X)` embeds the constants into a finite quotient.
-/

@[expose] public section

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain

attribute [local instance high] Module.Free.of_divisionRing

variable (K N : Type*) [Field K] [Field N]
  [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) N]
  [FiniteDimensional (RatFunc K) N]
  [Algebra.IsSeparable (RatFunc K) N]

local instance functionFieldConstantAlgebra : Algebra K N :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) N).comp
    (algebraMap K (RatFunc K)))

local instance functionFieldConstantRatFuncTower :
    IsScalarTower K (RatFunc K) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) functionFieldConstantPolynomialAlgebra :
    Algebra K[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) N).comp
    (algebraMap K[X] (RatFunc K)))

local instance functionFieldConstantPolynomialRatFuncTower :
    IsScalarTower K[X] (RatFunc K) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance functionFieldConstantPolynomialTower :
    IsScalarTower K K[X] N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance functionFieldConstantPolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] N :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) N

local instance functionFieldConstantFiniteClosureAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K N) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K N)).comp (algebraMap K K[X]))

local instance functionFieldConstantFiniteClosureTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance functionFieldConstantFiniteClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K N) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K N)

local instance functionFieldConstantFiniteClosureIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K N) :=
  IsIntegralClosure.isIntegral_algebra K[X] N

local instance functionFieldConstantFiniteClosureTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K N) :=
  IsIntegralClosure.isTorsionFree K[X] N

local instance functionFieldConstantFiniteClosureDedekind :
    IsDedekindDomain (RatFuncFiniteIntegralClosure K N) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) N
    (RatFuncFiniteIntegralClosure K N)

/-- The algebraic constant field of `N / K(t)`. -/
abbrev FunctionFieldConstantField := algebraicClosure K N

/-- Algebraic constants are integral over the finite polynomial model. -/
def functionFieldConstantToFiniteIntegralClosure :
    FunctionFieldConstantField K N →ₐ[K]
      RatFuncFiniteIntegralClosure K N where
  toFun c := ⟨c.1, c.2.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

local instance functionFieldConstantFinitePlaceMaximal
    (Q : FiniteExtensionFinitePlace K N) :
    Q.asIdeal.IsMaximal := Q.isMaximal

/-- Reduction modulo a finite place, restricted to the algebraic constant
field. -/
def functionFieldConstantQuotientAlgHom
    (Q : FiniteExtensionFinitePlace K N) :
    FunctionFieldConstantField K N →ₐ[K]
      (RatFuncFiniteIntegralClosure K N ⧸ Q.asIdeal) :=
  (Ideal.Quotient.mkₐ K Q.asIdeal).comp
    (functionFieldConstantToFiniteIntegralClosure K N)

omit [DecidableEq K] [DecidableEq (RatFunc K)]
  [FiniteDimensional (RatFunc K) N]
  [Algebra.IsSeparable (RatFunc K) N] in
/-- Reduction at a finite place is injective on algebraic constants. -/
theorem functionFieldConstantQuotientAlgHom_injective
    (Q : FiniteExtensionFinitePlace K N) :
    Function.Injective (functionFieldConstantQuotientAlgHom K N Q) :=
  (functionFieldConstantQuotientAlgHom K N Q).injective

omit [DecidableEq (RatFunc K)] in
/-- The residue field of a rational-function finite place is finite over a
finite constant field. -/
theorem ratFuncFinitePlaceResidueField_finite [Fintype K]
    (p : HeightOneSpectrum K[X]) : Finite p.asIdeal.ResidueField := by
  let r := finitePlaceNormalizedPrime p
  have hr0 : (r : K[X]) ≠ 0 := r.property.1.ne_zero
  have hrmonic : (r : K[X]).Monic :=
    (Polynomial.normalize_eq_self_iff_monic hr0).mp r.property.2
  have hp : p.asIdeal = Ideal.span ({(r : K[X])} : Set K[X]) := by
    calc
      p.asIdeal = (normalizedPrimeFinitePlace (K := K) r).asIdeal := by
        rw [normalizedPrimeFinitePlace_finitePlaceNormalizedPrime]
      _ = Ideal.span ({(r : K[X])} : Set K[X]) := rfl
  let : Module.Finite K (K[X] ⧸ p.asIdeal) := by
    rw [hp]
    exact hrmonic.finite_quotient
  let : Finite (K[X] ⧸ p.asIdeal) := Module.finite_of_finite K
  infer_instance

omit [DecidableEq (RatFunc K)] in
/-- Every finite-place residue field of a finite separable function field is
finite over a finite constant field. -/
theorem finiteExtensionFinitePlaceResidueField_finite [Fintype K]
    (P : FiniteExtensionFinitePlace K N) : Finite P.asIdeal.ResidueField := by
  let p := HeightOneSpectrum.under K[X] P
  let : Finite p.asIdeal.ResidueField :=
    ratFuncFinitePlaceResidueField_finite K p
  let : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal P.asIdeal
  let _ : IsScalarTower K[X] (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime P.asIdeal) := inferInstance
  let : Algebra.QuasiFiniteAt K[X] P.asIdeal := inferInstance
  let : Module.Finite p.asIdeal.ResidueField P.asIdeal.ResidueField :=
    inferInstance
  exact Module.finite_of_finite p.asIdeal.ResidueField

/-- Over a finite base field, the algebraic constant field of a finite
separable function field is finite-dimensional. -/
noncomputable instance functionFieldConstantField_finiteDimensional [Fintype K] :
    FiniteDimensional K (FunctionFieldConstantField K N) := by
  let p : HeightOneSpectrum K[X] := Polynomial.idealX K
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := RatFuncFiniteIntegralClosure K N) p.asIdeal (by
        intro x hx
        have hxA : algebraMap K[X] (RatFuncFiniteIntegralClosure K N) x = 0 :=
          (RingHom.mem_ker).mp hx
        have hxN : algebraMap K[X] N x = 0 :=
          congrArg Subtype.val hxA
        have hx0 : x = 0 := by
          exact FaithfulSMul.algebraMap_injective K[X] N (by simpa using hxN)
        subst x
        exact p.asIdeal.zero_mem)
  let P : p.asIdeal.primesOver (RatFuncFiniteIntegralClosure K N) :=
    ⟨Q, hQprime, ⟨hQcomap.symm⟩⟩
  let q : FiniteExtensionFinitePlace K N := primeOverHeightOne p P
  let : Finite q.asIdeal.ResidueField :=
    finiteExtensionFinitePlaceResidueField_finite K N q
  let : Finite (RatFuncFiniteIntegralClosure K N ⧸ q.asIdeal) :=
    Finite.of_injective
      (algebraMap (RatFuncFiniteIntegralClosure K N ⧸ q.asIdeal)
        q.asIdeal.ResidueField)
      (Ideal.injective_algebraMap_quotient_residueField q.asIdeal)
  let : Module.Finite K
      (RatFuncFiniteIntegralClosure K N ⧸ q.asIdeal) :=
    Module.Finite.of_finite
  exact FiniteDimensional.of_injective
    (functionFieldConstantQuotientAlgHom K N q).toLinearMap
    (functionFieldConstantQuotientAlgHom_injective K N q)

/-- The algebraic constant field is a finite type when the original constants
are finite. -/
noncomputable instance functionFieldConstantField_finite [Fintype K] :
    Finite (FunctionFieldConstantField K N) :=
  Module.finite_of_finite K

/-- The algebraic constant field is Galois over the finite base field. -/
noncomputable instance functionFieldConstantField_isGalois [Fintype K] :
    IsGalois K (FunctionFieldConstantField K N) :=
  inferInstance

end

end BGS.HasseWeil
