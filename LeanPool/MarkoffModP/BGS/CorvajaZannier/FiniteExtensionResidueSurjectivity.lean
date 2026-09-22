/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionPrincipalDivisor

/-!
# Constants surject onto residue fields of all function-field places

Let `L / K(X)` be finite and separable, with `K` algebraically closed.  At a
finite place of `L`, the residue field is integral over the residue field of
the place below it; the latter is canonically `K`.  The same argument applies
above infinity, using the explicit residue equivalence at the rational
function infinity place.  Thus constants surject onto every residue field.

This is the exact coefficient-lifting input used by Corvaja--Zannier case (i):
equal negative leading terms can be cancelled by a genuine constant.
-/

open scoped nonZeroDivisors Polynomial
open IsDedekindDomain

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) residuePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance residuePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  .of_algebraMap_eq' rfl

local instance residueFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance residueFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance residuePolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance residueFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance residueFiniteIntegralClosureConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
      (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance residueFiniteIntegralClosureConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

local instance residueInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance residueInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  .of_algebraMap_eq' rfl

local instance residueInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance residueInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance residueInfinityIntegralClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance residueInfinityIntegralClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  .of_algebraMap_eq' rfl

variable [IsAlgClosed K]

omit [DecidableEq (RatFunc K)] in
/-- Constants surject onto the residue field of every finite place of a finite
separable extension of `K(X)`, when `K` is algebraically closed. -/
theorem finiteExtensionFinitePlace_constantResidue_surjective
    (q : FiniteExtensionFinitePlace K L) :
    Function.Surjective (algebraMap K q.asIdeal.ResidueField) := by
  let p := HeightOneSpectrum.under K[X] q
  let : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have : IsScalarTower K[X] (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := inferInstance
  let : Algebra.QuasiFiniteAt K[X] q.asIdeal := inferInstance
  let : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    inferInstance
  let : Algebra.IsIntegral p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    Algebra.IsIntegral.of_finite _ _
  let e := ratFuncFinitePlaceResidueEquiv K p
  let : IsAlgClosed p.asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv K p.asIdeal.ResidueField e.symm.toRingEquiv
  let : IsScalarTower K p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    inferInstance
  intro z
  obtain ⟨a, ha⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := p.asIdeal.ResidueField) (K := q.asIdeal.ResidueField)).2 z
  refine ⟨e a, ?_⟩
  rw [← ha, IsScalarTower.algebraMap_apply K p.asIdeal.ResidueField]
  congr 1
  apply e.injective
  simp

/-- Constants surject onto the residue field of every place above infinity in
a finite separable extension of `K(X)`, when `K` is algebraically closed. -/
theorem finiteExtensionInfinityPlace_constantResidue_surjective
    (P : FiniteExtensionInfinityPlace K L) :
    Function.Surjective (algebraMap K P.1.ResidueField) := by
  let p := (ratFuncInfinityPlace K).asIdeal
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver p P.1
  have : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  let : Algebra.QuasiFiniteAt (RatFuncInfinityIntegers K) P.1 :=
    inferInstance
  let : Module.Finite p.ResidueField P.1.ResidueField := inferInstance
  let : Algebra.IsIntegral p.ResidueField P.1.ResidueField :=
    Algebra.IsIntegral.of_finite _ _
  let e := ratFuncInfinityPlaceResidueEquiv K
  let : IsAlgClosed p.ResidueField :=
    IsAlgClosed.of_ringEquiv K p.ResidueField e.symm.toRingEquiv
  let : IsScalarTower K p.ResidueField P.1.ResidueField := inferInstance
  intro z
  obtain ⟨a, ha⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := p.ResidueField) (K := P.1.ResidueField)).2 z
  refine ⟨e a, ?_⟩
  rw [← ha, IsScalarTower.algebraMap_apply K p.ResidueField]
  congr 1
  simpa using (e.symm.commutes (e a)).symm

end
end BGS.CorvajaZannier
