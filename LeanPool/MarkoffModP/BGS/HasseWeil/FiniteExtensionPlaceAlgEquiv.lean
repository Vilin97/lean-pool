/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceNormalizationTransport
import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlace

/-!
# Transporting function-field places across algebra equivalences

An equivalence of finite extensions over `K(X)` identifies both normalization
charts.  This file packages the induced equivalences of finite, infinity, and
exhaustive places and records preservation of absolute place degree.  In
particular, rational-place counts depend only on the `K(X)`-algebra up to
equivalence, not on its chosen field presentation.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain


section Fiber

variable (R A : Type*) [CommRing R] [IsDomain R]
  [CommRing A] [IsDomain A] [Algebra R A]
  [Algebra.IsIntegral R A] [Module.IsTorsionFree R A]

/-- A height-one prime restriction fiber is the usual type of primes above
the base prime. -/
def heightOneSpectrumFiberEquivPrimesOver (p : HeightOneSpectrum R) :
    {q : HeightOneSpectrum A // HeightOneSpectrum.under R q = p} ≃
      p.asIdeal.primesOver A where
  toFun q := ⟨q.1.asIdeal, q.1.isPrime, ⟨by
    have h := congrArg HeightOneSpectrum.asIdeal q.2
    exact h.symm⟩⟩
  invFun P := ⟨primeOverHeightOne p P, by
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def P.1 p.asIdeal).symm⟩
  left_inv q := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    rfl

end Fiber

variable (K L M : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
  [Field L] [Field M]
  [Algebra (RatFunc K) L] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) M]

local instance (priority := 10) finiteAlgEquivPolynomialAlgebraLeft :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance (priority := 10) finiteAlgEquivPolynomialAlgebraRight :
    Algebra K[X] M :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) M).comp
    (algebraMap K[X] (RatFunc K)))

local instance finiteAlgEquivPolynomialTowerLeft :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := K[X]) (S := RatFunc K) (A := L) rfl

local instance finiteAlgEquivPolynomialTowerRight :
    IsScalarTower K[X] (RatFunc K) M :=
  IsScalarTower.of_algebraMap_eq'
    (R := K[X]) (S := RatFunc K) (A := M) rfl

local instance (priority := 10) finiteAlgEquivInfinityAlgebraLeft :
    Algebra (RatFuncInfinityIntegers K) L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap (RatFuncInfinityIntegers K) (RatFunc K)))

local instance (priority := 10) finiteAlgEquivInfinityAlgebraRight :
    Algebra (RatFuncInfinityIntegers K) M :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) M).comp
    (algebraMap (RatFuncInfinityIntegers K) (RatFunc K)))

local instance finiteAlgEquivInfinityTowerLeft :
    IsScalarTower (RatFuncInfinityIntegers K) (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq'
    (R := RatFuncInfinityIntegers K) (S := RatFunc K) (A := L) rfl

local instance finiteAlgEquivInfinityTowerRight :
    IsScalarTower (RatFuncInfinityIntegers K) (RatFunc K) M :=
  IsScalarTower.of_algebraMap_eq'
    (R := RatFuncInfinityIntegers K) (S := RatFunc K) (A := M) rfl

local instance finiteAlgEquivInfinityConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance finiteAlgEquivInfinityConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegers K) (A := RatFunc K) rfl

local instance finiteAlgEquivPolynomialTorsionFreeLeft :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance finiteAlgEquivPolynomialTorsionFreeRight :
    Module.IsTorsionFree K[X] M :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) M

local instance finiteAlgEquivFiniteClosureTorsionFreeLeft :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance finiteAlgEquivFiniteClosureTorsionFreeRight :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree K[X] M

local instance finiteAlgEquivInfinityClosureTorsionFreeLeft :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance finiteAlgEquivInfinityClosureTorsionFreeRight :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) M

local instance finiteAlgEquivFiniteClosureConstantAlgebraLeft :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance finiteAlgEquivFiniteClosureConstantAlgebraRight :
    Algebra K (RatFuncFiniteIntegralClosure K M) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K M)).comp (algebraMap K K[X]))

local instance finiteAlgEquivFiniteClosureConstantTowerLeft :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := K[X]) (A := RatFuncFiniteIntegralClosure K L) rfl

local instance finiteAlgEquivFiniteClosureConstantTowerRight :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K M) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := K[X]) (A := RatFuncFiniteIntegralClosure K M) rfl

local instance finiteAlgEquivInfinityClosureConstantAlgebraLeft :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap (RatFuncInfinityIntegers K)
    (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance finiteAlgEquivInfinityClosureConstantAlgebraRight :
    Algebra K (RatFuncInfinityIntegralClosure K M) :=
  RingHom.toAlgebra ((algebraMap (RatFuncInfinityIntegers K)
    (RatFuncInfinityIntegralClosure K M)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance finiteAlgEquivInfinityClosureConstantTowerLeft :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegers K)
      (A := RatFuncInfinityIntegralClosure K L) rfl

local instance finiteAlgEquivInfinityClosureConstantTowerRight :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K M) :=
  IsScalarTower.of_algebraMap_eq'
    (R := K) (S := RatFuncInfinityIntegers K)
      (A := RatFuncInfinityIntegralClosure K M) rfl

/-- A `K(X)`-algebra equivalence restricts to the finite normalization
charts. -/
noncomputable def ratFuncFiniteIntegralClosureAlgEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    RatFuncFiniteIntegralClosure K L ≃ₐ[K[X]]
      RatFuncFiniteIntegralClosure K M :=
  (e.restrictScalars K[X]).mapIntegralClosure

/-- A `K(X)`-algebra equivalence restricts to the infinity normalization
charts. -/
noncomputable def ratFuncInfinityIntegralClosureAlgEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    RatFuncInfinityIntegralClosure K L ≃ₐ[RatFuncInfinityIntegers K]
      RatFuncInfinityIntegralClosure K M :=
  by
    change integralClosure (RatFuncInfinityIntegers K) L ≃ₐ[
      RatFuncInfinityIntegers K]
        integralClosure (RatFuncInfinityIntegers K) M
    exact (e.restrictScalars
      (RatFuncInfinityIntegers K)).mapIntegralClosure

/-- Finite places are invariant under an equivalence of the ambient
`K(X)`-algebras. -/
noncomputable def finiteExtensionFinitePlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionFinitePlace K L ≃ FiniteExtensionFinitePlace K M :=
  heightOneSpectrumEquivOfAlgEquiv
    (ratFuncFiniteIntegralClosureAlgEquivOfAlgEquiv K L M e)

/-- The residue fields of corresponding finite places are equivalent over
the constant field. -/
noncomputable def finiteExtensionFinitePlaceResidueFieldAlgEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) (Q : FiniteExtensionFinitePlace K L) :
    Q.asIdeal.ResidueField ≃ₐ[K]
      (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e Q).asIdeal.ResidueField :=
  heightOneSpectrumResidueFieldAlgEquiv
    ((ratFuncFiniteIntegralClosureAlgEquivOfAlgEquiv K L M e).restrictScalars K)
    Q

/-- Infinity places are invariant under an equivalence of the ambient
`K(X)`-algebras. -/
noncomputable def finiteExtensionInfinityPlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionInfinityPlace K L ≃
      FiniteExtensionInfinityPlace K M := by
  let R := RatFuncInfinityIntegers K
  let A := RatFuncInfinityIntegralClosure K L
  let B := RatFuncInfinityIntegralClosure K M
  let p := ratFuncInfinityPlace K
  let eAB : A ≃ₐ[R] B :=
    ratFuncInfinityIntegralClosureAlgEquivOfAlgEquiv K L M e
  let ePlaces : HeightOneSpectrum A ≃ HeightOneSpectrum B :=
    heightOneSpectrumEquivOfAlgEquiv eAB
  let eFibers :
      {q : HeightOneSpectrum A // HeightOneSpectrum.under R q = p} ≃
        {q : HeightOneSpectrum B // HeightOneSpectrum.under R q = p} :=
    { toFun := fun q => ⟨ePlaces q.1, by
          calc
            HeightOneSpectrum.under R (ePlaces q.1) =
                HeightOneSpectrum.under R q.1 := by
              exact heightOneSpectrumEquivOfAlgEquiv_under eAB q.1
            _ = p := q.2⟩
      invFun := fun q => ⟨ePlaces.symm q.1, by
          calc
            HeightOneSpectrum.under R (ePlaces.symm q.1) =
                HeightOneSpectrum.under R q.1 := by
              exact heightOneSpectrumEquivOfAlgEquiv_under eAB.symm q.1
            _ = p := q.2⟩
      left_inv := fun q => by
        apply Subtype.ext
        exact ePlaces.left_inv q.1
      right_inv := fun q => by
        apply Subtype.ext
        exact ePlaces.right_inv q.1 }
  exact
    (heightOneSpectrumFiberEquivPrimesOver R A p).symm.trans
      (eFibers.trans (heightOneSpectrumFiberEquivPrimesOver R B p))

/-- Exhaustive places are invariant under an equivalence of the ambient
`K(X)`-algebras. -/
noncomputable def finiteExtensionPlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionPlace K L ≃ FiniteExtensionPlace K M :=
  Equiv.sumCongr
    (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e)
    (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e)

/-- The absolute degree of a finite place is the dimension of its residue
field over the constant field. -/
theorem finiteExtensionFinitePlace_degree_eq_residue_finrank
    (Q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K L (.inl Q) =
      Module.finrank K Q.asIdeal.ResidueField := by
  let P := HeightOneSpectrum.under K[X] Q
  let : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  let _ : IsScalarTower K[X] (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime Q.asIdeal) := inferInstance
  let _ : Module.Free P.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    Module.Free.of_divisionRing P.asIdeal.ResidueField Q.asIdeal.ResidueField
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq P.asIdeal Q.asIdeal]
  rw [ratFuncFinitePlaceDegree_eq_finrank_residueField K P]
  rw [mul_comm, Module.finrank_mul_finrank]

/-- The absolute degree of an infinity place is the dimension of its residue
field over the constant field. -/
theorem finiteExtensionInfinityPlace_degree_eq_residue_finrank
    (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K L (.inr P) =
      Module.finrank K P.1.ResidueField := by
  let p := (ratFuncInfinityPlace K).asIdeal
  let hLocalAlg := Localization.AtPrime.algebraOfLiesOver p P.1
  let _ : IsScalarTower (RatFuncInfinityIntegers K) (Localization.AtPrime p)
      (Localization.AtPrime P.1) := inferInstance
  let _ : Module.Free p.ResidueField P.1.ResidueField :=
    Module.Free.of_divisionRing p.ResidueField P.1.ResidueField
  let : Algebra p.ResidueField P.1.ResidueField :=
    IsLocalRing.ResidueField.instAlgebra
  let : IsScalarTower K p.ResidueField P.1.ResidueField := inferInstance
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq p P.1]
  have hbase : Module.finrank K p.ResidueField = 1 :=
    by simpa [p] using
      (ratFuncInfinityPlaceResidueEquiv K).toLinearEquiv.finrank_eq
  calc
    Module.finrank p.ResidueField P.1.ResidueField =
        1 * Module.finrank p.ResidueField P.1.ResidueField := by simp
    _ = Module.finrank K p.ResidueField *
        Module.finrank p.ResidueField P.1.ResidueField := by rw [hbase]
    _ = Module.finrank K P.1.ResidueField :=
      Module.finrank_mul_finrank K p.ResidueField P.1.ResidueField

/-- Corresponding finite places have the same absolute degree. -/
@[simp]
theorem finiteExtensionFinitePlaceEquivOfAlgEquiv_degree
    (e : L ≃ₐ[RatFunc K] M) (Q : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K M
        (.inl (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e Q)) =
      finiteExtensionPlaceDegree K L (.inl Q) := by
  calc
    finiteExtensionPlaceDegree K M
        (.inl (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e Q)) =
        Module.finrank K
          (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e Q).asIdeal.ResidueField :=
      finiteExtensionFinitePlace_degree_eq_residue_finrank K M _
    _ = Module.finrank K Q.asIdeal.ResidueField :=
      (finiteExtensionFinitePlaceResidueFieldAlgEquivOfAlgEquiv
        K L M e Q).toLinearEquiv.finrank_eq.symm
    _ = finiteExtensionPlaceDegree K L (.inl Q) :=
      (finiteExtensionFinitePlace_degree_eq_residue_finrank K L Q).symm

@[simp]
theorem finiteExtensionInfinityPlaceEquivOfAlgEquiv_asIdeal
    (e : L ≃ₐ[RatFunc K] M) (P : FiniteExtensionInfinityPlace K L) :
    (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e P).1 =
      P.1.comap
        (ratFuncInfinityIntegralClosureAlgEquivOfAlgEquiv K L M e).symm := by
  rfl

/-- The residue fields of corresponding infinity places are equivalent over
the constant field. -/
noncomputable def finiteExtensionInfinityPlaceResidueFieldAlgEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) (P : FiniteExtensionInfinityPlace K L) :
    P.1.ResidueField ≃ₐ[K]
      (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e P).1.ResidueField := by
  let eInf := ratFuncInfinityIntegralClosureAlgEquivOfAlgEquiv K L M e
  change P.1.ResidueField ≃ₐ[K] (P.1.comap eInf.symm).ResidueField
  exact Ideal.residueFieldAlgEquiv P.1 (P.1.comap eInf.symm)
    (eInf.restrictScalars K) (by
      change P.1 = (P.1.comap eInf.symm).comap eInf
      exact (Ideal.comap_of_equiv eInf.toRingEquiv).symm)

/-- Corresponding infinity places have the same absolute degree. -/
@[simp]
theorem finiteExtensionInfinityPlaceEquivOfAlgEquiv_degree
    (e : L ≃ₐ[RatFunc K] M) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K M
        (.inr (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e P)) =
      finiteExtensionPlaceDegree K L (.inr P) := by
  calc
    finiteExtensionPlaceDegree K M
        (.inr (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e P)) =
        Module.finrank K
          (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e P).1.ResidueField :=
      finiteExtensionInfinityPlace_degree_eq_residue_finrank K M _
    _ = Module.finrank K P.1.ResidueField :=
      (finiteExtensionInfinityPlaceResidueFieldAlgEquivOfAlgEquiv
        K L M e P).toLinearEquiv.finrank_eq.symm
    _ = finiteExtensionPlaceDegree K L (.inr P) :=
      (finiteExtensionInfinityPlace_degree_eq_residue_finrank K L P).symm

/-- The exhaustive place equivalence preserves absolute degree. -/
@[simp]
theorem finiteExtensionPlaceEquivOfAlgEquiv_degree
    (e : L ≃ₐ[RatFunc K] M) (P : FiniteExtensionPlace K L) :
    finiteExtensionPlaceDegree K M
        (finiteExtensionPlaceEquivOfAlgEquiv K L M e P) =
      finiteExtensionPlaceDegree K L P := by
  cases P with
  | inl Q =>
      exact finiteExtensionFinitePlaceEquivOfAlgEquiv_degree K L M e Q
  | inr Q =>
      exact finiteExtensionInfinityPlaceEquivOfAlgEquiv_degree K L M e Q

/-- Degree-one finite places are invariant under a `K(X)`-algebra
equivalence. -/
noncomputable def finiteExtensionRationalFinitePlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionRationalFinitePlace K L ≃
      FiniteExtensionRationalFinitePlace K M :=
  Equiv.subtypeEquiv
    (finiteExtensionFinitePlaceEquivOfAlgEquiv K L M e) (by
      intro Q
      rw [finiteExtensionFinitePlaceEquivOfAlgEquiv_degree K L M e Q])

/-- Degree-one infinity places are invariant under a `K(X)`-algebra
equivalence. -/
noncomputable def finiteExtensionRationalInfinityPlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionRationalInfinityPlace K L ≃
      FiniteExtensionRationalInfinityPlace K M :=
  Equiv.subtypeEquiv
    (finiteExtensionInfinityPlaceEquivOfAlgEquiv K L M e) (by
      intro P
      rw [finiteExtensionInfinityPlaceEquivOfAlgEquiv_degree K L M e P])

/-- Complete degree-one place types are invariant under a `K(X)`-algebra
equivalence. -/
noncomputable def finiteExtensionRationalPlaceEquivOfAlgEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    FiniteExtensionRationalPlace K L ≃
      FiniteExtensionRationalPlace K M :=
  Equiv.sumCongr
    (finiteExtensionRationalFinitePlaceEquivOfAlgEquiv K L M e)
    (finiteExtensionRationalInfinityPlaceEquivOfAlgEquiv K L M e)

/-- Complete rational-place counts are invariant under an equivalence of
finite `K(X)`-algebras. -/
theorem finiteExtensionRationalPlaceCount_eq_of_algEquiv
    (e : L ≃ₐ[RatFunc K] M) :
    finiteExtensionRationalPlaceCount K L =
      finiteExtensionRationalPlaceCount K M :=
  Nat.card_congr (finiteExtensionRationalPlaceEquivOfAlgEquiv K L M e)

end

end BGS.HasseWeil
