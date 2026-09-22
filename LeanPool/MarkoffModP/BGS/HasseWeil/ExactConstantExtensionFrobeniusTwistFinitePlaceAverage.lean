/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionPlaceSplittingMultiplicity
import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionRationalPlace
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlaceFrobeniusAverage
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistFinitePlaceUnramified
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentCotrace
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneRationalPlaceAffineComparison
import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlaceTower

/-!
# Global finite-place averaging for Frobenius twists

This file removes the presentation choice from the local Frobenius-coset
fixed-point identity and assembles the rational finite places of all
Frobenius-twist fields without duplication.
-/

open scoped Polynomial TensorProduct BigOperators

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


/-- Restricting a finite place first to an intermediate function field and
then to `K(X)` agrees with direct restriction to `K(X)`.  This is the
finite-extension-place version of `Ideal.under_under`; unlike the raw chart
statement `finitePlaceUnder_under`, both sides live in the normalized
finite-place model of `K(X)`. -/
theorem finitePlaceUnder_ratFunc_under
    (K M L : Type*) [Field K] [Field M] [Field L]
    [DecidableEq K] [DecidableEq (RatFunc K)]
    [Algebra (RatFunc K) M] [FiniteDimensional (RatFunc K) M]
    [Algebra.IsSeparable (RatFunc K) M]
    [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    [Algebra.IsSeparable (RatFunc K) L]
    [Algebra M L] [IsScalarTower (RatFunc K) M L]
    (Q : FiniteExtensionFinitePlace K L) :
    finitePlaceUnder K (RatFunc K) M (finitePlaceUnder K M L Q) =
      finitePlaceUnder K (RatFunc K) L Q := by
  let : Algebra (RatFuncFiniteIntegralClosure K (RatFunc K))
      (RatFuncFiniteIntegralClosure K M) :=
    (finiteIntegralClosureMap K (RatFunc K) M).toAlgebra
  let : Algebra (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
    (finiteIntegralClosureMap K M L).toAlgebra
  let : Algebra (RatFuncFiniteIntegralClosure K (RatFunc K))
      (RatFuncFiniteIntegralClosure K L) :=
    (finiteIntegralClosureMap K (RatFunc K) L).toAlgebra
  let : SMul (RatFuncFiniteIntegralClosure K (RatFunc K))
      (RatFuncFiniteIntegralClosure K M) := Algebra.toSMul
  let : SMul (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) := Algebra.toSMul
  let : SMul (RatFuncFiniteIntegralClosure K (RatFunc K))
      (RatFuncFiniteIntegralClosure K L) := Algebra.toSMul
  let : IsScalarTower (RatFuncFiniteIntegralClosure K (RatFunc K))
      (RatFuncFiniteIntegralClosure K M)
      (RatFuncFiniteIntegralClosure K L) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      apply Subtype.ext
      change algebraMap (RatFunc K) L x.1 =
        algebraMap M L (algebraMap (RatFunc K) M x.1)
      exact IsScalarTower.algebraMap_apply (RatFunc K) M L x.1
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact Ideal.under_under Q.asIdeal

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance finiteAverageRatFuncRationalFinitePlaceFintype :
    Fintype (RatFuncRationalFinitePlace C) := Fintype.ofFinite _

local instance finiteAverageBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance finiteAverageBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteAverageTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

local instance finiteAverageRatFuncClosureConstantAlgebra :
    Algebra C (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (RatFuncFiniteIntegralClosure C (RatFunc C))).comp
      (algebraMap C C[X]))

local instance finiteAverageRatFuncClosureConstantTower :
    IsScalarTower C C[X]
      (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The chart-normalization equivalence over the polynomial base ring. -/
noncomputable def ratFuncFiniteBasePolynomialAlgEquivChart :
    C[X] ≃ₐ[C[X]] RatFuncFiniteIntegralClosure C (RatFunc C) :=
  { ratFuncFiniteBaseRingEquivChart C with
    commutes' := fun r => by
      apply Subtype.ext
      change algebraMap (FunctionField.ringOfIntegers C (RatFunc C))
          (RatFunc C)
          (ratFuncFiniteBaseRingEquivChart C r) =
        algebraMap (FunctionField.ringOfIntegers C (RatFunc C))
          (RatFunc C)
          (algebraMap C[X] (FunctionField.ringOfIntegers C (RatFunc C)) r)
      rw [ratFuncFiniteBaseRingEquivChart_algebraMap]
      rfl }

/-- The same equivalence over the constant field. -/
noncomputable def ratFuncFiniteBaseAlgEquivChart :
    C[X] ≃ₐ[C] RatFuncFiniteIntegralClosure C (RatFunc C) :=
  (ratFuncFiniteBasePolynomialAlgEquivChart C).restrictScalars C

local instance finiteAverageRatFuncClosureModuleFinite :
    Module.Finite C[X] (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  Module.Finite.equiv
    (ratFuncFiniteBasePolynomialAlgEquivChart C).toLinearEquiv

/-- The finite-chart normalization of `C[X]` in `C(X)` is canonically
equivalent to `C[X]` itself, hence their finite-place models agree. -/
noncomputable def ratFuncFinitePlaceEquivFiniteExtension :
    IsDedekindDomain.HeightOneSpectrum C[X] ≃
      FiniteExtensionFinitePlace C (RatFunc C) :=
  heightOneSpectrumEquivOfAlgEquiv
    (ratFuncFiniteBasePolynomialAlgEquivChart C)

private theorem finrank_mul_finrank_of_fields
    (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] :
    Module.finrank K F * Module.finrank F E = Module.finrank K E :=
  Module.finrank_mul_finrank K F E

/-- A finite-place degree is the dimension of its residue field over the
constant field. -/
private theorem finiteExtensionPlaceDegree_inl_eq_finrank_residueField_ratFunc
    (Q : FiniteExtensionFinitePlace C (RatFunc C)) :
    finiteExtensionPlaceDegree C (RatFunc C) (.inl Q) =
      Module.finrank C Q.asIdeal.ResidueField := by
  let P := IsDedekindDomain.HeightOneSpectrum.under C[X] Q
  let : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  let hLocalAlg :=
    Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  let : IsScalarTower C[X] (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime Q.asIdeal) := inferInstance
  rw [finiteExtensionPlaceDegree, Ideal.inertiaDeg_eq P.asIdeal Q.asIdeal]
  rw [ratFuncFinitePlaceDegree_eq_finrank_residueField C P]
  rw [mul_comm, finrank_mul_finrank_of_fields]

/-- The chart-normalization equivalence preserves finite-place degree. -/
@[simp]
theorem finiteExtensionPlaceDegree_ratFuncFinitePlaceEquivFiniteExtension
    (P : IsDedekindDomain.HeightOneSpectrum C[X]) :
    finiteExtensionPlaceDegree C (RatFunc C)
        (.inl (ratFuncFinitePlaceEquivFiniteExtension C P)) =
      ratFuncFinitePlaceDegree P := by
  let Q := ratFuncFinitePlaceEquivFiniteExtension C P
  have hres := heightOneSpectrum_residueField_finrank_eq
    (ratFuncFiniteBaseAlgEquivChart C) P
  calc
    finiteExtensionPlaceDegree C (RatFunc C) (.inl Q) =
        Module.finrank C Q.asIdeal.ResidueField :=
      finiteExtensionPlaceDegree_inl_eq_finrank_residueField_ratFunc C Q
    _ = Module.finrank C P.asIdeal.ResidueField := hres.symm
    _ = ratFuncFinitePlaceDegree P :=
      (ratFuncFinitePlaceDegree_eq_finrank_residueField C P).symm

/-- Degree-one finite places in the direct `C[X]` chart and in the generic
finite-extension place model of `C(X)` are canonically equivalent. -/
noncomputable def ratFuncRationalFinitePlaceEquivFiniteExtension :
    RatFuncRationalFinitePlace C ≃
      FiniteExtensionRationalFinitePlace C (RatFunc C) :=
  Equiv.subtypeEquiv (ratFuncFinitePlaceEquivFiniteExtension C) (by
    intro P
    rw [finiteExtensionPlaceDegree_ratFuncFinitePlaceEquivFiniteExtension])

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- Choose the explicit `S[X]` presentation of an actual top finite place,
while transporting rationality of its restriction to the downstairs place.
This is the only point where the nested integral-closure contraction tower is
expanded in this file. -/
private theorem exists_presentedFinitePlace_of_under_rational :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finiteExtensionPlaceDegree C (RatFunc C)
          (.inl (finitePlaceUnder C (RatFunc C)
            (ExactConstantExtension C N S) Q)) = 1 →
      ∃ q : IsDedekindDomain.HeightOneSpectrum
          (integralClosure S[X] (ExactConstantExtension C N S)),
        exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q = Q ∧
          finiteExtensionPlaceDegree C (RatFunc C)
            (.inl (finitePlaceUnder C (RatFunc C) N
              (exactConstantExtensionDownstairsFinitePlace
                C S N hExact q))) = 1 := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  intro Q hBase
  let e := exactConstantExtensionPresentedFinitePlaceEquiv C S N hExact
  let q := e.symm Q
  have heq : exactConstantExtensionCompatibleBaseFinitePlace
      C S N hExact q = Q := by
    calc
      exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q =
          e q :=
        (exactConstantExtensionPresentedFinitePlaceEquiv_apply
          C S N hExact q).symm
      _ = Q := e.apply_symm_apply Q
  have hDownstairs : finitePlaceUnder C N T Q =
      exactConstantExtensionDownstairsFinitePlace C S N hExact q := by
    calc
      finitePlaceUnder C N T Q =
          finitePlaceUnder C N T
            (exactConstantExtensionCompatibleBaseFinitePlace
              C S N hExact q) := congrArg _ heq.symm
      _ = exactConstantExtensionDownstairsFinitePlace C S N hExact q :=
        exactConstantExtensionCompatibleBaseFinitePlace_under_original
          C S N hExact q
  have hUnderTower : finitePlaceUnder C (RatFunc C) N
      (finitePlaceUnder C N T Q) =
        finitePlaceUnder C (RatFunc C) T Q :=
    finitePlaceUnder_ratFunc_under C N T Q
  refine ⟨q, heq, ?_⟩
  rw [← hDownstairs, hUnderTower]
  exact hBase

/-- Every actual top finite place over a rational finite place of `C(X)` has
ambient degree `[S : C]`, provided the constant-extension degree is divisible
by the original Galois degree. -/
theorem exactConstantExtensionFinitePlace_degree_eq_finrank_of_under_rational
    (hDegreeDiv : Module.finrank (RatFunc C) N ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finiteExtensionPlaceDegree C (RatFunc C)
          (.inl (finitePlaceUnder C (RatFunc C)
            (ExactConstantExtension C N S) Q)) = 1 →
    finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inl Q) =
      Module.finrank C S := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) T := Algebra.toSMul
  let : Module (RatFunc S) T := Algebra.toModule
  let : FiniteDimensional (RatFunc S) T :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) T :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  intro Q hBase
  obtain ⟨q, heq, hBaseQ⟩ :=
    exists_presentedFinitePlace_of_under_rational C S N hExact Q hBase
  have hS : finiteExtensionPlaceDegree S T
      (.inl (exactConstantExtensionUpstairsFinitePlace C S N hExact q)) = 1 :=
    exactConstantExtensionUpstairsFinitePlace_degree_eq_one_of_under_degree_one
      C S N hExact q hBaseQ hDegreeDiv
  have hDegree := exactConstantExtensionCompatibleBaseFinitePlace_degree_eq
    C S N hExact q hS
  rw [heq] at hDegree
  exact hDegree

/-- Presentation-free local Frobenius-coset identity above an arbitrary
rational finite base place. -/
theorem exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum_of_under_rational
    (hDegreeDiv : Module.finrank (RatFunc C) N ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    ∀ (Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S)),
      finiteExtensionPlaceDegree C (RatFunc C)
          (.inl (finitePlaceUnder C (RatFunc C)
            (ExactConstantExtension C N S) Q)) = 1 →
    let P := finitePlaceUnder C (RatFunc C)
      (ExactConstantExtension C N S) Q
    let pi := exactConstantExtensionConstantQuotient
      C (RatFunc C) N S hExact
    letI : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
    letI : Fintype
        (ExactConstantExtension C N S ≃ₐ[RatFunc C]
          ExactConstantExtension C N S) := Fintype.ofFinite _
    letI : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
    letI : Fintype
        (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
          Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
    letI := finiteIntegralClosureGalAction C (RatFunc C)
      (ExactConstantExtension C N S)
    letI := finitePlaceUnderFiberGalAction C (RatFunc C)
      (ExactConstantExtension C N S) P
    (∑ g : pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
        Set (S ≃ₐ[C] S)),
      Nat.card (MulAction.fixedBy
        (FinitePlaceUnderFiber C (RatFunc C)
          (ExactConstantExtension C N S) P) g.1)) =
      Nat.card (N ≃ₐ[RatFunc C] N) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  intro Q hBase
  obtain ⟨q, heq, hBaseQ⟩ :=
    exists_presentedFinitePlace_of_under_rational C S N hExact Q hBase
  rw [← heq]
  exact exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum
    C S N hExact (RatFunc C) q hBaseQ hDegreeDiv

/-- The Frobenius-fiber parametrization sends `g` to the ambient
Frobenius-twist automorphism `(Frob, g)`. -/
@[simp]
theorem exactConstantExtensionFrobeniusFiberEquiv_apply_val
    (g : N ≃ₐ[RatFunc C] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    ((exactConstantExtensionFrobeniusFiberEquiv
        C (RatFunc C) N S hExact) g).1 =
      exactConstantExtensionFrobeniusTwist
        C (RatFunc C) N S hExact g := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  rfl

/-- Above one rational finite place of `C(X)`, summing fixed top places over
all canonical Frobenius twists contributes exactly `|Gal(N/C(X))|`. -/
theorem sum_card_finitePlaceUnderFiber_fixedBy_frobeniusTwist_eq_card_galois
    (hDegreeDiv : Module.finrank (RatFunc C) N ∣ Module.finrank C S)
    (P : RatFuncRationalFinitePlace C) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    let P₀ := ratFuncRationalFinitePlaceEquivFiniteExtension C P
    letI := finiteIntegralClosureGalAction C (RatFunc C)
      (ExactConstantExtension C N S)
    letI := finitePlaceUnderFiberGalAction C (RatFunc C)
      (ExactConstantExtension C N S) P₀.1
    (∑ g : N ≃ₐ[RatFunc C] N,
      Nat.card (MulAction.fixedBy
        (FinitePlaceUnderFiber C (RatFunc C)
          (ExactConstantExtension C N S) P₀.1)
        (exactConstantExtensionFrobeniusTwist
          C (RatFunc C) N S hExact g))) =
      Nat.card (N ≃ₐ[RatFunc C] N) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let P₀ := ratFuncRationalFinitePlaceEquivFiniteExtension C P
  let := finiteIntegralClosureGalAction C (RatFunc C) T
  let := finitePlaceUnderFiberGalAction C (RatFunc C) T P₀.1
  let pi := exactConstantExtensionConstantQuotient
    C (RatFunc C) N S hExact
  let : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
  let : Fintype (T ≃ₐ[RatFunc C] T) := Fintype.ofFinite _
  let : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
  let : Fintype
      (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
        Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
  obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective C (RatFunc C) T P₀.1
  have hBase : finiteExtensionPlaceDegree C (RatFunc C)
      (.inl (finitePlaceUnder C (RatFunc C) T Q)) = 1 := by
    rw [hQ]
    exact P₀.2
  have hlocal :=
    exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum_of_under_rational
      C S N hExact hDegreeDiv Q hBase
  rw [hQ] at hlocal
  let e := exactConstantExtensionFrobeniusFiberEquiv
    C (RatFunc C) N S hExact
  calc
    (∑ g : N ≃ₐ[RatFunc C] N,
        Nat.card (MulAction.fixedBy
          (FinitePlaceUnderFiber C (RatFunc C) T P₀.1)
          (exactConstantExtensionFrobeniusTwist
            C (RatFunc C) N S hExact g))) =
        ∑ g : N ≃ₐ[RatFunc C] N,
          Nat.card (MulAction.fixedBy
            (FinitePlaceUnderFiber C (RatFunc C) T P₀.1) (e g).1) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [exactConstantExtensionFrobeniusFiberEquiv_apply_val]
    _ = ∑ x : pi ⁻¹'
          ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
            Set (S ≃ₐ[C] S)),
          Nat.card (MulAction.fixedBy
            (FinitePlaceUnderFiber C (RatFunc C) T P₀.1) x.1) :=
      e.sum_comp (fun x => Nat.card (MulAction.fixedBy
        (FinitePlaceUnderFiber C (RatFunc C) T P₀.1) x.1))
    _ = Nat.card (N ≃ₐ[RatFunc C] N) := hlocal

/-- Fixed top finite places in the restriction fiber above one rational
finite place of `C(X)`, for one canonical Frobenius twist. -/
abbrev FrobeniusTwistFinitePlaceFiberFixedBy
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) (P : RatFuncRationalFinitePlace C) :
    Type _ :=
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  letI : DistribMulAction (RatFunc C)
      (ExactConstantExtension C N S) := Module.toDistribMulAction
  letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
    DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let P₀ := ratFuncRationalFinitePlaceEquivFiniteExtension C P
  @MulAction.fixedBy
    (ExactConstantExtension C N S ≃ₐ[RatFunc C]
      ExactConstantExtension C N S)
    (FinitePlaceUnderFiber C (RatFunc C)
      (ExactConstantExtension C N S) P₀.1)
    _
    (finitePlaceUnderFiberGalAction C (RatFunc C)
      (ExactConstantExtension C N S) P₀.1)
    (exactConstantExtensionFrobeniusTwist
      C (RatFunc C) N S hExact g)

/-- Rational finite places of one Frobenius-twist field are the disjoint
union, over rational finite places of `C(X)`, of the ambient fixed top places
in the corresponding restriction fiber. -/
noncomputable def
    frobeniusTwistField_rationalFinitePlace_equiv_sigma_fiberFixedBy
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[RatFunc C] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : DistribMulAction (RatFunc C)
        (ExactConstantExtension C N S) := Module.toDistribMulAction
    letI : MulAction (RatFunc C) (ExactConstantExtension C N S) :=
      DistribMulAction.toMulAction
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : IsGalois (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C (RatFunc C) N S hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let F := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact g
    letI : Algebra (RatFunc C) F :=
      SubalgebraClass.toAlgebra F.toSubalgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) := inferInstance
    letI : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    letI : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C (RatFunc C) N S hExact g
    FiniteExtensionRationalFinitePlace C F ≃
      Σ P : RatFuncRationalFinitePlace C,
        FrobeniusTwistFinitePlaceFiberFixedBy C S N hExact g P := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) F T := inferInstance
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  let sigma := exactConstantExtensionFrobeniusTwist
    C (RatFunc C) N S hExact g
  let baseEquiv := ratFuncRationalFinitePlaceEquivFiniteExtension C
  have hDegreeDiv : Module.finrank (RatFunc C) N ∣ Module.finrank C S := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hdiv
  let AmbientFixed :=
    {Q : FiniteExtensionFinitePlace C T //
      finiteExtensionPlaceDegree C T (.inl Q) = Module.finrank C S ∧
        finitePlaceGalSmul C (RatFunc C) T sigma Q = Q}
  let SigmaFixed := Σ P : RatFuncRationalFinitePlace C,
    FrobeniusTwistFinitePlaceFiberFixedBy C S N hExact g P
  let toAmbient : SigmaFixed → AmbientFixed := fun x => by
    let P₀ := baseEquiv x.1
    let Q := x.2.1.1
    have hBase : finiteExtensionPlaceDegree C (RatFunc C)
        (.inl (finitePlaceUnder C (RatFunc C) T Q)) = 1 := by
      rw [x.2.1.2]
      exact P₀.2
    refine ⟨Q,
      exactConstantExtensionFinitePlace_degree_eq_finrank_of_under_rational
        C S N hExact hDegreeDiv Q hBase, ?_⟩
    exact congrArg Subtype.val x.2.2
  have hInjective : Function.Injective toAmbient := by
    rintro ⟨P, x⟩ ⟨R, y⟩ hxy
    have hQ : x.1.1 = y.1.1 := congrArg Subtype.val hxy
    have hBase : (baseEquiv P).1 = (baseEquiv R).1 := by
      calc
        (baseEquiv P).1 = finitePlaceUnder C (RatFunc C) T x.1.1 := x.1.2.symm
        _ = finitePlaceUnder C (RatFunc C) T y.1.1 := congrArg _ hQ
        _ = (baseEquiv R).1 := y.1.2
    have hP : P = R := baseEquiv.injective (Subtype.ext hBase)
    subst R
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Subtype.ext
    exact hQ
  have hSurjective : Function.Surjective toAmbient := by
    intro z
    let Q := z.1
    have hFdegree : finiteExtensionPlaceDegree C F
        (.inl (finitePlaceUnder C F T Q)) = 1 :=
      frobeniusTwistField_ambientFixed_finitePlace_under_degree_eq_one
        C N S hExact g hdiv Q z.2.1 z.2.2
    let R₀ : FiniteExtensionRationalFinitePlace C F :=
      ⟨finitePlaceUnder C F T Q, hFdegree⟩
    let P₀ : FiniteExtensionRationalFinitePlace C (RatFunc C) :=
      rationalFinitePlaceUnder C (RatFunc C) F R₀
    let P : RatFuncRationalFinitePlace C := baseEquiv.symm P₀
    have hP : baseEquiv P = P₀ := baseEquiv.apply_symm_apply P₀
    have hFiber : finitePlaceUnder C (RatFunc C) T Q = (baseEquiv P).1 := by
      calc
        finitePlaceUnder C (RatFunc C) T Q =
            finitePlaceUnder C (RatFunc C) F (finitePlaceUnder C F T Q) :=
          (finitePlaceUnder_ratFunc_under C F T Q).symm
        _ = P₀.1 := rfl
        _ = (baseEquiv P).1 := congrArg Subtype.val hP.symm
    let xFiber : FinitePlaceUnderFiber C (RatFunc C) T (baseEquiv P).1 :=
      ⟨Q, hFiber⟩
    let xFixed : FrobeniusTwistFinitePlaceFiberFixedBy
        C S N hExact g P := ⟨xFiber, by
      apply Subtype.ext
      exact z.2.2⟩
    refine ⟨⟨P, xFixed⟩, ?_⟩
    apply Subtype.ext
    change Q = z.1
    rfl
  let eSigma : SigmaFixed ≃ AmbientFixed :=
    Equiv.ofBijective toAmbient ⟨hInjective, hSurjective⟩
  exact (frobeniusTwistField_rationalFinitePlace_equiv_ambientFixedFinitePlace
    C N S hExact g hdiv).trans eSigma.symm

/-- The number of rational finite places of the fixed field attached to one
canonical Frobenius twist.  The instances are fixed explicitly so that this
number can be summed over the original Galois group. -/
noncomputable def frobeniusTwistFieldRationalFinitePlaceCount
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) : ℕ :=
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  letI : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  letI : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  Nat.card (FiniteExtensionRationalFinitePlace C F)

/-- For one twist, rational finite places split as the finite sum of fixed
restriction fibers above the rational finite places of `C(X)`. -/
theorem frobeniusTwistFieldRationalFinitePlaceCount_eq_sum_fiberFixedBy
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[RatFunc C] N) :
    frobeniusTwistFieldRationalFinitePlaceCount C S N hExact g =
      ∑ P : RatFuncRationalFinitePlace C,
        Nat.card (FrobeniusTwistFinitePlaceFiberFixedBy
          C S N hExact g P) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : DistribMulAction (RatFunc C) T := Module.toDistribMulAction
  let : MulAction (RatFunc C) T := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : IsGalois (RatFunc C) T :=
    exactConstantExtension_isGalois C (RatFunc C) N S hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let F := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact g
  let : Algebra (RatFunc C) F :=
    SubalgebraClass.toAlgebra F.toSubalgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_frobeniusTwistField_over_ratFunc C N S hExact g
  let : Algebra F T := F.toAlgebra
  let : SMul F T := Algebra.toSMul
  let : Module F T := Algebra.toModule
  let : IsScalarTower (RatFunc C) F T := inferInstance
  let : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  let : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C (RatFunc C) N S hExact g
  change Nat.card (FiniteExtensionRationalFinitePlace C F) = _
  rw [Nat.card_congr
    (frobeniusTwistField_rationalFinitePlace_equiv_sigma_fiberFixedBy
      C S N hExact hdiv g), Nat.card_sigma]

/-- Summed over all canonical Frobenius twists, the number of rational
finite places is exactly the order of the original Galois group times the
number of constants. -/
theorem sum_frobeniusTwistFieldRationalFinitePlaceCount_eq_card_galois_mul_card
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[RatFunc C] N,
      frobeniusTwistFieldRationalFinitePlaceCount C S N hExact g) =
      Nat.card (N ≃ₐ[RatFunc C] N) * Nat.card C := by
  have hDegreeDiv :
      Module.finrank (RatFunc C) N ∣ Module.finrank C S := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hdiv
  calc
    (∑ g : N ≃ₐ[RatFunc C] N,
        frobeniusTwistFieldRationalFinitePlaceCount C S N hExact g) =
        ∑ g : N ≃ₐ[RatFunc C] N,
          ∑ P : RatFuncRationalFinitePlace C,
            Nat.card (FrobeniusTwistFinitePlaceFiberFixedBy
              C S N hExact g P) := by
      apply Finset.sum_congr rfl
      intro g _
      exact frobeniusTwistFieldRationalFinitePlaceCount_eq_sum_fiberFixedBy
        C S N hExact hdiv g
    _ = ∑ P : RatFuncRationalFinitePlace C,
          ∑ g : N ≃ₐ[RatFunc C] N,
            Nat.card (FrobeniusTwistFinitePlaceFiberFixedBy
              C S N hExact g P) := by
      rw [Finset.sum_comm]
    _ = ∑ _P : RatFuncRationalFinitePlace C,
          Nat.card (N ≃ₐ[RatFunc C] N) := by
      apply Finset.sum_congr rfl
      intro P _
      simpa only [FrobeniusTwistFinitePlaceFiberFixedBy] using
        (sum_card_finitePlaceUnderFiber_fixedBy_frobeniusTwist_eq_card_galois
          C S N hExact hDegreeDiv P)
    _ = Nat.card (RatFuncRationalFinitePlace C) *
          Nat.card (N ≃ₐ[RatFunc C] N) := by
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card C * Nat.card (N ≃ₐ[RatFunc C] N) := by
      rw [Nat.card_congr (ratFuncRationalFinitePlaceEquiv C)]
    _ = Nat.card (N ≃ₐ[RatFunc C] N) * Nat.card C := Nat.mul_comm _ _

end

end BGS.HasseWeil
