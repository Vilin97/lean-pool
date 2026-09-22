/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFiniteDifferent
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionInfinityDifferent
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionInfinityPlaceCompatibility
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionGenusInvariance
import LeanPool.MarkoffModP.BGS.HasseWeil.IdealMultiplicityMap

/-!
# Local different coefficients under exact constant extension

The finite and reciprocal-infinity different ideals commute with exact
extension of finite constants.  Since every place in a constant extension
has ramification index one, their multiplicities agree place by place.  This
discharges the local hypothesis of the global different-degree and genus
transport theorems.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

private theorem normalization_map_injective
    {R B N E : Type*} [CommRing R] [CommRing B] [Field N] [Field E]
    [Algebra R B] [Algebra N E]
    (i : R → N) (j : B → E) (hi : Function.Injective i)
    (hcompat : ∀ x, j (algebraMap R B x) = algebraMap N E (i x)) :
    Function.Injective (algebraMap R B) := by
  intro x y hxy
  apply hi
  apply (algebraMap N E).injective
  exact (hcompat x).symm.trans ((congrArg j hxy).trans (hcompat y))


private theorem comap_liesOver_of_commutes
    {A R B C : Type*} [CommRing A] [CommRing R] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra R B]
    (e : C →+* B) (f : A →+* R)
    (hcomp : e.comp (algebraMap A C) = (algebraMap R B).comp f)
    (p : Ideal A) (r : Ideal R) (q : Ideal B) [q.LiesOver r]
    (hbase : r.comap f = p) : (q.comap e).LiesOver p := by
  constructor
  change p = Ideal.comap (algebraMap A C) (q.comap e)
  rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
  change p = Ideal.comap f (q.under R)
  rw [← (inferInstance : q.LiesOver r).over, hbase]


noncomputable section

open BGS.CorvajaZannier IsDedekindDomain


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000)
    exactConstantDifferentCoefficientConstantsDecidableEq
    (K : Type*) [Field K] : DecidableEq K :=
  infinityBridgeDecidableEqConstants K

local instance (priority := 10001)
    exactConstantDifferentCoefficientRatFuncDecidableEq
    (K : Type*) [Field K] : DecidableEq (RatFunc K) :=
  infinityBridgeDecidableEqRatFuncConstants K

local instance exactConstantDifferentCoefficientBaseConstantAlgebra :
    Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance exactConstantDifferentCoefficientBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10)
    exactConstantDifferentCoefficientBasePolynomialAlgebra : Algebra C[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C[X] (RatFunc C)))

local instance exactConstantDifferentCoefficientBasePolynomialTower :
    IsScalarTower C[X] (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance exactConstantDifferentCoefficientBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance exactConstantDifferentCoefficientTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  constantExtensionTensorPolynomialAlgebra C S N

@[reducible] private noncomputable def
    exactConstantDifferentCoefficientCanonicalFractionRingAlgebra
    (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (FractionRing R) := inferInstance

private theorem exactConstantDifferentCoefficientCanonicalFractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    letI := exactConstantDifferentCoefficientCanonicalFractionRingAlgebra R
    IsFractionRing R (FractionRing R) := by
  let := exactConstantDifferentCoefficientCanonicalFractionRingAlgebra R
  infer_instance

private theorem integralClosureAlgEquivRatFuncFiniteOfEq_coe
    {k T : Type*} [Field k] [Field T] [Algebra (RatFunc k) T]
    (a : Algebra k[X] T)
    (h : ratFuncInducedPolynomialAlgebra k T = a)
    (x : letI := a; integralClosure k[X] T) :
    letI := a
    (((integralClosureAlgEquivRatFuncFiniteOfEq k T a h) x :
        RatFuncFiniteIntegralClosure k T) : T) = x := by
  subst a
  rfl

/-- Changing only the presentation of a finite normalization does not change
the multiplicity of its different.  The equivalence here is the equality
transport from a chosen compatible polynomial action to the action induced
by the fixed rational-function-field embedding. -/
private def idealMapMulEquiv {R T : Type*} [CommSemiring R] [CommSemiring T]
    (e : R ≃+* T) : Ideal R ≃* Ideal T where
  toFun I := I.map e
  invFun I := I.map e.symm
  left_inv I := Ideal.map_of_equiv e
  right_inv I := Ideal.map_of_equiv e.symm
  map_mul' I J := Ideal.map_mul e I J

private theorem finiteNormalization_multiplicity_map_eq
    {k T : Type*} [Field k] [Field T] [Algebra (RatFunc k) T]
    (a : Algebra k[X] T)
    (h : ratFuncInducedPolynomialAlgebra k T = a)
    (q : letI := a
      IsDedekindDomain.HeightOneSpectrum (integralClosure k[X] T))
    (I : letI := a; Ideal (integralClosure k[X] T)) :
    letI := a
    let e := integralClosureAlgEquivRatFuncFiniteOfEq k T a h
    multiplicity (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal
          (Ideal.map e I) =
      multiplicity q.asIdeal I := by
  dsimp only
  rw [heightOneSpectrumEquivOfAlgEquiv_asIdeal]
  let e := integralClosureAlgEquivRatFuncFiniteOfEq k T a h
  rw [show Ideal.comap e.symm q.asIdeal = Ideal.map e q.asIdeal by
    exact (Ideal.map_comap_of_equiv e.toRingEquiv).symm]
  exact multiplicity_map_eq
    (idealMapMulEquiv e.toRingEquiv)

private theorem finiteNormalization_differentIdeal_eq_map
    {k T : Type*} [Field k] [Finite k] [Field T]
    [Algebra (RatFunc k) T] [FiniteDimensional (RatFunc k) T]
    [Algebra.IsSeparable (RatFunc k) T]
    (a : Algebra k[X] T)
    (h : ratFuncInducedPolynomialAlgebra k T = a)
    (hDedekind : letI := a
      IsDedekindDomain (integralClosure k[X] T))
    (hTorsionFree : letI := a
      Module.IsTorsionFree k[X] (integralClosure k[X] T)) :
    letI := a
    letI : IsDedekindDomain (integralClosure k[X] T) := hDedekind
    letI : Module.IsTorsionFree k[X] (integralClosure k[X] T) :=
      hTorsionFree
    let e := integralClosureAlgEquivRatFuncFiniteOfEq k T a h
    differentIdeal k[X] (RatFuncFiniteIntegralClosure k T) =
      Ideal.map e (differentIdeal k[X] (integralClosure k[X] T)) := by
  subst a
  dsimp only
  change differentIdeal k[X] (RatFuncFiniteIntegralClosure k T) =
    Ideal.map (AlgEquiv.refl :
      RatFuncFiniteIntegralClosure k T ≃ₐ[k[X]]
        RatFuncFiniteIntegralClosure k T)
      (differentIdeal k[X] (RatFuncFiniteIntegralClosure k T))
  exact (Ideal.map_id _).symm

/-- Ramification indices are unchanged by an equivalence of the upper
Dedekind domains that is linear over the lower Dedekind domain. -/
private theorem ramificationIdx_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [IsDomain R] [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra R A] [Algebra R B]
    [Module.IsTorsionFree R A] [Module.IsTorsionFree R B]
    (e : A ≃ₐ[R] B) (p : HeightOneSpectrum R)
    (q : HeightOneSpectrum A)
    [q.asIdeal.LiesOver p.asIdeal]
    [(heightOneSpectrumEquivOfAlgEquiv e q).asIdeal.LiesOver p.asIdeal] :
    (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal.ramificationIdx R =
      q.asIdeal.ramificationIdx R := by
  let q' := heightOneSpectrumEquivOfAlgEquiv e q
  have hIdeal : q'.asIdeal = Ideal.map e.toRingHom q.asIdeal := by
    dsimp only [q']
    rw [heightOneSpectrumEquivOfAlgEquiv_asIdeal]
    exact (Ideal.map_comap_of_equiv e.toRingEquiv).symm
  calc
    q'.asIdeal.ramificationIdx R =
        p.asIdeal.ramificationIdx' q'.asIdeal :=
      (Ideal.ramificationIdx'_eq_ramificationIdx
        p.asIdeal q'.asIdeal p.ne_bot).symm
    _ = p.asIdeal.ramificationIdx' q.asIdeal := by
      rw [hIdeal]
      exact Ideal.ramificationIdx'_map_eq p.asIdeal q.asIdeal e
    _ = q.asIdeal.ramificationIdx R :=
      Ideal.ramificationIdx'_eq_ramificationIdx
        p.asIdeal q.asIdeal p.ne_bot

/-- A prime in the explicit `S[X]`-normalization is unramified over its
contracted prime in the original `C[X]`-normalization.  The proof transports
the prime to the canonical `C[X]`-normalization used by the place tower and
then invokes unramifiedness of exact constant extensions. -/
theorem exactConstantExtensionPresentedFinitePlace_ramificationIdx_eq_one
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    let R2 := RatFuncFiniteIntegralClosure C N
    let B := integralClosure S[X] E
    letI : Algebra R2 B :=
      exactConstantExtensionFiniteNormalizationAlgebra C S N
    q.asIdeal.ramificationIdx R2 = 1 := by
  dsimp only
  let E := ExactConstantExtension C N S
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) E := Algebra.toSMul
  let : Module (RatFunc C) E := Algebra.toModule
  let : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : Algebra S[X] E :=
    constantExtensionTensorPolynomialAlgebra C S N
  let : SMul S[X] E := Algebra.toSMul
  let : Module S[X] E := Algebra.toModule
  let : Algebra S[X] (RatFunc S) := inferInstance
  let : IsFractionRing S[X] (RatFunc S) := inferInstance
  let : IsScalarTower S[X] (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] E p =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) p)
      exact
        (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  let R2 := RatFuncFiniteIntegralClosure C N
  let B := integralClosure S[X] E
  let CC := RatFuncFiniteIntegralClosure C E
  let CS := RatFuncFiniteIntegralClosure S E
  let : Algebra C[X] (RatFunc C) := inferInstance
  let : IsFractionRing C[X] (RatFunc C) := inferInstance
  let : IsScalarTower C[X] (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C C[X] N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsDedekindDomain R2 :=
    IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) N R2
  let : Module.IsTorsionFree C[X] N := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      ((algebraMap (RatFunc C) N).comp (algebraMap C[X] (RatFunc C)))
    exact (algebraMap (RatFunc C) N).injective.comp
      (RatFunc.algebraMap_injective C)
  let : Module.IsTorsionFree C[X] R2 :=
    IsIntegralClosure.isTorsionFree C[X] N
  let : Algebra C R2 :=
    RingHom.toAlgebra
      ((algebraMap C[X] R2).comp (algebraMap C C[X]))
  let : SMul C R2 := Algebra.toSMul
  let : Module C R2 := Algebra.toModule
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) E B
  let : Algebra R2 B :=
    exactConstantExtensionFiniteNormalizationAlgebra C S N
  let : SMul R2 B := Algebra.toSMul
  let : Module R2 B := Algebra.toModule
  let : Algebra N E := exactConstantExtensionAlgebra C N S
  let : SMul N E := Algebra.toSMul
  let : Module N E := Algebra.toModule
  let : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra C[X] E :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) E).comp (algebraMap C[X] (RatFunc C)))
  let : SMul C[X] E := Algebra.toSMul
  let : Module C[X] E := Algebra.toModule
  let : IsScalarTower C[X] (RatFunc C) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C[X] S[X] := Polynomial.algebra C S
  let : IsScalarTower C[X] S[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap (RatFunc C) E
          (algebraMap C[X] (RatFunc C) p) =
        algebraMap S[X] E (algebraMap C[X] S[X] p)
      rw [IsScalarTower.algebraMap_apply S[X] (RatFunc S) E]
      rw [rationalBase_algebraMap_eq C S N hExact]
      apply congrArg (algebraMap (RatFunc S) E)
      exact ratFuncCoefficientAlgHom_algebraMap C S p)
  let : Algebra R2 CC := (finiteIntegralClosureMap C N E).toAlgebra
  let : SMul R2 CC := Algebra.toSMul
  let : Module R2 CC := Algebra.toModule
  let : IsDedekindDomain CC :=
    IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) E CC
  let : Algebra S CC :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  let : Algebra S CS :=
    RingHom.toAlgebra
      ((algebraMap S[X] CS).comp (algebraMap S S[X]))
  let eS := integralClosureAlgEquivRatFuncFiniteOfAlgebraMap
    S E (constantExtensionTensorPolynomialAlgebra C S N)
      (ratFuncToExactConstantExtension_algebraMap C S N hExact)
  let eBase := exactConstantExtensionFiniteClosureBaseChangeAlgEquiv
    C S N hExact
  let eRing : B ≃+* CC := eS.toRingEquiv.trans eBase.toRingEquiv.symm
  let e : B ≃ₐ[R2] CC :=
    { eRing with
      commutes' := fun x => by
        apply Subtype.ext
        have heBaseCoe (y : CC) :
            ((eBase y : CS) : E) = y := by
          exact integralClosureRingEquivOfIntegralTower_coe C[X] S[X] E y
        have heBaseSymmCoe (z : CS) :
            ((eBase.symm z : CC) : E) = z := by
          calc
            ((eBase.symm z : CC) : E) =
                ((eBase (eBase.symm z) : CS) : E) :=
              (heBaseCoe (eBase.symm z)).symm
            _ = (z : E) := congrArg Subtype.val (eBase.apply_symm_apply z)
        calc
          ((eRing ((algebraMap R2 B) x) : CC) : E) =
              ((eS ((algebraMap R2 B) x) : CS) : E) :=
            heBaseSymmCoe (eS ((algebraMap R2 B) x))
          _ = (((algebraMap R2 B) x : B) : E) :=
            integralClosureAlgEquivRatFuncFiniteOfEq_coe
              (constantExtensionTensorPolynomialAlgebra C S N)
              (ratFuncInducedPolynomialAlgebra_eq S E
                (constantExtensionTensorPolynomialAlgebra C S N)
                (ratFuncToExactConstantExtension_algebraMap C S N hExact))
              ((algebraMap R2 B) x)
          _ = (((algebraMap R2 CC) x : CC) : E) := by
            change
              (((finiteFieldConstantExtensionIntegralClosureRingEquiv C S N)
                (1 ⊗ₜ[C] x) : B) : E) =
                algebraMap N E (x : N)
            exact finiteFieldConstantExtensionIntegralClosureRingEquiv_tmul
              C S N 1 x }
  have hTargetInjective : Function.Injective (algebraMap R2 CC) := by
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap N E).injective
    exact congrArg Subtype.val hxy
  let : Module.IsTorsionFree R2 CC := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hTargetInjective
  let : Module.IsTorsionFree R2 B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply hTargetInjective
    rw [← e.commutes x, ← e.commutes y, hxy]
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let Q := exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q
  have hQ : heightOneSpectrumEquivOfAlgEquiv e q = Q := by
    apply (HeightOneSpectrum.equivOfRingEquiv eBase.toRingEquiv).injective
    calc
      HeightOneSpectrum.equivOfRingEquiv eBase.toRingEquiv
          (heightOneSpectrumEquivOfAlgEquiv e q) =
          heightOneSpectrumEquivOfAlgEquiv eS q := by
            rfl
      _ = exactConstantExtensionUpstairsFinitePlace C S N hExact q := by
        exact
          (exactConstantExtensionUpstairsFinitePlace_eq_compatibleNormalizationTransport
            C S N hExact q).symm
      _ = HeightOneSpectrum.equivOfRingEquiv eBase.toRingEquiv Q := by
        exact
          (exactConstantExtensionCompatibleBaseFinitePlace_baseChange
            C S N hExact q).symm
  let q' := heightOneSpectrumEquivOfAlgEquiv e q
  let : q.asIdeal.LiesOver P.asIdeal := ⟨by
    change P.asIdeal = q.asIdeal.comap (algebraMap R2 B)
    rfl⟩
  let : q'.asIdeal.LiesOver P.asIdeal := ⟨by
    change P.asIdeal = q'.asIdeal.comap (algebraMap R2 CC)
    rw [show q' = Q by exact hQ]
    exact congrArg HeightOneSpectrum.asIdeal
      (exactConstantExtensionCompatibleBaseFinitePlace_under_original
        C S N hExact q).symm⟩
  calc
    q.asIdeal.ramificationIdx R2 =
        (heightOneSpectrumEquivOfAlgEquiv e q).asIdeal.ramificationIdx R2 :=
      (ramificationIdx_algEquiv e P q).symm
    _ = Q.asIdeal.ramificationIdx R2 := by rw [hQ]
    _ = 1 := by
      exact exactConstantExtensionFinitePlace_ramificationIdx_eq_one
        C S N hExact Q

/-- Every prime in the explicit extended infinity normalization is unramified
over the original infinity normalization. -/
theorem exactConstantExtensionPresentedInfinityPlace_ramificationIdx_eq_one
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let R2 := RatFuncInfinityIntegralClosure C N
    let B := RatFuncInfinityIntegralClosure S E
    letI : Algebra R2 B :=
      exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
    (exactConstantExtensionUpstairsInfinityPlace
      C S N hExact q.1 q.2).1.ramificationIdx R2 = 1 := by
  dsimp only
  let E := ExactConstantExtension C N S
  let A := RatFuncInfinityIntegers C
  let R1 := RatFuncInfinityIntegers S
  let R2 := RatFuncInfinityIntegralClosure C N
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) E := Algebra.toSMul
  let : Module (RatFunc C) E := Algebra.toModule
  let : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra N E := exactConstantExtensionAlgebra C N S
  let : SMul N E := Algebra.toSMul
  let : Module N E := Algebra.toModule
  let : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : DistribMulAction (RatFunc S) E := Module.toDistribMulAction
  let : MulAction (RatFunc S) E := DistribMulAction.toMulAction
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  let B := RatFuncInfinityIntegralClosure S E
  let CC := RatFuncInfinityIntegralClosure C E
  let : Algebra A (RatFunc C) := Algebra.ofSubsemiring A
  let : SMul A (RatFunc C) := Algebra.toSMul
  let : Module A (RatFunc C) := Algebra.toModule
  let : Algebra R1 (RatFunc S) := Algebra.ofSubsemiring R1
  let : SMul R1 (RatFunc S) := Algebra.toSMul
  let : Module R1 (RatFunc S) := Algebra.toModule
  let : IsFractionRing A (RatFunc C) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv C)
  let : IsFractionRing R1 (RatFunc S) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv S)
  let : Algebra A N := Algebra.ofSubsemiring A
  let : SMul A N := Algebra.toSMul
  let : Module A N := Algebra.toModule
  let : IsScalarTower A (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A E := Algebra.ofSubsemiring A
  let : SMul A E := Algebra.toSMul
  let : Module A E := Algebra.toModule
  let : Module.IsTorsionFree A E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (RatFunc C) E).injective.comp
      (IsFractionRing.injective A (RatFunc C))
  let : IsScalarTower A (RatFunc C) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R1 E := Algebra.ofSubsemiring R1
  let : SMul R1 E := Algebra.toSMul
  let : Module R1 E := Algebra.toModule
  let : Algebra A R1 :=
    RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  let : SMul A R1 := Algebra.toSMul
  let : Module A R1 := Algebra.toModule
  let : Module.Finite A R1 :=
    ratFuncInfinityIntegers_coefficient_moduleFinite C S
  let : Algebra.IsIntegral A R1 := by infer_instance
  let : IsScalarTower A R1 E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change algebraMap (RatFunc C) E z.1 =
        algebraMap (RatFunc S) E (ratFuncCoefficientAlgHom C S z.1)
      exact DFunLike.congr_fun
        (rationalBase_algebraMap_eq C S N hExact) z.1)
  let : IsDedekindDomain R2 :=
    integralClosure.isDedekindDomain A (RatFunc C) N
  let : IsDedekindDomain B :=
    integralClosure.isDedekindDomain R1 (RatFunc S) E
  let : IsDedekindDomain CC :=
    integralClosure.isDedekindDomain A (RatFunc C) E
  let : Algebra A R2 := inferInstance
  let : SMul A R2 := Algebra.toSMul
  let : Module A R2 := Algebra.toModule
  let : Module.IsTorsionFree A R2 :=
    IsIntegralClosure.isTorsionFree A N
  let : Algebra A CC := inferInstance
  let : SMul A CC := Algebra.toSMul
  let : Module A CC := Algebra.toModule
  let : Module.IsTorsionFree A CC :=
    IsIntegralClosure.isTorsionFree A E
  let : Module.IsTorsionFree R1 E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (RatFunc S) E).injective.comp
      (IsFractionRing.injective R1 (RatFunc S))
  let : Module.IsTorsionFree R1 B :=
    IsIntegralClosure.isTorsionFree R1 E
  let : Algebra R2 B :=
    exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
  let : SMul R2 B := Algebra.toSMul
  let : Module R2 B := Algebra.toModule
  let : Algebra R2 CC := (infinityIntegralClosureMap C N E).toAlgebra
  let : SMul R2 CC := Algebra.toSMul
  let : Module R2 CC := Algebra.toModule
  let : IsScalarTower A R2 CC :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      rfl)
  let eRing : CC ≃+* B :=
    integralClosureRingEquivOfIntegralTower A R1 E
  let e : CC ≃ₐ[R2] B :=
    { eRing with
      commutes' := fun x => by
        apply Subtype.ext
        calc
          ((eRing ((algebraMap R2 CC) x) : B) : E) =
              ((algebraMap R2 CC) x : CC) :=
            integralClosureRingEquivOfIntegralTower_coe A R1 E _
          _ = algebraMap N E (x : N) := rfl
          _ = ((algebraMap R2 B) x : B) :=
            (exactConstantExtensionInfinityNormalizationAlgebra_coe
              C S N hExact x).symm }
  have hTargetInjective : Function.Injective (algebraMap R2 CC) :=
    normalization_map_injective Subtype.val Subtype.val Subtype.val_injective (fun _ => rfl)
  let : Module.IsTorsionFree R2 CC :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 hTargetInjective
  let : Module.IsTorsionFree R2 B :=
    Function.Injective.moduleIsTorsionFree e.symm e.symm.injective (map_smul e.symm.toLinearEquiv)
  let w := exactConstantExtensionUpstairsInfinityPlace C S N hExact q.1 q.2
  let QI : Ideal CC := Ideal.comap eRing.toRingHom w.1
  have hQIPrime : QI.IsPrime := Ideal.comap_isPrime (f := eRing.toRingHom) (K := w.1)
  have heMap : eRing.toRingHom.comp (algebraMap A CC) =
      (algebraMap R1 B).comp (ratFuncInfinityIntegersRingHom C S) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    calc
      ((eRing (algebraMap A CC x) : B) : E) =
          ((algebraMap A CC x : CC) : E) :=
        integralClosureRingEquivOfIntegralTower_coe A R1 E _
      _ = algebraMap (RatFunc C) E x.1 := rfl
      _ = algebraMap (RatFunc S) E
            (ratFuncCoefficientAlgHom C S x.1) :=
        DFunLike.congr_fun
          (rationalBase_algebraMap_eq C S N hExact) x.1
      _ = ((algebraMap R1 B
            (ratFuncInfinityIntegersRingHom C S x) : B) : E) := rfl
  have hQIOver : QI.LiesOver (ratFuncInfinityPlace C).asIdeal :=
    comap_liesOver_of_commutes eRing.toRingHom
      (ratFuncInfinityIntegersRingHom C S) heMap
      (ratFuncInfinityPlace C).asIdeal (ratFuncInfinityPlace S).asIdeal w.1
      (ratFuncInfinityIntegersRingHom_comap_infinityPlace C S)
  let Q : FiniteExtensionInfinityPlace C E :=
    ⟨QI, hQIPrime, hQIOver⟩
  let qH := primeOverHeightOne (ratFuncInfinityPlace C) Q
  let wH := primeOverHeightOne (ratFuncInfinityPlace S) w
  have hCompat : heightOneSpectrumEquivOfAlgEquiv e qH = wH := by
    apply HeightOneSpectrum.ext
    rw [heightOneSpectrumEquivOfAlgEquiv_asIdeal]
    dsimp only [qH, wH, primeOverHeightOne, Q, QI]
    exact Ideal.comap_of_equiv eRing.symm
  let P := infinityPlaceUnder C N E Q
  let pH := primeOverHeightOne (ratFuncInfinityPlace C) P
  let : qH.asIdeal.LiesOver pH.asIdeal := ⟨by
    dsimp only [qH, pH, primeOverHeightOne]
    change P.1 = Q.1.comap (algebraMap R2 CC)
    exact infinityPlaceUnder_asIdeal C N E Q⟩
  let : (heightOneSpectrumEquivOfAlgEquiv e qH).asIdeal.LiesOver
      pH.asIdeal := ⟨by
    rw [hCompat]
    dsimp only [wH, pH, primeOverHeightOne]
    change P.1 = w.1.comap (algebraMap R2 B)
    rw [show P.1 = Q.1.comap (algebraMap R2 CC) by
      exact infinityPlaceUnder_asIdeal C N E Q]
    ext x
    change eRing (algebraMap R2 CC x) ∈ w.1 ↔
      algebraMap R2 B x ∈ w.1
    have he := e.commutes x
    change eRing (algebraMap R2 CC x) = algebraMap R2 B x at he
    rw [he]⟩
  change w.1.ramificationIdx R2 = 1
  calc
    w.1.ramificationIdx R2 =
        (heightOneSpectrumEquivOfAlgEquiv e qH).asIdeal.ramificationIdx R2 := by
      rw [hCompat]
      rfl
    _ = qH.asIdeal.ramificationIdx R2 :=
      ramificationIdx_algEquiv e pH qH
    _ = 1 := by
      exact exactConstantExtensionInfinityPlace_ramificationIdx_eq_one
        C S N hExact Q

private theorem different_ne_bot_of_fraction_fields
    (A B K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDedekindDomain B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [Algebra A B] [IsScalarTower A B L]
    [Module.Finite A B] [Module.IsTorsionFree A B] : differentIdeal A B ≠ ⊥ := by
  let : Algebra A (FractionRing A) := exactConstantDifferentCoefficientCanonicalFractionRingAlgebra A
  let : SMul A (FractionRing A) := Algebra.toSMul
  let : IsFractionRing A (FractionRing A) := exactConstantDifferentCoefficientCanonicalFractionRing A
  let : Algebra B (FractionRing B) := exactConstantDifferentCoefficientCanonicalFractionRingAlgebra B
  let : SMul B (FractionRing B) := Algebra.toSMul
  let : IsFractionRing B (FractionRing B) := exactConstantDifferentCoefficientCanonicalFractionRing B
  let : Algebra A (FractionRing B) :=
    RingHom.toAlgebra ((algebraMap B (FractionRing B)).comp (algebraMap A B))
  let : SMul A (FractionRing B) := Algebra.toSMul
  let : IsScalarTower A B (FractionRing B) := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul A (FractionRing B) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    change Function.Injective
      ((algebraMap B (FractionRing B)).comp (algebraMap A B))
    exact (IsFractionRing.injective B (FractionRing B)).comp
      (FaithfulSMul.algebraMap_injective A B)
  let : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  let : SMul (FractionRing A) (FractionRing B) := Algebra.toSMul
  let : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv ?_
    ext z
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A K).symm (FractionRing.algEquiv B L).symm z
  exact differentIdeal_ne_bot


private theorem exactConstantExtension_presented_totalDifferentMultiplicity_eq_finite
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    let E := ExactConstantExtension C N S
    let : Field E := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : SMul (RatFunc C) E := Algebra.toSMul
    let : Module (RatFunc C) E := Algebra.toModule
    let : FiniteDimensional (RatFunc C) E :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    let : Algebra.IsSeparable (RatFunc C) E :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) E := Algebra.toSMul
    let : Module (RatFunc S) E := Algebra.toModule
    let : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    let : SMul S[X] E := Algebra.toSMul
    let : Module S[X] E := Algebra.toModule
    let : IsScalarTower S[X] (RatFunc S) E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] E p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    let : FiniteDimensional (RatFunc S) E :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) E :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionTotalDifferentEffectiveDivisor S E
        (exactConstantExtensionPresentedUpstairsPlaceEquiv
          C S N hExact (.inl q)) =
      finiteExtensionTotalDifferentEffectiveDivisor C N
        (exactConstantExtensionPresentedDownstairsPlace
          C S N hExact (.inl q)) := by
  intro E model1 model2 model3 model4 model5 model6 model7 model8 model9
    model10 model11 model12 model13 model14 model15
  let : Algebra S[X] (RatFunc S) :=
    inferInstance
  let : IsFractionRing S[X] (RatFunc S) :=
    inferInstance
  let : Module.IsTorsionFree S[X] E :=
    Module.IsTorsionFree.trans_faithfulSMul S[X] (RatFunc S) E
  let : IsDedekindDomain (integralClosure S[X] E) :=
    IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) E
      (integralClosure S[X] E)
  let : Module.IsTorsionFree S[X] (integralClosure S[X] E) :=
    IsIntegralClosure.isTorsionFree S[X] E
  let R2 := RatFuncFiniteIntegralClosure C N
  let B := integralClosure S[X] E
  let : Algebra C[X] (RatFunc C) := inferInstance
  let : IsFractionRing C[X] (RatFunc C) := inferInstance
  let : IsScalarTower C[X] (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsDedekindDomain R2 :=
    IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) N R2
  let : Module.IsTorsionFree C[X] N := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      ((algebraMap (RatFunc C) N).comp
        (algebraMap C[X] (RatFunc C)))
    exact (algebraMap (RatFunc C) N).injective.comp
      (RatFunc.algebraMap_injective C)
  let : Module.IsTorsionFree C[X] R2 :=
    IsIntegralClosure.isTorsionFree C[X] N
  let : Algebra R2 B :=
    exactConstantExtensionFiniteNormalizationAlgebra C S N
  let : SMul R2 B := Algebra.toSMul
  let : Module R2 B := Algebra.toModule
  let : SMul C R2 := Algebra.toSMul
  let : Module C R2 := Algebra.toModule
  let : Module.Free C R2 := Module.Free.of_divisionRing C R2
  let : Module.Flat C R2 := Module.Flat.of_free
  let eNorm : S ⊗[C] R2 ≃+* B :=
    finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
  let : Module.IsTorsionFree R2 B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      (eNorm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R2)).toRingHom)
    exact eNorm.injective.comp
      (Algebra.TensorProduct.includeRight_injective
        (R := C) (A := S) (B := R2) (algebraMap C S).injective)
  let a : Algebra S[X] E :=
    constantExtensionTensorPolynomialAlgebra C S N
  have hAlgebra : ratFuncInducedPolynomialAlgebra S E = a :=
    ratFuncInducedPolynomialAlgebra_eq S E a
      (ratFuncToExactConstantExtension_algebraMap C S N hExact)
  let e := integralClosureAlgEquivRatFuncFiniteOfEq
    S E a hAlgebra
  have hDifferent :
      differentIdeal S[X] (RatFuncFiniteIntegralClosure S E) =
        Ideal.map e
          (differentIdeal S[X] (integralClosure S[X] E)) :=
    finiteNormalization_differentIdeal_eq_map
      a hAlgebra inferInstance inferInstance
  have hUpstairs :
      exactConstantExtensionUpstairsFinitePlace C S N hExact q =
        heightOneSpectrumEquivOfAlgEquiv e q := by
    simpa [e, a, hAlgebra,
      integralClosureAlgEquivRatFuncFiniteOfAlgebraMap] using
        (exactConstantExtensionUpstairsFinitePlace_eq_compatibleNormalizationTransport
          C S N hExact q)
  rw [exactConstantExtensionPresentedUpstairsPlaceEquiv_apply]
  simp only [exactConstantExtensionPresentedUpstairsPlace,
    exactConstantExtensionPresentedDownstairsPlace,
    finiteExtensionTotalDifferentEffectiveDivisor_inl]
  rw [hUpstairs, hDifferent]
  rw [finiteNormalization_multiplicity_map_eq
    a hAlgebra q
      (differentIdeal S[X] (integralClosure S[X] E))]
  rw [exactConstantExtension_finiteDifferent_eq_map C S N hExact]
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let : q.asIdeal.LiesOver P.asIdeal := ⟨by
    change P.asIdeal = q.asIdeal.comap (algebraMap R2 B)
    rfl⟩
  have hDifferentBase :
      differentIdeal C[X] R2 ≠ ⊥ :=
    finiteExtensionFiniteDifferentIdeal_ne_bot C N
  calc
    multiplicity q.asIdeal
        (Ideal.map (algebraMap R2 B)
          (differentIdeal C[X] R2)) =
        q.asIdeal.ramificationIdx R2 *
          multiplicity P.asIdeal (differentIdeal C[X] R2) :=
      multiplicity_map_eq_ramificationIdx_mul
        (R := R2) (S := B) P q
          (differentIdeal C[X] R2) hDifferentBase
    _ = multiplicity P.asIdeal (differentIdeal C[X] R2) := by
      have hRam : q.asIdeal.ramificationIdx R2 = 1 := by
        exact exactConstantExtensionPresentedFinitePlace_ramificationIdx_eq_one
          C S N hExact q
      rw [hRam]
      simpa only [one_mul]


private theorem exactConstantExtension_presented_totalDifferentMultiplicity_eq_infinity
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    let E := ExactConstantExtension C N S
    let : Field E := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : SMul (RatFunc C) E := Algebra.toSMul
    let : Module (RatFunc C) E := Algebra.toModule
    let : FiniteDimensional (RatFunc C) E :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    let : Algebra.IsSeparable (RatFunc C) E :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) E := Algebra.toSMul
    let : Module (RatFunc S) E := Algebra.toModule
    let : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    let : SMul S[X] E := Algebra.toSMul
    let : Module S[X] E := Algebra.toModule
    let : IsScalarTower S[X] (RatFunc S) E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] E p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    let : FiniteDimensional (RatFunc S) E :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) E :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionTotalDifferentEffectiveDivisor S E
        (exactConstantExtensionPresentedUpstairsPlaceEquiv
          C S N hExact (.inr q)) =
      finiteExtensionTotalDifferentEffectiveDivisor C N
        (exactConstantExtensionPresentedDownstairsPlace
          C S N hExact (.inr q)) := by
  intro E model1 model2 model3 model4 model5 model6 model7 model8 model9
    model10 model11 model12 model13 model14 model15
  rw [exactConstantExtensionPresentedUpstairsPlaceEquiv_apply]
  simp only [exactConstantExtensionPresentedUpstairsPlace,
    exactConstantExtensionPresentedDownstairsPlace,
    finiteExtensionTotalDifferentEffectiveDivisor_inr]
  let A := RatFuncInfinityIntegers C
  let R1 := RatFuncInfinityIntegers S
  let R2 := RatFuncInfinityIntegralClosure C N
  let B := RatFuncInfinityIntegralClosure S E
  let : Algebra N E := exactConstantExtensionAlgebra C N S
  let : SMul N E := Algebra.toSMul
  let : Module N E := Algebra.toModule
  let : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra A (RatFunc C) := Algebra.ofSubsemiring A
  let : SMul A (RatFunc C) := Algebra.toSMul
  let : Module A (RatFunc C) := Algebra.toModule
  let : IsFractionRing A (RatFunc C) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv C)
  let : Algebra R1 (RatFunc S) := Algebra.ofSubsemiring R1
  let : SMul R1 (RatFunc S) := Algebra.toSMul
  let : Module R1 (RatFunc S) := Algebra.toModule
  let : IsFractionRing R1 (RatFunc S) :=
    IsFractionRing.of_algEquiv (ratFuncInfinityFractionRingEquiv S)
  let : Algebra A N := Algebra.ofSubsemiring A
  let : SMul A N := Algebra.toSMul
  let : Module A N := Algebra.toModule
  let : IsScalarTower A (RatFunc C) N :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R1 E := Algebra.ofSubsemiring R1
  let : SMul R1 E := Algebra.toSMul
  let : Module R1 E := Algebra.toModule
  let : IsScalarTower R1 (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A R1 :=
    RingHom.toAlgebra (ratFuncInfinityIntegersRingHom C S)
  let : SMul A R1 := Algebra.toSMul
  let : Module A R1 := Algebra.toModule
  let : IsDedekindDomain R2 :=
    integralClosure.isDedekindDomain A (RatFunc C) N
  let : IsDedekindDomain B :=
    integralClosure.isDedekindDomain R1 (RatFunc S) E
  let : Algebra A R2 := inferInstance
  let : SMul A R2 := Algebra.toSMul
  let : Module A R2 := Algebra.toModule
  let : Algebra R2 N := Algebra.ofSubsemiring R2
  let : SMul R2 N := Algebra.toSMul
  let : Module R2 N := Algebra.toModule
  let : IsScalarTower A R2 N :=
    IsScalarTower.of_algebraMap_eq' (by ext z; rfl)
  let : IsIntegralClosure R2 A N :=
    integralClosure.isIntegralClosure A N
  let : Module.Finite A R2 :=
    IsIntegralClosure.finite A (RatFunc C) N R2
  let : Module.IsTorsionFree A R2 :=
    IsIntegralClosure.isTorsionFree A N
  let : Module.IsTorsionFree R1 E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (RatFunc S) E).injective.comp
      (IsFractionRing.injective R1 (RatFunc S))
  let : Module.IsTorsionFree R1 B :=
    IsIntegralClosure.isTorsionFree R1 E
  let : Algebra R2 B :=
    exactConstantExtensionInfinityNormalizationAlgebra C S N hExact
  let : SMul R2 B := Algebra.toSMul
  let : Module R2 B := Algebra.toModule
  let : Module.IsTorsionFree R2 B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact normalization_map_injective Subtype.val Subtype.val
      Subtype.val_injective
      (exactConstantExtensionInfinityNormalizationAlgebra_coe C S N hExact)
  let : IsFractionRing R2 N :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      A (RatFunc C) N R2
  rw [exactConstantExtension_infinityDifferent_eq_map C S N hExact]
  let w := exactConstantExtensionUpstairsInfinityPlace
    C S N hExact q.1 q.2
  let wH := primeOverHeightOne (ratFuncInfinityPlace S) w
  let P := exactConstantExtensionDownstairsInfinityPlace C S N q.1 q.2
  let pH := primeOverHeightOne (ratFuncInfinityPlace C) P
  let : wH.asIdeal.LiesOver pH.asIdeal := ⟨by
    change P.1 = w.1.comap (algebraMap R2 B)
    exact (exactConstantExtensionUpstairsInfinityPlace_under
      C S N hExact q).symm⟩
  have hDifferentBase :
      differentIdeal (RatFuncInfinityIntegers C) R2 ≠ ⊥ :=
    different_ne_bot_of_fraction_fields A R2 (RatFunc C) N
  calc
    multiplicity w.1
        (Ideal.map (algebraMap R2 B)
          (differentIdeal (RatFuncInfinityIntegers C) R2)) =
        w.1.ramificationIdx R2 *
          multiplicity pH.asIdeal
            (differentIdeal (RatFuncInfinityIntegers C) R2) := by
      exact multiplicity_map_eq_ramificationIdx_mul
        (R := R2) (S := B) pH wH
          (differentIdeal (RatFuncInfinityIntegers C) R2) hDifferentBase
    _ = multiplicity P.1
          (differentIdeal (RatFuncInfinityIntegers C) R2) := by
      change w.1.ramificationIdx R2 *
          multiplicity P.1 (differentIdeal A R2) =
        multiplicity P.1 (differentIdeal A R2)
      have hRam : w.1.ramificationIdx R2 = 1 :=
        exactConstantExtensionPresentedInfinityPlace_ramificationIdx_eq_one
          C S N hExact q
      rw [hRam]
      simpa only [one_mul]


/-- Exact constant extension preserves the total-different coefficient at
every presented finite or infinity place. -/
theorem exactConstantExtension_presented_totalDifferentMultiplicity_eq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (q : ExactConstantExtensionPresentedPlace C S N) :
    let E := ExactConstantExtension C N S
    let : Field E := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) E :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : SMul (RatFunc C) E := Algebra.toSMul
    let : Module (RatFunc C) E := Algebra.toModule
    let : FiniteDimensional (RatFunc C) E :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    let : Algebra.IsSeparable (RatFunc C) E :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) E := Algebra.toSMul
    let : Module (RatFunc S) E := Algebra.toModule
    let : Algebra S[X] E :=
      constantExtensionTensorPolynomialAlgebra C S N
    let : SMul S[X] E := Algebra.toSMul
    let : Module S[X] E := Algebra.toModule
    let : IsScalarTower S[X] (RatFunc S) E :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] E p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    let : FiniteDimensional (RatFunc S) E :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) E :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionTotalDifferentEffectiveDivisor S E
        (exactConstantExtensionPresentedUpstairsPlaceEquiv
          C S N hExact q) =
      finiteExtensionTotalDifferentEffectiveDivisor C N
        (exactConstantExtensionPresentedDownstairsPlace
          C S N hExact q) := by
  cases q with
  | inl q => exact exactConstantExtension_presented_totalDifferentMultiplicity_eq_finite C S N hExact q
  | inr q => exact exactConstantExtension_presented_totalDifferentMultiplicity_eq_infinity C S N hExact q

/-- Exact finite extension of the full constant field preserves intrinsic
function-field genus. -/
theorem exactConstantExtension_genus_eq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    let E := ExactConstantExtension C N S
    letI : Field E := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) E :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    FunctionField.genus S E = FunctionField.genus C N := by
  dsimp only
  let E := ExactConstantExtension C N S
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) E := Algebra.toSMul
  let : Module (RatFunc C) E := Algebra.toModule
  let : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  let : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  let extendedConstantAlgebra : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  let tensorConstantAlgebra : Algebra S E :=
    Algebra.TensorProduct.leftAlgebra
  have hconstantMap (s : S) :
      (@algebraMap S E _ _ extendedConstantAlgebra) s =
        (@algebraMap S E _ _ tensorConstantAlgebra) s := by
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s
  have hConstantAlgebra :
      tensorConstantAlgebra = extendedConstantAlgebra := by
    apply Algebra.algebra_ext
    intro s
    exact (hconstantMap s).symm
  have hIntrinsicGenus :
      @FunctionField.genus S E _ _ tensorConstantAlgebra =
        @FunctionField.genus S E _ _ extendedConstantAlgebra := by
    rw [hConstantAlgebra]
  have htensorPolynomialMap (s : S) :
      (@algebraMap S E _ _ tensorConstantAlgebra) s =
        (@algebraMap S[X] E _ _
          (constantExtensionTensorPolynomialAlgebra C S N))
            (algebraMap S S[X] s) := by
    change (s ⊗ₜ[C] (1 : N)) =
      Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N)
        (Polynomial.C s)
    simp
  let : Algebra S E := extendedConstantAlgebra
  let : SMul S E := Algebra.toSMul
  let : Algebra S[X] E :=
    constantExtensionTensorPolynomialAlgebra C S N
  let : SMul S[X] E := Algebra.toSMul
  let : IsScalarTower S[X] (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap S[X] E p =
        ratFuncToExactConstantExtension C S N hExact
          (algebraMap S[X] (RatFunc S) p)
      exact
        (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
  let : IsScalarTower S S[X] E :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro s
      exact (hconstantMap s).trans (htensorPolynomialMap s))
  let : FunctionField.IsFullConstantField C N :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot C N).2
      hExact
  let : FunctionField.IsFullConstantField S E :=
    (FunctionField.isFullConstantField_iff_algebraicClosure_eq_bot S E).2
      (by
        simpa only [E] using
          (exactConstantExtension_extended_algebraicClosure_eq_bot
            C S N hExact))
  calc
    @FunctionField.genus S E _ _ tensorConstantAlgebra =
        @FunctionField.genus S E _ _ extendedConstantAlgebra :=
      hIntrinsicGenus
    _ = FunctionField.Chart.genus S E :=
      FunctionField.genus_eq_genusChart S E
    _ = FunctionField.Chart.genus C N :=
      exactConstantExtension_chart_genus_eq_of_presentedMultiplicity
        C S N hExact
          (exactConstantExtension_presented_totalDifferentMultiplicity_eq
            C S N hExact)
    _ = FunctionField.genus C N :=
      (FunctionField.genus_eq_genusChart C N).symm

end

end BGS.HasseWeil
