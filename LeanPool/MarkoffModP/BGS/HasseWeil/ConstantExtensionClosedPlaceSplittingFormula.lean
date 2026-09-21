/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionInfinityPlaceDegreeTower

/-!
# Closed-place splitting formula for an exact extension of constants

This file supplies the exhaustive presentation equivalences needed to sum
the local constant-extension splitting laws over all closed places.

The finite branch is recorded first, then the reciprocal-infinity branch is
transported to actual places.  Their exact sum-branch fiber equivalence gives
the global gcd splitting law and the closed-place degree-extension identity.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

section FinitePresentation

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance splittingFormulaBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance splittingFormulaBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance splittingFormulaTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The explicit `S[X]`-normalization presentation exhausts the actual
finite places over the enlarged rational function field `S(X)`.

The first equivalence presents the same primes as places over `C(X)`; the
second is the finite-normalization base-change equivalence from `C` to `S`.
-/
noncomputable def exactConstantExtensionPresentedUpstairsFinitePlaceEquiv :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) ≃
      FiniteExtensionFinitePlace S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let first := exactConstantExtensionPresentedFinitePlaceEquiv
    C S N hExact
  let second := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (ratFuncFiniteIntegralClosureRingEquiv C S
      (ExactConstantExtension C N S)
      (exactConstantExtension_ratFunc_polynomialCompatibility
        C S N hExact))
  exact first.trans second

/-- The exhaustive finite-place equivalence is definitionally the existing
upstairs finite-place construction on presented primes. -/
@[simp]
theorem exactConstantExtensionPresentedUpstairsFinitePlaceEquiv_apply
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    exactConstantExtensionPresentedUpstairsFinitePlaceEquiv
        C S N hExact q =
      exactConstantExtensionUpstairsFinitePlace C S N hExact q := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  change IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (ratFuncFiniteIntegralClosureRingEquiv C S
        (ExactConstantExtension C N S)
        (exactConstantExtension_ratFunc_polynomialCompatibility
          C S N hExact))
      (exactConstantExtensionPresentedFinitePlaceEquiv C S N hExact q) = _
  rw [exactConstantExtensionPresentedFinitePlaceEquiv_apply]
  exact exactConstantExtensionCompatibleBaseFinitePlace_baseChange
    C S N hExact q

/-- Every downstairs finite place has the standard gcd number of presented
finite places above it.  Unlike the selected-prime form of the splitting
theorem, this statement is indexed by an arbitrary downstairs place and is
therefore ready for fiberwise summation. -/
theorem exactConstantExtensionPresentedFinitePlaceFiber_natCard_eq_gcd_of_downstairs
    (P : FiniteExtensionFinitePlace C N) :
    Nat.card {q : IsDedekindDomain.HeightOneSpectrum
        (integralClosure S[X] (ExactConstantExtension C N S)) //
      exactConstantExtensionDownstairsFinitePlace C S N hExact q = P} =
      Nat.gcd (Module.finrank C S)
        (finiteExtensionPlaceDegree C N (.inl P)) := by
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) E := Algebra.toSMul
  letI : Module (RatFunc C) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra N E := exactConstantExtensionAlgebra C N S
  letI : SMul N E := Algebra.toSMul
  letI : Module N E := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective C N E P
  let Q₀ : FinitePlaceUnderFiber C N E P := ⟨Q, hQ⟩
  let e := exactConstantExtensionPresentedFinitePlaceFiberEquiv
    C S N hExact P
  let q₀ := e.symm Q₀
  have hselected :=
    exactConstantExtensionPresentedFinitePlaceFiber_natCard_eq_gcd
      C S N hExact q₀.1
  simpa only [q₀.2] using hselected

end FinitePresentation

section InfinityPresentation


private theorem splittingFormulaReciprocalPolynomialAlgebra_map
    (K L : Type*) [Field K] [Field L]
    [DecidableEq K] [DecidableEq (RatFunc K)]
    [Algebra (RatFunc K) L] (p : K[X]) :
    letI : Algebra K[X] L :=
      ratFuncExtensionReciprocalPolynomialAlgebra K L
    algebraMap K[X] L p = algebraMap (RatFunc K) L
      (((reciprocalPolynomialRingHom K p :
        RatFuncInfinityIntegers K) : RatFunc K)) := by
  letI : Algebra K[X] L :=
    ratFuncExtensionReciprocalPolynomialAlgebra K L
  change algebraMap (RatFuncInfinityIntegers K) L
      (reciprocalPolynomialRingHom K p) = _
  exact IsScalarTower.algebraMap_apply
    (RatFuncInfinityIntegers K) (RatFunc K) L _

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000) splittingFormulaBaseRatFuncDecidableEq :
    DecidableEq (RatFunc C) :=
  closedPlaceRatFuncBaseDecidableEq C

local instance (priority := 10000) splittingFormulaTargetRatFuncDecidableEq :
    DecidableEq (RatFunc S) :=
  closedPlaceRatFuncConstantsDecidableEq S

local instance splittingFormulaInfinityBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance splittingFormulaInfinityBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance splittingFormulaBaseReciprocalPolynomialAlgebra :
    Algebra C[X] N :=
  infinityBridgeBaseReciprocalPolynomialAlgebra C N

local instance splittingFormulaBaseReciprocalConstantTower :
    IsScalarTower C C[X] N :=
  infinityBridgeBaseConstantPolynomialTower C N

local instance splittingFormulaOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  infinityBridgeOldNormalizationConstantAlgebra C N

local instance splittingFormulaOldNormalizationConstantTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  infinityBridgeOldNormalizationConstantPolynomialTower C N

local instance splittingFormulaTensorReciprocalPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  infinityBridgeTensorPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The reciprocal-normalization presentation exhausts the actual infinity
places of the exact constant extension over the enlarged constant field
`S`.  The equivalence first transports the reciprocal affine prime to the
`S[X]`-normalization, then localizes at the reciprocal origin. -/
noncomputable def exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv :
    ExactConstantExtensionPresentedInfinityPlace C S N ≃
      letI : Field (ExactConstantExtension C N S) :=
        exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      FiniteExtensionInfinityPlace S (ExactConstantExtension C N S) := by
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) E := Algebra.toSMul
  letI : Module (RatFunc S) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  letI : Algebra S[X] E :=
    ratFuncExtensionReciprocalPolynomialAlgebra S E
  letI : SMul S[X] E := Algebra.toSMul
  letI : Module S[X] E := Algebra.toModule
  let R := S ⊗[C] integralClosure C[X] N
  let A := integralClosure S[X] E
  let V := RatFuncInfinityIntegers S
  let B := RatFuncInfinityIntegralClosure S E
  let o := Ideal.span ({Polynomial.X} : Set S[X])
  let e := exactConstantExtensionInfinityAffineNormalizationAlgEquiv
    C S N hExact
  let eH := heightOneSpectrumEquivOfAlgEquiv e
  let first : ExactConstantExtensionPresentedInfinityPlace C S N ≃
      {q : IsDedekindDomain.HeightOneSpectrum A //
        q.asIdeal.under S[X] = o} := by
    apply eH.subtypeEquiv
    intro q
    change q.asIdeal.under S[X] = o ↔
      (eH q).asIdeal.under S[X] = o
    have hUnder : (eH q).asIdeal.under S[X] =
        q.asIdeal.under S[X] := by
      ext p
      change e.symm _ ∈ q.asIdeal ↔ _ ∈ q.asIdeal
      rw [e.symm.commutes]
    rw [hUnder]
  have ho : o ≠ ⊥ := by
    exact fun h => Polynomial.X_ne_zero
      (Ideal.span_singleton_eq_bot.mp h)
  letI : o.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
      Polynomial.prime_X
  letI : Algebra S[X] (RatFunc S) :=
    ratFuncExtensionReciprocalPolynomialAlgebra S (RatFunc S)
  letI : SMul S[X] (RatFunc S) := Algebra.toSMul
  letI : IsScalarTower S[X] (RatFunc S) E :=
    IsScalarTower.of_algebraMap_eq fun p => by
      calc
        algebraMap S[X] E p =
            algebraMap (RatFunc S) E
              (((reciprocalPolynomialRingHom S p :
                RatFuncInfinityIntegers S) : RatFunc S)) :=
          splittingFormulaReciprocalPolynomialAlgebra_map S E p
        _ = algebraMap (RatFunc S) E
            (algebraMap S[X] (RatFunc S) p) := by
          rw [splittingFormulaReciprocalPolynomialAlgebra_map
            S (RatFunc S) p]
          exact congrArg (algebraMap (RatFunc S) E)
            (Algebra.algebraMap_self_apply _).symm
  letI : IsFractionRing S[X] (RatFunc S) :=
    ratFunc_isFractionRing_reciprocalPolynomial S
  letI : IsDedekindDomain A :=
    IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) E A
  letI : Module S[X] A := Algebra.toModule
  letI : Module.IsTorsionFree S[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply IsFractionRing.injective S[X] (RatFunc S)
    apply (algebraMap (RatFunc S) E).injective
    simpa only [IsScalarTower.algebraMap_apply S[X] (RatFunc S) E]
      using hxy
  letI : IsScalarTower S[X] A E := by infer_instance
  letI : Module.IsTorsionFree S[X] A :=
    IsIntegralClosure.isTorsionFree S[X] E
  let origin : IsDedekindDomain.HeightOneSpectrum S[X] :=
    ⟨o, inferInstance, ho⟩
  let second : {q : IsDedekindDomain.HeightOneSpectrum A //
        q.asIdeal.under S[X] = o} ≃ o.primesOver A :=
    { toFun := fun q => ⟨q.1.asIdeal, q.1.isPrime, ⟨q.2.symm⟩⟩
      invFun := fun P => ⟨primeOverHeightOne origin P, by
        exact (Ideal.over_def P.1 o).symm⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  letI : Algebra S[X] V :=
    ratFuncInfinityReciprocalPolynomialAlgebra S
  letI : IsLocalization o.primeCompl V :=
    ratFuncInfinityIntegers_isLocalization_reciprocal S
  letI : Algebra A B :=
    ratFuncInfinityReciprocalIntegralClosureAlgebra S E
  letI : SMul A B := Algebra.toSMul
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A o.primeCompl) B :=
    ratFuncInfinityIntegralClosure_isLocalization_reciprocal S E
  letI : Algebra S[X] B :=
    RingHom.toAlgebra
      ((algebraMap V B).comp (algebraMap S[X] V))
  letI : IsScalarTower S[X] V B :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S[X] A B :=
    IsScalarTower.of_algebraMap_eq fun p => by
      apply Subtype.ext
      rfl
  let third : o.primesOver A ≃ FiniteExtensionInfinityPlace S E := by
    change o.primesOver A ≃
      (IsLocalRing.maximalIdeal V).primesOver B
    exact (IsDedekindDomain.primesOverEquivPrimesOver
      o V B ho).toEquiv
  exact first.trans (second.trans third)

omit [DecidableEq C] in
/-- On a reciprocal affine prime, the exhaustive equivalence is exactly the
existing upstairs infinity-place construction. -/
@[simp]
theorem exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv_apply
    (q : ExactConstantExtensionPresentedInfinityPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv
        C S N hExact q =
      exactConstantExtensionUpstairsInfinityPlace
        C S N hExact q.1 q.2 := by
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  apply Subtype.ext
  rfl

include hExact

omit [DecidableEq C] [DecidableEq S] in
/-- Every downstairs infinity place has the standard gcd number of presented
reciprocal-normalization places above it.  This removes the selected-prime
index from the infinity splitting theorem and makes it ready for global
fiberwise summation. -/
theorem exactConstantExtensionPresentedInfinityPlaceFiber_natCard_eq_gcd_of_downstairs :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    (P : FiniteExtensionInfinityPlace C N) →
      Nat.card {q : ExactConstantExtensionPresentedInfinityPlace C S N //
        exactConstantExtensionDownstairsInfinityPlace
          C S N q.1 q.2 = P} =
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N (.inr P)) := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  intro P
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) E := Algebra.toSMul
  letI : Module (RatFunc C) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : Algebra N E := exactConstantExtensionAlgebra C N S
  letI : SMul N E := Algebra.toSMul
  letI : Module N E := Algebra.toModule
  letI : IsScalarTower (RatFunc C) N E :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  obtain ⟨Q, hQ⟩ := infinityPlaceUnder_surjective C N E P
  let Q₀ : InfinityPlaceUnderFiber C N E P := ⟨Q, hQ⟩
  let e := exactConstantExtensionPresentedInfinityPlaceFiberEquiv
    C S N hExact P
  let q₀ := e.symm Q₀
  have hselected :=
    exactConstantExtensionPresentedInfinityPlaceFiber_natCard_eq_gcd
      C S N hExact q₀.1
  simpa only [q₀.2] using hselected

end InfinityPresentation

section GlobalPresentation

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance (priority := 10000) globalPresentationBaseRatFuncDecidableEq :
    DecidableEq (RatFunc C) :=
  closedPlaceRatFuncBaseDecidableEq C

local instance (priority := 10000) globalPresentationTargetRatFuncDecidableEq :
    DecidableEq (RatFunc S) :=
  closedPlaceRatFuncConstantsDecidableEq S

local instance globalPresentationBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance globalPresentationBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance globalPresentationTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The finite-normalization and reciprocal-normalization presentations
together exhaust all actual closed places of the exact constant extension
over `S`. -/
noncomputable def exactConstantExtensionPresentedUpstairsPlaceEquiv :
    ExactConstantExtensionPresentedPlace C S N ≃
      letI : Field (ExactConstantExtension C N S) :=
        exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
        ratFuncExactConstantExtensionAlgebra C S N hExact
      FiniteExtensionPlace S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  exact Equiv.sumCongr
    (exactConstantExtensionPresentedUpstairsFinitePlaceEquiv
      C S N hExact)
    (exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv
      C S N hExact)

/-- The global exhaustive equivalence agrees branchwise with the existing
presented-upstairs-place construction. -/
@[simp]
theorem exactConstantExtensionPresentedUpstairsPlaceEquiv_apply
    (q : ExactConstantExtensionPresentedPlace C S N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    exactConstantExtensionPresentedUpstairsPlaceEquiv C S N hExact q =
      exactConstantExtensionPresentedUpstairsPlace C S N hExact q := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  cases q with
  | inl q =>
      change Sum.inl
          (exactConstantExtensionPresentedUpstairsFinitePlaceEquiv
            C S N hExact q) =
        Sum.inl
          (exactConstantExtensionUpstairsFinitePlace C S N hExact q)
      exact congrArg Sum.inl
        (exactConstantExtensionPresentedUpstairsFinitePlaceEquiv_apply
          C S N hExact q)
  | inr q =>
      change Sum.inr
          (exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv
            C S N hExact q) =
        Sum.inr
          (exactConstantExtensionUpstairsInfinityPlace
            C S N hExact q.1 q.2)
      exact congrArg Sum.inr
        (exactConstantExtensionPresentedUpstairsInfinityPlaceEquiv_apply
          C S N hExact q)

include hExact

omit [DecidableEq C] [DecidableEq S] in
/-- The contraction fiber of the combined finite-plus-infinity presentation
over an arbitrary downstairs closed place has the standard gcd cardinality.
The proof is an exact branchwise fiber equivalence, so finite and infinity
places cannot be mixed by the presentation map. -/
theorem exactConstantExtensionPresentedPlaceFiber_natCard_eq_gcd_of_downstairs :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    (P : FiniteExtensionPlace C N) →
      Nat.card {q : ExactConstantExtensionPresentedPlace C S N //
        exactConstantExtensionPresentedDownstairsPlace
          C S N hExact q = P} =
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N P) := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  intro P
  cases P with
  | inl P =>
      let e : {q : ExactConstantExtensionPresentedPlace C S N //
          exactConstantExtensionPresentedDownstairsPlace
            C S N hExact q = .inl P} ≃
          {q : IsDedekindDomain.HeightOneSpectrum
              (integralClosure S[X] (ExactConstantExtension C N S)) //
            exactConstantExtensionDownstairsFinitePlace
              C S N hExact q = P} :=
        { toFun := fun q => by
            rcases q with ⟨q, hq⟩
            cases q with
            | inl q =>
                refine ⟨q, ?_⟩
                exact Sum.inl.inj hq
            | inr q =>
                change Sum.inr _ = Sum.inl P at hq
                exact (Sum.inr_ne_inl hq).elim
          invFun := fun q =>
            ⟨.inl q.1, congrArg Sum.inl q.2⟩
          left_inv := by
            intro q
            apply Subtype.ext
            rcases q with ⟨q, hq⟩
            cases q with
            | inl q => rfl
            | inr q =>
                change Sum.inr _ = Sum.inl P at hq
                exact (Sum.inr_ne_inl hq).elim
          right_inv := by
            intro q
            apply Subtype.ext
            rfl }
      calc
        Nat.card {q : ExactConstantExtensionPresentedPlace C S N //
            exactConstantExtensionPresentedDownstairsPlace
              C S N hExact q = .inl P} =
            Nat.card {q : IsDedekindDomain.HeightOneSpectrum
                (integralClosure S[X] (ExactConstantExtension C N S)) //
              exactConstantExtensionDownstairsFinitePlace
                C S N hExact q = P} := Nat.card_congr e
        _ = Nat.gcd (Module.finrank C S)
            (finiteExtensionPlaceDegree C N (.inl P)) :=
          exactConstantExtensionPresentedFinitePlaceFiber_natCard_eq_gcd_of_downstairs
            C S N hExact P
  | inr P =>
      let e : {q : ExactConstantExtensionPresentedPlace C S N //
          exactConstantExtensionPresentedDownstairsPlace
            C S N hExact q = .inr P} ≃
          {q : ExactConstantExtensionPresentedInfinityPlace C S N //
            exactConstantExtensionDownstairsInfinityPlace
              C S N q.1 q.2 = P} :=
        { toFun := fun q => by
            rcases q with ⟨q, hq⟩
            cases q with
            | inl q =>
                change Sum.inl _ = Sum.inr P at hq
                exact (Sum.inl_ne_inr hq).elim
            | inr q =>
                refine ⟨q, ?_⟩
                exact Sum.inr.inj hq
          invFun := fun q =>
            ⟨.inr q.1, congrArg Sum.inr q.2⟩
          left_inv := by
            intro q
            apply Subtype.ext
            rcases q with ⟨q, hq⟩
            cases q with
            | inl q =>
                change Sum.inl _ = Sum.inr P at hq
                exact (Sum.inl_ne_inr hq).elim
            | inr q => rfl
          right_inv := by
            intro q
            apply Subtype.ext
            rfl }
      calc
        Nat.card {q : ExactConstantExtensionPresentedPlace C S N //
            exactConstantExtensionPresentedDownstairsPlace
              C S N hExact q = .inr P} =
            Nat.card {q : ExactConstantExtensionPresentedInfinityPlace C S N //
              exactConstantExtensionDownstairsInfinityPlace
                C S N q.1 q.2 = P} := Nat.card_congr e
        _ = Nat.gcd (Module.finrank C S)
            (finiteExtensionPlaceDegree C N (.inr P)) :=
          exactConstantExtensionPresentedInfinityPlaceFiber_natCard_eq_gcd_of_downstairs
            C S N hExact P

omit [DecidableEq C] [DecidableEq S] in
/-- Exact closed-place count identity for an extension of constants.  At
level `n`, the exhaustive closed-place count over `S` is the original count
at level `[S : C] * n`.  The proof transfers the bounded upstairs family
through the exhaustive presentation equivalence and sums the degree and gcd
fiber formulas. -/
theorem exactConstantExtensionClosedPlaceExtensionCount_eq
    (level : ℕ) :
    letI : DecidableEq C := infinityBridgeDecidableEqConstants C
    letI : DecidableEq (RatFunc C) :=
      infinityBridgeDecidableEqRatFuncConstants C
    letI : DecidableEq S := infinityBridgeDecidableEqConstants S
    letI : DecidableEq (RatFunc S) :=
      infinityBridgeDecidableEqRatFuncConstants S
    letI : Fintype S := Fintype.ofFinite S
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc S) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc S)
        (ExactConstantExtension C N S) :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc S)
        (ExactConstantExtension C N S) :=
      isSeparable_over_extendedRatFunc C S N hExact
    finiteExtensionClosedPlaceExtensionCount S
        (ExactConstantExtension C N S) level =
      finiteExtensionClosedPlaceExtensionCount C N
        (Module.finrank C S * level) := by
  letI : DecidableEq C := infinityBridgeDecidableEqConstants C
  letI : DecidableEq (RatFunc C) :=
    infinityBridgeDecidableEqRatFuncConstants C
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    infinityBridgeDecidableEqRatFuncConstants S
  letI : Fintype S := Fintype.ofFinite S
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) E :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) E := Algebra.toSMul
  letI : Module (RatFunc C) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) E :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc
      C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) E :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) E := Algebra.toSMul
  letI : Module (RatFunc S) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  by_cases hlevel : level = 0
  · subst level
    simp
  have hlevelPos : 0 < level := Nat.pos_of_ne_zero hlevel
  let Base := FiniteExtensionPlace C N
  let Up := ExactConstantExtensionPresentedPlace C S N
  let Actual := FiniteExtensionPlace S E
  let down : Up → Base :=
    exactConstantExtensionPresentedDownstairsPlace C S N hExact
  let baseDegree : Base → ℕ := finiteExtensionPlaceDegree C N
  let e : Up ≃ Actual :=
    exactConstantExtensionPresentedUpstairsPlaceEquiv C S N hExact
  let upDegree : Up → ℕ := fun q =>
    finiteExtensionPlaceDegree S E (e q)
  let BaseLE := {P : Base //
    baseDegree P ≤ Module.finrank C S * level}
  let UpLE := {q : Up // upDegree q ≤ level}
  let ActualLE := {Q : Actual //
    finiteExtensionPlaceDegree S E Q ≤ level}
  letI : Fintype BaseLE :=
    finiteExtensionPlaceDegreeLEFintype C N
      (Module.finrank C S * level)
  letI : Fintype ActualLE :=
    finiteExtensionPlaceDegreeLEFintype S E level
  let eLE : UpLE ≃ ActualLE :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  letI : Fintype UpLE := Fintype.ofEquiv ActualLE eLE.symm
  let UpDvd := {q : UpLE // upDegree q.1 ∣ level}
  let ActualDvd := {Q : ActualLE //
    finiteExtensionPlaceDegree S E Q.1 ∣ level}
  let eDvd : UpDvd ≃ ActualDvd :=
    Equiv.subtypeEquiv eLE (fun _ => Iff.rfl)
  have hsumPresented :
      (∑ q : UpDvd, upDegree q.1.1) =
        ∑ P : {P : BaseLE //
          baseDegree P.1 ∣ Module.finrank C S * level},
          baseDegree P.1.1 := by
    apply sum_degree_dvd_eq_sum_degree_dvd_of_div_gcd_fibers
      down baseDegree upDegree (Module.finrank C S) level
      Module.finrank_pos hlevelPos
    · intro q
      change finiteExtensionPlaceDegree S E (e q) =
        finiteExtensionPlaceDegree C N (down q) /
          Nat.gcd (Module.finrank C S)
            (finiteExtensionPlaceDegree C N (down q))
      dsimp [e, down]
      rw [exactConstantExtensionPresentedUpstairsPlaceEquiv_apply]
      exact exactConstantExtensionPresentedPlace_degree_eq_div_gcd
        C S N hExact q
    · intro P
      exact exactConstantExtensionPresentedPlaceFiber_natCard_eq_gcd_of_downstairs
        C S N hExact P
  have hsumEquiv :
      (∑ q : UpDvd, upDegree q.1.1) =
        ∑ Q : ActualDvd,
          finiteExtensionPlaceDegree S E Q.1.1 := by
    apply Fintype.sum_equiv eDvd
    intro q
    rfl
  rw [finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd,
    finiteExtensionClosedPlaceExtensionCount_eq_sum_degree_dvd]
  exact hsumEquiv.symm.trans hsumPresented

end GlobalPresentation

end

end BGS.HasseWeil
