/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldConstantExtensionResidue
public import LeanPool.MarkoffModP.BGS.HasseWeil.FinitePlaceNormalizationTransport
public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldConstantField
public import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension

/-!
# Finite places in an exact constant extension

Let `N / C(X)` be finite separable with exact constant field `C`, and let `S / C`
be finite Galois.  This file connects maximal ideals in the explicit
normalization of `S ⊗[C] N` to the project's finite-place types over `S` and
`C`.  It proves that the upstairs residue field is finite, packages the
downstairs contraction as an actual finite place of `N`, and expresses the
constant-extension residue formula as

`deg_S(Q) = deg_C(P) / gcd([S : C], deg_C(P))`.

No maximality or residue-finiteness hypothesis is left to downstream users.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance bridgeBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance (priority := 10000) bridgeBasePolynomialAlgebra : Algebra C[X] N :=
  ratFuncInducedPolynomialAlgebra C N

local instance bridgeBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)

local instance (priority := 10000) bridgeTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  constantExtensionTensorPolynomialAlgebra C S N

local instance (priority := 10000) bridgeTensorNormalizationPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  constantExtensionNormalizationTensorPolynomialAlgebra C S N

local instance bridgeUpstairsConstantAlgebra :
    Algebra S
      (integralClosure S[X] (ExactConstantExtension C N S)) :=
  RingHom.toAlgebra
    ((algebraMap S[X]
      (integralClosure S[X] (ExactConstantExtension C N S))).comp
        (algebraMap S S[X]))

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- A ring equivalence transports the residue field of a height-one ideal. -/
private noncomputable def heightOneResidueFieldRingEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : IsDedekindDomain.HeightOneSpectrum A) :
    q.asIdeal.ResidueField ≃+*
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e q).asIdeal.ResidueField :=
  Ideal.residueFieldRingEquiv q.asIdeal
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e q).asIdeal e
    (by
      change q.asIdeal = (q.asIdeal.comap e.symm).comap e
      exact (Ideal.comap_of_equiv e).symm)

/-- Pull an ideal in the explicit base-changed normalization back to the
constant tensor of the original normalization. -/
noncomputable def exactConstantExtensionTensorNormalizationHeightOne
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    IsDedekindDomain.HeightOneSpectrum
      (S ⊗[C] integralClosure C[X] N) :=
  heightOneSpectrumEquivOfAlgEquiv
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).symm q

/-- Package a height-one ideal of the explicit normalization as an actual
finite place over `S`. -/
noncomputable def exactConstantExtensionUpstairsFinitePlace
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    FiniteExtensionFinitePlace S (ExactConstantExtension C N S) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  exact finiteExtensionFinitePlaceEquivOfNormalizationAlgEquiv
    S (ExactConstantExtension C N S)
    (S ⊗[C] integralClosure C[X] N)
    (exactConstantExtensionNormalizationAlgEquiv C S N hExact)
    (exactConstantExtensionTensorNormalizationHeightOne C S N q)

include hExact

omit [Fintype C] [DecidableEq C] [DecidableEq S]
    [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)] in
/-- The residue field of an upstairs height-one ideal is finite. -/
theorem exactConstantExtensionUpstairsResidueField_finite [Finite C]
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    Finite q.asIdeal.ResidueField := by
  let : Fintype C := Fintype.ofFinite C
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Fintype S := Fintype.ofFinite S
  let qTensor := exactConstantExtensionTensorNormalizationHeightOne C S N q
  let e₂ := exactConstantExtensionNormalizationAlgEquiv C S N hExact
  let Q : FiniteExtensionFinitePlace S (ExactConstantExtension C N S) :=
    IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      e₂.toRingEquiv qTensor
  let : Finite Q.asIdeal.ResidueField :=
    finiteExtensionFinitePlaceResidueField_finite S
      (ExactConstantExtension C N S) Q
  let e₁ := finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N
  let r₁ := heightOneResidueFieldRingEquiv e₁.symm.toRingEquiv q
  let r₂ := heightOneResidueFieldRingEquiv e₂.toRingEquiv qTensor
  exact Finite.of_injective (r₂ ∘ r₁) (r₂.injective.comp r₁.injective)

omit [Fintype C] [DecidableEq C] [DecidableEq S]
    [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)] in
/-- Every upstairs height-one ideal is maximal. -/
theorem exactConstantExtensionUpstairsIdeal_isMaximal [Finite C]
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    q.asIdeal.IsMaximal := by
  let : Finite q.asIdeal.ResidueField :=
    exactConstantExtensionUpstairsResidueField_finite C S N hExact q
  let : Finite
      (integralClosure S[X] (ExactConstantExtension C N S) ⧸ q.asIdeal) :=
    Finite.of_injective
      (algebraMap
        (integralClosure S[X] (ExactConstantExtension C N S) ⧸ q.asIdeal)
        q.asIdeal.ResidueField)
      q.asIdeal.injective_algebraMap_quotient_residueField
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient q.asIdeal).mpr
    (Finite.isField_of_domain
      (integralClosure S[X] (ExactConstantExtension C N S) ⧸ q.asIdeal))

/-- Package the downstairs contraction as an actual finite place of `N/C(X)`. -/
noncomputable def exactConstantExtensionDownstairsFinitePlace
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    FiniteExtensionFinitePlace C N := by
  letI : Finite q.asIdeal.ResidueField :=
    exactConstantExtensionUpstairsResidueField_finite C S N hExact q
  letI : q.asIdeal.IsMaximal :=
    exactConstantExtensionUpstairsIdeal_isMaximal C S N hExact q
  let p := finiteFieldConstantExtensionDownstairsIdeal C S N q.asIdeal
  letI : p.IsMaximal :=
    finiteFieldConstantExtensionDownstairsIdeal_isMaximal C S N q.asIdeal
  change IsDedekindDomain.HeightOneSpectrum (integralClosure C[X] N)
  exact
    { asIdeal := p
      isPrime := Ideal.IsMaximal.isPrime
        (show p.IsMaximal from inferInstance)
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        (show p.IsMaximal from inferInstance)
        (by
          intro hfield
          have hinj : Function.Injective
              (algebraMap C[X] (integralClosure C[X] N)) := by
            intro x y hxy
            apply RatFunc.algebraMap_injective C
            apply (algebraMap (RatFunc C) N).injective
            exact congrArg Subtype.val hxy
          exact Polynomial.not_isField C
            (isField_of_isIntegral_of_isField hinj hfield)) }

omit [DecidableEq C] [DecidableEq (RatFunc C)]
    [DecidableEq (RatFunc S)] in
@[simp]
theorem exactConstantExtensionDownstairsFinitePlace_asIdeal
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    (exactConstantExtensionDownstairsFinitePlace C S N hExact q).asIdeal =
      finiteFieldConstantExtensionDownstairsIdeal C S N q.asIdeal :=
  rfl

/-- Constant extension changes the degree of an actual finite place by the
standard division-by-gcd formula. -/
theorem exactConstantExtensionFinitePlace_degree_eq_div_gcd
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S))) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    finiteExtensionPlaceDegree S (ExactConstantExtension C N S)
        (.inl (exactConstantExtensionUpstairsFinitePlace C S N hExact q)) =
      finiteExtensionPlaceDegree C N
          (.inl (exactConstantExtensionDownstairsFinitePlace C S N hExact q)) /
        Nat.gcd (Module.finrank C S)
          (finiteExtensionPlaceDegree C N
            (.inl (exactConstantExtensionDownstairsFinitePlace C S N hExact q))) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) (ExactConstantExtension C N S) :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc S) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : FiniteDimensional (RatFunc S)
      (ExactConstantExtension C N S) :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S)
      (ExactConstantExtension C N S) :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : Finite q.asIdeal.ResidueField :=
    exactConstantExtensionUpstairsResidueField_finite C S N hExact q
  let : q.asIdeal.IsMaximal :=
    exactConstantExtensionUpstairsIdeal_isMaximal C S N hExact q
  let A := S ⊗[C] integralClosure C[X] N
  let T := ExactConstantExtension C N S
  let : Algebra S[X] A :=
    bridgeTensorNormalizationPolynomialAlgebra C S N
  let : Algebra S A := Algebra.TensorProduct.leftAlgebra
  let : Algebra S (RatFuncFiniteIntegralClosure S T) :=
    RingHom.toAlgebra
      ((algebraMap S[X] (RatFuncFiniteIntegralClosure S T)).comp
        (algebraMap S S[X]))
  let : SMul S A := Algebra.toSMul
  let : SMul S (RatFuncFiniteIntegralClosure S T) := Algebra.toSMul
  let : SMul S[X] (RatFuncFiniteIntegralClosure S T) := Algebra.toSMul
  let : IsScalarTower S S[X] (RatFuncFiniteIntegralClosure S T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let qTensor := exactConstantExtensionTensorNormalizationHeightOne C S N q
  let Q := exactConstantExtensionUpstairsFinitePlace C S N hExact q
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let : (finiteFieldConstantExtensionTensorIdeal
      C S N q.asIdeal).IsPrime := by
    change qTensor.asIdeal.IsPrime
    exact qTensor.isPrime
  let p := finiteFieldConstantExtensionDownstairsIdeal C S N q.asIdeal
  let : p.IsMaximal :=
    finiteFieldConstantExtensionDownstairsIdeal_isMaximal C S N q.asIdeal
  let : p.IsPrime := Ideal.IsMaximal.isPrime
    (show p.IsMaximal from inferInstance)
  let e₂ := exactConstantExtensionNormalizationAlgEquiv C S N hExact
  let e₂S : A ≃ₐ[S] RatFuncFiniteIntegralClosure S T :=
    { e₂.toRingEquiv with
      commutes' := fun s => by
        change e₂ (s ⊗ₜ[C] (1 : integralClosure C[X] N)) =
          algebraMap S[X] (RatFuncFiniteIntegralClosure S T) (Polynomial.C s)
        rw [← e₂.commutes (Polynomial.C s)]
        congr 1
        change s ⊗ₜ[C] (1 : integralClosure C[X] N) =
          Polynomial.aeval
            (polynomialTensorCancelEvaluationPoint C S
              (integralClosure C[X] N)) (Polynomial.C s)
        simp }
  have hTensorToUpstairs :
      Module.finrank S qTensor.asIdeal.ResidueField =
        Module.finrank S q.asIdeal.ResidueField := by
    change Module.finrank S
        (finiteFieldConstantExtensionTensorIdeal C S N q.asIdeal).ResidueField =
      Module.finrank S q.asIdeal.ResidueField
    exact (finiteFieldConstantExtensionResidueFieldAlgEquiv
      C S N q.asIdeal).toLinearEquiv.finrank_eq
  have hTensorToPlace :
      Module.finrank S qTensor.asIdeal.ResidueField =
        Module.finrank S Q.asIdeal.ResidueField := by
    exact heightOneSpectrum_residueField_finrank_eq e₂S qTensor
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField S T Q,
    finiteExtensionFinitePlace_degree_eq_finrank_residueField C N P]
  calc
    Module.finrank S Q.asIdeal.ResidueField =
        Module.finrank S qTensor.asIdeal.ResidueField := hTensorToPlace.symm
    _ = Module.finrank S q.asIdeal.ResidueField := hTensorToUpstairs
    _ = Module.finrank C
          (finiteFieldConstantExtensionDownstairsIdeal C S N q.asIdeal).ResidueField /
        Nat.gcd (Module.finrank C S)
          (Module.finrank C
            (finiteFieldConstantExtensionDownstairsIdeal
              C S N q.asIdeal).ResidueField) :=
      finiteFieldConstantExtensionResidue_finrank_over_constants_eq_div_gcd
        C S N q.asIdeal
    _ = Module.finrank C P.asIdeal.ResidueField /
        Nat.gcd (Module.finrank C S)
          (Module.finrank C P.asIdeal.ResidueField) := by
      rfl

end

end BGS.HasseWeil
