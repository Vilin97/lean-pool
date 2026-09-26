/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlaceCompatibility

/-!
# Frobenius-coset averaging at finite places of an exact constant extension

This file composes the actual constant-extension finite-place construction
with the Frobenius-coset form of Burnside's lemma.  A rational place below
one explicit constant-extended finite place supplies the decomposition-group
cardinality at that place.  Transitivity of the relative Galois action and
cyclicity of the finite-field Galois group propagate surjectivity of the
constant quotient to every stabilizer in the same restriction fiber.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


/-- In a transitive action, surjectivity of a homomorphism on one stabilizer
propagates to every stabilizer when the target is cyclic.  Stabilizers in the
same orbit are conjugate, and conjugation disappears in a cyclic target. -/
theorem MonoidHom.stabilizer_surjective_of_isPretransitive_of_isCyclic
    {G A X : Type*} [Group G] [Group A] [IsCyclic A]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (pi : G →* A) (x₀ : X)
    (h₀ : Function.Surjective
      (pi.comp (MulAction.stabilizer G x₀).subtype)) :
    ∀ x : X, Function.Surjective
      (pi.comp (MulAction.stabilizer G x).subtype) := by
  let : CommGroup A := IsCyclic.commGroup
  intro x c
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x₀ x
  obtain ⟨h, hh⟩ := h₀ c
  change pi (h : G) = c at hh
  let h' : MulAction.stabilizer G x :=
    MulAction.stabilizerEquivStabilizer hg.symm h
  refine ⟨h', ?_⟩
  change pi (h' : G) = c
  rw [show (h' : G) = MulAut.conj g (h : G) by
    exact MulAction.stabilizerEquivStabilizer_apply hg.symm h]
  simpa [MulAut.conj_apply, map_mul] using hh

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance averageBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance averageBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance averageTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

section IntermediateField

variable (L : Type*) [Field L]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L N] [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

local instance averageIntermediateConstantAlgebra : Algebra C L :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) L).comp
    (algebraMap C (RatFunc C)))

local instance averageConstantIntermediateTopTower :
    IsScalarTower C L N := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
    algebraMap L N
      (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) c))
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N _

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional L N] [IsGalois L N] in
/-- The rational-function base, the intermediate field, and the exact
constant extension form the tower used by the finite-place action. -/
private theorem exactConstantExtensionFrobeniusAverage_ratFuncBaseTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) := by
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change (1 : S) ⊗ₜ[C] algebraMap (RatFunc C) N x =
    (1 : S) ⊗ₜ[C] algebraMap L N (algebraMap (RatFunc C) L x)
  congr 1
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N x

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [Algebra (RatFunc C) L]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [IsScalarTower (RatFunc C) L N] [IsGalois L N] in
/-- The exact constant extension is finite-dimensional over the chosen
intermediate field. -/
private theorem finiteDimensional_exactConstantExtension_over_intermediate
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    FiniteDimensional L (ExactConstantExtension C N S) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower L N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C L N S
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N (ExactConstantExtension C N S) :=
    Module.Finite.equiv e
  let : Module.Finite L (ExactConstantExtension C N S) :=
    Module.Finite.trans N (ExactConstantExtension C N S)
  infer_instance

/-- Local Frobenius-coset Burnside identity for an actual finite place of an
exact constant extension.  The assumptions say only that its restriction to
`L` is rational and that `[N : L]` divides the constant-extension degree.
The exact decomposition-group cardinality, stabilizer surjectivity, and the
fixed-point total are all derived internally. -/
theorem exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum
    (q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure S[X] (ExactConstantExtension C N S)))
    (hBase : finiteExtensionPlaceDegree C L
      (.inl (finitePlaceUnder C L N
        (exactConstantExtensionDownstairsFinitePlace C S N hExact q))) = 1)
    (hDegreeDiv : Module.finrank L N ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      by exact exactConstantExtensionFrobeniusAverage_ratFuncBaseTower C S N L
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    letI : FiniteDimensional L (ExactConstantExtension C N S) :=
      by
        exact finiteDimensional_exactConstantExtension_over_intermediate
          (C := C) (S := S) (N := N) (L := L) hExact
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let Q := exactConstantExtensionCompatibleBaseFinitePlace
      C S N hExact q
    let P := finitePlaceUnder C L (ExactConstantExtension C N S) Q
    let pi := exactConstantExtensionConstantQuotient C L N S hExact
    letI : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
    letI : Fintype
        (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) := Fintype.ofFinite _
    letI : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
    letI : Fintype
        (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
          Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
    letI := finiteIntegralClosureGalAction C L
      (ExactConstantExtension C N S)
    letI := finitePlaceUnderFiberGalAction C L
      (ExactConstantExtension C N S) P
    (∑ g : pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
        Set (S ≃ₐ[C] S)),
      Nat.card (MulAction.fixedBy
        (FinitePlaceUnderFiber C L (ExactConstantExtension C N S) P) g.1)) =
      Nat.card (N ≃ₐ[L] N) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N (ExactConstantExtension C N S) :=
    exactConstantExtensionAlgebra C N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) :=
    Algebra.toModule
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  let : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module N (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) L
      (ExactConstantExtension C N S) :=
    exactConstantExtensionFrobeniusAverage_ratFuncBaseTower C S N L
  let : IsScalarTower (RatFunc C) N
      (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsScalarTower L N (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseTower C L N S
  let : IsGalois L (ExactConstantExtension C N S) :=
    exactConstantExtension_isGalois C L N S hExact
  let : FiniteDimensional L (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_intermediate
      (C := C) (S := S) (N := N) (L := L) hExact
  let : FiniteDimensional (RatFunc C)
      (ExactConstantExtension C N S) :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc C)
      (ExactConstantExtension C N S) :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let Q := exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q
  let P := finitePlaceUnder C L (ExactConstantExtension C N S) Q
  let pi := exactConstantExtensionConstantQuotient C L N S hExact
  let : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
  let : Fintype
      (ExactConstantExtension C N S ≃ₐ[L]
        ExactConstantExtension C N S) := Fintype.ofFinite _
  let : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
  let : Fintype
      (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
        Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
  let := finiteIntegralClosureGalAction C L
    (ExactConstantExtension C N S)
  let := finitePlaceUnderFiberGalAction C L
    (ExactConstantExtension C N S) P
  let : MulAction.IsPretransitive
      (ExactConstantExtension C N S ≃ₐ[L] ExactConstantExtension C N S)
      (FinitePlaceUnderFiber C L (ExactConstantExtension C N S) P) :=
    finitePlaceUnderFiberGalAction_isPretransitive C L
      (ExactConstantExtension C N S) P
  let Q₀ : FinitePlaceUnderFiber C L
      (ExactConstantExtension C N S) P := ⟨Q, rfl⟩
  let : Nonempty (FinitePlaceUnderFiber C L
      (ExactConstantExtension C N S) P) := ⟨Q₀⟩
  have hdecomp :=
    exactConstantExtensionFinitePlace_decompositionGroup_card_of_rational_base
      C S N hExact L q hBase hDegreeDiv
  have hcard₀ :
      Nat.card (MulAction.stabilizer
        (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) Q₀) =
        Nat.card
            (pi.comp (MulAction.stabilizer
              (ExactConstantExtension C N S ≃ₐ[L]
                ExactConstantExtension C N S) Q₀).subtype).ker *
          Nat.card (S ≃ₐ[C] S) := by
    rw [finitePlaceUnderFiber_stabilizer_eq_decompositionGroup
      C L (ExactConstantExtension C N S) P Q₀]
    exact hdecomp
  have hsurj₀ : Function.Surjective
      (pi.comp (MulAction.stabilizer
        (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) Q₀).subtype) :=
    MonoidHom.surjective_of_card_eq_card_ker_mul_card _ hcard₀
  have hsurj : ∀ x : FinitePlaceUnderFiber C L
      (ExactConstantExtension C N S) P,
      Function.Surjective
        (pi.comp (MulAction.stabilizer
          (ExactConstantExtension C N S ≃ₐ[L]
            ExactConstantExtension C N S) x).subtype) :=
    MonoidHom.stabilizer_surjective_of_isPretransitive_of_isCyclic
      pi Q₀ hsurj₀
  have hburnside := sum_card_fixedBy_quotientFiber_eq_card_ker
    pi hsurj (FiniteField.frobeniusAlgEquivOfAlgebraic C S)
  calc
    (∑ g : pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
          Set (S ≃ₐ[C] S)),
        Nat.card (MulAction.fixedBy
          (FinitePlaceUnderFiber C L (ExactConstantExtension C N S) P)
          g.1)) =
        Nat.card pi.ker := hburnside
    _ = Nat.card (N ≃ₐ[L] N) := by
      rw [exactConstantExtensionConstantQuotient_ker C L N S hExact]
      have hinjective : Function.Injective
          (exactConstantExtensionFunctionAutHom C L N S) := by
        intro g h hgh
        have hp := exactConstantExtensionCombinedAutHom_injective C L N S
          (show exactConstantExtensionCombinedAutHom C L N S
                (1, g) =
              exactConstantExtensionCombinedAutHom C L N S
                (1, h) by
            simpa [exactConstantExtensionCombinedAutHom] using hgh)
        exact congrArg Prod.snd hp
      exact Nat.card_congr (Equiv.ofInjective
        (exactConstantExtensionFunctionAutHom C L N S)
        hinjective).symm

end IntermediateField

end

end BGS.HasseWeil
