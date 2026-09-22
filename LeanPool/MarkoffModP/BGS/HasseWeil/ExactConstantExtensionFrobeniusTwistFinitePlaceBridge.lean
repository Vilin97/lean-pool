/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlaceFrobeniusAverage
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistRiemannLower

/-!
# Finite places of Frobenius-twist fields

This file connects the fixed finite places occurring in Frobenius-coset
averaging with finite places of the corresponding Frobenius-twist fixed
field.  The first step is the arithmetic core of that comparison: every
rational finite place of a twist field has a unique finite place above it in
the exact constant extension.

Indeed, the top residue field contains the enlarged constant field `S`, so
its degree over `C` is divisible by `[S : C]`.  Multiplicativity of place
degree identifies that degree with the relative residue degree above a
rational twist-field place.  Since the entire extension has degree
`[S : C]`, the Galois decomposition formula forces both the number of places
above the rational place and the ramification index to be one.

Only this rational-place-to-fixed-lift direction is asserted here.  The
reverse implication for an arbitrary twist-fixed top place additionally
requires the unramified residue-field descent for the constant extension;
that result is not hidden in the interface below.
-/

open scoped Pointwise Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


variable (C N S : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Field S] [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [Finite S] [DecidableEq S] [DecidableEq (RatFunc S)]

local instance twistBridgeConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance twistBridgeConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

section GenericUniqueFiber

variable (K M T : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)] [Field M] [Field T]
  [Algebra (RatFunc K) M] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
  [Algebra (RatFunc K) T] [FiniteDimensional (RatFunc K) T]
  [Algebra.IsSeparable (RatFunc K) T]
  [Algebra M T] [IsScalarTower (RatFunc K) M T]
  [FiniteDimensional M T] [IsGalois M T]

/-- If every top finite-place degree is divisible by the relative field
degree, then every rational finite place downstairs has a unique place above
it.  The proof uses only degree multiplicativity and the Galois
decomposition formula. -/
theorem rationalFinitePlace_fiber_card_eq_one_of_finrank_dvd_degree
    (hdegree : ∀ Q : FiniteExtensionFinitePlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inl Q))
    (P : FiniteExtensionRationalFinitePlace K M) :
    Fintype.card (FinitePlaceUnderFiber K M T P.1) = 1 := by
  obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective K M T P.1
  let Q₀ : FinitePlaceUnderFiber K M T P.1 := ⟨Q, hQ⟩
  have hplaceDegree :=
    finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M T Q
  have hrelative : finitePlaceRelativeInertiaDeg K M T Q =
      finiteExtensionPlaceDegree K T (.inl Q) := by
    rw [hQ] at hplaceDegree
    simpa [P.2] using hplaceDegree.symm
  have hm_dvd_f : Module.finrank M T ∣
      finitePlaceRelativeInertiaDeg K M T Q := by
    rw [hrelative]
    exact hdegree Q
  have hfiber :=
    finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
      K M T P.1 Q₀
  dsimp [Q₀] at hfiber
  have hf_dvd_m : finitePlaceRelativeInertiaDeg K M T Q ∣
      Module.finrank M T := by
    rw [← hfiber]
    exact dvd_mul_left _ _
  have hf : finitePlaceRelativeInertiaDeg K M T Q =
      Module.finrank M T := Nat.dvd_antisymm hf_dvd_m hm_dvd_f
  have hmpos : 0 < Module.finrank M T := Module.finrank_pos
  have hproduct :
      Fintype.card (FinitePlaceUnderFiber K M T P.1) *
          finitePlaceRelativeRamificationIdx K M T Q = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hmpos
    simpa [Nat.mul_assoc, hf] using hfiber
  exact Nat.eq_one_of_dvd_one
    ⟨finitePlaceRelativeRamificationIdx K M T Q, hproduct.symm⟩

/-- Under the same degree-divisibility hypothesis, every relative Galois
automorphism fixes every finite place above a rational finite place.  This is
the action form of the singleton-fiber theorem. -/
theorem finitePlaceGalSmul_eq_self_over_rationalFinitePlace_of_finrank_dvd_degree
    (hdegree : ∀ Q : FiniteExtensionFinitePlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inl Q))
    (P : FiniteExtensionRationalFinitePlace K M)
    (Q : FiniteExtensionFinitePlace K T)
    (hQ : finitePlaceUnder K M T Q = P.1)
    (sigma : T ≃ₐ[M] T) :
    finitePlaceGalSmul K M T sigma Q = Q := by
  let := finiteIntegralClosureGalAction K M T
  let := finitePlaceUnderFiberGalAction K M T P.1
  have hcard :=
    rationalFinitePlace_fiber_card_eq_one_of_finrank_dvd_degree
      K M T hdegree P
  obtain ⟨Q₀, hQ₀⟩ := Fintype.card_eq_one_iff.mp hcard
  let x : FinitePlaceUnderFiber K M T P.1 := ⟨Q, hQ⟩
  let y : FinitePlaceUnderFiber K M T P.1 :=
    ⟨finitePlaceGalSmul K M T sigma Q, by
      rw [finitePlaceUnder_finitePlaceGalSmul, hQ]⟩
  have hxy : x = y := (hQ₀ x).trans (hQ₀ y).symm
  exact congrArg Subtype.val hxy |>.symm

end GenericUniqueFiber

/-- Every finite place of the exact constant extension, viewed over the
original constants `C`, has degree divisible by `[S : C]`.  This is the
degree-theoretic expression of the inclusion of `S` in every top residue
field. -/
theorem exactConstantExtensionFinitePlace_finrank_constants_dvd_degree
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (Q :
      letI : Field (ExactConstantExtension C N S) :=
        exactConstantExtensionField C N S hExact
      letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
        exactConstantExtensionBaseAlgebra C (RatFunc C) N S
      FiniteExtensionFinitePlace C (ExactConstantExtension C N S)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    Module.finrank C S ∣ finiteExtensionPlaceDegree C
      (ExactConstantExtension C N S) (.inl Q) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : SMul (RatFunc S) T := Algebra.toSMul
  let : Module (RatFunc S) T := Algebra.toModule
  let : FiniteDimensional (RatFunc S) T :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) T :=
    isSeparable_over_extendedRatFunc C S N hExact
  rw [finiteExtensionFinitePlace_degree_baseChange C S T
    (exactConstantExtension_ratFunc_polynomialCompatibility C S N hExact)
    Q]
  exact dvd_mul_right _ _

/-- The Frobenius-twist generator, regarded as an automorphism over its own
fixed field.  Its underlying field automorphism is definitionally the same
twist used in the Frobenius fiber over `C(X)`. -/
noncomputable def exactConstantExtensionFrobeniusTwistOverFixedField
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    ExactConstantExtension C N S ≃ₐ[
      exactConstantExtensionFrobeniusTwistField
        C (RatFunc C) N S hExact g]
      ExactConstantExtension C N S := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let sigma := exactConstantExtensionFrobeniusTwist
    C (RatFunc C) N S hExact g
  let H := exactConstantExtensionFrobeniusTwistSubgroup
    C (RatFunc C) N S hExact g
  exact IntermediateField.subgroupEquivAlgEquiv H
    ⟨sigma, Subgroup.mem_zpowers sigma⟩

@[simp]
theorem exactConstantExtensionFrobeniusTwistOverFixedField_apply
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (x : ExactConstantExtension C N S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    exactConstantExtensionFrobeniusTwistOverFixedField
        C N S hExact g x =
      exactConstantExtensionFrobeniusTwist
        C (RatFunc C) N S hExact g x := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  change
    (exactConstantExtensionFrobeniusTwist
      C (RatFunc C) N S hExact g).toEquiv x =
      exactConstantExtensionFrobeniusTwist
        C (RatFunc C) N S hExact g x
  rfl

/-- A rational finite place of a Frobenius-twist field has exactly one finite
place above it in the exact constant extension. -/
theorem frobeniusTwistField_rationalFinitePlace_fiber_card_eq_one
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
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
    ∀ P : FiniteExtensionRationalFinitePlace C F,
      Fintype.card (FinitePlaceUnderFiber C F
        (ExactConstantExtension C N S) P.1) = 1 := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
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
  dsimp only
  intro P
  apply rationalFinitePlace_fiber_card_eq_one_of_finrank_dvd_degree
    C F T ?_ P
  intro Q
  rw [finrank_exactConstantExtension_over_frobeniusTwistField
    C (RatFunc C) N S hExact g hdiv]
  exact exactConstantExtensionFinitePlace_finrank_constants_dvd_degree
    C N S hExact Q

/-- Every finite-place lift of a rational Frobenius-twist-field place is
fixed by the canonical twist generator over its fixed field. -/
theorem frobeniusTwistField_rationalFinitePlace_lift_fixed
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[RatFunc C] N)
    (hdiv : Nat.card (N ≃ₐ[RatFunc C] N) ∣ Module.finrank C S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc
        C S N hExact
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
    ∀ (P : FiniteExtensionRationalFinitePlace C F)
      (Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S)),
      finitePlaceUnder C F (ExactConstantExtension C N S) Q = P.1 →
        finitePlaceGalSmul C F (ExactConstantExtension C N S)
          (exactConstantExtensionFrobeniusTwistOverFixedField
            C N S hExact g) Q = Q := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
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
  dsimp only
  intro P Q hQ
  apply
    finitePlaceGalSmul_eq_self_over_rationalFinitePlace_of_finrank_dvd_degree
      C F T ?_ P Q hQ
  intro R
  rw [finrank_exactConstantExtension_over_frobeniusTwistField
    C (RatFunc C) N S hExact g hdiv]
  exact exactConstantExtensionFinitePlace_finrank_constants_dvd_degree
    C N S hExact R

section RationalFinitePlaceLifts

variable (K M T : Type*) [Field K] [DecidableEq K]
  [DecidableEq (RatFunc K)] [Field M] [Field T]
  [Algebra (RatFunc K) M] [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
  [Algebra (RatFunc K) T] [FiniteDimensional (RatFunc K) T]
  [Algebra.IsSeparable (RatFunc K) T]
  [Algebra M T] [IsScalarTower (RatFunc K) M T]
  [FiniteDimensional M T] [IsGalois M T]

/-- A rational finite place together with a finite place above it. -/
abbrev RationalFinitePlaceLift :=
  Σ P : FiniteExtensionRationalFinitePlace K M,
    FinitePlaceUnderFiber K M T P.1

/-- If the relative degree divides every top place degree, projection from
rational finite-place lifts is an equivalence.  Equivalently, every rational
finite place has exactly one top lift. -/
noncomputable def rationalFinitePlaceEquivLift
    (hdegree : ∀ Q : FiniteExtensionFinitePlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inl Q)) :
    FiniteExtensionRationalFinitePlace K M ≃
      RationalFinitePlaceLift K M T := by
  let projection : RationalFinitePlaceLift K M T →
      FiniteExtensionRationalFinitePlace K M := fun x => x.1
  refine (Equiv.ofBijective projection ⟨?_, ?_⟩).symm
  · rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
    dsimp only [projection] at h
    subst P'
    have hcard :=
      rationalFinitePlace_fiber_card_eq_one_of_finrank_dvd_degree
        K M T hdegree P
    obtain ⟨Q₀, hQ₀⟩ := Fintype.card_eq_one_iff.mp hcard
    exact Sigma.ext rfl <| heq_of_eq <|
      (hQ₀ Q).trans (hQ₀ Q').symm
  · intro P
    obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective K M T P.1
    exact ⟨⟨P, Q, hQ⟩, rfl⟩

/-- Every top lift of a rational finite place is fixed by every relative
Galois automorphism under the degree-divisibility hypothesis. -/
theorem rationalFinitePlaceLift_fixed
    (hdegree : ∀ Q : FiniteExtensionFinitePlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inl Q))
    (sigma : T ≃ₐ[M] T) (x : RationalFinitePlaceLift K M T) :
    finitePlaceGalSmul K M T sigma x.2.1 = x.2.1 :=
  finitePlaceGalSmul_eq_self_over_rationalFinitePlace_of_finrank_dvd_degree
    K M T hdegree x.1 x.2.1 x.2.2 sigma

/-- Cardinal form of the rational-place/unique-lift correspondence. -/
theorem natCard_rationalFinitePlaceLift_eq
    (hdegree : ∀ Q : FiniteExtensionFinitePlace K T,
      Module.finrank M T ∣ finiteExtensionPlaceDegree K T (.inl Q)) :
    Nat.card (RationalFinitePlaceLift K M T) =
      Nat.card (FiniteExtensionRationalFinitePlace K M) :=
  Nat.card_congr (rationalFinitePlaceEquivLift K M T hdegree).symm

end RationalFinitePlaceLifts

end

end BGS.HasseWeil
