/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionPlaceSplittingMultiplicity
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFinitePlaceFrobeniusAverage
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistFinitePlaceUnramified
public import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlaceTower

/-!
# Finite-place Frobenius-twist averaging over an intermediate base

This file proves the finite-place part of Stichtenoth's Frobenius-twist
average for `C(X) \subseteq L \subseteq N`.
-/

@[expose] public section

open scoped BigOperators Pointwise Polynomial TensorProduct

namespace BGS.HasseWeil

open BGS.CorvajaZannier

private theorem finitePlaceUnder_trans_of_fields
    (C L F T : Type*) [Field C] [Field L] [Field F] [Field T]
    [DecidableEq C] [DecidableEq (RatFunc C)]
    [Algebra (RatFunc C) L] [Algebra (RatFunc C) F] [Algebra (RatFunc C) T]
    [FiniteDimensional (RatFunc C) L] [FiniteDimensional (RatFunc C) F]
    [FiniteDimensional (RatFunc C) T]
    [Algebra.IsSeparable (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) F]
    [Algebra.IsSeparable (RatFunc C) T]
    [Algebra L F] [Algebra F T] [Algebra L T]
    [IsScalarTower (RatFunc C) L F] [IsScalarTower (RatFunc C) L T]
    [IsScalarTower (RatFunc C) F T] [IsScalarTower L F T]
    (Q : FiniteExtensionFinitePlace C T) :
    finitePlaceUnder C L F (finitePlaceUnder C F T Q) = finitePlaceUnder C L T Q := by
  let R₀ := RatFuncFiniteIntegralClosure C L
  let R₁ := RatFuncFiniteIntegralClosure C F
  let R₂ := RatFuncFiniteIntegralClosure C T
  let : Algebra R₀ R₁ := (finiteIntegralClosureMap C L F).toAlgebra
  let : Algebra R₁ R₂ := (finiteIntegralClosureMap C F T).toAlgebra
  let : Algebra R₀ R₂ := (finiteIntegralClosureMap C L T).toAlgebra
  let : SMul R₀ R₁ := Algebra.toSMul
  let : Module R₀ R₁ := Algebra.toModule
  let : SMul R₁ R₂ := Algebra.toSMul
  let : Module R₁ R₂ := Algebra.toModule
  let : SMul R₀ R₂ := Algebra.toSMul
  let : Module R₀ R₂ := Algebra.toModule
  let : IsScalarTower R₀ R₁ R₂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap L T (x : L) =
      algebraMap F T (algebraMap L F (x : L))
    exact IsScalarTower.algebraMap_apply L F T _
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact Ideal.under_under Q.asIdeal

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain


variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance intermediateAverageTopConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance intermediateAverageTopConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance intermediateAverageTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

section IntermediateBase

variable (L : Type*) [Field L]
  [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [Algebra L N] [IsScalarTower (RatFunc C) L N]
  [FiniteDimensional L N] [IsGalois L N]

local instance intermediateAverageBaseConstantAlgebra : Algebra C L :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) L).comp
    (algebraMap C (RatFunc C)))

local instance intermediateAverageConstantTower : IsScalarTower C L N := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
    algebraMap L N
      (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) c))
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N _

local instance intermediateAverageRationalFinitePlaceFintype :
    Fintype (FiniteExtensionRationalFinitePlace C L) := Fintype.ofFinite _

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [Algebra (RatFunc C) L]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [IsScalarTower (RatFunc C) L N] [IsGalois L N] in
/-- The exact constant extension is finite-dimensional over every
intermediate function field `L`. -/
theorem finiteDimensional_exactConstantExtension_over_intermediateBase
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    FiniteDimensional L (ExactConstantExtension C N S) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower L N T :=
    exactConstantExtensionBaseTower C L N S
  let tensorEquiv := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  let : Module.Finite N T := Module.Finite.equiv tensorEquiv
  let : Module.Finite L T := Module.Finite.trans N T
  infer_instance

omit [Fintype C] [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional L N] [IsGalois L N] in
/-- Compatibility of the rational-function and intermediate-base algebra
maps on the exact constant extension. -/
theorem exactConstantExtensionIntermediate_ratFuncBaseTower :
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) := by
  let T := ExactConstantExtension C N S
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  change (1 : S) ⊗ₜ algebraMap (RatFunc C) N x =
    (1 : S) ⊗ₜ algebraMap L N (algebraMap (RatFunc C) L x)
  congr 1
  exact IsScalarTower.algebraMap_apply (RatFunc C) L N x

/-- The rational-function algebra on an intermediate-base Frobenius-twist
field is obtained through `C(X) → L → F_g`. -/
@[implicit_reducible]
noncomputable def intermediateFrobeniusTwistFieldRatFuncAlgebra
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    Algebra (RatFunc C)
      (exactConstantExtensionFrobeniusTwistField C L N S hExact g) := by
  letI : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  letI : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  exact RingHom.toAlgebra
    ((show L →+* F from algebraMap L F).comp
      (show RatFunc C →+* L from algebraMap (RatFunc C) L))

/-- The induced rational-function algebra is compatible with the inclusion
of the twist field into the exact constant extension. -/
theorem intermediateFrobeniusTwistField_ratFunc_tower
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
    letI : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module F (ExactConstantExtension C N S) := Algebra.toModule
    IsScalarTower (RatFunc C) F (ExactConstantExtension C N S) := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : Algebra F T := F.toAlgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : SMul F T := Algebra.toSMul
  let : Module F T := Algebra.toModule
  let : IsScalarTower L F T := IsScalarTower.of_algebraMap_eq' rfl
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  calc
    algebraMap (RatFunc C) T x =
        algebraMap L T (algebraMap (RatFunc C) L x) :=
      IsScalarTower.algebraMap_apply (RatFunc C) L T x
    _ = algebraMap F T (algebraMap L F (algebraMap (RatFunc C) L x)) :=
      IsScalarTower.algebraMap_apply L F T _
    _ = algebraMap F T (algebraMap (RatFunc C) F x) := rfl

/-- Every intermediate-base Frobenius-twist field is a finite function field
over `C(X)`. -/
theorem finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    FiniteDimensional (RatFunc C) F := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : Algebra F T := F.toAlgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : SMul F T := Algebra.toSMul
  let : Module F T := Algebra.toModule
  let : IsScalarTower (RatFunc C) F T :=
    intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
  let : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Module.IsTorsionFree F T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap F T).injective
  exact Module.Finite.left (RatFunc C) F T

/-- Separability of the exact constant extension descends to every
intermediate-base Frobenius-twist field. -/
theorem isSeparable_intermediateFrobeniusTwistField_over_ratFunc
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    Algebra.IsSeparable (RatFunc C) F := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) T := Algebra.toSMul
  let : Module (RatFunc C) T := Algebra.toModule
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : Algebra F T := F.toAlgebra
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : SMul F T := Algebra.toSMul
  let : Module F T := Algebra.toModule
  let : IsScalarTower (RatFunc C) F T :=
    intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
  let : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  exact Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc C) F T

/-- The ambient Frobenius twist regarded as an automorphism over its own
fixed field. -/
noncomputable def intermediateFrobeniusTwistOverFixedField
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    ExactConstantExtension C N S ≃ₐ[
      exactConstantExtensionFrobeniusTwistField C L N S hExact g]
      ExactConstantExtension C N S := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  letI : SMul L T := Algebra.toSMul
  letI : Module L T := Algebra.toModule
  letI : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  let sigma := exactConstantExtensionFrobeniusTwist C L N S hExact g
  let H := exactConstantExtensionFrobeniusTwistSubgroup C L N S hExact g
  exact IntermediateField.subgroupEquivAlgEquiv H
    ⟨sigma, Subgroup.mem_zpowers sigma⟩

@[simp]
theorem intermediateFrobeniusTwistOverFixedField_apply
    (g : N ≃ₐ[L] N) (x : ExactConstantExtension C N S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    intermediateFrobeniusTwistOverFixedField C S N hExact L g x =
      exactConstantExtensionFrobeniusTwist C L N S hExact g x := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  change (exactConstantExtensionFrobeniusTwist
    C L N S hExact g).toEquiv x = _
  rfl

/-- The twist over its fixed field generates the full relative Galois
group. -/
theorem intermediateFrobeniusTwistOverFixedField_zpowers_eq_top
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    Subgroup.zpowers
      (intermediateFrobeniusTwistOverFixedField C S N hExact L g) = ⊤ := by
  let T := ExactConstantExtension C N S
  let : Field T := exactConstantExtensionField C N S hExact
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  let sigma := exactConstantExtensionFrobeniusTwist C L N S hExact g
  let H := exactConstantExtensionFrobeniusTwistSubgroup C L N S hExact g
  let e := IntermediateField.subgroupEquivAlgEquiv H
  let u : H := ⟨sigma, Subgroup.mem_zpowers sigma⟩
  change Subgroup.zpowers (e u) = ⊤
  apply (Subgroup.eq_top_iff' _).mpr
  intro tau
  let h : H := e.symm tau
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  calc
    (e u) ^ k = e (u ^ k) := (map_zpow e u k).symm
    _ = e h := congrArg e (Subtype.ext hk)
    _ = tau := e.apply_symm_apply tau

omit [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [FiniteDimensional L N] [IsGalois L N] in
omit [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] in
/-- A power of the generic intermediate-base twist acts on the enlarged
constants by the same power of finite-field Frobenius. -/
private theorem intermediateFrobeniusTwist_zpow_includeLeft
    (g : N ≃ₐ[L] N) (k : ℤ) (s : S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    ((exactConstantExtensionFrobeniusTwist C L N S hExact g) ^ k)
        (Algebra.TensorProduct.includeLeft
          (R := C) (S := C) (A := S) (B := N) s) =
      Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N)
        (((FiniteField.frobeniusAlgEquivOfAlgebraic C S) ^ k) s) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  change
    ((exactConstantExtensionCombinedAutHom C L N S
      (FiniteField.frobeniusAlgEquivOfAlgebraic C S, g)) ^ k)
      (Algebra.TensorProduct.includeLeft
        (R := C) (S := C) (A := S) (B := N) s) = _
  rw [← map_zpow]
  simp [Algebra.TensorProduct.includeLeft_apply,
    exactConstantExtensionCombinedAutHom,
    exactConstantExtensionConstantAutHom,
    exactConstantExtensionFunctionAutHom,
    exactConstantExtensionConstantAlgEquivOverBase,
    exactConstantExtensionFunctionAlgEquivOverBase]

/-- Every finite place of the exact constant extension is unramified over an
intermediate-base Frobenius-twist fixed field. -/
theorem intermediateFrobeniusTwistField_finitePlace_ramificationIdx_eq_one
    (g : N ≃ₐ[L] N)
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    let : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    let : SMul (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toSMul
    let : Module (RatFunc C) (ExactConstantExtension C N S) :=
      Algebra.toModule
    let : FiniteDimensional (RatFunc C)
        (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    let : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    let : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    let : SMul (RatFunc C) F := Algebra.toSMul
    let : Module (RatFunc C) F := Algebra.toModule
    let : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra F (ExactConstantExtension C N S) := F.toAlgebra
    let : SMul F (ExactConstantExtension C N S) := Algebra.toSMul
    let : Module F (ExactConstantExtension C N S) := Algebra.toModule
    let : IsScalarTower (RatFunc C) F
        (ExactConstantExtension C N S) :=
      intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
    let : FiniteDimensional F (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    let : IsGalois F (ExactConstantExtension C N S) :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finitePlaceRelativeRamificationIdx C F
        (ExactConstantExtension C N S) Q = 1 := by
  intro model0 model1 model2 model3 model4 model5 model6 F model8 model9 model10 model11 model12
    model13 model14 model15 model16 model17 model18
  let T := ExactConstantExtension C N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase C S N L hExact
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra C[X] F :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) F).comp (algebraMap C[X] (RatFunc C)))
  let : IsScalarTower C[X] (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C[X] T :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) T).comp (algebraMap C[X] (RatFunc C)))
  let : IsScalarTower C[X] (RatFunc C) T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let A := RatFuncFiniteIntegralClosure C T
  let AF := RatFuncFiniteIntegralClosure C F
  let : Algebra AF A := (finiteIntegralClosureMap C F T).toAlgebra
  let : SMul AF A := Algebra.toSMul
  let : Module AF A := Algebra.toModule
  let : Algebra S A :=
    exactConstantExtensionFiniteIntegralClosureConstantAlgebra C N S hExact
  let : IsScalarTower AF F T := inferInstance
  let : Algebra.IsIntegral C[X] AF :=
    IsIntegralClosure.isIntegral_algebra C[X] F
  let : IsScalarTower C[X] AF T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap (RatFunc C) T
          (algebraMap C[X] (RatFunc C) x) =
      algebraMap F T
        (algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) x))
    exact IsScalarTower.algebraMap_apply (RatFunc C) F T _
  let : IsScalarTower AF A T :=
    ⟨fun r t x => by
      simp only [Algebra.smul_def, map_mul]
      rw [show algebraMap A T (algebraMap AF A r) =
          algebraMap AF T r by rfl]
      ring⟩
  let : IsIntegralClosure A AF T :=
    IsIntegralClosure.tower_top (R := C[X])
  let : IsDedekindDomain A := inferInstance
  let : MulSemiringAction (T ≃ₐ[F] T) A :=
    finiteIntegralClosureGalAction C F T
  intro Q
  let : Q.asIdeal.IsMaximal := Q.isMaximal
  rw [← finitePlaceInertiaGroup_card_eq_ramificationIdx C F T Q]
  have hInertia : finitePlaceInertiaGroup C F T Q = ⊥ := by
    ext tau
    constructor
    · intro htau
      rw [Subgroup.mem_bot]
      let sigma := exactConstantExtensionFrobeniusTwist C L N S hExact g
      let H := exactConstantExtensionFrobeniusTwistSubgroup C L N S hExact g
      let e := IntermediateField.subgroupEquivAlgEquiv H
      let h : H := e.symm tau
      have he_apply (z : H) (x : T) : e z x = z.1 x := by
        change z.1.toEquiv x = z.1 x
        rfl
      have htau_apply (x : T) : tau x = h.1 x := by
        calc
          tau x = e h x := by
            exact congrArg (fun z : T ≃ₐ[F] T => z x)
              (e.apply_symm_apply tau).symm
          _ = h.1 x := he_apply h x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
      let frob := FiniteField.frobeniusAlgEquivOfAlgebraic C S
      have hfrob_apply (s : S) : (frob ^ k) s = s := by
        let a : A := algebraMap S A s
        have haction : tau • a = algebraMap S A ((frob ^ k) s) := by
          apply Subtype.ext
          calc
            ((tau • a : A) : T) = tau (a : T) := by
              change algebraMap A T ((galRestrict AF F T A tau) a) =
                tau (algebraMap A T a)
              exact algebraMap_galRestrict_apply AF tau a
            _ = h.1 (a : T) := htau_apply (a : T)
            _ = h.1 (Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N) s) := by
              exact congrArg h.1
                (exactConstantExtensionFiniteIntegralClosure_algebraMap_val
                  C N S hExact s)
            _ = (sigma ^ k) (Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N) s) := by
              exact congrArg
                (fun z : T ≃ₐ[L] T => z (Algebra.TensorProduct.includeLeft
                  (R := C) (S := C) (A := S) (B := N) s)) hk |>.symm
            _ = Algebra.TensorProduct.includeLeft
                (R := C) (S := C) (A := S) (B := N) ((frob ^ k) s) :=
              intermediateFrobeniusTwist_zpow_includeLeft
                C S N hExact L g k s
            _ = ((algebraMap S A ((frob ^ k) s) : A) : T) :=
              (exactConstantExtensionFiniteIntegralClosure_algebraMap_val
                C N S hExact ((frob ^ k) s)).symm
        have hmem : tau • a - a ∈ Q.asIdeal := htau a
        have hmem' : algebraMap S A ((frob ^ k) s - s) ∈ Q.asIdeal := by
          have heq : algebraMap S A ((frob ^ k) s - s) = tau • a - a := by
            calc
              algebraMap S A ((frob ^ k) s - s) =
                  algebraMap S A ((frob ^ k) s) - algebraMap S A s :=
                map_sub (algebraMap S A) _ _
              _ = algebraMap S A ((frob ^ k) s) - a := rfl
              _ = tau • a - a := congrArg (fun z : A => z - a) haction.symm
          exact heq.symm ▸ hmem
        let J : Ideal S := Q.asIdeal.comap (algebraMap S A)
        have hmemJ : (frob ^ k) s - s ∈ J := hmem'
        have hJne : J ≠ ⊤ :=
          Ideal.comap_ne_top (algebraMap S A) Q.isPrime.ne_top
        have hJ : J = ⊥ := (Ideal.eq_bot_or_top J).resolve_right hJne
        have hs : (frob ^ k) s - s = 0 := by
          rw [hJ] at hmemJ
          simpa only [Ideal.mem_bot] using hmemJ
        exact sub_eq_zero.mp hs
      have hFrob : frob ^ k = 1 := by
        ext s
        exact hfrob_apply s
      have hkdiv : (Module.finrank C S : ℤ) ∣ k := by
        rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic C S]
        exact orderOf_dvd_iff_zpow_eq_one.mpr hFrob
      have hsigma : sigma ^ k = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one,
          orderOf_exactConstantExtensionFrobeniusTwist
            C L N S hExact g hdiv]
        exact hkdiv
      have hambient : (h.1 : T ≃ₐ[L] T) = 1 := by
        calc
          (h.1 : T ≃ₐ[L] T) = sigma ^ k := hk.symm
          _ = 1 := hsigma
      have hh : h = 1 := Subtype.ext hambient
      exact (e.apply_symm_apply tau).symm.trans
        ((congrArg e hh).trans (map_one e))
    · intro htau
      rw [Subgroup.mem_bot] at htau
      simp [htau]
  rw [hInertia]
  exact Nat.card_unique

/-- Restriction of an exact-constant-extension finite place through `N`
agrees with direct restriction to the intermediate field `L`. -/
private theorem finitePlaceUnder_intermediate_original
    :
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
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    letI : Algebra N (ExactConstantExtension C N S) :=
      exactConstantExtensionAlgebra C N S
    letI : SMul N (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module N (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N
        (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finitePlaceUnder C L N
          (finitePlaceUnder C N (ExactConstantExtension C N S) Q) =
        finitePlaceUnder C L (ExactConstantExtension C N S) Q := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsScalarTower L N T :=
    exactConstantExtensionBaseTower C L N S
  let R₀ := RatFuncFiniteIntegralClosure C L
  let R₁ := RatFuncFiniteIntegralClosure C N
  let R₂ := RatFuncFiniteIntegralClosure C T
  let : Algebra R₀ R₁ := (finiteIntegralClosureMap C L N).toAlgebra
  let : Algebra R₁ R₂ := (finiteIntegralClosureMap C N T).toAlgebra
  let : Algebra R₀ R₂ := (finiteIntegralClosureMap C L T).toAlgebra
  let : SMul R₀ R₁ := Algebra.toSMul
  let : Module R₀ R₁ := Algebra.toModule
  let : SMul R₁ R₂ := Algebra.toSMul
  let : Module R₁ R₂ := Algebra.toModule
  let : SMul R₀ R₂ := Algebra.toSMul
  let : Module R₀ R₂ := Algebra.toModule
  let : IsScalarTower R₀ R₁ R₂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap L T (x : L) =
      algebraMap N T (algebraMap L N (x : L))
    exact IsScalarTower.algebraMap_apply L N T _
  intro Q
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact Ideal.under_under Q.asIdeal

/-- Choose an `S[X]`-presentation of a top finite place while transporting
rationality of its restriction to the intermediate field `L`. -/
private theorem exists_presentedFinitePlace_of_under_intermediate_rational :
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
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finiteExtensionPlaceDegree C L
          (.inl (finitePlaceUnder C L (ExactConstantExtension C N S) Q)) = 1 →
        ∃ q : IsDedekindDomain.HeightOneSpectrum
            (integralClosure S[X] (ExactConstantExtension C N S)),
          exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q = Q ∧
            finiteExtensionPlaceDegree C L
              (.inl (finitePlaceUnder C L N
                (exactConstantExtensionDownstairsFinitePlace
                  C S N hExact q))) = 1 := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
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
      exactConstantExtensionCompatibleBaseFinitePlace C S N hExact q = e q :=
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
  refine ⟨q, heq, ?_⟩
  rw [← hDownstairs,
    finitePlaceUnder_intermediate_original C S N hExact L Q]
  exact hBase

/-- Every top finite place over a rational finite place of `L` has absolute
degree `[S : C]` when `[N : L]` divides the constant-extension degree. -/
theorem exactConstantExtensionFinitePlace_degree_eq_finrank_of_under_intermediate_rational
    (hDegreeDiv : Module.finrank L N ∣ Module.finrank C S) :
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
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finiteExtensionPlaceDegree C L
          (.inl (finitePlaceUnder C L (ExactConstantExtension C N S) Q)) = 1 →
        finiteExtensionPlaceDegree C (ExactConstantExtension C N S) (.inl Q) =
          Module.finrank C S := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let : Algebra N T := exactConstantExtensionAlgebra C N S
  let : SMul N T := Algebra.toSMul
  let : Module N T := Algebra.toModule
  let : IsScalarTower (RatFunc C) N T :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : IsScalarTower L N T := exactConstantExtensionBaseTower C L N S
  let : Algebra (RatFunc S) T :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) T := Algebra.toSMul
  let : Module (RatFunc S) T := Algebra.toModule
  let : FiniteDimensional (RatFunc S) T :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) T :=
    isSeparable_over_extendedRatFunc C S N hExact
  intro Q hBase
  obtain ⟨q, heq, hBaseQ⟩ :=
    exists_presentedFinitePlace_of_under_intermediate_rational
      C S N hExact L Q hBase
  let P := exactConstantExtensionDownstairsFinitePlace C S N hExact q
  let P₀ := finitePlaceUnder C L N P
  have hInertiaDiv : finitePlaceRelativeInertiaDeg C L N P ∣
      Module.finrank L N := by
    let PInFiber : FinitePlaceUnderFiber C L N P₀ := ⟨P, rfl⟩
    have hFiber :=
      finitePlaceUnderFiber_card_mul_ramificationIdx_mul_inertiaDeg_eq_field_finrank
        C L N P₀ PInFiber
    refine ⟨Fintype.card (FinitePlaceUnderFiber C L N P₀) *
      finitePlaceRelativeRamificationIdx C L N P, ?_⟩
    simpa [PInFiber, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hFiber.symm
  have hDownDegreeEq : finiteExtensionPlaceDegree C N (.inl P) =
      finitePlaceRelativeInertiaDeg C L N P := by
    have hDegree := finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg
      C L N P
    simpa [P₀, P, hBaseQ] using hDegree
  have hDownDegreeDiv : finiteExtensionPlaceDegree C N (.inl P) ∣
      Module.finrank C S := by
    rw [hDownDegreeEq]
    exact hInertiaDiv.trans hDegreeDiv
  have hUpstairsRational :
      finiteExtensionPlaceDegree S T
        (.inl (exactConstantExtensionUpstairsFinitePlace C S N hExact q)) = 1 := by
    rw [exactConstantExtensionFinitePlace_degree_eq_div_gcd
      C S N hExact q,
      (Nat.gcd_eq_right_iff_dvd).2 hDownDegreeDiv]
    exact Nat.div_self (finiteExtensionPlaceDegree_pos C N (.inl P))
  have hTop := exactConstantExtensionCompatibleBaseFinitePlace_degree_eq
    C S N hExact q hUpstairsRational
  rw [heq] at hTop
  exact hTop

/-- Presentation-free local Frobenius-coset identity over a rational finite
place of the intermediate field `L`. -/
theorem exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum_of_under_intermediate_rational
    (hDegreeDiv : Module.finrank L N ∣ Module.finrank C S) :
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
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C)
        (ExactConstantExtension C N S) :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L
        (ExactConstantExtension C N S) :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    letI : FiniteDimensional L (ExactConstantExtension C N S) :=
      finiteDimensional_exactConstantExtension_over_intermediateBase
        C S N L hExact
    letI : IsGalois L (ExactConstantExtension C N S) :=
      exactConstantExtension_isGalois C L N S hExact
    ∀ Q : FiniteExtensionFinitePlace C (ExactConstantExtension C N S),
      finiteExtensionPlaceDegree C L
          (.inl (finitePlaceUnder C L (ExactConstantExtension C N S) Q)) = 1 →
      let P := finitePlaceUnder C L (ExactConstantExtension C N S) Q
      let pi := exactConstantExtensionConstantQuotient C L N S hExact
      letI : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
      letI : Fintype (ExactConstantExtension C N S ≃ₐ[L]
          ExactConstantExtension C N S) := Fintype.ofFinite _
      letI : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
      letI : Fintype
          (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
            Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
      letI := finiteIntegralClosureGalAction C L
        (ExactConstantExtension C N S)
      letI := finitePlaceUnderFiberGalAction C L
        (ExactConstantExtension C N S) P
      (∑ g : pi ⁻¹'
          ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
            Set (S ≃ₐ[C] S)),
        Nat.card (MulAction.fixedBy
          (FinitePlaceUnderFiber C L (ExactConstantExtension C N S) P)
          g.1)) =
        Nat.card (N ≃ₐ[L] N) := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  let : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
  intro Q hBase
  obtain ⟨q, heq, hBaseQ⟩ :=
    exists_presentedFinitePlace_of_under_intermediate_rational
      C S N hExact L Q hBase
  rw [← heq]
  exact exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum
    C S N hExact L q hBaseQ hDegreeDiv

omit [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] in
/-- The Frobenius-fiber parametrization sends `g` to the ambient twist
`(Frob, g)` over the intermediate field. -/
@[simp]
theorem intermediate_exactConstantExtensionFrobeniusFiberEquiv_apply_val
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    ((exactConstantExtensionFrobeniusFiberEquiv
        C L N S hExact) g).1 =
      exactConstantExtensionFrobeniusTwist C L N S hExact g := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  rfl

/-- Fixed top finite places in the restriction fiber above one rational
finite place of `L`, for one intermediate-base Frobenius twist. -/
abbrev IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
    (g : N ≃ₐ[L] N) (P : FiniteExtensionRationalFinitePlace C L) : Type _ :=
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  letI : SMul L T := Algebra.toSMul
  letI : Module L T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  letI : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  letI : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
  @MulAction.fixedBy (T ≃ₐ[L] T) (FinitePlaceUnderFiber C L T P.1) _
    (finitePlaceUnderFiberGalAction C L T P.1)
    (exactConstantExtensionFrobeniusTwist C L N S hExact g)

/-- Above one rational finite place of `L`, summing fixed top places over all
intermediate-base Frobenius twists contributes exactly `|Gal(N/L)|`. -/
theorem sum_card_finitePlaceUnderFiber_fixedBy_intermediateFrobeniusTwist_eq_card_galois
    (hDegreeDiv : Module.finrank L N ∣ Module.finrank C S)
    (P : FiniteExtensionRationalFinitePlace C L) :
    (∑ g : N ≃ₐ[L] N,
      Nat.card (IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
        C S N hExact L g P)) = Nat.card (N ≃ₐ[L] N) := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  let : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
  let : Fintype (T ≃ₐ[L] T) := Fintype.ofFinite _
  let := finiteIntegralClosureGalAction C L T
  let := finitePlaceUnderFiberGalAction C L T P.1
  let pi := exactConstantExtensionConstantQuotient C L N S hExact
  let : DecidableEq (S ≃ₐ[C] S) := Classical.decEq _
  let : Fintype (S ≃ₐ[C] S) := Fintype.ofFinite _
  let : Fintype
      (pi ⁻¹' ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
        Set (S ≃ₐ[C] S))) := Fintype.ofFinite _
  obtain ⟨Q, hQ⟩ := finitePlaceUnder_surjective C L T P.1
  have hBase : finiteExtensionPlaceDegree C L
      (.inl (finitePlaceUnder C L T Q)) = 1 := by
    rw [hQ]
    exact P.2
  have hlocal :=
    exactConstantExtensionFinitePlace_frobeniusFiber_fixedPoint_sum_of_under_intermediate_rational
      C S N hExact L hDegreeDiv Q hBase
  rw [hQ] at hlocal
  let e := exactConstantExtensionFrobeniusFiberEquiv C L N S hExact
  calc
    (∑ g : N ≃ₐ[L] N,
        Nat.card (IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
          C S N hExact L g P)) =
        ∑ g : N ≃ₐ[L] N,
          Nat.card (MulAction.fixedBy
            (FinitePlaceUnderFiber C L T P.1) (e g).1) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [intermediate_exactConstantExtensionFrobeniusFiberEquiv_apply_val]
    _ = ∑ x : pi ⁻¹'
          ({FiniteField.frobeniusAlgEquivOfAlgebraic C S} :
            Set (S ≃ₐ[C] S)),
          Nat.card (MulAction.fixedBy
            (FinitePlaceUnderFiber C L T P.1) x.1) :=
      e.sum_comp (fun x ↦ Nat.card (MulAction.fixedBy
        (FinitePlaceUnderFiber C L T P.1) x.1))
    _ = Nat.card (N ≃ₐ[L] N) := hlocal

/-- Rational finite places of an intermediate-base twist field are exactly
the degree-`[S : C]` top finite places fixed by its ambient Frobenius twist. -/
noncomputable def
    intermediateFrobeniusTwistField_rationalFinitePlace_equiv_ambientFixedFinitePlace
    (g : N ≃ₐ[L] N)
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) T :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) T := Algebra.toSMul
    letI : Module (RatFunc C) T := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) T :=
      finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra.IsSeparable (RatFunc C) T :=
      isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
    letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L T := Algebra.toSMul
    letI : Module L T := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L T :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    letI : FiniteDimensional L T :=
      finiteDimensional_exactConstantExtension_over_intermediateBase
        C S N L hExact
    letI : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
    letI : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : SMul (RatFunc C) F := Algebra.toSMul
    letI : Module (RatFunc C) F := Algebra.toModule
    letI : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    letI : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    letI : Algebra F T := F.toAlgebra
    letI : SMul F T := Algebra.toSMul
    letI : Module F T := Algebra.toModule
    letI : IsScalarTower (RatFunc C) F T :=
      intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
    letI : FiniteDimensional F T :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    letI : IsGalois F T :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    FiniteExtensionRationalFinitePlace C F ≃
      {Q : FiniteExtensionFinitePlace C T //
        finiteExtensionPlaceDegree C T (.inl Q) = Module.finrank C S ∧
          finitePlaceGalSmul C L T
            (exactConstantExtensionFrobeniusTwist C L N S hExact g) Q = Q} := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) T :=
    finiteDimensional_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc C) T :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  letI : SMul L T := Algebra.toSMul
  letI : Module L T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  letI : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  letI : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  letI : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  letI : SMul L F := Algebra.toSMul
  letI : Module L F := Algebra.toModule
  letI : IsScalarTower (RatFunc C) L F :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  letI : Algebra F T := F.toAlgebra
  letI : SMul F T := Algebra.toSMul
  letI : Module F T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) F T :=
    intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
  letI : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g
  letI : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g
  have hfinrank : Module.finrank F T = Module.finrank C S :=
    finrank_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g hdiv
  have hdegree : ∀ Q : FiniteExtensionFinitePlace C T,
      Module.finrank F T ∣ finiteExtensionPlaceDegree C T (.inl Q) := by
    intro Q
    rw [hfinrank]
    exact exactConstantExtensionFinitePlace_finrank_constants_dvd_degree
      C N S hExact Q
  let sigmaF := intermediateFrobeniusTwistOverFixedField
    C S N hExact L g
  let sigmaL := exactConstantExtensionFrobeniusTwist C L N S hExact g
  let eFixed := rationalFinitePlaceEquivGeneratorFixedPlace
    C F T hdegree sigmaF
      (intermediateFrobeniusTwistOverFixedField_zpowers_eq_top
        C S N hExact L g)
      (intermediateFrobeniusTwistField_finitePlace_ramificationIdx_eq_one
        C S N hExact L g hdiv)
  let eCompare :
      {Q : FiniteExtensionFinitePlace C T //
        finiteExtensionPlaceDegree C T (.inl Q) = Module.finrank F T ∧
          finitePlaceGalSmul C F T sigmaF Q = Q} ≃
      {Q : FiniteExtensionFinitePlace C T //
        finiteExtensionPlaceDegree C T (.inl Q) = Module.finrank C S ∧
          finitePlaceGalSmul C L T sigmaL Q = Q} :=
    { toFun := fun Q ↦ ⟨Q.1, Q.2.1.trans hfinrank,
        (finitePlaceGalSmul_eq_of_apply_eq C F L T sigmaF sigmaL
          (fun x ↦ intermediateFrobeniusTwistOverFixedField_apply
            C S N hExact L g x) Q.1).symm.trans Q.2.2⟩
      invFun := fun Q ↦ ⟨Q.1, Q.2.1.trans hfinrank.symm,
        (finitePlaceGalSmul_eq_of_apply_eq C F L T sigmaF sigmaL
          (fun x ↦ intermediateFrobeniusTwistOverFixedField_apply
            C S N hExact L g x) Q.1).trans Q.2.2⟩
      left_inv := fun Q ↦ Subtype.ext rfl
      right_inv := fun Q ↦ Subtype.ext rfl }
  exact eFixed.trans eCompare

/-- Restriction through an intermediate Frobenius-twist field agrees with
direct restriction to `L`. -/
theorem finitePlaceUnder_intermediateFrobeniusTwist_under
    (g : N ≃ₐ[L] N) :
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
    let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
    let : SMul L T := Algebra.toSMul
    let : Module L T := Algebra.toModule
    let : IsScalarTower (RatFunc C) L T :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
    let : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    let : SMul L F := Algebra.toSMul
    let : Module L F := Algebra.toModule
    let : IsScalarTower (RatFunc C) L F :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : SMul (RatFunc C) F := Algebra.toSMul
    let : Module (RatFunc C) F := Algebra.toModule
    let : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra F T := F.toAlgebra
    let : SMul F T := Algebra.toSMul
    let : Module F T := Algebra.toModule
    let : IsScalarTower (RatFunc C) F T :=
      intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
    ∀ Q : FiniteExtensionFinitePlace C T,
      finitePlaceUnder C L F (finitePlaceUnder C F T Q) =
        finitePlaceUnder C L T Q := by
  intro T model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 F model12 model13
    model14 model15 model16 model17 model18 model19 model20 model21 model22 model23 model24
  let : IsScalarTower L F T := IsScalarTower.of_algebraMap_eq' rfl
  exact finitePlaceUnder_trans_of_fields C L F T

/-- Rational finite places of one intermediate-base twist field are the
disjoint union, over rational finite places of `L`, of fixed top places in
the corresponding restriction fiber. -/
noncomputable def
    intermediateFrobeniusTwistField_rationalFinitePlace_equiv_sigma_fiberFixedBy
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[L] N) :
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
    let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
    let : SMul L T := Algebra.toSMul
    let : Module L T := Algebra.toModule
    let : IsScalarTower (RatFunc C) L T :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    let : FiniteDimensional L T :=
      finiteDimensional_exactConstantExtension_over_intermediateBase
        C S N L hExact
    let : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
    let : Algebra (RatFunc C) F :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    let : SMul L F := Algebra.toSMul
    let : Module L F := Algebra.toModule
    let : IsScalarTower (RatFunc C) L F :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : SMul (RatFunc C) F := Algebra.toSMul
    let : Module (RatFunc C) F := Algebra.toModule
    let : FiniteDimensional (RatFunc C) F :=
      finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra.IsSeparable (RatFunc C) F :=
      isSeparable_intermediateFrobeniusTwistField_over_ratFunc
        C S N hExact L g
    let : Algebra F T := F.toAlgebra
    let : SMul F T := Algebra.toSMul
    let : Module F T := Algebra.toModule
    let : IsScalarTower (RatFunc C) F T :=
      intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
    let : FiniteDimensional F T :=
      finiteDimensional_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    let : IsGalois F T :=
      isGalois_exactConstantExtension_over_frobeniusTwistField
        C L N S hExact g
    FiniteExtensionRationalFinitePlace C F ≃
      Σ P : FiniteExtensionRationalFinitePlace C L,
        IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
          C S N hExact L g P := by
  intro T model1 model2 model3 model4 model5 model6 model7 model8 model9 model10 model11 model12 F
    model14 model15 model16 model17 model18 model19 model20 model21 model22 model23 model24
    model25 model26 model27 model28
  let : IsScalarTower L F T := IsScalarTower.of_algebraMap_eq' rfl
  have hDegreeDiv : Module.finrank L N ∣ Module.finrank C S := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hdiv
  have hfinrank : Module.finrank F T = Module.finrank C S :=
    finrank_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g hdiv
  let sigmaF := intermediateFrobeniusTwistOverFixedField
    C S N hExact L g
  let sigmaL := exactConstantExtensionFrobeniusTwist C L N S hExact g
  let AmbientFixed :=
    {Q : FiniteExtensionFinitePlace C T //
      finiteExtensionPlaceDegree C T (.inl Q) = Module.finrank C S ∧
        finitePlaceGalSmul C L T sigmaL Q = Q}
  let SigmaFixed := Σ P : FiniteExtensionRationalFinitePlace C L,
    IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
      C S N hExact L g P
  let toAmbient : SigmaFixed → AmbientFixed := fun x ↦ by
    let Q := x.2.1.1
    have hBase : finiteExtensionPlaceDegree C L
        (.inl (finitePlaceUnder C L T Q)) = 1 := by
      rw [x.2.1.2]
      exact x.1.2
    refine ⟨Q,
      exactConstantExtensionFinitePlace_degree_eq_finrank_of_under_intermediate_rational
        C S N hExact L hDegreeDiv Q hBase, ?_⟩
    exact congrArg Subtype.val x.2.2
  have hInjective : Function.Injective toAmbient := by
    rintro ⟨P, x⟩ ⟨R, y⟩ hxy
    have hQ : x.1.1 = y.1.1 := congrArg Subtype.val hxy
    have hBase : P.1 = R.1 := by
      calc
        P.1 = finitePlaceUnder C L T x.1.1 := x.1.2.symm
        _ = finitePlaceUnder C L T y.1.1 := congrArg _ hQ
        _ = R.1 := y.1.2
    have hP : P = R := Subtype.ext hBase
    subst R
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    apply Subtype.ext
    exact hQ
  have hSurjective : Function.Surjective toAmbient := by
    intro z
    let Q := z.1
    have hfixedF : finitePlaceGalSmul C F T sigmaF Q = Q :=
      (finitePlaceGalSmul_eq_of_apply_eq C F L T sigmaF sigmaL
        (fun x ↦ intermediateFrobeniusTwistOverFixedField_apply
          C S N hExact L g x) Q).trans z.2.2
    have hFdegree : finiteExtensionPlaceDegree C F
        (.inl (finitePlaceUnder C F T Q)) = 1 :=
      finitePlaceUnder_degree_eq_one_of_generator_fixed C F T sigmaF
        (intermediateFrobeniusTwistOverFixedField_zpowers_eq_top
          C S N hExact L g) Q hfixedF
        (intermediateFrobeniusTwistField_finitePlace_ramificationIdx_eq_one
          C S N hExact L g hdiv Q)
        (z.2.1.trans hfinrank.symm)
    let R₀ : FiniteExtensionRationalFinitePlace C F :=
      ⟨finitePlaceUnder C F T Q, hFdegree⟩
    let P : FiniteExtensionRationalFinitePlace C L :=
      rationalFinitePlaceUnder C L F R₀
    have hFiber : finitePlaceUnder C L T Q = P.1 := by
      calc
        finitePlaceUnder C L T Q =
            finitePlaceUnder C L F (finitePlaceUnder C F T Q) :=
          (finitePlaceUnder_intermediateFrobeniusTwist_under
            C S N hExact L g Q).symm
        _ = P.1 := rfl
    let xFiber : FinitePlaceUnderFiber C L T P.1 := ⟨Q, hFiber⟩
    let xFixed : IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
        C S N hExact L g P := ⟨xFiber, by
      apply Subtype.ext
      exact z.2.2⟩
    refine ⟨⟨P, xFixed⟩, ?_⟩
    apply Subtype.ext
    change Q = z.1
    rfl
  let eSigma : SigmaFixed ≃ AmbientFixed :=
    Equiv.ofBijective toAmbient ⟨hInjective, hSurjective⟩
  exact
    (intermediateFrobeniusTwistField_rationalFinitePlace_equiv_ambientFixedFinitePlace
      C S N hExact L g hdiv).trans eSigma.symm

/-- The rational finite-place count of one intermediate-base Frobenius-twist
field, with its rational-function algebra fixed explicitly. -/
noncomputable def intermediateFrobeniusTwistFieldRationalFinitePlaceCount
    (g : N ≃ₐ[L] N) : ℕ :=
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  letI : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  letI : SMul (RatFunc C) F := Algebra.toSMul
  letI : Module (RatFunc C) F := Algebra.toModule
  letI : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  letI : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  Nat.card (FiniteExtensionRationalFinitePlace C F)

/-- For one twist, rational finite places split as the finite sum of fixed
restriction fibers above the rational finite places of `L`. -/
theorem intermediateFrobeniusTwistFieldRationalFinitePlaceCount_eq_sum_fiberFixedBy
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S)
    (g : N ≃ₐ[L] N) :
    intermediateFrobeniusTwistFieldRationalFinitePlaceCount
        C S N hExact L g =
      ∑ P : FiniteExtensionRationalFinitePlace C L,
        Nat.card (IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
          C S N hExact L g P) := by
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
  let : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  let : SMul L T := Algebra.toSMul
  let : Module L T := Algebra.toModule
  let : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let : FiniteDimensional L T :=
    finiteDimensional_exactConstantExtension_over_intermediateBase
      C S N L hExact
  let : IsGalois L T := exactConstantExtension_isGalois C L N S hExact
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let : Algebra L F := SubalgebraClass.toAlgebra F.toSubalgebra
  let : Algebra (RatFunc C) F :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  let : SMul (RatFunc C) F := Algebra.toSMul
  let : Module (RatFunc C) F := Algebra.toModule
  let : FiniteDimensional (RatFunc C) F :=
    finiteDimensional_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Algebra.IsSeparable (RatFunc C) F :=
    isSeparable_intermediateFrobeniusTwistField_over_ratFunc
      C S N hExact L g
  let : Algebra F T := F.toAlgebra
  let : SMul F T := Algebra.toSMul
  let : Module F T := Algebra.toModule
  let : IsScalarTower (RatFunc C) F T :=
    intermediateFrobeniusTwistField_ratFunc_tower C S N hExact L g
  let : FiniteDimensional F T :=
    finiteDimensional_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g
  let : IsGalois F T :=
    isGalois_exactConstantExtension_over_frobeniusTwistField
      C L N S hExact g
  change Nat.card (FiniteExtensionRationalFinitePlace C F) = _
  rw [Nat.card_congr
    (intermediateFrobeniusTwistField_rationalFinitePlace_equiv_sigma_fiberFixedBy
      C S N hExact L hdiv g), Nat.card_sigma]

/-- Summed over all intermediate-base Frobenius twists, the rational finite
place count is exactly `|Gal(N/L)|` times the rational finite-place count of
`L`. -/
theorem sum_intermediateFrobeniusTwistFieldRationalFinitePlaceCount_eq_card_galois_mul_card
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    (∑ g : N ≃ₐ[L] N,
      intermediateFrobeniusTwistFieldRationalFinitePlaceCount
        C S N hExact L g) =
      Nat.card (N ≃ₐ[L] N) *
        Nat.card (FiniteExtensionRationalFinitePlace C L) := by
  have hDegreeDiv : Module.finrank L N ∣ Module.finrank C S := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hdiv
  calc
    (∑ g : N ≃ₐ[L] N,
        intermediateFrobeniusTwistFieldRationalFinitePlaceCount
          C S N hExact L g) =
        ∑ g : N ≃ₐ[L] N,
          ∑ P : FiniteExtensionRationalFinitePlace C L,
            Nat.card (IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
              C S N hExact L g P) := by
      apply Finset.sum_congr rfl
      intro g _
      exact
        intermediateFrobeniusTwistFieldRationalFinitePlaceCount_eq_sum_fiberFixedBy
          C S N hExact L hdiv g
    _ = ∑ P : FiniteExtensionRationalFinitePlace C L,
          ∑ g : N ≃ₐ[L] N,
            Nat.card (IntermediateFrobeniusTwistFinitePlaceFiberFixedBy
              C S N hExact L g P) := by
      rw [Finset.sum_comm]
    _ = ∑ _P : FiniteExtensionRationalFinitePlace C L,
          Nat.card (N ≃ₐ[L] N) := by
      apply Finset.sum_congr rfl
      intro P _
      exact
        sum_card_finitePlaceUnderFiber_fixedBy_intermediateFrobeniusTwist_eq_card_galois
          C S N hExact L hDegreeDiv P
    _ = Nat.card (FiniteExtensionRationalFinitePlace C L) *
          Nat.card (N ≃ₐ[L] N) := by
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card (N ≃ₐ[L] N) *
          Nat.card (FiniteExtensionRationalFinitePlace C L) := Nat.mul_comm _ _

omit [Finite S] [DecidableEq C] [DecidableEq S] [DecidableEq (RatFunc C)]
  [DecidableEq (RatFunc S)] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] [FiniteDimensional L N] [IsGalois L N] in
/-- Viewing an intermediate-base Frobenius twist over `C(X)` does not change
its underlying automorphism of the exact constant extension. -/
theorem exactConstantExtensionFrobeniusTwist_restrictScalars_apply
    (g : N ≃ₐ[L] N) (x : ExactConstantExtension C N S) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    exactConstantExtensionFrobeniusTwist C (RatFunc C) N S hExact
        (g.restrictScalars (RatFunc C)) x =
      exactConstantExtensionFrobeniusTwist C L N S hExact g x := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) := Algebra.toModule
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
      simp [exactConstantExtensionFrobeniusTwist,
        exactConstantExtensionCombinedAutHom,
        exactConstantExtensionConstantAutHom,
        exactConstantExtensionFunctionAutHom,
        exactConstantExtensionConstantAlgEquivOverBase,
        exactConstantExtensionFunctionAlgEquivOverBase]
  | add x y hx hy => simp [hx, hy]

/-- Equality of the two twists as `C(X)`-automorphisms. -/
theorem exactConstantExtensionFrobeniusTwist_restrictScalars
    (g : N ≃ₐ[L] N) :
    letI : Field (ExactConstantExtension C N S) :=
      exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra L (ExactConstantExtension C N S) :=
      exactConstantExtensionBaseAlgebra C L N S
    letI : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module (RatFunc C) (ExactConstantExtension C N S) := Algebra.toModule
    letI : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
    letI : Module L (ExactConstantExtension C N S) := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    (exactConstantExtensionFrobeniusTwist C L N S hExact g).restrictScalars
        (RatFunc C) =
      exactConstantExtensionFrobeniusTwist C (RatFunc C) N S hExact
        (g.restrictScalars (RatFunc C)) := by
  let : Field (ExactConstantExtension C N S) :=
    exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra L (ExactConstantExtension C N S) :=
    exactConstantExtensionBaseAlgebra C L N S
  let : SMul (RatFunc C) (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module (RatFunc C) (ExactConstantExtension C N S) := Algebra.toModule
  let : SMul L (ExactConstantExtension C N S) := Algebra.toSMul
  let : Module L (ExactConstantExtension C N S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) L (ExactConstantExtension C N S) :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  ext x
  exact (exactConstantExtensionFrobeniusTwist_restrictScalars_apply
    C S N hExact L g x).symm

/-- The fixed field constructed over `L` is the same function field as the
rational-base twist attached to `g.restrictScalars C(X)`. -/
noncomputable def
    intermediateFrobeniusTwistField_algEquiv_rationalBaseFrobeniusTwistField
    (g : N ≃ₐ[L] N) :
    let T := ExactConstantExtension C N S
    letI : Field T := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) T :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) T := Algebra.toSMul
    letI : Module (RatFunc C) T := Algebra.toModule
    letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
    letI : SMul L T := Algebra.toSMul
    letI : Module L T := Algebra.toModule
    letI : IsScalarTower (RatFunc C) L T :=
      exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
    let Fₗ := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    let Fᵣ := exactConstantExtensionFrobeniusTwistField
      C (RatFunc C) N S hExact (g.restrictScalars (RatFunc C))
    letI : Algebra L Fₗ := SubalgebraClass.toAlgebra Fₗ.toSubalgebra
    letI : Algebra (RatFunc C) Fₗ :=
      intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
    letI : Algebra (RatFunc C) Fᵣ :=
      SubalgebraClass.toAlgebra Fᵣ.toSubalgebra
    Fₗ ≃ₐ[RatFunc C] Fᵣ := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc C) T :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  letI : SMul (RatFunc C) T := Algebra.toSMul
  letI : Module (RatFunc C) T := Algebra.toModule
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  letI : SMul L T := Algebra.toSMul
  letI : Module L T := Algebra.toModule
  letI : IsScalarTower (RatFunc C) L T :=
    exactConstantExtensionIntermediate_ratFuncBaseTower C S N L
  let sigmaₗ := exactConstantExtensionFrobeniusTwist C L N S hExact g
  let sigmaᵣ := exactConstantExtensionFrobeniusTwist
    C (RatFunc C) N S hExact (g.restrictScalars (RatFunc C))
  let Fₗ := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  let Fᵣ := exactConstantExtensionFrobeniusTwistField
    C (RatFunc C) N S hExact (g.restrictScalars (RatFunc C))
  letI : Algebra L Fₗ := SubalgebraClass.toAlgebra Fₗ.toSubalgebra
  letI : Algebra (RatFunc C) Fₗ :=
    intermediateFrobeniusTwistFieldRatFuncAlgebra C S N hExact L g
  letI : Algebra (RatFunc C) Fᵣ :=
    SubalgebraClass.toAlgebra Fᵣ.toSubalgebra
  have hsigma : sigmaₗ.restrictScalars (RatFunc C) = sigmaᵣ :=
    exactConstantExtensionFrobeniusTwist_restrictScalars
      C S N hExact L g
  have hto (x : Fₗ) : (x.1 : T) ∈ Fᵣ := by
    change x.1 ∈ IntermediateField.fixedField (Subgroup.zpowers sigmaᵣ)
    rw [IntermediateField.mem_fixedField_iff]
    intro tau htau
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htau
    have hxmem : x.1 ∈
        IntermediateField.fixedField (Subgroup.zpowers sigmaₗ) := x.2
    rw [IntermediateField.mem_fixedField_iff] at hxmem
    have hx := hxmem (sigmaₗ ^ k)
      (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    calc
      tau x.1 = (sigmaᵣ ^ k) x.1 := congrArg (fun a ↦ a x.1) hk.symm
      _ = ((sigmaₗ.restrictScalars (RatFunc C)) ^ k) x.1 := by rw [hsigma]
      _ = ((sigmaₗ ^ k).restrictScalars (RatFunc C)) x.1 := by
        exact congrArg (fun a ↦ a x.1)
          (map_zpow (AlgEquiv.restrictScalarsHom (RatFunc C)) sigmaₗ k).symm
      _ = (sigmaₗ ^ k) x.1 := rfl
      _ = x.1 := hx
  have hfrom (x : Fᵣ) : (x.1 : T) ∈ Fₗ := by
    change x.1 ∈ IntermediateField.fixedField (Subgroup.zpowers sigmaₗ)
    rw [IntermediateField.mem_fixedField_iff]
    intro tau htau
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htau
    have hxmem : x.1 ∈
        IntermediateField.fixedField (Subgroup.zpowers sigmaᵣ) := x.2
    rw [IntermediateField.mem_fixedField_iff] at hxmem
    have hx := hxmem (sigmaᵣ ^ k)
      (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    calc
      tau x.1 = (sigmaₗ ^ k) x.1 := congrArg (fun a ↦ a x.1) hk.symm
      _ = ((sigmaₗ ^ k).restrictScalars (RatFunc C)) x.1 := rfl
      _ = ((sigmaₗ.restrictScalars (RatFunc C)) ^ k) x.1 := by
        exact congrArg (fun a ↦ a x.1)
          (map_zpow (AlgEquiv.restrictScalarsHom (RatFunc C)) sigmaₗ k)
      _ = (sigmaᵣ ^ k) x.1 := by rw [hsigma]
      _ = x.1 := hx
  exact
    { toFun := fun x ↦ ⟨x.1, hto x⟩
      invFun := fun x ↦ ⟨x.1, hfrom x⟩
      left_inv := fun x ↦ Subtype.ext rfl
      right_inv := fun x ↦ Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext rfl
      map_add' := fun _ _ ↦ Subtype.ext rfl
      commutes' := fun r ↦ by
        apply Subtype.ext
        change algebraMap L T (algebraMap (RatFunc C) L r) =
          algebraMap (RatFunc C) T r
        exact (IsScalarTower.algebraMap_apply (RatFunc C) L T r).symm }

end IntermediateBase

end


end BGS.HasseWeil
