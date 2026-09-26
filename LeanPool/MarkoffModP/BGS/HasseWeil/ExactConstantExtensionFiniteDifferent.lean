/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldPolynomialDifferent
public import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension
public import Mathlib.RingTheory.DedekindDomain.LinearDisjoint

/-!
# The finite different after exact constant extension

This file supplies the field-theoretic input for transporting the finite
different through an exact finite constant extension.  Inside
`ExactConstantExtension C N S`, the copies of `S(X)` and `N` generate the
whole tensor field and are linearly disjoint over `C(X)`.  The proof uses the
explicit tensor generation and the extension-degree formulas already proved
for rational-function and exact constant extensions.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section


/-- The canonical polynomial algebra structure on the rational function field. -/
@[reducible] noncomputable def
    finiteDifferentCanonicalRatFuncPolynomialAlgebra
    (K : Type*) [Field K] : Algebra K[X] (RatFunc K) := inferInstance

/-- The rational function field is the fraction field of its canonical polynomial algebra. -/
theorem finiteDifferentCanonicalRatFuncPolynomialFractionRing
    (K : Type*) [Field K] :
    letI := finiteDifferentCanonicalRatFuncPolynomialAlgebra K
    IsFractionRing K[X] (RatFunc K) := by
  let := finiteDifferentCanonicalRatFuncPolynomialAlgebra K
  infer_instance

@[reducible] private noncomputable def
    finiteDifferentCanonicalFractionRingAlgebra
    (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (FractionRing R) := inferInstance

private theorem finiteDifferentCanonicalFractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    letI := finiteDifferentCanonicalFractionRingAlgebra R
    IsFractionRing R (FractionRing R) := by
  let := finiteDifferentCanonicalFractionRingAlgebra R
  infer_instance

private theorem different_eq_map_of_disjoint_fields
    (A B R₁ R₂ K L : Type*)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDedekindDomain B]
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [Algebra A B] [IsScalarTower A B L]
    [FaithfulSMul A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra A R₁] [Algebra A R₂] [Algebra R₁ B] [Algebra R₂ B]
    [Algebra R₁ L] [Algebra R₂ L]
    [IsScalarTower A R₁ L] [IsScalarTower R₁ B L] [IsScalarTower R₂ B L]
    [Module.Finite A R₁] [Module.Finite A R₂] [Module.Free A R₂]
    [Module.Finite R₁ B] [Module.Finite R₂ B]
    [IsScalarTower A R₁ B] [IsScalarTower A R₂ B]
    [Module.IsTorsionFree A R₁] [Module.IsTorsionFree A R₂]
    [Module.IsTorsionFree R₁ B] [Module.IsTorsionFree R₂ B]
    [IsIntegralClosure B R₁ L]
    (F₁ F₂ : IntermediateField K L)
    [Algebra R₁ F₁] [Algebra R₂ F₂] [Module.IsTorsionFree R₁ F₁]
    [IsFractionRing R₁ F₁] [IsFractionRing R₂ F₂]
    [IsScalarTower A F₂ L] [IsScalarTower A R₂ F₂]
    [IsScalarTower R₁ F₁ L] [IsScalarTower R₂ F₂ L]
    [Algebra.IsSeparable K F₂] [Algebra.IsSeparable F₁ L]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors A)) F₂]
    (hdisjoint : F₁.LinearDisjoint F₂) (hsup : F₁ ⊔ F₂ = ⊤)
    (hcoprime : IsCoprime
      ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal R₁ B = Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  let : Algebra A (FractionRing A) := finiteDifferentCanonicalFractionRingAlgebra A
  let : SMul A (FractionRing A) := Algebra.toSMul
  let : IsFractionRing A (FractionRing A) := finiteDifferentCanonicalFractionRing A
  let : Algebra B (FractionRing B) := finiteDifferentCanonicalFractionRingAlgebra B
  let : SMul B (FractionRing B) := Algebra.toSMul
  let : IsFractionRing B (FractionRing B) := finiteDifferentCanonicalFractionRing B
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
  exact IsDedekindDomain.differentIdeal_eq_map_differentIdeal
    (K := K) (L := L) (F₁ := F₁) (F₂ := F₂) A B R₁ R₂ hdisjoint hsup hcoprime

private theorem finite_torsionFree_of_integral_base_change
    (A R₁ R₂ B K L : Type*)
    [CommRing A] [CommRing R₁] [CommRing R₂] [CommRing B] [Field K] [Field L]
    [IsDedekindDomain R₂]
    [Algebra A R₁] [Algebra A R₂] [Algebra A L]
    [Algebra R₁ L] [Algebra R₂ L] [Algebra B L] [Algebra R₂ B]
    [Algebra R₂ K] [IsFractionRing R₂ K] [Algebra K L]
    [IsScalarTower R₂ K L] [IsScalarTower R₂ B L] [Module.IsTorsionFree R₂ L]
    [IsScalarTower A R₁ L] [IsScalarTower A R₂ L]
    [Algebra.IsIntegral A R₁] [Algebra.IsIntegral A R₂]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B R₁ L] :
    Module.Finite R₂ B ∧ Module.IsTorsionFree R₂ B := by
  let : IsIntegralClosure B R₂ L := by
    refine ⟨IsIntegralClosure.algebraMap_injective B R₁ L, ?_⟩
    intro x
    constructor
    · intro hx
      have hxA : IsIntegral A x := isIntegral_trans (R := A) x hx
      exact (IsIntegralClosure.isIntegral_iff (A := B) (R := R₁)).mp hxA.tower_top
    · intro hx
      have hxR₁ : IsIntegral R₁ x :=
        (IsIntegralClosure.isIntegral_iff (A := B) (R := R₁)).mpr hx
      exact (isIntegral_trans (R := A) x hxR₁).tower_top
  exact ⟨IsIntegralClosure.finite R₂ K L B, IsIntegralClosure.isTorsionFree R₂ L⟩

/-- Base change preserves the relative different when the fraction-field images are linearly
disjoint, generate the ambient field, and the original differents are coprime. -/
theorem different_eq_map_of_linearlyDisjoint_fieldRanges
    (A R₁ R₂ B K K₁ K₂ L : Type*)
    [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂] [CommRing B] [IsDedekindDomain B]
    [Field K] [Field K₁] [Field K₂] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K K₁] [Algebra K K₂] [Algebra K L]
    [Algebra K₁ L] [Algebra K₂ L] [Algebra A K₂]
    [IsScalarTower K K₁ L] [IsScalarTower K K₂ L] [IsScalarTower A K K₂]
    [Algebra A R₁] [Algebra A R₂] [Algebra A B] [Algebra A L]
    [Algebra R₁ K₁] [IsFractionRing R₁ K₁]
    [Algebra R₂ K₂] [IsFractionRing R₂ K₂]
    [Algebra R₁ B] [Algebra R₂ B] [Algebra R₁ L] [Algebra R₂ L] [Algebra B L]
    [IsScalarTower A K L] [IsScalarTower A K₂ L]
    [IsScalarTower R₁ K₁ L] [IsScalarTower R₂ K₂ L]
    [IsScalarTower A R₂ K₂] [IsScalarTower A R₁ L] [IsScalarTower A R₂ L]
    [IsScalarTower A R₁ B] [IsScalarTower A R₂ B]
    [IsScalarTower R₁ B L] [IsScalarTower R₂ B L] [IsScalarTower A B L]
    [FiniteDimensional K K₂] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A R₁] [Module.Finite A R₂] [Module.Free A R₂]
    [Module.IsTorsionFree A R₁] [Module.IsTorsionFree A R₂]
    [Module.IsTorsionFree R₁ L] [Module.IsTorsionFree R₂ L]
    [Module.IsTorsionFree R₁ B]
    [IsIntegralClosure R₂ A K₂] [IsIntegralClosure B R₁ L]
    (hdisjoint : (IsScalarTower.toAlgHom K K₁ L).fieldRange.LinearDisjoint
      (IsScalarTower.toAlgHom K K₂ L).fieldRange)
    (hsup : (IsScalarTower.toAlgHom K K₁ L).fieldRange ⊔
      (IsScalarTower.toAlgHom K K₂ L).fieldRange = ⊤)
    (hcoprime : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal R₁ B = Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  let f₁ := IsScalarTower.toAlgHom K K₁ L
  let f₂ := IsScalarTower.toAlgHom K K₂ L
  let F₁ := f₁.fieldRange
  let F₂ := f₂.fieldRange
  let e₁ := f₁.equivFieldRange
  let e₂ := f₂.equivFieldRange
  let : Algebra R₁ F₁ :=
    RingHom.toAlgebra (e₁.toRingHom.comp (algebraMap R₁ K₁))
  let e₁inf : K₁ ≃ₐ[R₁] F₁ := { e₁.toRingEquiv with commutes' := fun _ => rfl }
  let : IsFractionRing R₁ F₁ := IsFractionRing.of_algEquiv e₁inf
  let : Module.IsTorsionFree R₁ F₁ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact IsFractionRing.injective R₁ F₁
  let : IsScalarTower R₁ F₁ L := IsScalarTower.of_algebraMap_eq (fun z => by
    change algebraMap R₁ L z = algebraMap K₁ L (algebraMap R₁ K₁ z)
    exact IsScalarTower.algebraMap_apply R₁ K₁ L z)
  let : Algebra R₂ F₂ :=
    RingHom.toAlgebra (e₂.toRingHom.comp (algebraMap R₂ K₂))
  let e₂norm : K₂ ≃ₐ[R₂] F₂ := { e₂.toRingEquiv with commutes' := fun _ => rfl }
  let : IsFractionRing R₂ F₂ := IsFractionRing.of_algEquiv e₂norm
  let : IsScalarTower R₂ F₂ L := IsScalarTower.of_algebraMap_eq (fun z => by
    change algebraMap R₂ L z = algebraMap K₂ L (algebraMap R₂ K₂ z)
    exact IsScalarTower.algebraMap_apply R₂ K₂ L z)
  let : Algebra A F₂ := IntermediateField.algebra' F₂
  let : IsScalarTower A R₂ F₂ := IsScalarTower.of_algebraMap_eq (fun z => by
    apply Subtype.ext
    change algebraMap A L z = algebraMap K₂ L (algebraMap R₂ K₂ (algebraMap A R₂ z))
    rw [← IsScalarTower.algebraMap_apply A R₂ K₂,
      ← IsScalarTower.algebraMap_apply A K₂ L])
  let : IsScalarTower A F₂ L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors A)) K₂ :=
    IsIntegralClosure.isLocalization A K K₂ R₂
  let : IsLocalization (Algebra.algebraMapSubmonoid R₂ (nonZeroDivisors A)) F₂ :=
    IsLocalization.isLocalization_of_algEquiv _ e₂norm
  have hnormalization := finite_torsionFree_of_integral_base_change A R₁ R₂ B F₂ L
  let : Module.Finite R₂ B := hnormalization.1
  let : Module.IsTorsionFree R₂ B := hnormalization.2
  let : Module.Finite R₁ B := IsIntegralClosure.finite R₁ F₁ L B
  let : Module.Finite A B := Module.Finite.trans R₂ B
  let : Module.IsTorsionFree A B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    have hR₂B := Module.isTorsionFree_iff_algebraMap_injective.mp
      (show Module.IsTorsionFree R₂ B from inferInstance)
    have hAR₂ := Module.isTorsionFree_iff_algebraMap_injective.mp
      (show Module.IsTorsionFree A R₂ from inferInstance)
    intro x y hxy
    apply hAR₂
    apply hR₂B
    exact (IsScalarTower.algebraMap_apply A R₂ B x).symm.trans
      (hxy.trans (IsScalarTower.algebraMap_apply A R₂ B y))
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R₁ F₁ L B
  exact different_eq_map_of_disjoint_fields A B R₁ R₂ K L F₁ F₂ hdisjoint hsup hcoprime

private theorem scalarTower_of_injective_algebraMap
    (A R B L : Type*) [CommRing A] [CommRing R] [CommRing B] [CommRing L]
    [Algebra A R] [Algebra A B] [Algebra A L]
    [Algebra R B] [Algebra R L] [Algebra B L]
    [IsScalarTower A R L] [IsScalarTower A B L] [IsScalarTower R B L]
    (hinjective : Function.Injective (algebraMap B L)) : IsScalarTower A R B := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  apply hinjective
  rw [← IsScalarTower.algebraMap_apply A B L,
    ← IsScalarTower.algebraMap_apply R B L,
    ← IsScalarTower.algebraMap_apply A R L]

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance finiteDifferentBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance finiteDifferentBasePolynomialAlgebra : Algebra C[X] N :=
  ratFuncInducedPolynomialAlgebra C N

local instance finiteDifferentBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' (by ext c; rfl)

local instance finiteDifferentCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] := Polynomial.algebra C S

local instance finiteDifferentTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  constantExtensionTensorPolynomialAlgebra C S N

local instance finiteDifferentTensorNormalizationPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  constantExtensionNormalizationTensorPolynomialAlgebra C S N

/-- The original finite normalization acts on the finite normalization after
constant extension through the right tensor factor and the canonical
normalization equivalence. -/
@[reducible] noncomputable def
    exactConstantExtensionFiniteNormalizationAlgebra
    [Fintype C] [Finite S] :
    Algebra (integralClosure C[X] N)
      (integralClosure S[X] (ExactConstantExtension C N S)) :=
  by
    let eNorm :
        S ⊗[C] integralClosure C[X] N ≃+*
          integralClosure S[X] (ExactConstantExtension C N S) :=
      finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
    exact RingHom.toAlgebra
      (eNorm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom)

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- In an exact constant extension, the embedded copies of `S(X)` and `N`
are linearly disjoint over `C(X)` and generate the whole tensor field. -/
theorem exactConstantExtension_rationalFunctionRanges_linearDisjoint :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : SMul (RatFunc C) L := Algebra.toSMul
    letI : Module (RatFunc C) L := Algebra.toModule
    letI : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
    letI : MulAction (RatFunc C) L := DistribMulAction.toMulAction
    letI : Algebra N L := exactConstantExtensionAlgebra C N S
    letI : SMul N L := Algebra.toSMul
    letI : Module N L := Algebra.toModule
    letI : IsScalarTower (RatFunc C) N L :=
      exactConstantExtensionBaseTower C (RatFunc C) N S
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
    letI : Module (RatFunc C) (RatFunc S) := Algebra.toModule
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) L := Algebra.toSMul
    letI : Module (RatFunc S) L := Algebra.toModule
    letI : IsScalarTower (RatFunc C) (RatFunc S) L :=
      rationalBase_scalarTower C S N hExact
    let f₁ : RatFunc S →ₐ[RatFunc C] L :=
      IsScalarTower.toAlgHom (RatFunc C) (RatFunc S) L
    let f₂ : N →ₐ[RatFunc C] L :=
      IsScalarTower.toAlgHom (RatFunc C) N L
    let F₁ : IntermediateField (RatFunc C) L := f₁.fieldRange
    let F₂ : IntermediateField (RatFunc C) L := f₂.fieldRange
    F₁.LinearDisjoint F₂ ∧ F₁ ⊔ F₂ = ⊤ := by
  let L := ExactConstantExtension C N S
  let : Field L := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : Module (RatFunc C) L := Algebra.toModule
  let : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
  let : MulAction (RatFunc C) L := DistribMulAction.toMulAction
  let : Algebra N L := exactConstantExtensionAlgebra C N S
  let : SMul N L := Algebra.toSMul
  let : Module N L := Algebra.toModule
  let : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  let : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) L := Algebra.toSMul
  let : Module (RatFunc S) L := Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  let e := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  let : Module.Finite N L := Module.Finite.equiv e
  let : FiniteDimensional (RatFunc C) L :=
    Module.Finite.trans N L
  let f₁ : RatFunc S →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) (RatFunc S) L
  let f₂ : N →ₐ[RatFunc C] L :=
    IsScalarTower.toAlgHom (RatFunc C) N L
  let F₁ : IntermediateField (RatFunc C) L := f₁.fieldRange
  let F₂ : IntermediateField (RatFunc C) L := f₂.fieldRange
  have hsup : F₁ ⊔ F₂ = ⊤ := by
    apply top_unique
    intro z _
    induction z using TensorProduct.inductionOn with
    | tmul s n =>
        rw [show s ⊗ₜ[C] n = (s ⊗ₜ[C] 1) * (1 ⊗ₜ[C] n) by simp]
        apply (F₁ ⊔ F₂).mul_mem
        · apply (show F₁ ≤ F₁ ⊔ F₂ from le_sup_left)
          exact ⟨algebraMap S (RatFunc S) s, by
            change f₁ (algebraMap S (RatFunc S) s) = s ⊗ₜ[C] 1
            exact (ratFuncToExactConstantExtension C S N hExact).commutes s⟩
        · apply (show F₂ ≤ F₁ ⊔ F₂ from le_sup_right)
          exact ⟨n, rfl⟩
    | add x y hx hy =>
        exact (F₁ ⊔ F₂).add_mem (hx (by simp)) (hy (by simp))
  let e₁ : RatFunc S ≃ₐ[RatFunc C] F₁ := f₁.equivFieldRange
  let e₂ : N ≃ₐ[RatFunc C] F₂ := f₂.equivFieldRange
  let : FiniteDimensional (RatFunc C) F₁ := by
    let : Module.Finite (RatFunc C) (RatFunc S) :=
      ratFuncCoefficient_moduleFinite C S
    exact Module.Finite.equiv e₁.toLinearEquiv
  let : FiniteDimensional (RatFunc C) F₂ :=
    Module.Finite.equiv e₂.toLinearEquiv
  have hfinL :
      Module.finrank (RatFunc C) L =
        Module.finrank (RatFunc C) F₁ *
          Module.finrank (RatFunc C) F₂ := by
    calc
      Module.finrank (RatFunc C) L =
          Module.finrank (RatFunc C) N * Module.finrank N L := by
        rw [Module.finrank_mul_finrank]
      _ = Module.finrank (RatFunc C) N * Module.finrank C S := by
        rw [exactConstantExtension_finrank C N S]
      _ = Module.finrank C S * Module.finrank (RatFunc C) N := by
        rw [mul_comm]
      _ = Module.finrank (RatFunc C) (RatFunc S) *
          Module.finrank (RatFunc C) N := by
        rw [ratFuncCoefficient_finrank C S]
      _ = Module.finrank (RatFunc C) F₁ *
          Module.finrank (RatFunc C) F₂ := by
        rw [e₁.toLinearEquiv.finrank_eq, e₂.toLinearEquiv.finrank_eq]
  have hdisjoint : F₁.LinearDisjoint F₂ := by
    apply IntermediateField.LinearDisjoint.of_finrank_sup
    rw [hsup, IntermediateField.finrank_top']
    exact hfinL
  exact ⟨hdisjoint, hsup⟩

omit [FiniteDimensional (RatFunc C) N] [Algebra.IsSeparable (RatFunc C) N] in
private theorem normalization_finite_and_torsionFree
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    let R₂ := integralClosure C[X] N
    let B := integralClosure S[X] L
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra S[X] L := constantExtensionTensorPolynomialAlgebra C S N
    let : Algebra R₂ B := exactConstantExtensionFiniteNormalizationAlgebra C S N
    let : SMul R₂ B := Algebra.toSMul
    let : Module R₂ B := Algebra.toModule
    Module.Finite R₂ B ∧ Module.IsTorsionFree R₂ B := by
  intro L R₂ B field polynomial normalization scalar module
  let : IsDomain R₂ := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra R₂ (S ⊗[C] R₂) :=
    Algebra.TensorProduct.rightAlgebra
  let : SMul R₂ (S ⊗[C] R₂) := Algebra.toSMul
  let : Module R₂ (S ⊗[C] R₂) := Algebra.toModule
  let : Algebra R₂ (R₂ ⊗[C] S) :=
    Algebra.TensorProduct.leftAlgebra
  let : SMul R₂ (R₂ ⊗[C] S) := Algebra.toSMul
  let : Module R₂ (R₂ ⊗[C] S) := Algebra.toModule
  let eSwap : R₂ ⊗[C] S ≃ₐ[R₂] S ⊗[C] R₂ :=
    { (Algebra.TensorProduct.comm C R₂ S).toRingEquiv with
      commutes' := fun r => by
        change (Algebra.TensorProduct.comm C R₂ S)
          (r ⊗ₜ[C] (1 : S)) = (1 : S) ⊗ₜ[C] r
        rfl }
  let : Module.Finite R₂ (R₂ ⊗[C] S) :=
    Module.Finite.base_change C R₂ S
  let : Module.Finite R₂ (S ⊗[C] R₂) :=
    Module.Finite.equiv eSwap.toLinearEquiv
  let eNorm : S ⊗[C] R₂ ≃+* B :=
    finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
  let : Algebra R₂ B :=
    exactConstantExtensionFiniteNormalizationAlgebra C S N
  let : SMul R₂ B := Algebra.toSMul
  let : Module R₂ B := Algebra.toModule
  let eNormR₂ : S ⊗[C] R₂ ≃ₐ[R₂] B :=
    { eNorm with
      commutes' := fun r => by
        change eNorm (1 ⊗ₜ[C] r) =
          finiteFieldConstantExtensionIntegralClosureRingEquiv C S N
            (1 ⊗ₜ[C] r)
        rfl }
  let : Module.Finite R₂ B :=
    Module.Finite.equiv eNormR₂.toLinearEquiv
  let : Module.IsTorsionFree R₂ B := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective
      (eNorm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := R₂)).toRingHom)
    exact eNorm.injective.comp
      (Algebra.TensorProduct.includeRight_injective
        (R := C) (A := S) (B := R₂) (algebraMap C S).injective)
  exact ⟨inferInstance, inferInstance⟩

/-- In an exact finite constant extension, the different of the extended
finite normalization is the extension of the original finite different.
The map on ideals is the right-factor map supplied by
`exactConstantExtensionFiniteNormalizationAlgebra`. -/
theorem exactConstantExtension_finiteDifferent_eq_map
    [Fintype C] [Finite S] :
    let L := ExactConstantExtension C N S
    let R₂ := integralClosure C[X] N
    let B := integralClosure S[X] L
    let : Field L := exactConstantExtensionField C N S hExact
    let : Algebra S[X] L :=
      constantExtensionTensorPolynomialAlgebra C S N
    let : SMul S[X] L := Algebra.toSMul
    let : Module S[X] L := Algebra.toModule
    let : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    let : SMul (RatFunc S) L := Algebra.toSMul
    let : Module (RatFunc S) L := Algebra.toModule
    let : Algebra S[X] (RatFunc S) :=
      finiteDifferentCanonicalRatFuncPolynomialAlgebra S
    let : IsFractionRing S[X] (RatFunc S) :=
      finiteDifferentCanonicalRatFuncPolynomialFractionRing S
    let : IsScalarTower S[X] (RatFunc S) L :=
      IsScalarTower.of_algebraMap_eq' (by
        apply DFunLike.ext _ _
        intro p
        change algebraMap S[X] L p =
          ratFuncToExactConstantExtension C S N hExact
            (algebraMap S[X] (RatFunc S) p)
        exact
          (ratFuncToExactConstantExtension_algebraMap C S N hExact p).symm)
    let : Module.IsTorsionFree S[X] L := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      intro p q hpq
      apply RatFunc.algebraMap_injective S
      apply (algebraMap (RatFunc S) L).injective
      simpa only [IsScalarTower.algebraMap_apply S[X] (RatFunc S) L]
        using hpq
    let : FiniteDimensional (RatFunc S) L :=
      finiteDimensional_over_extendedRatFunc C S N hExact
    let : Algebra.IsSeparable (RatFunc S) L :=
      isSeparable_over_extendedRatFunc C S N hExact
    let : IsDedekindDomain B :=
      IsIntegralClosure.isDedekindDomain S[X] (RatFunc S) L B
    let : Module.IsTorsionFree S[X] B :=
      IsIntegralClosure.isTorsionFree S[X] L
    let : Algebra C[X] (RatFunc C) :=
      finiteDifferentCanonicalRatFuncPolynomialAlgebra C
    let : IsFractionRing C[X] (RatFunc C) :=
      finiteDifferentCanonicalRatFuncPolynomialFractionRing C
    let : IsScalarTower C[X] (RatFunc C) N :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsDedekindDomain R₂ :=
      IsIntegralClosure.isDedekindDomain C[X] (RatFunc C) N R₂
    let : Module.IsTorsionFree C[X] N := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      change Function.Injective
        ((algebraMap (RatFunc C) N).comp
          (algebraMap C[X] (RatFunc C)))
      exact (algebraMap (RatFunc C) N).injective.comp
        (RatFunc.algebraMap_injective C)
    let : Module.IsTorsionFree C[X] R₂ :=
      IsIntegralClosure.isTorsionFree C[X] N
    let : Algebra R₂ B :=
      exactConstantExtensionFiniteNormalizationAlgebra C S N
    differentIdeal S[X] B =
      Ideal.map (algebraMap R₂ B) (differentIdeal C[X] R₂) := by
  intro L R₂ B model0 model1 model2 model3 model4 model5 model6 model7 model8 model9
    model10 model11 model12 model13 model14 model15 model16 model17 model18 model19 model20 model21
  let : IsDomain R₂ := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : Module (RatFunc C) L := Algebra.toModule
  let : DistribMulAction (RatFunc C) L := Module.toDistribMulAction
  let : MulAction (RatFunc C) L := DistribMulAction.toMulAction
  let : Algebra N L := exactConstantExtensionAlgebra C N S
  let : SMul N L := Algebra.toSMul
  let : Module N L := Algebra.toModule
  let : IsScalarTower (RatFunc C) N L :=
    exactConstantExtensionBaseTower C (RatFunc C) N S
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  let : Algebra C[X] L :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc C) L).comp
        (algebraMap C[X] (RatFunc C)))
  let : SMul C[X] L := Algebra.toSMul
  let : Module C[X] L := Algebra.toModule
  let : IsScalarTower C[X] (RatFunc C) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra C[X] B :=
    RingHom.toAlgebra
      ((algebraMap S[X] B).comp (algebraMap C[X] S[X]))
  let : SMul C[X] B := Algebra.toSMul
  let : Module C[X] B := Algebra.toModule
  let : IsScalarTower C[X] S[X] B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S[X] B L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C[X] S[X] L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap (RatFunc C) L
          (algebraMap C[X] (RatFunc C) p) =
        algebraMap S[X] L (algebraMap C[X] S[X] p)
      rw [IsScalarTower.algebraMap_apply S[X] (RatFunc S) L]
      rw [rationalBase_algebraMap_eq C S N hExact]
      apply congrArg (algebraMap (RatFunc S) L)
      exact ratFuncCoefficientAlgHom_algebraMap C S p)
  let : IsScalarTower C[X] B L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply DFunLike.ext _ _
      intro p
      change algebraMap C[X] L p =
        algebraMap S[X] L (algebraMap C[X] S[X] p)
      exact IsScalarTower.algebraMap_apply C[X] S[X] L p)
  let : SMul C[X] S[X] := Algebra.toSMul
  let : Module C[X] S[X] := Algebra.toModule
  let : Module.Finite C[X] (C[X] ⊗[C] S) :=
    Module.Finite.base_change C C[X] S
  let : Module.Finite C[X] S[X] :=
    Module.Finite.equiv
      (Algebra.IsPushout.equiv C C[X] S S[X]).toLinearEquiv
  let : Module.IsTorsionFree C[X] S[X] := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    change Function.Injective (Polynomial.map (algebraMap C S))
    exact Polynomial.map_injective (algebraMap C S) (algebraMap C S).injective
  let : Module.Free C[X] S[X] :=
    Module.free_of_finite_type_torsion_free'
  let eNL := exactConstantExtensionLinearEquiv C N S
  let : Module.Finite N (N ⊗[C] S) :=
    Module.Finite.base_change C N S
  let : Module.Finite N L := Module.Finite.equiv eNL
  let : FiniteDimensional (RatFunc C) L :=
    Module.Finite.trans N L
  let : Algebra.IsSeparable (RatFunc C) L :=
    isSeparable_exactConstantExtension_over_baseRatFunc C S N hExact
  let : Algebra R₂ L :=
    RingHom.toAlgebra ((algebraMap N L).comp (algebraMap R₂ N))
  let : SMul R₂ L := Algebra.toSMul
  let : Module R₂ L := Algebra.toModule
  let : IsScalarTower R₂ N L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsFractionRing R₂ N :=
    IsIntegralClosure.isFractionRing_of_finite_extension C[X] (RatFunc C) N R₂
  let : IsScalarTower C[X] R₂ N := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C[X] N L := IsScalarTower.of_algebraMap_eq (fun p => by
    change algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) p) =
      algebraMap N L (algebraMap C[X] N p)
    rw [IsScalarTower.algebraMap_apply C[X] (RatFunc C) N]
    exact IsScalarTower.algebraMap_apply (RatFunc C) N L _)
  let : IsScalarTower C[X] R₂ L := IsScalarTower.of_algebraMap_eq (fun p => by
    change algebraMap C[X] L p =
      algebraMap N L (algebraMap R₂ N (algebraMap C[X] R₂ p))
    rw [← IsScalarTower.algebraMap_apply C[X] R₂ N,
      ← IsScalarTower.algebraMap_apply C[X] N L])
  let : Module.IsTorsionFree R₂ L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap N L).injective.comp (IsFractionRing.injective R₂ N)
  let : SMul R₂ B := Algebra.toSMul
  let : Module R₂ B := Algebra.toModule
  have hR₂BL :
      (algebraMap R₂ L) =
        (algebraMap B L).comp (algebraMap R₂ B) := by
    ext r
    change (1 : S) ⊗ₜ[C] (r : N) =
      (((finiteFieldConstantExtensionIntegralClosureRingEquiv
          C S N) (1 ⊗ₜ[C] r) : B) : L)
    exact
      (finiteFieldConstantExtensionIntegralClosureRingEquiv_tmul
        C S N 1 r).symm
  let : IsScalarTower R₂ B L :=
    IsScalarTower.of_algebraMap_eq' hR₂BL
  let : IsScalarTower C[X] R₂ B :=
    scalarTower_of_injective_algebraMap C[X] R₂ B L
      (fun _ _ h => Subtype.ext h)
  let : Module.Finite C[X] R₂ :=
    IsIntegralClosure.finite C[X] (RatFunc C) N R₂
  let : Module.Free C[X] R₂ :=
    Module.free_of_finite_type_torsion_free'
  have hranges :=
    exactConstantExtension_rationalFunctionRanges_linearDisjoint C S N hExact
  have hcoprime :
      IsCoprime
        ((differentIdeal C[X] S[X]).map (algebraMap S[X] B))
        ((differentIdeal C[X] R₂).map (algebraMap R₂ B)) := by
    rw [finiteFieldPolynomial_differentIdeal_eq_top C S]
    rw [Ideal.map_top]
    apply Ideal.isCoprime_iff_sup_eq.mpr
    exact top_sup_eq
      (Ideal.map (algebraMap R₂ B) (differentIdeal C[X] R₂))
  exact different_eq_map_of_linearlyDisjoint_fieldRanges C[X] S[X] R₂ B
    (RatFunc C) (RatFunc S) N L hranges.1 hranges.2 hcoprime

end

end BGS.HasseWeil
