/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormStatement
/-!
# Proof of ordinary norm comparison in finite towers of rational fixed fields

This proof leaf installs the canonical finite-tower context once and splits
the normal-closure embedding calculation, the pointwise coset action, and the
finite product calculation into separate commands.  The public theorem is a
thin wrapper around those providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open FiniteTowerNormCore

section RationalFiniteTower

variable
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)]

local notation "F₀" =>
  abstractFixedField ℚ (SeparableClosure ℚ) K
local notation "E₀" =>
  abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
local notation "N₀" =>
  IntermediateField.normalClosure F₀ E₀ (SeparableClosure ℚ)
private abbrev rationalFiniteTowerRestrictedNormal :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ N₀
private abbrev rationalFiniteTowerRestrictedUpper :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ E₀
local notation "EQ₀" =>
  rationalFiniteTowerRestrictedUpper K L hLK
local notation "NQ₀" =>
  rationalFiniteTowerRestrictedNormal K L hLK
local notation "U₀" => rationalNormalClosure NQ₀
local notation "Q₀" =>
  K.toSubgroup ⧸ extensionSubgroup K L hLK

noncomputable local instance rationalFiniteTowerLowerFiniteDimensional :
    FiniteDimensional ℚ F₀ :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K hKfinite

noncomputable local instance rationalFiniteTowerUpperFiniteDimensional :
    FiniteDimensional F₀ E₀ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite

local instance rationalFiniteTowerLowerUpperScalarTower :
    IsScalarTower ℚ F₀ E₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance rationalFiniteTowerUpperAbsoluteFiniteDimensional :
    FiniteDimensional ℚ E₀ :=
  FiniteDimensional.trans ℚ F₀ E₀

noncomputable local instance rationalFiniteTowerRestrictedUpperFiniteDimensional :
    FiniteDimensional ℚ EQ₀ := by
  change FiniteDimensional ℚ E₀
  infer_instance

noncomputable local instance rationalFiniteTowerLowerNumberField :
    NumberField F₀ :=
  NumberField.of_module_finite ℚ F₀

noncomputable local instance rationalFiniteTowerUpperNumberField :
    NumberField E₀ :=
  NumberField.of_module_finite ℚ E₀

local instance rationalFiniteTowerUpperSeparableClosureScalarTower :
    IsScalarTower F₀ E₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_upper :
    F₀ ≤ IntermediateField.restrictScalars ℚ E₀ :=
  abstractFixedField_le ℚ (SeparableClosure ℚ) hLK

omit hKfinite hfinite in
private theorem rationalFiniteTower_upper_le_normal :
    IntermediateField.restrictScalars ℚ E₀ ≤ NQ₀ := by
  intro x hx
  exact IntermediateField.le_normalClosure E₀ hx

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_normal :
    F₀ ≤ NQ₀ :=
  (rationalFiniteTower_lower_le_upper K L hLK).trans
    (rationalFiniteTower_upper_le_normal K L hLK)

local instance rationalFiniteTowerNormalScalarTower :
    IsScalarTower ℚ F₀ N₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance rationalFiniteTowerNormalFiniteDimensional :
    FiniteDimensional F₀ N₀ :=
  normalClosure.is_finiteDimensional F₀ E₀ (SeparableClosure ℚ)

noncomputable local instance rationalFiniteTowerNormalAbsoluteFiniteDimensional :
    FiniteDimensional ℚ N₀ :=
  FiniteDimensional.trans ℚ F₀ N₀

noncomputable local instance rationalFiniteTowerNormalNumberField :
    NumberField N₀ :=
  NumberField.of_module_finite ℚ N₀

noncomputable local instance rationalFiniteTowerRestrictedNormalFiniteDimensional :
    FiniteDimensional ℚ NQ₀ := by
  change FiniteDimensional ℚ N₀
  infer_instance

private theorem rationalFiniteTower_normal_le_rationalNormalClosure :
    NQ₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) := by
  change NQ₀ ≤ IntermediateField.normalClosure
    ℚ NQ₀ (SeparableClosure ℚ)
  exact IntermediateField.le_normalClosure NQ₀

private theorem rationalFiniteTower_lower_le_rationalNormalClosure :
    F₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_lower_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

private theorem rationalFiniteTower_upper_le_rationalNormalClosure :
    IntermediateField.restrictScalars ℚ E₀ ≤
      (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_upper_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

/-- The rational normal closure is an algebra over the lower field through the specified
inclusion. -/
local instance rationalFiniteTowerRationalNormalClosureLowerAlgebra :
    Algebra F₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

/-- The rational normal closure is an algebra over the upper field through the specified
inclusion. -/
local instance rationalFiniteTowerRationalNormalClosureUpperAlgebra :
    Algebra E₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

/-- The rational normal closure is an algebra over the intermediate normal closure through
inclusion. -/
local instance rationalFiniteTowerRationalNormalClosureNormalAlgebra :
    Algebra N₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

local instance rationalFiniteTowerRationalNormalClosureLowerScalarTower :
    IsScalarTower ℚ F₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerRationalNormalClosureUpperScalarTower :
    IsScalarTower ℚ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerRationalNormalClosureNormalScalarTower :
    IsScalarTower ℚ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerLowerUpperClosureScalarTower :
    IsScalarTower F₀ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

local instance rationalFiniteTowerLowerNormalClosureScalarTower :
    IsScalarTower F₀ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

local instance rationalFiniteTowerClosureSeparableClosureScalarTower :
    IsScalarTower F₀ U₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

noncomputable local instance rationalFiniteTowerClosureOverUpperFiniteDimensional :
    FiniteDimensional E₀ U₀ :=
  FiniteDimensional.right ℚ E₀ U₀

noncomputable local instance rationalFiniteTowerClosureOverLowerFiniteDimensional :
    FiniteDimensional F₀ U₀ :=
  FiniteDimensional.right ℚ F₀ U₀

noncomputable local instance rationalFiniteTowerClosureOverNormalFiniteDimensional :
    FiniteDimensional N₀ U₀ :=
  FiniteDimensional.right ℚ N₀ U₀

local instance rationalFiniteTowerLowerSeparableClosureGalois :
    IsGalois F₀ (SeparableClosure ℚ) :=
  IsGalois.tower_top_of_isGalois ℚ F₀ (SeparableClosure ℚ)

local instance rationalFiniteTowerNormalGalois : IsGalois F₀ N₀ :=
  IsGalois.normalClosure F₀ E₀ (SeparableClosure ℚ)

local instance rationalFiniteTowerClosureOverLowerGalois : IsGalois F₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ F₀ U₀

local instance rationalFiniteTowerClosureOverNormalGalois : IsGalois N₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ N₀ U₀

/-- The quotient indexing embeddings in the rational finite tower has a finite enumeration. -/
noncomputable local instance rationalFiniteTowerQuotientFintype : Fintype Q₀ :=
  Fintype.ofFinite Q₀

private noncomputable def rationalFiniteTowerCosetEquiv :
    Q₀ ≃ (E₀ →ₐ[F₀] N₀) :=
  (abstractFixedFieldCosetEquivAlgHom
    ℚ (SeparableClosure ℚ) K L hLK).trans
    (normalClosureAlgHomEquiv
      (F := F₀) (E := E₀) (L := SeparableClosure ℚ))

private noncomputable def rationalFiniteTowerNormalInclusion :
    N₀ →ₐ[F₀] U₀ :=
  algHomOfCompatibleRingHom
    (IntermediateField.inclusion
      (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)).toRingHom
    (fun _ => rfl)

private noncomputable def rationalFiniteTowerUpperInclusion :
    E₀ →ₐ[ℚ] U₀ :=
  IntermediateField.inclusion
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK)

private noncomputable def rationalFiniteTowerRelativeClass
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.ClassGroup F₀ E₀ :=
  (_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := F₀) (L := E₀)).symm c

private noncomputable def rationalFiniteTowerRationalRelativeClass
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.ClassGroup ℚ E₀ :=
  (_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := E₀)).symm c

private noncomputable def rationalFiniteTowerEmbeddedClass
    (c : IdeleClassGroup E₀) (q : Q₀) : IdeleClassGroup U₀ :=
  _root_.relativeIdeleClassBaseChangeMulEquiv
    (K := F₀) (L := U₀)
    (RelativeIdeleGroup.classEmbedding
      ((rationalFiniteTowerNormalInclusion K L hLK).comp
        (rationalFiniteTowerCosetEquiv K L hLK q))
      (rationalFiniteTowerRelativeClass K L hLK c))

private theorem rationalFiniteTowerCoset_comp_normalInclusion
    (q : Q₀) :
    (IsScalarTower.toAlgHom F₀ U₀ (SeparableClosure ℚ)).comp
        ((rationalFiniteTowerNormalInclusion K L hLK).comp
          (rationalFiniteTowerCosetEquiv K L hLK q)) =
      abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK q := by
  apply AlgHom.ext
  intro x
  change
    ((normalClosure.algHomEquiv
      F₀ E₀ (SeparableClosure ℚ))
        ((normalClosure.algHomEquiv
          F₀ E₀ (SeparableClosure ℚ)).symm
          (abstractFixedFieldCosetToAlgHom
            ℚ (SeparableClosure ℚ) K L hLK q))) x = _
  exact DFunLike.congr_fun
    ((normalClosure.algHomEquiv
      F₀ E₀ (SeparableClosure ℚ)).apply_symm_apply
      (abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK q)) x

private theorem rationalFiniteTower_restrictedEmbedding
    (sigma : K.toSubgroup) :
    (AlgEquiv.restrictNormalHom U₀ sigma.1).toAlgHom.comp
        (rationalFiniteTowerUpperInclusion K L hLK) =
      ((rationalFiniteTowerNormalInclusion K L hLK).comp
        (rationalFiniteTowerCosetEquiv K L hLK
          (QuotientGroup.mk sigma))).restrictScalars ℚ := by
  apply AlgHom.ext
  intro x
  apply (IsScalarTower.toAlgHom ℚ U₀
    (SeparableClosure ℚ)).injective
  change
    algebraMap U₀ (SeparableClosure ℚ)
        ((AlgEquiv.restrictNormalHom U₀ sigma.1)
          (rationalFiniteTowerUpperInclusion K L hLK x)) =
      algebraMap U₀ (SeparableClosure ℚ)
        ((rationalFiniteTowerNormalInclusion K L hLK)
          (rationalFiniteTowerCosetEquiv K L hLK
            (QuotientGroup.mk sigma) x))
  calc
    algebraMap U₀ (SeparableClosure ℚ)
        ((AlgEquiv.restrictNormalHom U₀ sigma.1)
          (rationalFiniteTowerUpperInclusion K L hLK x)) =
      sigma.1
        (algebraMap U₀ (SeparableClosure ℚ)
          (rationalFiniteTowerUpperInclusion K L hLK x)) :=
      AlgEquiv.restrictNormal_commutes sigma.1 U₀
        (rationalFiniteTowerUpperInclusion K L hLK x)
    _ = sigma.1 (x : SeparableClosure ℚ) := by rfl
    _ = (abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK
          (QuotientGroup.mk sigma)) x := by rfl
    _ = algebraMap U₀ (SeparableClosure ℚ)
        ((rationalFiniteTowerNormalInclusion K L hLK)
          (rationalFiniteTowerCosetEquiv K L hLK
            (QuotientGroup.mk sigma) x)) :=
      (DFunLike.congr_fun
        (rationalFiniteTowerCoset_comp_normalInclusion K L hLK
          (QuotientGroup.mk sigma)) x).symm

private theorem rationalFiniteTower_representativeAction
    (c : IdeleClassGroup E₀) (sigma : K.toSubgroup) :
    Additive.toMul
        (Additive.ofMul
          (sigma.1 •
            rationalIntermediateIdeleClassToDirectLimit EQ₀ c)) =
      rationalIntermediateIdeleClassToDirectLimit U₀
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom U₀ sigma.1).toAlgHom.comp
              (rationalFiniteTowerUpperInclusion K L hLK))
            (rationalFiniteTowerRationalRelativeClass K L hLK c))) := by
  let dℚ := rationalFiniteTowerRationalRelativeClass K L hLK c
  let tau := AlgEquiv.restrictNormalHom U₀ sigma.1
  let jEU := rationalFiniteTowerUpperInclusion K L hLK
  rw [toMul_ofMul]
  have hlevel :
      rationalIntermediateIdeleClassToDirectLimit EQ₀ c =
        rationalRelativeIdeleClassToDirectLimit U₀
          (RelativeIdeleGroup.classEmbedding jEU dℚ) := by
    exact rationalIntermediateIdeleClassToDirectLimit_classEmbedding
      EQ₀ U₀
      (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK) c
  rw [hlevel]
  rw [rationalFiniteGaloisIdeleClassToDirectLimit_baseChange]
  change
    sigma.1 •
        (⟦⟨U₀, RelativeIdeleGroup.classEmbedding jEU dℚ⟩⟧ :
          rationalIdeleClassDirectLimit) = _
  change (⟦⟨U₀, sigma.1 • RelativeIdeleGroup.classEmbedding jEU dℚ⟩⟧ :
    rationalIdeleClassDirectLimit) = _
  apply congrArg
    (fun z : RelativeIdeleGroup.ClassGroup ℚ U₀ =>
      (⟦⟨U₀, z⟩⟧ : rationalIdeleClassDirectLimit))
  exact classEmbedding_smul_eq_classEmbedding_comp jEU tau dℚ

private theorem rationalRelativeFixedFieldCosetActionPointwise
    (c : IdeleClassGroup E₀) (q : Q₀) :
    Additive.toMul
        ((relativeCosetAction rationalIdeleClassRepresentation
          K L hLK
          (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
            K L hLK (Additive.ofMul c)) q :
          Additive rationalIdeleClassDirectLimit)) =
      rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (rationalFiniteTowerEmbeddedClass K L hLK c q) := by
  let dℚ := rationalFiniteTowerRationalRelativeClass K L hLK c
  let dF := rationalFiniteTowerRelativeClass K L hLK c
  let a :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK (Additive.ofMul c)
  let term : Q₀ → Additive rationalIdeleClassDirectLimit :=
    fun q =>
      (relativeCosetAction rationalIdeleClassRepresentation
        K L hLK a q : Additive rationalIdeleClassDirectLimit)
  change
    Additive.toMul (term q) =
      rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            ((rationalFiniteTowerNormalInclusion K L hLK).comp
              (rationalFiniteTowerCosetEquiv K L hLK q)) dF))
  have hbase (f : E₀ →ₐ[F₀] U₀) :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            (f.restrictScalars ℚ) dℚ) =
        _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := U₀)
          (RelativeIdeleGroup.classEmbedding f dF) := by
    exact relativeIdeleClassBaseChange_classEmbedding_changeBase
      (k := ℚ) (F := F₀) (E := E₀) (U := U₀) f c
  rw [← hbase ((rationalFiniteTowerNormalInclusion K L hLK).comp
    (rationalFiniteTowerCosetEquiv K L hLK q))]
  obtain ⟨sigma, rfl⟩ :=
    QuotientGroup.mk_surjective q
  rw [← rationalFiniteTower_restrictedEmbedding K L hLK sigma]
  change
    Additive.toMul
        (Additive.ofMul
          (sigma.1 • rationalIntermediateIdeleClassToDirectLimit EQ₀ c)) =
      rationalIntermediateIdeleClassToDirectLimit U₀
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom U₀ sigma.1).toAlgHom.comp
              (rationalFiniteTowerUpperInclusion K L hLK)) dℚ))
  exact rationalFiniteTower_representativeAction K L hLK c sigma

private theorem rationalFiniteTower_product_embeddedClass
    (c : IdeleClassGroup E₀) :
    ∏ q : Q₀, rationalFiniteTowerEmbeddedClass K L hLK c q =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c)))) := by
  unfold rationalFiniteTowerEmbeddedClass
  exact relativeIdeleClassBaseChange_prod_embeddings
    (rationalFiniteTowerCosetEquiv K L hLK)
    (rationalFiniteTowerNormalInclusion K L hLK)
    (rationalFiniteTowerRelativeClass K L hLK c)

private theorem rationalFiniteTowerNormalInclusion_eq_toAlgHom :
    rationalFiniteTowerNormalInclusion K L hLK =
      IsScalarTower.toAlgHom F₀ N₀ U₀ := by
  apply AlgHom.ext
  intro x
  rfl

private theorem rationalFiniteTowerLowerInclusion_eq_toAlgHom :
    IntermediateField.inclusion
        (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK) =
      IsScalarTower.toAlgHom ℚ F₀ U₀ := by
  apply AlgHom.ext
  intro x
  rfl

private theorem rationalFiniteTower_ideleClassExtension_comp_apply
    (x : IdeleClassGroup F₀) :
    _root_.ideleClassExtension N₀ U₀
        (_root_.ideleClassExtension F₀ N₀ x) =
      _root_.ideleClassExtension F₀ U₀ x := by
  have hcomp :
      (_root_.ideleClassExtension N₀ U₀).comp
          (_root_.ideleClassExtension F₀ N₀) =
        _root_.ideleClassExtension F₀ U₀ :=
    _root_.ideleClassExtension_comp
      (K := F₀) (L := U₀) N₀
  exact DFunLike.congr_fun hcomp x

private theorem rationalFiniteTower_baseChange_classInclusion
    (x : IdeleClassGroup F₀) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := N₀)
        (RelativeIdeleGroup.classInclusion F₀ N₀ x) =
      _root_.ideleClassExtension F₀ N₀ x :=
  _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion
    (K := F₀) (L := N₀) x

private theorem
    rationalFiniteTower_baseChange_normalInclusion_classInclusion
    (x : IdeleClassGroup F₀) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀ x)) =
      _root_.ideleClassExtension F₀ U₀ x := by
  rw [rationalFiniteTowerNormalInclusion_eq_toAlgHom K L hLK]
  rw [relativeIdeleClassBaseChange_classEmbedding_toAlgHom
    (K := F₀) (M := N₀) (L := U₀)]
  exact
    (congrArg (_root_.ideleClassExtension N₀ U₀)
      (rationalFiniteTower_baseChange_classInclusion K L hLK x)).trans
        (rationalFiniteTower_ideleClassExtension_comp_apply K L hLK x)

private theorem rationalFiniteTower_directLimit_ideleClassExtension
    (x : IdeleClassGroup F₀) :
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.ideleClassExtension F₀ U₀ x) =
      rationalIntermediateIdeleClassToDirectLimit F₀ x := by
  let dℚF : RelativeIdeleGroup.ClassGroup ℚ F₀ :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F₀)).symm x
  have hext := rationalIntermediateIdeleClassToDirectLimit_extension
    (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK) dℚF
  rw [rationalFiniteTowerLowerInclusion_eq_toAlgHom K L hLK] at hext
  rw [relativeIdeleClassBaseChange_classEmbedding_toAlgHom
    (K := ℚ) (M := F₀) (L := U₀) dℚF] at hext
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := F₀)).apply_symm_apply] at hext
  exact hext

private theorem rationalFiniteTower_relativeClassNorm_eq_ordinaryNorm
    (c : IdeleClassGroup E₀) :
    RelativeIdeleGroup.classNorm F₀ E₀
        (rationalFiniteTowerRelativeClass K L hLK c) =
      _root_.ideleClassNorm F₀ E₀ c := by
  let d := rationalFiniteTowerRelativeClass K L hLK c
  have hd :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := E₀) d = c := by
    dsimp only [d, rationalFiniteTowerRelativeClass]
    exact (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := F₀) (L := E₀)).apply_symm_apply c
  calc
    RelativeIdeleGroup.classNorm F₀ E₀ d =
        _root_.ideleClassNorm F₀ E₀
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F₀) (L := E₀) d) :=
      (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange d).symm
    _ = _root_.ideleClassNorm F₀ E₀ c :=
      congrArg (_root_.ideleClassNorm F₀ E₀) hd

private theorem rationalFiniteTower_directLimit_extension_eq_norm
    (c : IdeleClassGroup E₀) :
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F₀) (L := U₀)
          (RelativeIdeleGroup.classEmbedding
            (rationalFiniteTowerNormalInclusion K L hLK)
            (RelativeIdeleGroup.classInclusion F₀ N₀
              (RelativeIdeleGroup.classNorm F₀ E₀
                (rationalFiniteTowerRelativeClass K L hLK c))))) =
      rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
  calc
    rationalIntermediateIdeleClassToDirectLimit
        (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c))))) =
      rationalIntermediateIdeleClassToDirectLimit U₀
        (_root_.ideleClassExtension F₀ U₀
          (RelativeIdeleGroup.classNorm F₀ E₀
            (rationalFiniteTowerRelativeClass K L hLK c))) := by
      apply congrArg
        (rationalIntermediateIdeleClassToDirectLimit
          (U₀ : IntermediateField ℚ (SeparableClosure ℚ)))
      exact
        rationalFiniteTower_baseChange_normalInclusion_classInclusion
          K L hLK
          (RelativeIdeleGroup.classNorm F₀ E₀
            (rationalFiniteTowerRelativeClass K L hLK c))
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (RelativeIdeleGroup.classNorm F₀ E₀
          (rationalFiniteTowerRelativeClass K L hLK c)) :=
      rationalFiniteTower_directLimit_ideleClassExtension K L hLK _
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
      apply congrArg (rationalIntermediateIdeleClassToDirectLimit F₀)
      exact rationalFiniteTower_relativeClassNorm_eq_ordinaryNorm K L hLK c

private theorem rationalFiniteTower_product_embeddings_eq_norm
    (c : IdeleClassGroup E₀) :
    ∏ q : Q₀,
        rationalIntermediateIdeleClassToDirectLimit
          (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
          (rationalFiniteTowerEmbeddedClass K L hLK c q) =
      rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) := by
  let g := rationalIntermediateIdeleClassToDirectLimit
    (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
  let b : Q₀ → IdeleClassGroup U₀ := fun q =>
    rationalFiniteTowerEmbeddedClass K L hLK c q
  have hprodMap (s : Finset Q₀) :
      g (s.prod b) = s.prod (fun q => g (b q)) := by
    exact map_prod g b s
  change (∏ q : Q₀, g (b q)) = _
  calc
    ∏ q : Q₀, g (b q) = g (∏ q : Q₀, b q) :=
      (hprodMap Finset.univ).symm
    _ = g (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F₀) (L := U₀)
        (RelativeIdeleGroup.classEmbedding
          (rationalFiniteTowerNormalInclusion K L hLK)
          (RelativeIdeleGroup.classInclusion F₀ N₀
            (RelativeIdeleGroup.classNorm F₀ E₀
              (rationalFiniteTowerRelativeClass K L hLK c))))) := by
      exact congrArg g
        (rationalFiniteTower_product_embeddedClass K L hLK c)
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) :=
      rationalFiniteTower_directLimit_extension_eq_norm K L hLK c

private theorem rationalAbstractRelativeFixedFieldNormCore
    (c : IdeleClassGroup E₀) :
    relativeNorm rationalIdeleClassRepresentation K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
          K L hLK (Additive.ofMul c)) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul (_root_.ideleClassNorm F₀ E₀ c)) := by
  let a :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK (Additive.ofMul c)
  let term : Q₀ → Additive rationalIdeleClassDirectLimit :=
    fun q =>
      (relativeCosetAction rationalIdeleClassRepresentation
        K L hLK a q : Additive rationalIdeleClassDirectLimit)
  apply Subtype.ext
  apply Additive.toMul.injective
  change
    Additive.toMul (∑ q : Q₀, term q) =
      rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c)
  rw [toMul_sum]
  calc
    ∏ q : Q₀, Additive.toMul (term q) =
        ∏ q : Q₀,
          rationalIntermediateIdeleClassToDirectLimit
            (U₀ : IntermediateField ℚ (SeparableClosure ℚ))
            (rationalFiniteTowerEmbeddedClass K L hLK c q) := by
      apply Finset.prod_congr rfl
      intro q _
      exact rationalRelativeFixedFieldCosetActionPointwise K L hLK c q
    _ = rationalIntermediateIdeleClassToDirectLimit F₀
        (_root_.ideleClassNorm F₀ E₀ c) :=
      rationalFiniteTower_product_embeddings_eq_norm K L hLK c

/-- The abstract relative norm agrees with the ordinary idèle-class norm
for every finite tower of rational fixed fields. -/
theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm_ofFiniteTower :
    rationalAbstractRelativeFixedFieldNormStatement K L hLK := by
  unfold rationalAbstractRelativeFixedFieldNormStatement
  intro F E c
  exact rationalAbstractRelativeFixedFieldNormCore K L hLK c

end RationalFiniteTower

end Reciprocity
end GlobalClassFieldTheory
