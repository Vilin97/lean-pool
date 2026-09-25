/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormCore
/-!
# Ordinary norms in finite towers of rational fixed fields

This leaf compares the abstract relative norm in the rational idèle-class
direct limit with the ordinary idèle-class norm for a finite fixed-field
tower.  The upper field need not be Galois over the lower field.

The construction is kept separate from the foundational direct-limit norm
module so that the normal-closure and coset-product proof elaborates in a
fresh command environment.
-/

@[expose] public section

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open FiniteTowerNormCore

/-- The finite absolute quotient attached to a rational fixed field. -/
abbrev rationalFixedFieldAbsoluteQuotient
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :=
  (baseField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
    extensionSubgroup
      (baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      K (le_baseField K)

/-- The finite relative quotient attached to an inclusion of rational
fixed fields. -/
abbrev rationalFixedFieldRelativeQuotient
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :=
  K.toSubgroup ⧸ extensionSubgroup K L hLK

/-- The proposition that the abstract relative norm agrees with the ordinary
idele-class norm on a finite tower of rational fixed fields. -/
@[irreducible] noncomputable def
    rationalAbstractRelativeFixedFieldNormStatement
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)] : Prop :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  ∀ c : IdeleClassGroup E,
    relativeNorm rationalIdeleClassRepresentation K L hLK
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
          K L hLK (Additive.ofMul c)) =
      rationalAbstractFixedFieldIdeleClassEquivFixed K
        (Additive.ofMul (_root_.ideleClassNorm F E c))

/-- The pointwise comparison between the abstract coset action and the
ordinary class embedding into a common rational normal closure. -/
@[irreducible] noncomputable def
    rationalRelativeFixedFieldCosetActionStatement
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)] : Prop :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsScalarTower F E (SeparableClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  let N := IntermediateField.normalClosure F E (SeparableClosure ℚ)
  let Nℚ := N.restrictScalars ℚ
  let hFE : F ≤ E.restrictScalars ℚ :=
    abstractFixedField_le ℚ (SeparableClosure ℚ) hLK
  let hEN : E.restrictScalars ℚ ≤ Nℚ := fun _ hx =>
    IntermediateField.le_normalClosure E hx
  let hFN : F ≤ Nℚ := hFE.trans hEN
  letI : Algebra F N :=
    (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F N :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional F N :=
    normalClosure.is_finiteDimensional F E (SeparableClosure ℚ)
  letI : FiniteDimensional ℚ N := FiniteDimensional.trans ℚ F N
  letI : NumberField N := NumberField.of_module_finite ℚ N
  letI : FiniteDimensional ℚ Nℚ := by
    change FiniteDimensional ℚ N
    infer_instance
  let U := rationalNormalClosure Nℚ
  let hNU : Nℚ ≤
      (U : IntermediateField ℚ (SeparableClosure ℚ)) := by
    change Nℚ ≤ IntermediateField.normalClosure
      ℚ Nℚ (SeparableClosure ℚ)
    exact IntermediateField.le_normalClosure Nℚ
  let hFU : F ≤
      (U : IntermediateField ℚ (SeparableClosure ℚ)) := hFN.trans hNU
  letI : Algebra F U :=
    (IntermediateField.inclusion hFU).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F U :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional F U := FiniteDimensional.right ℚ F U
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  letI : Fintype Q := Fintype.ofFinite Q
  let liftCoset : Q → (E →ₐ[F] N) := fun q =>
    normalClosureLiftAlgHom
      (abstractFixedFieldCosetToAlgHom
        ℚ (SeparableClosure ℚ) K L hLK q)
  let jNU : N →ₐ[F] U :=
    algHomOfCompatibleRingHom
      (IntermediateField.inclusion hNU).toRingHom
      (fun _ => rfl)
  ∀ (c : IdeleClassGroup E) (q : Q),
    Additive.toMul
        ((relativeCosetAction rationalIdeleClassRepresentation
          K L hLK
          (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
            K L hLK (Additive.ofMul c)) q :
          Additive rationalIdeleClassDirectLimit)) =
      rationalIntermediateIdeleClassToDirectLimit
        (U : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := U)
          (RelativeIdeleGroup.classEmbedding
            (jNU.comp (liftCoset q))
            ((_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := F) (L := E)).symm c)))


end Reciprocity
end GlobalClassFieldTheory
