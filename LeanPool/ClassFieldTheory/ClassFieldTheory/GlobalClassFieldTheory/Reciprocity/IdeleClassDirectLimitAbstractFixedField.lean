/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPoints
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm
/-!
# Abstract fixed fields in the rational idele-class representation

Fixed-point comparisons for finite-index closed subgroups and their actual
abstract fixed fields.
-/

@[expose] public section

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology

/-- The ordinary rational idele class group is the fixed part at the
distinguished base subgroup.  This is `rationalIdeleClassEquivFixed` at
the bottom intermediate field, transported along mathlib's canonical
`ℚ ≃ₐ[ℚ] ⊥` equivalence and the identity
`Gal(ℚ_bar/⊥) = baseField`. -/
noncomputable def rationalIdeleClassEquivBaseFixed :
    Additive (IdeleClassGroup ℚ) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) := by
  let B := (⊥ :
    IntermediateField ℚ (SeparableClosure ℚ))
  letI : FiniteDimensional ℚ B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm.toLinearEquiv.finiteDimensional
  letI : NumberField B :=
    NumberField.of_module_finite ℚ B
  let e : ℚ ≃ₐ[ℚ] B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm
  let hB :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) B =
        baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField
      ℚ (SeparableClosure ℚ)
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr e)).trans
        ((rationalIdeleClassEquivFixed B).trans
          (AddEquiv.addSubgroupCongr
            (congrArg
              (KummerTheory.ambientFixedAddSubgroup
                rationalIdeleClassRepresentation)
              hB)))

/-- Scalar extension between finite rational intermediate fields becomes
the literal inclusion between their fixed parts in the absolute
idele-class representation. -/
theorem rationalIdeleClassEquivFixed_extension_coe
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    (rationalIdeleClassEquivFixed E
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
              (IntermediateField.inclusion hFE) c)))).1 =
      (rationalIdeleClassEquivFixed F
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))).1 := by
  change
    Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
              (IntermediateField.inclusion hFE) c))) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit F
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_extension hFE c)

/-- The distinguished base fixed-part equivalence sends an ordinary
rational idele class to its diagonal class at every finite Galois level
of the absolute direct limit. -/
theorem rationalIdeleClassEquivBaseFixed_coe
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : IdeleClassGroup ℚ) :
    (rationalIdeleClassEquivBaseFixed
        (Additive.ofMul c)).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit E
          (RelativeIdeleGroup.classInclusion ℚ E c)) := by
  let B := (⊥ :
    IntermediateField ℚ (SeparableClosure ℚ))
  let : FiniteDimensional ℚ B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm.toLinearEquiv.finiteDimensional
  let : NumberField B :=
    NumberField.of_module_finite ℚ B
  let e : ℚ ≃ₐ[ℚ] B :=
    (IntermediateField.botEquiv
      ℚ (SeparableClosure ℚ)).symm
  let hBE :
      B ≤ (E : IntermediateField ℚ (SeparableClosure ℚ)) :=
    bot_le
  let cB : RelativeIdeleGroup.ClassGroup ℚ B :=
    RelativeIdeleGroup.classInclusion ℚ B c
  have hbaseChange :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := B) cB =
        ideleClassCongr e c := by
    calc
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := B) cB =
          ideleClassExtension ℚ B c := by
        simpa only [cB] using
          (_root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion
            (K := ℚ) (L := B) c)
      _ = ideleClassCongr e c :=
        DFunLike.congr_fun
          (rationalIdeleClassExtension_eq_ideleClassCongr e) c
  have hclassEmbedding :
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
          (IntermediateField.inclusion hBE) cB =
        RelativeIdeleGroup.classInclusion ℚ E c := by
    simpa only [cB] using
      (rationalRelativeIdeleClassEmbedding_classInclusion hBE c)
  have h0 :
      (rationalIdeleClassEquivBaseFixed (Additive.ofMul c)).1 =
        (rationalIdeleClassEquivFixed B
          (Additive.ofMul (ideleClassCongr e c))).1 := by
    rfl
  have h1 :
      (rationalIdeleClassEquivFixed B
          (Additive.ofMul (ideleClassCongr e c))).1 =
        (rationalIdeleClassEquivFixed B
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := B) cB))).1 :=
    congrArg
      (fun x : IdeleClassGroup B =>
        (rationalIdeleClassEquivFixed B (Additive.ofMul x)).1)
      hbaseChange.symm
  have h2 :
      (rationalIdeleClassEquivFixed B
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := B) cB))).1 =
        (rationalIdeleClassEquivFixed E
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB)))).1 :=
    (rationalIdeleClassEquivFixed_extension_coe hBE cB).symm
  have h3 :
      (rationalIdeleClassEquivFixed E
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB)))).1 =
        Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classInclusion ℚ E c))) := by
    change
      Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := B) (M := E)
                (IntermediateField.inclusion hBE) cB))) = _
    rw [hclassEmbedding]
  have h4 :
      Additive.ofMul
          (rationalIntermediateIdeleClassToDirectLimit E
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E)
              (RelativeIdeleGroup.classInclusion ℚ E c))) =
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit E
            (RelativeIdeleGroup.classInclusion ℚ E c)) :=
    congrArg Additive.ofMul
      (rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
        E (RelativeIdeleGroup.classInclusion ℚ E c))
  exact Eq.trans h0 (Eq.trans h1 (Eq.trans h2 (Eq.trans h3 h4)))

private noncomputable instance
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K)

/-- The actual idele class group of the fixed field represented by a
finite-index closed subgroup is the corresponding fixed part of the
rational absolute idele-class representation.  This is the closed-subgroup
endpoint of `rationalIdeleClassEquivFixed`. -/
noncomputable def rationalAbstractFixedFieldIdeleClassEquivFixed
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    Additive
        (IdeleClassGroup
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) K)) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K := by
  letI : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  have hclosed :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) K) =
        K :=
    LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) K
  exact
    (rationalIdeleClassEquivFixed
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K)).trans
      (AddEquiv.addSubgroupCongr
        (congrArg
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation)
          hclosed))

/-- The closed-subgroup fixed-field endpoint has the same underlying
direct-limit class as the intermediate-field comparison from which it is
transported. -/
@[simp]
theorem rationalAbstractFixedFieldIdeleClassEquivFixed_coe
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) K))) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed K c).1 =
      (rationalIdeleClassEquivFixed
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) K) c).1 := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hfinite
  rfl

/-- The relative abstract fixed-field idele class group, identified with
the fixed part at the upper closed subgroup when finite dimensionality is
already available. -/
noncomputable def
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK)]
    [NumberField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK)] :
    Additive
        (IdeleClassGroup
          (LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hLK)) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let hclosed :
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) (E.restrictScalars ℚ) =
        L := by
    change
      RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) L) =
        L
    exact
      LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
        ℚ (SeparableClosure ℚ) L
  exact
    (rationalIdeleClassEquivFixed
      (E.restrictScalars ℚ)).trans
      (AddEquiv.addSubgroupCongr
        (congrArg
          (KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation)
          hclosed))

end Reciprocity
end GlobalClassFieldTheory
