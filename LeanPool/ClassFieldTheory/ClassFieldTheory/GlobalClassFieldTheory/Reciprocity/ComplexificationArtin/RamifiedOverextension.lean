/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.InfinitePlaceOverfield
/-!
# The quadratic overextension at a ramified real place

This module constructs the real fixed field of complex conjugation, the
quadratic overextension above it, and the faithful cyclotomic restriction.
-/

open scoped IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  infinitePlaceComplexificationOverfieldRationalAlgebra

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

open scoped Classical in
/-- The base `K'` in the archimedean overextension: the fixed field
of complex conjugation in `L(i)`. -/
def ramifiedInfinitePlaceRealFixedField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IntermediateField.fixedField
    (Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified))

omit [FiniteDimensional K L] in
open scoped Classical in
/-- Ambient complex conjugation on the overfield fixes the embedded base
field at a ramified real place. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_fixes_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap K
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v) x) =
      algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x := by
  apply Subtype.ext
  let w := chosenInfinitePlaceAbove (L := L) v
  let σ :=
    chosenInfinitePlaceArtinMonoidHom
      (K := K) (L := L) v
      (-1 : v.Completionˣ)
  have hσ :
      NumberField.ComplexEmbedding.IsConj
        (InfinitePlace.embedding w) σ :=
    chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := K) (L := L) v hRamified
  change
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
      InfinitePlace.embedding w
        (algebraMap K L x)
  calc
    star
        (InfinitePlace.embedding w
          (algebraMap K L x)) =
        InfinitePlace.embedding w
          (σ (algebraMap K L x)) :=
      (hσ.eq (algebraMap K L x)).symm
    _ =
        InfinitePlace.embedding w
          (algebraMap K L x) := by
      exact
        congrArg (InfinitePlace.embedding w)
          (σ.commutes x)

open scoped Classical in
/-- The compatible embedding `K → K'` into the real fixed field. -/
noncomputable def ramifiedInfinitePlaceRealFixedFieldEmbedding
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    K →ₐ[ℚ]
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified :=
  (IsScalarTower.toAlgHom ℚ K
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).codRestrict
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified).toSubalgebra
    (fun x => by
      apply
        (IntermediateField.mem_fixedField_iff _ _).2
      intro g hg
      have hc :
          ramifiedInfinitePlaceOverfieldConjugation
                (K := K) (L := L) v hRamified ∈
            MulAction.stabilizer
              ((infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v) ≃ₐ[ℚ]
                infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v)
              (algebraMap K
                (infinitePlaceComplexificationOverfield
                  (K := K) (L := L) v) x) := by
        exact
          MulAction.mem_stabilizer_iff.mpr
            (ramifiedInfinitePlaceOverfieldConjugation_fixes_base
              (K := K) (L := L) v hRamified x)
      exact
        MulAction.mem_stabilizer_iff.mp
          ((Subgroup.zpowers_le).2 hc hg))

omit [FiniteDimensional K L] in
open scoped Classical in
/-- The fixed-field embedding agrees with the original base-field
algebra map after coercion to the overfield. -/
@[simp]
theorem ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x : K) :
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) =
      algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x := by
  calc
    ((ramifiedInfinitePlaceRealFixedFieldEmbedding
        (K := K) (L := L) v hRamified x :
      ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) =
        (IsScalarTower.toAlgHom ℚ K
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)) x := by
      exact
        AlgHom.coe_codRestrict
          (IsScalarTower.toAlgHom ℚ K
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v))
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified).toSubalgebra _ x
    _ = algebraMap K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x :=
      IsScalarTower.toAlgHom_apply ℚ K
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) x

open scoped Classical in
@[reducible]
noncomputable instance
    ramifiedInfinitePlaceRealFixedFieldAlgebra
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Algebra K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  (ramifiedInfinitePlaceRealFixedFieldEmbedding
    (K := K) (L := L) v hRamified).toRingHom.toAlgebra

open scoped Classical in
instance ramifiedInfinitePlaceRealFixedField_ratScalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower ℚ K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IsScalarTower.of_algHom
    (ramifiedInfinitePlaceRealFixedFieldEmbedding
      (K := K) (L := L) v hRamified)

open scoped Classical in
instance ramifiedInfinitePlaceRealFixedField_scalarTower
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsScalarTower K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  IsScalarTower.of_algHom
    { (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified).val.toRingHom with
      commutes' := fun x =>
        ramifiedInfinitePlaceRealFixedFieldEmbedding_coe
          (K := K) (L := L) v hRamified x }

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
theorem
    ramifiedInfinitePlaceRealFixedField_finiteDimensional
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    FiniteDimensional ℚ
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  FiniteDimensional.left ℚ
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

open scoped Classical in
noncomputable instance ramifiedInfinitePlaceRealFixedField_numberField
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    NumberField
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  by
    let : FiniteDimensional ℚ
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) :=
      ramifiedInfinitePlaceRealFixedField_finiteDimensional
        (K := K) (L := L) v hRamified
    exact
      NumberField.of_module_finite ℚ
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)

omit [FiniteDimensional K L] in
open scoped Classical in
theorem
    ramifiedInfinitePlaceRealFixedField_finiteDimensional_over_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    FiniteDimensional K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  FiniteDimensional.right ℚ K
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)

open scoped Classical in
noncomputable instance
    ramifiedInfinitePlaceRealFixedField_isAbelianGalois_over_base
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois K
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified) :=
  IsAbelianGalois.tower_bot K
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
theorem
    ramifiedInfinitePlaceOverfield_finiteDimensional_over_fixed
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    FiniteDimensional
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  FiniteDimensional.right ℚ
    (ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified)
    (infinitePlaceComplexificationOverfield
      (K := K) (L := L) v)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
theorem ramifiedInfinitePlaceOverextension_isGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  unfold ramifiedInfinitePlaceRealFixedField
  exact
    IsGalois.of_fixed_field
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      (Subgroup.zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified))

open scoped Classical in
noncomputable instance
    ramifiedInfinitePlaceOverextension_isAbelianGalois
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IsAbelianGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) := by
  let : IsGalois
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
    ramifiedInfinitePlaceOverextension_isGalois
      (K := K) (L := L) v hRamified
  let H :=
    Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified)
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let :
      IsCyclic
        Gal((infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)/(ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)) :=
    e.isCyclic.mp
      (Subgroup.isCyclic_zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified))
  exact IsAbelianGalois.of_isCyclic _ _

open scoped Classical in
/-- The distinguished nontrivial automorphism of the quadratic
overextension `L(i)/K'`, obtained from ambient complex conjugation. -/
noncomputable def ramifiedInfinitePlaceOverextensionConjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal((infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)/(ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) :=
  IntermediateField.subgroupEquivAlgEquiv
    (Subgroup.zpowers
      (ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified))
    ⟨ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified,
      Subgroup.mem_zpowers
        (ramifiedInfinitePlaceOverfieldConjugation
          (K := K) (L := L) v hRamified)⟩

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The distinguished overextension automorphism is the restriction
of ambient complex conjugation. -/
@[simp]
theorem ramifiedInfinitePlaceOverextensionConjugation_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (z :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :
    ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified z =
      ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified z := by
  rfl

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Every automorphism of the overextension is either the identity or
the distinguished complex conjugation. -/
theorem ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (σ :
      Gal((infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)/(ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))) :
    σ = 1 ∨
      σ =
        ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified := by
  let c :=
    ramifiedInfinitePlaceOverfieldConjugation
      (K := K) (L := L) v hRamified
  let H := Subgroup.zpowers c
  let e :=
    IntermediateField.subgroupEquivAlgEquiv H
  let cH : H :=
    ⟨c, Subgroup.mem_zpowers c⟩
  have hcSq : c ^ 2 = 1 :=
    (pow_two c).trans
      (ramifiedInfinitePlaceOverfieldConjugation_sq
        (K := K) (L := L) v hRamified)
  have hσCases :
      (e.symm σ).1 = 1 ∨
        (e.symm σ).1 = c := by
    obtain ⟨n, hσ⟩ :=
      Subgroup.mem_zpowers_iff.mp (e.symm σ).property
    have hσPower :
        (e.symm σ).1 = c ^ (n % (2 : ℤ)) :=
      hσ.symm.trans
        (zpow_eq_zpow_emod' n hcSq)
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · left
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_zero c))
    · right
      exact
        hσPower.trans
          ((congrArg (fun m : ℤ => c ^ m) hn).trans
            (zpow_one c))
  rcases hσCases with hσ | hσ
  · left
    have hσSub : e.symm σ = 1 :=
      Subtype.ext hσ
    exact
      e.symm.injective
        (hσSub.trans
          (map_one e.symm).symm)
  · right
    have hσSub : e.symm σ = cH :=
      Subtype.ext hσ
    change σ = e cH
    exact
      (e.apply_symm_apply σ).symm.trans
        (congrArg e hσSub)

attribute [local instance]
  rationalComplexificationCyclotomicField_isAbelianGalois

open scoped Classical in
/-- Restriction of the quadratic overextension Galois group to the
rational fourth-root factor. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Gal((infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)/(ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)) →*
      Gal(rationalComplexificationCyclotomicField/ℚ) :=
  (AlgEquiv.restrictNormalHom
    rationalComplexificationCyclotomicField).comp
      (AlgEquiv.restrictScalarsHom ℚ)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The mapped primitive fourth root in the overfield is not fixed by
ambient complex conjugation. -/
theorem ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) ≠
      algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) := by
  let ζ :=
    IsCyclotomicExtension.zeta
      4 ℚ rationalComplexificationCyclotomicField
  let j :
      infinitePlaceComplexificationOverfield
        (K := K) (L := L) v :=
    algebraMap rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) ζ
  have hζ :
      IsPrimitiveRoot ζ 4 :=
    IsCyclotomicExtension.zeta_spec
      4 ℚ rationalComplexificationCyclotomicField
  have hj :
      IsPrimitiveRoot j 4 :=
    hζ.map_of_injective
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)).injective
  have hj2 : j ^ 2 = -1 :=
    (hj.pow (by norm_num : 0 < 4)
      (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right
  intro hfixed
  have hfixedComplex :
      star (j : ℂ) = (j : ℂ) := by
    simpa only [j,
      ramifiedInfinitePlaceOverfieldConjugation_apply] using
      congrArg Subtype.val hfixed
  have hj2Complex : (j : ℂ) ^ 2 = -1 :=
    congrArg Subtype.val hj2
  have hjIm : (j : ℂ).im = 0 :=
    Complex.conj_eq_iff_im.mp hfixedComplex
  have hjRe := congrArg Complex.re hj2Complex
  simp only [pow_two, Complex.mul_re,
    Complex.neg_re, Complex.one_re] at hjRe
  nlinarith [hjIm, sq_nonneg (j : ℂ).re]

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The distinguished overextension conjugation restricts
nontrivially to the rational fourth-root factor. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified) ≠
      1 := by
  intro h
  apply
    ramifiedInfinitePlaceOverfieldConjugation_map_zeta_ne
      (K := K) (L := L) v hRamified
  have hz :=
    DFunLike.congr_fun h
      (IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField)
  change
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (ramifiedInfinitePlaceOverextensionConjugation
          (K := K) (L := L) v hRamified)
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) =
      IsCyclotomicExtension.zeta
        4 ℚ rationalComplexificationCyclotomicField at hz
  have hz' :=
    congrArg
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
      hz
  change
    (algebraMap rationalComplexificationCyclotomicField
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v))
        (((AlgEquiv.restrictNormalHom
          rationalComplexificationCyclotomicField)
            ((ramifiedInfinitePlaceOverextensionConjugation
              (K := K) (L := L) v hRamified).restrictScalars ℚ))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (algebraMap rationalComplexificationCyclotomicField
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
        (IsCyclotomicExtension.zeta
          4 ℚ rationalComplexificationCyclotomicField) at hz'
  calc
    ramifiedInfinitePlaceOverfieldConjugation
        (K := K) (L := L) v hRamified
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) =
      (ramifiedInfinitePlaceOverextensionConjugation
        (K := K) (L := L) v hRamified).restrictScalars ℚ
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (ramifiedInfinitePlaceOverextensionConjugation_apply
          (K := K) (L := L) v hRamified _).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
          (((AlgEquiv.restrictNormalHom
            rationalComplexificationCyclotomicField)
              ((ramifiedInfinitePlaceOverextensionConjugation
                (K := K) (L := L) v hRamified).restrictScalars ℚ))
            (IsCyclotomicExtension.zeta
              4 ℚ rationalComplexificationCyclotomicField)) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          ((ramifiedInfinitePlaceOverextensionConjugation
            (K := K) (L := L) v hRamified).restrictScalars ℚ)
          rationalComplexificationCyclotomicField
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField)).symm
    _ =
        (algebraMap rationalComplexificationCyclotomicField
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
          (IsCyclotomicExtension.zeta
            4 ℚ rationalComplexificationCyclotomicField) := hz'

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Restriction to the rational fourth-root factor is injective on the
quadratic overextension. -/
theorem
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_injective
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Function.Injective
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified) := by
  apply
    (injective_iff_map_eq_one
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified)).2
  intro σ hσ
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified σ with hσOne | hσConj
  · exact hσOne
  · subst σ
    exact
      (ramifiedInfinitePlaceOverextensionCyclotomicRestriction_conjugation_ne_one
        (K := K) (L := L) v hRamified hσ).elim

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
