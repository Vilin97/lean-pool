/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.RamifiedOverextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
/-!
# Artin reciprocity on the ramified infinite-place overextension

This module proves principal-idele triviality, descends the chosen Artin
product to the norm quotient, and identifies it with global reciprocity.
-/

open scoped IsMulCommutative
open NumberField
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

section

attribute [-instance]
  ramifiedInfinitePlaceRealFixedField_ratScalarTower

open scoped Classical in
local instance
    ramifiedInfinitePlaceOverextensionIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] ramifiedInfinitePlaceOverextensionIdeleClassGroupIsMulCommutative

open scoped Classical in
private noncomputable def quotientLiftData
    {A B : Type} [CommGroup A] [Group B]
    (N : Subgroup A) (f : A →* B)
    (hN : ∀ x, x ∈ N → f x = 1) :
    {g : A ⧸ N →* B //
      ∀ x, g (QuotientGroup.mk' N x) = f x} := by
  refine ⟨QuotientGroup.lift N f hN, ?_⟩
  intro x
  exact QuotientGroup.lift_mk _ _ _

open scoped Classical in
private theorem globalNormResidueEquiv_mk_one
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E] :
    AddEquiv.toMultiplicative
        (globalNormResidueEquiv F E)
        (QuotientGroup.mk (1 : IdeleClassGroup F)) =
      1 := by
  change
    Additive.toMul
        (globalNormResidueEquiv F E
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm F E).range
              (1 : IdeleClassGroup F)))) =
      1
  simpa only [globalNormResidueMonoidHom_apply] using
    map_one (globalNormResidueMonoidHom F E)

open scoped Classical in
private theorem globalNormResidueEquiv_mk
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (c : IdeleClassGroup F) :
    AddEquiv.toMultiplicative
        (globalNormResidueEquiv F E)
        (QuotientGroup.mk c) =
      globalNormResidueMonoidHom F E c := by
  change
    Additive.toMul
        (globalNormResidueEquiv F E
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm F E).range c))) =
      globalNormResidueMonoidHom F E c
  exact (globalNormResidueMonoidHom_apply F E c).symm

open scoped Classical in
private theorem globalNormResidueEquiv_ne_one_of_ne_mk_one
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (q :
      IdeleClassGroup F ⧸
        (_root_.ideleClassNorm F E).range)
    (hq : q ≠ QuotientGroup.mk (1 : IdeleClassGroup F)) :
    AddEquiv.toMultiplicative
        (globalNormResidueEquiv F E) q ≠
      1 := by
  intro h
  apply hq
  apply
    (AddEquiv.toMultiplicative
      (globalNormResidueEquiv F E)).injective
  exact
    h.trans
      (globalNormResidueEquiv_mk_one F E).symm

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The chosen local-factor Artin product on the actual special
overextension `L(i)/K'` is trivial on principal ideles. -/
theorem
    ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (x :
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)ˣ) :
    globalArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        (IdeleGroup.principalIdele
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified) x) =
      1 := by
  let :
      IsAbelianGalois ℚ rationalComplexificationCyclotomicField :=
    rationalComplexificationCyclotomicField_isAbelianGalois
  apply
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction_injective
      (K := K) (L := L) v hRamified
  have hdiamond :=
    DFunLike.congr_fun
      (globalArtinMonoidHom_norm_restriction
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (K' :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L' :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
      (IdeleGroup.principalIdele
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) x)
  change
    ramifiedInfinitePlaceOverextensionCyclotomicRestriction
        (K := K) (L := L) v hRamified
        (globalArtinMonoidHom
          (K :=
            ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
          (L :=
            infinitePlaceComplexificationOverfield
              (K := K) (L := L) v)
          (IdeleGroup.principalIdele
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified) x)) =
      globalArtinMonoidHom
        (K := ℚ)
        (L := rationalComplexificationCyclotomicField)
        (IdeleGroup.norm ℚ
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (IdeleGroup.principalIdele
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified) x)) at hdiamond
  rw [IdeleGroup.norm_principalIdele,
    rationalComplexificationGlobalArtin_principalIdele] at hdiamond
  simpa only [map_one] using hdiamond

open scoped Classical in
/-- The actual local-factor product for the special overextension,
descended through principal ideles of its real fixed field. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) →*
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :=
  QuotientGroup.lift
    (IdeleGroup.principalSubgroup
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified))
    (globalArtinMonoidHom
      (K :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v))
    (by
      rintro _ ⟨x, rfl⟩
      exact
        ramifiedInfinitePlaceOverextensionGlobalArtin_principalIdele
          (K := K) (L := L) v hRamified x)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Evaluation of the descended special-overextension Artin map on
an idele representative is the genuine product of chosen local
symbols. -/
theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (a :
      IdeleGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified))
          a) =
      globalArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        a := by
  rw [ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The descended special-overextension Artin map kills every
genuine idele-class norm from its top field. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (c :
      IdeleClassGroup
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          c) =
      1 := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup
              (infinitePlaceComplexificationOverfield
                (K := K) (L := L) v))
            a)) =
      1
  rw [_root_.ideleClassNorm_mk,
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk]
  exact
    globalArtinMonoidHom_ideleNorm_eq_one
      (K :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      a

open scoped Classical in
private noncomputable def
    ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :=
  quotientLiftData
    (A :=
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))
    (B :=
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)))
    (_root_.ideleClassNorm
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)).range
    (ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
      (K := K) (L := L) v hRamified)
    (by
      rintro _ ⟨c, rfl⟩
      exact
        ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_ideleClassNorm
          (K := K) (L := L) v hRamified c)

open scoped Classical in
/-- The chosen-local-factor Artin map on the actual norm quotient of
the special overextension. -/
noncomputable def
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :=
  (ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (K := K) (L := L) v hRamified).1

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Evaluation of the norm-quotient Artin map on an idele-class
representative. -/
@[simp]
theorem
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    ∀ c :
        IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified),
      ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
          (K := K) (L := L) v hRamified
          (QuotientGroup.mk c) =
        ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
          (K := K) (L := L) v hRamified c :=
  (ramifiedInfinitePlaceOverextensionNormQuotientArtinData
    (K := K) (L := L) v hRamified).2

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The norm-quotient Artin map for the special overextension is
surjective onto its actual Galois group. -/
theorem
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_surjective
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Function.Surjective
      (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
        (K := K) (L := L) v hRamified) := by
  intro σ
  obtain ⟨a, ha⟩ :=
    globalArtinMonoidHom_surjective
      (K :=
        ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
      (L :=
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
      σ
  let c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified) :=
    QuotientGroup.mk'
      (IdeleGroup.principalSubgroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))
      a
  refine
    ⟨QuotientGroup.mk c, ?_⟩
  rw [ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk,
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk]
  exact ha

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The norm-quotient Artin map for the special overextension is
bijective. -/
theorem
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_bijective
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K) :
    Function.Bijective
      (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
        (K := K) (L := L) v hRamified) := by
  let K' :=
    ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified
  let L' :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let Q :=
    IdeleClassGroup K' ⧸
      (_root_.ideleClassNorm K' L').range
  let e : Q ≃* Gal(L' / K') :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquiv K' L')
  let : Finite Q :=
    Finite.of_injective e e.injective
  exact
    (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_surjective
      (K := K) (L := L) v hRamified).bijective_of_nat_card_le
        (Nat.card_congr e.toEquiv).le

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- Any two nonidentity automorphisms of the quadratic overextension agree. -/
theorem
    ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    {σ τ :
      Gal(
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) /
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))}
    (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) :
    σ = τ := by
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified σ with hσ1 | hσc
  · exact (hσ hσ1).elim
  rcases
      ramifiedInfinitePlaceOverextension_eq_one_or_conjugation
        (K := K) (L := L) v hRamified τ with hτ1 | hτc
  · exact (hτ hτ1).elim
  exact hσc.trans hτc.symm

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
private theorem
    ramifiedInfinitePlaceOverextensionGlobalNormResidue_ne_one_of_ne_mk_one
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (q :
      IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified) ⧸
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)).range)
    (hq :
      q ≠
        QuotientGroup.mk
          (1 :
            IdeleClassGroup
              (ramifiedInfinitePlaceRealFixedField
                (K := K) (L := L) v hRamified))) :
    AddEquiv.toMultiplicative
        (globalNormResidueEquiv
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)) q ≠
      1 := by
  exact
    globalNormResidueEquiv_ne_one_of_ne_mk_one
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      q hq

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
private theorem
    ramifiedInfinitePlaceOverextensionGlobalNormResidue_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    AddEquiv.toMultiplicative
        (globalNormResidueEquiv
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
        (QuotientGroup.mk c) =
      globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) c := by
  exact
    globalNormResidueEquiv_mk
      (ramifiedInfinitePlaceRealFixedField
        (K := K) (L := L) v hRamified)
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v)
      c

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- At each class in the genuine norm quotient of the special
overextension, the chosen-local-factor product is the canonical
global norm-residue equivalence. -/
theorem
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (q :
      IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified) ⧸
        (_root_.ideleClassNorm
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)).range) :
    ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
        (K := K) (L := L) v hRamified q =
      AddEquiv.toMultiplicative
        (globalNormResidueEquiv
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)) q := by
  let K' :=
    ramifiedInfinitePlaceRealFixedField
      (K := K) (L := L) v hRamified
  let L' :=
    infinitePlaceComplexificationOverfield
      (K := K) (L := L) v
  let N := (_root_.ideleClassNorm K' L').range
  let Q := IdeleClassGroup K' ⧸ N
  let : N.Normal := inferInstance
  change Q at q
  let qOne : Q :=
    QuotientGroup.mk
      (1 :
        IdeleClassGroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified))
  have hArtinOne :
      ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
          (K := K) (L := L) v hRamified
          (QuotientGroup.mk
            (1 :
              IdeleClassGroup
                (ramifiedInfinitePlaceRealFixedField
                  (K := K) (L := L) v hRamified))) =
        1 := by
    rw [ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk,
      map_one]
  have hResidueOne :
      AddEquiv.toMultiplicative
          (globalNormResidueEquiv
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified)
            (infinitePlaceComplexificationOverfield
              (K := K) (L := L) v))
          (QuotientGroup.mk
            (1 :
              IdeleClassGroup
                (ramifiedInfinitePlaceRealFixedField
                  (K := K) (L := L) v hRamified))) =
        1 := by
    exact
      globalNormResidueEquiv_mk_one
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
  by_cases hq : q = qOne
  · subst q
    dsimp only [qOne]
    exact hArtinOne.trans hResidueOne.symm
  · have hArtinNe :
        ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom
            (K := K) (L := L) v hRamified q ≠
          1 := by
      intro h
      apply hq
      apply
        (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_bijective
          (K := K) (L := L) v hRamified).1
      exact
        h.trans
          hArtinOne.symm
    have hqRaw :
        q ≠
          QuotientGroup.mk
            (1 :
              IdeleClassGroup
                (ramifiedInfinitePlaceRealFixedField
                  (K := K) (L := L) v hRamified)) := by
      intro h
      apply hq
      exact h
    have hNormResidueNe :=
      ramifiedInfinitePlaceOverextensionGlobalNormResidue_ne_one_of_ne_mk_one
        (K := K) (L := L) v hRamified q hqRaw
    exact
      ramifiedInfinitePlaceOverextension_galois_eq_of_ne_one
        (K := K) (L := L) v hRamified hArtinNe hNormResidueNe

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
private theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtin_eq_globalNormResidueEquiv_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified c =
      AddEquiv.toMultiplicative
        (globalNormResidueEquiv
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
          (infinitePlaceComplexificationOverfield
            (K := K) (L := L) v))
        (QuotientGroup.mk c) := by
  exact
    (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_mk
      (K := K) (L := L) v hRamified c).symm.trans
      (ramifiedInfinitePlaceOverextensionNormQuotientArtinMonoidHom_eq_globalNormResidue_apply
        (K := K) (L := L) v hRamified
        (QuotientGroup.mk c))

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- On idele classes of the real fixed field, the actual product of
chosen local symbols for the special overextension is the canonical
global norm-residue map. -/
theorem
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (c :
      IdeleClassGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom
        (K := K) (L := L) v hRamified c =
      globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v) c := by
  exact
    (ramifiedInfinitePlaceOverextensionIdeleClassArtin_eq_globalNormResidueEquiv_mk
      (K := K) (L := L) v hRamified
      c).trans
      (ramifiedInfinitePlaceOverextensionGlobalNormResidue_mk
        (K := K) (L := L) v hRamified c)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- On an actual idele representative of the real fixed field, the
canonical global norm-residue map for the special overextension is
the product of the chosen local Artin symbols. -/
theorem
    globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_ideleClass_mk
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (a :
      IdeleGroup
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)) :
    globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified))
          a) =
      globalArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        a := by
  exact
    (ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_eq_globalNormResidue_apply
      (K := K) (L := L) v hRamified
      (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup
          (ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified))
        a)).symm.trans
      (ramifiedInfinitePlaceOverextensionIdeleClassArtinMonoidHom_mk
        (K := K) (L := L) v hRamified a)

omit [NumberField K] [FiniteDimensional K L] in
open scoped Classical in
/-- The canonical global norm-residue symbol of an archimedean
one-place idele class in the special overextension is the chosen
infinite local Artin symbol. -/
theorem
    globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_infinitePlaceIdeleClass
    (v : InfinitePlace K)
    (hRamified :
      (chosenInfinitePlaceAbove (L := L) v).IsRamified K)
    (w :
      InfinitePlace
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified))
    (x : w.Completionˣ) :
    globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (IdeleGroup.infinitePlaceIdeleClass w x) =
      chosenInfinitePlaceArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        w x := by
  change
    globalNormResidueMonoidHom
        (ramifiedInfinitePlaceRealFixedField
          (K := K) (L := L) v hRamified)
        (infinitePlaceComplexificationOverfield
          (K := K) (L := L) v)
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup
            (ramifiedInfinitePlaceRealFixedField
              (K := K) (L := L) v hRamified))
          (IdeleGroup.infinitePlaceIdele w x)) =
      chosenInfinitePlaceArtinMonoidHom
        (K :=
          ramifiedInfinitePlaceRealFixedField
            (K := K) (L := L) v hRamified)
        (L :=
          infinitePlaceComplexificationOverfield
            (K := K) (L := L) v)
        w x
  rw [
    globalNormResidueMonoidHom_ramifiedInfinitePlaceOverextension_ideleClass_mk,
    globalArtinMonoidHom_infinitePlaceIdele]

end

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
