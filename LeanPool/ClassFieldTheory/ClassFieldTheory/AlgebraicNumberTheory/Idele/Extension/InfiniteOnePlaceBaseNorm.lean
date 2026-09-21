/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
/-!
# Norms of base units supported at one infinite place

For an infinite place `W` of an extension field, a unit of the
completion at the place below `W` can be extended to `W` and inserted
as a one-place idele.  Its ordinary idele norm remains supported at the
place below `W`; the surviving component is the corresponding local
degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

/-- Extend a unit of the completion below `W` to the completion at
`W`. -/
noncomputable def infinitePlaceBaseUnitExtension
    (W : InfinitePlace L) :
    ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ →*
      W.Completionˣ := by
  letI : W.1.LiesOver
      (_root_.infinitePlaceBelow (K := K) W).1 :=
    ⟨rfl⟩
  exact
    Units.map
      (NumberField.LiesOver.completionMap
        (v := _root_.infinitePlaceBelow (K := K) W)
        (w := W)).toMonoidHom

/-- The actual completion map carries negative one to negative one. -/
@[simp]
theorem infinitePlaceBaseUnitExtension_neg_one
    (W : InfinitePlace L) :
    infinitePlaceBaseUnitExtension
        (K := K) (L := L) W
        (-1 :
          ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) =
      (-1 : W.Completionˣ) := by
  let : W.1.LiesOver
      (_root_.infinitePlaceBelow (K := K) W).1 :=
    ⟨rfl⟩
  apply Units.ext
  simp [infinitePlaceBaseUnitExtension]

/-- The degree of the completed extension at `W` over the completion
at the place below it. -/
noncomputable def infinitePlaceCompletionDegree
    (W : InfinitePlace L) : ℕ := by
  let v := _root_.infinitePlaceBelow (K := K) W
  letI : W.1.LiesOver v.1 := ⟨rfl⟩
  letI : Algebra v.Completion W.Completion :=
    (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
  exact Module.finrank v.Completion W.Completion

/-- The idele norm of a base-completion unit supported at one
extension infinite place is the corresponding local-degree power
supported at the place below it. -/
theorem norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension
    (W : InfinitePlace L)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    norm K L
        (infinitePlaceIdele W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdele
        (_root_.infinitePlaceBelow (K := K) W)
        (x ^ infinitePlaceCompletionDegree
          (K := K) (L := L) W) := by
  classical
  let v := _root_.infinitePlaceBelow (K := K) W
  let W₀ :
      {U : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) U = v} :=
    ⟨W, rfl⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext r
    change
      infiniteComponent r
          (norm K L
            (infinitePlaceIdele W
              (infinitePlaceBaseUnitExtension
                (K := K) (L := L) W x))) =
        infiniteComponent r
          (infinitePlaceIdele v
            (x ^ infinitePlaceCompletionDegree
              (K := K) (L := L) W))
    by_cases hr : r = v
    · subst r
      rw [infiniteComponent_norm_eq_prod,
        infinitePlaceIdele_infiniteComponent_same]
      rw [Finset.prod_eq_single W₀]
      · rw [infinitePlaceIdele_infiniteComponent_same]
        let : W.1.LiesOver v.1 := ⟨rfl⟩
        let : Algebra v.Completion W.Completion :=
          (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
        have hmap :
            algebraMap v.Completion W.Completion =
              NumberField.LiesOver.completionMap (v := v) (w := W) :=
          RingHom.algebraMap_toAlgebra _
        change
          LocalFieldTheory.normUnits v.Completion W.Completion
              (Units.map
                (NumberField.LiesOver.completionMap (v := v) (w := W)).toMonoidHom
                x) =
            x ^ Module.finrank v.Completion W.Completion
        rw [← hmap]
        simpa [
          LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits,
          MonoidHom.id_apply] using
          (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
            (K := v.Completion) (L := W.Completion) x)
      · intro U _ hU
        have hUW : U.1 ≠ W := by
          intro h
          apply hU
          exact Subtype.ext h
        rw [
          infinitePlaceIdele_infiniteComponent_of_ne
            W U.1
            (infinitePlaceBaseUnitExtension
              (K := K) (L := L) W x)
            hUW,
          map_one]
      · simp
    · rw [
        infiniteComponent_norm_eq_prod,
        infinitePlaceIdele_infiniteComponent_of_ne
          v r
          (x ^ infinitePlaceCompletionDegree
            (K := K) (L := L) W)
          hr]
      apply Finset.prod_eq_one
      intro U _
      have hUW : U.1 ≠ W := by
        intro h
        apply hr
        calc
          r = _root_.infinitePlaceBelow (K := K) U.1 :=
            U.2.symm
          _ = v := by rw [h]
      rw [
        infinitePlaceIdele_infiniteComponent_of_ne
          W U.1
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)
          hUW,
        map_one]
  · apply RestrictedProduct.ext
    intro q
    change
      finiteComponent q
          (norm K L
            (infinitePlaceIdele W
              (infinitePlaceBaseUnitExtension
                (K := K) (L := L) W x))) =
        finiteComponent q
          (infinitePlaceIdele v
            (x ^ infinitePlaceCompletionDegree
              (K := K) (L := L) W))
    rw [finiteComponent_norm_eq_prod,
      infinitePlaceIdele_finiteComponent]
    apply Finset.prod_eq_one
    intro U _
    rw [infinitePlaceIdele_finiteComponent, map_one]

/-- If the chosen infinite place is unramified over the base, the
completed extension has degree one, so the norm of the extended
one-place idele is exactly the original one-place idele. -/
theorem norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isUnramified
    (W : InfinitePlace L)
    (hW : W.IsUnramified K)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    norm K L
        (infinitePlaceIdele W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdele
        (_root_.infinitePlaceBelow (K := K) W) x := by
  let v := _root_.infinitePlaceBelow (K := K) W
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  let : Algebra v.Completion W.Completion :=
    (NumberField.LiesOver.completionMap (v := v) (w := W)).toAlgebra
  have hDegree :
      Module.finrank v.Completion W.Completion = 1 :=
    InfinitePlace.IsUnramified.finrank_eq_one
      v hW
  rw [
    norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension,
    show infinitePlaceCompletionDegree
        (K := K) (L := L) W = 1 by
      simpa only [infinitePlaceCompletionDegree, v] using hDegree,
    pow_one]

/-- A real infinite place upstairs is unramified over every lower
number field, so the one-place norm of an extended base unit is
unchanged. -/
theorem norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isReal
    (W : InfinitePlace L)
    (hWReal : W.IsReal)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    norm K L
        (infinitePlaceIdele W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdele
        (_root_.infinitePlaceBelow (K := K) W) x := by
  apply
    norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isUnramified
      (K := K) (L := L) W
  exact InfinitePlace.isUnramified_iff.mpr (Or.inl hWReal)

/-- The degree-one one-place norm equality descends verbatim to the
actual idele class groups. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified
    (W : InfinitePlace L)
    (hW : W.IsUnramified K)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W) x := by
  change
    _root_.ideleClassNorm K L
        (QuotientGroup.mk'
          (principalSubgroup L)
          (infinitePlaceIdele W
            (infinitePlaceBaseUnitExtension
              (K := K) (L := L) W x))) =
      QuotientGroup.mk'
        (principalSubgroup K)
        (infinitePlaceIdele
          (_root_.infinitePlaceBelow (K := K) W) x)
  rw [
    _root_.ideleClassNorm_mk,
    norm_infinitePlaceIdele_infinitePlaceBaseUnitExtension_of_isUnramified
      (K := K) (L := L) W hW x]

/-- Idele-class form of the one-place norm equality at a real place
upstairs. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isReal
    (W : InfinitePlace L)
    (hWReal : W.IsReal)
    (x :
      ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W
          (infinitePlaceBaseUnitExtension
            (K := K) (L := L) W x)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W) x := by
  apply
    ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isUnramified
      (K := K) (L := L) W
  exact InfinitePlace.isUnramified_iff.mpr (Or.inl hWReal)

/-- At a real place upstairs, the idele-class norm of the one-place
negative-one class is the one-place negative-one class below. -/
theorem ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal
    (W : InfinitePlace L)
    (hWReal : W.IsReal) :
    _root_.ideleClassNorm K L
        (infinitePlaceIdeleClass W (-1 : W.Completionˣ)) =
      infinitePlaceIdeleClass
        (_root_.infinitePlaceBelow (K := K) W)
        (-1 :
          ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ) := by
  rw [← infinitePlaceBaseUnitExtension_neg_one
    (K := K) (L := L) W]
  exact
    ideleClassNorm_infinitePlaceIdeleClass_infinitePlaceBaseUnitExtension_of_isReal
      (K := K) (L := L) W hWReal
      (-1 :
        ((_root_.infinitePlaceBelow (K := K) W).Completion)ˣ)

end IdeleGroup
