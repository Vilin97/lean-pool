/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
/-!
# Norms of base units supported at one finite place

For a finite place `v` of an extension field, embed a unit of the
completion at the place below `v` into the completion at `v`, and
support it only at `v`.  Its ordinary idele norm is supported only at
the place below `v`; the surviving component is the corresponding
local-degree power.
-/

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- The map from units of the completion below `v` to units of the
completion at `v`, using the actual finite-place completion map. -/
noncomputable def finitePlaceBaseUnitExtension
    (v : HeightOneSpectrum (𝓞 L)) :
    ((_root_.finitePlaceBelow (K := K) v).adicCompletion K)ˣ →*
      (v.adicCompletion L)ˣ :=
  Units.map
    (finitePlaceAdicCompletionMap
      K L
      (_root_.finitePlaceBelow (K := K) v)
      ⟨v, rfl⟩).toMonoidHom

/-- The degree of the actual completed extension at `v` over the
completion at the place below `v`. -/
noncomputable def finitePlaceCompletionDegree
    (v : HeightOneSpectrum (𝓞 L)) : ℕ := by
  let q := _root_.finitePlaceBelow (K := K) v
  let W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  letI : Algebra (q.adicCompletion K) (v.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L q W).toAlgebra
  letI : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
    finitePlaceAdicCompletionMap_moduleFinite K L q W
  exact Module.finrank (q.adicCompletion K) (v.adicCompletion L)

/-- The completed local degree at an actual finite place is positive. -/
theorem finitePlaceCompletionDegree_pos
    (v : HeightOneSpectrum (𝓞 L)) :
    0 <
      finitePlaceCompletionDegree
        (K := K) (L := L) v := by
  let q := _root_.finitePlaceBelow (K := K) v
  let W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  let : Algebra (q.adicCompletion K) (v.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L q W).toAlgebra
  let : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
    finitePlaceAdicCompletionMap_moduleFinite K L q W
  change
    0 <
      Module.finrank
        (q.adicCompletion K) (v.adicCompletion L)
  exact Module.finrank_pos

omit [FiniteDimensional K L] in
/-- The idele norm of a base-completion unit supported at one extension
place is the corresponding local-degree power supported at the place
below it. -/
theorem norm_finitePlaceIdele_finitePlaceBaseUnitExtension
    (v : HeightOneSpectrum (𝓞 L))
    (x :
      ((_root_.finitePlaceBelow (K := K) v).adicCompletion K)ˣ) :
    norm K L
        (finitePlaceIdele v
          (finitePlaceBaseUnitExtension
            (K := K) (L := L) v x)) =
      finitePlaceIdele
        (_root_.finitePlaceBelow (K := K) v)
        (x ^ finitePlaceCompletionDegree
          (K := K) (L := L) v) := by
  classical
  let q := _root_.finitePlaceBelow (K := K) v
  let W₀ :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = q} :=
    ⟨v, rfl⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      infiniteComponent w
          (norm K L
            (finitePlaceIdele v
              (finitePlaceBaseUnitExtension
                (K := K) (L := L) v x))) =
        infiniteComponent w
          (finitePlaceIdele q
            (x ^ finitePlaceCompletionDegree
              (K := K) (L := L) v))
    rw [infiniteComponent_norm_eq_prod]
    rw [finitePlaceIdele_infiniteComponent]
    apply Finset.prod_eq_one
    intro W _
    rw [finitePlaceIdele_infiniteComponent]
    exact map_one _
  · apply Subtype.ext
    funext r
    change
      finiteComponent r
          (norm K L
            (finitePlaceIdele v
              (finitePlaceBaseUnitExtension
                (K := K) (L := L) v x))) =
        finiteComponent r
          (finitePlaceIdele q
            (x ^ finitePlaceCompletionDegree
              (K := K) (L := L) v))
    by_cases hr : r = q
    · subst r
      rw [finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_same]
      rw [Finset.prod_eq_single W₀]
      · rw [finitePlaceIdele_finiteComponent_same]
        let :
            Algebra (q.adicCompletion K) (v.adicCompletion L) :=
          (finitePlaceAdicCompletionMap K L q W₀).toAlgebra
        let : Module.Finite (q.adicCompletion K) (v.adicCompletion L) :=
          finitePlaceAdicCompletionMap_moduleFinite K L q W₀
        have hmap :
            algebraMap (q.adicCompletion K) (v.adicCompletion L) =
              finitePlaceAdicCompletionMap K L q W₀ :=
          RingHom.algebraMap_toAlgebra _
        change
          LocalFieldTheory.normUnits
              (q.adicCompletion K) (v.adicCompletion L)
              (Units.map
                (finitePlaceAdicCompletionMap K L q W₀).toMonoidHom x) =
            x ^ Module.finrank (q.adicCompletion K) (v.adicCompletion L)
        rw [← hmap]
        simpa [
          LocalFieldTheory.IsNonarchimedeanLocalField.mapBaseUnitsToExtensionUnits,
          MonoidHom.id_apply] using
          (LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
            (K := q.adicCompletion K) (L := v.adicCompletion L) x)
      · intro W _ hW
        have hWv : W.1 ≠ v := by
          intro h
          apply hW
          exact Subtype.ext h
        rw [
          finitePlaceIdele_finiteComponent_of_ne
            v W.1
            (finitePlaceBaseUnitExtension
              (K := K) (L := L) v x)
            hWv,
          map_one]
      · simp
    · rw [
        finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_of_ne
          q r
          (x ^ finitePlaceCompletionDegree
            (K := K) (L := L) v)
          hr]
      apply Finset.prod_eq_one
      intro W _
      have hWv : W.1 ≠ v := by
        intro h
        apply hr
        calc
          r = _root_.finitePlaceBelow (K := K) W.1 :=
            W.2.symm
          _ = q := by rw [h]
      rw [
        finitePlaceIdele_finiteComponent_of_ne
          v W.1
          (finitePlaceBaseUnitExtension
            (K := K) (L := L) v x)
          hWv,
        map_one]

omit [FiniteDimensional K L] in
/-- The ordinary idele norm of an arbitrary unit supported at one
upper finite place is supported at the place below, with surviving
component equal to the genuine completed local norm. -/
theorem norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits
    (v : HeightOneSpectrum (𝓞 K))
    (W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v})
    (y : (W.1.adicCompletion L)ˣ) :
    letI :
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    norm K L (finitePlaceIdele W.1 y) =
      finitePlaceIdele v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L) y) := by
  classical
  let :
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      infiniteComponent w
          (norm K L (finitePlaceIdele W.1 y)) =
        infiniteComponent w
          (finitePlaceIdele v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L) y))
    rw [infiniteComponent_norm_eq_prod]
    rw [finitePlaceIdele_infiniteComponent]
    apply Finset.prod_eq_one
    intro W' _
    rw [finitePlaceIdele_infiniteComponent]
    exact map_one _
  · apply Subtype.ext
    funext r
    change
      finiteComponent r
          (norm K L (finitePlaceIdele W.1 y)) =
        finiteComponent r
          (finitePlaceIdele v
            (LocalFieldTheory.normUnits
              (v.adicCompletion K) (W.1.adicCompletion L) y))
    by_cases hr : r = v
    · subst r
      rw [finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_same]
      rw [Finset.prod_eq_single W]
      · rw [finitePlaceIdele_finiteComponent_same]
      · intro W' _ hW'
        have hne : W'.1 ≠ W.1 := by
          intro h
          apply hW'
          exact Subtype.ext h
        rw [
          finitePlaceIdele_finiteComponent_of_ne W.1 W'.1 y hne,
          map_one]
      · simp
    · rw [
        finiteComponent_norm_eq_prod,
        finitePlaceIdele_finiteComponent_of_ne
          v r
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.1.adicCompletion L) y)
          hr]
      apply Finset.prod_eq_one
      intro W' _
      have hne : W'.1 ≠ W.1 := by
        intro h
        apply hr
        calc
          r = _root_.finitePlaceBelow (K := K) W'.1 :=
            W'.2.symm
          _ = v := by rw [h, W.2]
      rw [
        finitePlaceIdele_finiteComponent_of_ne W.1 W'.1 y hne,
        map_one]

omit [FiniteDimensional K L] in
/-- Passing the preceding one-place norm identity to ordinary idele
classes gives the norm--restriction input used in the global
reciprocity square. -/
theorem ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
    (v : HeightOneSpectrum (𝓞 K))
    (W :
      {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v})
    (y : (W.1.adicCompletion L)ˣ) :
    letI :
        Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    _root_.ideleClassNorm K L
        (finitePlaceIdeleClass W.1 y) =
      finitePlaceIdeleClass v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L) y) := by
  classical
  let :
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  rw [
    finitePlaceIdeleClass,
    MonoidHom.coe_comp,
    Function.comp_apply,
    _root_.ideleClassNorm_mk,
    norm_finitePlaceIdele_eq_finitePlaceIdele_normUnits]
  rfl

end IdeleGroup
