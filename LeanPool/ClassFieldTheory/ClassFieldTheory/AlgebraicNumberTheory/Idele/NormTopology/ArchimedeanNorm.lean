/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.FiniteNormArithmetic
/-!
# Archimedean behavior of idele norms

The positive archimedean norm, and consequently the absolute idele norm, is
preserved by the ordinary norm in a finite number-field extension.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

private theorem nnnormUnitHom_map_ringEquiv_of_isometry
    {F E : Type*}
    [NormedField F] [NormedField E]
    (e : F ≃+* E) (he : Isometry e) (x : Fˣ) :
    nnnormUnitHom E
        (Units.mapEquiv e.toMulEquiv x) =
      nnnormUnitHom F x := by
  apply Units.ext
  apply NNReal.eq
  exact
    he.norm_map_of_map_zero (map_zero e) (x : F)

/-- The ordinary norm from `ℂ` to `ℝ` squares the positive norm. -/
private theorem nnnormUnitHom_real_normUnits_complex
    (x : ℂˣ) :
    nnnormUnitHom ℝ
        (LocalFieldTheory.normUnits ℝ ℂ x) =
      nnnormUnitHom ℂ x ^ 2 := by
  apply Units.ext
  apply NNReal.eq
  change ‖Algebra.norm ℝ (x : ℂ)‖ =
    ‖(x : ℂ)‖ ^ 2
  rw [Algebra.norm_complex_apply, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]

/-- Compatible isometric identifications with one field make the local norm preserve norm. -/
private theorem nnnormUnitHom_normUnits_of_isometric_identifications
    {F E B : Type*} [NormedField F] [NormedField E] [NormedField B] [Algebra F E]
    (eBase : F ≃+* B) (eExtension : E ≃+* B)
    (hBase : Isometry eBase) (hExtension : Isometry eExtension)
    (hCompatible : (algebraMap B B).comp eBase.toRingHom =
      eExtension.toRingHom.comp (algebraMap F E)) (x : Eˣ) :
    nnnormUnitHom F (LocalFieldTheory.normUnits F E x) = nnnormUnitHom E x := by
  have hNorm := LocalClassFieldTheory.normUnits_map_ringEquiv eBase eExtension hCompatible x
  calc
    nnnormUnitHom F (LocalFieldTheory.normUnits F E x) =
        nnnormUnitHom B (Units.mapEquiv eBase.toMulEquiv
          (LocalFieldTheory.normUnits F E x)) :=
      (nnnormUnitHom_map_ringEquiv_of_isometry eBase hBase _).symm
    _ = nnnormUnitHom B (LocalFieldTheory.normUnits B B
          (Units.mapEquiv eExtension.toMulEquiv x)) := congrArg _ hNorm
    _ = nnnormUnitHom B (Units.mapEquiv eExtension.toMulEquiv x) := by
      simp [LocalFieldTheory.normUnits]
    _ = nnnormUnitHom E x :=
      nnnormUnitHom_map_ringEquiv_of_isometry eExtension hExtension x

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- At an infinite place, the positive norm of a local field norm, with
the base multiplicity, is the positive norm upstairs with the upstairs
multiplicity. -/
private theorem nnnormUnitHom_normUnits_infinitePlace
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    (hW : W ∈ v₀.placesOver L)
    (x : W.Completionˣ) :
    letI : W.1.LiesOver v₀.1 := hW
    nnnormUnitHom v₀.Completion
        (LocalFieldTheory.normUnits
          v₀.Completion W.Completion x) ^ v₀.mult =
      nnnormUnitHom W.Completion x ^ W.mult := by
  let : W.1.LiesOver v₀.1 := hW
  rcases v₀.isReal_or_isComplex with hvReal | hvComplex
  · rcases W.isReal_or_isComplex with hWReal | hWComplex
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hWReal
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℝ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hvReal z =
            InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hWReal ((algebraMap v₀.Completion W.Completion) z)
        apply Complex.ofReal_injective
        simpa only [
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply] using
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W (v := v₀)).symm
      rw [InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.mult_isReal ⟨W, hWReal⟩, pow_one, pow_one]
      exact nnnormUnitHom_normUnits_of_isometric_identifications eBase eExtension
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hvReal).isometry
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hWReal).isometry hCompatible x
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.Completion) := by
        ext z
        simp [eBase, eExtension]
      have hNorm :=
        LocalClassFieldTheory.normUnits_map_ringEquiv
          eBase eExtension
          hCompatible x
      rw [InfinitePlace.mult_isReal ⟨v₀, hvReal⟩,
        InfinitePlace.mult_isComplex ⟨W, hWComplex⟩,
        pow_one]
      calc
        nnnormUnitHom v₀.Completion
            (LocalFieldTheory.normUnits
              v₀.Completion W.Completion x) =
            nnnormUnitHom ℝ
              (Units.mapEquiv eBase.toMulEquiv
                (LocalFieldTheory.normUnits
                  v₀.Completion W.Completion x)) := by
          symm
          exact
            nnnormUnitHom_map_ringEquiv_of_isometry
              eBase
              (InfinitePlace.Completion.isometryEquivRealOfIsReal
                hvReal).isometry _
        _ =
            nnnormUnitHom ℝ
              (LocalFieldTheory.normUnits ℝ ℂ
                (Units.mapEquiv eExtension.toMulEquiv x)) := by
          rw [hNorm]
        _ =
            nnnormUnitHom ℂ
                (Units.mapEquiv eExtension.toMulEquiv x) ^ 2 :=
          nnnormUnitHom_real_normUnits_complex
            (Units.mapEquiv eExtension.toMulEquiv x)
        _ = nnnormUnitHom W.Completion x ^ 2 := by
          rw [nnnormUnitHom_map_ringEquiv_of_isometry
            eExtension
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              hWComplex).isometry]
  · have hWComplex :
        W.IsComplex :=
      InfinitePlace.LiesOver.isComplex_of_isComplex_under
        W hvComplex
    let eBase :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvComplex
    have hCore
        (eExtension : W.Completion ≃+* ℂ)
        (hCompatible : (algebraMap ℂ ℂ).comp eBase.toRingHom =
          eExtension.toRingHom.comp (algebraMap v₀.Completion W.Completion))
        (hExtensionIsometry : Isometry eExtension) :
        nnnormUnitHom v₀.Completion (LocalFieldTheory.normUnits v₀.Completion W.Completion x) =
          nnnormUnitHom W.Completion x :=
      nnnormUnitHom_normUnits_of_isometric_identifications eBase eExtension
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hvComplex).isometry
        hExtensionIsometry hCompatible x
    rw [InfinitePlace.mult_isComplex ⟨v₀, hvComplex⟩,
      InfinitePlace.mult_isComplex ⟨W, hWComplex⟩]
    congr 1
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          W v₀ with hEmbedding | hConjugate
    · let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let :
          NumberField.ComplexEmbedding.LiesOver W.embedding v₀.embedding :=
        ⟨hEmbedding⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_extensionEmbedding W v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbedding v₀ z =
            InfinitePlace.Completion.extensionEmbedding W
              ((algebraMap v₀.Completion W.Completion) z)
        exact
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W (v := v₀)).symm
      exact
        hCore eExtension hCompatible
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            hWComplex).isometry
    · let eExtension :=
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex).trans
          (starRingAut (R := ℂ))
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate W.embedding) v₀.embedding :=
        ⟨hConjugate⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate
              (InfinitePlace.Completion.extensionEmbedding W))
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding W v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.Completion) := by
        ext z
        simp [eBase, eExtension, ← ComplexEmbedding.conjugate_coe_eq]
      have hExtensionIsometry : Isometry eExtension := by
        intro y z
        change
          edist (star (InfinitePlace.Completion.extensionEmbedding W y))
              (star (InfinitePlace.Completion.extensionEmbedding W z)) =
            edist y z
        calc
          edist (star (InfinitePlace.Completion.extensionEmbedding W y))
              (star (InfinitePlace.Completion.extensionEmbedding W z)) =
              edist (InfinitePlace.Completion.extensionEmbedding W y)
                (InfinitePlace.Completion.extensionEmbedding W z) :=
            star_isometry.edist_eq _ _
          _ = edist y z :=
            (InfinitePlace.Completion.isometry_extensionEmbedding W).edist_eq _ _
      exact hCore eExtension hCompatible hExtensionIsometry

/-- The archimedean positive norm is preserved by the ordinary idele norm. -/
theorem archimedeanNorm_norm
    (a : IdeleGroup L) :
    InfiniteIdeleGroup.archimedeanNorm
        (norm K L a).1 =
      InfiniteIdeleGroup.archimedeanNorm a.1 := by
  classical
  let : ∀ (v₀ : InfinitePlace K)
      (W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀}),
      W.1.1.LiesOver v₀.1 :=
    fun v₀ W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ (v₀ : InfinitePlace K)
      (W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀}),
      Algebra v₀.Completion W.1.Completion :=
    fun v₀ W =>
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
  rw [InfiniteIdeleGroup.archimedeanNorm_apply,
    InfiniteIdeleGroup.archimedeanNorm_apply]
  change
    (∏ v₀ : InfinitePlace K,
        nnnormUnitHom v₀.Completion
          (infiniteComponent v₀ (norm K L a)) ^ v₀.mult) =
      ∏ W : InfinitePlace L,
        nnnormUnitHom W.Completion
          (infiniteComponent W a) ^ W.mult
  calc
    (∏ v₀ : InfinitePlace K,
        nnnormUnitHom v₀.Completion
          (infiniteComponent v₀ (norm K L a)) ^ v₀.mult) =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom v₀.Completion
                (LocalFieldTheory.normUnits
                  v₀.Completion W.1.Completion
                  (infiniteComponent W.1 a)) ^ v₀.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      rw [infiniteComponent_norm_eq_prod]
      let vK := v₀.1
      let hvK : vK.IsNontrivial := v₀.isNontrivial
      let :=
        AlgebraicNumberTheory.Valuations.completionTensorDecompositionExtensionFintype
          (K := K) (L := L) vK hvK
      let eAbove :=
        infinitePlaceAboveEquivExtension (K := K) (L := L) v₀
      have hUniv :
          @Finset.univ
              {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀}
              (Fintype.ofEquiv
                (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L)
                eAbove.symm) =
            @Finset.univ
              {W : InfinitePlace L //
                _root_.infinitePlaceBelow (K := K) W = v₀}
              (Subtype.fintype fun W =>
                _root_.infinitePlaceBelow (K := K) W = v₀) := by
        ext W
        simp
      rw [hUniv]
      rw [map_prod, Finset.prod_pow]
    _ =
        ∏ v₀ : InfinitePlace K,
          ∏ W : {W : InfinitePlace L //
              _root_.infinitePlaceBelow (K := K) W = v₀},
            nnnormUnitHom W.1.Completion
                (infiniteComponent W.1 a) ^ W.1.mult := by
      apply Finset.prod_congr rfl
      intro v₀ _
      apply Finset.prod_congr rfl
      intro W _
      exact
        nnnormUnitHom_normUnits_infinitePlace
          (K := K) (L := L) v₀ W.1
          ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
          (infiniteComponent W.1 a)
    _ =
        ∏ W : InfinitePlace L,
          nnnormUnitHom W.Completion
            (infiniteComponent W a) ^ W.mult := by
      exact
        Fintype.prod_fiberwise
          (_root_.infinitePlaceBelow (K := K))
          (fun W : InfinitePlace L =>
            nnnormUnitHom W.Completion
              (infiniteComponent W a) ^ W.mult)

/-- The absolute idele norm is preserved by the ordinary idele norm. -/
theorem absoluteNorm_norm
    (a : IdeleGroup L) :
    absoluteNorm (norm K L a) =
      absoluteNorm a := by
  rw [absoluteNorm_apply, absoluteNorm_apply,
    finiteAbsoluteNorm_norm, archimedeanNorm_norm]


end IdeleGroup

end
