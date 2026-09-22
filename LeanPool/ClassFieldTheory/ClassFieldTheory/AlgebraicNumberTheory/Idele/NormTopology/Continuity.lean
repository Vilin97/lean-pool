/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.AbsoluteValue
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
/-!
# Continuity of the global idele norm

The norm on ideles in a finite number-field extension is continuous. The
proof works first on the open chart with integral finite components and then
uses the topological-group structure to obtain continuity everywhere.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

open AlgebraicNumberTheory.Valuations

universe u v w

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- A concrete finite-place local norm carries concrete integer units to
concrete integer units. -/
theorem finitePlace_normUnits_mem_integerUnits
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀})
    (z : (W.1.adicCompletionIntegers L).units) :
    letI : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)
        ((W.1.adicCompletionIntegers L).units.subtype z) ∈
      (v₀.adicCompletionIntegers K).units := by
  let : Algebra
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  apply
    (FiniteIdeleGroup.localOrder_eq_zero_iff v₀
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)
        ((W.1.adicCompletionIntegers L).units.subtype z))).mp
  rw [FiniteIdeleGroup.localOrder_normUnits]
  rw [(FiniteIdeleGroup.localOrder_eq_zero_iff W.1
    ((W.1.adicCompletionIntegers L).units.subtype z)).mpr z.property]
  simp

omit [FiniteDimensional K L] in
private theorem finitePlace_normUnits_continuous
    (v₀ : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀}) :
    letI : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    Continuous
      (LocalFieldTheory.normUnits
        (v₀.adicCompletion K) (W.1.adicCompletion L)) := by
  let : Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  let : IsScalarTower
      K (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    finitePlaceAdicCompletionMap_isScalarTower K L v₀ W
  let : ContinuousSMul
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (by
      change Continuous (finitePlaceAdicCompletionMap K L v₀ W)
      exact finitePlaceAdicCompletionMap_continuous K L v₀ W)
  let : FiniteDimensional
      (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    inferInstance
  let : NontriviallyNormedField (v₀.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨ϖ, hϖ⟩ :=
        IsDiscreteValuationRing.exists_irreducible
          (v₀.adicCompletionIntegers K)
      refine ⟨(ϖ : v₀.adicCompletion K), ?_, ?_⟩
      · intro h
        exact hϖ.ne_zero (Subtype.ext h)
      · exact ne_of_lt (RayClass.local_irreducible_norm_lt_one v₀ hϖ))
  exact
    LocalFieldTheory.normUnits_continuous_of_finiteDimensional
      (v₀.adicCompletion K) (W.1.adicCompletion L)

/-- The product of all finite local norms on the integral finite components. -/
private noncomputable def integralFiniteNormComponents
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    ∀ v₀ : HeightOneSpectrum (𝓞 K),
      (v₀.adicCompletionIntegers K).units :=
  fun v₀ => by
    classical
    let vK := HeightOneSpectrum.adicAbv K v₀
    let hvK0 : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v₀
    let eAbove :=
      finitePlaceExtensionEquivAbove
        (K := K) (L := L) v₀
    letI :=
      completionTensorDecompositionExtensionFintype
        (K := K) (L := L) vK hvK0
    letI : Fintype {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀} :=
      Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
    letI : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v₀},
        Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
      fun W =>
        (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
    refine
      ⟨∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1)), ?_⟩
    exact
      Subgroup.prod_mem
        (v₀.adicCompletionIntegers K).units
        (t := Finset.univ)
        (f := fun W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v₀} =>
          LocalFieldTheory.normUnits
            (v₀.adicCompletion K) (W.1.adicCompletion L)
            ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1)))
        (fun W _ =>
          finitePlace_normUnits_mem_integerUnits
            (K := K) (L := L) v₀ W (a.2 W.1))

/-- The finite local norm product is continuous on the integral-idele chart. -/
private theorem integralFiniteNormComponents_continuous :
    Continuous (integralFiniteNormComponents K L) := by
  rw [continuous_pi_iff]
  intro v₀
  apply continuous_induced_rng.mpr
  classical
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK0
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  apply continuous_finsetProd Finset.univ
  intro W _
  exact
    (finitePlace_normUnits_continuous
      (K := K) (L := L) v₀ W).comp
      (continuous_subtype_val.comp
        ((continuous_apply W.1).comp continuous_snd))

/-- The product of the archimedean local norms on the integral-idele chart. -/
private noncomputable def integralInfiniteNormComponents
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    ∀ v₀ : InfinitePlace K, v₀.Completionˣ :=
  fun v₀ => by
    classical
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
        W.1.1.LiesOver v₀.1 :=
      fun W =>
        ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : ∀ W : {W : InfinitePlace L //
        _root_.infinitePlaceBelow (K := K) W = v₀},
        Algebra v₀.Completion W.1.Completion :=
      fun W =>
        (NumberField.LiesOver.completionMap
          (v := v₀) (w := W.1)).toAlgebra
    exact
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          v₀.Completion W.1.Completion
          (ContinuousMulEquiv.piUnits a.1 W.1)

omit [NumberField L] in
/-- A norm between completions at infinite places is continuous. -/
private theorem infinitePlace_normUnits_continuous
    (v₀ : InfinitePlace K)
    (W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀}) :
    letI : W.1.1.LiesOver v₀.1 :=
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
    letI : Algebra v₀.Completion W.1.Completion :=
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
    Continuous
      (LocalFieldTheory.normUnits v₀.Completion W.1.Completion) := by
  let : W.1.1.LiesOver v₀.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : Algebra v₀.Completion W.1.Completion :=
    (NumberField.LiesOver.completionMap
      (v := v₀) (w := W.1)).toAlgebra
  rcases v₀.isReal_or_isComplex with hvReal | hvComplex
  · rcases W.1.isReal_or_isComplex with hWReal | hWComplex
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hWReal
      let eBaseUnits : v₀.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eBase.toMulEquiv
      let eExtensionUnits : W.1.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W.1 hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℝ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hvReal z =
            InfinitePlace.Completion.extensionEmbeddingOfIsReal
              hWReal ((algebraMap v₀.Completion W.1.Completion) z)
        apply Complex.ofReal_injective
        simpa only [
          InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply] using
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W.1 (v := v₀)).symm
      have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
        change Continuous (Units.map eBase.symm.toMonoidHom)
        simpa only [eBase] using
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hvReal).symm.continuous.units_map _
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivRealOfIsReal hWReal).continuous.units_map
            _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℝ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℝ ℝ).comp
          hExtensionUnitsContinuous)
    · let eBase :=
        InfinitePlace.Completion.ringEquivRealOfIsReal hvReal
      let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let eBaseUnits : v₀.Completionˣ ≃* ℝˣ :=
        Units.mapEquiv eBase.toMulEquiv
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
          W.1 hvReal
      have hCompatible :
          RingHom.comp (algebraMap ℝ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        simp [eBase, eExtension]
      have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
        change Continuous (Units.map eBase.symm.toMonoidHom)
        simpa only [eBase] using
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hvReal).symm.continuous.units_map _
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            hWComplex).continuous.units_map _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℝ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℝ ℂ).comp
          hExtensionUnitsContinuous)
  · have hWComplex : W.1.IsComplex :=
      InfinitePlace.LiesOver.isComplex_of_isComplex_under W.1 hvComplex
    let eBase :=
      InfinitePlace.Completion.ringEquivComplexOfIsComplex hvComplex
    let eBaseUnits : v₀.Completionˣ ≃* ℂˣ :=
      Units.mapEquiv eBase.toMulEquiv
    have hBaseUnitsContinuous : Continuous eBaseUnits.symm := by
      change Continuous (Units.map eBase.symm.toMonoidHom)
      simpa only [eBase] using
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          hvComplex).symm.continuous.units_map _
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          W.1 v₀ with hEmbedding | hConjugate
    · let eExtension :=
        InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver W.1.embedding v₀.embedding :=
        ⟨hEmbedding⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (InfinitePlace.Completion.extensionEmbedding W.1)
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_extensionEmbedding W.1 v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        change
          InfinitePlace.Completion.extensionEmbedding v₀ z =
            InfinitePlace.Completion.extensionEmbedding W.1
              ((algebraMap v₀.Completion W.1.Completion) z)
        exact
          (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
            W.1 (v := v₀)).symm
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        refine
          ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            hWComplex).continuous.units_map _).congr ?_
        intro x
        apply Units.ext
        rfl
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℂ ℂ).comp
          hExtensionUnitsContinuous)
    · let eExtension :=
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hWComplex).trans
          (starRingAut (R := ℂ))
      let eExtensionUnits : W.1.Completionˣ ≃* ℂˣ :=
        Units.mapEquiv eExtension.toMulEquiv
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate W.1.embedding) v₀.embedding :=
        ⟨hConjugate⟩
      let :
          NumberField.ComplexEmbedding.LiesOver
            (ComplexEmbedding.conjugate
              (InfinitePlace.Completion.extensionEmbedding W.1))
            (InfinitePlace.Completion.extensionEmbedding v₀) :=
        InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding W.1 v₀
      have hCompatible :
          RingHom.comp (algebraMap ℂ ℂ) eBase.toRingHom =
            RingHom.comp eExtension.toRingHom
              (algebraMap v₀.Completion W.1.Completion) := by
        ext z
        simp [eBase, eExtension, ← ComplexEmbedding.conjugate_coe_eq]
      have hExtensionContinuous : Continuous eExtension := by
        refine
          (InfinitePlace.Completion.isometry_extensionEmbedding W.1).continuous.star.congr ?_
        intro x
        change
          star (InfinitePlace.Completion.extensionEmbedding W.1 x) =
            star (InfinitePlace.Completion.extensionEmbedding W.1 x)
        rfl
      have hExtensionUnitsContinuous : Continuous eExtensionUnits := by
        change Continuous (Units.map eExtension.toMonoidHom)
        exact hExtensionContinuous.units_map _
      have hNormEq :
          (fun x : W.1.Completionˣ =>
            LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
            fun x =>
              eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x)) := by
        funext x
        apply eBaseUnits.injective
        calc
          eBaseUnits (LocalFieldTheory.normUnits v₀.Completion W.1.Completion x) =
              LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x) := by
            simpa only [eBaseUnits, eExtensionUnits] using
              (LocalClassFieldTheory.normUnits_map_ringEquiv
                eBase eExtension hCompatible x)
          _ = eBaseUnits
              (eBaseUnits.symm
                (LocalFieldTheory.normUnits ℂ ℂ (eExtensionUnits x))) := by
            simp
      change Continuous (fun x : W.1.Completionˣ =>
        LocalFieldTheory.normUnits v₀.Completion W.1.Completion x)
      rw [hNormEq]
      exact hBaseUnitsContinuous.comp
        ((LocalFieldTheory.normUnits_continuous_of_finiteDimensional ℂ ℂ).comp
          hExtensionUnitsContinuous)

/-- The archimedean local norm product is continuous on the
integral-idele chart. -/
private theorem integralInfiniteNormComponents_continuous :
    Continuous (integralInfiniteNormComponents K L) := by
  rw [continuous_pi_iff]
  intro v₀
  classical
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.1.LiesOver v₀.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      Algebra v₀.Completion W.1.Completion :=
    fun W =>
      (NumberField.LiesOver.completionMap
        (v := v₀) (w := W.1)).toAlgebra
  apply continuous_finsetProd Finset.univ
  intro W _
  exact
    (infinitePlace_normUnits_continuous
      (K := K) (L := L) v₀ W).comp
      ((continuous_apply W.1).comp
        (ContinuousMulEquiv.piUnits.continuous.comp continuous_fst))

/-- The open chart consisting of arbitrary infinite components and integral
finite components. -/
private def integralIdeleEmbedding
    (F : Type w) [Field F] [NumberField F] :
    (InfiniteIdeleGroup F ×
        (∀ v₀ : HeightOneSpectrum (𝓞 F),
          (v₀.adicCompletionIntegers F).units)) →
      IdeleGroup F :=
  Prod.map id
    (RestrictedProduct.structureMap
      (fun v₀ : HeightOneSpectrum (𝓞 F) =>
        (v₀.adicCompletion F)ˣ)
      (fun v₀ : HeightOneSpectrum (𝓞 F) =>
        ((v₀.adicCompletionIntegers F).units :
          Set (v₀.adicCompletion F)ˣ))
      Filter.cofinite)

/-- The integral-idele chart is an open subspace of the idele group. -/
private theorem integralIdeleEmbedding_isOpenEmbedding
    (F : Type w) [Field F] [NumberField F] :
    Topology.IsOpenEmbedding (integralIdeleEmbedding F) := by
  exact
    Topology.IsOpenEmbedding.id.prodMap
      (RestrictedProduct.isOpenEmbedding_structureMap
        (isOpen_finiteLocalUnits F))

/-- The finite part of the norm on the integral chart is the restricted
product structure map of the finite local norm products. -/
private theorem norm_integralIdeleEmbedding_finite
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    (norm K L (integralIdeleEmbedding L a)).2 =
      RestrictedProduct.structureMap
        (fun v₀ : HeightOneSpectrum (𝓞 K) =>
          (v₀.adicCompletion K)ˣ)
        (fun v₀ : HeightOneSpectrum (𝓞 K) =>
          ((v₀.adicCompletionIntegers K).units :
            Set (v₀.adicCompletion K)ˣ))
        Filter.cofinite
        (integralFiniteNormComponents K L a) := by
  classical
  apply RestrictedProduct.ext
  intro v₀
  let vK := HeightOneSpectrum.adicAbv K v₀
  let hvK0 : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v₀
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v₀
  let :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK0
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀} :=
    Fintype.ofEquiv (AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v₀},
      Algebra (v₀.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (finitePlaceAdicCompletionMap K L v₀ W).toAlgebra
  change
    finiteComponent v₀
        (norm K L (integralIdeleEmbedding L a)) =
      ∏ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          (v₀.adicCompletion K) (W.1.adicCompletion L)
          ((W.1.adicCompletionIntegers L).units.subtype (a.2 W.1))
  rw [finiteComponent_norm_eq_prod]
  rfl

/-- The infinite part of the norm on the integral chart is the product of
the archimedean local norms. -/
private theorem norm_integralIdeleEmbedding_infinite
    (a :
      InfiniteIdeleGroup L ×
        (∀ W : HeightOneSpectrum (𝓞 L),
          (W.adicCompletionIntegers L).units)) :
    (norm K L (integralIdeleEmbedding L a)).1 =
      ContinuousMulEquiv.piUnits.symm
        (integralInfiniteNormComponents K L a) := by
  classical
  apply ContinuousMulEquiv.piUnits.injective
  funext v₀
  let : ∀ W : {W : InfinitePlace L //
      _root_.infinitePlaceBelow (K := K) W = v₀},
      W.1.1.LiesOver v₀.1 :=
    fun W =>
      ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
  let vK := v₀.1
  let hvK : vK.IsNontrivial := v₀.isNontrivial
  let :=
    completionTensorDecompositionExtensionFintype
      (K := K) (L := L) vK hvK
  change
    infiniteComponent v₀
        (norm K L (integralIdeleEmbedding L a)) =
      ∏ W : {W : InfinitePlace L //
          _root_.infinitePlaceBelow (K := K) W = v₀},
        LocalFieldTheory.normUnits
          v₀.Completion W.1.Completion
          (ContinuousMulEquiv.piUnits a.1 W.1)
  rw [infiniteComponent_norm_eq_prod]
  let eAbove :=
    infinitePlaceAboveEquivExtension (K := K) (L := L) v₀
  have hUniv :
      @Finset.univ
          {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀}
          (Fintype.ofEquiv (AbsoluteValueExtension v₀.1 L) eAbove.symm) =
        @Finset.univ
          {W : InfinitePlace L //
            _root_.infinitePlaceBelow (K := K) W = v₀}
          (Subtype.fintype fun W =>
            _root_.infinitePlaceBelow (K := K) W = v₀) := by
    ext W
    simp
  rw [hUniv]
  rfl

/-- The actual idele norm is continuous on the open integral-idele chart. -/
private theorem norm_comp_integralIdeleEmbedding_continuous :
    Continuous
      ((norm K L : IdeleGroup L → IdeleGroup K) ∘
        integralIdeleEmbedding L) := by
  let target :
      (InfiniteIdeleGroup L ×
          (∀ W : HeightOneSpectrum (𝓞 L),
            (W.adicCompletionIntegers L).units)) →
        IdeleGroup K :=
    fun a =>
      (ContinuousMulEquiv.piUnits.symm
          (integralInfiniteNormComponents K L a),
        RestrictedProduct.structureMap
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            (v₀.adicCompletion K)ˣ)
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            ((v₀.adicCompletionIntegers K).units :
              Set (v₀.adicCompletion K)ˣ))
          Filter.cofinite
          (integralFiniteNormComponents K L a))
  have hInfinite :
      Continuous (fun a =>
        ContinuousMulEquiv.piUnits.symm
          (integralInfiniteNormComponents K L a)) :=
    ContinuousMulEquiv.piUnits.symm.continuous.comp
      (integralInfiniteNormComponents_continuous K L)
  have hFinite :
      Continuous (fun a =>
        RestrictedProduct.structureMap
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            (v₀.adicCompletion K)ˣ)
          (fun v₀ : HeightOneSpectrum (𝓞 K) =>
            ((v₀.adicCompletionIntegers K).units :
              Set (v₀.adicCompletion K)ˣ))
          Filter.cofinite
          (integralFiniteNormComponents K L a)) :=
    (RestrictedProduct.isOpenEmbedding_structureMap
      (isOpen_finiteLocalUnits K)).continuous.comp
        (integralFiniteNormComponents_continuous K L)
  have hTarget : Continuous target :=
    hInfinite.prodMk hFinite
  rw [show
      ((norm K L : IdeleGroup L → IdeleGroup K) ∘
          integralIdeleEmbedding L) = target by
    funext a
    apply Prod.ext
    · exact norm_integralIdeleEmbedding_infinite K L a
    · exact norm_integralIdeleEmbedding_finite K L a]
  exact hTarget

/-- The norm on the idele group of a finite extension is continuous. -/
theorem norm_continuous :
    Continuous (norm K L) := by
  have hChartAt :
      ContinuousAt
        ((norm K L : IdeleGroup L → IdeleGroup K) ∘
          integralIdeleEmbedding L)
        (1 :
          InfiniteIdeleGroup L ×
            (∀ W : HeightOneSpectrum (𝓞 L),
              (W.adicCompletionIntegers L).units)) :=
    (norm_comp_integralIdeleEmbedding_continuous K L).continuousAt
  have hAt :
      ContinuousAt (norm K L) (1 : IdeleGroup L) := by
    have hAtChart :
        ContinuousAt (norm K L)
          (integralIdeleEmbedding L
            (1 :
              InfiniteIdeleGroup L ×
                (∀ W : HeightOneSpectrum (𝓞 L),
                  (W.adicCompletionIntegers L).units))) :=
      ((integralIdeleEmbedding_isOpenEmbedding L).continuousAt_iff
        (g := (norm K L : IdeleGroup L → IdeleGroup K))).mp hChartAt
    have hOne :
        integralIdeleEmbedding L
          (1 :
            InfiniteIdeleGroup L ×
              (∀ W : HeightOneSpectrum (𝓞 L),
                (W.adicCompletionIntegers L).units)) =
          (1 : IdeleGroup L) := by
      apply Prod.ext
      · rfl
      · apply RestrictedProduct.ext
        intro W
        rfl
    rw [hOne] at hAtChart
    exact hAtChart
  exact continuous_of_continuousAt_one (norm K L) hAt

/-- The idele norm bundled as a continuous monoid homomorphism. -/
noncomputable def ideleNormContinuousMonoidHom :
    IdeleGroup L →ₜ* IdeleGroup K where
  __ := norm K L
  continuous_toFun := norm_continuous K L

@[simp]
theorem ideleNormContinuousMonoidHom_apply
    (a : IdeleGroup L) :
    ideleNormContinuousMonoidHom K L a = norm K L a :=
  rfl

end IdeleGroup

end
