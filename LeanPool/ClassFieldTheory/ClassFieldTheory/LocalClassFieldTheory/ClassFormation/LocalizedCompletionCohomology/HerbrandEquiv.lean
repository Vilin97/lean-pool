/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
/-!
# Low-degree Herbrand equivalences for a localized completion
-/

@[expose] public section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable
section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

/-- Degree-zero multiplicative Herbrand cohomology for a decomposition group
identified with degree-zero Tate cohomology of the localized field units. -/
noncomputable def localHerbrandH0EquivUnitsTateH0
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      Multiplicative
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eTate :
      (unitsInvariantSubmodule vK.Completion
          (LocalizedCompletion vK w) ⧸
        unitsTateH0NormSubmodule vK.Completion
          (LocalizedCompletion vK w)) ≃+
        tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 :=
    (tateUnitsH0IsoInvariantsQuotient
      vK.Completion
      (LocalizedCompletion vK w)).symm.toLinearEquiv.toAddEquiv
  exact
    (herbrandH0CompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ) e).trans
      ((herbrandH0MulEquivInvariantsNormQuotient
        vK.Completion (LocalizedCompletion vK w)).trans
          eTate.toMultiplicative)

/-- Degree-minus-one multiplicative Herbrand cohomology for a decomposition
group identified with degree-minus-one Tate cohomology of localized units. -/
noncomputable def localHerbrandHMinusOneEquivUnitsTateHminusOne
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1) σ hgen) ≃
      tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let δ :=
    subgroupGeneratorOfGenerator
      (absoluteValueDecompositionGroup k w.1) σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  exact
    (herbrandHMinusOneCompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ)
      e δ).toEquiv.trans
      (herbrandHminusOneEquivUnitsTateHminusOne
        vK.Completion (LocalizedCompletion vK w)
        g hg)

/-- Degree-zero Herbrand cohomology for a decomposition group identified with
the norm quotient of the localized field extension. -/
noncomputable def localHerbrandH0EquivNormQuotient
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      NormQuotient vK.Completion
        (LocalizedCompletion vK w) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  let e0 :=
    localHerbrandH0EquivUnitsTateH0 vK hvK w
  let eAdd :
      tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 ≃+
        Additive
          (NormQuotient vK.Completion
            (LocalizedCompletion vK w)) :=
    (H0TateUnitsIsoNormQuotient
      vK.Completion
      (LocalizedCompletion vK w)).toLinearEquiv.toAddEquiv
  exact e0.trans <|
    eAdd.toMultiplicative.trans <|
      MulEquiv.multiplicativeAdditive
        (NormQuotient vK.Completion
          (LocalizedCompletion vK w))


end LocalTateComparison

end LocalClassFieldTheory
