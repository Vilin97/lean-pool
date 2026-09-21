/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
/-!
# Finiteness of localized-completion Herbrand groups
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandH0Finite
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
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
    Finite
      (HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ) := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0) :=
    hcard.finiteH0
  exact Finite.of_equiv
    (Multiplicative
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0))
    (localHerbrandH0EquivUnitsTateH0
      vK hvK w).symm.toEquiv

theorem localHerbrandHMinusOneFinite
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
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
    Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard.cardHminusOne]
    exact one_ne_zero
  exact Finite.of_equiv
    (tateCohomology
      (Rep.ofAlgebraAutOnUnits vK.Completion
        (LocalizedCompletion vK w)) (-1))
    (localHerbrandHMinusOneEquivUnitsTateHminusOne
      vK hvK w σ hgen).symm


end LocalTateComparison

end LocalClassFieldTheory
