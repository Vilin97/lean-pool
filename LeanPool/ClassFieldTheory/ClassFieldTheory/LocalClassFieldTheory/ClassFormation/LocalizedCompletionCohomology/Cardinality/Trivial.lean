/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
/-!
# Triviality of localized degree-minus-one Herbrand cohomology
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

theorem localHerbrandHMinusOne_eq_one
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
    ∀ c : HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen),
      c = 1 := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let _ : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let _ : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let _ := localizedCompletionDecompositionGroupFintype vK w
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let _ : Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    localHerbrandHMinusOneFinite
      vK hvK w σ hgen
  have hcard :
      Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) = 1 := by
    exact localHerbrandHMinusOne_card_eq_one
      vK hvK w σ hgen
  let _ : Subsingleton
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro c
  exact Subsingleton.elim c 1


end LocalTateComparison

end LocalClassFieldTheory
