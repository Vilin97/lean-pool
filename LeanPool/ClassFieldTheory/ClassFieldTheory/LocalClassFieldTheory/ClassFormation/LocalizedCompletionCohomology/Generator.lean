/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
/-!
# A generator of a localized finite Galois group
-/

@[expose] public section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

universe u v

variable {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L]

/-- The canonical finite structure on the decomposition group used by the
localized low-degree cohomology calculations. -/
@[reducible]
noncomputable def localizedCompletionDecompositionGroupFintype
    (vK : AbsoluteValue K ℝ)
    (w : AbsoluteValueExtension vK L) :
    Fintype (absoluteValueDecompositionGroup K w.1) :=
  Fintype.ofFinite _

/-- A generator of the localized Galois group induced by a chosen generator
of the global cyclic Galois group. -/
noncomputable def localizedCompletionGaloisGenerator
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    LocalizedCompletion vK w ≃ₐ[vK.Completion]
      LocalizedCompletion vK w :=
  (decompositionGroupEquivAlgebraicLocalizationAut
    vK hvK w)
      (subgroupGeneratorOfGenerator
        (absoluteValueDecompositionGroup K w.1) σ hgen)

theorem localizedCompletionGaloisGenerator_generates
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    ∀ τ : LocalizedCompletion vK w ≃ₐ[vK.Completion]
        LocalizedCompletion vK w,
      τ ∈ Subgroup.zpowers
        (localizedCompletionGaloisGenerator
          vK hvK w σ hgen) := by
  let := localizedCompletionBaseAlgebra vK w
  let H := absoluteValueDecompositionGroup K w.1
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let δ :=
    subgroupGeneratorOfGenerator H σ hgen
  intro τ
  rw [show localizedCompletionGaloisGenerator
      vK hvK w σ hgen = e δ from rfl]
  change τ ∈ Subgroup.zpowers (e.toMonoidHom δ)
  rw [← MonoidHom.map_zpowers e.toMonoidHom δ]
  refine ⟨e.symm τ, ?_, e.apply_symm_apply τ⟩
  exact subgroupGeneratorOfGenerator_generates
    H σ hgen (e.symm τ)

end LocalClassFieldTheory
