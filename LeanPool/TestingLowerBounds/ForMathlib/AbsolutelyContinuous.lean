/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.RadonNikodym
import LeanPool.TestingLowerBounds.ForMathlib.KernelFstSnd

/-!
# Bridging `Measure.compProd` and `Kernel.compProd`

A handful of helper lemmas relating compositions of measures and kernels that have not yet
been merged into Mathlib.
-/

open ProbabilityTheory MeasurableSpace Set

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α γ}

lemma mutuallySingular_compProd_left (hμν : μ ⟂ₘ ν) (κ η : Kernel α γ) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  by_cases hκ : IsSFiniteKernel κ
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hκ]; simp
  by_cases hη : IsSFiniteKernel η
  swap; · rw [compProd_of_not_isSFiniteKernel _ _ hη]; simp
  refine ⟨hμν.nullSet ×ˢ univ, hμν.measurableSet_nullSet.prod .univ, ?_⟩
  rw [compProd_apply_prod hμν.measurableSet_nullSet .univ, compl_prod_eq_union]
  simp only [MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [compProd_apply_prod hμν.measurableSet_nullSet.compl .univ]
  simp

lemma mutuallySingular_compProd_iff_of_same_right (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel α γ) [IsFiniteKernel κ] [hκ : ∀ x, NeZero (κ x)] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ κ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_left h _ _⟩
  rw [← withDensity_rnDeriv_eq_zero]
  have hh := mutuallySingular_of_mutuallySingular_compProd h ?_ ?_ (ξ  := ν.withDensity (∂μ/∂ν))
  rotate_left
  · exact absolutelyContinuous_of_le (μ.withDensity_rnDeriv_le ν)
  · exact withDensity_absolutelyContinuous _ _
  simp_rw [MutuallySingular.self_iff, (hκ _).ne] at hh
  exact ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hh)

lemma absolutelyContinuous_compProd_of_compProd'
    [SigmaFinite μ] [SigmaFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  rw [ν.haveLebesgueDecomposition_add μ, compProd_add_left, add_comm] at hκη
  have h : μ ⊗ₘ κ ≪ μ.withDensity (∂ν/∂μ) ⊗ₘ η :=
    absolutelyContinuous_of_add_of_mutuallySingular hκη
      (mutuallySingular_compProd_left (mutuallySingular_singularPart _ _).symm _ _)
  refine h.trans ?_
  exact (withDensity_absolutelyContinuous _ _).compProd_left _

variable [CountableOrCountablyGenerated α γ]

lemma mutuallySingular_compProd_right
    (μ ν : Measure α) {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η :=
  MutuallySingular.compProd_of_right μ ν hκη

lemma mutuallySingular_compProd_right'
    (μ ν : Measure α) {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂ν, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  by_cases hμ : SFinite μ
  swap; · rw [compProd_of_not_sfinite _ _ hμ]; simp
  by_cases hν : SFinite ν
  swap; · rw [compProd_of_not_sfinite _ _ hν]; simp
  refine (mutuallySingular_compProd_right _ _ ?_).symm
  simp_rw [MutuallySingular.comm, hκη]

lemma mutuallySingular_compProd_iff_of_same_left (μ : Measure α) [SFinite μ]
    (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ μ ⊗ₘ η ↔ ∀ᵐ a ∂μ, κ a ⟂ₘ η a := by
  refine ⟨fun h ↦ ?_, fun h ↦ mutuallySingular_compProd_right _ _ h⟩
  exact mutuallySingular_of_mutuallySingular_compProd h (fun _ a ↦ a) (fun _ a ↦ a)

end MeasureTheory.Measure

open MeasureTheory

lemma ProbabilityTheory.Kernel.absolutelyContinuous_compProd_iff
    {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
    [CountableOrCountablyGenerated β γ] {κ₁ η₁ : Kernel α β}
    {κ₂ η₂ : Kernel (α × β) γ} [IsFiniteKernel κ₁] [IsFiniteKernel η₁] [IsFiniteKernel κ₂]
    [IsFiniteKernel η₂] (a : α) [∀ b, NeZero (κ₂ (a, b))] :
    (κ₁ ⊗ₖ κ₂) a ≪ (η₁ ⊗ₖ η₂) a ↔ κ₁ a ≪ η₁ a ∧ ∀ᵐ b ∂κ₁ a, κ₂ (a, b) ≪ η₂ (a, b) := by
  rw [Kernel.compProd_apply_eq_compProd_snd', Kernel.compProd_apply_eq_compProd_snd',
    Measure.absolutelyContinuous_compProd_iff, Measure.absolutelyContinuous_compProd_right_iff]
  simp_rw [Kernel.snd'_apply]
