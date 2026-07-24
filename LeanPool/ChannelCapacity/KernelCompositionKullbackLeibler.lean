/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Kullback-Leibler divergence and kernel composition products

This file contains generic lemmas about Kullback-Leibler divergence and Radon-Nikodym derivatives
for composition products of measures and kernels.

It is designed to sit next to
`Mathlib/Probability/Kernel/Composition/RadonNikodym.lean` and
`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`.
The theorem `rnDeriv_compProd_right` supplies the kernel-only Radon-Nikodym description that is
left as a TODO in the former file, while `klDiv_compProd_right` packages the corresponding
pointwise-integral formula for Kullback-Leibler divergence.

## Main statements

* `InformationTheory.klDiv_map_measurableEquiv`: Kullback-Leibler divergence is invariant under a
  measurable equivalence.
* `ProbabilityTheory.rnDeriv_compProd_right`: the Radon-Nikodym derivative
  `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` is given by the Radon-Nikodym derivative of the kernels.
* `ProbabilityTheory.klDiv_compProd_right`: the Kullback-Leibler divergence
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` is the integral of the pointwise kernel divergences.

The last two lemmas complement the existing composition-product Radon-Nikodym and KL chain-rule
infrastructure in Mathlib, where the mixed-left-measure and additive chain-rule statements are
already available.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Kullback-Leibler divergence is invariant under a measurable equivalence. -/
lemma klDiv_map_measurableEquiv (e : α ≃ᵐ β) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]
  by_cases hμν : μ ≪ ν
  · have hmap : μ.map e ≪ ν.map e := e.measurableEmbedding.absolutelyContinuous_map hμν
    simp only [hμν, hmap, ↓reduceIte]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    simp [hx]
  · have hmap : ¬ μ.map e ≪ ν.map e := by
      intro h
      have h' := e.symm.measurableEmbedding.absolutelyContinuous_map h
      exact hμν (by simpa using h')
    simp [hμν, hmap]

end InformationTheory

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The Radon-Nikodym derivative of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η` is the pointwise
Radon-Nikodym derivative of the kernels. -/
theorem rnDeriv_compProd_right
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ κ.rnDeriv η p.1 p.2 := by
  have hs : μ ⊗ₘ κ.singularPart η ⟂ₘ μ ⊗ₘ η :=
    MeasureTheory.Measure.MutuallySingular.compProd_of_right _ _
      (.of_forall <| Kernel.mutuallySingular_singularPart _ _)
  have hadd :
      μ ⊗ₘ κ = μ ⊗ₘ κ.singularPart η
        + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
    calc
      μ ⊗ₘ κ
        = μ ⊗ₘ (Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η) := by
            rw [Kernel.rnDeriv_add_singularPart]
      _ = μ ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η) + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_add_right]
      _ = (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2)
          + μ ⊗ₘ Kernel.singularPart κ η := by
            rw [Measure.compProd_withDensity]
            exact κ.measurable_rnDeriv η
      _ = μ ⊗ₘ Kernel.singularPart κ η
          + (μ ⊗ₘ η).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2) := by
            rw [add_comm]
  exact (Measure.eq_rnDeriv (κ.measurable_rnDeriv η) hs hadd).symm

/-- The Kullback-Leibler divergence of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η` is the integral of the
pointwise kernel divergences. -/
theorem klDiv_compProd_right
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  have h_kernel_ac : ∀ᵐ a ∂μ, κ a ≪ η a :=
    (Measure.absolutelyContinuous_compProd_right_iff).mp h_ac
  have hmeas :
      Measurable
        (fun p : α × β ↦
          ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η p.1 p.2).toReal))) := by
    exact
      (InformationTheory.measurable_klFun.comp
        (κ.measurable_rnDeriv η).ennreal_toReal).ennreal_ofReal
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
  calc
    ∫⁻ p, ENNReal.ofReal
        (InformationTheory.klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂μ ⊗ₘ η
      = ∫⁻ p,
          ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂μ ⊗ₘ η := by
          refine lintegral_congr_ae ?_
          exact (rnDeriv_compProd_right (μ := μ) (κ := κ) (η := η)).mono fun p hp => by
            simp [hp]
    _ = ∫⁻ a,
          ∫⁻ b, ENNReal.ofReal (InformationTheory.klFun ((κ.rnDeriv η a b).toReal)) ∂η a ∂μ := by
          rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [h_kernel_ac] with a ha
          rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac ha]
          refine lintegral_congr_ae ?_
          exact (κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)).mono fun x hx => by
            simp [hx]

end ProbabilityTheory
