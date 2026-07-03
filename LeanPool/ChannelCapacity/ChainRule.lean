/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Basic
import LeanPool.ChannelCapacity.KernelCompositionKullbackLeibler

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Posterior

/-!
# ChannelCapacity.ChainRule

Bridge lemmas relating mutual information to KL divergences against fixed output references.

The main theorem rewrites the KL divergence from the joint law `p ⊗ k` to the product
`p ⊗ const ν` as the mutual information plus the KL divergence of the induced output law
against `ν`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

open InformationTheory

theorem klDiv_mutualInformation_chain
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) (ν : Measure β)
    [IsFiniteMeasure ν] :
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
      klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        klDiv (outputPrior k p).toMeasure ν := by
  let e : (α × β) ≃ᵐ (β × α) := MeasurableEquiv.prodComm
  let post : Kernel β α := k†p.toMeasure
  have hswap_joint :
      ((jointLaw k p).toMeasure).map e = (outputPrior k p).toMeasure ⊗ₘ post := by
    simpa [jointLaw_toMeasure, outputPrior_toMeasure, e, post] using
      (ProbabilityTheory.compProd_posterior_eq_map_swap (κ := k) (μ := p.toMeasure)).symm
  have hswap_const :
      (p.toMeasure ⊗ₘ Kernel.const α ν).map e = ν ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [e] using
      (by
        rw [Measure.compProd_const, Measure.prod_swap, ← Measure.compProd_const] :
          (p.toMeasure ⊗ₘ Kernel.const α ν).map Prod.swap =
            ν ⊗ₘ Kernel.const β p.toMeasure)
  have hswap_indep :
      ((independentJointLaw k p).toMeasure).map e =
        (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [independentJointLaw_toMeasure, e] using
      (by
        rw [independentJointLaw_toMeasure, Measure.compProd_const, Measure.prod_swap,
          ← Measure.compProd_const] :
          (independentJointLaw k p).toMeasure.map Prod.swap =
            (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure)
  have hleft :
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
    calc
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
          klDiv (((jointLaw k p).toMeasure).map e) ((p.toMeasure ⊗ₘ Kernel.const α ν).map e) := by
            symm
            exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
              (p.toMeasure ⊗ₘ Kernel.const α ν)
      _ = klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
        rw [hswap_joint, hswap_const]
  have hright :
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
        klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
    calc
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
          klDiv (((jointLaw k p).toMeasure).map e)
            (((independentJointLaw k p).toMeasure).map e) := by
            rw [hswap_joint, hswap_indep]
      _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
        exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure
  calc
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := hleft
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
            ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) := by
          rw [InformationTheory.klDiv_compProd_eq_add]
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
          rw [hright]
    _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
          klDiv (outputPrior k p).toMeasure ν := by
          rw [add_comm]

end ChannelCapacity
