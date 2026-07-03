/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Basic

/-!
# ChannelCapacity.NonDegeneracy

Correct non-degeneracy conditions for uniqueness in the prior variable.

- `Kernel.priorPushforward`
- `Kernel.InjectivePriorPushforward`
- `Kernel.RowSeparating`
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

/-- The output prior map `p ↦ Σ_x p(x) k(x, ·)`. -/
noncomputable def priorPushforward (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : ProbabilityMeasure β :=
  outputPrior k p

/-- Pairwise-distinct rows of a kernel. This is weaker than injective prior pushforward. -/
def RowSeparating (k : Kernel α β) : Prop :=
  ∀ ⦃a a' : α⦄, a ≠ a' → k a ≠ k a'

/-- The correct non-degeneracy hypothesis for uniqueness in the prior variable. -/
def InjectivePriorPushforward (k : Kernel α β) [IsMarkovKernel k] : Prop :=
  Function.Injective (priorPushforward k)

/-- Reference measures needed by the strict-concavity proof: output marginals of priors that
dominate the given prior. -/
def OutputMarginalReference (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (ν : Measure β) : Prop :=
  ∃ q : ProbabilityMeasure α, p.toMeasure ≪ q.toMeasure ∧ ν = (outputPrior k q).toMeasure

/-- Measure-theoretic non-degeneracy bundle for the capacity theorem. Each prior's rows are
absolutely continuous with respect to the induced output marginal, and the joint KL divergence is
finite against the output-marginal references used in the strict-concavity argument. The chain-rule
field is the extra bridge needed for strict concavity: it isolates the positive output-marginal
correction term against an arbitrary dominating reference. -/
structure WellConditionedForCapacity (k : Kernel α β) [IsMarkovKernel k] : Prop where
  hRowAC : ∀ p : ProbabilityMeasure α,
    ∀ᵐ x ∂p.toMeasure, k x ≪ (outputPrior k p).toMeasure
  hFiniteRefKL : ∀ (p : ProbabilityMeasure α) (ν : Measure β),
    OutputMarginalReference k p ν →
      InformationTheory.klDiv (p.toMeasure ⊗ₘ k) (p.toMeasure ⊗ₘ Kernel.const _ ν) ≠ ∞
  hChainRule : ∀ (p : ProbabilityMeasure α) (ν : Measure β),
    OutputMarginalReference k p ν →
      InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const _ ν) =
        InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
          InformationTheory.klDiv (outputPrior k p).toMeasure ν

@[simp]
lemma priorPushforward_dirac (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    Kernel.priorPushforward k (MeasureTheory.diracProba a) =
      (⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩ :
        ProbabilityMeasure β) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  have hd : (MeasureTheory.diracProba a).toMeasure = Measure.dirac a := rfl
  simpa [priorPushforward, outputPrior, hd] using
    congrArg (fun μ : Measure β => μ s) (Measure.dirac_bind k.measurable a)

lemma priorPushforward_convexCombination (k : Kernel α β) [IsMarkovKernel k]
    (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    Kernel.priorPushforward k (ProbabilityMeasure.convexCombination p q t ht) =
      ProbabilityMeasure.convexCombination
        (Kernel.priorPushforward k p)
        (Kernel.priorPushforward k q)
        t ht := by
  apply ProbabilityMeasure.toMeasure_injective
  change k ∘ₘ (ProbabilityMeasure.convexCombination p q t ht).toMeasure =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [ProbabilityMeasure.convexCombination_toMeasure, Measure.comp_add]
  change k ∘ₘ ((t : ENNReal) • p.toMeasure) +
      k ∘ₘ ((((1 : NNReal) - t : NNReal) : ENNReal) • q.toMeasure) =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [Measure.comp_smul, Measure.comp_smul, ProbabilityMeasure.convexCombination_toMeasure]
  change t • (k ∘ₘ p.toMeasure) + (1 - (t : ENNReal)) • (k ∘ₘ q.toMeasure) =
    t • (k ∘ₘ p.toMeasure) + (1 - (t : ENNReal)) • (k ∘ₘ q.toMeasure)
  rfl

@[simp]
lemma priorPushforward_id (p : ProbabilityMeasure α) :
    Kernel.priorPushforward (Kernel.id : Kernel α α) p = p := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simp [priorPushforward, outputPrior]

lemma id_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward (Kernel.id : Kernel α α) := by
  intro p q hpq
  simpa using hpq

lemma outputMarginalReference_self
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    Kernel.OutputMarginalReference k p (outputPrior k p).toMeasure := by
  exact ⟨p, Measure.AbsolutelyContinuous.rfl, rfl⟩

end Kernel

end ChannelCapacity
