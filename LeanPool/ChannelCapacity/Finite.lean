/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Capacity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# ChannelCapacity.Finite

Finite-alphabet capacity-achieving prior uniqueness.

This file specializes the general development to finite measurable alphabets. In that setting,
Shannon entropy gives an explicit formula for mutual information, so continuity and strict
concavity can be proved internally without passing abstract topology or semicontinuity hypotheses
through the public theorem statement.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace ChannelCapacity

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

namespace ProbabilityMeasure

/-- Shannon entropy on a finite measurable alphabet, in nats. -/
noncomputable def entropy (μ : ProbabilityMeasure α) : ℝ :=
  ∑ a, Real.negMulLog ((μ.toMeasure {a}).toReal)

end ProbabilityMeasure

namespace Kernel

/-- A concrete finite non-degeneracy condition: the row matrix has trivial kernel over `ℝ`. -/
def RowMatrixFullRank (k : Kernel α β) : Prop :=
  Function.Injective fun w : α → ℝ =>
    fun b => ∑ a, w a * (k a {b}).toReal

end Kernel

section DiscreteKL

omit [Fintype α] in
lemma toMeasure_eq_count_withDensity (μ : ProbabilityMeasure α) :
    [Countable α] → μ.toMeasure = Measure.count.withDensity (fun a => μ.toMeasure {a}) := by
  intro _instCountable
  ext s hs
  rw [MeasureTheory.withDensity_apply _ hs, ← MeasureTheory.lintegral_indicator hs,
    MeasureTheory.lintegral_count]
  simpa using (μ.toMeasure.tsum_indicator_apply_singleton s hs).symm

omit [Fintype α] in
lemma rnDeriv_count_ae (μ : ProbabilityMeasure α) :
    [Countable α] →
      μ.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] fun a => μ.toMeasure {a} := by
  intro _instCountable
  have hcount :
      Measure.count.withDensity (fun a : α => μ.toMeasure {a}) = μ.toMeasure :=
    (toMeasure_eq_count_withDensity (μ := μ)).symm
  simpa [hcount] using
    (Measure.rnDeriv_withDensity
      (ν := Measure.count)
      (f := fun a : α => μ.toMeasure {a})
      (measurable_of_countable (fun a : α => μ.toMeasure {a})))

omit [Fintype α] [MeasurableSingletonClass α] in
lemma klFun_singletonMass (μ : ProbabilityMeasure α) (a : α) :
    InformationTheory.klFun ((μ.toMeasure {a}).toReal) =
      1 - (μ.toMeasure {a}).toReal - Real.negMulLog ((μ.toMeasure {a}).toReal) := by
  rw [InformationTheory.klFun, Real.negMulLog]
  ring

lemma toReal_klDiv_count (μ : ProbabilityMeasure α) :
    (InformationTheory.klDiv μ.toMeasure Measure.count).toReal =
      (Fintype.card α : ℝ) - 1 - ProbabilityMeasure.entropy μ := by
  let _instCountable : Countable α := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := by
    rw [toMeasure_eq_count_withDensity (μ := μ)]
    exact withDensity_absolutelyContinuous _ _
  have h_rn : ∀ a : α, μ.toMeasure.rnDeriv Measure.count a = μ.toMeasure {a} := by
    simpa using (Measure.ae_count_iff.mp (rnDeriv_count_ae (μ := μ)))
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun h_ac, MeasureTheory.integral_count]
  simp_rw [h_rn, klFun_singletonMass (μ := μ)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  have hprob : ∑ a, (μ.toMeasure {a}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]
  rw [ProbabilityMeasure.entropy, hprob, Finset.card_univ]
  ring

lemma sum_toReal_singletonMass (μ : ProbabilityMeasure α) :
    ∑ a, (μ.toMeasure {a}).toReal = 1 := by
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]

end DiscreteKL

section EntropyFormula

/-- The probability measure associated to a kernel row. -/
noncomputable def Kernel.rowProbabilityMeasure (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    ProbabilityMeasure β :=
  ⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩

/-- Row entropy for a finite Markov kernel. -/
noncomputable def Kernel.rowEntropy (k : Kernel α β) [IsMarkovKernel k] (a : α) : ℝ :=
  ProbabilityMeasure.entropy (Kernel.rowProbabilityMeasure k a)

/-- Conditional output entropy, linear in the prior. -/
noncomputable def conditionalEntropy (p : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] : ℝ :=
  ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The KL divergence of a kernel row against counting measure is the usual finite entropy
expression. -/
lemma Kernel.toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy
    (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    (InformationTheory.klDiv (k a) Measure.count).toReal =
      (Fintype.card β : ℝ) - 1 - Kernel.rowEntropy k a := by
  simpa [Kernel.rowEntropy, Kernel.rowProbabilityMeasure] using
    (toReal_klDiv_count (Kernel.rowProbabilityMeasure k a))

/-- Averaging the row KL divergences against counting measure recovers the conditional entropy. -/
lemma weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ∑ a, (p.toMeasure {a}).toReal * (InformationTheory.klDiv (k a) Measure.count).toReal =
      (Fintype.card β : ℝ) - 1 - conditionalEntropy p k := by
  have hprob := sum_toReal_singletonMass p
  calc
    ∑ a, (p.toMeasure {a}).toReal * (InformationTheory.klDiv (k a) Measure.count).toReal
      = ∑ a, (p.toMeasure {a}).toReal *
          ((Fintype.card β : ℝ) - 1 - Kernel.rowEntropy k a) := by
            simp_rw [Kernel.toReal_klDiv_count_eq_card_sub_one_sub_rowEntropy]
    _ = ∑ a,
          ((p.toMeasure {a}).toReal * ((Fintype.card β : ℝ) - 1) -
            (p.toMeasure {a}).toReal * Kernel.rowEntropy k a) := by
          simp_rw [mul_sub]
    _ = (∑ a, (p.toMeasure {a}).toReal * ((Fintype.card β : ℝ) - 1)) -
          ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ a, (p.toMeasure {a}).toReal) * ((Fintype.card β : ℝ) - 1) -
          conditionalEntropy p k := by
          rw [Finset.sum_mul, conditionalEntropy]
    _ = (Fintype.card β : ℝ) - 1 - conditionalEntropy p k := by
          rw [hprob]
          ring

omit [Fintype α] in
lemma convexCombination_toReal_apply (p q : ProbabilityMeasure α) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) (a : α) :
    ((ProbabilityMeasure.convexCombination p q t ht).toMeasure {a}).toReal =
      (t : ℝ) * (p.toMeasure {a}).toReal + (1 - (t : ℝ)) * (q.toMeasure {a}).toReal := by
  rw [ProbabilityMeasure.convexCombination_apply _ _ _ _ (measurableSet_singleton a)]
  have hp_fin : p.toMeasure {a} ≠ ∞ := measure_ne_top _ _
  have hq_fin : q.toMeasure {a} ≠ ∞ := measure_ne_top _ _
  have hleft_fin : ((t : ENNReal) * p.toMeasure {a}) ≠ ∞ := ENNReal.mul_ne_top (by simp) hp_fin
  have hright_fin :
      ((((1 : NNReal) - t : NNReal) : ENNReal) * q.toMeasure {a}) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hq_fin
  rw [ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_mul, ENNReal.toReal_mul]
  change (t : ℝ) * (p.toMeasure {a}).toReal + (((1 : NNReal) - t : NNReal) : ℝ) *
      (q.toMeasure {a}).toReal =
    (t : ℝ) * (p.toMeasure {a}).toReal + (1 - (t : ℝ)) * (q.toMeasure {a}).toReal
  rw [NNReal.coe_sub ht]
  simp

omit [MeasurableSingletonClass β] in
lemma conditionalEntropy_convexCombination (p q : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] (t : NNReal) (ht : t ≤ (1 : NNReal)) :
    conditionalEntropy (ProbabilityMeasure.convexCombination p q t ht) k =
      (t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k := by
  unfold conditionalEntropy
  simp_rw [convexCombination_toReal_apply, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

omit [Fintype α] [MeasurableSingletonClass α] in
lemma absolutelyContinuous_count (μ : ProbabilityMeasure α) :
    μ.toMeasure ≪ Measure.count := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero => ?_
  rw [Measure.count_eq_zero_iff] at hs_zero
  simp [hs_zero]

omit [Fintype β] in
lemma outputPrior_apply_singleton (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    (outputPrior k p).toMeasure {b} = ∑ a, p.toMeasure {a} * k a {b} := by
  calc
    (outputPrior k p).toMeasure {b}
      = (Measure.sum fun a : α => p.toMeasure {a} • k a) {b} := by
          rw [outputPrior_toMeasure, Measure.comp_eq_sum_of_countable]
    _ = ∑' a : α, (p.toMeasure {a} • k a) {b} := by
          rw [Measure.sum_apply _ (measurableSet_singleton b)]
    _ = ∑' a : α, p.toMeasure {a} * k a {b} := by
          simp [Measure.smul_apply]
    _ = ∑ a, p.toMeasure {a} * k a {b} := by
          rw [tsum_fintype]

omit [Fintype β] in
lemma toReal_outputPrior_apply_singleton (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (b : β) :
    ((outputPrior k p).toMeasure {b}).toReal =
      ∑ a, (p.toMeasure {a}).toReal * (k a {b}).toReal := by
  rw [outputPrior_apply_singleton]
  rw [ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_mul]
  · intro a _ha
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

omit [Fintype β] in
lemma klDiv_count_ne_top (μ : ProbabilityMeasure β) [Finite β] :
    InformationTheory.klDiv μ.toMeasure Measure.count ≠ ∞ := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableβ : Countable β := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := absolutelyContinuous_count μ
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac, MeasureTheory.lintegral_count,
    tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

omit [Fintype α] [Fintype β] in
lemma joint_klDiv_count_ne_top (k : Kernel α β) [IsMarkovKernel k] [Finite α] [Finite β]
    (p : ProbabilityMeasure α) :
    InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    rw [jointLaw_toMeasure]
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl, MeasureTheory.lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun a _ha =>
    ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)

omit [Fintype β] in
lemma toReal_joint_klDiv_count (k : Kernel α β) [IsMarkovKernel k] [Finite β]
    (p : ProbabilityMeasure α) :
    (InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
      ∑ a, (p.toMeasure {a}).toReal *
        (InformationTheory.klDiv (k a) Measure.count).toReal := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl]
  have hsum :
      ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure =
        ∑ a, InformationTheory.klDiv (k a) Measure.count * p.toMeasure {a} := by
    simpa [mul_comm] using
      (MeasureTheory.lintegral_fintype
        (μ := p.toMeasure)
        (f := fun a : α => InformationTheory.klDiv (k a) Measure.count))
  have hsum_toReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum] at hsum_toReal
  · simpa [ENNReal.toReal_mul, Kernel.rowProbabilityMeasure, toReal_klDiv_count, mul_comm] using
      hsum_toReal
  · intro a _ha
    exact ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)

theorem mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy
    (k : Kernel α β) [IsMarkovKernel k] [Finite β] (p : ProbabilityMeasure α) :
    mutualInformation p k =
      ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  let _instDiscreteMeasurableα : DiscreteMeasurableSpace α := by infer_instance
  let _instStandardBorelα : StandardBorelSpace α := by infer_instance
  let _instNonemptyα : Nonempty α := p.nonempty
  have h_chain :=
    klDiv_mutualInformation_chain (k := k) (p := p) (ν := Measure.count)
  have h_left_fin : InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ :=
    joint_klDiv_count_ne_top k p
  have h_out_fin : InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count ≠ ∞ :=
    klDiv_count_ne_top (outputPrior k p)
  have h_mi_fin :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure ≠ ∞ := by
    intro h_top
    have h_left_top :
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count) = ∞ := by
      calc
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (p.toMeasure ⊗ₘ Kernel.const α Measure.count)
            =
              InformationTheory.klDiv
                (jointLaw k p).toMeasure
                (independentJointLaw k p).toMeasure +
                  InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := h_chain
        _ = ∞ + InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count := by rw [h_top]
        _ = ∞ := by simp
    exact h_left_fin h_left_top
  have h_chain_real : (InformationTheory.klDiv
      (jointLaw k p).toMeasure
      (p.toMeasure ⊗ₘ Kernel.const α Measure.count)).toReal =
        mutualInformation p k +
          (InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count).toReal := by
    have h_chain_real' := congrArg ENNReal.toReal h_chain
    rw [ENNReal.toReal_add h_mi_fin h_out_fin] at h_chain_real'
    simpa [mutualInformation, jointLaw_toMeasure, independentJointLaw_toMeasure,
      outputPrior_toMeasure]
      using h_chain_real'
  have h_output :
      (InformationTheory.klDiv (outputPrior k p).toMeasure Measure.count).toReal =
        (Fintype.card β : ℝ) - 1 - ProbabilityMeasure.entropy (outputPrior k p) := by
    simpa [ProbabilityMeasure.entropy] using toReal_klDiv_count (outputPrior k p)
  rw [toReal_joint_klDiv_count,
    weighted_toReal_klDiv_count_eq_card_sub_one_sub_conditionalEntropy, h_output] at h_chain_real
  have h_formula :
      mutualInformation p k =
        ProbabilityMeasure.entropy (outputPrior k p) - conditionalEntropy p k := by
    linarith
  linarith

theorem entropy_strictlyConcave (p q : ProbabilityMeasure α) (h_ne : p ≠ q)
    (t : NNReal) (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    ProbabilityMeasure.entropy (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
      (t : ℝ) * ProbabilityMeasure.entropy p + (1 - (t : ℝ)) * ProbabilityMeasure.entropy q := by
  have hneq_coord : ∃ a : α, (p.toMeasure {a}).toReal ≠ (q.toMeasure {a}).toReal := by
    by_contra h_eq
    have h_eq' : ∀ a : α, (p.toMeasure {a}).toReal = (q.toMeasure {a}).toReal := by
      simpa using not_exists.mp h_eq
    apply h_ne
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_singleton
    intro a
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h_eq' a)
  obtain ⟨a0, ha0⟩ := hneq_coord
  have ht_pos' : 0 < (t : ℝ) := by exact_mod_cast ht_pos
  have h1mt_pos : 0 < 1 - (t : ℝ) := by
    linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
  have hle :
      ∀ a : α,
        (t : ℝ) * Real.negMulLog ((p.toMeasure {a}).toReal) +
            (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a}).toReal) ≤
          Real.negMulLog (((ProbabilityMeasure.convexCombination p q t
            (le_of_lt ht_lt_one)).toMeasure {a}).toReal) := by
    intro a
    rw [convexCombination_toReal_apply]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (Real.concaveOn_negMulLog.2
        (ENNReal.toReal_nonneg : (p.toMeasure {a}).toReal ∈ Set.Ici (0 : ℝ))
        (ENNReal.toReal_nonneg : (q.toMeasure {a}).toReal ∈ Set.Ici (0 : ℝ))
        (show 0 ≤ (t : ℝ) by exact_mod_cast (le_of_lt ht_pos))
        (show 0 ≤ 1 - (t : ℝ) by linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one])
        (by ring : (t : ℝ) + (1 - (t : ℝ)) = 1))
  have hlt :
      (t : ℝ) * Real.negMulLog ((p.toMeasure {a0}).toReal) +
          (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a0}).toReal) <
        Real.negMulLog (((ProbabilityMeasure.convexCombination p q t
          (le_of_lt ht_lt_one)).toMeasure {a0}).toReal) := by
    rw [convexCombination_toReal_apply]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (Real.strictConcaveOn_negMulLog.2
        (ENNReal.toReal_nonneg : (p.toMeasure {a0}).toReal ∈ Set.Ici (0 : ℝ))
        (ENNReal.toReal_nonneg : (q.toMeasure {a0}).toReal ∈ Set.Ici (0 : ℝ))
        ha0 ht_pos' h1mt_pos
        (by ring : (t : ℝ) + (1 - (t : ℝ)) = 1))
  have hweighted :
      (t : ℝ) * ProbabilityMeasure.entropy p + (1 - (t : ℝ)) * ProbabilityMeasure.entropy q =
        ∑ a,
          ((t : ℝ) * Real.negMulLog ((p.toMeasure {a}).toReal) +
            (1 - (t : ℝ)) * Real.negMulLog ((q.toMeasure {a}).toReal)) := by
    rw [ProbabilityMeasure.entropy, ProbabilityMeasure.entropy, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
  rw [ProbabilityMeasure.entropy, hweighted]
  simpa [gt_iff_lt] using Finset.sum_lt_sum (fun a _ha => hle a) ⟨a0, Finset.mem_univ _, hlt⟩

omit [Fintype β] in
theorem Kernel.injectivePriorPushforward_of_rowMatrixFullRank
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    Kernel.InjectivePriorPushforward k := by
  intro p q hpq
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  have hrowEq :
      ∀ b : β,
        ∑ a, ((p.toMeasure {a}).toReal - (q.toMeasure {a}).toReal) * (k a {b}).toReal = 0 := by
    intro b
    have hb :
        ((outputPrior k p).toMeasure {b}).toReal = ((outputPrior k q).toMeasure {b}).toReal := by
      simpa [Kernel.priorPushforward] using
        congrArg (fun μ : ProbabilityMeasure β => ((μ.toMeasure {b}).toReal)) hpq
    rw [toReal_outputPrior_apply_singleton, toReal_outputPrior_apply_singleton] at hb
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hb
  have hweights :
      (fun a' : α => (p.toMeasure {a'}).toReal - (q.toMeasure {a'}).toReal) = 0 := by
    apply hRank
    funext b
    simpa using hrowEq b
  have ha_toReal : (p.toMeasure {a}).toReal = (q.toMeasure {a}).toReal := by
    have ha_sub : (p.toMeasure {a}).toReal - (q.toMeasure {a}).toReal = 0 := by
      simpa using congrArg (fun w : α → ℝ => w a) hweights
    exact sub_eq_zero.mp ha_sub
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ha_toReal

omit [Fintype β] in
theorem Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  intro p q h_ne t ht_pos ht_lt_one
  have hPush : Kernel.InjectivePriorPushforward k :=
    Kernel.injectivePriorPushforward_of_rowMatrixFullRank k hRank
  have hOut_ne : outputPrior k p ≠ outputPrior k q := by
    intro hEq
    exact h_ne (hPush hEq)
  have hEntropy :
      ProbabilityMeasure.entropy
          (ProbabilityMeasure.convexCombination (outputPrior k p) (outputPrior k q) t
            (le_of_lt ht_lt_one)) >
        (t : ℝ) * ProbabilityMeasure.entropy (outputPrior k p) +
          (1 - (t : ℝ)) * ProbabilityMeasure.entropy (outputPrior k q) :=
    entropy_strictlyConcave (outputPrior k p) (outputPrior k q) hOut_ne t ht_pos ht_lt_one
  calc
    mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k =
        ProbabilityMeasure.entropy
            (ProbabilityMeasure.convexCombination (outputPrior k p) (outputPrior k q) t
              (le_of_lt ht_lt_one)) -
          ((t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k) := by
            rw [mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
            rw [conditionalEntropy_convexCombination]
            simpa [Kernel.priorPushforward] using
              congrArg ProbabilityMeasure.entropy
                (Kernel.priorPushforward_convexCombination k p q t (le_of_lt ht_lt_one))
    _ > ((t : ℝ) * ProbabilityMeasure.entropy (outputPrior k p) +
            (1 - (t : ℝ)) * ProbabilityMeasure.entropy (outputPrior k q)) -
          ((t : ℝ) * conditionalEntropy p k + (1 - (t : ℝ)) * conditionalEntropy q k) := by
            gcongr
    _ = (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
          rw [mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy,
            mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy]
          ring

section FiniteWeakTopology

variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]

/-- The indicator of the singleton `{a}` as a continuous bundled map, using that `α` is discrete. -/
noncomputable def singletonIndicatorContinuousMap (a : α) : C(α, ℝ) :=
  ⟨({a} : Set α).indicator (fun _ => (1 : ℝ)), continuous_of_discreteTopology⟩

omit [Fintype α] in
lemma continuous_toReal_apply_singleton (a : α) :
    Continuous fun p : ProbabilityMeasure α => (p.toMeasure {a}).toReal := by
  let f : C(α, ℝ) := singletonIndicatorContinuousMap a
  simpa [f, singletonIndicatorContinuousMap, measureReal_def, integral_indicator_one] using
    (ProbabilityMeasure.continuous_integral_continuousMap f)

lemma continuous_entropy :
    Continuous fun p : ProbabilityMeasure α => ProbabilityMeasure.entropy p := by
  simpa [ProbabilityMeasure.entropy] using
    (continuous_finsetSum (s := Finset.univ) fun a _ha =>
      Real.continuous_negMulLog.comp (continuous_toReal_apply_singleton a))

omit [TopologicalSpace α] [DiscreteTopology α] [BorelSpace α] [CompactSpace α] in
lemma ProbabilityMeasure.integral_eq_sum_singletonMass (μ : ProbabilityMeasure α) (f : α → ℝ) :
    ∫ a, f a ∂μ.toMeasure = ∑ a, (μ.toMeasure {a}).toReal * f a := by
  have hf : Integrable f μ.toMeasure := by
    have hf_simple :
        Integrable (MeasureTheory.SimpleFunc.ofFinite f : α → ℝ) μ.toMeasure :=
      (MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure
        (μ := μ.toMeasure) (MeasureTheory.SimpleFunc.ofFinite f))
    exact hf_simple
  simpa [measureReal_def, smul_eq_mul] using
    (MeasureTheory.integral_fintype (μ := μ.toMeasure) (f := f) hf)

omit [Fintype α] [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β] in
lemma continuous_outputPrior_toReal_apply_singleton [Finite α]
    (k : Kernel α β) [IsMarkovKernel k] (b : β) :
    Continuous fun p : ProbabilityMeasure α => ((outputPrior k p).toMeasure {b}).toReal := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  have hsum :
      Continuous fun p : ProbabilityMeasure α =>
        ∑ a, (p.toMeasure {a}).toReal * (k a {b}).toReal :=
    continuous_finsetSum (s := (Finset.univ : Finset α)) fun a _ha =>
      (continuous_toReal_apply_singleton a).mul continuous_const
  convert hsum using 1
  ext p
  exact toReal_outputPrior_apply_singleton k p b

omit [Fintype α] [Fintype β] [DiscreteTopology β] in
lemma continuous_outputPrior [Finite α] [Finite β] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => outputPrior k p := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  rw [ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral]
  intro f
  have hsum :
      Continuous fun p : ProbabilityMeasure α =>
        ∑ b, ((outputPrior k p).toMeasure {b}).toReal * f b :=
    continuous_finsetSum (s := (Finset.univ : Finset β)) fun b _hb =>
      (continuous_outputPrior_toReal_apply_singleton k b).mul continuous_const
  convert hsum using 1
  ext p
  rw [ProbabilityMeasure.integral_eq_sum_singletonMass]

omit [Fintype α] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β] [CompactSpace β] in
lemma continuous_outputEntropy [Finite α] (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => ProbabilityMeasure.entropy (outputPrior k p) := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  simpa [ProbabilityMeasure.entropy] using
    (continuous_finsetSum (s := (Finset.univ : Finset β)) fun b _hb =>
      Real.continuous_negMulLog.comp (continuous_outputPrior_toReal_apply_singleton k b))

omit [MeasurableSingletonClass β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β] in
lemma continuous_conditionalEntropy (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => conditionalEntropy p k := by
  simpa [conditionalEntropy] using
    (continuous_finsetSum (s := (Finset.univ : Finset α)) fun a _ha =>
      (continuous_toReal_apply_singleton a).mul continuous_const)

omit [Fintype α] [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β] in
lemma continuous_mutualInformation_of_finite [Finite α] [Finite β]
    (k : Kernel α β) [IsMarkovKernel k] :
    Continuous fun p : ProbabilityMeasure α => mutualInformation p k := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  convert (continuous_outputEntropy k).sub (continuous_conditionalEntropy k) using 1
  ext p
  exact mutualInformation_eq_entropy_outputPrior_sub_conditionalEntropy k p

end FiniteWeakTopology

section

omit [Fintype β] in
private lemma exists_unique_capacity_achieving_prior_of_finite_aux [Finite β]
    [Nonempty α] [TopologicalSpace α] [TopologicalSpace β]
    [DiscreteTopology α] [DiscreteTopology β] [T2Space α] [T2Space β]
    [BorelSpace α] [BorelSpace β] [CompactSpace α] [CompactSpace β]
    (k : Kernel α β) [IsMarkovKernel k] (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  have hcont : Continuous fun p : ProbabilityMeasure α => mutualInformation p k :=
    continuous_mutualInformation_of_finite k
  have hNonempty : (Set.univ : Set (ProbabilityMeasure α)).Nonempty := by
    refine ⟨MeasureTheory.diracProba (Classical.choice ‹Nonempty α›), by simp⟩
  obtain ⟨pMax, -, hpMax⟩ := IsCompact.exists_isMaxOn (α := ℝ)
    (β := ProbabilityMeasure α) isCompact_univ hNonempty hcont.continuousOn
  refine ⟨pMax, (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm, ?_⟩
  intro q hq
  have hpMax' : ∀ p : ProbabilityMeasure α, mutualInformation p k ≤ mutualInformation pMax k :=
    isMaxOn_univ_iff.mp hpMax
  have hqMax : IsMaxOn (fun p : ProbabilityMeasure α => mutualInformation p k) Set.univ q := by
    apply isMaxOn_univ_iff.mpr
    intro p
    calc
      mutualInformation p k ≤ mutualInformation pMax k := hpMax' p
      _ = channelCapacity k := (channelCapacity_eq_of_isMaxOn_univ k hpMax).symm
      _ = mutualInformation q k := hq.symm
  exact ProbabilityMeasure.eq_of_isMaxOn_univ_of_strictConcave
    (p := pMax) (q := q)
    (Kernel.mutualInformation_strictlyConcave_of_rowMatrixFullRank k hRank) hpMax hqMax |>.symm

omit [Fintype β] in
/-- Finite-alphabet capacity theorem with all hypotheses discharged internally. The general
measure-theoretic theorem remains available separately; this theorem is the concrete upstream-ready
specialization using the canonical weak topology on probability measures over finite discrete
alphabets. -/
theorem exists_unique_capacity_achieving_prior_of_finite [Finite β]
    [Nonempty α] (k : Kernel α β) [IsMarkovKernel k]
    (hRank : ChannelCapacity.Kernel.RowMatrixFullRank k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  let : Fintype β := Fintype.ofFinite β
  let : TopologicalSpace α := ⊥
  let : TopologicalSpace β := ⊥
  let : DiscreteTopology α := ⟨rfl⟩
  let : DiscreteTopology β := ⟨rfl⟩
  let : T2Space α := by infer_instance
  let : T2Space β := by infer_instance
  let : BorelSpace α := by infer_instance
  let : BorelSpace β := by infer_instance
  let : CompactSpace α := Finite.compactSpace
  let : CompactSpace β := Finite.compactSpace
  exact exists_unique_capacity_achieving_prior_of_finite_aux k hRank

end

end EntropyFormula

end ChannelCapacity
