/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.ChannelCapacity.Capacity
import LeanPool.ChannelCapacity.NonDegeneracy
import LeanPool.ChannelCapacity.ChainRule
import LeanPool.ChannelCapacity.KernelCompositionKullbackLeibler

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Kernel.WithDensity

/-!
# ChannelCapacity.Discharged

Concrete density-regularity hypotheses for discharging the generic capacity theorem.

This module introduces `Kernel.ContinuousPositiveDensity`, a compact-Polish channel class whose
rows admit a common strictly positive jointly continuous density. For that class it discharges the
abstract `WellConditionedForCapacity` bundle (`hRowAC`, `hFiniteRefKL`, and `hChainRule`) and the
compactness side of the ambient maximization argument, then derives the top-level theorem
`exists_unique_capacity_achieving_prior_discharged` with no external bundle hypotheses.

Currently, upper semicontinuity of
`p ↦ mutualInformation p k` is carried as a field of the concrete class rather than derived from
the density hypotheses alone. The intended follow-up is a general theorem
`upperSemicontinuous_mutualInformation_of_continuousPositiveDensity` proved from the density
assumptions plus compactness of `α × β`.

The worked example lives in `ChannelCapacity.DischargedExample`: a positive full-rank `Fin 2`
channel with counting-measure reference, an explicit `ContinuousPositiveDensity` inhabitant, and a
concrete application of `exists_unique_capacity_achieving_prior_discharged`.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]

namespace Kernel

/-- A concrete compact-Polish regularity class for a Markov kernel: all rows have a common density
with respect to `ν`, this density is jointly continuous, it is strictly positive, and the induced
mutual-information functional is upper semicontinuous on priors. -/
structure ContinuousPositiveDensity
    (k : Kernel α β) (ν : Measure β) [IsMarkovKernel k] [OpensMeasurableSpace α] where
  /-- The common density of every row of `k` with respect to `ν`. -/
  density : α → β → NNReal
  continuous_density : Continuous (Function.uncurry density)
  eq_withDensity : ∀ a, k a = ν.withDensity (fun b => (density a b : ℝ≥0∞))
  density_pos : ∀ a b, 0 < density a b
  mutualInformation_usc :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k

namespace ContinuousPositiveDensity

variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}

lemma row_eq_withDensity (h : ContinuousPositiveDensity k ν) (a : α) :
    k a = ν.withDensity (fun b => (h.density a b : ENNReal)) :=
  h.eq_withDensity a

lemma row_absolutelyContinuous_ref (h : ContinuousPositiveDensity k ν) (a : α) :
    k a ≪ ν := by
  rw [h.row_eq_withDensity a]
  simpa using MeasureTheory.withDensity_absolutelyContinuous ν
    (fun b => (h.density a b : ENNReal))

lemma density_ne_zero (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    h.density a b ≠ 0 :=
  ne_of_gt (h.density_pos a b)

lemma density_ennreal_pos (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    0 < (h.density a b : ENNReal) :=
  ENNReal.coe_pos.mpr (h.density_pos a b)

lemma density_ennreal_ne_zero (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    (h.density a b : ENNReal) ≠ 0 :=
  ne_of_gt (h.density_ennreal_pos a b)

lemma upperSemicontinuous_mutualInformation
    (h : ContinuousPositiveDensity k ν) :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k :=
  h.mutualInformation_usc

section UniformBounds

variable [CompactSpace α] [CompactSpace β] [Nonempty α] [Nonempty β]

/-- A strictly positive jointly continuous density on a compact product has a positive uniform lower
bound and a finite uniform upper bound. -/
lemma exists_uniform_density_bounds
    (h : ContinuousPositiveDensity k ν) :
    ∃ c C : NNReal,
      0 < c ∧ ∀ a b, c ≤ h.density a b ∧ h.density a b ≤ C := by
  let f : α × β → NNReal := Function.uncurry h.density
  obtain ⟨xMin, -, hxMin⟩ := IsCompact.exists_isMinOn (α := NNReal)
    (β := α × β) isCompact_univ Set.univ_nonempty h.continuous_density.continuousOn
  obtain ⟨xMax, -, hxMax⟩ := IsCompact.exists_isMaxOn (α := NNReal)
    (β := α × β) isCompact_univ Set.univ_nonempty h.continuous_density.continuousOn
  refine ⟨f xMin, f xMax, ?_, ?_⟩
  · simpa [f, Function.uncurry] using h.density_pos xMin.1 xMin.2
  · intro a b
    constructor
    · exact (isMinOn_univ_iff.mp hxMin) (a, b)
    · exact (isMaxOn_univ_iff.mp hxMax) (a, b)

end UniformBounds

lemma klFun_le_sq_add_one {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) :
    InformationTheory.klFun x ≤ B ^ 2 + 1 := by
  have hlog : Real.log x ≤ x := Real.log_le_self hx
  calc
    InformationTheory.klFun x = x * Real.log x + 1 - x := rfl
    _ ≤ x * x + 1 - x := by
      gcongr
    _ ≤ B ^ 2 + 1 := by
      nlinarith

section OutputPrior

variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]

/-- The density of the output prior `outputPrior k p` with respect to `ν`, given as the
`p`-average of the row densities. -/
noncomputable def outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    β → ENNReal :=
  fun b => ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure

omit [CompactSpace α] [CompactSpace β] [BorelSpace α] [BorelSpace β] in
lemma aemeasurable_outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    AEMeasurable (h.outputDensity p) ν := by
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod ν) := by
    exact (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  exact hbase.lintegral_prod_left (μ := p.toMeasure) (ν := ν)

omit [CompactSpace α] [CompactSpace β] [BorelSpace α] [BorelSpace β] in
lemma outputPrior_eq_withDensity_outputDensity
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = ν.withDensity (h.outputDensity p) := by
  ext s hs
  rw [outputPrior_toMeasure, Measure.bind_apply hs k.aemeasurable,
    MeasureTheory.withDensity_apply _ hs]
  simp_rw [h.row_eq_withDensity]
  simp_rw [MeasureTheory.withDensity_apply _ hs]
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod (ν.restrict s)) := by
    exact (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  exact (lintegral_lintegral_swap (μ := p.toMeasure) (ν := ν.restrict s)
      (f := fun a b => (h.density a b : ENNReal)) hbase)

omit [CompactSpace β] [PolishSpace α] [PolishSpace β] [BorelSpace α] [BorelSpace β]
  [OpensMeasurableSpace β] [IsFiniteMeasure ν] in
lemma outputDensity_pos (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (b : β) :
    0 < h.outputDensity p b := by
  letI : Nonempty α := p.nonempty
  have hcont : Continuous fun a : α => h.density a b := by
    have hpair : Continuous fun a : α => (a, b) := by
      fun_prop
    exact h.continuous_density.comp hpair
  obtain ⟨a0, -, ha0⟩ := IsCompact.exists_isMinOn (α := NNReal)
    (β := α) isCompact_univ Set.univ_nonempty hcont.continuousOn
  have ha0' : ∀ a : α, h.density a0 b ≤ h.density a b :=
    isMinOn_univ_iff.mp ha0
  have hle : ∀ a : α, (h.density a0 b : ENNReal) ≤ (h.density a b : ENNReal) := by
    intro a
    exact_mod_cast ha0' a
  have hconst_le :
      (h.density a0 b : ENNReal) ≤ h.outputDensity p b := by
    calc
      (h.density a0 b : ENNReal) = ∫⁻ a, (h.density a0 b : ENNReal) ∂p.toMeasure := by simp
      _ ≤ ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure := lintegral_mono hle
      _ = h.outputDensity p b := rfl
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (h.density_pos a0 b)) hconst_le

omit [CompactSpace β] [BorelSpace α] [BorelSpace β] in
lemma ae_row_absolutelyContinuous_outputPrior
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k p).toMeasure := by
  have hν_ac_out :
      ν ≪ (outputPrior k p).toMeasure := by
    have hν_ac_withDensity :
        ν ≪ ν.withDensity (h.outputDensity p) :=
      MeasureTheory.withDensity_absolutelyContinuous'
        (h.aemeasurable_outputDensity p)
        (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using hν_ac_withDensity
  exact Filter.Eventually.of_forall fun a =>
    (h.row_absolutelyContinuous_ref a).trans hν_ac_out

omit [CompactSpace β] [BorelSpace α] [BorelSpace β] in
lemma row_absolutelyContinuous_outputPrior
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (a : α) :
    k a ≪ (outputPrior k p).toMeasure := by
  have hν_ac_out :
      ν ≪ (outputPrior k p).toMeasure := by
    have hν_ac_withDensity :
        ν ≪ ν.withDensity (h.outputDensity p) :=
      MeasureTheory.withDensity_absolutelyContinuous'
        (h.aemeasurable_outputDensity p)
        (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using hν_ac_withDensity
  exact (h.row_absolutelyContinuous_ref a).trans hν_ac_out

omit [BorelSpace α] [BorelSpace β] in
lemma row_klDiv_le_outputPrior_bound
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ a : α, InformationTheory.klDiv (k a) (outputPrior k p).toMeasure ≤ B := by
  letI : Nonempty α := p.nonempty
  letI : Nonempty β := (outputPrior k p).nonempty
  rcases h.exists_uniform_density_bounds with ⟨c, C, hc_pos, h_bounds⟩
  let Breal : ℝ := (((c : ENNReal)⁻¹ * (C : ENNReal)).toReal) ^ 2 + 1
  let B : ℝ≥0∞ := ENNReal.ofReal Breal
  refine ⟨B, by simp [B], ?_⟩
  intro a
  have h_out_lower : ∀ b, (c : ENNReal) ≤ h.outputDensity p b := by
    intro b
    have h_c_le_density : ∀ a' : α, (c : ENNReal) ≤ (h.density a' b : ENNReal) := by
      intro a'
      exact_mod_cast (h_bounds a' b).1
    calc
      (c : ENNReal) = ∫⁻ a', (c : ENNReal) ∂p.toMeasure := by simp
      _ ≤ ∫⁻ a', (h.density a' b : ENNReal) ∂p.toMeasure := by
        exact lintegral_mono h_c_le_density
      _ = h.outputDensity p b := rfl
  have h_out_upper : ∀ b, h.outputDensity p b ≤ (C : ENNReal) := by
    intro b
    have h_density_le_C : ∀ a' : α, (h.density a' b : ENNReal) ≤ (C : ENNReal) := by
      intro a'
      exact_mod_cast (h_bounds a' b).2
    calc
      h.outputDensity p b = ∫⁻ a', (h.density a' b : ENNReal) ∂p.toMeasure := rfl
      _ ≤ ∫⁻ a', (C : ENNReal) ∂p.toMeasure := by
        exact lintegral_mono h_density_le_C
      _ = (C : ENNReal) := by simp
  have h_out_ne_top : ∀ b, h.outputDensity p b ≠ ∞ := by
    intro b
    exact ne_top_of_le_ne_top (by simp) (h_out_upper b)
  have h_ac : k a ≪ (outputPrior k p).toMeasure :=
    h.row_absolutelyContinuous_outputPrior p a
  have h_out_ac_ref :
      (outputPrior k p).toMeasure ≪ ν := by
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using
      MeasureTheory.withDensity_absolutelyContinuous ν (h.outputDensity p)
  have hmeas_density_a : Measurable (fun b => (h.density a b : ENNReal)) := by
    have hcont_density_a : Continuous fun b : β => h.density a b := by
      have hpair : Continuous fun b : β => (a, b) := by
        fun_prop
      exact h.continuous_density.comp hpair
    exact (ENNReal.continuous_coe.comp hcont_density_a).measurable
  have h_rnDeriv_ref :
      (k a).rnDeriv ν =ᵐ[ν] fun b => (h.density a b : ENNReal) := by
    rw [h.row_eq_withDensity a]
    exact Measure.rnDeriv_withDensity ν hmeas_density_a
  have h_rnDeriv_withDensity :
      (k a).rnDeriv (ν.withDensity (h.outputDensity p)) =ᵐ[ν]
        fun b => (h.outputDensity p b)⁻¹ * ((k a).rnDeriv ν b) := by
    exact Measure.rnDeriv_withDensity_right
      (μ := k a) (ν := ν) (f := h.outputDensity p)
      (h.aemeasurable_outputDensity p)
      (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
      (Filter.Eventually.of_forall fun b => h_out_ne_top b)
  have h_rnDeriv_out_ν :
      (k a).rnDeriv ((outputPrior k p).toMeasure) =ᵐ[ν]
        fun b => (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) := by
    filter_upwards [h_rnDeriv_withDensity, h_rnDeriv_ref] with b hb hb'
    simpa [h.outputPrior_eq_withDensity_outputDensity p, hb'] using hb
  have h_rnDeriv_out :
      (k a).rnDeriv ((outputPrior k p).toMeasure) =ᵐ[(outputPrior k p).toMeasure]
        fun b => (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) := by
    exact h_out_ac_ref.ae_eq h_rnDeriv_out_ν
  have h_integrand_le :
      ∀ᵐ b ∂(outputPrior k p).toMeasure,
        ENNReal.ofReal
            (InformationTheory.klFun
              (((k a).rnDeriv ((outputPrior k p).toMeasure) b).toReal)) ≤
          B := by
    filter_upwards [h_rnDeriv_out] with b hb
    have h_density_le_C : (h.density a b : ENNReal) ≤ (C : ENNReal) := by
      exact_mod_cast (h_bounds a b).2
    have hratio_le :
        (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) ≤
          (c : ENNReal)⁻¹ * (C : ENNReal) := by
      calc
        (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) ≤
            (c : ENNReal)⁻¹ * (h.density a b : ENNReal) := by
              gcongr
              exact h_out_lower b
        _ ≤ (c : ENNReal)⁻¹ * (C : ENNReal) := by
              gcongr
    have hratio_real_le :
        (((h.outputDensity p b)⁻¹ * (h.density a b : ENNReal)).toReal) ≤
          (((c : ENNReal)⁻¹ * (C : ENNReal)).toReal) := by
      have hbound_ne_top : ((c : ENNReal)⁻¹ * (C : ENNReal)) ≠ ∞ := by
        refine ENNReal.mul_ne_top ?_ ?_
        · simp [hc_pos.ne']
        · simp
      exact ENNReal.toReal_mono hbound_ne_top hratio_le
    have hkl_le :
        InformationTheory.klFun
            (((h.outputDensity p b)⁻¹ * (h.density a b : ENNReal)).toReal) ≤
          Breal := by
      exact klFun_le_sq_add_one ENNReal.toReal_nonneg hratio_real_le
    have hkl_le' :
        InformationTheory.klFun
            ((((k a).rnDeriv ((outputPrior k p).toMeasure)) b).toReal) ≤
          Breal := by
      rw [hb]
      simpa [ENNReal.toReal_mul, h_out_ne_top b, ENNReal.toReal_inv,
        (h.outputDensity_pos p b).ne'] using hkl_le
    exact ENNReal.ofReal_le_ofReal hkl_le'
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
  calc
    ∫⁻ b,
        ENNReal.ofReal
          (InformationTheory.klFun (((k a).rnDeriv ((outputPrior k p).toMeasure) b).toReal)) ∂
        (outputPrior k p).toMeasure ≤
      ∫⁻ _, B ∂(outputPrior k p).toMeasure := by
        exact lintegral_mono_ae h_integrand_le
    _ = B := by simp [B]

omit [BorelSpace α] in
theorem hFiniteRefKL_of_continuousPositiveDensity
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (ν' : Measure β)
    (hRef : Kernel.OutputMarginalReference k p ν') :
    InformationTheory.klDiv (p.toMeasure ⊗ₘ k) (p.toMeasure ⊗ₘ Kernel.const _ ν') ≠ ∞ := by
  rcases hRef with ⟨q, hpq, rfl⟩
  rcases h.row_klDiv_le_outputPrior_bound q with ⟨B, hB_fin, hB⟩
  have hp_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k q).toMeasure := by
    rw [ae_iff]
    exact hpq (by simpa [ae_iff] using h.ae_row_absolutelyContinuous_outputPrior q)
  have h_ac :
      p.toMeasure ⊗ₘ k ≪ p.toMeasure ⊗ₘ Kernel.const α (outputPrior k q).toMeasure :=
    Measure.AbsolutelyContinuous.compProd_right hp_rows
  have h_le :
      InformationTheory.klDiv (p.toMeasure ⊗ₘ k)
          (p.toMeasure ⊗ₘ Kernel.const α (outputPrior k q).toMeasure) ≤
        B := by
    rw [ProbabilityTheory.klDiv_compProd_right (μ := p.toMeasure)
      (κ := k) (η := Kernel.const α (outputPrior k q).toMeasure) h_ac]
    calc
      ∫⁻ a, InformationTheory.klDiv (k a) ((Kernel.const α (outputPrior k q).toMeasure) a)
          ∂p.toMeasure ≤
        ∫⁻ _, B ∂p.toMeasure := by
          refine lintegral_mono ?_
          intro a
          simpa using hB a
      _ = B := by simp
  exact ne_top_of_le_ne_top hB_fin h_le

omit [TopologicalSpace β] [CompactSpace α] [CompactSpace β] [PolishSpace β] [BorelSpace β]
  [OpensMeasurableSpace α] [OpensMeasurableSpace β] [IsFiniteMeasure ν] in
theorem hChainRule_of_outputMarginalReference
    (p : ProbabilityMeasure α) (ν' : Measure β)
    (hRef : Kernel.OutputMarginalReference k p ν') :
    InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const _ ν') =
      InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        InformationTheory.klDiv (outputPrior k p).toMeasure ν' := by
  rcases hRef with ⟨q, -, rfl⟩
  letI : Nonempty α := p.nonempty
  simpa using
    klDiv_mutualInformation_chain (k := k) (p := p) (ν := (outputPrior k q).toMeasure)

theorem wellConditionedForCapacity_of_continuousPositiveDensity
    (h : ContinuousPositiveDensity k ν) :
    Kernel.WellConditionedForCapacity k := by
  refine
    { hRowAC := h.ae_row_absolutelyContinuous_outputPrior
      hFiniteRefKL := h.hFiniteRefKL_of_continuousPositiveDensity
      hChainRule := hChainRule_of_outputMarginalReference (k := k) }

end OutputPrior

section Compactness

variable [CompactSpace α] [PolishSpace α] [BorelSpace α] [Nonempty α]

omit [TopologicalSpace α] [CompactSpace α] [PolishSpace α] [BorelSpace α]
  [OpensMeasurableSpace α] in
lemma univ_nonempty_probabilityMeasure :
    (Set.univ : Set (ProbabilityMeasure α)).Nonempty := by
  exact ⟨MeasureTheory.diracProba (Classical.choice ‹Nonempty α›), Set.mem_univ _⟩

omit [Nonempty α] in
lemma isCompact_univ_probabilityMeasure :
    IsCompact (Set.univ : Set (ProbabilityMeasure α)) :=
  isCompact_univ

end Compactness

end ContinuousPositiveDensity

end Kernel

section Capacity

variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace α] [OpensMeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
variable [Nonempty α]

theorem exists_unique_capacity_achieving_prior_discharged
    (k : Kernel α β) [IsMarkovKernel k]
    (ν : Measure β) [IsFiniteMeasure ν]
    (hDensity : Kernel.ContinuousPositiveDensity k ν)
    (hInj : Kernel.InjectivePriorPushforward k) :
    ∃! p : ProbabilityMeasure α, mutualInformation p k = channelCapacity k := by
  exact exists_unique_capacity_achieving_prior k hInj
    (Kernel.ContinuousPositiveDensity.wellConditionedForCapacity_of_continuousPositiveDensity
      (k := k) (ν := ν) hDensity)
    Kernel.ContinuousPositiveDensity.univ_nonempty_probabilityMeasure
    Kernel.ContinuousPositiveDensity.isCompact_univ_probabilityMeasure
    hDensity.upperSemicontinuous_mutualInformation

end Capacity

end ChannelCapacity
