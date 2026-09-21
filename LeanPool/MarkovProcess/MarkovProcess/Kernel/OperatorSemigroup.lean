/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator

/-!
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

private instance fact_one_le_coe_nnreal (p : NNReal) [Fact (1 ≤ p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out⟩

private theorem kernelIntegral_id_ae {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    kernelIntegral Kernel.id f =ᵐ[μ] f := by
  let g := hf.mk f
  have hfg : kernelIntegral Kernel.id f =ᵐ[μ] kernelIntegral Kernel.id g :=
    kernelIntegral_congr_ae (by rw [Measure.id_comp]) hf.ae_eq_mk
  refine hfg.trans ?_
  filter_upwards [hf.ae_eq_mk] with x hx
  rw [kernelIntegral, Kernel.id_apply, integral_dirac' g x hf.stronglyMeasurable_mk]
  exact hx.symm

private theorem ae_integrable_kernel_finite {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) {p : NNReal}
    (hp : 1 ≤ p) (f : Lp ℝ (p : ℝ≥0∞) μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := (Lp.memLp f).mono_measure hκμ
  have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.1.ae_eq_mk
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
  have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  have hxEq' : f =ᵐ[κ x] hfComp.1.mk f := hxEq
  have hxMeas : AEStronglyMeasurable f (κ x) :=
    hfComp.1.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
  have hxMemLp : MemLp f p (κ x) :=
    (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  exact hxMemLp.integrable (by exact_mod_cast hp)

private theorem ae_integrable_kernel_top {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  have hCtop : eLpNormEssSup f μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top]
    exact (Lp.memLp f).2.ne
  have hCcoe : ((eLpNormEssSup f μ).toNNReal : ℝ≥0∞) = eLpNormEssSup f μ :=
    ENNReal.coe_toNNReal hCtop
  have hFiberEq : ∀ᵐ x ∂μ, f =ᵐ[κ x] (Lp.aestronglyMeasurable f).mk f :=
    ae_ae_kernel_of_comp_le hκμ (Lp.aestronglyMeasurable f).ae_eq_mk
  have hBound := ae_ae_kernel_of_comp_le hκμ (enorm_ae_le_eLpNormEssSup f μ)
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  filter_upwards [hFiberEq, hBound] with x hxEq hxBound
  have hxAS : AEStronglyMeasurable f (κ x) :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  apply MemLp.integrable (q := ∞) le_top
  apply memLp_top_of_bound_enorm hxAS (eLpNormEssSup f μ).toNNReal
  simpa only [hCcoe] using hxBound

private theorem kernelIntegral_add_ae_finite {μ : Measure α}
    (hμ : P.IsSubInvariant μ) (p : NNReal) [Fact (1 ≤ p)]
    (s t : NNReal) (f : Lp ℝ (p : ℝ≥0∞) μ) :
    kernelIntegral (P (s + t)) f =ᵐ[μ]
      kernelIntegral (P s) (kernelIntegral (P t) f) := by
  filter_upwards
    [ae_integrable_kernel_finite (P.isSubMarkovKernel (s + t)) (hμ (s + t)) Fact.out f]
      with x hx
  have hx' : Integrable f ((P t ∘ₖ P s) x) := by
    rw [← P.add]
    exact hx
  rw [kernelIntegral, P.add]
  exact Kernel.integral_comp hx'

private theorem kernelIntegral_add_ae_top {μ : Measure α}
    (hμ : P.IsSubInvariant μ) (s t : NNReal) (f : Lp ℝ ∞ μ) :
    kernelIntegral (P (s + t)) f =ᵐ[μ]
      kernelIntegral (P s) (kernelIntegral (P t) f) := by
  filter_upwards
    [ae_integrable_kernel_top (P.isSubMarkovKernel (s + t)) (hμ (s + t)) f] with x hx
  have hx' : Integrable f ((P t ∘ₖ P s) x) := by
    rw [← P.add]
    exact hx
  rw [kernelIntegral, P.add]
  exact Kernel.integral_comp hx'

/-- The finite-exponent canonical operator at time zero is the identity. -/
theorem operatorFinite_zero (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] :
    P.operatorFinite μ hμ p 0 = ContinuousLinearMap.id ℝ (Lp ℝ (p : ℝ≥0∞) μ) := by
  ext f
  refine (P.isAssociatedFinite_operatorFinite μ hμ p 0 f).trans ?_
  rw [P.zero]
  exact (kernelIntegral_id_ae (Lp.aestronglyMeasurable f)).trans
    Filter.EventuallyEq.rfl

/-- The finite-exponent canonical operators obey the add-time law. -/
theorem operatorFinite_add (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] (s t : NNReal) :
    P.operatorFinite μ hμ p (s + t) =
      (P.operatorFinite μ hμ p s).comp (P.operatorFinite μ hμ p t) := by
  ext f
  refine (P.isAssociatedFinite_operatorFinite μ hμ p (s + t) f).trans ?_
  refine (kernelIntegral_add_ae_finite P hμ p s t f).trans ?_
  refine (kernelIntegral_congr_ae (hμ s)
    (P.isAssociatedFinite_operatorFinite μ hμ p t f).symm).trans ?_
  exact (P.isAssociatedFinite_operatorFinite μ hμ p s (P.operatorFinite μ hμ p t f)).symm

/-- The infinite-exponent canonical operator at time zero is the identity. -/
theorem operatorTop_zero (μ : Measure α) (hμ : P.IsSubInvariant μ) :
    P.operatorTop μ hμ 0 = ContinuousLinearMap.id ℝ (Lp ℝ ∞ μ) := by
  ext f
  refine (P.isAssociatedTop_operatorTop μ hμ 0 f).trans ?_
  rw [P.zero]
  exact (kernelIntegral_id_ae (Lp.aestronglyMeasurable f)).trans
    Filter.EventuallyEq.rfl

/-- The infinite-exponent canonical operators obey the add-time law. -/
theorem operatorTop_add (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (s t : NNReal) :
    P.operatorTop μ hμ (s + t) =
      (P.operatorTop μ hμ s).comp (P.operatorTop μ hμ t) := by
  ext f
  refine (P.isAssociatedTop_operatorTop μ hμ (s + t) f).trans ?_
  refine (kernelIntegral_add_ae_top P hμ s t f).trans ?_
  refine (kernelIntegral_congr_ae (hμ s)
    (P.isAssociatedTop_operatorTop μ hμ t f).symm).trans ?_
  exact (P.isAssociatedTop_operatorTop μ hμ s (P.operatorTop μ hμ t f)).symm

end SubMarkovKernelSemigroup

end MarkovProcess
