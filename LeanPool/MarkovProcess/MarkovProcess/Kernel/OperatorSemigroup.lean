/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator


/-!
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

@[expose] public section

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
