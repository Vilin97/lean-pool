/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Measure.OpenPos
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator

/-!
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- The constant-one class in `L∞`, available without a finiteness assumption
on the reference measure. -/
noncomputable def oneLpTop (μ : Measure α) : Lp ℝ ∞ μ :=
  (memLp_top_const (μ := μ) (1 : ℝ)).toLp (fun _ : α => (1 : ℝ))

/-- The `L∞` constant-one class is represented by the constant-one function. -/
theorem coeFn_oneLpTop (μ : Measure α) :
    oneLpTop μ =ᵐ[μ] fun _ : α => (1 : ℝ) :=
  (memLp_top_const (μ := μ) (1 : ℝ)).coeFn_toLp

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)

/-- Conservativity almost everywhere in the starting point, relative to `μ`. -/
def IsConservativeAE (μ : Measure α) : Prop :=
  ∀ t, ∀ᵐ x ∂μ, P t x Set.univ = 1

/-- An `L∞` operator family preserves the constant-one equivalence class. -/
def PreservesOneTop (μ : Measure α)
    (T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ) : Prop :=
  ∀ t, T t (oneLpTop μ) = oneLpTop μ

/-- Association with a subinvariant kernel family and preservation of one imply
conservativity almost everywhere in the starting point. -/
theorem IsAssociatedTop.isConservativeAE_of_preservesOne
    {μ : Measure α} {T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ}
    (hμ : P.IsSubInvariant μ) (hAssoc : P.IsAssociatedTop μ T)
    (hOne : PreservesOneTop μ T) : P.IsConservativeAE μ := by
  intro t
  have hPres : T t (oneLpTop μ) =ᵐ[μ] oneLpTop μ :=
    Filter.Eventually.of_forall fun x => congrArg (fun f : Lp ℝ ∞ μ => f x) (hOne t)
  have hKernel := kernelIntegral_congr_ae (hμ t) (coeFn_oneLpTop μ)
  filter_upwards [hAssoc t (oneLpTop μ), hPres, coeFn_oneLpTop μ, hKernel] with
    x hAssocX hPresX hOneX hKernelX
  have hIntegral : kernelIntegral (P t) (fun _ : α => (1 : ℝ)) x = 1 := by
    calc
      kernelIntegral (P t) (fun _ : α => (1 : ℝ)) x =
          kernelIntegral (P t) (oneLpTop μ) x := hKernelX.symm
      _ = T t (oneLpTop μ) x := hAssocX.symm
      _ = oneLpTop μ x := hPresX
      _ = 1 := hOneX
  have hReal : (P t x Set.univ).toReal = 1 := by
    simpa only [kernelIntegral, integral_const, Measure.real_def, smul_eq_mul, mul_one]
      using hIntegral
  exact (ENNReal.toReal_eq_one_iff _).mp hReal

/-- If the canonical `L∞` operator family preserves one, then the transition
kernel is conservative almost everywhere in the starting point. -/
theorem isConservativeAE_of_operatorTop_preservesOne
    {μ : Measure α} (hμ : P.IsSubInvariant μ)
    (hOne : PreservesOneTop μ (P.operatorTop μ hμ)) :
    P.IsConservativeAE μ :=
  IsAssociatedTop.isConservativeAE_of_preservesOne
    (P := P) hμ (P.isAssociatedTop_operatorTop μ hμ) hOne

/-- Almost-everywhere conservativity becomes pointwise conservativity when
transition mass is continuous and the reference measure is positive on every
nonempty open set. -/
theorem IsConservativeAE.isConservative_of_continuous_mass
    {μ : Measure α} [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    (hAE : P.IsConservativeAE μ)
    (hcont : ∀ t, Continuous fun x => P t x Set.univ) :
    P.IsConservative := by
  intro t x
  exact congrFun (Measure.eq_of_ae_eq (hAE t) (hcont t) continuous_const) x

end SubMarkovKernelSemigroup

end MarkovProcess
