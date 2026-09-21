/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Lp

/-!
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- Finite-exponent kernel operators at possibly different exponents have
almost-everywhere equal representatives on almost-everywhere equal inputs. -/
theorem kernelLpFinite_consistent
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p q : NNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp ℝ (p : ℝ≥0∞) μ) (g : Lp ℝ (q : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ q g := by
  exact (coeFn_kernelLpFinite μ κ hκ hκμ p f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpFinite μ κ hκ hκμ q g).symm)

/-- The finite-exponent and infinite-exponent packages have almost-everywhere
equal representatives on almost-everywhere equal inputs. -/
theorem kernelLpFinite_consistent_top
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal) [Fact (1 ≤ p)]
    (f : Lp ℝ (p : ℝ≥0∞) μ) (g : Lp ℝ ∞ μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ]
      kernelLpTop μ κ hκ hκμ g := by
  exact (coeFn_kernelLpFinite μ κ hκ hκμ p f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpTop μ κ hκ hκμ g).symm)

/-- Symmetric orientation of `kernelLpFinite_consistent_top`. -/
theorem kernelLpTop_consistent_finite
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal) [Fact (1 ≤ p)]
    (f : Lp ℝ ∞ μ) (g : Lp ℝ (p : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ p g := by
  exact (coeFn_kernelLpTop μ κ hκ hκμ f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpFinite μ κ hκ hκμ p g).symm)

end MarkovProcess
