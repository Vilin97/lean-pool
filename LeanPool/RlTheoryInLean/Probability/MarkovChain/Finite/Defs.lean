/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.Probability.MarkovChain.Defs
import LeanPool.RlTheoryInLean.Data.Matrix.Stochastic
import LeanPool.RlTheoryInLean.Probability.Kernel.Basic

/-!
# LeanPool.RlTheoryInLean.Probability.MarkovChain.Finite.Defs
-/

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory
open Finset NNReal ENNReal Preorder Function StochasticMatrix Filter

namespace ProbabilityTheory

namespace MarkovChain

namespace Finite

universe u
variable {S : Type u}
variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Matrix representation of a finite-state Markov transition kernel. -/
def kernelMat (M : HomMarkovChainSpec S)
  : Matrix S S ℝ :=
  Matrix.of (fun a b => (M.kernel a {b}).toReal)

/-- Vector representation of the initial distribution of a finite Markov chain. -/
def initVec (M : HomMarkovChainSpec S)
  : S → ℝ :=
  fun s => (M.init {s}).toReal

lemma prob_sum_to_one
  (μ : Measure S) [IsProbabilityMeasure μ] :
  ∑ s, (μ {s}).toReal = 1 := by
  have : ∑ s, μ {s} = 1 := by simp
  have := congrArg ENNReal.toReal this
  rw [ENNReal.toReal_sum (fun s _ => measure_ne_top μ {s})] at this
  exact this

instance (M : HomMarkovChainSpec S)
  : StochasticVec (initVec M) := by
  constructor
  case nonneg =>
    intro s;
    unfold initVec; simp
  case rowsum =>
    unfold initVec
    apply prob_sum_to_one

instance (M : HomMarkovChainSpec S)
  : RowStochastic (kernelMat M) := by
  constructor
  intro s
  constructor
  case nonneg =>
    intro j; unfold kernelMat; simp
  case rowsum =>
    unfold kernelMat
    simp only [Matrix.of_apply]
    have := (M.markov_kernel).isProbabilityMeasure s
    apply prob_sum_to_one

omit [Fintype S] [MeasurableSingletonClass S] in
lemma kernel_apply_eq_mat_apply
  (M : HomMarkovChainSpec S) (s s' : S) :
  (M.kernel s {s'}).toReal = kernelMat M s s' := by
  simp [kernelMat]

lemma integral_fintype_kernel_iter
  {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α] [DecidableEq S]
  (M : HomMarkovChainSpec S) (n : ℕ) (f : S → α) (s : S) :
  ∫ s', f s' ∂ M.kernel.iter n s = ∑ s', ((kernelMat M) ^ n) s s' • f s' := by
  induction n generalizing s with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    have hiter0 : (M.kernel.iter 0) s = Measure.dirac s := Kernel.id_apply s
    rw [hiter0, integral_dirac]
    symm
    simp only [ite_smul, one_smul, zero_smul]
    rw [sum_ite_eq]
    simp
  | succ n ih =>
    simp only [pow_succ']
    -- iter (n+1) = (iter n).comp κ = iter n ∘ₖ κ
    -- M.kernel is a Markov kernel
    haveI hmarkovK : IsMarkovKernel M.kernel := M.markov_kernel
    -- M.kernel.iter (n+1) is also a Markov kernel (by the instance in Kernel.Basic)
    haveI hmarkovIter : IsMarkovKernel (M.kernel.iter (n + 1)) :=
      ProbabilityTheory.Kernel.instIsMarkovKernelIter (n + 1) M.kernel
    haveI hprob : IsProbabilityMeasure ((M.kernel.iter (n + 1)) s) :=
      hmarkovIter.isProbabilityMeasure s
    have hInt : Integrable f ((M.kernel.iter (n + 1)) s) := Integrable.of_finite
    -- Rewrite using the definitional equality
    conv_lhs => rw [show M.kernel.iter (n + 1) = (M.kernel.iter n) ∘ₖ M.kernel from rfl]
    rw [Kernel.integral_comp hInt]
    simp_rw [fun x => ih x]
    simp only [Matrix.mul_apply]
    haveI hprob' : IsProbabilityMeasure (M.kernel s) := M.markov_kernel.isProbabilityMeasure s
    have hfInt : Integrable (fun s' => ∑ s'', (kernelMat M ^ n) s' s'' • f s'') (M.kernel s) :=
      Integrable.of_finite
    rw [integral_fintype hfInt]
    simp_rw [Measure.real_def, kernel_apply_eq_mat_apply]
    -- LHS: ∑ x, kernelMat M s x • ∑ s'', (kernelMat M ^ n) x s'' • f s''
    -- RHS: ∑ x, (∑ j, kernelMat M s j * (kernelMat M ^ n) j x) • f x
    -- Expand the smul in LHS
    simp_rw [smul_sum, smul_smul]
    -- LHS: ∑ x, ∑ x_1, (kernelMat M s x * (kernelMat M ^ n) x x_1) • f x_1
    -- RHS: ∑ x, (∑ j, kernelMat M s j * (kernelMat M ^ n) j x) • f x
    -- Swap the outer and inner sum
    rw [Finset.sum_comm]
    -- Now LHS: ∑ x_1, ∑ x, (kernelMat M s x * (kernelMat M ^ n) x x_1) • f x_1
    -- Manipulate to match RHS
    congr 1
    ext x
    rw [← Finset.sum_smul]

end Finite

end MarkovChain

end ProbabilityTheory
