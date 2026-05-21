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

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory
open Finset NNReal ENNReal Preorder Function StochasticMatrix Filter

namespace ProbabilityTheory

namespace MarkovChain

namespace Finite

universe u
variable {S : Type u}
variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Matrix representation of a finite-state Markov transition kernel. -/
def kernel_mat (M : HomMarkovChainSpec S)
  : Matrix S S ℝ :=
  Matrix.of (fun a b => (M.kernel a {b}).toReal)

/-- Vector representation of the initial distribution of a finite Markov chain. -/
def init_vec (M : HomMarkovChainSpec S)
  : S → ℝ :=
  fun s => (M.init {s}).toReal

lemma prob_sum_to_one
  (μ : Measure S) [IsProbabilityMeasure μ] :
  ∑ s, (μ {s}).toReal = 1 := by
  have h : ∑ s, μ {s} = 1 := by simp
  have := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_sum (fun s _ => measure_ne_top μ {s})] at this

instance (M : HomMarkovChainSpec S)
  : StochasticVec (init_vec M) :=
  ⟨fun s => by unfold init_vec; simp, by unfold init_vec; apply prob_sum_to_one⟩

instance (M : HomMarkovChainSpec S)
  : RowStochastic (kernel_mat M) :=
  ⟨fun s => ⟨fun j => by unfold kernel_mat; simp, by
    unfold kernel_mat
    simp only [Matrix.of_apply]
    haveI := (M.markov_kernel).isProbabilityMeasure s
    apply prob_sum_to_one⟩⟩

omit [Fintype S] [MeasurableSingletonClass S] in
lemma kernel_apply_eq_mat_apply
  (M : HomMarkovChainSpec S) (s s' : S) :
  (M.kernel s {s'}).toReal = kernel_mat M s s' := by
  simp [kernel_mat]

lemma integral_fintype_kernel_iter
  {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α] [DecidableEq S]
  (M : HomMarkovChainSpec S) (n : ℕ) (f : S → α) (s : S) :
  ∫ s', f s' ∂ M.kernel.iter n s = ∑ s', ((kernel_mat M) ^ n) s s' • f s' := by
  induction n generalizing s with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rw [show M.kernel.iter 0 s = Measure.dirac s from Kernel.id_apply s, integral_dirac]
    simp [sum_ite_eq]
  | succ n ih =>
    simp only [pow_succ']
    haveI : IsMarkovKernel M.kernel := M.markov_kernel
    haveI : IsMarkovKernel (M.kernel.iter (n + 1)) :=
      ProbabilityTheory.Kernel.instIsMarkovKernelIter (n + 1) M.kernel
    haveI : IsProbabilityMeasure ((M.kernel.iter (n + 1)) s) := by infer_instance
    have hInt : Integrable f ((M.kernel.iter (n + 1)) s) := Integrable.of_finite
    conv_lhs => rw [show M.kernel.iter (n + 1) = (M.kernel.iter n) ∘ₖ M.kernel from rfl]
    rw [Kernel.integral_comp hInt]
    simp_rw [fun x => ih x]
    simp only [Matrix.mul_apply]
    haveI : IsProbabilityMeasure (M.kernel s) := M.markov_kernel.isProbabilityMeasure s
    rw [integral_fintype (Integrable.of_finite)]
    simp_rw [Measure.real_def, kernel_apply_eq_mat_apply, smul_sum, smul_smul]
    rw [Finset.sum_comm]
    congr 1; ext x; rw [← Finset.sum_smul]

end Finite

end MarkovChain

end ProbabilityTheory
