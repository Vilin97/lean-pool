/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.MeasureTheory.MeasurableSpace.Constructions
import LeanPool.RlTheoryInLean.Probability.MarkovChain.Defs
import LeanPool.RlTheoryInLean.MeasureTheory.Function.L1Space.Integrable

open RLTheory
open MeasureTheory MeasureTheory.Measure Filtration
open ProbabilityTheory.Kernel
open ProbabilityTheory
open Finset Bornology
open NNReal ENNReal Preorder Filter


namespace ProbabilityTheory

namespace MarkovChain

universe u
variable {S : Type u} [MeasurableSpace S]

/-- Comap a homogeneous kernel along the latest state in a finite history. -/
noncomputable def kernel_comap_trivial
  (κ : Kernel S S) (n : ℕ) :
  Kernel (Iic n → S) S := by
  let g : (Iic n → S) → S :=
    fun history => history ⟨n, by simp [mem_Iic]⟩
  have hg : Measurable g := by apply measurable_pi_apply
  exact κ.comap g hg

/-- Expand a homogeneous Markov-chain kernel to act on finite trajectory prefixes. -/
noncomputable def expand_kernel
  (M : HomMarkovChainSpec S) :
  ∀ n : ℕ, Kernel (Iic n → S) S := by
    intro n
    let g : (Iic n → S) → S :=
      fun history => history ⟨n, by simp [mem_Iic]⟩
    have hg : Measurable g := by apply measurable_pi_apply
    exact M.kernel.comap g hg

instance (M : HomMarkovChainSpec S) :
  ∀ n, IsMarkovKernel (expand_kernel M n) := by
  intro n
  have := M.markov_kernel
  unfold expand_kernel
  apply IsMarkovKernel.comap

/-- The trajectory law started from a fixed length-zero prefix. -/
noncomputable def traj_prob₀
  (M : HomMarkovChainSpec S) (x₀ : Iic 0 → S)
  : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := fun _ : ℕ => S) (expand_kernel M) 0
  let prob := κ x₀
  exact ⟨prob, inferInstance⟩

/-- The trajectory law obtained by first sampling the initial state. -/
noncomputable def traj_prob
  (M : HomMarkovChainSpec S) : ProbabilityMeasure (ℕ → S) := by
  let κ := traj (X := fun _ : ℕ => S) (expand_kernel M) 0
  let f : S → (Iic 0 → S) := fun s => (fun _ : Iic 0 => s)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_id
  let init := M.init.map hf.aemeasurable
  haveI : IsProbabilityMeasure init.1 := init.2
  let prob := init.1.bind κ
  exact ⟨prob, inferInstance⟩

end MarkovChain

end ProbabilityTheory
