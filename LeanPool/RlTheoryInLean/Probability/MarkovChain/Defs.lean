/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Logic.Function.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# LeanPool.RlTheoryInLean.Probability.MarkovChain.Defs
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory
open Finset NNReal ENNReal Preorder Function

namespace ProbabilityTheory

namespace MarkovChain

universe u
variable (S : Type u) [MeasurableSpace S]

/-- A homogeneous Markov chain specified by its transition kernel and initial law. -/
structure HomMarkovChainSpec (S : Type u) [MeasurableSpace S] where
  /-- The one-step transition kernel. -/
  kernel : Kernel S S
  /-- The transition kernel is Markov. -/
  markov_kernel : IsMarkovKernel kernel
  /-- The initial distribution. -/
  init : ProbabilityMeasure S

/-- Iterates of the transition kernel of a Markov chain. -/
noncomputable def Kernel.iter (κ : Kernel S S) : ℕ → Kernel S S
| 0       => Kernel.id
| (n + 1) => ((iter κ) n).comp κ

end MarkovChain

end ProbabilityTheory
