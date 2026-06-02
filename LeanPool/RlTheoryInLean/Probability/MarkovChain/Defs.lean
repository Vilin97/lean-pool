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
import Mathlib.Logic.Function.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# LeanPool.RlTheoryInLean.Probability.MarkovChain.Defs
-/

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
