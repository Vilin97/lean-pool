/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

/-!
# LeanPool.RlTheoryInLean.Probability.Kernel.Basic
-/

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory
open Finset Bornology NNReal ENNReal Preorder Filter

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Iterates of a homogeneous transition kernel. -/
noncomputable def iter (κ : Kernel α α) : ℕ → Kernel α α
| 0       => Kernel.id
| (n + 1) => ((iter κ) n).comp κ

instance (n : ℕ) (κ : Kernel α α) [IsMarkovKernel κ] :
  IsMarkovKernel (κ.iter n) := by
  induction n with
  | zero => simp only [iter]
            infer_instance
  | succ n ih => simp only [iter]
                 infer_instance

lemma iter_comm (κ : Kernel α α) (n : ℕ) :
  κ ∘ₖ κ.iter n = κ.iter n ∘ₖ κ := by
  induction n with
  | zero => simp [iter, Kernel.id_comp]
  | succ n ih =>
    simp only [iter]
    conv_rhs => rw [← ih]
    simp [comp_assoc]

lemma iter_comp (κ : Kernel α α) (m n : ℕ) :
  (κ.iter m).comp (κ.iter n) = κ.iter (m + n) := by
  induction m with
  | zero => simp [iter, Kernel.id_comp]
  | succ m ih =>
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this, iter, iter, ← ih]
    simp only [comp_assoc]
    apply congrArg
    simp [iter_comm]

end ProbabilityTheory.Kernel
