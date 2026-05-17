/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Bornology.Basic

import LeanPool.RlTheoryInLean.MeasureTheory.Measure.Prod

open MeasureTheory MeasureTheory.Measure Filtration ProbabilityTheory.Kernel ProbabilityTheory
open Finset Bornology NNReal ENNReal Preorder Filter

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Comap a kernel along the last coordinate of a finite trajectory prefix. -/
noncomputable def comap_last
  (κ : Kernel α α) (n : ℕ) :
  Kernel (Iic n → α) α := by
  let g : (Iic n → α) → α :=
    fun history => history ⟨n, by simp [mem_Iic]⟩
  have hg : Measurable g := by apply measurable_pi_apply
  exact κ.comap g hg

lemma prod_map_fst
(κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsMarkovKernel η] :
(κ.prod η).map Prod.fst = κ := by
  ext a s hs
  rw [Kernel.map_apply, Measure.map_apply, Kernel.prod_apply, prod_preimage_fst]
  · simp
  · infer_instance
  · measurability
  · exact hs
  · measurability

lemma prod_map_snd
  (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] :
  (κ.prod η).map Prod.snd = η := by
  ext a s hs
  rw [Kernel.map_apply, Measure.map_apply, Kernel.prod_apply, prod_preimage_snd]
  · simp
  · infer_instance
  · measurability
  · exact hs
  · measurability


end ProbabilityTheory.Kernel
