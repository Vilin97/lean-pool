/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Kernel.Defs

open MeasureTheory ProbabilityTheory Filter

lemma Tendsto.filter_congr
  {α β : Type*} {f : α → β} {a : Filter α} {b b' : Filter β}
  (hb : b = b') (hf : Tendsto f a b) : Tendsto f a b' := by
  rw [←hb]
  exact hf


lemma Kernel.congrFun_apply
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {κ₁ κ₂ : Kernel α β}
  (h : κ₁ = κ₂) :
  ∀ a, κ₁ a = κ₂ a := by
  intro a
  rw [h]

lemma Measurable.congr
  {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β} {f g : α → β}
  (hfg : f = g) : Measurable f → Measurable g := by
  intro hf
  rw [←hfg]
  exact hf

lemma Integrable.measure_congr
  {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  {β : Type*} {f : α → β}
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {hμν : μ = ν}
  (hf : Integrable f μ) : Integrable f ν := by
  rw [←hμν]
  exact hf

lemma Integral.measure_congr
  {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  {β : Type*} {f : α → β}
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {hμν : μ = ν} : ∫ x, f x ∂ μ = ∫ x, f x ∂ ν := by
  rw [hμν]

lemma HasDerivAt.congr
  {f g : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hfg : f = g)
  (h : HasDerivAt f f' x) : HasDerivAt g f' x := by
  rw [←hfg]
  exact h

lemma HasDerivAt.congr_congr
  {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
  (h : HasDerivAt f f' x)
  (hfg : f = g) (hfg' : f' = g') : HasDerivAt g g' x := by
  rw [←hfg, ←hfg']
  exact h

namespace RLTheory

variable {d : ℕ}
/-- Euclidean space of dimension `d`, used for finite-dimensional RL iterates. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

end RLTheory
