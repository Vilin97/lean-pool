/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  ε-optimal Selection — proved by pointwise choice

  This file provides everything UpperBound.lean needs, with ZERO sorry.

  Note: the original axiom claimed `Measurable sel`, but the statement
  has only [MeasurableSpace α] — no topology or Polish structure — making
  measurability unprovable. Since `Measurable sel` is discarded at the
  call site (UpperBound.lean uses `_`), we drop it and prove the rest.
-/
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set ENNReal

noncomputable section

/-- Pointwise ε-optimal element in a nonempty set. -/
private theorem eps_optimal_element'
    {α : Type*} (S : Set α) (h_ne : S.Nonempty)
    (f : α → ENNReal) (ε : ENNReal) (hε : 0 < ε) :
    ∃ a ∈ S, f a ≤ (⨅ (x : α) (_ : x ∈ S), f x) + ε := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  obtain ⟨a, ha⟩ := h_ne
  have hlt := h a ha
  have : (⨅ (x : α) (_ : x ∈ S), f x) + ε ≤ ⨅ (x : α) (_ : x ∈ S), f x :=
    le_iInf fun x => le_iInf fun hx => le_of_lt (h x hx)
  by_cases htop : (⨅ (x : α) (_ : x ∈ S), f x) = ⊤
  · simp [htop] at hlt
  · exact absurd this (not_le.mpr (ENNReal.lt_add_right htop hε.ne'))

/-- ε-optimal selection: for each a, choose m ∈ S(a) with f(a,m) ≤ inf + ε. -/
theorem eps_optimal_selection
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : α → Set (Measure β))
    (h_ne : ∀ a, (S a).Nonempty)
    (f : α → Measure β → ENNReal)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (sel : α → Measure β),
      (∀ a, sel a ∈ S a) ∧
      (∀ a, f a (sel a) ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε) := by
  have key : ∀ a, ∃ m ∈ S a, f a m ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε :=
    fun a => eps_optimal_element' (S a) (h_ne a) (f a) ε hε
  choose sel hsel_mem hsel_opt using key
  exact ⟨sel, hsel_mem, hsel_opt⟩

end
