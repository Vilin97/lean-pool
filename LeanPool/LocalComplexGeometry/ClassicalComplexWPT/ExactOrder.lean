/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Basic
import Mathlib.Analysis.Analytic.Order

/-!
# Exact order in the distinguished variable

This file connects the public derivative-based order condition to elementary
properties of the distinguished-variable slice.  The deeper comparison with
analytic order is developed separately from these edge-case lemmas.
-/

open scoped Topology


namespace ClassicalComplexWPT

/-- Restricting an analytic germ to the distinguished-variable axis preserves analyticity. -/
theorem analyticAt_lastSlice {n : ℕ} {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (lastSlice f) 0 := by
  change AnalyticAt ℂ (fun w : ℂ ↦ f ((0 : Base n), w)) 0
  have haxis : AnalyticAt ℂ (fun w : ℂ ↦ ((0 : Base n), w)) 0 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ (0 : Base n)) 0).prod analyticAt_id
  have hcomp := AnalyticAt.comp (g := f) (f := fun w : ℂ ↦ ((0 : Base n), w)) hf haxis
  simpa [Function.comp_def] using hcomp

/-- Exact order zero is exactly nonvanishing at the origin. -/
theorem exactOrderInLastVariable_zero_iff {n : ℕ} {f : Ambient n → ℂ} :
    ExactOrderInLastVariable f 0 ↔ f 0 ≠ 0 := by
  have hzero : (0 : Ambient n) = ((0 : Base n), 0) := by
    ext <;> simp
  constructor
  · intro h
    rw [hzero]
    simpa [lastSlice] using h.2
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      omega
    · rw [iteratedDeriv_zero]
      change f ((0 : Base n), 0) ≠ 0
      rw [← hzero]
      exact h

/-- For an analytic germ, the public derivative condition agrees with Mathlib's analytic order. -/
theorem exactOrderInLastVariable_iff_analyticOrderAt {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ExactOrderInLastVariable f d ↔ analyticOrderAt (lastSlice f) 0 = d := by
  simpa [ExactOrderInLastVariable] using
    (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (analyticAt_lastSlice hf) (n := d)).symm

/-- The exact-order hypothesis supplies the normalized one-variable axis factorization. -/
theorem exists_lastSlice_eq_pow_mul {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
      lastSlice f =ᶠ[𝓝 0] fun w ↦ w ^ d * g w := by
  have hord : analyticOrderAt (lastSlice f) 0 = d :=
    (exactOrderInLastVariable_iff_analyticOrderAt hf).mp horder
  obtain ⟨g, hg, hg0, heq⟩ :=
    (AnalyticAt.analyticOrderAt_eq_natCast (analyticAt_lastSlice hf)).mp hord
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [heq] with w hw
  simpa using hw

end ClassicalComplexWPT
