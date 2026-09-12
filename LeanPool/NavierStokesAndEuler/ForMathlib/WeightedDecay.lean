/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Weighted bounds for fields with bounded future time support

A uniform weighted bound on a time slab gives a global reciprocal-weight bound
when the field vanishes after the slab. The spatial type, normed codomain, lower
time endpoint, and positive weight are arbitrary. Periodic and compact-support
force estimates supply the slab bound by different compactness arguments.
-/

public section

namespace NavierStokesAndEuler.WeightedDecay

open Set

/-- Extend a weighted bound on `[a, T]` to a reciprocal-weight estimate for all
`t ≥ a`, when the field vanishes for `t > T`. -/
theorem exists_pos_norm_le_div_of_slab_bound {X V : Type*} [SeminormedAddCommGroup V]
    {J : ℝ × X → V} {w : ℝ × X → ℝ} {a T : ℝ}
    (hw : ∀ t : ℝ, a ≤ t → ∀ x : X, 0 < w (t, x))
    (hzero : ∀ t : ℝ, T < t → ∀ x : X, J (t, x) = 0)
    (hbound : ∃ M : ℝ, ∀ t ∈ Icc a T, ∀ x : X, ‖J (t, x)‖ * w (t, x) ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, a ≤ t → ∀ x : X, ‖J (t, x)‖ ≤ C / w (t, x) := by
  obtain ⟨M, hM⟩ := hbound
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  have hwpos := hw t ht x
  by_cases htT : t ≤ T
  · rw [le_div_iff₀ hwpos]
    exact (hM t ⟨ht, htT⟩ x).trans (le_max_left _ _)
  · rw [hzero t (lt_of_not_ge htT) x, norm_zero]
    exact (div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hwpos).le

end NavierStokesAndEuler.WeightedDecay
