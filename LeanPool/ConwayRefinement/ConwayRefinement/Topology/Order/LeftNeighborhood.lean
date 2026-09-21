/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Topology.Order.Basic

import Mathlib.Topology.Order.LeftRightNhds

/-!
# Eventual predicates in a left neighborhood

This module packages Mathlib's interval basis for `𝓝[<] a` as an explicit-cutoff criterion for an
eventual predicate. It is independent of generalized power series.
-/

universe u

open Set Filter Topology

public section

variable {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [NoMinOrder α]

/-- A predicate holds eventually to the left of `a` exactly when it holds throughout some open
interval `(l, a)`. -/
theorem eventually_nhdsLT_iff_exists {P : α → Prop} {a : α} :
    (∀ᶠ x in 𝓝[<] a, P x) ↔
      ∃ l < a, ∀ x, l < x → x < a → P x := by
  constructor
  · intro hP
    obtain ⟨l, hl, hsubset⟩ := (nhdsLT_basis a).eventually_iff.mp hP
    exact ⟨l, hl, fun x hlx hxa ↦ hsubset ⟨hlx, hxa⟩⟩
  · rintro ⟨l, hl, hP⟩
    apply (nhdsLT_basis a).eventually_iff.mpr
    exact ⟨l, hl, fun x hx ↦ hP x hx.1 hx.2⟩
