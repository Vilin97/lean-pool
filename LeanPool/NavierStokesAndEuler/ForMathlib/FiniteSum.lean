/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Comparing finite sums along an injection

Separate the pointwise estimate, reindexing, and enlargement of the index set.
-/

public section

namespace NavierStokesAndEuler

open Finset

theorem sum_le_sum_of_injOn {ι κ A : Type*} [DecidableEq κ]
    [AddCommMonoid A] [Preorder A] [AddLeftMono A]
    {s : Finset ι} {t : Finset κ} {f : ι → A} {g : κ → A}
    (e : ι → κ) (he : Set.InjOn e s) (himage : s.image e ⊆ t)
    (hbound : ∀ i ∈ s, f i ≤ g (e i))
    (hnonnegative : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) :
    ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc
    _ ≤ ∑ i ∈ s, g (e i) := sum_le_sum hbound
    _ = ∑ j ∈ s.image e, g j := (sum_image he).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg himage hnonnegative

end NavierStokesAndEuler
