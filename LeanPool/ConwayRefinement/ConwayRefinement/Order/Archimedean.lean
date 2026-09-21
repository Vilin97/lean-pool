/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.WellFoundedSet

import Mathlib.Data.Real.Embedding
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Countability in Archimedean ordered groups

Every partially well-ordered subset of an Archimedean linearly ordered additive group is
countable. The proof embeds the group into `ℝ` and assigns to each point the gap before its
successor in the subset; second countability of `ℝ` makes the resulting disjoint family of
intervals countable.
-/

universe u

public section

variable {G : Type u}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]

open TopologicalSpace

namespace Set.IsPWO

/-- A partially well-ordered subset of an Archimedean ordered additive group is countable. -/
theorem countable_of_archimedean {s : Set G} (hs : s.IsPWO) : s.Countable := by
  obtain ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective G
  have hfstrict : StrictMono f := f.monotone'.strictMono_of_injective hf
  have hcount := countable_image_lt_image_Ioi_within (t := s) f
  apply hcount.mono
  intro x hx
  refine ⟨hx, ?_⟩
  by_cases hupper : ({y ∈ s | x < y} : Set G).Nonempty
  · obtain ⟨y, hy⟩ := (hs.mono fun z hz => hz.1).exists_minimal hupper
    refine ⟨f y, ?_, ?_⟩
    · exact hfstrict hy.1.2
    · intro z hz hxz
      exact f.monotone' ((le_total y z).elim id fun hzy => hy.2 ⟨hz, hxz⟩ hzy)
  · refine ⟨f x + 1, by linarith, ?_⟩
    intro y hy hxy
    exact (hupper ⟨y, hy, hxy⟩).elim

end Set.IsPWO
