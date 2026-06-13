/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# LeanPool.RlTheoryInLean.Order.Filter.Basic
-/

open Finset Real Filter
open scoped BigOperators

namespace Filter

lemma EventuallyEq.finset_sum {α ι β : Type*} [AddCommGroup β] {l : Filter α}
  {s : Finset ι} {f g : ι → α → β} (hfg : ∀ i ∈ s, f i =ᶠ[l] g i) :
  ∑ i ∈ s, f i =ᶠ[l] ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hfg a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))

end Filter
