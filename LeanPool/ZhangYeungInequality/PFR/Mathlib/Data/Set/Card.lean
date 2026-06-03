/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Set.Card
public import LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic
public import LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Insert

/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Card

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Card`.
-/

public section

namespace Set
variable {α : Type*}

-- TODO: Rename `ncard_singleton_inter` to `ncard_singleton_inter_le_one`

lemma ncard_singleton_inter' (a : α) (s : Set α) [Decidable (a ∈ s)] :
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

lemma ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

end Set
