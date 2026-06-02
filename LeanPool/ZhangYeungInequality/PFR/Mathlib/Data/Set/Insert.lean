/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Set.Insert

/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Insert

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Insert`.
-/

public section

namespace Set
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_singleton_eq_empty` to `inter_singleton_eq_empty_iff`
alias ⟨_, inter_singleton_eq_empty'⟩ := inter_singleton_eq_empty

-- TODO: Rename `singleton_inter_eq_empty` to `singleton_inter_eq_empty_iff`
alias ⟨_, singleton_inter_eq_empty'⟩ := singleton_inter_eq_empty

end Set
