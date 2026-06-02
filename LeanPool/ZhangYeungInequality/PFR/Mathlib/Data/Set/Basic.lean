/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Set.Basic

/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic`.
-/

public section

namespace Set
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_eq_left` to `inter_eq_left_iff`
@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right

end Set
