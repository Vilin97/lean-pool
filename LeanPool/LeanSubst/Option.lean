/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.Subst
import LeanPool.LeanSubst.Laws

namespace LeanSubst

variable {S T : Type}

def Option.rmap [i : RenMap S] (r : Ren) : Option S -> Option S
| none => none
| some t => some (i.rmap r t)

instance [RenMap S] : RenMap (Option S) where
  rmap := Option.rmap

def Option.smap [SubstMap S T] (σ : Subst T) : Option S -> Option S
| none => none
| some t => some t[σ:_]

instance [SubstMap S T] : SubstMap (Option S) T where
  smap := Option.smap

@[simp, grind =]
theorem Option.smap_none [SubstMap S T] {σ : Subst T}
  : (@Option.none S)[σ:_] = none
:= by
  simp [SubstMap.smap, Option.smap]

@[simp, grind =]
theorem Option.smap_some [SubstMap S T] {x : S} {σ : Subst T}
  : (some x)[σ:_] = some x[σ:_]
:= by
  simp [SubstMap.smap, Option.smap]

instance [RenMap T] [SubstMap S T] [SubstMapId S T]
  : SubstMapId (Option S) T
where
  apply_id := by intro t; cases t <;> simp

instance [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
  : SubstMapCompose (Option S) T
where
  apply_compose := by intro s σ τ; cases s <;> simp

end LeanSubst
