/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.Subst
import LeanPool.LeanSubst.Laws
import LeanPool.LeanSubst.Option

namespace LeanSubst

variable {S T : Type}

def List.rmap [i : RenMap S] (r : Ren) : List S -> List S
| [] => []
| .cons x tl => (i.rmap r x) :: rmap r tl

instance [RenMap S] : RenMap (List S) where
  rmap := List.rmap

@[simp, grind =]
theorem List.rmap_nil [RenMap S] {r : Ren} : (@List.nil S)⟨r⟩ = [] := by
  simp [RenMap.rmap, List.rmap]

@[simp, grind =]
theorem List.rmap_cons [RenMap S] {x} {tl : List S} {r : Ren}
  : (x :: tl)⟨r⟩ = x⟨r⟩ :: tl⟨r⟩
:= by
  simp [RenMap.rmap, List.rmap]

def List.smap [SubstMap S T] (σ : Subst T) : List S -> List S
| [] => []
| .cons x tl => x[σ:_] :: smap σ tl

instance [SubstMap S T] : SubstMap (List S) T where
  smap := List.smap

@[simp, grind =]
theorem List.smap_nil [SubstMap S T] {σ : Subst T} : (@List.nil S)[σ:_] = [] := by
  simp [SubstMap.smap, List.smap]

@[simp, grind =]
theorem List.smap_cons [SubstMap S T] {x} {tl : List S} {σ : Subst T}
  : (x :: tl)[σ:_] = x[σ:_] :: tl[σ:_]
:= by
  simp [SubstMap.smap, List.smap]

instance [RenMap T] [SubstMap S T] [SubstMapId S T]
  : SubstMapId (List S) T
where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
  : SubstMapCompose (List S) T
where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

@[simp, grind =]
def List.dep_subst_get [SubstMap S T] (σ : Subst T) : List S -> Nat -> Option S
| .nil, _ => none
| .cons h _, 0 => return h[σ:_]
| .cons _ t, n + 1 => (dep_subst_get σ t n)[σ:_]

abbrev List.dep_subst_get1 [SubstMap S S] (σ : Subst S) : List S -> Nat -> Option S :=
  dep_subst_get σ

macro:max t:term noWs "[" x:term "|" σ:term  ":" T:term "]" : term =>
  `(List.dep_subst_get (T := $T) $σ $t $x)

macro:max t:term noWs "[" x:term "|" σ:term "]" : term =>
  `(List.dep_subst_get1 $σ $t $x)

@[app_unexpander List.dep_subst_get1]
def unexpand_list_dep_subst_get1 : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t $x) => `($t[$x|$σ])
| _ => throw ()

@[app_unexpander smap]
def unexpand_list_dep_subst_get : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t $x) => `($t[$x|$σ : _])
| `($_ (T := $T) $σ $t $x) => `($t[$x|$σ : $T])
| _ => throw ()

@[simp, grind =]
theorem List.dep_subst_get_zero [SubstMap S T] {σ : Subst T} {A : S} {Γ : List S}
  : (A::Γ)[0|σ:_] = A[σ:_]
:= by
  simp [dep_subst_get]

@[simp, grind =]
theorem List.dep_subst_get_succ [SubstMap S T] {σ : Subst T} {A : S} {Γ : List S} {x}
  : (A::Γ)[x + 1|σ:_] = Γ[x|σ:_][σ:_]
:= by
  simp [dep_subst_get]

end LeanSubst
