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

/-- Apply a renaming pointwise to every element of a list. -/
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

/-- Apply a substitution pointwise to every element of a list. -/
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

/-- Look up the `n`-th element of a context list, substituting all binders crossed. -/
@[simp, grind =]
def List.depSubstGet [SubstMap S T] (σ : Subst T) : List S -> Nat -> Option S
| .nil, _ => none
| .cons h _, 0 => return h[σ:_]
| .cons _ t, n + 1 => (depSubstGet σ t n)[σ:_]

/-- Homogeneous variant of `List.depSubstGet` (the `S = T` case). -/
abbrev List.depSubstGet1 [SubstMap S S] (σ : Subst S) : List S -> Nat -> Option S :=
  depSubstGet σ

/-- Notation `t[x|σ : T]` for `List.depSubstGet` over `T`. -/
macro:max t:term noWs "[" x:term "|" σ:term  ":" T:term "]" : term =>
  `(List.depSubstGet (T := $T) $σ $t $x)

/-- Notation `t[x|σ]` for the homogeneous `List.depSubstGet1`. -/
macro:max t:term noWs "[" x:term "|" σ:term "]" : term =>
  `(List.depSubstGet1 $σ $t $x)

/-- Pretty-printer that displays `List.depSubstGet1 σ t x` as `t[x|σ]`. -/
@[app_unexpander List.depSubstGet1]
def unexpandListDepSubstGet1 : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t $x) => `($t[$x|$σ])
| _ => throw ()

/-- Pretty-printer that displays `List.depSubstGet σ t x` as `t[x|σ : _]`. -/
@[app_unexpander smap]
def unexpandListDepSubstGet : Lean.PrettyPrinter.Unexpander
| `($_ $σ $t $x) => `($t[$x|$σ : _])
| `($_ (T := $T) $σ $t $x) => `($t[$x|$σ : $T])
| _ => throw ()

@[simp, grind =]
theorem List.depSubstGetZero [SubstMap S T] {σ : Subst T} {A : S} {Γ : List S}
  : (A::Γ)[0|σ:_] = A[σ:_]
:= by
  simp [depSubstGet]

@[simp, grind =]
theorem List.depSubstGetSucc [SubstMap S T] {σ : Subst T} {A : S} {Γ : List S} {x}
  : (A::Γ)[x + 1|σ:_] = Γ[x|σ:_][σ:_]
:= by
  simp [depSubstGet]

end LeanSubst
