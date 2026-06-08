/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import Mathlib.Logic.Relation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Cases

/-!
# Basic

Basic definitions for the Chomsky-hierarchy formalization: symbols of a formal grammar.
-/


section notations

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr

/-- The "left" or "top" variant. -/
prefix:max "◩" => Sum.inl

/-- The "right" or "bottom" variant. -/
prefix:max "◪" => Sum.inr

/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
notation:max "↓"t:arg => (fun _ => t)

end notations


section unexpanders

@[app_unexpander List.map]
def List.map_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

@[app_unexpander List.filterMap]
def List.filterMap_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `filterMap) $f)
  | _ => throw ()

@[app_unexpander List.take]
def List.take_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

@[app_unexpander List.drop]
def List.drop_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `drop) $n)
  | _ => throw ()

end unexpanders
