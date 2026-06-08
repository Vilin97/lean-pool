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


namespace Chomsky

/-- The left-to-right direction of `↔`. -/
scoped postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
scoped postfix:max ".←" => Iff.mpr

/-- The "left" or "top" variant. -/
scoped prefix:max "◄" => Sum.inl

/-- The "right" or "bottom" variant. -/
scoped prefix:max "▶" => Sum.inr

/-- Writing `↓t` is slightly more general than writing `Function.const _ t`. -/
scoped notation:max "↓"t:arg => (fun _ => t)

end Chomsky


namespace Chomsky

section unexpanders

/-- Pretty-print `List.map f l` using dot notation `l.map f`. -/
@[app_unexpander List.map]
def List.mapUnexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `map) $f)
  | _ => throw ()

/-- Pretty-print `List.filterMap f l` using dot notation `l.filterMap f`. -/
@[app_unexpander List.filterMap]
def List.filterMapUnexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $l) => `($(l).$(Lean.mkIdent `filterMap) $f)
  | _ => throw ()

/-- Pretty-print `List.take n l` using dot notation `l.take n`. -/
@[app_unexpander List.take]
def List.takeUnexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `take) $n)
  | _ => throw ()

/-- Pretty-print `List.drop n l` using dot notation `l.drop n`. -/
@[app_unexpander List.drop]
def List.dropUnexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $n $l) => `($(l).$(Lean.mkIdent `drop) $n)
  | _ => throw ()

end unexpanders

end Chomsky
