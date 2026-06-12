/-
Copyright (c) 2026 André Hernandez-Espiet, Vladimir Sedlacek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: André Hernandez-Espiet, Vladimir Sedlacek
-/
import LeanPool.SyntheticEuclid4.Tactics

/-!
The permutation tactics `perm`, `perma`, and `linperm` for the symmetric area
and angle relations, along with the helper `splitAll` and `push_contra`
tactics. These normalize the point arguments of the geometric primitives using
the symmetry lemmas from `Tactics`.
-/

open SyntheticEuclid4
open IncidenceGeometry

namespace Lean.Elab.Tactic

/-- Definitions for perm tactic -/
def getNthArgName (tgt : Expr) (n : Nat) : MetaM Name :=
  do
    let some id := Lean.Expr.fvarId? (Lean.Expr.getArg! tgt n) | throwError
      "argument {n} is not a free variable"
    id.getUserName

/-- Definitions for perm tactic -/
def lte (n1 : @& Name) (n2 : @& Name) : Bool :=
  Name.lt n1 n2 || n1 = n2

/-- ## Conv tactic `areaNf`
A conv tactic for permuting the variables in an `area` expression. A building block for the `perm`
tactic.
 -/
elab "areaNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@ar132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@ar213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@ar312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@ar231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@ar321 _ _ _] )) -- cba

/-- ## Conv tactic `colinearNf`
A conv tactic for permuting the variables in an `colinear` expression. A building block for the
`perm` tactic.
 -/
elab "colinearNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@col132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@col213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@col312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@col231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@col321 _ _ _] )) -- cba

/-- ## Conv tactic `triangleNf`
A conv tactic for permuting the variables in an `triangle` expression. A building block for the
`perm` tactic.
 -/
elab "triangleNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  let n3 ← getNthArgName tgt 3
  if lte n1 n2 && lte n2 n3 then
    evalTactic (← `(tactic| skip )) -- abc
  else if lte n1 n3 && lte n3 n2 then
    evalTactic (← `(tactic| rw [@tr132 _ _ _] )) -- acb
  else if lte n2 n1 && lte n1 n3 then
    evalTactic (← `(tactic| rw [@tr213 _ _ _] )) -- bac
  else if lte n3 n1 && lte n1 n2 then
    evalTactic (← `(tactic| rw [@tr312 _ _ _] )) -- bca
  else if lte n2 n3 && lte n3 n1 then
    evalTactic (← `(tactic| rw [@tr231 _ _ _] )) -- cab
  else if lte n3 n2 && lte n2 n1 then
    evalTactic (← `(tactic| rw [@tr321 _ _ _] )) -- cba

/-- ## Conv tactic `lengthNf`
A conv tactic for permuting the variables in an `length` expression. A building block for the
`perm` tactic.
 -/
elab "lengthNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@length_symm _ _] ))

/-- ## Conv tactic `angleNf`
A conv tactic for permuting the variables in an `angle` expression. A building block for the
`perm` tactic.
 -/
elab "angleNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n3 ← getNthArgName tgt 3
  if n3.lt n1 then
    evalTactic (← `(tactic| rw [@angle_symm _ _] ))

/-- ## Conv tactic `samesideNf`
A conv tactic for permuting the variables in an `sameside` expression. A building block for the
`perm` tactic.
 -/
elab "samesideNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@ss21 _ _] ))

/-- ## Conv tactic `diffsideNf`
A conv tactic for permuting the variables in an `diffside` expression. A building block for the
`perm` tactic.
 -/
elab "diffsideNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@ds21 _ _] ))

/-- ## Conv tactic `paraNf`
A conv tactic for permuting the variables in an `para` expression. A building block for the `perm`
tactic.
 -/
elab "paraNf" : conv => withMainContext do
  let tgt ← instantiateMVars (← Conv.getLhs)
  let n1 ← getNthArgName tgt 1
  let n2 ← getNthArgName tgt 2
  if n2.lt n1 then
    evalTactic (← `(tactic| rw [@para21 _ _] ))

/-- ## Tactic perm
A custom experimental tactic for permuting the variables in geometric primitives. The ordering is
the one in which the variables are introduced, so it is not necessarily lexigraphic in general.
Usage:
- `perm` permutes the variables in the goal
- `perm at h` permutes the variables in hypothesis `h`
- `perm at *` permutes the variables in the goal and all hypotheses
- `perm [t1 t2 ...]` adds permuted proof terms `t1, t2, ...` to the local context, then runs `perm`
In each of these variants but the last, `perm` can be replaced with `perm only [perm_type]`, where
`perm_type` is one of area, colinear, triangle, length, angle, sameside, diffside.
 -/
syntax "perm" (" [" term,* "]")? ("only" " [" ident "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| perm) => `(tactic|
    (
      try conv in (occs := *) area _ _ _ => all_goals areaNf
      try conv in (occs := *) colinear _ _ _ => all_goals colinearNf
      try conv in (occs := *) triangle _ _ _ => all_goals triangleNf
      try conv in (occs := *) length _ _ => all_goals lengthNf
      try conv in (occs := *) angle _ _ _ => all_goals angleNf
      try conv in (occs := *) SameSide _ _ _ => all_goals samesideNf
      try conv in (occs := *) diffside _ _ _ => all_goals diffsideNf
      try conv in (occs := *) para _ _ => all_goals paraNf
    ))
  | `(tactic| perm at $h:ident) => `(tactic|
    (
      try conv at $h in (occs := *) area _ _ _ => all_goals areaNf
      try conv at $h in (occs := *) colinear _ _ _ => all_goals colinearNf
      try conv at $h in (occs := *) triangle _ _ _ => all_goals triangleNf
      try conv at $h in (occs := *) length _ _ => all_goals lengthNf
      try conv at $h in (occs := *) angle _ _ _ => all_goals angleNf
      try conv at $h in (occs := *) SameSide _ _ _ => all_goals samesideNf
      try conv at $h in (occs := *) diffside _ _ _ => all_goals diffsideNf
      try conv at $h in (occs := *) para _ _ => all_goals paraNf
    ))

open Lean Meta in
/-- Definitions for perm tactic -/
def haveExpr (n : Name) (h : Expr) :=
  withMainContext do
    let t ← inferType h
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← Lean.MVarId.assert mvarId n t h
      let (_, mvarIdNew) ← Lean.MVarId.intro1P mvarIdNew
      return [mvarIdNew]

open Parser Tactic Syntax

/-- Definitions for perm tactic -/
syntax "havePerms" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| havePerms $[[$args,*]]?) => withMainContext do
    let hyps := (← ((args.map (TSepArray.getElems)).getD {}).mapM (elabTerm ·.raw none)).toList
    for h in hyps do
      haveExpr `this h
      evalTactic (← `(tactic| perm at $(mkIdent `this):ident))

macro_rules
  | `(tactic| perm [$args,*] ) => `(tactic| havePerms [$args,*]; perm)

elab_rules: tactic
  | `(tactic| perm only [$perm_type:ident]) => do
    if perm_type == mkIdent `area then
        evalTactic (← `(tactic| try conv in (occs := *) area _ _ _ => all_goals areaNf))
    else if perm_type == mkIdent `colinear then
      evalTactic (← `(tactic| try conv in (occs := *) colinear _ _ _ => all_goals colinearNf))
    else if perm_type == mkIdent `triangle then
      evalTactic (← `(tactic| try conv in (occs := *) triangle _ _ _ => all_goals triangleNf))
    else if perm_type == mkIdent `length then
      evalTactic (← `(tactic| try conv in (occs := *) length _ _ => all_goals lengthNf))
    else if perm_type == mkIdent `angle then
      evalTactic (← `(tactic| try conv in (occs := *) angle _ _ _ => all_goals angleNf))
    else if perm_type == mkIdent `SameSide then
      evalTactic (← `(tactic| try conv in (occs := *) SameSide _ _ _ => all_goals samesideNf))
    else if perm_type == mkIdent `diffside then
      evalTactic (← `(tactic| try conv in (occs := *) diffside _ _ _ => all_goals diffsideNf))
    else if perm_type == mkIdent `para then
      evalTactic (← `(tactic| try conv in (occs := *) para _ _ => all_goals paraNf))
    else
      throwError "permutation type {perm_type} is not valid, please use one of
        'area/colinear/triangle/length/angle/sameside/diffside/para'"
  | `(tactic| perm only [$perm_type:ident] at $h:ident) => withMainContext do
    if perm_type == mkIdent `area then
      evalTactic (← `(tactic| try conv at $h in (occs := *) area _ _ _ => all_goals areaNf))
    else if perm_type == mkIdent `colinear then
      evalTactic (← `(tactic| try conv at $h in (occs := *) colinear _ _ _
        => all_goals colinearNf))
    else if perm_type == mkIdent `triangle then
      evalTactic (← `(tactic| try conv at $h in (occs := *) triangle _ _ _
        => all_goals triangleNf))
    else if perm_type == mkIdent `length then
      evalTactic (← `(tactic| try conv at $h in (occs := *) length _ _ => all_goals lengthNf))
    else if perm_type == mkIdent `angle then
      evalTactic (← `(tactic| try conv at $h in (occs := *) angle _ _ _ => all_goals angleNf))
    else if perm_type == mkIdent `SameSide then
      evalTactic (← `(tactic| try conv at $h in (occs := *) SameSide _ _ _
        => all_goals samesideNf))
    else if perm_type == mkIdent `diffside then
      evalTactic (← `(tactic| try conv at $h in (occs := *) diffside _ _ _
        => all_goals diffsideNf))
    else if perm_type == mkIdent `para then
      evalTactic (← `(tactic| try conv at $h in (occs := *) para _ _ => all_goals paraNf))
    else
      throwError "permutation type {perm_type} is not valid, please use one of
        'area/colinear/triangle/length/angle/sameside/diffside'"
  | `(tactic| perm at *) => withMainContext do
    evalTactic (← `(tactic| perm))
    for ldecl in ← getLCtx do
      let name := mkIdent ldecl.userName
      if !ldecl.isImplementationDetail then evalTactic (← `(tactic| perm at $name:ident))
  | `(tactic| perm only [$perm_type] at *) => withMainContext do
    evalTactic (← `(tactic| perm only [$perm_type]))
    for ldecl in ← getLCtx do
      let name := mkIdent ldecl.userName
      if !ldecl.isImplementationDetail then
        evalTactic (← `(tactic| perm only [$perm_type] at $name:ident))

/-- Definitions for perm tactic -/
elab "assumptionSymm" : tactic => withMainContext do
  for ldecl in ← getLCtx do
    let name := mkIdent ldecl.userName
    if !ldecl.isImplementationDetail then
      evalTactic (← `(tactic| try exact Eq.symm $name))

/-- ## Tactic perma
Like `perm`, but also tries to exact assumptions and their symmetrized versions.
 -/
syntax "perma" ("[" term,* "]")? ("only" " [" ident "]")? (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| perma) => `(tactic| perm; try assumption; try assumptionSymm)
  | `(tactic| perma at $h:ident) => `(tactic| perm at $h:ident; try exact $h; try exact Eq.symm $h)
  | `(tactic| perma only [$perm_type]) =>
      `(tactic| perm only [$perm_type]; try assumption; try assumptionSymm)
  | `(tactic| perma only [$perm_type] at $h:ident) =>
      `(tactic| perm only [$perm_type] at $h:ident; try exact $h; try exact Eq.symm $h)
  | `(tactic| perma at *) =>
      `(tactic| perm at *; try assumption; try assumptionSymm)
  | `(tactic| perma only [$perm_type] at *) =>
      `(tactic| perm only [$perm_type] at *; try assumption; try assumptionSymm)
  | `(tactic| perma [$args,*] ) =>
      `(tactic| perm [$args,*]; try assumption; try assumptionSymm)

/-- ## Tactic linperm
A combination of linarith and perm.
Usage:
- `linperm` runs `perm at *` followed by `linarith`
- `linperm [t1 t2 ...]` runs `perm at *`, adds permuted proof terms `t1, t2, ...` to the local
context, and finishes with `linarith`
 -/
syntax "linperm " ("[" term,* "]")? : tactic

macro_rules
  | `(tactic| linperm) => `(tactic| perm at *; linarith)
  | `(tactic| linperm [$args,*] ) => `(tactic| perm at *; havePerms [$args,*]; linarith)

/-- Tactic for breaking ands up -/
macro "splitAll" : tactic => `(tactic | repeat' constructor)

/-- by_contra followed by `push Not` -/
syntax "push_contra" ident location : tactic

macro_rules
  | `(tactic| push_contra $h:ident $l:location) => `(tactic|
    (
      by_contra $h
      push Not $l:location
    ))

end Lean.Elab.Tactic
