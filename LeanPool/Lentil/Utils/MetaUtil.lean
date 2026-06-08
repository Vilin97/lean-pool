/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean

open Lean Meta Elab Tactic

namespace LentilLib

/-- Add a single theorem to the environment by providing its name, type and proof. -/
def simpleAddTheorem (name : Name) (lvlParams : List Name) (type value : Expr) (nonComputable? : Bool) : CoreM Unit := do
  let thm := Declaration.thmDecl <| mkTheoremValEx name lvlParams type value []
  if nonComputable? then
    addDecl <| thm
    setEnv <| addNoncomputable (← getEnv) name
  else
    addAndCompile thm

/-- Prove a theorem at the level of `MetaM`, without going into the proof mode. -/
def simpleProveTheorem (name : Name) (lvlParams : List Name) (type : Expr) (proofScript : TSyntax `term)
    (nonComputable? : Bool) : MetaM Unit := do
  let proof ← liftCommandElabM <| Command.liftTermElabM do
    -- when things go wrong, print the proof goal
    let proof ← Term.elabTermAndSynthesize proofScript type
    if proof.hasSorry then
      trace[lentil.debug] "theorem {name} : {type} := {proofScript}"
    -- it is **SUPER WEIRD** that without adding this check, `proof` would still contain
    -- level metavariables, and `instantiateMVars` would not work as expected!
    check proof
    instantiateMVars proof
  simpleAddTheorem name lvlParams type proof nonComputable?

-- inspired by [this discussion](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Generating.20fresh.20names.20for.20universe.20levels)
/-- Search successive indexed names `baseName_i` (starting at `i`) for one not in
    `names`. `fuel` bounds the search; `names.length + 1` candidates always
    contain a fresh one. -/
private def mkUnusedNameLoop (names : List Name) (baseName : Name) (i : Nat) :
    Nat → Name
  | 0 => Name.appendIndexAfter baseName i
  | fuel + 1 =>
    let w := Name.appendIndexAfter baseName i
    if names.contains w then
      mkUnusedNameLoop names baseName (i + 1) fuel
    else
      w

/-- Gives a name based on `baseName` that's not already in the list. -/
def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    mkUnusedNameLoop names baseName 1 (names.length + 1)

/-- Is `stx`, a `Term`, an `Ident`? -/
def termIdentOpt (stx : TSyntax `term) : TacticM (Option (TSyntax `ident)) := do
  match stx with
  | `(term| $id:ident) => pure (some id)
  | _ => pure none

-- NOTE: This comes from Mathlib
/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
def «let» (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := none) :
    MetaM (FVarId × MVarId) := do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

end LentilLib
