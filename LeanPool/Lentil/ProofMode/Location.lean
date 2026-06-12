/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

namespace TLA.ProofMode

open Lean Meta Elab Tactic

/-- Syntax for referring to a proof-mode hypothesis by name or index. -/
syntax temporalHypLoc := (ident <|> num)

/-- Locations for proof-mode hypotheses. Can be a name or an index. -/
inductive TemporalHypLoc where
  | byName (name : String)
  | byIdx (idx : Nat)

/-- Parse a `temporalHypLoc` syntax into a `TemporalHypLoc`. -/
def parseTemporalHypLoc (pos : Syntax) (errorMsg : MessageData) : TacticM TemporalHypLoc := do
  -- FIXME: Is this too hacky? It seems that matching on both `term` and `temporalHypLoc` is
  -- necessary in certain cases, but is there a better way to do this?
  match pos with
  | `(term| $id:ident) | `(temporalHypLoc| $id:ident) => pure <| .byName <| toString id.getId
  | `(term| $num:num) | `(temporalHypLoc| $num:num) => pure <| .byIdx <| num.getNat
  | _ => throwError errorMsg

/-- Quote a `TemporalHypLoc` back into `temporalHypLoc` syntax. -/
def quoteTemporalHypLoc : TemporalHypLoc → TacticM (TSyntax ``temporalHypLoc)
  | .byName name => `(temporalHypLoc| $(mkIdent (.mkSimple name)):ident)
  | .byIdx idx => `(temporalHypLoc| $(Syntax.mkNatLit idx):num)

/-- Quote a `TemporalHypLoc` as a term. -/
def quoteTemporalHypLocToTerm : TemporalHypLoc → TSyntax `term
  | .byName name => quote name
  | .byIdx idx => quote idx

/-- Look up a hypothesis by location, returning `none` if absent. -/
def findByTemporalHypLocOpt (xs : List (String × α)) : TemporalHypLoc → Option (String × α)
  | .byName name => xs.find? fun x => x.1 == name
  | .byIdx idx => xs[idx]?

/-- Look up a hypothesis by location, throwing an error if absent. -/
def findByTemporalHypLoc [Monad m] [MonadError m] (xs : List (String × α)) (loc : TemporalHypLoc)  (errorMsgPrefix errorMsgSuffix : String) : m (String × α) := do
  match findByTemporalHypLocOpt xs loc with
  | some res => pure res
  | none =>
    match loc with
    | .byName name => throwError m!"{errorMsgPrefix}: hypothesis '{name}' not found in {errorMsgSuffix}"
    | .byIdx idx => throwError m!"{errorMsgPrefix}: hypothesis index {idx} not found in {errorMsgSuffix}"

/-- If `tm` is a bare identifier that names a proof-mode hypothesis in `hyps`,
return that name. Lean locals shadow proof-mode hypotheses. -/
def temporalHypNameOfBareTermOpt (hyps : List (String × α)) (tm : Term) :
    TacticM (Option String) := withMainContext do
  let some id ← LentilLib.termIdentOpt tm | return none
  if (← getLCtx).findFromUserName? id.getId |>.isSome then
    return none
  let name := toString id.getId
  return if hyps.any (fun ⟨hypName, _⟩ => hypName == name) then some name else none

/-- Interpret a bare term as a hypothesis location, if it names one. -/
def temporalHypLocOfBareTermOpt (hyps : List (String × α)) (tm : Term) :
    TacticM (Option TemporalHypLoc) := do
  return (← temporalHypNameOfBareTermOpt hyps tm).map .byName

/-- Locations for `rewrite`/`simp`-like tactics. -/
structure RewriteLocation where
  /-- The hypothesis indices targeted by a rewrite location. -/
  idxs : Array Nat
  /-- Whether the rewrite location includes the goal. -/
  includeGoal : Bool
  /-- Whether the rewrite location is a wildcard. -/
  isWildCard : Bool

/-- Parse a rewrite location into the targeted indices. -/
def parseRewriteLocation
    (hyps : List (String × Expr))
    (loc? : Option (TSyntax ``Lean.Parser.Tactic.location))
    (errorMsgPrefix : String) : TacticM RewriteLocation := do
  match loc? with
  | none => return ⟨#[], true, false⟩
  | some loc =>
    -- Reuse the logic for location expansion from Lean
    -- NOTE: `expandOptLocation` does not work here, it seems
    let loc := expandLocation loc
    match loc with
    | Location.wildcard =>
      return ⟨Array.range hyps.length, true, true⟩
    | Location.targets stxs includeGoal =>
      let idxs ← stxs.mapM fun x => do
        let hypLoc ← parseTemporalHypLoc x m!"{errorMsgPrefix}: unsupported location {x}; expected a proof-mode hypothesis name or index"
        match hypLoc with
        | .byName name =>
          let some idx := hyps.findIdx? fun hyp => hyp.1 == name
            | throwError "{errorMsgPrefix}: hypothesis {name} not found in the goal"
          pure idx
        | .byIdx idx =>
          if idx < hyps.length then pure idx else throwError "{errorMsgPrefix}: hypothesis index {idx} is out of bounds"
      return ⟨idxs, includeGoal, false⟩

end TLA.ProofMode
