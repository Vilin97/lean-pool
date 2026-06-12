/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Basic

namespace TLA.Expr

open Lean Meta

/-- Split a TLA conjunction `Expr` into its list of conjuncts. -/
def splitAndIntoParts (p : Expr) : MetaM (List Expr) := do
  match p with
  | .app (.app (.app (.const ``TLA.tlaAnd _) _) a) b =>
    let as ← splitAndIntoParts a
    let bs ← splitAndIntoParts b
    pure (as ++ bs)
  | _ => pure [p]

/-- Split a chain of TLA implications into its list of premises and conclusion,
    optionally further splitting each premise conjunction (`cutAnd?`). -/
def splitImplicationsIntoParts (p : Expr) (cutAnd? : Bool := true) :
    MetaM (List Expr × Expr) := do
  match p with
  | .app (.app (.app (.const ``TLA.tlaImplies _) _) hp) q =>
    let ps ← if cutAnd? then splitAndIntoParts hp else pure [hp]
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure ([], p)

/-- Split a `predImplies`/`valid` statement into its premises and conclusion. -/
def splitPredImpliesIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.predImplies _ p q =>
    let ps ← splitAndIntoParts p
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | TLA.valid _ body => splitImplicationsIntoParts body
  | _ => throwError "not a |-tla- statement"

/-- Given some TLA related expression and return the type of the state
    (i.e., the argument after `TLA.pred`).
    While this could be done via `inferType`, just peeking the expression
    should be much "cheaper". -/
def peekStateType (p : Expr) : Option Expr :=
  match_expr p with
  | TLA.predImplies σ _ _ => .some σ
  | TLA.valid σ _ => .some σ
  | _ => .none

end TLA.Expr
