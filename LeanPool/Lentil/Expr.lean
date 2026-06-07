/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Basic

namespace TLA.Expr

open Lean Meta

partial def splitAndIntoParts (p : Expr) : MetaM (List Expr) := do
  match_expr p with
  | TLA.tla_and _ a b =>
    let as ← splitAndIntoParts a
    let bs ← splitAndIntoParts b
    pure (as ++ bs)
  | _ => pure [p]

partial def splitImplicationsIntoParts (p : Expr) (cutAnd? : Bool := true) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.tla_implies _ p q =>
    let ps ← if cutAnd? then splitAndIntoParts p else pure [p]
    let (ps', q') ← splitImplicationsIntoParts q
    pure (ps ++ ps', q')
  | _ => pure ([], p)

def splitPredImpliesIntoParts (p : Expr) : MetaM (List Expr × Expr) := do
  match_expr p with
  | TLA.pred_implies _ p q =>
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
  | TLA.pred_implies σ _ _ => .some σ
  | TLA.valid σ _ => .some σ
  | _ => .none

end TLA.Expr
