/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Aesop
import Batteries.Tactic.Basic
import LeanPool.Lentil.Basic

open Lean Meta Elab Tactic

namespace TLA

/-- Try to unfold the given identifiers everywhere. -/
syntax "try_unfold_at_all" ident+ : tactic
macro_rules
  | `(tactic| try_unfold_at_all $idt:ident ) => `(tactic| (try unfold $idt at *) )
  | `(tactic| try_unfold_at_all $idt:ident $idts:ident* ) => `(tactic| (try unfold $idt at *); try_unfold_at_all $idts* )

attribute [tlasimp_def] leadsTo weakFairness tlaAnd tlaOr tlaNot tlaImplies tlaForall tlaExists tlaTrue tlaFalse alwaysImplies
  always eventually later tlaUntil statePred purePred actionPred
  valid predImplies exec.satisfies exec.drop_drop
  tlaBigwedge tlaBigvee Foldable.fold

attribute [execsimp] exec.drop Nat.add_zero Nat.zero_add

/-- Unfold TLA definitions in all hypotheses and the goal. -/
macro "tlaUnfold" : tactic => `(tactic| (try dsimp only [tlasimp_def] at *))

/-- Unfold TLA and execution definitions everywhere. -/
macro "tlaUnfold'" : tactic => `(tactic| (tlaUnfold; (try dsimp only [execsimp] at *)))

/-- Unfold TLA definitions and simplify everywhere. -/
macro "tlaUnfoldSimp" : tactic => `(tactic| (simp [tlasimp_def] at *))

/-- Unfold TLA and execution definitions and simplify everywhere. -/
macro "tlaUnfoldSimp'" : tactic => `(tactic| (tlaUnfoldSimp; (try simp only [execsimp] at *)))

attribute [tla_nontemporal_def] tlaAnd tlaOr tlaNot tlaImplies tlaForall tlaExists tlaTrue tlaFalse
  statePred purePred actionPred
  valid predImplies exec.satisfies
  tlaBigwedge tlaBigvee Foldable.fold

/-- Simplify with the non-temporal TLA lemmas everywhere. -/
macro "tlaNontemporalSimp" : tactic => `(tactic| (simp [tla_nontemporal_def] at *))

/-- Normalize a sequent goal into a validity goal, by definitional equality. -/
def changePredImpliesToValid : TacticM Unit := withMainContext do
  let target ← getMainTarget
  match_expr target.headBeta.cleanupAnnotations with
  | TLA.predImplies _ p q =>
    let imp ← mkAppM ``TLA.tlaImplies #[p, q]
    let target' ← mkAppM ``TLA.valid #[imp]
    let goal ← getMainGoal
    replaceMainGoal [← goal.change target']
  | _ =>
    pure ()

end TLA
