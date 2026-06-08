/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/

import Lean
import LeanPool.MRiscX.Elab.HandleExpr
import LeanPool.MRiscX.Hoare.HoareCore

/-!
# HelpCodeProofTactics

This module provides auxiliary helpers for the MRiscX code-proof tactics.
-/

open Lean Elab Parser Tactic RCases



/--
Tries to solve a `s.currInstr = instr` goal. Requires the s.cdoe and s.pc being introduced
as `h_code'` and `h_pc` respectively as hypothesis
-/
elab "simpCurrInstr" : tactic => do
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| rw [($(mkIdent `h_code')), ($(mkIdent `h_pc))]))
  evalTactic (← `(tactic| simp [t_update_neq, t_update_eq]))

/- Tries to solve goals where `(pmap).get r = some label`.-/
/-- Simplify total-map updates appearing in the goal. -/
elab "simpTUpdate" : tactic => do
  evalTactic (← `( tactic | repeat (first | rw [t_update_eq] | rw [t_update_neq]
                            <;> try (apply Ne.symm; try assumption))
                            <;> try assumption))
  evalTactic (← `(tactic | repeat first
                          | constructor
                          | assumption))


/- This tactic prpares the second proofgoal after applying S_SEQ. It introduces the
parameters and unfolds `hoareTripleUp`-/
/-- Prepare the goal for the second branch of a sequencing proof. -/
elab "prepareSecondSeq": tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `l') $(mkIdent `h_l') ))
  evalTactic (← `(tactic | rw [($(mkIdent `h_l'))] ))
  evalTactic (← `(tactic | unfold hoareTripleUp))
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s)
    $(mkIdent `h_code') $(mkIdent `h_pc) ))
  evalTactic (← `(tactic | rw [←($(mkIdent `h_code'))] ))


/-- Collapse a list of `rcases` alternatives into a single pattern, using the lone
pattern directly when there is exactly one. Adapted from `Lean.Elab.Tactic.RCases`. -/
def RCasesPatt.alts' (ref : Syntax) : List/-Σ-/ RCasesPatt →RCasesPatt
  | [p] => p
  | ps  => RCasesPatt.alts ref ps

/-- The total number of nodes in a syntax tree, an upper bound on its depth. -/
private def patternSyntaxSize : Syntax → Nat
  | .node _ _ args => 1 + args.foldl (fun acc s => acc + patternSyntaxSize s) 0
  | _ => 1

/-- Fuel-bounded core of `RCasesPatt.parse`; `fuel` bounds the recursion. -/
private def RCasesPatt.parseAux (fuel : Nat) (stx : Syntax) : MetaM RCasesPatt :=
  match fuel with
  | 0 => throwUnsupportedSyntax
  | fuel + 1 =>
    match stx with
    | `(rcasesPatMed| $ps:rcasesPat|*) =>
      return RCasesPatt.alts' stx (← ps.getElems.toList.mapM (parseAux fuel ·.raw))
    | `(rcasesPatLo| $pat:rcasesPatMed : $t:term) => return .typed stx (← parseAux fuel pat) t
    | `(rcasesPatLo| $pat:rcasesPatMed) => parseAux fuel pat
    | `(rcasesPat| _) => return .one stx `_
    | `(rcasesPat| $h:ident) => return .one h h.getId
    | `(rcasesPat| -) => return .clear stx
    | `(rcasesPat| @$pat) => return .explicit stx (← parseAux fuel pat)
    | `(rcasesPat| ⟨$ps,*⟩) => return .tuple stx (← ps.getElems.toList.mapM (parseAux fuel ·.raw))
    | `(rcasesPat| ($pat)) => return .paren stx (← parseAux fuel pat)
    | _ => throwUnsupportedSyntax

/-- Parses a `Syntax` into the `RCasesPatt` type used by the `RCases` tactic. -/
def RCasesPatt.parse (stx : Syntax) : MetaM RCasesPatt :=
  RCasesPatt.parseAux (patternSyntaxSize stx) stx





/- a tactic which puts conjunction and disjunction in a precondition into its parts. -/
/-- Split the conjunctions and disjunctions in the given hypothesis. -/
elab "splitCondis" &" in " h:ident : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      if decl.userName == h.getId then
        let type := decl.type
        let pat ← splitConjDisj type
        let pat' ← RCasesPatt.parse pat
        return some pat'
      return none
    match option_matching_expr with
    | some e =>
      let tgts : Array (Option Ident × Syntax) := #[(none, h)]
      let g ← getMainGoal
      g.withContext do replaceMainGoal (← RCases.rcases tgts e g)
    | none =>
      Lean.Meta.throwTacticEx `splitCondis goal
        (m!"failure")
