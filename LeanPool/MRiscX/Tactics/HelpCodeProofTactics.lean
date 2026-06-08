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
elab "simp_currInstr" : tactic => do
  evalTactic (← `(tactic| try simp))
  evalTactic (← `(tactic| rw [($(mkIdent `h_code')), ($(mkIdent `h_pc))]))
  evalTactic (← `(tactic| simp [t_update_neq, t_update_eq]))

/- Tries to solve goals where `(pmap).get r = some label`.-/
elab "simp_t_update" : tactic => do
  evalTactic (← `( tactic | repeat (first | rw [t_update_eq] | rw [t_update_neq]
                            <;> try (apply Ne.symm; try assumption))
                            <;> try assumption))
  evalTactic (← `(tactic | repeat first
                          | constructor
                          | assumption))


/- This tactic prpares the second proofgoal after applying S_SEQ. It introduces the
parameters and unfolds `hoare_triple_up`-/
elab "prepare_second_seq": tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `l') $(mkIdent `h_l') ))
  evalTactic (← `(tactic | rw [($(mkIdent `h_l'))] ))
  evalTactic (← `(tactic | unfold hoare_triple_up))
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s) $(mkIdent `h_code') $(mkIdent `h_pc) ))
  evalTactic (← `(tactic | rw [←($(mkIdent `h_code'))] ))


/- To be able to split conjunction and disjunction in hypothesis, the next two functions are
required. Those functions are from Lean.Elab.Tactic.RCases -/
def RCasesPatt.alts' (ref : Syntax) : List/-Σ-/ RCasesPatt →RCasesPatt
  | [p] => p
  | ps  => RCasesPatt.alts ref ps

/-- Parses a `Syntax` into the `RCasesPatt` type used by the `RCases` tactic. -/
def RCasesPatt.parse (stx : Syntax) : MetaM RCasesPatt :=
  match stx with
  | `(rcasesPatMed| $ps:rcasesPat|*) =>
    return RCasesPatt.alts' stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPatLo| $pat:rcasesPatMed : $t:term) => return .typed stx (← parse pat) t
  | `(rcasesPatLo| $pat:rcasesPatMed) => parse pat
  | `(rcasesPat| _) => return .one stx `_
  | `(rcasesPat| $h:ident) => return .one h h.getId
  | `(rcasesPat| -) => return .clear stx
  | `(rcasesPat| @$pat) => return .explicit stx (← parse pat)
  | `(rcasesPat| ⟨$ps,*⟩) => return .tuple stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPat| ($pat)) => return .paren stx (← parse pat)
  | _ => throwUnsupportedSyntax





/- a tactic which puts conjunction and disjunction in a precondition into its parts. -/
elab "split_condis" &" in " h:ident : tactic => do
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
      Lean.Meta.throwTacticEx `split_condis goal
        (m!"failure")
