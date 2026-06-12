/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import Mathlib.Tactic.Common

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta

Auxiliary declarations for the Borel determinacy formalization.
-/


/-- Auxiliary declaration for the Borel determinacy formalization. -/
register_simp_attr simp_lengths --seemingly not usable in file where declared
/-- Auxiliary declaration for the Borel determinacy formalization. -/
register_simp_attr simp_fixing
/-- Auxiliary declaration for the Borel determinacy formalization. -/
register_simp_attr simp_isPosition

open Lean Meta Elab Tactic Term

section «simpAtStar»
--modify getNondepPropHyps
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Lean.MVarId.getPropHyps (mvarId : MVarId) : MetaM (Array FVarId) := do
  mvarId.withContext do
  let mut result := #[]
  for ldecl in ← getLCtx do
    if !ldecl.isImplementationDetail && (← isProp ldecl.type) && !ldecl.hasValue then
      result := result.push ldecl.fvarId
  return result
--modify simpLocation
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def simpLocationAtStar (ctx : Simp.Context)
  (simprocs : Simp.SimprocsArray)
  (discharge? : Option Simp.Discharge := none) :
  Tactic.TacticM Simp.Stats := do
    Tactic.withMainContext do
      go (← (← Tactic.getMainGoal).getPropHyps) (simplifyTarget := true)
where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  go (fvarIdsToSimp : Array FVarId) (simplifyTarget : Bool) :
    TacticM Simp.Stats := do
    let mvarId ← getMainGoal
    let (result?, stats) ← simpGoal mvarId ctx (simprocs := simprocs)
      (simplifyTarget := simplifyTarget) (discharge? := discharge?) (fvarIdsToSimp := fvarIdsToSimp)
    match result? with
    | none => replaceMainGoal []
    | some (_, mvarId) => replaceMainGoal [mvarId]
    return stats
--variant of simp at * that also simplifies dependent hypotheses
/-- Tactic support used by the Borel determinacy formalization. -/
syntax (name := simpAtStar) "simpAtStar" (Parser.Tactic.config)?
  (Parser.Tactic.discharger)? (&" only")?
  (" [" withoutPosition((Parser.Tactic.simpStar
    <|> Lean.Parser.Tactic.simpErase <|> Parser.Tactic.simpLemma),*,?) "]")? : tactic
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[tactic simpAtStar] def evalSimpAtStar : Tactic :=
  fun stx => withMainContext do withSimpDiagnostics do
  let { ctx, simprocs, dischargeWrapper, .. } ←
    mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocationAtStar ctx simprocs discharge?
  return stats.diag
end «simpAtStar»
