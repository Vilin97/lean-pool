/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

open Lean

namespace TLA.ProofMode

/-- Display syntax for a single proof-mode hypothesis. -/
syntax tlaPmHyp := ident " : " tlafml
/-- Display syntax for a proof-mode entailment. -/
syntax tlaPmEntails := ppDedent(ppLine tlaPmHyp)* ppDedent(ppLine "|-tla- " tlafml)

open PrettyPrinter.Delaborator SubExpr

/-- Delaborate the name component of a `NamedPred`. -/
def delabNameInNamedPred : DelabM Ident := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  let some s := parseStringLitOpt e | failure
  pure <| mkIdent <| Name.mkSimple s

/-- Delaborate a `NamedPred` into a displayed hypothesis. -/
def delabNamedPred : DelabM (TSyntax ``tlaPmHyp) := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  unless e.isAppOfArity' ``TLA.ProofMode.NamedPred.mk 3 do
    failure
  let fml ← withAppArg TLA.delabTlafmlInner
  let nm ← withAppFn <| withAppArg delabNameInNamedPred
  `(tlaPmHyp| $nm:ident : $fml:tlafml)

/-- Delaborate a `List (NamedPred σ)` expression into a list of proof-mode
    hypotheses. `fuel` bounds the list length and each recursive call drops one
    `List.cons`, so the expression's depth always suffices. -/
def delabNamedPredListAux (fuel : Nat) : DelabM (List (TSyntax ``tlaPmHyp)) := do
  let e ← getExpr
  if e.isAppOfArity' ``List.nil 1 then
    return []
  match fuel with
  | 0 => failure
  | fuel + 1 =>
    if e.isAppOfArity' ``List.cons 3 then
      -- List.cons {α} head tail   →  args 0,1,2
      let head ← withAppFn <| withAppArg delabNamedPred
      let tail ← withAppArg (delabNamedPredListAux fuel)
      return head :: tail
    failure

/-- Delaborate a `List (NamedPred σ)` expression into a list of proof-mode
    hypotheses, seeding the fuel from the expression's approximate depth. -/
def delabNamedPredList : DelabM (List (TSyntax ``tlaPmHyp)) := do
  delabNamedPredListAux ((← getExpr).approxDepth.toNat + 1)

/-- Delaborator for `Entails` goals, rendering them in proof-mode layout. -/
def delabEntails : Delab := do
  let e ← getExpr
  unless e.isAppOfArity' ``TLA.ProofMode.Entails 3 do failure
  -- Entails {σ} hyps goal   →  args 0,1,2
  let hyps ← withAppFn <| withAppArg delabNamedPredList
  let hyps := hyps.toArray
  let goal ← withAppArg TLA.delabTlafmlInner
  let q ← `(tlaPmEntails| $hyps:tlaPmHyp* |-tla- $goal:tlafml)
  -- NOTE: This is a hack, but making `tlaPmEntails` a `term` might again introduce some
  -- weird parsing errors, so just "pretend" the result is a `term` and display it
  pure ⟨q⟩

attribute [delab app.TLA.ProofMode.Entails] delabEntails

end TLA.ProofMode
