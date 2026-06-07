/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Basic

open Lean

namespace TLA.ProofMode

syntax tlaPmHyp := ident " : " tlafml
syntax tlaPmEntails := ppDedent(ppLine tlaPmHyp)* ppDedent(ppLine "|-tla- " tlafml)

open PrettyPrinter.Delaborator SubExpr

def delabNameInNamedPred : DelabM Ident := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  let some s := parseStringLit? e | failure
  pure <| mkIdent <| Name.mkSimple s

def delabNamedPred : DelabM (TSyntax ``tlaPmHyp) := do -- whenPPOption (fun o => o.get lentil.pp.useDelab.name true) do
  let e ← getExpr
  unless e.isAppOfArity' ``TLA.ProofMode.NamedPred.mk 3 do
    failure
  let fml ← withAppArg delab_tlafml_inner
  let nm ← withAppFn <| withAppArg delabNameInNamedPred
  `(tlaPmHyp| $nm:ident : $fml:tlafml)

partial def delabNamedPredList : DelabM (List (TSyntax ``tlaPmHyp)) := do
  let e ← getExpr
  if e.isAppOfArity' ``List.nil 1 then
    return []
  if e.isAppOfArity' ``List.cons 3 then
    -- List.cons {α} head tail   →  args 0,1,2
    let head ← withAppFn <| withAppArg delabNamedPred
    let tail ← withAppArg delabNamedPredList
    return head :: tail
  failure

def delabEntails : Delab := do
  let e ← getExpr
  unless e.isAppOfArity' ``TLA.ProofMode.Entails 3 do failure
  -- Entails {σ} hyps goal   →  args 0,1,2
  let hyps ← withAppFn <| withAppArg delabNamedPredList
  let hyps := hyps.toArray
  let goal ← withAppArg delab_tlafml_inner
  let q ← `(tlaPmEntails| $hyps:tlaPmHyp* |-tla- $goal:tlafml)
  -- NOTE: This is a hack, but making `tlaPmEntails` a `term` might again introduce some
  -- weird parsing errors, so just "pretend" the result is a `term` and display it
  pure ⟨q⟩

attribute [delab app.TLA.ProofMode.Entails] delabEntails

end TLA.ProofMode
