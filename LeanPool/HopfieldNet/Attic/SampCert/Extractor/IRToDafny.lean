/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Lean
import LeanPool.HopfieldNet.SampCert.Extractor.IR
import LeanPool.HopfieldNet.SampCert.Extractor.Dafny
import LeanPool.HopfieldNet.SampCert.Extractor.Extension

namespace Lean.ToDafny

def compileReturn (e : Expression) : MetaM Expression := do
  match e with
  | .pure e => return .letb "o" e (.pure (.name "o"))
  | _ => return e

def compileBind (e : Expression) : MetaM Expression := do
  match e with
  | .bind rhs (.lam v body) => return .letb v rhs body
  | .bind .. => throwError "WF violation: second argument of a bind must be a lambda"
  | e => return e

def compileProbUntil (e : Expression) : MetaM Expression := do
  match e with
  | .prob_until body (.lam n cond) => return .prob_while (.lam n (.unop .negation cond)) body body
  | e => return e

def subst (param : String) (arg : Expression) (e : Expression) : MetaM Expression := do
  match e with
  | .name n => if n = param then return arg else return e
  | .letb n rhs body =>
    if n = param ∧ n = "o"
    then if let .name st := arg
         then return .letb st rhs body
         else throwError ""
    else return e
  | _=> return e

def inline (e : Expression) : MetaM Expression := do
  match e with
  | .letb binder (.prob_while (.lam state cond) (.monadic callee args) init) body =>
    let st : State := extension.getState (← getEnv)
    if callee ∈ st.inlines
    then
      if let some defn := st.glob.find? callee
      then
        let body' ← defn.body.map (subst "o" (.name state))
        let pas := List.zip defn.inParam args
        let body'' ← pas.foldlM (λ bo => λ (param,arg) => bo.map (subst param arg)) body'
        return .letb binder (.prob_while (.lam state cond) body'' init) body
      else throwError "Definition is in list of inlines but not exported"
    else return e
  | _ => return e

partial def Expression.toStatements (e : Expression) : MetaM (List Statement) := do
  match e with
  | tr => throwError "toStatements: unexpected expression tr {e}"
  | fa => throwError "toStatements: unexpected expression fa {e}"
  | num .. => throwError "toStatements: unexpected expression num {e}"
  | str .. => throwError "toStatements: unexpected expression str {e}"
  | letb binder rhs (pure (name _)) => return [.assignment binder rhs]
  | pure .. => throwError "invariant violation: pure should appear in simple bind"
  | letb v (.prob_while (.lam state cond) rcomp init) body =>
    let s_tmp : Expression := (.prob_while (.lam state cond) rcomp init)
    let s1 : List Statement ← s_tmp.toStatements
    let s2 : Statement := .vardecl v (.name state)
    let s3 : List Statement ← body.toStatements
    return s1 ++ [s2] ++ s3
  | letb v rhs body => return ((.vardecl v rhs) :: (← body.toStatements))
  | ite cond (.throw msg) right =>
    let s1 : Statement := .expect cond msg
    return s1 :: (← right.toStatements)
  | ite cond left right => return [.conditional cond (← left.toStatements) (← right.toStatements)]
  | bind .. => throwError "toStatements: to do {e}"
  | lam .. => throwError "toStatements: unexpected expression lam {e}"
  | throw .. => throwError "WF: throw must appear immediately as the left side of a conditional"
  | prob_until .. => throwError "invariant violation: prob_until should have been compiled away"
  -- Brittle: it turns out that it is important to know if we're dealing
  -- with a while or an until to determine if we need to pass the state
  | prob_while (.lam state cond) (.monadic callee args) init =>
    let s1 : Statement := .vardecl state init
    let st : State := extension.getState (← getEnv)
    if let some defn := st.glob.find? callee
      then let args := if List.length args = List.length defn.inParam then args else args ++ [.name state]
           let s3 : Statement := .loop cond ([.assignment state (.monadic callee args)])
           return [s1] ++ [s3]
    else let s3 : Statement := .loop cond ([.assignment state (.monadic callee args)])
         return [s1] ++ [s3]
  | prob_while (.lam state cond) body init =>
    let s1 : Statement := .vardecl state init
    let s2 : List Statement ← body.toStatements
    -- condition needs to be substituted
    let s3 : Statement := .loop cond s2
    return [s1] ++ [s3]
  | prob_while .. => throwError "toStatements: to do {e}"
  | name .. => throwError "toStatements: unexpected expression name {e}"
  | unop .. => throwError "toStatements: unexpected expression unop {e}"
  | binop .. => throwError "toStatements: unexpected expression binop {e}"
  | proj .. => throwError "toStatements: unexpected expression proj {e}"
  | pair .. => throwError "toStatements: unexpected expression pair {e}"
  | monadic .. => throwError "toStatements: unexpected expression monadic {e}"

def Expression.pipeline (body : Expression) : MetaM Expression := do
  --IO.println body.print
  let body1 ← body.map compileBind
  --IO.println body1.print
  let body2 ← body1.map compileReturn
  --IO.println body2.print
  let body3 ← body2.map compileProbUntil
  --IO.println body3.print
  let body4 ← body3.map inline
  --IO.println body4.print
  return body4

def CodeGen (pi : MDef) : MetaM Method := do
  let body' ← pi.body.pipeline
  modifyEnv fun env => extension.addEntry env (.addFunc pi.name { pi with body := body' })
  return {
    name := pi.name,
    inParamType := pi.inParamType,
    outParamType := pi.outParamType,
    inParam := pi.inParam,
    body := ← body'.toStatements
  }

end Lean.ToDafny
