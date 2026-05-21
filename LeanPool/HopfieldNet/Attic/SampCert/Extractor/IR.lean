/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Lean

namespace Lean.ToDafny

inductive UnOp where
  | negation
  | minus
  | numerator
  | denominator
  | abs
  deriving DecidableEq

inductive BinOp where
  | equality
  | inequality
  | equivalence
  | least
  | leastequal
  | greater
  | greaterequal
  | conjunction
  | disjunction
  | implication
  | addition
  | substraction
  | multiplication
  | division
  | log
  | pow
  | mod
  deriving DecidableEq

mutual

inductive Typ where
  | bool
  | int
  | nat
  | pos
  | prod (left right : Typ)
  | dependent (e : Expression)

inductive Expression where
  | tr
  | fa
  | num (val : Nat)
  | str (s : String)
  | letb (v : String) (rhs : Expression) (body : Expression)
  | ite (cond left right : Expression)
  | bind (rhs : Expression) (rhs : Expression)
  | lam (v : String) (body : Expression)
  | pure (e : Expression)
  | throw (e : Expression)
  | prob_until (body cond : Expression)
  | prob_while (cond body init : Expression)
  | name (s: String)
  | unop (op : UnOp) (rhs : Expression)
  | binop (op : BinOp) (lhs rhs : Expression)
  | proj (name : Expression) (idx : Nat)
  | pair (left right : Expression)
  | monadic (name : String) (arg : List Expression)

end

structure MDef where
  name : String
  inParamType : List Typ
  outParamType : Typ
  inParam : List String
  body : Expression

def join (s : List String) : String :=
  match s with
  | [] => ""
  | [a] => a
  | a::as => a ++ ", " ++ join as

def Typ.print (t : Typ): String :=
  match t with
  | bool => "bool"
  | int => "int"
  | nat => "nat"
  | pos => "pos"
  | prod t1 t2 => s!"({t1.print},{t2.print})"
  | dependent _ => "dependent"

def UnOp.print (o : UnOp) : String :=
  match o with
  | negation => "!"
  | minus => "-"
  | numerator => "numerator"
  | denominator => "denominator"
  | abs => "abs"

def BinOp.print (o : BinOp) : String :=
  match o with
  | equality => "=="
  | inequality => "!="
  | equivalence => "<==>"
  | least => "<"
  | leastequal => "<="
  | greater => ">"
  | greaterequal => ">="
  | conjunction => "&&"
  | disjunction => "||"
  | implication => "==>"
  | addition => "+"
  | substraction => "-"
  | multiplication => "*"
  | division => "/"
  | log => "log"
  | pow => "pow"
  | mod => "%"

partial def Expression.print (e : Expression) : String :=
  match e with
  | tr => "true"
  | fa => "false"
  | num val => toString val
  | str s => s!"\"{s}\""
  | letb v rhs body => s!"let {v} := {rhs.print} in {body.print}"
  | ite cond left right => s!"if {cond.print} then {left.print} else {right.print}"
  | bind v body => s!"bind [{v.print}] ← [{body.print}]"
  | lam v body => s!"fun {v} => {body.print}"
  | pure e => s!"return {e.print}"
  | throw e => s!"throw {e.print}"
  | prob_until body cond => s!"prob_until {body.print} {cond.print}"
  | prob_while cond body init => s!"prob_while ({cond.print}) ({body.print}) ({init.print})"
  | name n => n
  | unop .abs e => s!"(if {e.print} < 0 then -({e.print}) else ({e.print}))"
  | unop .numerator rhs => s!"{rhs.print}.numerator"
  | unop .denominator rhs => s!"{rhs.print}.denominator"
  | unop op rhs => s!"{op.print} ({rhs.print})"
  | binop .pow lhs (.num 2) => s!"({lhs.print}) * ({lhs.print})"
  | binop op lhs rhs => s!"{lhs.print} {op.print} {rhs.print}"
  | proj id idx => s!"{id.print}.{idx-1}"
  | pair left right => s!"({left.print},{right.print})"
  | monadic n e => s!"{n}({join (e.map (·.print))})"

instance : ToString Expression where
  toString := Expression.print

def printArgs (names : List String) (types : List Typ) : String :=
  match names, types with
  | [], [] => ""
  | name :: [], typ :: [] => s!"{name}: {typ.print}"
  | name :: names, typ :: types =>
    let res : String := printArgs names types
    s!"{name}: {typ.print}, " ++ res
  | _, _ => "printArgs: list of names and types mismatch"

def printRequires (types : List Typ) (indent : String) : String :=
  match types with
  | [] => ""
  | .dependent e :: types =>
    indent ++ s!"requires {e} \n" ++
    printRequires types indent
  | _ => "printRequires: list of requires contains a non-dependent type"

def MDef.print (m : MDef) : String :=
  s!"method {m.name}({printArgs m.inParam m.inParamType}) : returns ({m.outParamType.print}) \n {m.body.print} \n "

partial def Expression.map (transform : Expression → MetaM Expression) (e : Expression) : MetaM Expression := do
  match e with
  | tr =>
    transform $ .tr
  | fa =>
    transform $ .fa
  | num val =>
    transform $ .num val
  | str s =>
    transform $ .str s
  | letb v rhs body =>
    let rhs' ← rhs.map transform
    let body' ← body.map transform
    transform $ .letb v rhs' body'
  | ite cond left right =>
    let cond' ← cond.map transform
    let left' ← left.map transform
    let right' ← right.map transform
    transform $ .ite cond' left' right'
  | bind v body =>
    let v' ← v.map transform
    let body' ← body.map transform
    transform $ .bind v' body'
  | lam v body =>
    let body' ← body.map transform
    transform $ .lam v body'
  | pure e =>
    let e' ← e.map transform
    transform $ .pure e'
  | throw e =>
    let e' ← e.map transform
    transform $ .throw e'
  | prob_until body cond =>
    let body' ← body.map transform
    let cond' ← cond.map transform
    transform $ .prob_until body' cond'
  | prob_while cond body init =>
    let cond' ← cond.map transform
    let body' ← body.map transform
    let init' ← init.map transform
    transform $ .prob_while cond' body' init'
  | name s =>
    transform $ .name s
  | unop op rhs =>
    let rhs' ← rhs.map transform
    transform $ .unop op rhs'
  | binop op lhs rhs =>
    let lhs' ← lhs.map transform
    let rhs' ← rhs.map transform
    transform $ .binop op lhs' rhs'
  | proj id idx =>
    let id' ← id.map transform
    transform $ .proj id' idx
  | pair left right =>
    let left' ← left.map transform
    let right' ← right.map transform
    transform $ .pair left' right'
  | monadic n e =>
    let e' ← e.mapM (map transform)
    transform $ .monadic n e'

end Lean.ToDafny
