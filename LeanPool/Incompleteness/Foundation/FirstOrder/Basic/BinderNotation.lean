/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Operator

/-! # BinderNotation -/


open Lean PrettyPrinter Delaborator SubExpr

namespace LO
namespace FirstOrder

namespace BinderNotation

/-- Imported declaration from the Incompleteness formalization. -/
abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ

open Semiterm Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
declare_syntax_cat firstOrderTerm

/-- Imported declaration from the Incompleteness formalization. -/
syntax "foTerm[" ident* " | " ident* " | " firstOrderTerm:0 "]" : term

/-- Imported declaration from the Incompleteness formalization. -/
syntax "(" firstOrderTerm ")" : firstOrderTerm

/-- Imported declaration from the Incompleteness formalization. -/
syntax:max ident : firstOrderTerm         -- bounded variable
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "#" term:max : firstOrderTerm  -- bounded variable
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "&" term:max : firstOrderTerm  -- free variable
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 "!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 "!!" term:max : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 ".!" term:max firstOrderTerm:81* (" ⋯")? : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:80 ".!!" term:max : firstOrderTerm

/-- Imported declaration from the Incompleteness formalization. -/
syntax num : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "↑" term:max : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋆" : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:50 firstOrderTerm:50 " + " firstOrderTerm:51 : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 firstOrderTerm:60 " * " firstOrderTerm:61 : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:65 firstOrderTerm:65 " ^ " firstOrderTerm:66 : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:70 firstOrderTerm " ^' " num  : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "²"  : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "³"  : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max firstOrderTerm "⁴"  : firstOrderTerm
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⌜" term:max "⌝" : firstOrderTerm

/-- Imported declaration from the Incompleteness formalization. -/
syntax:67  "exp " firstOrderTerm:68 : firstOrderTerm

macro_rules
  | `(foTerm[ $binders* | $fbinders* | ($e)    ]) => `(foTerm[ $binders* | $fbinders* | $e ])
  | `(foTerm[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(foTerm[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(foTerm[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(foTerm[ $_*       | $_*        | $m:num     ]) => `(Semiterm.numeral $m)
  | `(foTerm[ $_*       | $_*        | ↑$m:term   ]) => `(Semiterm.numeral $m)
  | `(foTerm[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(foTerm[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(foTerm[ $binders* | $fbinders* | $e₁ + $e₂  ]) =>
    `(Semiterm.Operator.Add.add.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e₁ * $e₂  ]) =>
    `(Semiterm.Operator.Mul.mul.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) =>
    `(Semiterm.Operator.Pow.pow.operator ![
      foTerm[ $binders* | $fbinders* | $e₁ ],
      foTerm[ $binders* | $fbinders* | $e₂ ]])
  | `(foTerm[ $binders* | $fbinders* | $e ^' $n   ]) =>
    `((Semiterm.Operator.npow _ $n).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e²        ]) =>
    `((Semiterm.Operator.npow _ 2).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e³        ]) =>
    `((Semiterm.Operator.npow _ 3).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | $e⁴        ]) =>
    `((Semiterm.Operator.npow _ 4).operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $binders* | $fbinders* | exp $e     ]) =>
    `(Semiterm.Operator.Exp.exp.operator ![foTerm[ $binders* | $fbinders* | $e ]])
  | `(foTerm[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(foTerm[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)
  | `(foTerm[ $binders* | $fbinders* | !$t:term $vs:firstOrderTerm* ])    => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
      (fun a s => `(foTerm[ $binders* | $fbinders* | $a ] :> $s))
    `(Rew.substs $v $t)
  | `(foTerm[ $binders* | $fbinders* | !$t:term $vs:firstOrderTerm* ⋯ ])  =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _)
      (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.substs $v $t)
  | `(foTerm[ $binders* | $fbinders* | .!$t:term $vs:firstOrderTerm* ])   => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![]))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(foTerm[ $binders* | $fbinders* | .!$t:term $vs:firstOrderTerm* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _)
      (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)

/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" firstOrderTerm:0 "’" : term
/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" ident* "| " firstOrderTerm:0 "’" : term
/-- Imported declaration from the Incompleteness formalization. -/
syntax "‘" ident* ". " firstOrderTerm:0 "’" : term

macro_rules
  | `(‘ $e:firstOrderTerm ’)              => `(foTerm[           |            | $e ])
  | `(‘ $fbinders* | $e:firstOrderTerm ’) => `(foTerm[           | $fbinders* | $e ])
  | `(‘ $binders*. $e:firstOrderTerm ’)   => `(foTerm[ $binders* |            | $e ])

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.numeral]
def unexpsnderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.const]
def unexpsnderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.Add.add]
def unexpsnderAdd : Unexpander
  | `($_) => `(op(+))

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.Mul.mul]
def unexpsnderMul : Unexpander
  | `($_) => `(op(*))

/-


-/

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.Operator.operator]
def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     + $u    )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     + #$x   )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     + &$x   )’)
  | `($_ op(+) ![‘$t:firstOrderTerm’,   $u                      ]) => `(‘($t     + !!$u  )’)
  | `($_ op(+) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    + $u    )’)
  | `($_ op(+) ![#$x,                     #$y                     ]) => `(‘(#$x    + #$y   )’)
  | `($_ op(+) ![#$x,                     &$y                     ]) => `(‘(#$x    + &$y   )’)
  | `($_ op(+) ![#$x,                     $u                      ]) => `(‘(#$x    + !!$u  )’)
  | `($_ op(+) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    + $u    )’)
  | `($_ op(+) ![&$x,                     #$y                     ]) => `(‘(&$x    + #$y   )’)
  | `($_ op(+) ![&$x,                     &$y                     ]) => `(‘(&$x    + &$y   )’)
  | `($_ op(+) ![&$x,                     $u                      ]) => `(‘(&$x    + !!$u  )’)
  | `($_ op(+) ![$t,                      ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   + $u    )’)
  | `($_ op(+) ![$t,                      #$y                     ]) => `(‘(!!$t   + #$y   )’)
  | `($_ op(+) ![$t,                      &$y                     ]) => `(‘(!!$t   + &$y   )’)
  | `($_ op(+) ![$t,                      $u                      ]) => `(‘(!!$t   + !!$u  )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   ‘$u:firstOrderTerm’   ]) => `(‘($t     * $u    )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   #$x                     ]) => `(‘($t     * #$x   )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   &$x                     ]) => `(‘($t     * &$x   )’)
  | `($_ op(*) ![‘$t:firstOrderTerm’,   $u                      ]) => `(‘($t     * !!$u  )’)
  | `($_ op(*) ![#$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(#$x    * $u    )’)
  | `($_ op(*) ![#$x,                     #$y                     ]) => `(‘(#$x    * #$y   )’)
  | `($_ op(*) ![#$x,                     &$y                     ]) => `(‘(#$x    * &$y   )’)
  | `($_ op(*) ![#$x,                     $u                      ]) => `(‘(#$x    * !!$u  )’)
  | `($_ op(*) ![&$x,                     ‘$u:firstOrderTerm’   ]) => `(‘(&$x    * $u    )’)
  | `($_ op(*) ![&$x,                     #$y                     ]) => `(‘(&$x    * #$y   )’)
  | `($_ op(*) ![&$x,                     &$y                     ]) => `(‘(&$x    * &$y   )’)
  | `($_ op(*) ![&$x,                     $u                      ]) => `(‘(&$x    * !!$u  )’)
  | `($_ op(*) ![$t,                      ‘$u:firstOrderTerm’   ]) => `(‘(!!$t   * $u    )’)
  | `($_ op(*) ![$t,                      #$y                     ]) => `(‘(!!$t   * #$y   )’)
  | `($_ op(*) ![$t,                      &$y                     ]) => `(‘(!!$t   * &$y   )’)
  | `($_ op(*) ![$t,                      $u                      ]) => `(‘(!!$t   * !!$u  )’)
  | _                             => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiterm.numeral]
def unexpandNumeral : Unexpander
  | `($_ $n:num) => `(‘$n:num’)
  | _            => throw ()

end «lp_section_1»

open Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
declare_syntax_cat firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax "foFormula[" ident* " | " ident* " | " firstOrderFormula:0 "]" : term

/-- Imported declaration from the Incompleteness formalization. -/
syntax "(" firstOrderFormula ")" : firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 "!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 "!!" term:max : firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 ".!" term:max firstOrderTerm:61* ("⋯")? : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:60 ".!!" term:max : firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax "⊤" : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax "⊥" : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:32 firstOrderFormula:33 " ∧ " firstOrderFormula:32 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:30 firstOrderFormula:31 " ∨ " firstOrderFormula:30 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "¬" firstOrderFormula:35 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:10 firstOrderFormula:9 " → " firstOrderFormula:10 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:5 firstOrderFormula " ↔ " firstOrderFormula : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋀ " ident ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋁ " ident ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋀ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "⋁ " ident " < " term ", " firstOrderFormula:0 : firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident+ ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident+ ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀' " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃' " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃[" firstOrderFormula "] " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(foFormula[ $binders* | $fbinders* | ($e:firstOrderFormula)          ]) =>
    `(foFormula[ $binders* | $fbinders* | $e ])
  | `(foFormula[ $_*       | $_*        | !!$φ:term                         ]) => `($φ)
  | `(foFormula[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm*    ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s =>
      `(foTerm[ $binders* | $fbinders* | $a ] :> $s))
    `($φ <~ $v)
  | `(foFormula[ $binders* | $fbinders* | !$φ:term $vs:firstOrderTerm* ⋯  ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s
      ↦ `(foTerm[ $binders* | $fbinders* | $a] :> $s))
    `($φ <~ $v)
  | `(foFormula[ $_*       | $_*        | .!!$φ:term ])                        =>
    `(Rewriting.embedding $φ)
  | `(foFormula[ $_*       | $_*        | ⊤                                 ]) => `(⊤)
  | `(foFormula[ $_*       | $_*        | ⊥                                 ]) => `(⊥)
  | `(foFormula[ $binders* | $fbinders* | $φ ∧ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ⋏ foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | $φ ∨ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ⋎ foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ¬$φ                               ]) =>
    `(∼foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | $φ → $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] ==> foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | $φ ↔ $ψ                           ]) =>
    `(foFormula[ $binders* | $fbinders* | $φ ] <=> foFormula[ $binders* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ⋀ $i, $φ                          ]) =>
    `(Matrix.conjVec fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ⋁ $i, $φ                          ]) =>
    `(Matrix.disj fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ⋀ $i < $t, $φ                     ]) =>
    `(conjLt (fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ]) $t)
  | `(foFormula[ $binders* | $fbinders* | ⋁ $i < $t, $φ                     ]) =>
    `(disjLt (fun $i ↦ foFormula[ $binders* | $fbinders* | $φ ]) $t)
  | `(foFormula[ $binders* | $fbinders* | ∀ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(foFormula[ $binders'* | $fbinders* | $φ ])
      (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀' $ψ))
    return s
  | `(foFormula[ $binders* | $fbinders* | ∃ $xs*, $φ                        ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(foFormula[ $binders'* | $fbinders* | $φ ])
      (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃' $ψ))
    return s
  | `(foFormula[ $binders* | $fbinders* | ∀' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀' foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∃' $φ ])                            => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃' foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∀[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀[foFormula[ $binders'* | $fbinders* | $φ ]] foFormula[ $binders'* | $fbinders* | $ψ ])
  | `(foFormula[ $binders* | $fbinders* | ∃[ $φ ] $ψ ])                       => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃[foFormula[ $binders'* | $fbinders* | $φ ]] foFormula[ $binders'* | $fbinders* | $ψ ])

/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" ident* "| "  firstOrderFormula:0 "”" : term
/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" ident* ". "  firstOrderFormula:0 "”" : term
/-- Imported declaration from the Incompleteness formalization. -/
syntax "“" firstOrderFormula:0 "”" : term

macro_rules
  | `(“ $e:firstOrderFormula ”)              => `(foFormula[           |            | $e ])
  | `(“ $binders*. $e:firstOrderFormula ”)   => `(foFormula[ $binders* |            | $e ])
  | `(“ $fbinders* | $e:firstOrderFormula ”) => `(foFormula[           | $fbinders* | $e ])

/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " = " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " < " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " > " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≤ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≥ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∈ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∋ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≠ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " </ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ≰ " firstOrderTerm:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:45 firstOrderTerm:45 " ∉ " firstOrderTerm:0 : firstOrderFormula

/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∀ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " < " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " ≤ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula
/-- Imported declaration from the Incompleteness formalization. -/
syntax:max "∃ " ident " ∈ " firstOrderTerm ", " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(foFormula[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballLT
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballLE
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballMem
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexLT
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexLE
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexMem
      foTerm[ $binders* | $fbinders* | $t ]
      foFormula[ $binders'* | $fbinders* | $φ ])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm = $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.Eq.eq ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm < $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.LT.lt ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm > $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.LT.lt ![
      foTerm[ $binders* | $fbinders* | $u ],
      foTerm[ $binders* | $fbinders* | $t]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ≤ $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.LE.le ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ≥ $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.LE.le ![
      foTerm[ $binders* | $fbinders* | $u ],
      foTerm[ $binders* | $fbinders* | $t ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ∈ $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.Mem.mem ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ∋ $u:firstOrderTerm ]) =>
    `(Semiformula.Operator.operator Operator.Mem.mem ![
      foTerm[ $binders* | $fbinders* | $u ],
      foTerm[ $binders* | $fbinders* | $t ]])
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ≠ $u:firstOrderTerm ]) =>
    `(∼(Semiformula.Operator.operator Operator.Eq.eq ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]]))
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm </ $u:firstOrderTerm ]) =>
    `(∼(Semiformula.Operator.operator Operator.LT.lt ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]]))
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ≰ $u:firstOrderTerm ]) =>
    `(∼(Semiformula.Operator.operator Operator.LE.le ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]]))
  | `(foFormula[ $binders* | $fbinders* | $t:firstOrderTerm ∉ $u:firstOrderTerm ]) =>
    `(∼(Semiformula.Operator.operator Operator.Mem.mem ![
      foTerm[ $binders* | $fbinders* | $t ],
      foTerm[ $binders* | $fbinders* | $u ]]))

section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Language.Eq.eq]
def unexpsnderEq : Unexpander
  | `($_) => `(op(=))

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Language.LT.lt]
def unexpsnderLe : Unexpander
  | `($_) => `(op(<))

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Wedge.wedge]
def unexpandAnd : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Vee.vee]
def unexpandOr : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Tilde.tilde]
def unexpandNeg : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ¬$φ ”)
  | _                                => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander UnivQuantifier.univ]
def unexpandUniv : Unexpander
  | `($_ “ $φ:firstOrderFormula ”) => `(“ ∀' $φ:firstOrderFormula ”)
  | _                                => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander ExQuantifier.ex]
def unexpandEx : Unexpander
  | `($_ “ $φ:firstOrderFormula”) => `(“ ∃' $φ:firstOrderFormula ”)
  | _                                   => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander ball]
def unexpandBall : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∀[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∀[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∀[!$t] $ψ) ”)
  | _                                                           => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander bex]
def unexpandBex : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula ”) => `(“ (∃[$φ] $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                   ) => `(“ (∃[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula ”) => `(“ (∃[!$t] $ψ) ”)
  | _                                                           => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Arrow.arrow]
def unexpandArrow : Unexpander
  | `($_ “ $φ:firstOrderFormula ” “ $ψ:firstOrderFormula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:firstOrderFormula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:firstOrderFormula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander LogicalConnective.iff]
def unexpandIff : Unexpander
  | `($_ “ $φ:firstOrderFormula” “ $ψ:firstOrderFormula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:firstOrderFormula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:firstOrderFormula”) => `(“ (!$t ↔ $ψ) ”)
  | _                                                         => throw ()

/-- Imported declaration from the Incompleteness formalization. -/
@[app_unexpander Semiformula.Operator.operator]
def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm = $u   ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm = #$y  ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm = &$y  ”)
  | `($_ op(=) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm = !!$u ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 = $u   ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 = #$y  ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 = &$y  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 = !!$u ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 = $u   ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 = #$y  ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 = &$y  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 = !!$u ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                = $u   ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                = #$y  ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                = &$y  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                = !!$u ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm < $u   ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm < #$y  ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm < &$y  ”)
  | `($_ op(<) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm < !!$u ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 < $u   ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 < #$y  ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 < &$y  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 < !!$u ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 < $u   ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 < #$y  ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 < &$y  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 < !!$u ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                < $u   ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                < #$y  ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                < &$y  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                < !!$u ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm ≤ $u   ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm ≤ #$y  ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm ≤ &$y  ”)
  | `($_ op(≤) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm ≤ !!$u ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 ≤ $u   ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 ≤ #$y  ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 ≤ &$y  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 ≤ !!$u ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 ≤ $u   ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 ≤ #$y  ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 ≤ &$y  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 ≤ !!$u ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                ≤ $u   ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                ≤ #$y  ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                ≤ &$y  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                ≤ !!$u ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  ‘ $u:firstOrderTerm ’]) =>
    `(“ $t:firstOrderTerm ∈ $u   ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  #$y:term               ]) =>
    `(“ $t:firstOrderTerm ∈ #$y  ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  &$y:term               ]) =>
    `(“ $t:firstOrderTerm ∈ &$y  ”)
  | `($_ op(∈) ![‘ $t:firstOrderTerm ’,  $u                     ]) =>
    `(“ $t:firstOrderTerm ∈ !!$u ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ #$x                 ∈ $u   ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) =>
    `(“ #$x                 ∈ #$y  ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) =>
    `(“ #$x                 ∈ &$y  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) =>
    `(“ #$x                 ∈ !!$u ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:firstOrderTerm ’]) =>
    `(“ &$x                 ∈ $u   ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) =>
    `(“ &$x                 ∈ #$y  ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) =>
    `(“ &$x                 ∈ &$y  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) =>
    `(“ &$x                 ∈ !!$u ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:firstOrderTerm ’]) =>
    `(“ !!$t                ∈ $u   ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) =>
    `(“ !!$t                ∈ #$y  ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) =>
    `(“ !!$t                ∈ &$y  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) =>
    `(“ !!$t                ∈ !!$u ”)
  | _                                                            => throw ()

end «lp_section_2»

end BinderNotation

end FirstOrder
end LO
