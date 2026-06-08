/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.Parser.AssemblySyntax
import LeanPool.MRiscX.Elab.CodeElaborator
import LeanPool.MRiscX.AbstractSyntax.Instr

/-!
# DelabCode

This module provides delaborators rendering MRiscX `Code` back to assembly syntax.
-/
open Lean PrettyPrinter Delaborator SubExpr Expr Nat

/-
This file contains the delaborator of the code datastructure, which
is implemented as unexpander of the Code.mk function.
-/

def SyntaxInstrMap := TMap UInt64  (TSyntax `mriscx_Instr)
deriving Repr, Inhabited



-- Turn term of function of mriscx_Instr syntax
def termToInstr (t: TSyntax `term) : UnexpandM (TSyntax `mriscx_Instr) := do
  match t with
  | `(Instr.LoadAddress $dst $addr) =>
    let dstNum ← numOrIdentToSyntax dst
    let addrNum ← numOrIdentToSyntax addr
    `(mriscx_Instr | la x$dstNum, $addrNum
    )
  | `(Instr.LoadImmediate $dst $i) =>
    let dstNum ← numOrIdentToSyntax dst
    let iNum  ← numOrIdentToSyntax i
    `(mriscx_Instr | li x$dstNum, $iNum
    )
  | `(Instr.CopyRegister $dst $src) =>
    let dstNum ← numOrIdentToSyntax dst
    let srcNum ← numOrIdentToSyntax src
    `(mriscx_Instr | mv x$dstNum, x$srcNum
    )
  | `(Instr.AddImmediate $dst $reg $i) =>
    let dstNum ← numOrIdentToSyntax dst
    let regNum ← numOrIdentToSyntax reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | addi x$dstNum, x$regNum, $iNum
    )
  | `(Instr.Increment $dst) =>
    let dstNum ← numOrIdentToSyntax dst
    `(mriscx_Instr | inc x$dstNum
    )
  | `(Instr.AddRegister $dst $reg1 $reg2) =>
    let dstNum ← numOrIdentToSyntax dst
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | add x$dstNum, x$reg1Num, x$reg2Num
    )
  | `(Instr.SubImmediate $dst $reg $i) =>
    let dstNum ← numOrIdentToSyntax dst
    let regNum ← numOrIdentToSyntax reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | subi x$dstNum, x$regNum, $iNum
    )
  | `(Instr.Decrement $dst) =>
    let dstNum ← numOrIdentToSyntax dst
    `(mriscx_Instr | dec x$dstNum
    )
  | `(Instr.SubRegister $dst $reg1 $reg2) =>
    let dstNum ← numOrIdentToSyntax dst
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | sub x$dstNum, x$reg1Num, x$reg2Num
    )

  | `(Instr.XorImmediate $dst $reg $i) =>
    let dstNum ← numOrIdentToSyntax dst
    let regNum ← numOrIdentToSyntax reg
    let iNum ← numOrIdentToSyntax i
    `(mriscx_Instr | xori x$dstNum, x$regNum, $iNum
    )

  | `(Instr.XOR $dst $reg1 $reg2) =>
    let dstNum ← numOrIdentToSyntax dst
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | xor x$dstNum, x$reg1Num, x$reg2Num
    )

  | `(Instr.LoadWordImmediate $dst $addr) =>
    let dstNum ← numOrIdentToSyntax dst
    let addrNum ← numOrIdentToSyntax addr
    `(mriscx_Instr | lw x$dstNum, $addrNum
    )

  | `(Instr.LoadWordReg $dst $addr) =>
    let dstNum ← numOrIdentToSyntax dst
    let addrNum ← numOrIdentToSyntax addr
    `(mriscx_Instr | lw x$dstNum, x$addrNum
    )

  | `(Instr.StoreWord $reg $dst) =>
    let dstNum ← numOrIdentToSyntax dst
    let regNum ← numOrIdentToSyntax reg
    `(mriscx_Instr | sw x$regNum, x$dstNum
    )

  | `(Instr.Jump $lbl:ident) => `(mriscx_Instr | j $(mkIdent s!"{lbl}".toName)
  )
  | `(Instr.Jump $lbl:str) => `(mriscx_Instr | j $(mkIdent lbl.getString.toName)
  )
  | `(Instr.JumpEq $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | beq x$reg1Num, x$reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpEq $reg1 $reg2 $lbl:str) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | beq x$reg1Num, x$reg2Num, $(mkIdent lbl.getString.toName)
    )

  | `(Instr.JumpNeq $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | bne x$reg1Num, x$reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpNeq $reg1 $reg2 $lbl:str) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | bne x$reg1Num, x$reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpGt $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | bgt x$reg1Num, x$reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpGt $reg1 $reg2 $lbl:str) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | bgt x$reg1Num, x$reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpLe $reg1 $reg2 $lbl:ident) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | ble x$reg1Num, x$reg2Num, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpLe $reg1 $reg2 $lbl:str) =>
    let reg1Num ← numOrIdentToSyntax reg1
    let reg2Num ← numOrIdentToSyntax reg2
    `(mriscx_Instr | ble x$reg1Num, x$reg2Num, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpEqZero $reg $lbl:ident) =>
    let regNum ← numOrIdentToSyntax reg
    `(mriscx_Instr | beqz x$regNum, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpEqZero $reg $lbl:str) =>
    let regNum ← numOrIdentToSyntax reg
    `(mriscx_Instr | beqz x$regNum, $(mkIdent lbl.getString.toName)
    )
  | `(Instr.JumpNeqZero $reg $lbl:ident) =>
    let regNum ← numOrIdentToSyntax reg
    `(mriscx_Instr | bnez x$regNum, $(mkIdent s!"{lbl}".toName)
    )
  | `(Instr.JumpNeqZero $reg $lbl:str) =>
    let regNum ← numOrIdentToSyntax reg
    `(mriscx_Instr | bnez x$regNum, $(mkIdent lbl.getString.toName)
    )
  | _ => return ←`(mriscx_Instr | PANIC!
  )

partial def termToInstrMap (t: TSyntax `term) : UnexpandM SyntaxInstrMap := do
  match t with
  | `(TMap.empty $_) =>
    return (TMap.empty (←`(mriscx_Instr | PANIC!
    )))
  | `((UInt64.ofNat $k:num ↦ $v ; $m)) =>
    return ((UInt64.ofNat k.getNat) ↦ (←termToInstr v) ; (←termToInstrMap m))
  | `(($k:num ↦ $v ; $m)) =>
    return ((UInt64.ofNat k.getNat) ↦ (←termToInstr v) ; (←termToInstrMap m))
  | _ => return TMap.empty (⟨t⟩)


partial def termToLabelMap (t: TSyntax `term) : LabelMap :=
  match t with
  | `(PMap.empty) => PMap.empty
  | `(EmptyLabels) => PMap.empty
  | `(PMap.put $k:str $v:num $m) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | `(p($k:str ↦ UInt64.ofNat $v:num ; $m)) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | `(p($k:str ↦ $v:num ; $m)) =>
    PMap.put (k.getString) (UInt64.ofNat v.getNat) (termToLabelMap m)
  | _ => EmptyLabels




def createLabelInstructionArray (instructionMap:SyntaxInstrMap) (labelMap:LabelMap) :
    Array (String × Array (TSyntax `mriscx_Instr)) := Id.run do
  let labels := labelMap.getKeys

  if labels.length == 1 then do
    let result_lbl := labels.head!
    let mut result_insts := #[]

    for keyInstr in instructionMap.getKeys do
      result_insts := result_insts.push (instructionMap.get keyInstr)

    return #[(result_lbl, result_insts)]


  let mut result := #[]
  for i in [0 : labels.length : 1] do
    let label_entry := labels.get!Internal i
    let label_entry_plus_one := labels.get?Internal (i + 1)

    match label_entry_plus_one with
    | some label_plus_one =>
      let cur_index := labelMap.get label_entry
      let next_index := labelMap.get label_plus_one
      let mut cur_Instrs := #[]

      match cur_index, next_index with
      | some cur, some next => do
        for j in [cur.toNat : next.toNat : 1] do
          cur_Instrs := cur_Instrs.push (instructionMap.get (id j.toUInt64))
        result := result.push (label_entry, cur_Instrs)

      | _, _ => unreachable!

    | none =>
      let cur_index := labelMap.get label_entry
      let last_c_index := instructionMap.getLastKey
      let mut cur_Instrs := #[]

      match cur_index, last_c_index with
      | some cur, some last =>
        for j in [cur.toNat : last.toNat + 1 : 1] do
          cur_Instrs := cur_Instrs.push (instructionMap.get (id j.toUInt64))
        result := result.push (label_entry, cur_Instrs)
      | _ , _ => unreachable!

  return result



@[app_unexpander Code.mk]
def CodeUnexpander : Unexpander
  | `($_ $i $l) => do

    let labels := termToLabelMap l
    let instructionMap := (←termToInstrMap i)
    let syntaxArray := createLabelInstructionArray instructionMap labels

    if syntaxArray.size > 0 then
      let mut syntaxes := #[]

      for labelWithCode in syntaxArray do
        let instrs := labelWithCode.2
        let mut instrSyntaxes := #[]

        for instr in instrs do
          let syntaxInstr := instr
          instrSyntaxes := instrSyntaxes.push (←`(mriscx_Instr | $syntaxInstr))

        if String.Pos.Raw.get labelWithCode.1 0 == '.' then
          let labelName := mkIdent (labelWithCode.1.drop 1).copy.toName
          syntaxes := syntaxes.push (←`(mriscx_label | .$labelName:ident : $instrSyntaxes*))
        else
          let labelName := mkIdent labelWithCode.1.toName
          syntaxes := syntaxes.push (←`(mriscx_label | $labelName:ident : $instrSyntaxes*))
      `(mriscx_syntax | mriscx
        $syntaxes*
        end)
    else
      throw Unit.unit

  | _ => throw Unit.unit
