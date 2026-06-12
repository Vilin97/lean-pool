/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Parser.AssemblySyntax
import LeanPool.MRiscX.AbstractSyntax.Map
import LeanPool.MRiscX.AbstractSyntax.Instr
import LeanPool.MRiscX.AbstractSyntax.AbstractSyntax
import LeanPool.MRiscX.Elab.HandleNumOrIdent
import Lean

/-!
# CodeElaborator

This module provides the elaborator turning MRiscX assembly syntax into `Code`.
-/
open Lean.Elab Command Term
open Nat
open Lean Lean.Expr Lean.Meta Lean.Parser

/-
CodeElaborator
-/

/-
First, we identify the current instruction and extract the relevant
variables. Next, we use the functions
parseMriscxNumOrIdent to obtain the expression for either the numerical
value or the variable. For jumps, we need parse Labelname to obtain the labelname either as
actual variable or as string.
Finally, we generate a constant expression representing the instruction,
along with the associated variables, and push this into the "expression"
array.
-/
/-- Elaborate a single parsed instruction into the `Expr` of its `Instr` value. -/
def getInstrExpr (t: TSyntax `mriscxInstr): TermElabM Expr := do
  match t with
    | `(mriscxInstr | la x$r:mriscxNumOrIdent, $addr:mriscxNumOrIdent
    )
    | `(mriscxInstr | la x$r:mriscxNumOrIdent, $addr:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[r, addr]
      return (mkAppN (.const `Instr.LoadAddress []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | li x$r:mriscxNumOrIdent, $v:mriscxNumOrIdent
    )
    | `(mriscxInstr | li x$r:mriscxNumOrIdent, $v:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[r, v]
      return (mkAppN (.const `Instr.LoadImmediate []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | mv x$r:mriscxNumOrIdent, x$v:mriscxNumOrIdent
    )
    | `(mriscxInstr | mv x$r:mriscxNumOrIdent, x$v:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[r, v]
      return (mkAppN (.const `Instr.CopyRegister []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | addi x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent
    )
    | `(mriscxInstr | addi x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg, i]
      return (mkAppN (.const `Instr.AddImmediate []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | inc x$dst:mriscxNumOrIdent
    )
    | `(mriscxInstr | inc x$dst:mriscxNumOrIdent;) =>
      let expr ← parseMriscxNumOrIdent dst
      return (mkAppN (.const `Instr.Increment []) #[expr])
    | `(mriscxInstr | add x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent
    )
    | `(mriscxInstr | add x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg1, reg2]
      return (mkAppN (.const `Instr.AddRegister []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | subi x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent
    )
    | `(mriscxInstr | subi x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg, i]
      return (mkAppN (.const `Instr.SubImmediate []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | dec x$reg:mriscxNumOrIdent
    )
    | `(mriscxInstr | dec x$reg:mriscxNumOrIdent;) =>
      let expr ← parseMriscxNumOrIdent reg
      return (mkAppN (.const `Instr.Decrement []) #[expr])
    | `(mriscxInstr | sub x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent
    )
    | `(mriscxInstr | sub x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg1, reg2]
      return (mkAppN (.const `Instr.SubRegister []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | xori x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent
    )
    | `(mriscxInstr | xori x$dst:mriscxNumOrIdent, x$reg:mriscxNumOrIdent,
                        $i:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg, i]

      return (mkAppN (.const `Instr.XorImmediate []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | xor x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent
    )
    | `(mriscxInstr | xor x$dst:mriscxNumOrIdent, x$reg1:mriscxNumOrIdent,
                        x$reg2:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, reg1, reg2]
      return (mkAppN (.const `Instr.XOR []) #[exprs[0]!, exprs[1]!, exprs[2]!])
    | `(mriscxInstr | lw x$dst:mriscxNumOrIdent, $addr:mriscxNumOrIdent
    )
    | `(mriscxInstr | lw x$dst:mriscxNumOrIdent, $addr:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, addr]
      return (mkAppN (.const `Instr.LoadWordImmediate []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | lw x$dst:mriscxNumOrIdent, x$addr:mriscxNumOrIdent
    )
    | `(mriscxInstr | lw x$dst:mriscxNumOrIdent, x$addr:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[dst, addr]
      return (mkAppN (.const `Instr.LoadWordReg []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | sw x$reg:mriscxNumOrIdent, x$dst:mriscxNumOrIdent
    )
    | `(mriscxInstr | sw x$reg:mriscxNumOrIdent, x$dst:mriscxNumOrIdent;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg, dst]
      return (mkAppN (.const `Instr.StoreWord []) #[exprs[0]!, exprs[1]!])
    | `(mriscxInstr | j $lbl:ident
    )
    | `(mriscxInstr | j $lbl:ident;) =>
      let expr ← parseLabelname lbl false
      return(mkAppN (.const `Instr.Jump []) #[expr])
    | `(mriscxInstr | j .$lbl:ident
    )
    | `(mriscxInstr | j .$lbl:ident;) =>
      let expr ← parseLabelname lbl true
      return(mkAppN (.const `Instr.Jump []) #[expr])
    | `(mriscxInstr | beq x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | beq x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpEq []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | beq x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | beq x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpEq []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | bne x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | bne x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpNeq []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | bne x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | bne x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpNeq []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | bgt x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | bgt x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpGt []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | bgt x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | bgt x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpGt []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | ble x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | ble x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, $lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpLe []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | ble x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | ble x$reg1:mriscxNumOrIdent, x$reg2:mriscxNumOrIdent, .$lbl:ident;) =>
      let exprs ← parseMriscxNumOrIdentArray #[reg1, reg2]
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpLe []) #[exprs[0]!, exprs[1]!, lblExpr])
    | `(mriscxInstr | beqz x$reg:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | beqz x$reg:mriscxNumOrIdent, $lbl:ident;)  =>
      let regExpr ← parseMriscxNumOrIdent reg
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpEqZero []) #[regExpr, lblExpr])
    | `(mriscxInstr | beqz x$reg:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | beqz x$reg:mriscxNumOrIdent, .$lbl:ident;) =>
      let regExpr ← parseMriscxNumOrIdent reg
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpEqZero []) #[regExpr, lblExpr])
    | `(mriscxInstr | bnez x$reg:mriscxNumOrIdent, $lbl:ident
    )
    | `(mriscxInstr | bnez x$reg:mriscxNumOrIdent, $lbl:ident;) =>
      let regExpr ← parseMriscxNumOrIdent reg
      let lblExpr ← parseLabelname lbl false
      return (mkAppN (.const `Instr.JumpNeqZero []) #[regExpr, lblExpr])
    | `(mriscxInstr | bnez x$reg:mriscxNumOrIdent, .$lbl:ident
    )
    | `(mriscxInstr | bnez x$reg:mriscxNumOrIdent, .$lbl:ident;) =>
      let regExpr ← parseMriscxNumOrIdent reg
      let lblExpr ← parseLabelname lbl true
      return (mkAppN (.const `Instr.JumpNeqZero []) #[regExpr, lblExpr])
    | _ => throwError ("Not a know Instruction")


/-
Iterate through the array of instructions and converting them
into expressions with the help of the functions previously defined.
-/
/-- Elaborate an array of parsed instructions into an array of `Instr` expressions. -/
def getInstructionExprArr (seq: TSyntaxArray `mriscxInstr): TermElabM (Array Expr) := do
  let mut expressions := #[]
  for entry in seq do
    expressions := expressions.push (←getInstrExpr entry)

  return expressions

/-- Create a tuple holding a label and the expressions of its instructions. -/
def getLabelInstrArr (t: TSyntax `mriscxLabel): TermElabM (String × (Array Expr)) := do
  match t with
  | `(mriscxLabel | $name:ident : $seq:mriscxInstr*
    ) => do
      return (name.getId.getString!, (←getInstructionExprArr seq))
  | `(mriscxLabel | .$name:ident : $seq:mriscxInstr*
    ) => do
      return ("." ++ name.getId.getString!, (←getInstructionExprArr seq))

  | _ => throwError ("Expected Label")


/-- Build the `LabelMap` of an assembly block by assigning each label its index. -/
def getLabelMapFromSyntax (syn : TSyntax `mriscxSyntax): TermElabM LabelMap := do
  match syn with
  | `(mriscxSyntax | mriscx
                        $lblSyn:mriscxLabel*
                      end) => do
    let mut counter := 0
    let mut labelInstrArr := #[]

    for synEntry in lblSyn do
      labelInstrArr := labelInstrArr.push (←getLabelInstrArr synEntry)

    let mut labelMap : LabelMap := EmptyLabels

    for label in labelInstrArr do
      labelMap := labelMap.put label.1 counter
      for _ in label.2 do
        counter := counter + 1

    return labelMap
  | _ => throwError "Expected mriscxSyntax while parsing labelMap from syntax"


/-- Elaborate a full `mriscx ... end` block into the `Expr` of its `Code` value. -/
def getCodeFromSyntax (syn: TSyntax `mriscxSyntax): TermElabM Expr := do
  match syn with
  | `(mriscxSyntax | mriscx
    $lblSyn:mriscxLabel*
    end) =>
    /-
    First, we define an array holding a pair of a String and another array.
    The second array consists the abstract syntax tree of the instructions.
    This array has the same structure as the input array.
    -/
    let mut labelInstrArr : Array (String × (Array Expr)) := #[]
    /-
      Here, the iteration through the array of labels finds place.
      Each "synEntry" holds a labelname and the corresponding instructions, if present
    -/
    for synEntry in lblSyn do
      labelInstrArr := labelInstrArr.push (←getLabelInstrArr synEntry)

    /-
    Now, we create the EmptyInstructionMap and the EmptyLabels we already defined in "Syntax.lean"
    as expression, so we can fill them with the just converted labels and instructions.
    -/
    let mut instruction_map := mkAppN (.const `TMap.empty []) #[(.const `InstructionIndex []) , (.const `Instr []) , (.const `Instr.Panic [])]
    let mut label_map := mkAppN (.const `PMap.empty []) #[(.const `String []) , (.const `UInt64 [])]
    /-
    Next, we initialize the starting point of the program counter (pc). (In the future,
    we may allow the user to specify the initial value of the pc for added flexibility.)
    We then iterate through the labelInstrArray, which contains label names paired with
    their corresponding arrays of instructions. Each label name is added to the labels_map,
    pointing to the current value of the program counter.
    Additionally, the counter is used to assign numerical values to the instructions.
    As we iterate through the array of instruction expressions associated with each
    label, the counter is incremented and both the counter value and instructions
    are added to the instruction_map.
    -/
    let mut counter : UInt64 := 0
    for labelInstr in labelInstrArr do
      label_map ← mkAppM ``PMap.put #[mkStrLit (labelInstr.1) , mkUInt64Lit counter , label_map]
      for instr in labelInstr.2 do
        instruction_map ← mkAppM ``TMap.put #[mkUInt64Lit (counter) , instr, instruction_map]
        counter := counter + 1
    /-
    Finally, a constant which represents the Code structure holding the two freshly
    filled maps as expression is returned.
    -/
    return mkAppN (.const `Code.mk []) #[instruction_map, label_map]
  | _ => throwError "Expected mriscx syntax"

/-
We can now begin the actual elaboration of the previously defined syntax.
This process starts with the elab keyword, followed by the specific syntax
we wish to elaborate. In this case, we trigger the elaboration as soon as
the mriscx keyword is encountered.
Next, we expect an indefinite number of mriscx_labels—ranging from zero
to an arbitrary amount. The new term is concluded with the keyword end.
As defined earlier, the mriscxLabel syntax consists of a label name
(an ident), followed by a colon and our custom instructions. For example:

label1: li x0, 12
        li x1, 13

In the end, we have an array of mriscx_labels, where each label consists
of an ident and an array of mriscx_instr. We can iterate through both
arrays to construct the abstract syntax tree, which will be returned at
the conclusion of the process.

Simultaneously, we can generate the "infoLogoration," a visual representation
of the syntax tree. This infoLogoration should closely resemble the original
source code as written by the user, ensuring clarity and ease of understanding.
-/
/-- Term elaborator turning a `mriscx ... end` assembly block into its `Code` value. -/
elab syn:mriscxSyntax : term => do
  return ←getCodeFromSyntax syn


/-
The added term elaboration now lets us write code like this
`

def codeExample :=
mriscx
  labelExample1:  li x 0, 1
                  li x 1, 2
  labelExample2:  j labelExample3
                  li x 10, 25
  labelExample3:  li x 99, 152
end

We can also check, what type "example1" has.
Checking the type of `codeExample` yields `codeExample : Code`.

Since it has the type Code, we have access to the instructionMap and
Labels. Moreover, we can use this to create a `MState` and run the
code we just wrote down.



To write and prove specifications for a single instruction,
without considering label names or program counters, we need an
additional term elaboration. This time, the goal is to interpret
just one instruction, while retaining the same features and
flexibility as before.

The next elaboration handles this, serving as a more concise version
of the previous elaborator extension, focused solely on individual
instructions.
-/

/-- Term elaborator turning a single bracketed instruction specification `⟪i⟫`
into the `Expr` of its `Instr` value. -/
elab s:mriscxSpec : term => do
  match s with
  | `(mriscxSpec | ⟪$entry:mriscxInstr⟫) => do
    return (←getInstrExpr entry)
  | _ => throwError "expexted an mriscx instruction"
