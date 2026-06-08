/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean

/-!
# AssemblySyntax

This module provides the parser/grammar for MRiscX assembly syntax.
-/
open Lean Parser
/-
In this file, we extend Lean by introducing a new term. This term allows
us to write assembly language source code, which can then be elaborated
into a form that is processable, which will be the Code structure.
To do so, the syntax needs to be defined. Furthermore, the syntax
should be elevated to the `Code` structure. For this, the syntax need to be
converted into the abstract syntax tree called `Expr`.
In order to understand this, the syntax and semantics of the MRiscX language should be present.

First of all, we define some syntax categories
-/

/-- Syntax category for a labelled block of MRiscX assembly instructions. -/
declare_syntax_cat mriscxLabel
 -- behaviour := both controls the behavior whether lean parser
 -- wants to parse func name as token / ident
/-- Syntax category for a single MRiscX assembly instruction. -/
declare_syntax_cat mriscxInstr (behavior := both)
/-- Syntax category for a complete MRiscX assembly program (`mriscx ... end`). -/
declare_syntax_cat mriscxSyntax
/-- Syntax category for an MRiscX program body. -/
declare_syntax_cat mriscxProgram
/-- Syntax category for an MRiscX operand: a numeral or a register/variable identifier. -/
declare_syntax_cat mriscxNumOrIdent
/-- Syntax category for MRiscX Hoare-triple notation. -/
declare_syntax_cat hoare

-- this cat is for making it easier to differentiate between single line
-- proofs and hole code snippets. Its specially for specifications.
/-- Syntax category for a single-instruction MRiscX specification (`⟪i⟫`). -/
declare_syntax_cat mriscxSpec

/-
Next, we define the syntax that will be valid within our language. Since we aim
to prove statements based on this language, it is essential to support numerical
literals (num) and variables as integers (ident).
-/
/-- Numeral operand syntax. -/
syntax num : mriscxNumOrIdent

/-- Identifier (register/variable) operand syntax. -/
syntax ident : mriscxNumOrIdent
/-
Now we can define the syntax of all the legal instructions we need for our program.
-/
/-
Operations in registers
-/
/-- Concrete syntax for the MRiscX `la` instruction. -/
syntax "la " &"x" mriscxNumOrIdent &", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `li` instruction. -/
syntax "li " &"x" mriscxNumOrIdent &", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `mv` instruction. -/
syntax "mv " &"x" mriscxNumOrIdent &"," &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `addi` instruction. -/
syntax "addi " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `inc` instruction. -/
syntax "inc " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `add` instruction. -/
syntax "add " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `subi` instruction. -/
syntax "subi " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent &", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `dec` instruction. -/
syntax "dec " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `sub` instruction. -/
syntax "sub " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `xori` instruction. -/
syntax "xori " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent &", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `xor` instruction. -/
syntax "xor " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr

/-
Operations on memory
-/
-- Load word immediately from address
/-- Concrete syntax for the MRiscX `lw` instruction. -/
syntax "lw " &"x" mriscxNumOrIdent ", " mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
-- Load word from address stored in register
/-- Concrete syntax for the MRiscX `lw` instruction. -/
syntax "lw " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
-- Store word stored in register
-- The first register is the source, the second holds the destination address
/-- Concrete syntax for the MRiscX `sw` instruction. -/
syntax "sw " &"x" mriscxNumOrIdent ", " &"x" mriscxNumOrIdent
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr

/-
Flow control operations
-/
/-- Concrete syntax for the MRiscX `j` instruction. -/
syntax &"j " ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `j` instruction. -/
syntax &"j " &"." ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `beq` instruction. -/
syntax "beq " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `beq` instruction. -/
syntax "beq " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", "  &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bne` instruction. -/
syntax "bne " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bne` instruction. -/
syntax "bne " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bgt` instruction. -/
syntax "bgt " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bgt` instruction. -/
syntax "bgt " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `ble` instruction. -/
syntax "ble " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `ble` instruction. -/
syntax "ble " &"x" mriscxNumOrIdent &", " &"x" mriscxNumOrIdent &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `beqz` instruction. -/
syntax "beqz " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `beqz` instruction. -/
syntax "beqz " &"x" mriscxNumOrIdent &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bnez` instruction. -/
syntax "bnez " &"x" mriscxNumOrIdent &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr
/-- Concrete syntax for the MRiscX `bnez` instruction. -/
syntax "bnez " &"x" mriscxNumOrIdent &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr

/-
Default instruction
-/
/-- Concrete syntax for the MRiscX `PANIC!` instruction. -/
syntax "PANIC!" withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscxInstr

/-
The labels followed by the instructions
-/
/-- Concrete syntax for a labelled block `name: instr...` of instructions. -/
syntax ppDedent(ppDedent(ppLine)) ident ": " mriscxInstr* : mriscxLabel
/-- Concrete syntax for a dotted labelled block `.name: instr...` of instructions. -/
syntax ppDedent(ppDedent(ppLine)) &"." ident ": " mriscxInstr* : mriscxLabel


/-- A complete MRiscX assembly program: a sequence of labelled instruction
blocks delimited by `mriscx ... end`. -/
syntax (name := mriscxSyntaxBlock) "mriscx" withPosition(linebreak)
  mriscxLabel*
  ppDedent("end") : mriscxSyntax

/-- Inject a parsed `mriscx ... end` block into the term language. -/
syntax mriscxSyntax : term


/-
Brackets to indicate specification of instruction
-/
/-- Bracket notation `⟪i⟫` marking a single-instruction specification. -/
syntax "⟪" mriscxInstr "⟫": mriscxSpec
