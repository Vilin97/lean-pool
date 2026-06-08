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

declare_syntax_cat mriscx_label
 -- behaviour := both controls the behavior whether lean parser
 -- wants to parse func name as token / ident
declare_syntax_cat mriscx_Instr (behavior := both)
declare_syntax_cat mriscx_syntax
declare_syntax_cat mriscx_program
declare_syntax_cat mriscx_num_or_ident
declare_syntax_cat hoare

-- this cat is for making it easier to differentiate between single line
-- proofs and hole code snippets. Its specially for specifications.
declare_syntax_cat mriscx_spec

/-
Next, we define the syntax that will be valid within our language. Since we aim
to prove statements based on this language, it is essential to support numerical
literals (num) and variables as integers (ident).
-/
syntax num : mriscx_num_or_ident

syntax ident : mriscx_num_or_ident
/-
Now we can define the syntax of all the legal instructions we need for our program.
-/
/-
Operations in registers
-/
syntax "la " &"x" mriscx_num_or_ident &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "li " &"x" mriscx_num_or_ident &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "mv " &"x" mriscx_num_or_ident &"," &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "addi " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "inc " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "add " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "subi " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "dec " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "sub " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "xori " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident &", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "xor " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Operations on memory
-/
-- Load word immediately from address
syntax "lw " &"x" mriscx_num_or_ident ", " mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
-- Load word from address stored in register
syntax "lw " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
-- Store word stored in register
-- The first register is the source, the second holds the destination address
syntax "sw " &"x" mriscx_num_or_ident ", " &"x" mriscx_num_or_ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Flow control operations
-/
syntax &"j " ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax &"j " &"." ident withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beq " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beq " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", "  &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bne " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bne " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bgt " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bgt " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "ble " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "ble " &"x" mriscx_num_or_ident &", " &"x" mriscx_num_or_ident &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beqz " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "beqz " &"x" mriscx_num_or_ident &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bnez " &"x" mriscx_num_or_ident &", " ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr
syntax "bnez " &"x" mriscx_num_or_ident &", " &"." ident
  withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
Default instruction
-/
syntax "PANIC!" withPosition(semicolonOrLinebreak ppDedent(ppLine)) : mriscx_Instr

/-
The labels followed by the instructions
-/
syntax ppDedent(ppDedent(ppLine)) ident ": " mriscx_Instr* : mriscx_label
syntax ppDedent(ppDedent(ppLine)) &"." ident ": " mriscx_Instr* : mriscx_label


syntax "mriscx" withPosition(linebreak)
  mriscx_label*
  ppDedent("end") : mriscx_syntax

syntax mriscx_syntax : term


/-
Brackets to indicate specification of instruction
-/
syntax "⟪" mriscx_Instr "⟫": mriscx_spec
