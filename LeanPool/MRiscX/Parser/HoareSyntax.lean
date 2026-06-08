/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Parser.AssemblySyntax
/-!
Syntax for hoare terms
-/
/-- Syntax category for a full MRiscX Hoare triple together with its program. -/
declare_syntax_cat hoareTerm

/-- A Hoare triple written with concrete `mriscx ... end` assembly before the triple. -/
syntax mriscxSyntax withPosition(linebreak ppDedent(ppLine))
    "⦃" term "⦄ " term " ↦ " "⟨" term " | " term "⟩" "⦃" term "⦄" : hoareTerm

/-- A Hoare triple written with a named `Code` identifier before the triple. -/
syntax ident withPosition(linebreak ppDedent(ppLine))
    "⦃" term "⦄ " term " ↦ " "⟨" term " | " term "⟩" "⦃" term "⦄" : hoareTerm

/-- Notation `⦃P⦄` for a Hoare assertion on the machine state. -/
syntax "⦃" term "⦄" : term

-- General Hoare Syntax
/-- Notation `x[r]` for the value of register `r` in the current state. -/
syntax "x[" mriscxNumOrIdent "]" : term
/-- Notation `mem[a]` for the value at memory address `a` in the current state. -/
syntax "mem[" term "]" : term
/-- Notation `labels[l]` for the target index of label `l` in the current state. -/
syntax "labels[" ident "]" : term
/-- Notation `labels[.l]` for the target index of a dotted label `l`. -/
syntax "labels[" &"." ident "]" : term
/--
To avoid parsing errors we decided to
put these double parenthesis around these tokens
-/
syntax "⸨pc⸩" : term
/-- Notation `⸨terminated⸩` for the termination flag of the current state. -/
syntax "⸨terminated⸩": term



-- Hoare Assignment syntax
/-- Syntax category for a single state assignment in a Hoare postcondition. -/
declare_syntax_cat hoareAssignment (behavior := both)
/-- Syntax category for a chain of state assignments separated by `;`. -/
declare_syntax_cat hoareAssignmentChain
/-- Syntax category for a bracketed Hoare assignment block `⟦ ... ⟧`. -/
declare_syntax_cat hoareAssignmentTerm

/-- Assignment `x[r] ← v` setting register `r` to `v`. -/
syntax "x[" mriscxNumOrIdent "]" &" ← " term : hoareAssignment
/-- Assignment `x[r] <- v`, an ASCII variant of `x[r] ← v`. -/
syntax "x[" mriscxNumOrIdent "]" &" <- " term : hoareAssignment
/-- Assignment `mem[a] ← v` setting memory address `a` to `v`. -/
syntax "mem[" term &"]" &" ← " term : hoareAssignment
/-- Assignment `mem[a] <- v`, an ASCII variant of `mem[a] ← v`. -/
syntax "mem[" term &"]" &" <- " term : hoareAssignment
/-- Assignment `pc++` incrementing the program counter. -/
syntax &"pc" &"++" : hoareAssignment
/-- Assignment `pc ← l` setting the program counter to `l`. -/
syntax &"pc" &" ← " term: hoareAssignment

/-- The empty assignment block `⟦⟧`, denoting the unchanged state. -/
syntax "⟦⟧" : hoareAssignmentTerm
/-- A single assignment, viewed as a one-element assignment chain. -/
syntax hoareAssignment : hoareAssignmentChain
/-- Two assignments composed with `;`. -/
syntax hoareAssignment &"; " hoareAssignment : hoareAssignmentChain
/-- An assignment followed by a further assignment chain, composed with `;`. -/
syntax hoareAssignment &"; " hoareAssignmentChain : hoareAssignmentChain
/-- An assignment followed by a base-case term, composed with `;`. -/
syntax hoareAssignment &"; " term : hoareAssignmentChain

/-- A bracketed assignment block `⟦ ... ⟧` denoting the resulting state update. -/
syntax "⟦" hoareAssignmentChain "⟧" : hoareAssignmentTerm
