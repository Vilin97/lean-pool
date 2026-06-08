/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Parser.AssemblySyntax
/-!
Syntax for hoare terms
-/
declare_syntax_cat hoare_term

syntax mriscx_syntax withPosition(linebreak ppDedent(ppLine))
    "⦃" term "⦄ " term " ↦ " "⟨" term " | " term "⟩" "⦃" term "⦄" : hoare_term

syntax ident withPosition(linebreak ppDedent(ppLine))
    "⦃" term "⦄ " term " ↦ " "⟨" term " | " term "⟩" "⦃" term "⦄" : hoare_term

syntax "⦃" term "⦄" : term

-- General Hoare Syntax
syntax "x[" mriscx_num_or_ident "]" : term
syntax "mem[" term "]" : term
syntax "labels[" ident "]" : term
syntax "labels[" &"." ident "]" : term
/--
To avoid parsing errors we decided to
put these double parenthesis around these tokens
-/
syntax "⸨pc⸩" : term
syntax "⸨terminated⸩": term



-- Hoare Assignment syntax
declare_syntax_cat hoare_assignment (behavior := both)
declare_syntax_cat hoare_assignment_chain
declare_syntax_cat hoare_assignment_term

syntax "x[" mriscx_num_or_ident "]" &" ← " term : hoare_assignment
syntax "x[" mriscx_num_or_ident "]" &" <- " term : hoare_assignment
syntax "mem[" term &"]" &" ← " term : hoare_assignment
syntax "mem[" term &"]" &" <- " term : hoare_assignment
syntax &"pc" &"++" : hoare_assignment
syntax &"pc" &" ← " term: hoare_assignment

syntax "⟦⟧" : hoare_assignment_term
syntax hoare_assignment : hoare_assignment_chain
syntax hoare_assignment &"; " hoare_assignment : hoare_assignment_chain
syntax hoare_assignment &"; " hoare_assignment_chain : hoare_assignment_chain
syntax hoare_assignment &"; " term : hoare_assignment_chain

syntax "⟦" hoare_assignment_chain "⟧" : hoare_assignment_term
