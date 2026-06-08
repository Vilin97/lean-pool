/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import Lean

import Lean.Elab.Tactic
import LeanPool.MRiscX.AbstractSyntax.Map
import LeanPool.MRiscX.Semantics.MsTheory
import LeanPool.MRiscX.Util.BasicTheorems
import LeanPool.MRiscX.Hoare.HoareCore
import LeanPool.MRiscX.Tactics.SplitLastSeq
import LeanPool.MRiscX.Tactics.ApplySpec
import LeanPool.MRiscX.Tactics.GeneralCustomTactics

import LeanPool.MRiscX.Tactics.HelpCodeProofTactics

/-!
# CodeProofTactics

This module provides tactics for discharging MRiscX code-proof goals.
-/

open Lean Meta Elab Parser Tactic RCases

/-
This file contains the custom tactics for proof automation of the formal proof of correctness for
the RISC-V assembly code.

Essentially, these are all the tactics to help you to prove that your implementation fulfills the
specification.

It is planned to extend this file to a level, where users can
prove a program written in risc-v without the requirement to know lean tactics at all,
but just use the tactics defined in this file.
-/





/-
%%%%%%
-/

/-
Proof automation for hoare-triples
-/
/--
Apply `S_SEQ` to 'peel' off the last instruction.
Also, try to solve all goals which are created during the process
except for the two goals, which involve the actual Hoare-triples which
will be generated.
-/
elab &"autoSeq" : tactic => do
  evalTactic (← `(tactic | peelLastInstr <;> try assumption))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | applyToLastGoal simpSetEq))


-- TODO make this more robust
/--
Apply the Hoare rule `S_SEQ` in order to split the current Hoare triple into two.
To do so, the names and values must be provided explicitly, each
separated by a colon.

The order is:

1. `P`
2. `R`
3. `L_W`
4. `L_W'`
5. `L_B`
6. `L_B'`

Also, try to automatically solve most of the "side goals" that are generated
during the process. These side goals are generally statements about the provided
sets (e.g., `L_W ≠ ∅`), which are trivial in most cases.

The same tactic can be used without providing `P`
-/
elab "sapplySSeq" &"P" &" := " P:term &", "
                    &"R" &" := "  R:term &", "
                    &"L_W" &" := "  L_w:term &", "
                    &"L_W'" &" := "  L_w':term &", "
                    &"L_B" &" := "  L_b:term &", "
                    &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
      (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simpSetEq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | applyToLastGoal simpSetEq ))

/--
The same as the other `sapplySSeq` tactic, but without having to provide
`P`.
-/
elab "sapplySSeq" &"R" &" := "  R:term &", "
                    &"L_W" &" := "  L_w:term &", "
                    &"L_W'" &" := "  L_w':term &", "
                    &"L_B" &" := "  L_b:term &", "
                    &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapplySSeq P := _ ,
                                        R := $R,
                                        L_W := $L_w,
                                        L_W' := $L_w',
                                        L_B := $L_b,
                                        L_B' := $L_b'))


/- apply S_SEQ with an automatic `try assumption` on every goal that is generated -/
/-- Apply the sequencing rule `S_SEQ` with the given assertions and address sets. -/
macro "sapplySSeq'" P:term ", " R:term ", " L_w:term ", " L_w':term : tactic => do
  `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R)
    (L_w := $L_w) (L_w' := $L_w') <;> try assumption)


/--
Like `sapplySSeq`, but without solving the sidegoal `L_b = L_b' ∩ L_b''`.
-/
elab "sapplySSeq''" R:term &", "
                      L_w:term &", "
                      L_w':term &", "
                      L_b:term &", "
                      L_b':term : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := _) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))

-- TODO make this more robust
/--
Apply `S_SEQ` without explicitly providing the names of the parameters.
The order is:
1. `R`
2. `L_W`
3. `L_W'`
4. `L_B`
5. `L_B'`

Also, try to automatically solve the most "side goals", which are generated
during the process. Those side goals generally are goals about the set provided
(e.g. `L_W ≠ ∅`), which are trivial is most cases.
-/
elab "sapplySSeq''"
                      -- &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := _) (R := $R) (L_w := $L_w)
      (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simpSetEq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))


/--
Apply `S_SEQ` with explicitly providing the names and values of the parameters.
The order is:
1. `P`
2. `R`
3. `L_W`
4. `L_W'`
5. `L_B`
6. `L_B'`

Also, try to automatically solve the most "side goals", which are generated
during the process. Those side goals generally are goals about the set provided
(e.g. `L_W ≠ ∅`), which are trivial is most cases.
-/
  elab "sapplySSeq''"
                      &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
      (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simpSetEq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))


/--
Apply `S_SEQ` without explicitly providing the names of the parameters.
The order is:
1. `P`
2. `R`
3. `L_W`
4. `L_W'`
5. `L_B`
6. `L_B'`
-/
elab "sapplySSeqPlain"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
      (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simpSetEq))


/-- Apply the plain sequencing rule with the given assertions and address sets. -/
elab "sapplySSeqPlain"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapplySSeqPlain P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))


-- TODO make this more robust
/--
Like `sapplySSeq''`, but also apply a tactic to automatically solve the
set equality which should be able to show `L_{B''} = L_B ∩ L_{B'}`.
-/
elab "sapplySSeq'''"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
      (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simpSetEq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | applyToLastGoal simpSetEq ))

/--
Apply S_SEQ with explicitly providing the names of the parameters.
The order is:
1. `R`
2. `L_W`
3. `L_W'`
4. `L_B`
5. `L_B'`

Also, apply a tactic to automatically solve set equality which should be
able to show `L_{B''} = L_B ∩ L_{B'}`.
-/
elab "sapplySSeq'''"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapplySSeq''' P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))




-- /- apply specification and simp some trivial goals. Requires a hypothesis being
--    introduced as `h_pc` -/
-- elab "applySpecBasic" spec:term : tactic => do
--   evalTactic (← `(tactic | apply $spec ))




/-- Discharge the routine side goals left after applying an instruction specification. -/
elab "cleanupGoalsAfterSpec" : tactic => do
  -- evalTactic (← `(tactic | first
  --                         | simpSetEq; simp
  --                         | simp  ))
  -- evalTactic (← `(tactic | simp ))
  -- evalTactic (← `(tactic | simp ))
  evalTactic (← `(tactic | simpSetEq))
  evalTactic (← `(tactic | repeat  simp))
  evalTactic (← `(tactic | simpCurrInstr ))
  evalTactic (← `(tactic | exact $(mkIdent `h_pc) ))
  evalTactic (← `(tactic | try simp at *))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | repeat assumption))

/-- Clean up the goals remaining after the proof automation has run. -/
elab "cleanupAfterAutomation" : tactic => do
  evalTactic (← `(tactic | try simpSetEq))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | try simpCurrInstr))
  evalTactic (← `(tactic | try exact $(mkIdent `h_pc)))
  evalTactic (← `(tactic | try simp at *))
  evalTactic (← `(tactic | try repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try repeat assumption))


/-- Discharge the side goals after applying a specification, using set equalities. -/
elab "cleanupGoalsAfterSpecWSetEq" : tactic => do
  evalTactic (← `(tactic | try simpSetEq ))
  evalTactic (← `(tactic | cleanupGoalsAfterSpec ))


/- apply specification after all hypothesis are introduced. Solve some trivial goals afterwards -/
/-- Apply the given instruction specification and clean up the resulting goals. -/
elab "applySpecAndCleanup" spec:term : tactic => do
  evalTactic (← `(tactic | apply $spec ))
  evalTactic (← `(tactic | cleanupGoalsAfterSpec ))


-- TODO unfold any identifier
/- apply specification for the 'first goal' of S_SEQ. This is only possible, when the goal has
been modified to a point where the first goal of S_SEQ is only one execution step -/
/-- Apply the default instruction specification and clean up the resulting goals. -/
elab "applySpecDefault" spec:term : tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s)
    $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | rw [← $(mkIdent `h_code')] ))
  evalTactic (← `(tactic | splitCondis in $(mkIdent `user_precondition) ))
  evalTactic (← `(tactic | repeat (apply $spec)))
  -- evalTactic (← `(tactic | repeat (applySpecAndCleanup $spec)))



/- apply specification for the 'second goal' of S_SEQ.-/
/-- Apply an instruction specification to the second goal and clean up. -/
elab "applySpecForSecond" spec:term : tactic => do
  evalTactic (← `(tactic | prepareSecondSeq))
  evalTactic (← `(tactic | intros $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | splitCondis in $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | apply $spec))
  -- evalTactic (← `(tactic | applySpecAndCleanup $spec))
  -- evalTactic (← `(tactic | try repeat (constructor <;> try assumption)))
  -- evalTactic (← `(tactic | try repeat (simp)))


/--
Apply a given specification and try to get rid of all proof goals which
are create during the process.

To be able to apply a specification, `L_B` **must** contain every line
except the one that is being executed. For example, if you want to
apply the specification for the `Instr.LoadImmediate`, which is on line `l`,
and you have some `(P Q : Prop)`, then the Hoare-triple needs to look like this:

`⦃P⦄ l ↦ ⟨{l+1} | {n:UInt64 | n ≠ l + 1}⟩ ⦃Q⦄`

TODO: Avoid having to provide pc, registers and values in application of specification
-/
elab "applySpec" spec:term : tactic => do
  evalTactic (← `(tactic | first
                          | applySpecDefault $spec
                          | applySpecForSecond $spec))
  evalTactic (← `(tactic | cleanupGoalsAfterSpec))
  evalTactic (← `(tactic | try simpTUpdate))

/-- Apply the instruction specification named by the given identifier. -/
elab "applySpec'" name:(ident) : tactic => do
  evalTactic (← `(tactic | first
                          | (applySpecScdGoal $name; cleanupAfterAutomation)
                          | applySpecFrstGoal $name; cleanupAfterAutomation))

/-- Apply the instruction specification inferred from the current goal. -/
elab "applySpec''" : tactic => do
  evalTactic (← `(tactic | first
                          | (applySpecScdGoal; cleanupAfterAutomation)
                          | applySpecFrstGoal; cleanupAfterAutomation))
