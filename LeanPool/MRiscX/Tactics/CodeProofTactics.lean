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
elab &"auto_seq" : tactic => do
  evalTactic (← `(tactic | peel_last_instr <;> try assumption))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | apply_to_last_goal simp_set_eq))


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
elab "sapply_s_seq" &"P" &" := " P:term &", "
                    &"R" &" := "  R:term &", "
                    &"L_W" &" := "  L_w:term &", "
                    &"L_W'" &" := "  L_w':term &", "
                    &"L_B" &" := "  L_b:term &", "
                    &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | apply_to_last_goal simp_set_eq ))

/--
The same as the other `sapply_s_seq` tactic, but without having to provide
`P`.
-/
elab "sapply_s_seq" &"R" &" := "  R:term &", "
                    &"L_W" &" := "  L_w:term &", "
                    &"L_W'" &" := "  L_w':term &", "
                    &"L_B" &" := "  L_b:term &", "
                    &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapply_s_seq P := _ ,
                                        R := $R,
                                        L_W := $L_w,
                                        L_W' := $L_w',
                                        L_B := $L_b,
                                        L_B' := $L_b'))


/- apply S_SEQ with an automatic `try assumption` on every goal that is generated -/
macro "sapply_s_seq'" P:term ", " R:term ", " L_w:term ", " L_w':term : tactic => do
  `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R)
    (L_w := $L_w) (L_w' := $L_w') <;> try assumption)


/--
Like `sapply_s_seq`, but without solving the sidegoal `L_b = L_b' ∩ L_b''`.
-/
elab "sapply_s_seq''" R:term &", "
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
elab "sapply_s_seq''"
                      -- &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := _) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
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
  elab "sapply_s_seq''"
                      &"P" &" := " P:term &", "
                      &"R" &" := "  R:term &", "
                      &"L_W" &" := "  L_w:term &", "
                      &"L_W'" &" := "  L_w':term &", "
                      &"L_B" &" := "  L_b:term &", "
                      &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
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
elab "sapply_s_seq_plain"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))


elab "sapply_s_seq_plain"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapply_s_seq_plain P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))


-- TODO make this more robust
/--
Like `sapply_s_seq''`, but also apply a tactic to automatically solve the
set equality which should be able to show `L_{B''} = L_B ∩ L_{B'}`.
-/
elab "sapply_s_seq'''"  &"P" &" := " P:term &", "
                        &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | apply $(mkIdent `S_SEQ) (P := $P) (R := $R) (L_w := $L_w)
                            (L_w' := $L_w') (L_b := $L_b) (L_b' := $L_b') <;> try assumption <;> try simp_set_eq))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | · simp ))
  evalTactic (← `(tactic | apply_to_last_goal simp_set_eq ))

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
elab "sapply_s_seq'''"  &"R" &" := "  R:term &", "
                        &"L_W" &" := "  L_w:term &", "
                        &"L_W'" &" := "  L_w':term &", "
                        &"L_B" &" := "  L_b:term &", "
                        &"L_B'" &" := "  L_b':term
      : tactic => do
  evalTactic (← `(tactic | sapply_s_seq''' P := _ ,
                                           R := $R,
                                           L_W := $L_w,
                                           L_W' := $L_w',
                                           L_B := $L_b,
                                           L_B' := $L_b'))




-- /- apply specification and simp some trivial goals. Requires a hypothesis being
--    introduced as `h_pc` -/
-- elab "apply_spec_basic" spec:term : tactic => do
--   evalTactic (← `(tactic | apply $spec ))




elab "cleanup_goals_after_spec" : tactic => do
  -- evalTactic (← `(tactic | first
  --                         | simp_set_eq; simp
  --                         | simp  ))
  -- evalTactic (← `(tactic | simp ))
  -- evalTactic (← `(tactic | simp ))
  evalTactic (← `(tactic | simp_set_eq))
  evalTactic (← `(tactic | repeat  simp))
  evalTactic (← `(tactic | simp_currInstr ))
  evalTactic (← `(tactic | exact $(mkIdent `h_pc) ))
  evalTactic (← `(tactic | try simp at *))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | repeat assumption))

elab "cleanup_after_automation" : tactic => do
  evalTactic (← `(tactic | try simp_set_eq))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | try simp))
  evalTactic (← `(tactic | try simp_currInstr))
  evalTactic (← `(tactic | try exact $(mkIdent `h_pc)))
  evalTactic (← `(tactic | try simp at *))
  evalTactic (← `(tactic | try repeat (constructor <;> try assumption)))
  evalTactic (← `(tactic | try repeat assumption))


elab "cleanup_goals_after_spec_w_set_eq" : tactic => do
  evalTactic (← `(tactic | try simp_set_eq ))
  evalTactic (← `(tactic | cleanup_goals_after_spec ))


/- apply specification after all hypothesis are introduced. Solve some trivial goals afterwards -/
elab "apply_spec_and_cleanup" spec:term : tactic => do
  evalTactic (← `(tactic | apply $spec ))
  evalTactic (← `(tactic | cleanup_goals_after_spec ))


-- TODO unfold any identifier
/- apply specification for the 'first goal' of S_SEQ. This is only possible, when the goal has
been modified to a point where the first goal of S_SEQ is only one execution step -/
elab "apply_spec_default" spec:term : tactic => do
  evalTactic (← `(tactic | intros $(mkIdent `h_inter) $(mkIdent `h_empty) $(mkIdent `s) $(mkIdent `h_code') $(mkIdent `h_pc) $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | rw [← $(mkIdent `h_code')] ))
  evalTactic (← `(tactic | split_condis in $(mkIdent `user_precondition) ))
  evalTactic (← `(tactic | repeat (apply $spec)))
  -- evalTactic (← `(tactic | repeat (apply_spec_and_cleanup $spec)))



/- apply specification for the 'second goal' of S_SEQ.-/
elab "apply_spec_for_second" spec:term : tactic => do
  evalTactic (← `(tactic | prepare_second_seq))
  evalTactic (← `(tactic | intros $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | split_condis in $(mkIdent `user_precondition)))
  evalTactic (← `(tactic | apply $spec))
  -- evalTactic (← `(tactic | apply_spec_and_cleanup $spec))
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
elab "apply_spec" spec:term : tactic => do
  evalTactic (← `(tactic | first
                          | apply_spec_default $spec
                          | apply_spec_for_second $spec))
  evalTactic (← `(tactic | cleanup_goals_after_spec))
  evalTactic (← `(tactic | try simp_t_update))

elab "apply_spec'" name:(ident) : tactic => do
  evalTactic (← `(tactic | first
                          | (apply_spec_scd_goal $name; cleanup_after_automation)
                          | apply_spec_frst_goal $name; cleanup_after_automation))

elab "apply_spec''" : tactic => do
  evalTactic (← `(tactic | first
                          | (apply_spec_scd_goal; cleanup_after_automation)
                          | apply_spec_frst_goal; cleanup_after_automation))
