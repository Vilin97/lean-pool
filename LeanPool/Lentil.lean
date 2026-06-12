/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Rules.BigOp
import LeanPool.Lentil.Rules.LeadsTo
import LeanPool.Lentil.Rules.StatePred
import LeanPool.Lentil.Rules.WF
import LeanPool.Lentil.ProofMode.Tactics
import LeanPool.Lentil.ProofMode.Display
import LeanPool.Lentil.Tactics.Basic
import LeanPool.Lentil.Tactics.FiniteWindow

/-!
# Lentil: Temporal Logic of Actions in Lean 4

Source: url:https://github.com/verse-lab/Lentil
Authors: Qiyuan Zhao
Status: verified
Main declarations: `TLA.always`, `TLA.eventually`, `TLA.always_induction`, `TLA.wf1`
Tags: temporal-logic, tla, formal-verification, proof-mode
MSC: 03B44, 68Q60
-/

/-!
# Lentil: Temporal Logic of Actions (TLA) in Lean 4

A shallow embedding of Leslie Lamport's Temporal Logic of Actions (TLA) in
Lean 4. The semantic definitions are ported from the `coq-tla` library, while
the proofs of the inference rules are reconstructed in Lean's tactic language.
The development includes the temporal modalities (`always`, `eventually`,
`later`), the standard propositional and temporal proof rules, weak-fairness
(`wf1`) and leads-to reasoning, plus an Iris-style interactive proof mode for
working with TLA judgments.
-/
