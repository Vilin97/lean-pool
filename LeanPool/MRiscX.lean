/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Basic
import LeanPool.MRiscX.Examples.Examples
import LeanPool.MRiscX.Examples.OtpProof
import LeanPool.MRiscX.Examples.singleProofsOTP

/-!
# MRiscX: a certified RISC-V interpreter with Hoare logic in Lean

MRiscX provides an environment for verifying RISC-V assembly code in Lean using
Hoare logic. It defines an abstract syntax and operational semantics for a
RISC-V-like assembly language, a Hoare-logic specification layer (`hoare_triple_up`),
proved Hoare rules (sequencing, strengthening, weakening, conditionals),
per-instruction specifications, and custom elaborators, delaborators, and tactics
that let assembly programs and Hoare triples be written and proved directly in Lean.
A complete worked correctness proof of a One-Time-Pad implementation (`proof_otp`)
demonstrates the framework end to end.

Source: url:https://github.com/JulsDE/MRiscX
Authors: Julius Marx
Status: verified
Main declarations: `hoare_triple_up`, `S_SEQ`, `PRE_STR`, `POST_WEAK`,
`specification_LoadImmediate`, `proof_otp`
Tags: hoare-logic, program-verification, risc-v, assembly, formal-methods
-/
