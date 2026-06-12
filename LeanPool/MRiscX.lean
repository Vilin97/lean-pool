/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
import LeanPool.MRiscX.Basic
import LeanPool.MRiscX.Examples.Examples
import LeanPool.MRiscX.Examples.OtpProof
import LeanPool.MRiscX.Examples.SingleProofsOTP
import LeanPool.MRiscX.Examples.SpecAutomation

/-!
# MRiscX

Source: doi:10.1007/978-3-030-58768-0_11, url:https://github.com/JulsDE/MRiscX
Authors: Julius Marx
Status: verified
Main declarations: `hoareTripleUp`, `S_SEQ`, `proof_otp`
Tags: hoare-logic, program-verification, risc-v, assembly, formal-methods
MSC: 68Q60
-/

/-!
# MRiscX: a Hoare logic for unstructured RISC-V-like assembly in Lean

MRiscX provides an environment for verifying unstructured RISC-V-like assembly
code in Lean, following the Hoare-style logic for unstructured programs of
Lundberg, Guanciale, Lindner, and Dam (SEFM 2020, doi:10.1007/978-3-030-58768-0_11).
It defines an abstract syntax and certified operational semantics for a
RISC-V-like assembly language, a Hoare-logic specification layer (`hoareTripleUp`)
whose judgements track program-counter whitelists and blacklists instead of
relying on structured control flow, proved structural Hoare rules (sequencing,
strengthening, weakening, conditionals), per-instruction specifications, and
custom elaborators, delaborators, and tactics that let assembly programs and
Hoare triples be written and proved directly in Lean. A complete worked
correctness proof of a One-Time-Pad implementation (`proof_otp`) demonstrates
the framework end to end.
-/
