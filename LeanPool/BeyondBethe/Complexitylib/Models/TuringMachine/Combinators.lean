/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Defs

/-!
# TM Combinators

This file provides TM constructions for composing machines, used to prove
closure properties of complexity classes.

## Main definitions

- `TM.unionTM` — Given `tm₁ : TM n₁` deciding `L₁` and `tm₂ : TM n₂` deciding `L₂`,
  construct a `TM (n₁ + 1 + n₂)` that decides `L₁ ∪ L₂`.
- `TM.complementTM` — Given a TM deciding `L`, construct a TM (with the same
  number of work tapes) deciding `Lᶜ` by flipping the output bit.
- `TM.seqTM` — Sequential composition: run `tm₁` to completion, then `tm₂`
  on the same tapes.
- `TM.ifTM` — Conditional branching: run a test machine, then branch to a
  "then" or "else" machine based on its output.
- `TM.loopTM` — Loop combinator: repeatedly run a body machine then a test
  machine, halting when the test outputs `Γ.one`.
- `TM.scannerTM` — Generic finite-state scanner: fold a finite-state
  transition function over the input bits and emit a final symbol.
- `TM.retargetInput` — Given `M : TM k`, construct a `TM (k + 1)` that runs
  `M` but reads its "input" from work tape `k` instead of the input tape.

## Design

The union machine has three phases:

1. **Phase 1**: Simulate `tm₁`, redirecting its output to work tape `n₁`
   (a "fake output" tape). The real output tape stays pristine.
2. **Transition**: Rewind the fake output to cell 1 and check the result.
   If `Γ.one` (tm₁ accepted), write `Γ.one` to the real output and halt.
   Otherwise rewind the input tape and reset Phase-2 tapes to cell 0.
3. **Phase 2**: Simulate `tm₂` using work tapes `n₁+1..n₁+n₂`
   and the real output tape.

### Work tape layout (0-indexed)

- `0 .. n₁-1` — Phase 1's work tapes (mirrors `tm₁.work`)
- `n₁` — Phase 1's redirected output (mirrors `tm₁.output`)
- `n₁+1 .. n₁+n₂` — Phase 2's work tapes (mirrors `tm₂.work`)

### State space

`Q₁ ⊕ UnionPhase ⊕ Q₂` where `UnionPhase` encodes the four transition states
between Phase 1 and Phase 2.
-/
