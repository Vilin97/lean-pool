/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork.Internal

/-!
# Binary work-tape loop combinator

`TM.forBinaryWorkTM driverIdx body` invokes `body` once per Boolean cell on a
designated work tape and stops at the first blank. The body sees the current
bit; the loopback seam advances the driver. This supplies width-driven control
for bitwise algorithms without iterating over the represented numeric value.

## Main results

- `TM.ForBinaryWorkLoopSpec.reachesIn` composes an indexed exact-execution
  certificate for the complete loop.
- `TM.ForBinaryWorkLoopSpaceSpec.prefix_withinAuxSpace` bounds every prefix of
  the certified loop run.
- `TM.IsTransducer.forBinaryWorkTM` preserves one-way output safety.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Exact remaining execution of a certified binary work-tape loop. -/
theorem ForBinaryWorkLoopSpec.reachesIn
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ}
    {total count value : ℕ}
    (spec : ForBinaryWorkLoopSpec driverIdx body bodyTime total)
    (htotal : value + count = total) :
    (forBinaryWorkTM driverIdx body).reachesIn
      (forBinaryWorkLoopTime bodyTime value count)
      (spec.scanCfg value) spec.doneCfg :=
  spec.reachesIn_internal count value htotal

/-- Every prefix up to the exact remaining runtime of a certified binary-work
loop respects its all-reachable auxiliary-space budget. -/
theorem ForBinaryWorkLoopSpaceSpec.prefix_withinAuxSpace
    {driverIdx : Fin n} {body : TM n} {bodyTime : ℕ → ℕ}
    {total inputLength spaceBound count value t : ℕ}
    {spec : ForBinaryWorkLoopSpec driverIdx body bodyTime total}
    (spaceSpec : ForBinaryWorkLoopSpaceSpec spec inputLength spaceBound)
    {c : Cfg n (forBinaryWorkTM driverIdx body).Q}
    (htotal : value + count = total)
    (hreach : (forBinaryWorkTM driverIdx body).reachesIn t
      (spec.scanCfg value) c)
    (htime : t ≤ forBinaryWorkLoopTime bodyTime value count) :
    c.WithinAuxSpace inputLength spaceBound :=
  spaceSpec.prefix_withinAuxSpace_internal count value t c htotal hreach
    htime

/-- Iterating a one-way-output body over a binary work tape remains a
transducer. -/
theorem IsTransducer.forBinaryWorkTM
    {driverIdx : Fin n} {body : TM n} (hbody : body.IsTransducer) :
    (forBinaryWorkTM driverIdx body).IsTransducer :=
  hbody.forBinaryWorkTM_internal

end TM

end Complexity
