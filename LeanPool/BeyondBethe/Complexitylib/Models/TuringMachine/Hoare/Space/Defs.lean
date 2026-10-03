/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# Space-aware Hoare specifications — definitions

Ordinary `TM.HoareTime` records a bounded terminating run, but logarithmic-space
computation requires a bound on every reachable configuration.  This module
pairs those two obligations in one compositional contract.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- An all-reachable auxiliary-space contract from tapes satisfying `pre`. -/
def HoareSpace (tm : TM n) (pre : TapePred n)
    (inputLength spaceBound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ c', tm.reaches
      { state := tm.qstart, input := inp, work := work, output := out } c' →
      c'.WithinAuxSpace inputLength spaceBound

/-- A time-and-space Hoare contract: ordinary terminating behavior paired with
an independent all-reachable auxiliary-space contract. -/
def HoareTimeSpace (tm : TM n) (pre post : TapePred n)
    (timeBound inputLength spaceBound : ℕ) : Prop :=
  tm.HoareTime pre post timeBound ∧ tm.HoareSpace pre inputLength spaceBound

end TM

end Complexity
