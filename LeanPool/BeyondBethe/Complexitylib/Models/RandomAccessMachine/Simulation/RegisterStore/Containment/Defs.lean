/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Bounds.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# RAM-to-TM time-class containment -- definitions

This layer fixes the twenty-work-tape concrete simulator and packages its
fourth-degree resource envelope as a natural polynomial.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- The canonical assignment of the eighteen data roles and one disjoint
program-counter role. The complete decision simulator adds one buffer tape,
so the resulting TM has twenty work tapes. -/
def standardControlInstructionTapes : ControlInstructionTapes 19 where
  data :=
    { idx := fun slot => ⟨slot.val, by omega⟩
      injective := by
        intro i j h
        apply Fin.ext
        simpa using congrArg Fin.val h }
  pc := ⟨18, by omega⟩
  pc_ne := by
    intro slot h
    have hval := congrArg Fin.val h
    change 18 = slot.val at hval
    omega

/-- Polynomial obtained by substituting a polynomial RAM-time bound into the
checked concrete simulation envelope. -/
noncomputable def programDecisionPolynomial (program : Program)
    (p : Polynomial ℕ) :
    Polynomial ℕ :=
  Polynomial.C (1000000000 * programResourceMagnitude program) *
    (Polynomial.X +
      Polynomial.C (programResourceMagnitude program + 2) * p +
      Polynomial.C (programResourceMagnitude program + 4)) ^ 4

end Machine

end RegisterStore

end RAM

end Complexity
