/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep.Internal

/-!
# One bounded sparse-entry scan iteration

This module exposes the compositional hit-or-next-iteration contract for one
encoded sparse register-store entry.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Decode and compare one entry, then either expose its decoded value on a
hit or restore the exact invariant for the remaining encoded stream. -/
theorem entryScanStepTM_hoareTime_frame {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (rest queryBits : List Bool)
    (initialWork iterationWork : Fin n → Tape) (inp₀ out₀ : Tape)
    (hready : EntryScanReady tapes (Entry.encode entry ++ rest) queryBits
      initialWork iterationWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (entryScanStepTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = iterationWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        ((entry.1.bits = queryBits ∧
            EntryScanHit tapes entry rest queryBits initialWork work) ∨
          (entry.1.bits ≠ queryBits ∧
            EntryScanReady tapes rest queryBits initialWork work)) ∧
        out = out₀)
      (entryScanStepTime tapes entry queryBits iterationWork) :=
  entryScanStepTM_hoareTime_frame_internal tapes entry rest queryBits
    initialWork iterationWork inp₀ out₀ hready hinput houtput

/-- One scan iteration preserves one-way output safety. -/
theorem entryScanStepTM_isTransducer {n : ℕ} (tapes : EntryMatchTapes n) :
    (entryScanStepTM tapes).IsTransducer := by
  have hskip : (TM.skipTM (n := n)).IsTransducer := by
    intro state iHead wHeads oHead
    cases state <;> cases oHead <;> simp [TM.skipTM, TM.idleDir]
  unfold entryScanStepTM entryScanBranchTM
  exact (entryMatchReadTM_isTransducer tapes).seqTM
    (hskip.branchWorkSymbolTM (entryMissCleanupTM_isTransducer tapes))

/-- Coarse all-prefix auxiliary-space envelope for one scan iteration. -/
theorem entryScanStepTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryMatchTapes n) (entry : Entry) (queryBits : List Bool)
    (initialWork : Fin n → Tape) (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryScanStepTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryScanStepTM tapes).reachesIn time start current)
    (htime : time ≤ entryScanStepTime tapes entry queryBits initialWork) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryScanStepTime tapes entry queryBits initialWork) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end Machine

end RegisterStore

end RAM

end Complexity
