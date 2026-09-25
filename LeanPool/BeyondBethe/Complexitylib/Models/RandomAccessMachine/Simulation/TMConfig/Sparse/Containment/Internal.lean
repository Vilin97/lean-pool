/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics.PolyBound
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.NormalForm
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Classes.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI

/-!
# TM-to-RAM time-class containment -- proof internals

This module lifts the checked public-ABI sparse simulation from one halting run
to deciders and then discharges the polynomial-bound arithmetic needed for the
forward machine-model robustness theorem.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


theorem compiledDecision_decidesInTime_internal
    {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (hdecides : tm.DecidesInTime L T) :
    (compiledDecision tm).DecidesInTime L
      (fun inputLength => decisionTimeBound tm inputLength (T inputLength)) := by
  intro x
  obtain ⟨halted, steps, hsteps, hreach, hhalted, hyes, hno⟩ := hdecides x
  obtain ⟨final, fuel, cost, _space, _hexec, hcost, _hspace, hrun,
      hramHalted, hlogCost, _hspaceExact, hverdict⟩ :=
    compiledDecision_resourceBound hreach hhalted
  refine ⟨fuel, hramHalted, ?_, ?_, ?_⟩
  · rw [hlogCost]
    exact le_trans hcost (decisionTimeBound_mono_steps tm x.length hsteps)
  · intro hx
    rw [hrun]
    change final stateReg = 1
    rw [hverdict, hyes hx]
    decide
  · intro hx
    rw [hrun]
    change final stateReg = 0
    rw [hverdict, hno hx]
    decide

theorem mem_DTIME_of_decidesInTime_internal
    {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (hdecides : tm.DecidesInTime L T) :
    L ∈ RAM.DTIME (fun inputLength =>
      decisionTimeBound tm inputLength (T inputLength)) :=
  ⟨compiledDecision tm,
    (fun inputLength => decisionTimeBound tm inputLength (T inputLength)),
    compiledDecision_decidesInTime_internal hdecides, BigO.refl _⟩

end Sparse

end TMConfig

end RAM

/-! ## Polynomial bounds on the sparse simulation's resource functions

Extensions of the generic `PolyBound` API of `Complexitylib.Asymptotics.PolyBound`
to the register, word, marshalling, and running-time bounds of this simulation.
They live in the root `PolyBound` namespace so that dot notation reaches them. -/

namespace PolyBound

open RAM RAM.TMConfig.Sparse

private theorem size_le_self (value : ℕ) : value.size ≤ value := by
  rw [Nat.size_le]
  exact Nat.lt_pow_self (by decide)

theorem width {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun inputLength => bitlen (f inputLength) + 1) := by
  apply (hf.add (const 1)).mono
  intro inputLength
  simpa [bitlen] using Nat.add_le_add_right (size_le_self (f inputLength)) 1

theorem registerBound (workTapes : ℕ) {f : ℕ → ℕ}
    (hf : PolyBound f) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.registerBound workTapes (f inputLength)) := by
  have h := (((const (cellBase workTapes)).add
    (hf.mul (const (workTapes + 2)))).add (const (workTapes + 1))).add
      (const 1)
  simpa [RAM.TMConfig.Sparse.registerBound, cellReg, outputTape,
    Nat.add_assoc] using h

theorem wordBound (tm : TM n) {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.wordBound tm (f inputLength)) := by
  have hsucc := hf.add (const 1)
  have hregister := registerBound n hsucc
  have hcard := const (Fintype.card tm.Q)
  simpa only [RAM.TMConfig.Sparse.wordBound] using
    hregister.max (hcard.max hsucc)

theorem wordWidth (tm : TM n) {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.wordWidth tm (f inputLength)) := by
  simpa only [RAM.TMConfig.Sparse.wordWidth] using (wordBound tm hf).width

theorem marshalBaseBound (workTapes : ℕ) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalBaseBound workTapes inputLength) := by
  simpa only [RAM.TMConfig.Sparse.marshalBaseBound] using
    registerBound workTapes (id.add (const 1))

theorem marshalBound (workTapes : ℕ) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalBound workTapes inputLength) := by
  simpa only [RAM.TMConfig.Sparse.marshalBound] using
    (marshalBaseBound workTapes).add id

theorem marshalBaseWidth (workTapes : ℕ) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalBaseWidth workTapes inputLength) := by
  simpa only [RAM.TMConfig.Sparse.marshalBaseWidth] using
    (marshalBaseBound workTapes).width

theorem marshalWidth (workTapes : ℕ) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalWidth workTapes inputLength) := by
  simpa only [RAM.TMConfig.Sparse.marshalWidth] using
    (marshalBound workTapes).width

theorem marshalLoopTimeBound (workTapes : ℕ) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalLoopTimeBound workTapes inputLength) := by
  have hfactor := (id.mul (const
    (3 + 4 * (marshalLoopOps workTapes).length))).add (const 1)
  simpa only [RAM.TMConfig.Sparse.marshalLoopTimeBound] using
    hfactor.mul (marshalWidth workTapes)

theorem marshalLeafTimeBound (tm : TM n) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalLeafTimeBound tm inputLength) := by
  have hconstants := (const (4 * (marshalConstants n).length)).mul
    (marshalBaseWidth n)
  have hloop := marshalLoopTimeBound n
  have hword := wordWidth tm (marshalBound n)
  have hrepair := (const ((captureRegs n).length * 27)).mul hword
  have hinitialize := (const (4 * (initializeConfigOps tm).length)).mul hword
  simpa [RAM.TMConfig.Sparse.marshalLeafTimeBound, Nat.mul_assoc] using
    ((hconstants.add hloop).add hrepair).add hinitialize

theorem marshalTimeBound (tm : TM n) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.marshalTimeBound tm inputLength) := by
  have hcapture := (const (3 * (captureRegs n).length)).mul
    (wordWidth tm (marshalBound n))
  simpa only [RAM.TMConfig.Sparse.marshalTimeBound] using
    hcapture.add (marshalLeafTimeBound tm)

theorem decisionTimeBound (tm : TM n) {T : ℕ → ℕ} (hT : PolyBound T) :
    PolyBound (fun inputLength =>
      RAM.TMConfig.Sparse.decisionTimeBound tm inputLength (T inputLength)) := by
  have hbound := (marshalBound n).add hT
  have hword := wordWidth tm hbound
  have hrun := ((hT.add (const 1)).mul (const (runFactor tm))).mul hword
  have hextract := (const (4 * (extractVerdictOps n).length)).mul hword
  simpa [RAM.TMConfig.Sparse.decisionTimeBound, Nat.mul_assoc] using
    ((marshalTimeBound tm).add hrun).add hextract

end PolyBound

namespace RAM

namespace TMConfig

namespace Sparse

theorem P_subset_internal : Complexity.P ⊆ RAM.P := by
  intro L hL
  obtain ⟨workTapes, tm, p, hdecides⟩ :=
    mem_P_iff_decidesInTime_polynomial.mp hL
  have hram := compiledDecision_decidesInTime_internal hdecides
  obtain ⟨q, hq⟩ := PolyBound.decisionTimeBound tm (PolyBound.eval p)
  apply Set.mem_iUnion.mpr
  exact ⟨q.natDegree, compiledDecision tm,
    (fun inputLength => decisionTimeBound tm inputLength (p.eval inputLength)),
    hram, BigO.of_polynomial_bound q hq⟩

end Sparse

end TMConfig

end RAM

end Complexity
