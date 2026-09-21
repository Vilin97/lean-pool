/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Internal

/-!
# Dense public-input lookup

This module exposes the fixed leaves used to look through a sparse tagged
overlay into the immutable public-input bank.
-/


public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- The direct-branch identity leaf preserves a fully parked frame exactly. -/
theorem denseInputIdleTM_reachesIn_frame {n : ℕ}
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∃ c',
      (denseInputIdleTM (n := n)).reachesIn 1
        { state := (denseInputIdleTM (n := n)).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (denseInputIdleTM (n := n)).halted c' ∧
      c'.input = inp₀ ∧ c'.work = work₀ ∧ c'.output = out₀ :=
  denseInputIdleTM_reachesIn_frame_internal inp₀ work₀ out₀
    hinput hwork houtput

/-- Copy the preceding Boolean input symbol into one canonical work tape and
restore the read-only input head in exactly two transitions. -/
theorem capturePreviousInputBitTM_reachesIn_frame {n : ℕ}
    (result : Fin n) (bit : Bool) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.StartInvariant) (hhead : 2 ≤ inp₀.head)
    (hbit : inp₀.cells (inp₀.head - 1) = Γ.ofBool bit)
    (hresult : work₀ result = TM.resetBinaryBlank)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    ∃ c',
      (capturePreviousInputBitTM result).reachesIn 2
        { state := (capturePreviousInputBitTM result).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (capturePreviousInputBitTM result).halted c' ∧
      c'.input = inp₀ ∧
      c'.work = Function.update work₀ result (denseInputBitTape bit) ∧
      c'.output = out₀ :=
  capturePreviousInputBitTM_reachesIn_frame_internal result bit inp₀
    work₀ out₀ hinput hhead hbit hresult hwork houtput

/-- The canonical captured-bit tape represents exactly zero or one. -/
theorem denseInputBitTape_hasBinaryNat (bit : Bool) :
    (denseInputBitTape bit).HasBinaryNat (if bit then 1 else 0) :=
  denseInputBitTape_hasBinaryNat_internal bit

/-- Every captured-bit tape is parked at its first data cell. -/
theorem denseInputBitTape_parked (bit : Bool) :
    TM.Parked (denseInputBitTape bit) :=
  denseInputBitTape_parked_internal bit

/-- One scan body step decrements a positive countdown, captures the preceding
input bit exactly when the countdown reaches zero, and preserves every frame. -/
theorem denseInputStepTM_reachesIn_frame {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (remaining : ℕ) (bit : Bool) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.StartInvariant) (hhead : 2 ≤ inp₀.head)
    (hbit : inp₀.cells (inp₀.head - 1) = Γ.ofBool bit)
    (hcounter : (work₀ counter).HasBinaryNat remaining)
    (hresult : remaining = 1 → work₀ result = TM.resetBinaryBlank)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    ∃ c',
      (denseInputStepTM counter result).reachesIn
        (denseInputStepTime remaining)
        { state := (denseInputStepTM counter result).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (denseInputStepTM counter result).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work counter).HasBinaryNat (remaining - 1) ∧
      c'.work result = denseInputStepResult remaining bit (work₀ result) ∧
      (∀ i, i ≠ counter → i ≠ result → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  denseInputStepTM_reachesIn_frame_internal counter result hne remaining bit
    inp₀ work₀ out₀ hinput hhead hbit hcounter hresult hwork houtput

/-- A positive RAM address can be looked up by one exact scan of the immutable
input bank. The scanner leaves the input contents unchanged, parks at the first
blank, decrements its counter once per bit, and returns `RAM.initRegs`. -/
theorem denseInputScanTM_reachesIn_frame {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (input : List Bool) (address : ℕ) (work₀ : Fin n → Tape)
    (out₀ : Tape) (haddress : address ≠ 0)
    (hcounter : (work₀ counter).HasBinaryNat address)
    (hresult : work₀ result = TM.resetBinaryBlank)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    ∃ c',
      (denseInputScanTM counter result).reachesIn
        (denseInputScanTime input.length address)
        { state := (denseInputScanTM counter result).qstart
          input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
          work := work₀
          output := out₀ } c' ∧
      (denseInputScanTM counter result).halted c' ∧
      c'.input.head = input.length + 1 ∧
      c'.input.cells = (Tape.init (input.map Γ.ofBool)).cells ∧
      (c'.work counter).HasBinaryNat (address - input.length) ∧
      (c'.work result).HasBinaryNat (Complexity.RAM.initRegs input address) ∧
      (∀ i, i ≠ counter → i ≠ result → c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  denseInputScanTM_reachesIn_frame_internal counter result hne input address
    work₀ out₀ haddress hcounter hresult hwork houtput

/-- Dense-bank lookup is linear in the public-input length and logarithmic in
the queried positive address. -/
theorem denseInputScanTime_le_width (inputLength address : ℕ) :
    denseInputScanTime inputLength address ≤
      inputLength * (2 * address.size + 9) + 1 :=
  denseInputScanTime_le_width_internal inputLength address

/-- Full dense-bank fallback preserves the query and scratch tapes, restores
the input head and countdown tape, and returns the standard RAM input value. -/
theorem denseInputLookupTM_hoareTime {n : ℕ}
    (query counter result scratch : Fin n)
    (hqc : query ≠ counter) (hqr : query ≠ result)
    (hqs : query ≠ scratch) (hcr : counter ≠ result)
    (hcs : counter ≠ scratch) (hrs : result ≠ scratch)
    (input : List Bool) (address : ℕ) (initialWork : Fin n → Tape)
    (out₀ : Tape) (haddress : address ≠ 0)
    (hready : DenseInputLookupReady query counter result scratch address
      initialWork)
    (houtput : TM.Parked out₀) :
    (denseInputLookupTM query counter result scratch).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        DenseInputLookupResult query counter result scratch input address
          initialWork work ∧
        out = out₀)
      (denseInputLookupTime input.length address) :=
  denseInputLookupTM_hoareTime_internal query counter result scratch
    hqc hqr hqs hcr hcs hrs input address initialWork out₀ haddress
    hready houtput

end Machine
end RegisterStore
end RAM
end Complexity
