/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Internal.Resources
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI.Defs

/-!
# Backward public-input copy -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- The backward-copy body always decrements its cursor and restores all four
loop constants, even when the cursor itself visits one of their registers. -/
theorem marshalLoopOps_control_internal (n : ℕ) (store : Structured.Store)
    (hcursor : 0 < store stateReg)
    (hzero : store (zeroReg n) = 0) :
    let final := Structured.Basic.execList (marshalLoopOps n) store
    final stateReg = store stateReg - 1 ∧
      final (zeroReg n) = 0 ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 ∧
      final (stateScratchReg n) = cellBase n ∧
      0 < final (cellReg n (inputTape n) (store stateReg)) := by
  let sourceAddressed :=
    (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
  let sourceLoaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
  let sourceCleared :=
    (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
  let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
  let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
  let counted := (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
  let based :=
    (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
  let encoded :=
    (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
  let multiplied :=
    (Structured.Basic.mul (addressReg n) stateReg (tapeCountReg n)).exec encoded
  let destinationAddressed :=
    (Structured.Basic.add (addressReg n) (addressReg n)
      (stateScratchReg n)).exec multiplied
  let destinationStored :=
    (Structured.Basic.store (addressReg n) (valueReg n)).exec
      destinationAddressed
  let final :=
    (Structured.Basic.sub stateReg stateReg (oneReg n)).exec destinationStored
  have hsourceAddress : sourceAddressed (addressReg n) = store stateReg := by
    simp [sourceAddressed, Structured.Basic.exec, hzero]
  have hsourceAddressZero : sourceAddressed (zeroReg n) = 0 := by
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hzero
  have hloadedAddress : sourceLoaded (addressReg n) = store stateReg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [addressReg, valueReg])]
    exact hsourceAddress
  have hloadedZero : sourceLoaded (zeroReg n) = 0 := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, valueReg])]
    exact hsourceAddressZero
  have hloadedState : sourceLoaded stateReg = store stateReg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, addressReg])]
  have hclearedState : sourceCleared stateReg = store stateReg := by
    simp only [sourceCleared, Structured.Basic.exec]
    have hne : stateReg ≠ sourceLoaded (addressReg n) := by
      have hpositive : 0 < sourceLoaded (addressReg n) := by
        rw [hloadedAddress]
        exact hcursor
      simp only [stateReg]
      omega
    rw [Function.update_of_ne hne]
    exact hloadedState
  have hbasedState : based stateReg = store stateReg := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, stateScratchReg]),
      Function.update_of_ne (by simp [stateReg, tapeCountReg]),
      Function.update_of_ne (by simp [stateReg, oneReg]),
      Function.update_of_ne (by simp [stateReg, zeroReg])]
    exact hclearedState
  have hbasedZero : based (zeroReg n) = 0 := by
    simp [based, counted, oned, zeroed, Structured.Basic.exec, zeroReg,
      oneReg, tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hbasedOne : based (oneReg n) = 1 := by
    simp [based, counted, oned, Structured.Basic.exec, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hbasedCount : based (tapeCountReg n) = n + 2 := by
    simp [based, counted, Structured.Basic.exec, tapeCountReg,
      stateScratchReg, Function.update_of_ne]
  have hbasedBase : based (stateScratchReg n) = cellBase n := by
    simp [based, Structured.Basic.exec]
  have hencodedState : encoded stateReg = store stateReg := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    exact hbasedState
  have hencodedZero : encoded (zeroReg n) = 0 := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, valueReg])]
    exact hbasedZero
  have hencodedOne : encoded (oneReg n) = 1 := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [oneReg, valueReg])]
    exact hbasedOne
  have hencodedCount : encoded (tapeCountReg n) = n + 2 := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, valueReg])]
    exact hbasedCount
  have hencodedBase : encoded (stateScratchReg n) = cellBase n := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, valueReg])]
    exact hbasedBase
  have hencodedValue : encoded (valueReg n) = based (valueReg n) + 1 := by
    simp [encoded, Structured.Basic.exec, hbasedOne]
  have hmultipliedAddress : multiplied (addressReg n) =
      store stateReg * (n + 2) := by
    simp [multiplied, Structured.Basic.exec, hencodedState, hencodedCount]
  have hmultipliedBase : multiplied (stateScratchReg n) = cellBase n := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, addressReg])]
    exact hencodedBase
  have hmultipliedValue : multiplied (valueReg n) =
      based (valueReg n) + 1 := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [valueReg, addressReg])]
    exact hencodedValue
  have hdestinationAddress : destinationAddressed (addressReg n) =
      store stateReg * (n + 2) + cellBase n := by
    simp [destinationAddressed, Structured.Basic.exec, hmultipliedAddress,
      hmultipliedBase]
  have htargetHigh : stateScratchReg n <
      store stateReg * (n + 2) + cellBase n := by
    simp [stateScratchReg, cellBase]
    omega
  have hstoredApply (reg : ℕ)
      (hreg : reg ≤ stateScratchReg n) :
      destinationStored reg = destinationAddressed reg := by
    simp only [destinationStored, Structured.Basic.exec]
    rw [Function.update_of_ne]
    intro heq
    rw [hdestinationAddress] at heq
    omega
  have hmultipliedState : multiplied stateReg = store stateReg := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, addressReg])]
    exact hencodedState
  have hmultipliedZero : multiplied (zeroReg n) = 0 := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hencodedZero
  have hmultipliedOne : multiplied (oneReg n) = 1 := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [oneReg, addressReg])]
    exact hencodedOne
  have hmultipliedCount : multiplied (tapeCountReg n) = n + 2 := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, addressReg])]
    exact hencodedCount
  have haddressedState : destinationAddressed stateReg = store stateReg := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, addressReg])]
    exact hmultipliedState
  have haddressedZero : destinationAddressed (zeroReg n) = 0 := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hmultipliedZero
  have haddressedOne : destinationAddressed (oneReg n) = 1 := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [oneReg, addressReg])]
    exact hmultipliedOne
  have haddressedCount : destinationAddressed (tapeCountReg n) = n + 2 := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, addressReg])]
    exact hmultipliedCount
  have haddressedBase : destinationAddressed (stateScratchReg n) = cellBase n := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, addressReg])]
    exact hmultipliedBase
  have haddressedValue : destinationAddressed (valueReg n) =
      based (valueReg n) + 1 := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [valueReg, addressReg])]
    exact hmultipliedValue
  have hstoredState : destinationStored stateReg = store stateReg := by
    rw [hstoredApply stateReg (by simp [stateReg, stateScratchReg]),
      haddressedState]
  have hstoredZero : destinationStored (zeroReg n) = 0 := by
    rw [hstoredApply (zeroReg n) (by simp [zeroReg, stateScratchReg]),
      haddressedZero]
  have hstoredOne : destinationStored (oneReg n) = 1 := by
    rw [hstoredApply (oneReg n) (by simp [oneReg, stateScratchReg]),
      haddressedOne]
  have hstoredCount : destinationStored (tapeCountReg n) = n + 2 := by
    rw [hstoredApply (tapeCountReg n) (by simp [tapeCountReg, stateScratchReg]),
      haddressedCount]
  have hstoredBase : destinationStored (stateScratchReg n) = cellBase n := by
    rw [hstoredApply (stateScratchReg n) le_rfl, haddressedBase]
  have hdestinationAddress' : destinationAddressed (addressReg n) =
      cellReg n (inputTape n) (store stateReg) := by
    rw [hdestinationAddress]
    simp [cellReg, inputTape]
    omega
  have hstoredDestination : destinationStored
      (cellReg n (inputTape n) (store stateReg)) =
        based (valueReg n) + 1 := by
    simp only [destinationStored, Structured.Basic.exec]
    rw [hdestinationAddress', Function.update_self, haddressedValue]
  have hfinalState : final stateReg = store stateReg - 1 := by
    simp [final, Structured.Basic.exec, hstoredState, hstoredOne]
  have hfinalZero : final (zeroReg n) = 0 := by
    simp only [final, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, stateReg])]
    exact hstoredZero
  have hfinalOne : final (oneReg n) = 1 := by
    simp only [final, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [oneReg, stateReg])]
    exact hstoredOne
  have hfinalCount : final (tapeCountReg n) = n + 2 := by
    simp only [final, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, stateReg])]
    exact hstoredCount
  have hfinalBase : final (stateScratchReg n) = cellBase n := by
    simp only [final, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, stateReg])]
    exact hstoredBase
  have hfinalDestination : 0 <
      final (cellReg n (inputTape n) (store stateReg)) := by
    simp only [final, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · rw [hstoredDestination]
      omega
    · simp [stateReg, cellReg, inputTape, cellBase]
  simpa [marshalLoopOps, sourceAddressed, sourceLoaded, sourceCleared,
    zeroed, oned, counted, based, encoded, multiplied, destinationAddressed,
    destinationStored, final] using!
    And.intro hfinalState (And.intro hfinalZero
      (And.intro hfinalOne
        (And.intro hfinalCount (And.intro hfinalBase hfinalDestination))))

/-- One backward-copy body has an exact structured execution. -/
theorem marshalLoopOps_exec_internal (n : ℕ) (store : Structured.Store) :
    ∃ cost space,
      Structured.Exec (.basics (marshalLoopOps n)) store
        (Structured.Basic.execList (marshalLoopOps n) store)
        (marshalLoopOps n).length cost space :=
  Structured.Internal.exec_basics_exists (marshalLoopOps n) store

/-- Away from the six captured scratch positions, one loop body clears the raw
source cell and writes its Boolean value, shifted to the sparse symbol code, to
the corresponding input cell. This is the relocation induction step. -/
theorem marshalLoopOps_data_internal (n : ℕ) (store : Structured.Store)
    (reg : ℕ) (hcursor : 0 < store stateReg)
    (hzero : store (zeroReg n) = 0)
    (hfree : store stateReg ∉ captureRegs n)
    (hdata : cellBase n ≤ reg) :
    Structured.Basic.execList (marshalLoopOps n) store reg =
      Function.update
        (Function.update store (store stateReg) 0)
        (cellReg n (inputTape n) (store stateReg))
        (store (store stateReg) + 1) reg := by
  have hcursorAddress : store stateReg ≠ addressReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hcursorValue : store stateReg ≠ valueReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  let sourceAddressed :=
    (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
  let sourceLoaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
  let sourceCleared :=
    (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
  let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
  let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
  let counted := (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
  let based :=
    (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
  let encoded :=
    (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
  let multiplied :=
    (Structured.Basic.mul (addressReg n) stateReg (tapeCountReg n)).exec encoded
  let destinationAddressed :=
    (Structured.Basic.add (addressReg n) (addressReg n)
      (stateScratchReg n)).exec multiplied
  let destinationStored :=
    (Structured.Basic.store (addressReg n) (valueReg n)).exec
      destinationAddressed
  let final :=
    (Structured.Basic.sub stateReg stateReg (oneReg n)).exec destinationStored
  have hsourceAddress : sourceAddressed (addressReg n) = store stateReg := by
    simp [sourceAddressed, Structured.Basic.exec, hzero]
  have hsourceCursor : sourceAddressed (store stateReg) =
      store (store stateReg) := by
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne hcursorAddress]
  have hloadedValue : sourceLoaded (valueReg n) = store (store stateReg) := by
    simp [sourceLoaded, Structured.Basic.exec, hsourceAddress, hsourceCursor]
  have hloadedAddress : sourceLoaded (addressReg n) = store stateReg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [addressReg, valueReg])]
    exact hsourceAddress
  have hloadedZero : sourceLoaded (zeroReg n) = 0 := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, valueReg])]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hzero
  have hclearedState : sourceCleared stateReg = store stateReg := by
    simp only [sourceCleared, Structured.Basic.exec]
    have hne : stateReg ≠ sourceLoaded (addressReg n) := by
      rw [hloadedAddress]
      simpa [stateReg] using (Nat.ne_of_lt hcursor)
    rw [Function.update_of_ne hne]
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, addressReg])]
  have hclearedValue : sourceCleared (valueReg n) =
      store (store stateReg) := by
    simp only [sourceCleared, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · exact hloadedValue
    · rw [hloadedAddress]
      exact Ne.symm hcursorValue
  have hbasedState : based stateReg = store stateReg := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, stateScratchReg]),
      Function.update_of_ne (by simp [stateReg, tapeCountReg]),
      Function.update_of_ne (by simp [stateReg, oneReg]),
      Function.update_of_ne (by simp [stateReg, zeroReg])]
    exact hclearedState
  have hbasedCount : based (tapeCountReg n) = n + 2 := by
    simp [based, counted, Structured.Basic.exec, tapeCountReg,
      stateScratchReg, Function.update_of_ne]
  have hbasedBase : based (stateScratchReg n) = cellBase n := by
    simp [based, Structured.Basic.exec]
  have hbasedOne : based (oneReg n) = 1 := by
    simp [based, counted, oned, Structured.Basic.exec, oneReg,
      tapeCountReg, stateScratchReg, Function.update_of_ne]
  have hbasedValue : based (valueReg n) = store (store stateReg) := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [valueReg, stateScratchReg]),
      Function.update_of_ne (by simp [valueReg, tapeCountReg]),
      Function.update_of_ne (by simp [valueReg, oneReg]),
      Function.update_of_ne (by simp [valueReg, zeroReg])]
    exact hclearedValue
  have hencodedState : encoded stateReg = store stateReg := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    exact hbasedState
  have hencodedCount : encoded (tapeCountReg n) = n + 2 := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, valueReg])]
    exact hbasedCount
  have hencodedBase : encoded (stateScratchReg n) = cellBase n := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, valueReg])]
    exact hbasedBase
  have hencodedValue : encoded (valueReg n) =
      store (store stateReg) + 1 := by
    simp [encoded, Structured.Basic.exec, hbasedValue, hbasedOne]
  have hmultipliedAddress : multiplied (addressReg n) =
      store stateReg * (n + 2) := by
    simp [multiplied, Structured.Basic.exec, hencodedState, hencodedCount]
  have hmultipliedBase : multiplied (stateScratchReg n) = cellBase n := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, addressReg])]
    exact hencodedBase
  have hmultipliedValue : multiplied (valueReg n) =
      store (store stateReg) + 1 := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [valueReg, addressReg])]
    exact hencodedValue
  have hdestinationAddress : destinationAddressed (addressReg n) =
      cellReg n (inputTape n) (store stateReg) := by
    simp [destinationAddressed, Structured.Basic.exec, hmultipliedAddress,
      hmultipliedBase, cellReg, inputTape]
    omega
  have hdestinationValue : destinationAddressed (valueReg n) =
      store (store stateReg) + 1 := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [valueReg, addressReg])]
    exact hmultipliedValue
  have hregState : reg ≠ stateReg := by
    intro heq
    rw [heq] at hdata
    simp [stateReg, cellBase] at hdata
  have hregAddress : reg ≠ addressReg n := by
    intro heq
    rw [heq] at hdata
    simp [addressReg, cellBase] at hdata
    omega
  have hregValue : reg ≠ valueReg n := by
    intro heq
    rw [heq] at hdata
    simp [valueReg, cellBase] at hdata
    omega
  have hregZero : reg ≠ zeroReg n := by
    intro heq
    rw [heq] at hdata
    simp [zeroReg, cellBase] at hdata
    omega
  have hregOne : reg ≠ oneReg n := by
    intro heq
    rw [heq] at hdata
    simp [oneReg, cellBase] at hdata
    omega
  have hregCount : reg ≠ tapeCountReg n := by
    intro heq
    rw [heq] at hdata
    simp [tapeCountReg, cellBase] at hdata
    omega
  have hregBase : reg ≠ stateScratchReg n := by
    intro heq
    rw [heq] at hdata
    simp [stateScratchReg, cellBase] at hdata
    omega
  have hloadedData : sourceLoaded reg = store reg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne hregValue]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
  have hclearedData : sourceCleared reg =
      Function.update store (store stateReg) 0 reg := by
    simp only [sourceCleared, Structured.Basic.exec]
    rw [hloadedAddress, hloadedZero]
    by_cases heq : reg = store stateReg
    · subst reg
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq, Function.update_of_ne heq]
      exact hloadedData
  have hbasedData : based reg =
      Function.update store (store stateReg) 0 reg := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne hregBase, Function.update_of_ne hregCount,
      Function.update_of_ne hregOne, Function.update_of_ne hregZero]
    exact hclearedData
  have hencodedData : encoded reg =
      Function.update store (store stateReg) 0 reg := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne hregValue]
    exact hbasedData
  have hmultipliedData : multiplied reg =
      Function.update store (store stateReg) 0 reg := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
    exact hencodedData
  have haddressedData : destinationAddressed reg =
      Function.update store (store stateReg) 0 reg := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
    exact hmultipliedData
  change final reg = _
  simp only [final, Structured.Basic.exec]
  rw [Function.update_of_ne hregState]
  simp only [destinationStored, Structured.Basic.exec]
  rw [hdestinationAddress, hdestinationValue]
  by_cases heq : reg = cellReg n (inputTape n) (store stateReg)
  · subst reg
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne heq, Function.update_of_ne heq]
    exact haddressedData

/-- Apart from the raw source, sparse destination, state, and six scratch
registers, a loop body preserves every register. This form does not assume that
the cursor avoids scratch, so it carries both future raw sources and previously
relocated cells across captured iterations. -/
theorem marshalLoopOps_of_ne_internal (n : ℕ)
    (store : Structured.Store) (reg : ℕ)
    (hcursor : 0 < store stateReg)
    (hzero : store (zeroReg n) = 0)
    (hstate : reg ≠ stateReg)
    (hfree : reg ∉ captureRegs n)
    (hsource : reg ≠ store stateReg)
    (hdestination :
      reg ≠ cellReg n (inputTape n) (store stateReg)) :
    Structured.Basic.execList (marshalLoopOps n) store reg = store reg := by
  let sourceAddressed :=
    (Structured.Basic.add (addressReg n) stateReg (zeroReg n)).exec store
  let sourceLoaded :=
    (Structured.Basic.load (valueReg n) (addressReg n)).exec sourceAddressed
  let sourceCleared :=
    (Structured.Basic.store (addressReg n) (zeroReg n)).exec sourceLoaded
  let zeroed := (Structured.Basic.imm (zeroReg n) 0).exec sourceCleared
  let oned := (Structured.Basic.imm (oneReg n) 1).exec zeroed
  let counted := (Structured.Basic.imm (tapeCountReg n) (n + 2)).exec oned
  let based :=
    (Structured.Basic.imm (stateScratchReg n) (cellBase n)).exec counted
  let encoded :=
    (Structured.Basic.add (valueReg n) (valueReg n) (oneReg n)).exec based
  let multiplied :=
    (Structured.Basic.mul (addressReg n) stateReg (tapeCountReg n)).exec encoded
  let destinationAddressed :=
    (Structured.Basic.add (addressReg n) (addressReg n)
      (stateScratchReg n)).exec multiplied
  let destinationStored :=
    (Structured.Basic.store (addressReg n) (valueReg n)).exec
      destinationAddressed
  let final :=
    (Structured.Basic.sub stateReg stateReg (oneReg n)).exec destinationStored
  have hsourceAddress : sourceAddressed (addressReg n) = store stateReg := by
    simp [sourceAddressed, Structured.Basic.exec, hzero]
  have hloadedAddress : sourceLoaded (addressReg n) = store stateReg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [addressReg, valueReg])]
    exact hsourceAddress
  have hloadedZero : sourceLoaded (zeroReg n) = 0 := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, valueReg])]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [zeroReg, addressReg])]
    exact hzero
  have hclearedState : sourceCleared stateReg = store stateReg := by
    simp only [sourceCleared, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · simp only [sourceLoaded, Structured.Basic.exec]
      rw [Function.update_of_ne (by simp [stateReg, valueReg])]
      simp only [sourceAddressed, Structured.Basic.exec]
      rw [Function.update_of_ne (by simp [stateReg, addressReg])]
    · rw [hloadedAddress]
      simpa [stateReg] using (Nat.ne_of_lt hcursor)
  have hbasedState : based stateReg = store stateReg := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, stateScratchReg]),
      Function.update_of_ne (by simp [stateReg, tapeCountReg]),
      Function.update_of_ne (by simp [stateReg, oneReg]),
      Function.update_of_ne (by simp [stateReg, zeroReg])]
    exact hclearedState
  have hbasedCount : based (tapeCountReg n) = n + 2 := by
    simp [based, counted, Structured.Basic.exec, tapeCountReg,
      stateScratchReg, Function.update_of_ne]
  have hbasedBase : based (stateScratchReg n) = cellBase n := by
    simp [based, Structured.Basic.exec]
  have hencodedState : encoded stateReg = store stateReg := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateReg, valueReg])]
    exact hbasedState
  have hencodedCount : encoded (tapeCountReg n) = n + 2 := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [tapeCountReg, valueReg])]
    exact hbasedCount
  have hencodedBase : encoded (stateScratchReg n) = cellBase n := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, valueReg])]
    exact hbasedBase
  have hmultipliedAddress : multiplied (addressReg n) =
      store stateReg * (n + 2) := by
    simp [multiplied, Structured.Basic.exec, hencodedState, hencodedCount]
  have hmultipliedBase : multiplied (stateScratchReg n) = cellBase n := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne (by simp [stateScratchReg, addressReg])]
    exact hencodedBase
  have hdestinationAddress : destinationAddressed (addressReg n) =
      cellReg n (inputTape n) (store stateReg) := by
    simp [destinationAddressed, Structured.Basic.exec, hmultipliedAddress,
      hmultipliedBase, cellReg, inputTape]
    omega
  have hregState : reg ≠ stateReg := hstate
  have hregAddress : reg ≠ addressReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hregValue : reg ≠ valueReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hregZero : reg ≠ zeroReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hregOne : reg ≠ oneReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hregCount : reg ≠ tapeCountReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hregBase : reg ≠ stateScratchReg n := by
    intro heq
    apply hfree
    simp [captureRegs, heq]
  have hloadedData : sourceLoaded reg = store reg := by
    simp only [sourceLoaded, Structured.Basic.exec]
    rw [Function.update_of_ne hregValue]
    simp only [sourceAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
  have hclearedData : sourceCleared reg = store reg := by
    simp only [sourceCleared, Structured.Basic.exec]
    rw [Function.update_of_ne]
    · exact hloadedData
    · rw [hloadedAddress]
      exact hsource
  have hbasedData : based reg = store reg := by
    simp only [based, counted, oned, zeroed, Structured.Basic.exec]
    rw [Function.update_of_ne hregBase, Function.update_of_ne hregCount,
      Function.update_of_ne hregOne, Function.update_of_ne hregZero]
    exact hclearedData
  have hencodedData : encoded reg = store reg := by
    simp only [encoded, Structured.Basic.exec]
    rw [Function.update_of_ne hregValue]
    exact hbasedData
  have hmultipliedData : multiplied reg = store reg := by
    simp only [multiplied, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
    exact hencodedData
  have haddressedData : destinationAddressed reg = store reg := by
    simp only [destinationAddressed, Structured.Basic.exec]
    rw [Function.update_of_ne hregAddress]
    exact hmultipliedData
  change final reg = store reg
  simp only [final, Structured.Basic.exec]
  rw [Function.update_of_ne hregState]
  simp only [destinationStored, Structured.Basic.exec]
  rw [hdestinationAddress, Function.update_of_ne hdestination]
  exact haddressedData

/-- The backward-copy loop executes exactly once per raw input cell and exits
with cursor zero and all constants restored. -/
theorem marshalLoop_exec_internal (n cursor : ℕ)
    (store : Structured.Store)
    (hcursor : store stateReg = cursor)
    (hzero : store (zeroReg n) = 0)
    (hone : store (oneReg n) = 1)
    (hcount : store (tapeCountReg n) = n + 2)
    (hbase : store (stateScratchReg n) = cellBase n) :
    ∃ final cost space,
      Structured.Exec (marshalLoop n) store final
        (marshalLoopSteps n cursor) cost space ∧
      final stateReg = 0 ∧
      final (zeroReg n) = 0 ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 ∧
      final (stateScratchReg n) = cellBase n := by
  induction cursor generalizing store with
  | zero =>
      have hcursorZero : store stateReg = 0 := by simpa using hcursor
      refine ⟨store, bitlen (store stateReg) + 1, store.space, ?_,
        hcursorZero, hzero, hone, hcount, hbase⟩
      simpa [marshalLoop, marshalLoopSteps] using
        (Structured.Exec.whileZero
          (body := .basics (marshalLoopOps n)) hcursorZero)
  | succ cursor ih =>
      have hpositive : 0 < store stateReg := by omega
      have hnonzero : store stateReg ≠ 0 := by omega
      let middle := Structured.Basic.execList (marshalLoopOps n) store
      obtain ⟨bodyCost, bodySpace, hbody⟩ :=
        marshalLoopOps_exec_internal n store
      have hcontrol := marshalLoopOps_control_internal n store hpositive hzero
      have hmiddleCursor : middle stateReg = cursor := by
        change Structured.Basic.execList (marshalLoopOps n) store stateReg = cursor
        rw [hcontrol.1, hcursor]
        omega
      obtain ⟨final, loopCost, loopSpace, hloop, hfinalCursor,
          hfinalZero, hfinalOne, hfinalCount, hfinalBase⟩ :=
        ih middle hmiddleCursor hcontrol.2.1 hcontrol.2.2.1
          hcontrol.2.2.2.1 hcontrol.2.2.2.2.1
      refine ⟨final,
        bitlen (store stateReg) + 1 + bodyCost + 1 + loopCost,
        max bodySpace loopSpace, ?_, hfinalCursor, hfinalZero, hfinalOne,
        hfinalCount, hfinalBase⟩
      have hexec := Structured.Exec.whileNonzero hnonzero hbody hloop
      convert! hexec using 1
      simp [marshalLoopSteps, Nat.succ_mul]
      omega

end Sparse

end TMConfig

end RAM

end Complexity
