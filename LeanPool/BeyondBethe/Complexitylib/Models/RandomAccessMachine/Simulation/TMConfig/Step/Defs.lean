/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Defs

/-!
# A fixed structured-RAM block for one Turing-machine transition

The finite transition function is compiled as a decision tree. The program
first loads the symbols under all named heads, dispatches on the finite-state
code and the `n + 2` four-symbol codes, then performs the selected transition
using indirect stores into the bounded tape blocks.

The construction is fixed once `tm` and the cell-window bound are fixed. It
does not install or consult an untrusted transition-table oracle.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Step


/-- Input tape index. -/
def inputTape (n : ℕ) : Fin (n + 2) := ⟨0, by omega⟩

/-- Work-tape index in the named input/work/output order. -/
def workTape (i : Fin n) : Fin (n + 2) := ⟨i.val + 1, by omega⟩

/-- Output tape index. -/
def outputTape (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

/-- Direct head register for one named tape. -/
def headReg (tape : Fin (n + 2)) : ℕ := 1 + tape.val

/-- First cell register of one named tape's bounded block. -/
def cellBase (n bound : ℕ) (tape : Fin (n + 2)) : ℕ :=
  1 + (n + 2) + tape.val * (bound + 1)

/-- First scratch register beyond the represented configuration. -/
def scratchBase (n bound : ℕ) : ℕ := registerCount n bound

/-- Constant-zero scratch register. -/
def zeroReg (n bound : ℕ) : ℕ := scratchBase n bound

/-- Constant-one scratch register used by decrementing switches and head moves. -/
def oneReg (n bound : ℕ) : ℕ := scratchBase n bound + 1

/-- Destructive copy of the finite-state code used by the outer switch. -/
def stateScratchReg (n bound : ℕ) : ℕ := scratchBase n bound + 2

/-- Scratch register holding an indirect cell address. -/
def addressReg (n bound : ℕ) : ℕ := scratchBase n bound + 3

/-- Scratch register holding a writable symbol code. -/
def valueReg (n bound : ℕ) : ℕ := scratchBase n bound + 4

/-- Scratch register holding the symbol loaded under one named head. -/
def symbolReg (n bound : ℕ) (tape : Fin (n + 2)) : ℕ :=
  scratchBase n bound + 5 + tape.val

/-- Exclusive upper bound on every configuration and scratch register. -/
def registerLimit (n bound : ℕ) : ℕ := scratchBase n bound + n + 7

/-- A uniform value bound large enough for addresses, states, symbols, and a
single rightward head move. -/
def wordBound (tm : TM n) (bound : ℕ) : ℕ :=
  max (registerLimit n bound) (max (Fintype.card tm.Q) (bound + 1))

/-- One-bit-cushioned width used in logarithmic-cost bounds. -/
def wordWidth (tm : TM n) (bound : ℕ) : ℕ :=
  bitlen (wordBound tm bound) + 1

/-- Peak-space envelope for one transition block. -/
def spaceBound (tm : TM n) (bound : ℕ) : ℕ :=
  registerLimit n bound *
    (bitlen (registerLimit n bound) + bitlen (wordBound tm bound))

/-- A store fits the explicit register/value envelope used by one transition
block. This public predicate states the concrete boundary directly without
exposing the internal resource-certificate structure. -/
def StoreBounded (tm : TM n) (bound : ℕ) (store : Structured.Store) : Prop :=
  (∀ reg, store reg ≠ 0 → reg < registerLimit n bound) ∧
    ∀ reg, store reg ≤ wordBound tm bound

/-- Decode one valid four-way switch branch as a tape symbol. -/
def symbolAt (code : Fin 4) : Γ := symbolDecode code.val

/-- Symbols currently read by all named TM heads. -/
def readSymbols (cfg : Complexity.Cfg n Q) : Fin (n + 2) → Γ :=
  fun tape => (tapeAt cfg tape).read

/-- Load the symbol under one represented head into its dedicated scratch
register. -/
def loadTapeOps (n bound : ℕ) (tape : Fin (n + 2)) : List Structured.Basic :=
  [.imm (addressReg n bound) (cellBase n bound tape),
    .add (addressReg n bound) (addressReg n bound) (headReg tape),
    .load (symbolReg n bound tape) (addressReg n bound)]

/-- Initialize constants and copy the represented finite-state code. -/
def setupOps (n bound : ℕ) : List Structured.Basic :=
  [.imm (zeroReg n bound) 0,
    .imm (oneReg n bound) 1,
    .add (stateScratchReg n bound) 0 (zeroReg n bound)]

/-- Initialize scratch state and load every represented head symbol. -/
def loadOps (n bound : ℕ) : List Structured.Basic :=
  setupOps n bound ++
    (List.finRange (n + 2)).flatMap (loadTapeOps n bound)

/-- Encode a writable tape symbol with the same zero-blank convention as the
configuration representation. -/
def writeCode (symbol : Γw) : ℕ := symbolCode symbol.toΓ

/-- Update a represented head in the indicated direction. -/
def moveOps (n bound : ℕ) (tape : Fin (n + 2)) : Dir3 → List Structured.Basic
  | .left => [.sub (headReg tape) (headReg tape) (oneReg n bound)]
  | .right => [.add (headReg tape) (headReg tape) (oneReg n bound)]
  | .stay => []

/-- Write one represented work/output tape and restore the left-end marker. -/
def writeOps (n bound : ℕ) (tape : Fin (n + 2))
    (write : Γw) : List Structured.Basic :=
  [.imm (addressReg n bound) (cellBase n bound tape),
    .add (addressReg n bound) (addressReg n bound) (headReg tape),
    .imm (valueReg n bound) (writeCode write),
    .store (addressReg n bound) (valueReg n bound),
    .imm (cellBase n bound tape) (symbolCode Γ.start)]

/-- Write one represented work/output tape and move its head.

The direct write restoring cell zero to `▷` makes this branch-free while
matching `Tape.write`, whose write at head zero is a no-op. -/
def writeMoveOps (n bound : ℕ) (tape : Fin (n + 2))
    (write : Γw) (direction : Dir3) : List Structured.Basic :=
  writeOps n bound tape write ++ moveOps n bound tape direction

/-- Straight-line register operations implementing a statically selected TM
transition case. -/
noncomputable def actionOps (tm : TM n) (bound : ℕ) (state : tm.Q)
    (symbols : Fin (n + 2) → Γ) : List Structured.Basic :=
  match tm.δ state (symbols (inputTape n))
      (fun i => symbols (workTape i)) (symbols (outputTape n)) with
  | (nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection) =>
      [.imm 0 (stateCode tm nextState)] ++
        moveOps n bound (inputTape n) inputDirection ++
        (List.finRange n).flatMap (fun i =>
          writeMoveOps n bound (workTape i) (workWrites i) (workDirections i)) ++
        writeMoveOps n bound (outputTape n) outputWrite outputDirection

/-- Structured command for one statically selected transition case. -/
noncomputable def action (tm : TM n) (bound : ℕ) (state : tm.Q)
    (symbols : Fin (n + 2) → Γ) : Structured.Cmd :=
  Structured.Cmd.basics (actionOps tm bound state symbols)

/-- Recursively dispatch on the loaded symbols for the listed named tapes. -/
noncomputable def dispatchSymbols (tm : TM n) (bound : ℕ) (state : tm.Q) :
    List (Fin (n + 2)) → (Fin (n + 2) → Γ) → Structured.Cmd
  | [], symbols => action tm bound state symbols
  | tape :: rest, symbols =>
      Structured.Switch.select 4 (symbolReg n bound tape) (oneReg n bound)
        (fun code => dispatchSymbols tm bound state rest
          (Function.update symbols tape (symbolAt code)))

/-- Dispatch on the finite-state code, then on every loaded tape symbol. -/
noncomputable def dispatchState (tm : TM n) (bound : ℕ) : Structured.Cmd :=
  Structured.Switch.select (Fintype.card tm.Q) (stateScratchReg n bound)
    (oneReg n bound) (fun stateCode =>
      dispatchSymbols tm bound ((Fintype.equivFin tm.Q).symm stateCode)
        (List.finRange (n + 2)) (fun _ => Γ.blank))

/-- Fixed structured-RAM program implementing one nonhalting TM transition. -/
noncomputable def program (tm : TM n) (bound : ℕ) : Structured.Cmd :=
  .seq (.basics (loadOps n bound)) (dispatchState tm bound)

/-- Concrete compiled RAM block for one nonhalting TM transition. -/
noncomputable def compiled (tm : TM n) (bound : ℕ) : Program :=
  (program tm bound).compile

/-- Exact transition count through symbol dispatch for the actually read case. -/
noncomputable def dispatchSteps (tm : TM n) (bound : ℕ) (state : tm.Q)
    (actual : Fin (n + 2) → Γ) : List (Fin (n + 2)) → ℕ
  | [] => (actionOps tm bound state actual).length
  | tape :: rest => Structured.Switch.stepCount (symbolCode (actual tape))
      (dispatchSteps tm bound state actual rest)

/-- Exact source/compiled transition count for one represented TM step. -/
noncomputable def stepCount (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  (loadOps n bound).length +
    Structured.Switch.stepCount (stateCode tm cfg.state)
      (dispatchSteps tm bound cfg.state (readSymbols cfg)
        (List.finRange (n + 2)))

/-- Logarithmic-cost bound through symbol dispatch. -/
noncomputable def dispatchCost (tm : TM n) (bound : ℕ) (state : tm.Q)
    (actual : Fin (n + 2) → Γ) : List (Fin (n + 2)) → ℕ
  | [] => 4 * (actionOps tm bound state actual).length * wordWidth tm bound
  | tape :: rest => Structured.Switch.costBound (symbolCode (actual tape))
      (dispatchCost tm bound state actual rest) (wordWidth tm bound)

/-- Explicit logarithmic-cost bound for one represented TM step. -/
noncomputable def timeBound (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  4 * (loadOps n bound).length * wordWidth tm bound +
    Structured.Switch.costBound (stateCode tm cfg.state)
      (dispatchCost tm bound cfg.state (readSymbols cfg)
        (List.finRange (n + 2))) (wordWidth tm bound)

end Step

end TMConfig

end RAM

end Complexity
