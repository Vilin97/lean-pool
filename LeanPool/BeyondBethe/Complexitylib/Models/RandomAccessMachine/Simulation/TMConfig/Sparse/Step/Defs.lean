/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Defs

/-!
# A fixed sparse-RAM block for one Turing-machine transition

Unlike the bounded dense block, this program is determined solely by `tm`.
It computes an interleaved tape-cell address as
`cellBase + head * (n + 2) + tape`, so the same finite RAM program can follow
an unbounded computation.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Input tape slot. -/
def inputTape (n : ℕ) : Fin (n + 2) := ⟨0, by omega⟩

/-- Work-tape slot. -/
def workTape (i : Fin n) : Fin (n + 2) := ⟨i.val + 1, by omega⟩

/-- Output tape slot. -/
def outputTape (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

/-- Symbols currently read by all named TM heads. -/
def readSymbols (cfg : Complexity.Cfg n Q) : Fin (n + 2) → Γ :=
  fun tape => (tapeAt cfg tape).read

/-- Compute the indirect address of the cell under one named head. `valueReg`
temporarily holds the tape-specific base constant. -/
def addressOps (n : ℕ) (tape : Fin (n + 2)) : List Structured.Basic :=
  [.imm (valueReg n) (cellBase n + tape.val),
    .mul (addressReg n) (headReg tape) (tapeCountReg n),
    .add (addressReg n) (addressReg n) (valueReg n)]

/-- Load the symbol under one named head. -/
def loadTapeOps (n : ℕ) (tape : Fin (n + 2)) : List Structured.Basic :=
  addressOps n tape ++ [.load (symbolReg n tape) (addressReg n)]

/-- Initialize fixed constants and copy the finite-state code. -/
def setupOps (n : ℕ) : List Structured.Basic :=
  [.imm (zeroReg n) 0,
    .imm (oneReg n) 1,
    .imm (tapeCountReg n) (n + 2),
    .add (stateScratchReg n) stateReg (zeroReg n)]

/-- Initialize scratch state and load every named head symbol. -/
def loadOps (n : ℕ) : List Structured.Basic :=
  setupOps n ++ (List.finRange (n + 2)).flatMap (loadTapeOps n)

/-- Update one represented head. -/
def moveOps (n : ℕ) (tape : Fin (n + 2)) : Dir3 → List Structured.Basic
  | .left => [.sub (headReg tape) (headReg tape) (oneReg n)]
  | .right => [.add (headReg tape) (headReg tape) (oneReg n)]
  | .stay => []

/-- Write the cell under one represented head and restore its immutable cell
zero to the left-end marker. -/
def writeOps (n : ℕ) (tape : Fin (n + 2)) (write : Γw) :
    List Structured.Basic :=
  addressOps n tape ++
    [.imm (valueReg n) (symbolCode write.toΓ),
      .store (addressReg n) (valueReg n),
      .imm (cellReg n tape 0) (symbolCode Γ.start)]

/-- Write and move one represented work/output tape. -/
def writeMoveOps (n : ℕ) (tape : Fin (n + 2))
    (write : Γw) (direction : Dir3) : List Structured.Basic :=
  writeOps n tape write ++ moveOps n tape direction

/-- Straight-line operations for one statically selected transition. -/
noncomputable def actionOps (tm : TM n) (state : tm.Q)
    (symbols : Fin (n + 2) → Γ) : List Structured.Basic :=
  match tm.δ state (symbols (inputTape n))
      (fun i => symbols (workTape i)) (symbols (outputTape n)) with
  | (nextState, workWrites, outputWrite, inputDirection,
      workDirections, outputDirection) =>
      [.imm stateReg (stateCode tm nextState)] ++
        moveOps n (inputTape n) inputDirection ++
        (List.finRange n).flatMap (fun i =>
          writeMoveOps n (workTape i) (workWrites i) (workDirections i)) ++
        writeMoveOps n (outputTape n) outputWrite outputDirection

/-- Structured selected-transition command. -/
noncomputable def action (tm : TM n) (state : tm.Q)
    (symbols : Fin (n + 2) → Γ) : Structured.Cmd :=
  .basics (actionOps tm state symbols)

/-- Recursively dispatch on loaded tape symbols. -/
noncomputable def dispatchSymbols (tm : TM n) (state : tm.Q) :
    List (Fin (n + 2)) → (Fin (n + 2) → Γ) → Structured.Cmd
  | [], symbols => action tm state symbols
  | tape :: rest, symbols =>
      Structured.Switch.select 4 (symbolReg n tape) (oneReg n)
        (fun code => dispatchSymbols tm state rest
          (Function.update symbols tape (symbolDecode code.val)))

/-- Dispatch on the state code and every loaded symbol. -/
noncomputable def dispatchState (tm : TM n) : Structured.Cmd :=
  Structured.Switch.select (Fintype.card tm.Q) (stateScratchReg n) (oneReg n)
    (fun stateCode =>
      dispatchSymbols tm ((Fintype.equivFin tm.Q).symm stateCode)
        (List.finRange (n + 2)) (fun _ => Γ.blank))

/-- Fixed uniform structured-RAM block for one nonhalting TM transition. -/
noncomputable def program (tm : TM n) : Structured.Cmd :=
  .seq (.basics (loadOps n)) (dispatchState tm)

/-- Concrete compiled uniform transition block. -/
noncomputable def compiled (tm : TM n) : Program :=
  (program tm).compile

/-- Runtime loop flag: zero exactly in the designated halt state. -/
def runningFlag (tm : TM n) (state : tm.Q) : ℕ :=
  if state = tm.qhalt then 0 else 1

/-- Finite-state branch that writes the runtime loop flag. -/
noncomputable def continueDispatch (tm : TM n) : Structured.Cmd :=
  Structured.Switch.select (Fintype.card tm.Q) (stateScratchReg n) (oneReg n)
    (fun code => .basics
      [.imm (valueReg n) (runningFlag tm ((Fintype.equivFin tm.Q).symm code))])

/-- Reload the represented state and set the runtime loop flag. The full load
prelude is deliberately reused so this fixed controller inherits its framing
theorem. -/
noncomputable def continueCheck (tm : TM n) : Structured.Cmd :=
  .seq (.basics (loadOps n)) (continueDispatch tm)

/-- One loop iteration: perform one TM transition, then recompute whether the
successor is halted. -/
noncomputable def loopBody (tm : TM n) : Structured.Cmd :=
  .seq (program tm) (continueCheck tm)

/-- Fixed structured program that repeats transitions until the represented TM
enters `qhalt`. -/
noncomputable def runUntilHalt (tm : TM n) : Structured.Cmd :=
  .seq (continueCheck tm)
    (.whileNonzero (valueReg n) (loopBody tm))

/-- Concrete compiled fixed program that simulates until `qhalt`. -/
noncomputable def compiledUntilHalt (tm : TM n) : Program :=
  (runUntilHalt tm).compile

/-- Exact instruction count of one continuation check. -/
noncomputable def continueSteps (tm : TM n) (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  (loadOps n).length +
    Structured.Switch.stepCount (stateCode tm cfg.state) 1

/-- Largest cell-register index needed when heads stay at most `bound`. -/
def registerBound (n bound : ℕ) : ℕ :=
  cellReg n (outputTape n) bound + 1

/-- Uniform value bound for a transition whose input heads are at most
`bound`; it includes a possible right move. -/
def wordBound (tm : TM n) (bound : ℕ) : ℕ :=
  max (registerBound n (bound + 1))
    (max (Fintype.card tm.Q) (bound + 1))

/-- One-bit-cushioned resource width. -/
def wordWidth (tm : TM n) (bound : ℕ) : ℕ :=
  bitlen (wordBound tm bound) + 1

/-- Peak sparse-store space envelope through one transition. -/
def spaceBound (tm : TM n) (bound : ℕ) : ℕ :=
  registerBound n (bound + 1) *
    (bitlen (registerBound n (bound + 1)) + bitlen (wordBound tm bound))

/-- Exact transition count through symbol dispatch. -/
noncomputable def dispatchSteps (tm : TM n) (state : tm.Q)
    (actual : Fin (n + 2) → Γ) : List (Fin (n + 2)) → ℕ
  | [] => (actionOps tm state actual).length
  | tape :: rest => Structured.Switch.stepCount (symbolCode (actual tape))
      (dispatchSteps tm state actual rest)

/-- Exact source/compiled instruction count for one sparse TM step. -/
noncomputable def stepCount (tm : TM n) (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  (loadOps n).length +
    Structured.Switch.stepCount (stateCode tm cfg.state)
      (dispatchSteps tm cfg.state (readSymbols cfg) (List.finRange (n + 2)))

/-- Exact instruction count of the while-loop suffix along `steps` TM
transitions. The `none` branch is unreachable in the corresponding simulation
theorem. -/
noncomputable def loopSteps (tm : TM n) :
    ℕ → Complexity.Cfg n tm.Q → ℕ
  | 0, _ => 1
  | steps + 1, cfg =>
      match tm.step cfg with
      | none => 0
      | some next => stepCount tm cfg + continueSteps tm next +
          loopSteps tm steps next + 2

/-- Exact instruction count of the complete fixed simulator along a known
halting run. -/
noncomputable def runSteps (tm : TM n) (steps : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  continueSteps tm cfg + loopSteps tm steps cfg

/-- Logarithmic-cost bound through symbol dispatch. -/
noncomputable def dispatchCost (tm : TM n) (bound : ℕ) (state : tm.Q)
    (actual : Fin (n + 2) → Γ) : List (Fin (n + 2)) → ℕ
  | [] => 4 * (actionOps tm state actual).length * wordWidth tm bound
  | tape :: rest => Structured.Switch.costBound (symbolCode (actual tape))
      (dispatchCost tm bound state actual rest) (wordWidth tm bound)

/-- Explicit logarithmic cost bound for one sparse TM step. -/
noncomputable def timeBound (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  4 * (loadOps n).length * wordWidth tm bound +
    Structured.Switch.costBound (stateCode tm cfg.state)
      (dispatchCost tm bound cfg.state (readSymbols cfg) (List.finRange (n + 2)))
      (wordWidth tm bound)

/-- Explicit logarithmic cost bound for one continuation check under a fixed
store envelope. -/
noncomputable def continueTimeBound (tm : TM n) (bound : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  4 * (loadOps n).length * wordWidth tm bound +
    Structured.Switch.costBound (stateCode tm cfg.state)
      (4 * wordWidth tm bound) (wordWidth tm bound)

/-- Accumulated logarithmic cost bound for the while-loop suffix. `base` bounds
the current heads; the remaining-step allowance supplies the common envelope. -/
noncomputable def loopTimeBound (tm : TM n) :
    ℕ → ℕ → Complexity.Cfg n tm.Q → ℕ
  | base, 0, _ => wordWidth tm base
  | base, steps + 1, cfg =>
      match tm.step cfg with
      | none => 0
      | some next =>
          let bound := base + steps + 1
          3 * wordWidth tm bound + timeBound tm bound cfg +
            continueTimeBound tm bound next +
            loopTimeBound tm (base + 1) steps next

/-- Accumulated logarithmic cost bound for the complete fixed simulator. -/
noncomputable def runTimeBound (tm : TM n) (base steps : ℕ)
    (cfg : Complexity.Cfg n tm.Q) : ℕ :=
  continueTimeBound tm (base + steps) cfg +
    loopTimeBound tm base steps cfg

/-- Width multiplier through the symbol-dispatch suffix. -/
noncomputable def dispatchFactor (tm : TM n) (state : tm.Q)
    (actual : Fin (n + 2) → Γ) : List (Fin (n + 2)) → ℕ
  | [] => 4 * (actionOps tm state actual).length
  | tape :: rest => 7 * symbolCode (actual tape) + 1 +
      dispatchFactor tm state actual rest

/-- Configuration-independent multiplier for one sparse transition, obtained
by taking the finite maximum over states and currently scanned symbols. -/
noncomputable def stepFactor (tm : TM n) : ℕ :=
  4 * (loadOps n).length +
    Finset.univ.sup fun state : tm.Q =>
      Finset.univ.sup fun actual : Fin (n + 2) → Γ =>
        7 * stateCode tm state + 1 +
          dispatchFactor tm state actual (List.finRange (n + 2))

/-- Configuration-independent multiplier for one continuation check. -/
def continueFactor (tm : TM n) : ℕ :=
  4 * (loadOps n).length + (7 * Fintype.card tm.Q + 5)

/-- Per-iteration multiplier including loop control, transition, and
continuation check. -/
noncomputable def iterationFactor (tm : TM n) : ℕ :=
  3 + stepFactor tm + continueFactor tm

/-- Coarse multiplier for a complete run, including the initial continuation
check and final zero test. -/
noncomputable def runFactor (tm : TM n) : ℕ :=
  continueFactor tm + iterationFactor tm + 1

end Sparse

end TMConfig

end RAM

end Complexity
