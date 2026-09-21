/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Defs

/-!
# Public RAM input/output ABI for the sparse TM simulator

The public RAM input occupies the unbounded prefix `R₁, …, Rₙ`, so no fixed
scratch register is initially disjoint from every input. The marshaller first
captures the six registers it must clobber in finite control flow. Each leaf
then copies the raw input backward into the sparse input tape while clearing the
old prefix, repairs those six statically remembered bits, and initializes the
state, heads, and left-end markers.
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Fixed registers clobbered before the backward input-copy loop reaches them. -/
def captureRegs (n : ℕ) : List ℕ :=
  [zeroReg n, oneReg n, tapeCountReg n, stateScratchReg n,
    addressReg n, valueReg n]

/-- Constants needed by each backward-copy iteration. They are restored inside
the loop because clearing the raw prefix eventually visits these registers. -/
def marshalConstants (n : ℕ) : List Structured.Basic :=
  [.imm (zeroReg n) 0,
    .imm (oneReg n) 1,
    .imm (tapeCountReg n) (n + 2),
    .imm (stateScratchReg n) (cellBase n)]

/-- Copy and clear the raw input cell selected by the cursor in `R₀`, convert
its public-ABI Boolean code `0/1` to the sparse tape-symbol code `1/2`, write it
to the sparse input-tape address, and decrement the cursor. -/
def marshalLoopOps (n : ℕ) : List Structured.Basic :=
  [.add (addressReg n) stateReg (zeroReg n),
    .load (valueReg n) (addressReg n),
    .store (addressReg n) (zeroReg n),
    .imm (zeroReg n) 0,
    .imm (oneReg n) 1,
    .imm (tapeCountReg n) (n + 2),
    .imm (stateScratchReg n) (cellBase n),
    .add (valueReg n) (valueReg n) (oneReg n),
    .mul (addressReg n) stateReg (tapeCountReg n),
    .add (addressReg n) (addressReg n) (stateScratchReg n),
    .store (addressReg n) (valueReg n),
    .sub stateReg stateReg (oneReg n)]

/-- Backward raw-input copy. -/
def marshalLoop (n : ℕ) : Structured.Cmd :=
  .whileNonzero stateReg (.basics (marshalLoopOps n))

/-- Exact source/compiled instruction count of the backward-copy loop. -/
def marshalLoopSteps (n inputLength : ℕ) : ℕ :=
  inputLength * ((marshalLoopOps n).length + 2) + 1

/-- Initial numeric allowance for public-input marshalling. It contains every
raw input register and every sparse destination address used by the copy. -/
def marshalBaseBound (n inputLength : ℕ) : ℕ :=
  registerBound n (inputLength + 1)

/-- Common sparse position/resource bound used after marshalling. The additive
input-length slack absorbs the one-unit value growth of every loop body. -/
def marshalBound (n inputLength : ℕ) : ℕ :=
  marshalBaseBound n inputLength + inputLength

/-- Logarithmic-cost width used by the public-input marshaller. -/
def marshalWidth (n inputLength : ℕ) : ℕ :=
  bitlen (marshalBound n inputLength) + 1

/-- Width of the smaller envelope used before the copy loop starts. -/
def marshalBaseWidth (n inputLength : ℕ) : ℕ :=
  bitlen (marshalBaseBound n inputLength) + 1

/-- Sparse-store space envelope used throughout public-input marshalling. -/
def marshalSpaceBound (n inputLength : ℕ) : ℕ :=
  registerBound n (marshalBound n inputLength + 1) *
    (bitlen (registerBound n (marshalBound n inputLength + 1)) +
      bitlen (marshalBound n inputLength))

/-- Concrete logarithmic-cost bound for the backward-copy loop. -/
def marshalLoopTimeBound (n inputLength : ℕ) : ℕ :=
  (inputLength * (3 + 4 * (marshalLoopOps n).length) + 1) *
    marshalWidth n inputLength

/-- Restore one input bit remembered in the capture tree, but only when the
copy loop actually visited that position. A visited destination is necessarily
positive because the loop writes `rawBit + 1`; an absent position remains the
initial zero beyond the raw input prefix. -/
def repairBit (n : ℕ) (captured : ℕ × ℕ) : Structured.Cmd :=
  .seq
    (.basics
      [.imm (addressReg n) (cellReg n (inputTape n) captured.1),
        .load (valueReg n) (addressReg n)])
    (.ifZero (valueReg n) .skip
      (.basics
        [.imm (valueReg n) (captured.2 + 1),
          .store (addressReg n) (valueReg n)]))

/-- Restore all visited scratch-position input bits remembered by a
capture-tree leaf. -/
def repairCaptured (n : ℕ) (captured : List (ℕ × ℕ)) :
    Structured.Cmd :=
  match captured with
  | [] => .skip
  | entry :: rest => .seq (repairBit n entry) (repairCaptured n rest)

/-- Values accumulated by the capture tree, in the same reverse order used by
`captureInput`. -/
def captureValues (store : Structured.Store) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], captured => captured
  | reg :: rest, captured =>
      captureValues store rest ((reg, store reg) :: captured)

/-- Immediate writes that initialize the semantic fields of `tm.initCfg` after
the raw input prefix has been relocated and cleared. -/
noncomputable def initializeConfigWrites (tm : TM n) : List (ℕ × ℕ) :=
  [(stateReg, stateCode tm tm.qstart)] ++
    (List.finRange (n + 2)).map (fun tape => (headReg tape, 0)) ++
    (List.finRange (n + 2)).map (fun tape =>
      (cellReg n tape 0, symbolCode Γ.start))

/-- Straight-line realization of the initial-configuration writes. -/
noncomputable def initializeConfigOps (tm : TM n) : List Structured.Basic :=
  (initializeConfigWrites tm).map fun write =>
    .imm write.1 write.2

/-- Concrete cost bound for one selected capture-tree leaf. -/
noncomputable def marshalLeafTimeBound (tm : TM n) (inputLength : ℕ) : ℕ :=
  4 * (marshalConstants n).length * marshalBaseWidth n inputLength +
    marshalLoopTimeBound n inputLength +
    (captureRegs n).length * (27 * wordWidth tm (marshalBound n inputLength)) +
    4 * (initializeConfigOps tm).length *
      wordWidth tm (marshalBound n inputLength)

/-- Concrete cost bound for the full public-input marshaller, including the
fixed capture tree. -/
noncomputable def marshalTimeBound (tm : TM n) (inputLength : ℕ) : ℕ :=
  3 * (captureRegs n).length * wordWidth tm (marshalBound n inputLength) +
    marshalLeafTimeBound tm inputLength

/-- One capture-tree leaf: initialize scratch constants, copy backward, repair
captured positions, and establish the sparse initial configuration. -/
noncomputable def marshalLeaf (tm : TM n)
    (captured : List (ℕ × ℕ)) : Structured.Cmd :=
  .seq (.basics (marshalConstants n))
    (.seq (marshalLoop n)
      (.seq (repairCaptured n captured)
        (.basics (initializeConfigOps tm))))

/-- Capture the initial Boolean contents of a finite register list in control
flow. The zero/nonzero branches record canonical numeric values `0` and `1`. -/
noncomputable def captureInput (tm : TM n) :
    List ℕ → List (ℕ × ℕ) → Structured.Cmd
  | [], captured => marshalLeaf tm captured
  | reg :: rest, captured =>
      .ifZero reg
        (captureInput tm rest ((reg, 0) :: captured))
        (captureInput tm rest ((reg, 1) :: captured))

/-- Fixed public-ABI marshaller for `tm`. -/
noncomputable def marshalInput (tm : TM n) : Structured.Cmd :=
  captureInput tm (captureRegs n) []

/-- Copy the halted TM output symbol at cell one into public verdict register
`R₀` and shift the sparse symbol codes `1/2` back to public verdicts `0/1`.
This intentionally destroys the final sparse state code. -/
def extractVerdictOps (n : ℕ) : List Structured.Basic :=
  [.imm (addressReg n) (cellReg n (outputTape n) 1),
    .load stateReg (addressReg n),
    .imm (oneReg n) 1,
    .sub stateReg stateReg (oneReg n)]

/-- End-to-end logarithmic-cost bound from the public ABI through verdict
extraction for a halting run of the given length. -/
noncomputable def decisionTimeBound (tm : TM n)
    (inputLength steps : ℕ) : ℕ :=
  marshalTimeBound tm inputLength +
    ((steps + 1) * runFactor tm) *
      wordWidth tm (marshalBound n inputLength + steps) +
    4 * (extractVerdictOps n).length *
      wordWidth tm (marshalBound n inputLength + steps)

/-- Complete fixed source program from the public RAM input ABI to verdict
register `R₀`. -/
noncomputable def decisionProgram (tm : TM n) : Structured.Cmd :=
  .seq (marshalInput tm)
    (.seq (runUntilHalt tm) (.basics (extractVerdictOps n)))

/-- Concrete compiled public-ABI simulator. -/
noncomputable def compiledDecision (tm : TM n) : Program :=
  (decisionProgram tm).compile

end Sparse

end TMConfig

end RAM

end Complexity
