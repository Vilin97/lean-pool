/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Soundness
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Classes
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Step
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.ABI
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Containment
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.DenseOverlay
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Containment
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.AddressEq
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryAppend
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryCleanup
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookup
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryLookupRestore
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMissCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryMatch
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryReplace
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScanStep
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryScan
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryUpdate
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Dense
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Dispatch
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Initialization
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInit
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDecision
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseBounds
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Decision
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Switch.Compiled
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Hamming
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateEval
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStep
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.GateStreamStep
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.Scanner
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.PairValidate
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.LastBit
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.ThreeSATSyntax
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured.UnaryDecode

/-!
# Random access machines (surface)

This is the public entry point for the library's Random Access Machine (RAM)
model: a register machine with indirect addressing, executed under a
**logarithmic-cost** time measure and a matching space measure. The model,
its executable semantics, and both cost measures are defined in
`Complexitylib.Models.RandomAccessMachine.Defs`; the operational metatheory is
proved in `…/Internal`; the soundness of the cost convention is established in
`…/Soundness`.

## Main definitions

- `RAM.Instr`, `RAM.Program`, `RAM.Cfg`, `RAM.step`, `RAM.run` — the model
- `RAM.logTimeUpto`, `RAM.unitTimeUpto`, `RAM.spaceUpto` — the resource measures
- `RAM.Program.DecidesInTime`, `RAM.Program.DecidesInSpace` — deciding a language
- `RAM.DTIME`, `RAM.DSPACE`, `RAM.P` — the RAM time/space classes, over the same
  `Language = Set (List Bool)` interface as the Turing-machine classes `DTIME`,
  `DSPACE`, so the two families are directly comparable

## Main results

- `RAM.logGap_squaring` — the **soundness theorem**: the squaring program family
  has unit time `k + 1` but logarithmic time at least `2 ^ k`, so unit cost is
  super-polynomially stronger than logarithmic cost. This is the formal reason
  the library measures RAM time logarithmically and only then compares it to
  Turing time.
- `RAM.unitTimeUpto_le_logTimeUpto` — the step count is always at most the
  logarithmic time (every step costs `≥ 1`).
- `RAM.Program.DecidesInTime.mono` — deciding is monotone in the time bound.
- `RAM.run_initCfg_finiteSupport` — the register file keeps finite support
  along any run, so the space measure `RAM.Cfg.space` is a genuine finite sum.
- `RAM.TMConfig.decode_encode` — the explicit bounded TM-configuration layout
  in RAM registers decodes exactly; registers beyond the state/head/cell blocks
  are zero.
- `RAM.TMConfig.Step.compiled_encode_decodes` — the complete bounded dense
  transition block compiles to concrete RAM code and decodes to the exact TM
  successor with explicit logarithmic-time and peak-space bounds.
- `RAM.TMConfig.Sparse.decode_encode` — the fixed interleaved layout represents
  and decodes every tape cell without a bound baked into the representation.
- `RAM.TMConfig.Sparse.loadOps_correct` — the fixed uniform transition prelude
  computes runtime cell addresses, preserves the complete representation, and
  loads the state and all named head symbols exactly.
- `RAM.TMConfig.Sparse.compiledUntilHalt_correct` — one concrete RAM program,
  determined solely by the TM, follows any exact halting TM run and decodes to
  its halted configuration with exact compiled cost and space preservation.
- `RAM.TMConfig.Sparse.compiledDecision_correct` — the fixed sparse simulator
  includes the public input/output ABI, follows any exact halting TM run, and
  returns the Boolean verdict in `R₀` with exact compiled cost and space.
- `RAM.TMConfig.Sparse.compiledDecision_resourceBound` — the same fixed program
  has a concrete end-to-end logarithmic-cost and sparse-store bound depending
  only on the TM, public input length, and simulated halting-run length.
- `RAM.TMConfig.Sparse.P_subset_RAM_P` — every polynomial-time Turing language
  is decided in polynomial logarithmic-cost RAM time by the fixed sparse
  simulator.
- `RAM.RegisterStore.Snapshot.decode_run` — a finite sparse address/value
  snapshot interpreter preserves canonicality and decodes exactly to the RAM
  run; its self-delimiting binary tape codec round-trips with a concrete
  quadratic-size envelope.
- `RAM.RegisterStore.Snapshot.encode_run_length_le_logTime` — every reachable
  encoded snapshot has an explicit quadratic envelope in initial store size,
  fixed program literals, and charged RAM logarithmic time.
- `RAM.RegisterStore.Snapshot.encode_initial_run_length_le_logTime` — the same
  envelope starts from the public `RAM.initCfg` ABI with explicit input-length
  dependence.
- `RAM.RegisterStore.Machine.wordWidthTM_reachesIn_frame` — the first concrete
  reverse-simulation parser phase scans a self-delimiting word's unary width
  prefix in exact time, stops on its separator, and produces the width on a
  canonical binary work tape.
- `RAM.RegisterStore.Machine.payloadBitTM_reachesIn_frame` — the concrete
  payload leaf consumes and appends one fixed-width payload bit while preserving
  every unrelated tape.
- `RAM.RegisterStore.Machine.wordPayloadTM_reachesIn_frame` — a canonical
  binary counter and preserved width drive that leaf for exactly the payload
  length, leaving the source at the next encoded word with an exact runtime.
- `RAM.RegisterStore.Machine.wordDecodeTM_reachesIn_frame_encode` — the complete
  decoder consumes one canonical `WordCode.encode` prefix, recovers its payload,
  and leaves the following encoded stream untouched; the companion
  `wordDecodeTM_prefix_withinAuxSpace` bounds every run prefix's auxiliary
  space.
- `RAM.RegisterStore.Machine.wordTargetRewind_reachesIn_frame` — a decoded
  append-position payload rewinds to the canonical cell-one read convention in
  linear time while preserving every framed tape.
- `TM.binaryEqTM_reachesIn_frame` — two canonical binary work tapes are compared
  in linear time, with the equality bit written to a dedicated work tape and
  every framed tape preserved.
- `TM.binaryRippleAddTM_reachesIn_frame` — two canonical binary operands are
  preserved while their sum is written to a fresh result tape in time linear in
  their bit widths, with a literal external frame and all-prefix space bound.
- `RAM.RegisterStore.Machine.entryDecodeTM_reachesIn_frame` — one canonical
  sparse address/value entry is decoded in exact time, leaving the following
  entry stream untouched; `entryDecodeTM_prefix_withinAuxSpace` bounds every
  run prefix's auxiliary space.
- `RAM.RegisterStore.Machine.decodedAddressEqTM_reachesIn_frame` — the decoded
  address is rewound and compared with a canonical query in linear time, with
  both left markers and every framed tape preserved.
- `RAM.RegisterStore.Machine.entryMatchTM_reachesIn_frame` — one concrete
  decode-and-compare unit consumes an encoded sparse entry, exposes its value
  and equality flag, preserves a parked frame, and has explicit time/space
  bounds ready for bounded iteration.
- `RAM.RegisterStore.Machine.entryMatchReadTM_reachesIn_frame` — the match flag
  is rewound to cell one for direct controller inspection while preserving all
  decoded scratch contracts and an explicit per-tape head bound.
- `RAM.RegisterStore.Machine.entryScanTM_hoareTime_frame` — one fixed bounded
  scanner uses a runtime binary entry count, returns the first matching decoded
  value or certifies a miss, and preserves every tape outside its ten-tape
  assignment with explicit time and all-prefix space envelopes.
- `RAM.RegisterStore.Machine.entryLookupTM_hoareTime_frame` — the same concrete
  scan is packaged as a sparse lookup whose decoded-value tape equals the pure
  `RegisterStore.read` result, including the default-zero miss case.
- `RAM.RegisterStore.Machine.entryUpdateTM_hoareTime_frame` — one fixed
  runtime-counted controller realizes the pure sparse-store `write`, including
  copy, replacement, deletion, absent-address append, exact frames, and an
  explicit time/all-prefix space envelope.
- `RAM.RegisterStore.Machine.binaryInstructionUpdateTM_hoareTime_frame` —
  width-efficient addition, truncated subtraction, or multiplication feeds its
  canonical result directly into sparse update, with no hidden value-counted
  copy between phases and with an exact framed runtime.
- `RAM.RegisterStore.Machine.binaryInstructionUpdateTM_retargetOutput_hoareTime_frame`
  — the same arithmetic/update kernel can place the updated encoded store on a
  fresh work tape while keeping the public output blank and parked.
- `RAM.RegisterStore.Machine.programInstructionTM_hoareTime_frame` — one fixed
  finite-control dispatch machine selects the RAM instruction named by the
  canonical program counter and realizes its exact sparse snapshot step in a
  fresh next-store buffer.
- `RAM.RegisterStore.Machine.programDecisionTM_hoareTime_ramRun` — one fixed
  twenty-work-tape machine marshals the public input, iterates exact sparse RAM
  steps through the first halt, and writes the RAM verdict to the public output.
- `RAM.RegisterStore.Machine.programDecisionTime_le_envelope` — the complete
  simulator has a checked fourth-degree runtime envelope in input length and
  charged RAM logarithmic time.
- `RAM.RegisterStore.Machine.denseProgramDecisionTM_hoareTime_ramRun` — the
  optimized fixed twenty-work-tape machine keeps the public input immutable and
  stores only a sparse tagged mutable overlay while realizing the same RAM run.
- `RAM.RegisterStore.Machine.denseProgramDecisionTime_le_envelope` — the
  optimized complete simulator has a checked quadratic envelope in input length
  plus charged RAM logarithmic time.
- `RAM.RegisterStore.Machine.RAM_DTIME_subset_DTIME_sq` — whenever `T`
  asymptotically dominates `n + 1`, logarithmic-cost `RAM.DTIME(T)` is contained
  in multitape `DTIME(T²)`.
- `RAM.RegisterStore.Machine.RAM_P_eq_P` — logarithmic-cost RAM polynomial time
  and deterministic multitape Turing polynomial time define the same class.
- `RAM.RegisterStore.Machine.wordEncodeTM_hoareTime_frame` and
  `rewindEntryEncodeTM_hoareTime_frame` — canonical or arbitrarily positioned
  decoded words and entries are re-emitted in the exact self-delimiting store
  codec, with explicit time, space, and external-frame contracts.
- `TM.resetBinaryWorkTM_hoareTime_frame` — an arbitrary cursor over canonical
  binary contents is rewound and cleared to the standard blank tape with an
  explicit time/space envelope and literal external frame.
- `RAM.Structured.Switch.select_compiled` — finite numeric case dispatch has an
  exact selected-branch transition count and transfers explicit logarithmic
  cost and space envelopes to concrete RAM code.
- `RAM.TMConfig.Step.loadOps_correct` — the fixed TM-transition block's loading
  phase preserves the represented configuration while recovering the finite
  state and all named head symbols exactly.
- `RAM.Structured.Exec.compile_correct` — structured source execution compiles
  with exact register, logarithmic-time, and peak-space preservation.
- `RAM.Structured.Hamming.compiled_performance` — a verified imperative
  Hamming-weight program with an exact transition count, explicit logarithmic
  time and peak-space bounds, and end-to-end source-to-RAM resource transfer.
- `RAM.Structured.Hamming.timeBound_bigO_quasilinear` and
  `spaceBound_bigO_quasilinear` — both explicit budgets are `O(n · bitlen n)`.
- `RAM.Structured.Scanner.compiled_performance` — a reusable verified compiler
  from numeric finite-state scanners to concrete logarithmic-cost RAM programs.
- `RAM.Structured.PairValidate.compiled_performance` — a table-driven
  reimplementation of `TM.pairValidateTM`, with exact steps, explicit
  logarithmic time/space, and agreement with `validPairEncoding`.
- `RAM.Structured.LastBit.compiled_performance` — a second typed-scanner
  instance, agreeing with the existing last-bit languages.
- `RAM.Structured.ThreeSATSyntax.compiled_performance` — the existing 27-state
  exact-3-CNF syntax automaton compiled with exact steps and language agreement.
- `RAM.Structured.UnaryDecode.compiled_performance` — a non-regular cursor
  decoder for terminated-unary circuit fields, including successful and
  truncated-input exits, exact steps, and the decoded suffix position.
- `RAM.Structured.GateEval.compiled_performance` — a branch-free twenty-step
  decoded-gate kernel with indirect memo reads and append, exact logarithmic
  cost, explicit peak space, and preservation of all existing wire entries.
- `RAM.Structured.GateStep.compiled_performance` — one fixed serialized-gate
  program composing two unary cursor calls with the decoded-gate kernel at a
  runtime-discovered memo base, with exact transitions and concrete transferred
  time/space bounds.
- `RAM.Structured.GateStreamStep.compiled_correct` — the bounded split-layout
  admission test: one routine consumes a gate from an arbitrary unread stream,
  advances a separate memo, preserves the tail, and transfers its exact source
  execution and resource measurements to concrete RAM execution.

## Relationship to the Turing-machine models

The RAM shares the library's `Language` interface, so `RAM.DTIME`/`RAM.DSPACE`
and the Turing-machine classes `DTIME`/`DSPACE` speak about the same objects.
The classical two-way simulation bounds that make the models polynomially
equivalent are (Cook–Reckhow, *Time bounded random access machines*, JCSS 7
(1973), 354–375; van Emde Boas, *Machine models and simulations*, Handbook of
Theoretical Computer Science A, 1990):

* **Turing machine → RAM.** A `T(n)`-time multi-tape Turing machine is
  simulated by a RAM in logarithmic time `O(T(n) · log T(n))`.
* **RAM → Turing machine.** A `T(n)`-time logarithmic-cost RAM is simulated by
  a multi-tape Turing machine in time `O(T(n)²)`.

Both overheads are polynomial, so `RAM.DTIME` and `DTIME` yield the *same*
polynomial-time class: `RAM-P = P`. Under the **unit-cost** measure the
RAM → TM direction fails — `RAM.logGap_squaring` exhibits a program whose
unit-time is linear but whose output already needs exponentially many Turing
steps to write — which is precisely why the model is defined with logarithmic
cost. The bounded dense transition block is proved end to end, including
selected actions, nested dispatch, concrete compilation, and explicit resource
bounds. That block is a bounded program family: its register layout depends on
the tape window, so it cannot by itself witness `RAM.DTIME`, whose program must
be fixed. The uniform replacement now has a fixed sparse interleaved
representation, checked runtime address/loading and action/dispatch layers, a
fixed compiled loop that follows an arbitrary exact halting TM run, and a
checked public-ABI marshaller and verdict extractor. The remaining TM-to-RAM
work is now narrower: the repeated sparse core and complete public
marshaller/extractor share a concrete envelope, a linear-times-word-width cost
theorem, and a checked logarithmic word-width bound. The fixed compiled program
now transfers `TM.DecidesInTime` to `RAM.Program.DecidesInTime`, packages the
result in `RAM.DTIME` at its explicit transformed bound, and proves the class
theorem `P ⊆ RAM.P`. The sharper parametric `DTIME(T)` statement still
requires an explicit input-length domination hypothesis: the public marshaller
necessarily costs `O(n · log n)`, while an arbitrary stated time bound `T` need
not dominate `n`. The reverse simulation is now checked end to end.
Finite-support register functions have canonical sparse snapshots whose binary
tape codec round-trips with an explicit length bound. Fixed lookup, update,
binary-arithmetic, control, cleanup, initialization, iteration, and output
machines realize every RAM instruction and complete halting run on twenty work
tapes. The original sparse public-input ABI retains an explicit fourth-degree
envelope as a simple fallback. The optimized machine instead leaves the dense
public input on its read-only tape and maintains a positive-tagged sparse
mutable overlay. Selected-width step accounting and a decreasing square
potential give a checked `O((n + T(n))²)` public-ABI bound. Consequently,
`RAM_DTIME_subset_DTIME_sq` gives the textbook `RAM.DTIME(T) ⊆ DTIME(T²)` under
the explicit hypothesis `n + 1 = O(T(n))`. Choosing the least halting fuel also
transfers every `RAM.P` decider to `P`; together with the fixed sparse forward
simulator this proves `RAM.RegisterStore.Machine.RAM_P_eq_P`.
-/


public section

namespace Complexity

namespace RAM

/-! ### A worked decider

The two-instruction program `⟨imm 0 1⟩` overwrites the verdict register with `1`
and then halts (its program counter runs off the end). It decides the universal
language in constant logarithmic time, exercising the full `DecidesInTime` API
end to end. -/

/-- The always-accept program: set the verdict register to `1`. -/
def acceptProg : Program := [Instr.imm 0 1]

/-- On any input, `acceptProg` halts after one step with verdict `1`. -/
theorem acceptProg_run (x : List Bool) :
    (run acceptProg 1 (initCfg x)).verdict = 1 := by
  rfl

/-- `acceptProg` decides the universal language in constant logarithmic time. -/
theorem acceptProg_decides : acceptProg.DecidesInTime Set.univ (fun _ => 2) := by
  intro x
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro _; rfl
  · intro hx; exact absurd (Set.mem_univ x) hx

/-- The universal language is in `RAM.DTIME` at a constant bound: a witness that
    the RAM time classes are inhabited over the shared `Language` interface. -/
theorem univ_mem_DTIME : Set.univ ∈ DTIME (fun _ => 2) :=
  ⟨acceptProg, (fun _ => 2), acceptProg_decides, BigO.refl _⟩

/-- The always-reject program: set the verdict register to `0`. -/
def rejectProg : Program := [Instr.imm 0 0]

/-- On any input, `rejectProg` halts after one step with verdict `0`. -/
theorem rejectProg_run (x : List Bool) :
    (run rejectProg 1 (initCfg x)).verdict = 0 := by rfl

/-- `rejectProg` decides the empty language in constant logarithmic time,
    exercising the rejection side of the `DecidesInTime` API. -/
theorem rejectProg_decides : rejectProg.DecidesInTime (∅ : Language) (fun _ => 2) := by
  intro x
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (1 : ℕ) ≤ 2; omega
  · intro hx; simp at hx
  · intro _; rfl

/-- The empty language is in `RAM.DTIME` at a constant bound (the rejection
    counterpart of `univ_mem_DTIME`). -/
theorem empty_mem_DTIME : (∅ : Language) ∈ DTIME (fun _ => 2) :=
  ⟨rejectProg, (fun _ => 2), rejectProg_decides, BigO.refl _⟩

end RAM

end Complexity
