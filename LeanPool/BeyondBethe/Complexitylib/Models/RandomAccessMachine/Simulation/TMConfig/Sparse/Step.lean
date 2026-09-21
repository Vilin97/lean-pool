/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse.Step.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Structured
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.TMConfig.Sparse

/-!
# A fixed sparse-RAM block for one Turing-machine transition

The generated program depends only on the Turing machine. Its interleaved
layout computes cell addresses at runtime, so no tape or time bound is baked
into the program. The exact address/loading layers, selected action, complete
nested dispatch, fixed iteration controller, and transfer to concrete compiled
RAM execution are checked. The separate `Sparse.ABI` surface supplies the
public input/output marshalling layer.
-/


public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse


/-- Computing a named tape's current-cell address preserves the represented
configuration and returns the exact sparse cell register. -/
theorem addressOps_correct {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    {store : Structured.Store} (hrepresents : Represents tm cfg store)
    (tape : Fin (n + 2)) (htapeCount : store (tapeCountReg n) = n + 2) :
    let final := Structured.Basic.execList (addressOps n tape) store
    Represents tm cfg final ∧
      final (addressReg n) = cellReg n tape (tapeAt cfg tape).head :=
  ⟨addressOps_represents_internal hrepresents tape,
    addressOps_address_internal hrepresents tape htapeCount⟩

/-- The fixed loading prelude preserves the complete sparse representation,
initializes its constants, and recovers the state and every head symbol. -/
theorem loadOps_correct {tm : TM n} {cfg : Complexity.Cfg n tm.Q}
    {store : Structured.Store} (hrepresents : Represents tm cfg store) :
    let final := Structured.Basic.execList (loadOps n) store
    Represents tm cfg final ∧
      final (zeroReg n) = 0 ∧
      final (oneReg n) = 1 ∧
      final (tapeCountReg n) = n + 2 ∧
      final (stateScratchReg n) = stateCode tm cfg.state ∧
      ∀ tape, final (symbolReg n tape) = symbolCode (readSymbols cfg tape) :=
  loadOps_loaded_internal hrepresents

/-- Once the loaded finite state and symbols select an action, the fixed sparse
operations represent the exact TM successor. -/
theorem actionOps_correct {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2) :
    Represents tm next
      (Structured.Basic.execList
        (actionOps tm cfg.state (readSymbols cfg)) store) :=
  actionOps_represents_internal hstep hrepresents
    (fun i => (hworkStart i).1) houtputStart.1 hone htapeCount

/-- The fixed structured program, determined solely by `tm`, performs exactly
one nonhalting TM transition with the advertised source instruction count. -/
theorem program_correct {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (program tm) store final
        (stepCount tm cfg) cost space ∧
      Represents tm next final :=
  program_exec_internal hstep hrepresents
    (fun i => (hworkStart i).1) houtputStart.1

/-- The complete fixed source block decodes to the exact successor without a
tape-window premise. -/
theorem program_decodes {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (program tm) store final
        (stepCount tm cfg) cost space ∧
      decode tm final = next := by
  obtain ⟨final, cost, space, hexec, hfinal⟩ :=
    program_correct hstep hrepresents hworkStart houtputStart
  exact ⟨final, cost, space, hexec,
    decode_of_represents tm next final hfinal⟩

/-- Exact transfer of the uniform one-step theorem to the concrete compiled
RAM block, including the compiler's logarithmic cost and peak space. -/
theorem compiled_correct {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (program tm) store final
        (stepCount tm cfg) cost space ∧
      run (compiled tm) (stepCount tm cfg) { pc := 0, regs := store } =
        { pc := (program tm).codeSize, regs := final } ∧
      Halted (compiled tm)
        (run (compiled tm) (stepCount tm cfg) { pc := 0, regs := store }) ∧
      logTimeUpto (compiled tm) (stepCount tm cfg)
        { pc := 0, regs := store } = cost ∧
      spaceUpto (compiled tm) (stepCount tm cfg)
        { pc := 0, regs := store } = space ∧
      decode tm final = next := by
  obtain ⟨final, cost, space, hexec, hfinal⟩ :=
    program_correct hstep hrepresents hworkStart houtputStart
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, ?_, ?_, ?_, ?_,
    decode_of_represents tm next final hfinal⟩
  · simpa [compiled] using hcompiled.1
  · simpa [compiled] using Structured.Exec.compile_halted hexec
  · simpa [compiled] using hcompiled.2.1
  · simpa [compiled] using hcompiled.2.2

/-- The fixed loop controller follows any exact halting TM run and retains a
complete representation of its halted configuration. -/
theorem runUntilHalt_correct {tm : TM n} {steps : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (runUntilHalt tm) store final
        (runSteps tm steps cfg) cost space ∧
      Represents tm halted final :=
  runUntilHalt_exec_internal hreach hhalted hrepresents
    (fun i => (hworkStart i).1) houtputStart.1

/-- The same fixed loop decodes to the exact halted TM configuration. -/
theorem runUntilHalt_decodes {tm : TM n} {steps : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (runUntilHalt tm) store final
        (runSteps tm steps cfg) cost space ∧
      decode tm final = halted := by
  obtain ⟨final, cost, space, hexec, hfinal⟩ :=
    runUntilHalt_correct hreach hhalted hrepresents hworkStart houtputStart
  exact ⟨final, cost, space, hexec,
    decode_of_represents tm halted final hfinal⟩

/-- Exact compiled-RAM transfer for the complete fixed simulation loop. -/
theorem compiledUntilHalt_correct {tm : TM n} {steps : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    ∃ final cost space,
      Structured.Exec (runUntilHalt tm) store final
        (runSteps tm steps cfg) cost space ∧
      run (compiledUntilHalt tm) (runSteps tm steps cfg)
          { pc := 0, regs := store } =
        { pc := (runUntilHalt tm).codeSize, regs := final } ∧
      Halted (compiledUntilHalt tm)
        (run (compiledUntilHalt tm) (runSteps tm steps cfg)
          { pc := 0, regs := store }) ∧
      logTimeUpto (compiledUntilHalt tm) (runSteps tm steps cfg)
        { pc := 0, regs := store } = cost ∧
      spaceUpto (compiledUntilHalt tm) (runSteps tm steps cfg)
        { pc := 0, regs := store } = space ∧
      decode tm final = halted := by
  obtain ⟨final, cost, space, hexec, hfinal⟩ :=
    runUntilHalt_correct hreach hhalted hrepresents hworkStart houtputStart
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, ?_, ?_, ?_, ?_,
    decode_of_represents tm halted final hfinal⟩
  · simpa [compiledUntilHalt] using hcompiled.1
  · simpa [compiledUntilHalt] using Structured.Exec.compile_halted hexec
  · simpa [compiledUntilHalt] using hcompiled.2.1
  · simpa [compiledUntilHalt] using hcompiled.2.2

/-- Quantitative one-step theorem for the fixed sparse program. The exact
source step count, logarithmic time, and peak sparse-store space are all
checked against one explicit envelope. -/
theorem program_resourceBound {tm : TM n} {bound : ℕ}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg bound)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant)
    (henvelope : StepEnvelope tm bound store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (program tm) store final
        (stepCount tm cfg) (timeBound tm bound cfg) (spaceBound tm bound) ∧
      Represents tm next final ∧ StepEnvelope tm bound final :=
  program_measured_internal hstep hrepresents hheads
    (fun i => (hworkStart i).1) houtputStart.1 henvelope

/-- Quantitative iteration theorem for the fixed sparse simulator. Starting
with heads bounded by `base`, `steps` transitions fit one envelope at
`base + steps`; costs compose into `runTimeBound`. -/
theorem runUntilHalt_resourceBound {tm : TM n} {steps base : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hrepresents : Represents tm cfg store)
    (hheads : HeadsBounded cfg base)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant)
    (henvelope : StepEnvelope tm (base + steps) store) :
    ∃ final,
      Structured.Internal.MeasuredRuns (runUntilHalt tm) store final
        (runSteps tm steps cfg) (runTimeBound tm base steps cfg)
        (spaceBound tm (base + steps)) ∧
      Represents tm halted final ∧
      StepEnvelope tm (base + steps) final :=
  runUntilHalt_measured_internal hreach hhalted hrepresents hheads
    (fun i => (hworkStart i).1) houtputStart.1 henvelope

/-- The accumulated exact cost expression is linear in the number of simulated
steps and logarithmic in the common sparse word bound. -/
theorem runTimeBound_le_linear (tm : TM n) (base steps : ℕ)
    (cfg : Complexity.Cfg n tm.Q) :
    runTimeBound tm base steps cfg ≤
      ((steps + 1) * runFactor tm) * wordWidth tm (base + steps) :=
  runTimeBound_le_linear_internal tm base steps cfg

/-- Sparse word width is logarithmic in the head allowance; all dependence on
the fixed machine is absorbed into the big-O constant. -/
theorem wordWidth_bigO_log (tm : TM n) :
    (fun bound => wordWidth tm bound) =O (fun bound => Nat.log 2 bound) := by
  let C := cellBase n + 3 * n + 10 + Fintype.card tm.Q
  let p : Polynomial ℕ := Polynomial.C C * Polynomial.X + Polynomial.C C
  have hword : ∀ bound, wordBound tm bound ≤ p.eval bound := by
    intro bound
    have hcoef : n + 2 ≤ C := by
      simp [C, cellBase]
      omega
    have hconstant : cellBase n + (n + 2) + (n + 1) + 1 ≤ C := by
      simp [C]
      omega
    have hregister : registerBound n (bound + 1) ≤ C * bound + C := by
      rw [registerBound, cellReg]
      simp only [outputTape]
      have hproduct := Nat.mul_le_mul_left bound hcoef
      have hproduct' : bound * (n + 2) ≤ C * bound := by
        simpa [Nat.mul_comm] using hproduct
      rw [show (bound + 1) * (n + 2) = bound * (n + 2) + (n + 2) by ring]
      omega
    have hcard : Fintype.card tm.Q ≤ C * bound + C := by
      have hle : Fintype.card tm.Q ≤ C := by
        simp [C]
      omega
    have hbound : bound + 1 ≤ C * bound + C := by
      have hone : 1 ≤ C := by
        simp [C, cellBase]
        omega
      have hmul := Nat.mul_le_mul_left bound hone
      have hmul' : bound ≤ C * bound := by
        simpa [Nat.mul_comm] using hmul
      omega
    simp only [wordBound, p, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [show C * bound + C = C * bound + C by rfl]
    exact Nat.max_le.mpr ⟨hregister, Nat.max_le.mpr ⟨hcard, hbound⟩⟩
  have hsize : (fun bound => (wordBound tm bound).size) =O
      (fun bound => Nat.log 2 bound) :=
    BigO.natSize_of_polynomial_bound p hword
  have hone : (fun _ : ℕ => 1) =O (fun bound => Nat.log 2 bound) :=
    BigO.const_le_logTwo 1
  simpa [wordWidth, bitlen] using BigO.add hsize hone

private theorem bounded_mono {cfg : Complexity.Cfg n Q}
    {bound larger : ℕ} (hbounded : Bounded cfg bound)
    (hle : bound ≤ larger) : Bounded cfg larger := by
  intro tape position hposition
  exact hbounded tape position (lt_of_le_of_lt hle hposition)

private theorem headsBounded_mono {cfg : Complexity.Cfg n Q}
    {bound larger : ℕ} (hheads : HeadsBounded cfg bound)
    (hle : bound ≤ larger) : HeadsBounded cfg larger := by
  intro tape
  exact le_trans (hheads tape) hle

/-- Concrete compiled-RAM resource transfer from a canonical sparse encoding.
This is the finite, directly checkable core of the forward containment: a
`steps`-step halting TM run is simulated by one program depending only on
`tm`, with the stated logarithmic time and sparse-store space bounds. -/
theorem compiledUntilHalt_resourceBound {tm : TM n} {steps base : ℕ}
    {cfg halted : Complexity.Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg halted)
    (hhalted : tm.halted halted)
    (hbounded : Bounded cfg base)
    (hheads : HeadsBounded cfg base)
    (hworkStart : ∀ i, (cfg.work i).StartInvariant)
    (houtputStart : cfg.output.StartInvariant) :
    let store := encodeRegs tm cfg
    ∃ final cost space,
      Structured.Exec (runUntilHalt tm) store final
        (runSteps tm steps cfg) cost space ∧
      cost ≤ runTimeBound tm base steps cfg ∧
      space ≤ spaceBound tm (base + steps) ∧
      run (compiledUntilHalt tm) (runSteps tm steps cfg)
          { pc := 0, regs := store } =
        { pc := (runUntilHalt tm).codeSize, regs := final } ∧
      Halted (compiledUntilHalt tm)
        (run (compiledUntilHalt tm) (runSteps tm steps cfg)
          { pc := 0, regs := store }) ∧
      decode tm final = halted := by
  let store := encodeRegs tm cfg
  have hboundLe : base ≤ base + steps := Nat.le_add_right _ _
  have henvelope := encodeRegs_envelope_internal tm cfg (base + steps)
    (bounded_mono hbounded hboundLe) (headsBounded_mono hheads hboundLe)
  obtain ⟨final, hmeasured, hfinalRepresents, _hfinalEnvelope⟩ :=
    runUntilHalt_resourceBound hreach hhalted (encodeRegs_represents tm cfg)
      hheads hworkStart houtputStart henvelope
  obtain ⟨cost, space, hexec, hcost, hspace⟩ := hmeasured
  have hcompiled := Structured.Exec.compile_correct hexec
  refine ⟨final, cost, space, hexec, hcost, hspace, ?_, ?_,
    decode_of_represents tm halted final hfinalRepresents⟩
  · simpa [compiledUntilHalt, store] using hcompiled.1
  · simpa [compiledUntilHalt, store] using
      Structured.Exec.compile_halted hexec

end Sparse

end TMConfig

end RAM

end Complexity
