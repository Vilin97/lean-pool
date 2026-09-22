/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.Init.Defs
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryEncode
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Sparse RAM public-input initialization -- proof internals
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem programBinaryPrefixTape_hasBinaryPrefix (bits : List Bool) :
    (programBinaryPrefixTape bits).HasBinaryPrefix bits := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    exact Tape.init_ofBool_cells_ge bits i hi

private theorem programBinaryPrefixTape_parked (bits : List Bool) :
    TM.Parked (programBinaryPrefixTape bits) := by
  refine ⟨by simp [programBinaryPrefixTape], ?_⟩
  exact (show (programBinaryPrefixTape bits).HasBinaryContent bits from
    (programBinaryPrefixTape_hasBinaryPrefix bits).2).cells_ne_start

private theorem binaryTape_parked (bits : List Bool) :
    TM.Parked (programBinaryTape bits) := by
  have hstring : (programBinaryTape bits).HasBinaryString bits := by
    simpa only [programBinaryTape] using!
      Tape.init_move_right_hasBinaryString bits
  exact ⟨by rw [hstring.1], hstring.hasBinaryContent.cells_ne_start⟩

private theorem initialLoopWork_lhs
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) :
    initialLoopWork tapes address count entries tapes.liftedLhs =
      programBinaryTape address.bits := by
  have hlhsRhs : tapes.liftedLhs ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hlhsCount : tapes.liftedLhs ≠
      tapes.lifted.data.update.remaining :=
    tapes.lifted.data.ne (by decide)
  have hlhsBuffer : tapes.liftedLhs ≠ tapes.buffer := by
    exact tapes.liftedData_ne_buffer 13
  unfold initialLoopWork
  rw [Function.update_of_ne hlhsBuffer,
    Function.update_of_ne hlhsCount,
    Function.update_of_ne hlhsRhs, Function.update_self]

private theorem initialLoopWork_rhs
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) :
    initialLoopWork tapes address count entries tapes.lifted.data.rhs =
      programBinaryTape (1 : ℕ).bits := by
  have hrhsCount : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.remaining :=
    tapes.lifted.data.ne (by decide)
  have hrhsBuffer : tapes.lifted.data.rhs ≠ tapes.buffer := by
    exact tapes.liftedData_ne_buffer 14
  unfold initialLoopWork
  rw [Function.update_of_ne hrhsBuffer,
    Function.update_of_ne hrhsCount, Function.update_self]

private theorem initialLoopWork_count
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) :
    initialLoopWork tapes address count entries
        tapes.lifted.data.update.remaining =
      programBinaryTape count.bits := by
  have hcountBuffer : tapes.lifted.data.update.remaining ≠ tapes.buffer := by
    exact tapes.liftedData_ne_buffer 9
  unfold initialLoopWork
  rw [Function.update_of_ne hcountBuffer,
    Function.update_self]

private theorem initialLoopWork_buffer
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) :
    initialLoopWork tapes address count entries tapes.buffer =
      programBinaryPrefixTape (entries.flatMap Entry.encode) := by
  simp [initialLoopWork]

private theorem initialLoopWork_other
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) (i : Fin (n + 1))
    (hlhs : i ≠ tapes.liftedLhs) (hrhs : i ≠ tapes.lifted.data.rhs)
    (hcount : i ≠ tapes.lifted.data.update.remaining)
    (hbuffer : i ≠ tapes.buffer) :
    initialLoopWork tapes address count entries i = TM.resetBinaryBlank := by
  unfold initialLoopWork
  rw [Function.update_of_ne hbuffer, Function.update_of_ne hcount,
    Function.update_of_ne hrhs, Function.update_of_ne hlhs]
  rfl

theorem initialLoopWork_ready_internal
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) :
    InitialLoopReady tapes address count entries
      (initialLoopWork tapes address count entries) := by
  have haddress := Tape.init_move_right_hasBinaryNat address
  have hvalue := Tape.init_move_right_hasBinaryNat 1
  have hcount := Tape.init_move_right_hasBinaryNat count
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have hblankParked : TM.Parked TM.resetBinaryBlank :=
    ⟨by rw [hblankNat.2.1], hblankNat.2.hasBinaryContent.cells_ne_start⟩
  refine
    { address := by
        rw [initialLoopWork_lhs]
        simpa only [programBinaryTape] using! haddress
      value := by
        rw [initialLoopWork_rhs]
        simpa only [programBinaryTape] using! hvalue
      count := by
        rw [initialLoopWork_count]
        simpa only [programBinaryTape] using! hcount
      buffer := by
        rw [initialLoopWork_buffer]
        exact programBinaryPrefixTape_hasBinaryPrefix _
      parked := ?_
      frame := initialLoopWork_other tapes address count entries }
  intro i
  by_cases hlhs : i = tapes.liftedLhs
  · subst i
    rw [initialLoopWork_lhs]
    exact binaryTape_parked _
  by_cases hrhs : i = tapes.lifted.data.rhs
  · subst i
    rw [initialLoopWork_rhs]
    exact binaryTape_parked _
  by_cases hcountIdx : i = tapes.lifted.data.update.remaining
  · subst i
    rw [initialLoopWork_count]
    exact binaryTape_parked _
  by_cases hbuffer : i = tapes.buffer
  · subst i
    rw [initialLoopWork_buffer]
    exact programBinaryPrefixTape_parked _
  · rw [initialLoopWork_other tapes address count entries i hlhs hrhs
      hcountIdx hbuffer]
    exact hblankParked

private theorem parked_of_binaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem parked_of_binaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    (show t.HasBinaryContent bits from h.2).cells_ne_start⟩

private theorem parked_of_binarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private def initialInputOneWrap (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialOneBitTM tapes).Q) :
    Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q :=
  { state := .inr (.inl c.state)
    input := c.input
    work := c.work
    output := c.output }

private def initialInputZeroWrap (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q) :
    Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q :=
  { state := .inr (.inr c.state)
    input := c.input
    work := c.work
    output := c.output }

private theorem initialInputLoopTM_one_step
    (tapes : ControlInstructionTapes n)
    {c c' : Complexity.Cfg (n + 1) (initialOneBitTM tapes).Q}
    (hstep : (initialOneBitTM tapes).step c = some c') :
    (initialInputLoopTM tapes).step (initialInputOneWrap tapes c) =
      some (initialInputOneWrap tapes c') := by
  have hne : c.state ≠ (initialOneBitTM tapes).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by simp [initialInputOneWrap, initialInputLoopTM])]
  simp only [initialInputOneWrap, initialInputLoopTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize (initialOneBitTM tapes).δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ :=
    action
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem initialInputLoopTM_zero_step
    (tapes : ControlInstructionTapes n)
    {c c' : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q}
    (hstep : (initialZeroBitTM tapes).step c = some c') :
    (initialInputLoopTM tapes).step (initialInputZeroWrap tapes c) =
      some (initialInputZeroWrap tapes c') := by
  have hne : c.state ≠ (initialZeroBitTM tapes).qhalt :=
    TM.state_ne_qhalt_of_step hstep
  rw [TM.step, ite_eq_right (by simp [initialInputZeroWrap, initialInputLoopTM])]
  simp only [initialInputZeroWrap, initialInputLoopTM, hne, ↓reduceIte]
  rw [TM.step, ite_eq_right hne] at hstep
  revert hstep
  generalize (initialZeroBitTM tapes).δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ :=
    action
  intro hstep
  cases Option.some.inj hstep
  rfl

private theorem initialInputLoopTM_one_reachesIn
    (tapes : ControlInstructionTapes n)
    {time : ℕ} {c c' : Complexity.Cfg (n + 1) (initialOneBitTM tapes).Q}
    (hreach : (initialOneBitTM tapes).reachesIn time c c') :
    (initialInputLoopTM tapes).reachesIn time
      (initialInputOneWrap tapes c) (initialInputOneWrap tapes c') :=
  TM.reachesIn_map (initialInputOneWrap tapes)
    (fun _ _ => initialInputLoopTM_one_step tapes) hreach

private theorem initialInputLoopTM_zero_reachesIn
    (tapes : ControlInstructionTapes n)
    {time : ℕ} {c c' : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q}
    (hreach : (initialZeroBitTM tapes).reachesIn time c c') :
    (initialInputLoopTM tapes).reachesIn time
      (initialInputZeroWrap tapes c) (initialInputZeroWrap tapes c') :=
  TM.reachesIn_map (initialInputZeroWrap tapes)
    (fun _ _ => initialInputLoopTM_zero_step tapes) hreach

private theorem initialInputLoopTM_step_scan_one
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q)
    (hstate : c.state = .inl .scan) (hone : c.input.read = Γ.one)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (initialInputLoopTM tapes).step c = some
      { state := .inr (.inl (initialOneBitTM tapes).qstart)
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [initialInputLoopTM])]
  simp only [initialInputLoopTM, hstate, hone, TM.allReadBack,
    reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · simp [TM.idleDir, Tape.move]
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir,
      ite_eq_right houtput]
    rfl

private theorem initialInputLoopTM_step_scan_zero
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q)
    (hstate : c.state = .inl .scan) (hzero : c.input.read = Γ.zero)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (initialInputLoopTM tapes).step c = some
      { state := .inr (.inr (initialZeroBitTM tapes).qstart)
        input := c.input
        work := c.work
        output := c.output } := by
  have hstart : c.input.read ≠ Γ.start := by rw [hzero]; decide
  have hblank : c.input.read ≠ Γ.blank := by rw [hzero]; decide
  have hone : c.input.read ≠ Γ.one := by rw [hzero]; decide
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [initialInputLoopTM])]
  simp only [initialInputLoopTM, hstate, hblank, hone, TM.allReadBack,
    ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · simp [TM.idleDir, hstart, Tape.move]
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir,
      ite_eq_right houtput]
    rfl

private theorem initialInputLoopTM_step_scan_blank
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q)
    (hstate : c.state = .inl .scan) (hblank : c.input.read = Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (initialInputLoopTM tapes).step c = some
      { state := .inl .done
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step, ite_eq_right (by rw [hstate]; simp [initialInputLoopTM])]
  simp only [initialInputLoopTM, hstate, hblank, TM.allReadBack,
    ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · simp [TM.idleDir, Tape.move]
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir,
      ite_eq_right houtput]
    rfl

private theorem initialInputLoopTM_step_one_halt
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialOneBitTM tapes).Q)
    (hhalt : (initialOneBitTM tapes).halted c)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (initialInputLoopTM tapes).step (initialInputOneWrap tapes c) = some
      { state := .inl .scan
        input := c.input.move Dir3.right
        work := c.work
        output := c.output } := by
  rw [TM.step,
    ite_eq_right (by simp [initialInputOneWrap, initialInputLoopTM])]
  simp only [initialInputOneWrap, initialInputLoopTM, hhalt, ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · rfl
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir,
      ite_eq_right houtput]
    rfl

private theorem initialInputLoopTM_step_zero_halt
    (tapes : ControlInstructionTapes n)
    (c : Complexity.Cfg (n + 1) (initialZeroBitTM tapes).Q)
    (hhalt : (initialZeroBitTM tapes).halted c)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (initialInputLoopTM tapes).step (initialInputZeroWrap tapes c) = some
      { state := .inl .scan
        input := c.input.move Dir3.right
        work := c.work
        output := c.output } := by
  rw [TM.step,
    ite_eq_right (by simp [initialInputZeroWrap, initialInputLoopTM])]
  simp only [initialInputZeroWrap, initialInputLoopTM, hhalt, ↓reduceIte]
  refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr
    ⟨rfl, ?_, ?_, ?_⟩)
  · rfl
  · funext i
    rw [TM.writeAndMove_readBack _ (hwork i), TM.idleDir,
      ite_eq_right (hwork i)]
    rfl
  · rw [TM.writeAndMove_readBack _ houtput, TM.idleDir,
      ite_eq_right houtput]
    rfl

private theorem copyWorkToWorkTM_exact_hoareTime
    (src dst : Fin n) (hne : src ≠ dst) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : work₀ src = programBinaryTape bits)
    (hdst : work₀ dst = TM.resetBinaryBlank)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.copyWorkToWorkTM src dst).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update
          (Function.update work₀ src (programBinaryPrefixTape bits))
          dst (programBinaryPrefixTape bits) ∧
        out = out₀)
      (bits.length + 1) := by
  let P : Tape → (Fin n → Tape) → Tape → Prop :=
    fun inp work out =>
      inp = inp₀ ∧ out = out₀ ∧
      ∀ i, i ≠ src → i ≠ dst → work i = work₀ i
  have hraw := TM.copyWorkToWorkTM_hoareTime_frame_of_binaryString
    src dst hne bits (P := P) (by
      intro inp work out inp' work' out' hP _ _ _ _ hinp' hout' hframe
      rcases hP with ⟨hinp, hout, hworkFrame⟩
      exact ⟨hinp'.trans hinp, hout'.trans hout,
        fun i hisrc hidst => (hframe i hisrc hidst).trans
          (hworkFrame i hisrc hidst)⟩)
  apply hraw.consequence
  · rintro inp work out ⟨hinp, hworkEq, hout⟩
    subst inp
    subst work
    subst out
    refine ⟨?_, ?_, hinput.read_ne_start, houtput.read_ne_start,
      houtput.1, ?_, rfl, rfl, ?_⟩
    · simpa only [programBinaryTape] using! hsrc
    · simpa [TM.resetBinaryBlank] using! hdst
    · intro i _ _
      exact ⟨(hwork i).read_ne_start, (hwork i).1⟩
    · intro i _ _
      rfl
  · intro inp work out hpost
    rcases hpost with ⟨hsrcCells, hsrcHead, hdstPrefix, hdstStart,
      hinp, hout, hframe⟩
    have hsrcEq : work src = programBinaryPrefixTape bits := by
      apply Tape.ext
      · simpa [programBinaryPrefixTape] using! hsrcHead
      · simpa [programBinaryPrefixTape] using! hsrcCells
    have hdstEq : work dst = programBinaryPrefixTape bits := by
      apply Tape.ext
      · simpa [programBinaryPrefixTape] using! hdstPrefix.1
      · rw [programBinaryPrefixTape]
        exact hdstPrefix.cells_eq_init hdstStart
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hidst : i = dst
    · subst i
      simp [hdstEq]
    · by_cases hisrc : i = src
      · subst i
        simp [hne, hsrcEq]
      · simp [hidst, hisrc, hframe i hisrc hidst]
  · exact le_rfl

private def initialAbiCountWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) (count : ℕ) : Fin (n + 1) → Tape :=
  Function.update work tapes.lifted.data.update.resultCount
    (programBinaryTape count.bits)

private def initialAbiBufferWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) (store : Store) : Fin (n + 1) → Tape :=
  Function.update work tapes.buffer
    (programBinaryTape (store.flatMap Entry.encode))

private def initialAbiCopiedWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) (store : Store) : Fin (n + 1) → Tape :=
  Function.update
    (Function.update work tapes.buffer
      (programBinaryPrefixTape (store.flatMap Entry.encode)))
    tapes.liftedSource
      (programBinaryPrefixTape (store.flatMap Entry.encode))

private def initialAbiSourceWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) (store : Store) : Fin (n + 1) → Tape :=
  Function.update work tapes.liftedSource
    (programBinaryTape (store.flatMap Entry.encode))

private def initialAbiBufferResetWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) : Fin (n + 1) → Tape :=
  Function.update work tapes.buffer TM.resetBinaryBlank

private def initialAbiFinalWork (tapes : ControlInstructionTapes n)
    (work : Fin (n + 1) → Tape) : Fin (n + 1) → Tape :=
  TM.resetBinaryWorkManyResult work (initialCleanupTargets tapes)

private theorem eq_programBinaryPrefixTape_of_hasBinaryPrefix
    {t : Tape} {bits : List Bool} (hprefix : t.HasBinaryPrefix bits)
    (hstart : t.cells 0 = Γ.start) :
    t = programBinaryPrefixTape bits := by
  apply Tape.ext
  · simpa [programBinaryPrefixTape] using! hprefix.1
  · rw [programBinaryPrefixTape]
    exact hprefix.cells_eq_init hstart

private theorem parked_update {work : Fin n → Tape} {idx : Fin n}
    {tape : Tape} (hwork : ∀ i, TM.Parked (work i))
    (htape : TM.Parked tape) :
    ∀ i, TM.Parked (Function.update work idx tape i) := by
  intro i
  by_cases hi : i = idx
  · subst i
    simp [htape]
  · simp [hi, hwork i]

private theorem exact_phaseTransition_of_parked
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    ∀ inp work out,
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      TM.transitionInput inp = inp₀ ∧
        (fun i => TM.transitionTape (work i)) = work₀ ∧
        TM.transitionTape out = out₀ := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact TM.phaseTransition_eq_self_of_reads_ne_start
    hinput.read_ne_start (fun i => (hwork i).read_ne_start)
    houtput.read_ne_start

private theorem rewindPrefixWorkTM_exact_hoareTime
    (idx : Fin n) (bits : List Bool) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : work₀ idx = programBinaryPrefixTape bits)
    (hinput : TM.Parked inp₀) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (TM.rewindWorkTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ idx (programBinaryTape bits) ∧
        out = out₀)
      (bits.length + 1 + 2) := by
  have hprefix := programBinaryPrefixTape_hasBinaryPrefix bits
  have hraw := TM.rewindBinaryWorkTM_hoareTime_frame idx bits
    (bits.length + 1) inp₀ work₀ out₀
    (by rw [htarget]; exact hprefix.2)
    (by rw [htarget]; simp [programBinaryPrefixTape])
    (by rw [htarget]; simp [programBinaryPrefixTape])
    hinput (fun i _ => hwork i) houtput
  apply hraw.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hidx, hframe, hout⟩
    refine ⟨hinp, ?_, hout⟩
    funext i
    by_cases hi : i = idx
    · subst i
      simp [hidx, programBinaryTape]
    · simp [hi, hframe i hi]
  · exact le_rfl

private theorem initialAbiFinalWork_eq_programSnapshotWork
    (tapes : ControlInstructionTapes n) (store : Store) (length : ℕ)
    (work₀ : Fin (n + 1) → Tape)
    (hready : InitialLoopReady tapes length store.length store work₀) :
    initialAbiFinalWork tapes
        (initialAbiBufferResetWork tapes
          (initialAbiSourceWork tapes
            (initialAbiCopiedWork tapes
              (initialAbiBufferWork tapes
                (initialAbiCountWork tapes work₀ store.length) store)
              store)
            store)) =
      programSnapshotWork tapes { pc := 0, store := store } := by
  have hsourceLhs : tapes.liftedSource ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  have hsourceRhs : tapes.liftedSource ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hsourceRemaining : tapes.liftedSource ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hsourceResult : tapes.liftedSource ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hlhsRhs : tapes.liftedLhs ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hlhsRemaining : tapes.liftedLhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hlhsResult : tapes.liftedLhs ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hrhsRemaining : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hrhsResult : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hremainingResult : tapes.lifted.data.update.remaining ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hlhsSource := hsourceLhs.symm
  have hrhsSource := hsourceRhs.symm
  have hremainingSource := hsourceRemaining.symm
  have hresultSource := hsourceResult.symm
  have hrhsLhs := hlhsRhs.symm
  have hremainingLhs := hlhsRemaining.symm
  have hresultLhs := hlhsResult.symm
  have hremainingRhs := hrhsRemaining.symm
  have hresultRhs := hrhsResult.symm
  have hresultRemaining := hremainingResult.symm
  have hsourcePC : tapes.liftedSource ≠ tapes.liftedPC :=
    tapes.liftedPC_ne_source.symm
  have hlhsPC : tapes.liftedLhs ≠ tapes.liftedPC :=
    tapes.lifted.lhs_ne_pc
  have hrhsPC : tapes.lifted.data.rhs ≠ tapes.liftedPC :=
    tapes.lifted.data_ne_pc 14
  have hremainingPC : tapes.lifted.data.update.remaining ≠
      tapes.liftedPC := tapes.lifted.data_ne_pc 9
  have hresultPC : tapes.lifted.data.update.resultCount ≠
      tapes.liftedPC := tapes.lifted.data_ne_pc 12
  have hsourceBuffer : tapes.liftedSource ≠ tapes.buffer :=
    tapes.liftedSource_ne_buffer
  have hlhsBuffer : tapes.liftedLhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 13
  have hrhsBuffer : tapes.lifted.data.rhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 14
  have hremainingBuffer : tapes.lifted.data.update.remaining ≠
      tapes.buffer := tapes.liftedData_ne_buffer 9
  have hresultBuffer : tapes.lifted.data.update.resultCount ≠
      tapes.buffer := tapes.liftedData_ne_buffer 12
  have hpcBuffer : tapes.liftedPC ≠ tapes.buffer :=
    tapes.liftedPC_ne_buffer
  have hcountEq :
      work₀ tapes.lifted.data.update.remaining =
        programBinaryTape store.length.bits := by
    simpa only [programBinaryTape] using! hready.count.eq_init_move_right
  funext i
  by_cases hlhs : i = tapes.liftedLhs
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork,
      programBinaryTape, TM.resetBinaryBlank]
  by_cases hrhs : i = tapes.lifted.data.rhs
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork,
      programBinaryTape, TM.resetBinaryBlank]
  by_cases hsource : i = tapes.liftedSource
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork]
  by_cases hremaining : i = tapes.lifted.data.update.remaining
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork]
  by_cases hresult : i = tapes.lifted.data.update.resultCount
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork]
  by_cases hpc : i = tapes.liftedPC
  · subst i
    have hpcBlank : work₀ tapes.liftedPC = TM.resetBinaryBlank :=
      hready.frame _ tapes.lifted.lhs_ne_pc.symm
        (tapes.lifted.data_ne_pc 14).symm
        (tapes.lifted.data_ne_pc 9).symm tapes.liftedPC_ne_buffer
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork, programBinaryTape,
      TM.resetBinaryBlank]
  by_cases hbuffer : i = tapes.buffer
  · subst i
    simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, initialCleanupTargets,
      TM.resetBinaryWorkManyResult, programSnapshotWork,
      programBinaryTape, TM.resetBinaryBlank]
  have hblank := hready.frame i hlhs hrhs hremaining hbuffer
  simp_all [initialAbiFinalWork, initialAbiBufferResetWork,
    initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
    initialAbiCountWork, initialCleanupTargets,
    TM.resetBinaryWorkManyResult, programSnapshotWork]

/-- A zero input bit preserves the streaming frame and advances only the
current register address. -/
theorem initialZeroBitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (out₀ : Tape) (hready : InitialLoopReady tapes address count entries work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (initialZeroBitTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InitialLoopReady tapes (address + 1) count entries work ∧
        out = out₀)
      (TM.binarySuccTime address) := by
  have hrun := TM.binarySuccTM_hoareTime_frame tapes.liftedLhs address
    inp₀ work₀ out₀ hready.address hinput.read_ne_start
    (fun i _ => (hready.parked i).read_ne_start) houtput.read_ne_start
  intro inp work out hpre
  obtain ⟨c, time, htime, hreach, hhalt, hinputEq, hframe,
      haddress, houtputEq⟩ := hrun inp work out hpre
  refine ⟨c, time, htime, hreach, hhalt, hinputEq, ?_, houtputEq⟩
  refine
    { address := haddress
      value := by
        rw [hframe tapes.lifted.data.rhs (tapes.lifted.data.ne (by decide))]
        exact hready.value
      count := by
        rw [hframe tapes.lifted.data.update.remaining
          (tapes.lifted.data.ne (by decide))]
        exact hready.count
      buffer := by
        rw [hframe tapes.buffer (tapes.liftedData_ne_buffer 13).symm]
        exact hready.buffer
      parked := ?_
      frame := ?_ }
  · intro i
    by_cases hi : i = tapes.liftedLhs
    · subst i
      exact parked_of_binaryNat haddress
    · rw [hframe i hi]
      exact hready.parked i
  · intro i hlhs hrhs hcount hbuffer
    rw [hframe i hlhs]
    exact hready.frame i hlhs hrhs hcount hbuffer

/-- A one input bit appends the current `(address, 1)` entry and advances the
entry count and current address, restoring every reusable source cursor. -/
theorem initialOneBitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (address count : ℕ)
    (entries : Store) (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (out₀ : Tape) (hready : InitialLoopReady tapes address count entries work₀)
    (hinput : TM.Parked inp₀) (houtput : out₀ = TM.resetBinaryBlank) :
    (initialOneBitTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InitialLoopReady tapes (address + 1) (count + 1)
          (entries ++ [(address, 1)]) work ∧
        out = out₀)
      (rewindEntryEncodeRestoreTime (address, 1) + 1 +
        (TM.binarySuccTime count + 1 + TM.binarySuccTime address)) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let baseWork : Fin n → Tape := fun i => work₀ (Fin.castSucc i)
  have hbaseAddress :
      (baseWork (initialBitEntryTapes tapes).address).HasBinaryNat address := by
    exact hready.address
  have hbaseValue :
      (baseWork (initialBitEntryTapes tapes).value).HasBinaryNat 1 := by
    exact hready.value
  have hbase := rewindEntryEncodeRestoreTM_hoareTime_frame
    (initialBitEntryTapes tapes) (address, 1)
    (entries.flatMap Entry.encode) inp₀ baseWork (work₀ tapes.buffer)
    hbaseAddress hbaseValue hinput
    (fun i _ _ => hready.parked (Fin.castSucc i)) hready.buffer
  have hlift := TM.retargetOutput_hoareTime
    (rewindEntryEncodeRestoreTM (initialBitEntryTapes tapes)) hbase
  obtain ⟨emitted, emitTime, hemitTime, hemitReach, hemitHalt,
      hemitPost, hemitOutput⟩ :=
    hlift inp₀ work₀ out₀
      ⟨⟨rfl, rfl, rfl⟩, by simpa [TM.resetBinaryBlank] using! houtput⟩
  rcases hemitPost with ⟨hemitInput, hemitBaseWork, hemitBuffer⟩
  have hemitOutput' : emitted.output = out₀ := by
    exact hemitOutput.trans (by simpa [TM.resetBinaryBlank] using! houtput.symm)
  have hemitFrame (i : Fin (n + 1)) (hi : i ≠ tapes.buffer) :
      emitted.work i = work₀ i := by
    have hil : i.val < n := by
      have hle : i.val ≤ n := by omega
      have hne : i.val ≠ n := by
        intro hval
        apply hi
        apply Fin.ext
        simpa [ControlInstructionTapes.buffer] using! hval
      omega
    let j : Fin n := ⟨i.val, hil⟩
    have hij : i = Fin.castSucc j := by
      apply Fin.ext
      rfl
    rw [hij]
    exact congrFun hemitBaseWork j
  have hemitInputParked : TM.Parked emitted.input := by
    rw [hemitInput]
    exact hinput
  have hemitOutputParked : TM.Parked emitted.output := by
    rw [hemitOutput']
    rw [houtput]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hemitWorkParked : ∀ i, TM.Parked (emitted.work i) := by
    intro i
    by_cases hi : i = tapes.buffer
    · subst i
      exact parked_of_binaryPrefix hemitBuffer
    · rw [hemitFrame i hi]
      exact hready.parked i
  have hremainingBuffer : tapes.lifted.data.update.remaining ≠
      tapes.buffer := tapes.liftedData_ne_buffer 9
  have hlhsBuffer : tapes.liftedLhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 13
  have hrhsBuffer : tapes.lifted.data.rhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 14
  have hlhsRemaining : tapes.liftedLhs ≠
      tapes.lifted.data.update.remaining :=
    tapes.lifted.data.ne (by decide)
  have hremainingLhs : tapes.lifted.data.update.remaining ≠
      tapes.liftedLhs := hlhsRemaining.symm
  have hrhsLhs : tapes.lifted.data.rhs ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  have hrhsRemaining : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.remaining :=
    tapes.lifted.data.ne (by decide)
  have hemitCount :
      (emitted.work tapes.lifted.data.update.remaining).HasBinaryNat count := by
    rw [hemitFrame _ hremainingBuffer]
    exact hready.count
  have hcountRun := TM.binarySuccTM_hoareTime_frame
    tapes.lifted.data.update.remaining count emitted.input emitted.work
    emitted.output hemitCount hemitInputParked.read_ne_start
    (fun i _ => (hemitWorkParked i).read_ne_start)
    hemitOutputParked.read_ne_start
  obtain ⟨counted, countTime, hcountTime, hcountReach, hcountHalt,
      hcountInput, hcountFrame, hcountValue, hcountOutput⟩ :=
    hcountRun emitted.input emitted.work emitted.output ⟨rfl, rfl, rfl⟩
  have hcountInputParked : TM.Parked counted.input := by
    rw [hcountInput]
    exact hemitInputParked
  have hcountOutputParked : TM.Parked counted.output := by
    rw [hcountOutput]
    exact hemitOutputParked
  have hcountWorkParked : ∀ i, TM.Parked (counted.work i) := by
    intro i
    by_cases hi : i = tapes.lifted.data.update.remaining
    · subst i
      exact parked_of_binaryNat hcountValue
    · rw [hcountFrame i hi]
      exact hemitWorkParked i
  have hcountAddress :
      (counted.work tapes.liftedLhs).HasBinaryNat address := by
    rw [hcountFrame _ hlhsRemaining]
    rw [hemitFrame _ hlhsBuffer]
    exact hready.address
  have haddressRun := TM.binarySuccTM_hoareTime_frame tapes.liftedLhs
    address counted.input counted.work counted.output hcountAddress
    hcountInputParked.read_ne_start
    (fun i _ => (hcountWorkParked i).read_ne_start)
    hcountOutputParked.read_ne_start
  obtain ⟨advanced, addressTime, haddressTime, haddressReach,
      haddressHalt, haddressInput, haddressFrame, haddressValue,
      haddressOutput⟩ :=
    haddressRun counted.input counted.work counted.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hcountInputTransition, hcountWorkTransition,
      hcountOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hcountInputParked.read_ne_start
      (fun i => (hcountWorkParked i).read_ne_start)
      hcountOutputParked.read_ne_start
  have haddressReach' : (TM.binarySuccTM tapes.liftedLhs).reachesIn
      addressTime
      { state := (TM.binarySuccTM tapes.liftedLhs).qstart
        input := TM.transitionInput counted.input
        work := fun i => TM.transitionTape (counted.work i)
        output := TM.transitionTape counted.output }
      advanced := by
    simpa only [hcountInputTransition, hcountWorkTransition,
      hcountOutputTransition] using! haddressReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.binarySuccTM tapes.lifted.data.update.remaining)
    (TM.binarySuccTM tapes.liftedLhs) hcountReach hcountHalt haddressReach'
  let tailFinal := TM.phase2Wrap
    (TM.binarySuccTM tapes.lifted.data.update.remaining)
    (TM.binarySuccTM tapes.liftedLhs) advanced
  have htailHalt :
      (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
        (TM.binarySuccTM tapes.liftedLhs)).halted tailFinal := by
    rw [TM.phase2Wrap_halted_iff]
    exact haddressHalt
  obtain ⟨hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hemitInputParked.read_ne_start
      (fun i => (hemitWorkParked i).read_ne_start)
      hemitOutputParked.read_ne_start
  have htailReach' :
      (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
        (TM.binarySuccTM tapes.liftedLhs)).reachesIn
        (countTime + 1 + addressTime)
        { state :=
            (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
              (TM.binarySuccTM tapes.liftedLhs)).qstart
          input := TM.transitionInput emitted.input
          work := fun i => TM.transitionTape (emitted.work i)
          output := TM.transitionTape emitted.output }
        tailFinal := by
    simpa only [hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition] using! htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeRestoreTM (initialBitEntryTapes tapes)).retargetOutput
    (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
      (TM.binarySuccTM tapes.liftedLhs))
    hemitReach hemitHalt htailReach'
  let finalCfg := TM.phase2Wrap
    (rewindEntryEncodeRestoreTM (initialBitEntryTapes tapes)).retargetOutput
    (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
      (TM.binarySuccTM tapes.liftedLhs)) tailFinal
  refine ⟨finalCfg, emitTime + 1 + (countTime + 1 + addressTime),
    ?_, hreach, ?_, ?_⟩
  · omega
  · change (initialOneBitTM tapes).halted finalCfg
    unfold initialOneBitTM
    exact (TM.phase2Wrap_halted_iff (rewindEntryEncodeRestoreTM (initialBitEntryTapes tapes)).retargetOutput
    (TM.seqTM (TM.binarySuccTM tapes.lifted.data.update.remaining)
      (TM.binarySuccTM tapes.liftedLhs)) tailFinal).mpr htailHalt
  · refine ⟨?_, ?_, ?_⟩
    · change advanced.input = inp₀
      exact haddressInput.trans (hcountInput.trans hemitInput)
    · refine
        { address := by
            change (advanced.work tapes.liftedLhs).HasBinaryNat (address + 1)
            exact haddressValue
          value := ?_
          count := ?_
          buffer := ?_
          parked := ?_
          frame := ?_ }
      · change (advanced.work tapes.lifted.data.rhs).HasBinaryNat 1
        rw [haddressFrame _ hrhsLhs, hcountFrame _ hrhsRemaining,
          hemitFrame _ hrhsBuffer]
        exact hready.value
      · change (advanced.work
          tapes.lifted.data.update.remaining).HasBinaryNat (count + 1)
        rw [haddressFrame _ hremainingLhs]
        exact hcountValue
      · change (advanced.work tapes.buffer).HasBinaryPrefix
          ((entries ++ [(address, 1)]).flatMap Entry.encode)
        rw [haddressFrame _ hlhsBuffer.symm,
          hcountFrame _ hremainingBuffer.symm]
        simpa [List.flatMap_append] using! hemitBuffer
      · intro i
        change TM.Parked (advanced.work i)
        by_cases hi : i = tapes.liftedLhs
        · subst i
          exact parked_of_binaryNat haddressValue
        · rw [haddressFrame i hi]
          exact hcountWorkParked i
      · intro i hlhs hrhs hcountIdx hbuffer
        change advanced.work i = TM.resetBinaryBlank
        rw [haddressFrame i hlhs, hcountFrame i hcountIdx,
          hemitFrame i hbuffer]
        exact hready.frame i hlhs hrhs hcountIdx hbuffer
    · change advanced.output = out₀
      exact haddressOutput.trans (hcountOutput.trans hemitOutput')

/-- The custom scanner consumes exactly the advertised Boolean suffix,
streaming its nonzero entries into the sparse-store buffer. -/
theorem initialInputLoopTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (address count : ℕ) (entries : Store)
    (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape) (out₀ : Tape)
    (hinput : inp₀.HasBinarySuffix input)
    (hready : InitialLoopReady tapes address count entries work₀)
    (houtput : out₀ = TM.resetBinaryBlank) :
    (initialInputLoopTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.HasBinarySuffix [] ∧
        InitialLoopReady tapes (address + input.length)
          (count + inputTrueCount input)
          (entries ++ inputBitStoreFrom address input) work ∧
        out = out₀)
      (initialInputLoopTime tapes address count input) := by
  induction input generalizing address count entries inp₀ work₀ out₀ with
  | nil =>
      intro inp work out hpre
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      let done : Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q :=
        { state := .inl .done
          input := inp₀
          work := work₀
          output := out₀ }
      have hstep := initialInputLoopTM_step_scan_blank tapes
        ({ state := (initialInputLoopTM tapes).qstart
           input := inp₀
           work := work₀
           output := out₀ } :
          Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q)
        rfl hinput.read_nil
        (fun i => (hready.parked i).read_ne_start)
        (by
          rw [houtput]
          have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
            simpa [TM.resetBinaryBlank] using!
              Tape.init_move_right_hasBinaryNat 0
          exact (parked_of_binaryNat hblankNat).read_ne_start)
      refine ⟨done, 1, by simp [initialInputLoopTime],
        .step (by simpa [done] using! hstep) .zero, ?_, ?_⟩
      · change done.state = (initialInputLoopTM tapes).qhalt
        rfl
      · exact ⟨hinput, by simpa [inputTrueCount, inputBitStoreFrom], rfl⟩
  | cons bit rest ih =>
      intro inp work out hpre
      rcases hpre with ⟨hinp, hwork, hout⟩
      subst inp
      subst work
      subst out
      let scan : Complexity.Cfg (n + 1) (initialInputLoopTM tapes).Q :=
        { state := (initialInputLoopTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ }
      have hinputParked : TM.Parked inp₀ := parked_of_binarySuffix hinput
      have houtputParked : TM.Parked out₀ := by
        rw [houtput]
        have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
          simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
        exact parked_of_binaryNat hblankNat
      cases bit with
      | false =>
          let bodyStart : Complexity.Cfg (n + 1)
              (initialZeroBitTM tapes).Q :=
            { state := (initialZeroBitTM tapes).qstart
              input := inp₀
              work := work₀
              output := out₀ }
          have hread : inp₀.read = Γ.zero := by
            simpa [Γ.ofBool] using! hinput.read_cons
          have hscanStep := initialInputLoopTM_step_scan_zero tapes scan
            rfl hread (fun i => (hready.parked i).read_ne_start)
            houtputParked.read_ne_start
          have hscanReach : (initialInputLoopTM tapes).reachesIn 1 scan
              (initialInputZeroWrap tapes bodyStart) :=
            .step (by simpa [scan, bodyStart, initialInputZeroWrap] using!
              hscanStep) .zero
          have hbody := initialZeroBitTM_hoareTime_internal tapes address
            count entries inp₀ work₀ out₀ hready hinputParked
            houtputParked
          obtain ⟨bodyDone, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
              hbodyInput, hbodyReady, hbodyOutput⟩ :=
            hbody inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
          have hbodyLift := initialInputLoopTM_zero_reachesIn tapes hbodyReach
          let nextScan : Complexity.Cfg (n + 1)
              (initialInputLoopTM tapes).Q :=
            { state := .inl .scan
              input := bodyDone.input.move Dir3.right
              work := bodyDone.work
              output := bodyDone.output }
          have hseamStep := initialInputLoopTM_step_zero_halt tapes bodyDone
            hbodyHalt (fun i => (hbodyReady.parked i).read_ne_start)
            (by rw [hbodyOutput]; exact houtputParked.read_ne_start)
          have hseamReach : (initialInputLoopTM tapes).reachesIn 1
              (initialInputZeroWrap tapes bodyDone) nextScan :=
            .step (by simpa [nextScan] using! hseamStep) .zero
          have hnextInput :
              (bodyDone.input.move Dir3.right).HasBinarySuffix rest := by
            rw [hbodyInput]
            exact hinput.move_right_cons
          have hnextOutput : bodyDone.output = TM.resetBinaryBlank :=
            hbodyOutput.trans houtput
          have htail := ih (address + 1) count entries
            (bodyDone.input.move Dir3.right) bodyDone.work bodyDone.output
            hnextInput hbodyReady hnextOutput
          obtain ⟨tailDone, tailTime, htailTime, htailReach, htailHalt,
              htailInput, htailReady, htailOutput⟩ :=
            htail _ _ _ ⟨rfl, rfl, rfl⟩
          have hreach := TM.reachesIn_trans (initialInputLoopTM tapes)
            hscanReach (TM.reachesIn_trans (initialInputLoopTM tapes)
              hbodyLift (TM.reachesIn_trans (initialInputLoopTM tapes)
                hseamReach htailReach))
          refine ⟨tailDone, 1 + bodyTime + 1 + tailTime, ?_, ?_,
            htailHalt, ?_⟩
          · simp only [initialInputLoopTime, Bool.false_eq_true,
              ite_false, Nat.add_zero]
            omega
          · simpa [Nat.add_assoc] using! hreach
          · refine ⟨htailInput, ?_, htailOutput.trans hbodyOutput⟩
            simpa [inputTrueCount, inputBitStoreFrom, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using! htailReady
      | true =>
          let bodyStart : Complexity.Cfg (n + 1)
              (initialOneBitTM tapes).Q :=
            { state := (initialOneBitTM tapes).qstart
              input := inp₀
              work := work₀
              output := out₀ }
          have hread : inp₀.read = Γ.one := by
            simpa [Γ.ofBool] using! hinput.read_cons
          have hscanStep := initialInputLoopTM_step_scan_one tapes scan
            rfl hread (fun i => (hready.parked i).read_ne_start)
            houtputParked.read_ne_start
          have hscanReach : (initialInputLoopTM tapes).reachesIn 1 scan
              (initialInputOneWrap tapes bodyStart) :=
            .step (by simpa [scan, bodyStart, initialInputOneWrap] using!
              hscanStep) .zero
          have hbody := initialOneBitTM_hoareTime_internal tapes address
            count entries inp₀ work₀ out₀ hready hinputParked houtput
          obtain ⟨bodyDone, bodyTime, hbodyTime, hbodyReach, hbodyHalt,
              hbodyInput, hbodyReady, hbodyOutput⟩ :=
            hbody inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
          have hbodyLift := initialInputLoopTM_one_reachesIn tapes hbodyReach
          let nextScan : Complexity.Cfg (n + 1)
              (initialInputLoopTM tapes).Q :=
            { state := .inl .scan
              input := bodyDone.input.move Dir3.right
              work := bodyDone.work
              output := bodyDone.output }
          have hseamStep := initialInputLoopTM_step_one_halt tapes bodyDone
            hbodyHalt (fun i => (hbodyReady.parked i).read_ne_start)
            (by rw [hbodyOutput]; exact houtputParked.read_ne_start)
          have hseamReach : (initialInputLoopTM tapes).reachesIn 1
              (initialInputOneWrap tapes bodyDone) nextScan :=
            .step (by simpa [nextScan] using! hseamStep) .zero
          have hnextInput :
              (bodyDone.input.move Dir3.right).HasBinarySuffix rest := by
            rw [hbodyInput]
            exact hinput.move_right_cons
          have hnextOutput : bodyDone.output = TM.resetBinaryBlank :=
            hbodyOutput.trans houtput
          have htail := ih (address + 1) (count + 1)
            (entries ++ [(address, 1)])
            (bodyDone.input.move Dir3.right) bodyDone.work bodyDone.output
            hnextInput hbodyReady hnextOutput
          obtain ⟨tailDone, tailTime, htailTime, htailReach, htailHalt,
              htailInput, htailReady, htailOutput⟩ :=
            htail _ _ _ ⟨rfl, rfl, rfl⟩
          have hreach := TM.reachesIn_trans (initialInputLoopTM tapes)
            hscanReach (TM.reachesIn_trans (initialInputLoopTM tapes)
              hbodyLift (TM.reachesIn_trans (initialInputLoopTM tapes)
                hseamReach htailReach))
          refine ⟨tailDone, 1 + bodyTime + 1 + tailTime, ?_, ?_,
            htailHalt, ?_⟩
          · simp only [initialInputLoopTime, if_true]
            omega
          · simpa [Nat.add_assoc] using! hreach
          · refine ⟨htailInput, ?_, htailOutput.trans hbodyOutput⟩
            simpa [inputTrueCount, inputBitStoreFrom, List.append_assoc,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! htailReady

/-- The setup phase turns the standard all-heads-on-marker configuration into
the exact address-one/count-zero streaming boundary. -/
theorem initialSetupTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (initialSetupTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp.HasBinarySuffix input ∧
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InitialLoopReady tapes 1 0 [] work ∧
        out = TM.resetBinaryBlank)
      (1 + 1 + (TM.binarySuccTime 0 + 1 + TM.binarySuccTime 0)) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  let parkedInput := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let parkedWork : Fin (n + 1) → Tape := fun _ => TM.resetBinaryBlank
  let skipped : Complexity.Cfg (n + 1) (TM.skipTM (n := n + 1)).Q :=
    { state := (TM.skipTM (n := n + 1)).qhalt
      input := parkedInput
      work := parkedWork
      output := TM.resetBinaryBlank }
  have hskipStep : (TM.skipTM (n := n + 1)).step
      { state := (TM.skipTM (n := n + 1)).qstart
        input := Tape.init (input.map Γ.ofBool)
        work := fun _ => Tape.init []
        output := Tape.init [] } = some skipped := by
    rw [TM.step, ite_eq_right (by simp [TM.skipTM])]
    simp only [TM.skipTM]
    refine congrArg some (Complexity.Cfg.ext rfl ?_ ?_ ?_)
    · simp [skipped, parkedInput, TM.idleDir, Tape.read, Tape.move]
    · funext i
      simp [skipped, parkedWork, TM.resetBinaryBlank, TM.idleDir,
        TM.readBackWrite, Tape.read, Tape.write, Tape.move]
    · simp [skipped, TM.resetBinaryBlank, TM.idleDir,
        TM.readBackWrite, Tape.read, Tape.write, Tape.move]
  have hskipReach : (TM.skipTM (n := n + 1)).reachesIn 1
      { state := (TM.skipTM (n := n + 1)).qstart
        input := Tape.init (input.map Γ.ofBool)
        work := fun _ => Tape.init []
        output := Tape.init [] } skipped :=
    .step hskipStep .zero
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have hblankParked : TM.Parked TM.resetBinaryBlank :=
    parked_of_binaryNat hblankNat
  have hparkedInput : TM.Parked parkedInput :=
    parked_of_binarySuffix (by
      simpa only [parkedInput] using! Tape.init_move_right_hasBinarySuffix input)
  have hlhsRun := TM.binarySuccTM_hoareTime_frame tapes.liftedLhs 0
    skipped.input skipped.work skipped.output
    (by simpa [skipped, parkedWork] using! hblankNat)
    (by simpa [skipped] using! hparkedInput.read_ne_start)
    (fun i _ => by simpa [skipped, parkedWork] using!
      hblankParked.read_ne_start)
    (by simpa [skipped] using! hblankParked.read_ne_start)
  obtain ⟨lhsDone, lhsTime, hlhsTime, hlhsReach, hlhsHalt,
      hlhsInput, hlhsFrame, hlhsValue, hlhsOutput⟩ :=
    hlhsRun skipped.input skipped.work skipped.output ⟨rfl, rfl, rfl⟩
  have hlhsRhs : tapes.liftedLhs ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hrhsZero :
      (lhsDone.work tapes.lifted.data.rhs).HasBinaryNat 0 := by
    rw [hlhsFrame _ hlhsRhs.symm]
    simpa [skipped, parkedWork] using! hblankNat
  have hlhsInputParked : TM.Parked lhsDone.input := by
    rw [hlhsInput]
    simpa [skipped] using! hparkedInput
  have hlhsOutputParked : TM.Parked lhsDone.output := by
    rw [hlhsOutput]
    simpa [skipped] using! hblankParked
  have hlhsWorkParked : ∀ i, TM.Parked (lhsDone.work i) := by
    intro i
    by_cases hi : i = tapes.liftedLhs
    · subst i
      exact parked_of_binaryNat hlhsValue
    · rw [hlhsFrame i hi]
      simpa [skipped, parkedWork] using! hblankParked
  have hrhsRun := TM.binarySuccTM_hoareTime_frame
    tapes.lifted.data.rhs 0 lhsDone.input lhsDone.work lhsDone.output
    hrhsZero hlhsInputParked.read_ne_start
    (fun i _ => (hlhsWorkParked i).read_ne_start)
    hlhsOutputParked.read_ne_start
  obtain ⟨rhsDone, rhsTime, hrhsTime, hrhsReach, hrhsHalt,
      hrhsInput, hrhsFrame, hrhsValue, hrhsOutput⟩ :=
    hrhsRun lhsDone.input lhsDone.work lhsDone.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hlhsInputTransition, hlhsWorkTransition,
      hlhsOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hlhsInputParked.read_ne_start
      (fun i => (hlhsWorkParked i).read_ne_start)
      hlhsOutputParked.read_ne_start
  have hrhsReach' : (TM.binarySuccTM tapes.lifted.data.rhs).reachesIn
      rhsTime
      { state := (TM.binarySuccTM tapes.lifted.data.rhs).qstart
        input := TM.transitionInput lhsDone.input
        work := fun i => TM.transitionTape (lhsDone.work i)
        output := TM.transitionTape lhsDone.output }
      rhsDone := by
    simpa only [hlhsInputTransition, hlhsWorkTransition,
      hlhsOutputTransition] using! hrhsReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.binarySuccTM tapes.liftedLhs)
    (TM.binarySuccTM tapes.lifted.data.rhs)
    hlhsReach hlhsHalt hrhsReach'
  let tailDone := TM.phase2Wrap (TM.binarySuccTM tapes.liftedLhs)
    (TM.binarySuccTM tapes.lifted.data.rhs) rhsDone
  have htailHalt :
      (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
        (TM.binarySuccTM tapes.lifted.data.rhs)).halted tailDone := by
    exact (TM.phase2Wrap_halted_iff (TM.binarySuccTM tapes.liftedLhs)
      (TM.binarySuccTM tapes.lifted.data.rhs) rhsDone).mpr hrhsHalt
  obtain ⟨hskipInputTransition, hskipWorkTransition,
      hskipOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hparkedInput.read_ne_start (fun _ => hblankParked.read_ne_start)
      hblankParked.read_ne_start
  have hskipInputTransition' :
      TM.transitionInput skipped.input = skipped.input := by
    simpa [skipped] using! hskipInputTransition
  have hskipWorkTransition' :
      (fun i => TM.transitionTape (skipped.work i)) = skipped.work := by
    simpa [skipped] using! hskipWorkTransition
  have hskipOutputTransition' :
      TM.transitionTape skipped.output = skipped.output := by
    simpa [skipped] using! hskipOutputTransition
  have htailReach' :
      (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
        (TM.binarySuccTM tapes.lifted.data.rhs)).reachesIn
        (lhsTime + 1 + rhsTime)
        { state := (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
            (TM.binarySuccTM tapes.lifted.data.rhs)).qstart
          input := TM.transitionInput skipped.input
          work := fun i => TM.transitionTape (skipped.work i)
          output := TM.transitionTape skipped.output }
        tailDone := by
    simpa only [hskipInputTransition', hskipWorkTransition',
      hskipOutputTransition'] using! htailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (TM.skipTM (n := n + 1))
    (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
      (TM.binarySuccTM tapes.lifted.data.rhs))
    hskipReach rfl htailReach'
  let finalCfg := TM.phase2Wrap (TM.skipTM (n := n + 1))
    (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
      (TM.binarySuccTM tapes.lifted.data.rhs)) tailDone
  have hrhsInputSuffix : rhsDone.input.HasBinarySuffix input := by
    rw [hrhsInput, hlhsInput]
    simpa [skipped, parkedInput] using! Tape.init_move_right_hasBinarySuffix input
  have hrhsOutputBlank : rhsDone.output = TM.resetBinaryBlank := by
    exact hrhsOutput.trans (hlhsOutput.trans (by rfl))
  have hrhsWorkParked : ∀ i, TM.Parked (rhsDone.work i) := by
    intro i
    by_cases hi : i = tapes.lifted.data.rhs
    · subst i
      exact parked_of_binaryNat hrhsValue
    · rw [hrhsFrame i hi]
      exact hlhsWorkParked i
  have hrhsRemaining : tapes.lifted.data.update.remaining ≠
      tapes.lifted.data.rhs := tapes.lifted.data.ne (by decide)
  have hlhsRemaining : tapes.lifted.data.update.remaining ≠
      tapes.liftedLhs := tapes.lifted.data.ne (by decide)
  refine ⟨finalCfg, 1 + 1 + (lhsTime + 1 + rhsTime), ?_, hreach,
    ?_, ?_⟩
  · omega
  · change (initialSetupTM tapes).halted finalCfg
    unfold initialSetupTM
    exact (TM.phase2Wrap_halted_iff (TM.skipTM (n := n + 1))
    (TM.seqTM (TM.binarySuccTM tapes.liftedLhs)
      (TM.binarySuccTM tapes.lifted.data.rhs)) tailDone).mpr htailHalt
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change rhsDone.input.HasBinarySuffix input
      exact hrhsInputSuffix
    · change rhsDone.input =
          (Tape.init (input.map Γ.ofBool)).move Dir3.right
      rw [hrhsInput, hlhsInput]
    · refine
        { address := ?_
          value := ?_
          count := ?_
          buffer := ?_
          parked := ?_
          frame := ?_ }
      · change (rhsDone.work tapes.liftedLhs).HasBinaryNat 1
        rw [hrhsFrame _ hlhsRhs]
        simpa using! hlhsValue
      · change (rhsDone.work tapes.lifted.data.rhs).HasBinaryNat 1
        simpa using! hrhsValue
      · change (rhsDone.work
          tapes.lifted.data.update.remaining).HasBinaryNat 0
        rw [hrhsFrame _ hrhsRemaining, hlhsFrame _ hlhsRemaining]
        simpa [skipped, parkedWork] using! hblankNat
      · change (rhsDone.work tapes.buffer).HasBinaryPrefix []
        rw [hrhsFrame _ (tapes.liftedData_ne_buffer 14).symm,
          hlhsFrame _ (tapes.liftedData_ne_buffer 13).symm]
        have hblankString : TM.resetBinaryBlank.HasBinaryString [] :=
          hblankNat.2
        simpa [skipped, parkedWork] using!
          (show TM.resetBinaryBlank.HasBinaryPrefix [] from
            ⟨by simpa using! hblankString.1, hblankString.2⟩)
      · intro i
        change TM.Parked (rhsDone.work i)
        exact hrhsWorkParked i
      · intro i hlhs hrhs hcount hbuffer
        change rhsDone.work i = TM.resetBinaryBlank
        rw [hrhsFrame i hrhs, hlhsFrame i hlhs]
    · change rhsDone.output = TM.resetBinaryBlank
      exact hrhsOutputBlank

/-- Emit the length register into the sparse buffer and increment the runtime
entry count, restoring both encoder sources exactly. -/
theorem initialLengthEmitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (length count : ℕ)
    (entries : Store) (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (out₀ : Tape) (hready : InitialLoopReady tapes length count entries work₀)
    (hinput : TM.Parked inp₀) (houtput : out₀ = TM.resetBinaryBlank) :
    (initialLengthEmitTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InitialLoopReady tapes length (count + 1)
          (entries ++ [(0, length)]) work ∧
        out = out₀)
      (rewindEntryEncodeRestoreTime (0, length) + 1 +
        TM.binarySuccTime count) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hqueryLhs : tapes.lifted.data.update.entry.query ≠
      tapes.liftedLhs := tapes.lifted.data.ne (by decide)
  have hqueryRhs : tapes.lifted.data.update.entry.query ≠
      tapes.lifted.data.rhs := tapes.lifted.data.ne (by decide)
  have hqueryCount : tapes.lifted.data.update.entry.query ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hqueryBuffer : tapes.lifted.data.update.entry.query ≠
      tapes.buffer := tapes.liftedData_ne_buffer 7
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have hqueryZero :
      (work₀ tapes.lifted.data.update.entry.query).HasBinaryNat 0 := by
    rw [hready.frame _ hqueryLhs hqueryRhs hqueryCount hqueryBuffer]
    exact hblankNat
  have haddress :
      (work₀ (Fin.castSucc (initialLengthEntryTapes tapes).address)).HasBinaryNat 0 := by
    exact hqueryZero
  have hvalue :
      (work₀ (Fin.castSucc (initialLengthEntryTapes tapes).value)).HasBinaryNat
        length := by
    exact hready.address
  have hemit :=
    rewindEntryEncodeRestoreTM_retargetOutput_hoareTime_frame
      (initialLengthEntryTapes tapes) (0, length)
      (entries.flatMap Entry.encode) inp₀ work₀ haddress hvalue hinput
      (fun i _ _ => hready.parked (Fin.castSucc i)) hready.buffer
  obtain ⟨emitted, emitTime, hemitTime, hemitReach, hemitHalt,
      hemitInput, hemitFrame, hemitBuffer, hemitOutput⟩ :=
    hemit inp₀ work₀ out₀
      ⟨rfl, rfl, by simpa [TM.resetBinaryBlank] using! houtput⟩
  have hemitOutput' : emitted.output = out₀ := by
    exact hemitOutput.trans (by simpa [TM.resetBinaryBlank] using! houtput.symm)
  have hemitInputParked : TM.Parked emitted.input := by
    rw [hemitInput]
    exact hinput
  have hemitOutputParked : TM.Parked emitted.output := by
    rw [hemitOutput']
    rw [houtput]
    exact parked_of_binaryNat hblankNat
  have hemitWorkParked : ∀ i, TM.Parked (emitted.work i) := by
    intro i
    by_cases hi : i = tapes.buffer
    · subst i
      exact parked_of_binaryPrefix hemitBuffer
    · rw [hemitFrame i hi]
      exact hready.parked i
  have hcountBuffer : tapes.lifted.data.update.remaining ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 9
  have hemitCount :
      (emitted.work tapes.lifted.data.update.remaining).HasBinaryNat count := by
    rw [hemitFrame _ hcountBuffer]
    exact hready.count
  have hcountRun := TM.binarySuccTM_hoareTime_frame
    tapes.lifted.data.update.remaining count emitted.input emitted.work
    emitted.output hemitCount hemitInputParked.read_ne_start
    (fun i _ => (hemitWorkParked i).read_ne_start)
    hemitOutputParked.read_ne_start
  obtain ⟨counted, countTime, hcountTime, hcountReach, hcountHalt,
      hcountInput, hcountFrame, hcountValue, hcountOutput⟩ :=
    hcountRun emitted.input emitted.work emitted.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hemitInputParked.read_ne_start
      (fun i => (hemitWorkParked i).read_ne_start)
      hemitOutputParked.read_ne_start
  have hcountReach' :
      (TM.binarySuccTM tapes.lifted.data.update.remaining).reachesIn
        countTime
        { state := (TM.binarySuccTM
            tapes.lifted.data.update.remaining).qstart
          input := TM.transitionInput emitted.input
          work := fun i => TM.transitionTape (emitted.work i)
          output := TM.transitionTape emitted.output }
        counted := by
    simpa only [hemitInputTransition, hemitWorkTransition,
      hemitOutputTransition] using! hcountReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (rewindEntryEncodeRestoreTM
      (initialLengthEntryTapes tapes)).retargetOutput
    (TM.binarySuccTM tapes.lifted.data.update.remaining)
    hemitReach hemitHalt hcountReach'
  let finalCfg := TM.phase2Wrap
    (rewindEntryEncodeRestoreTM
      (initialLengthEntryTapes tapes)).retargetOutput
    (TM.binarySuccTM tapes.lifted.data.update.remaining) counted
  have hcountWorkParked : ∀ i, TM.Parked (counted.work i) := by
    intro i
    by_cases hi : i = tapes.lifted.data.update.remaining
    · subst i
      exact parked_of_binaryNat hcountValue
    · rw [hcountFrame i hi]
      exact hemitWorkParked i
  have hlhsCount : tapes.liftedLhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hrhsCount : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hlhsBuffer : tapes.liftedLhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 13
  have hrhsBuffer : tapes.lifted.data.rhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 14
  refine ⟨finalCfg, emitTime + 1 + countTime, by omega, hreach, ?_, ?_⟩
  · change (initialLengthEmitTM tapes).halted finalCfg
    unfold initialLengthEmitTM
    exact (TM.phase2Wrap_halted_iff (rewindEntryEncodeRestoreTM
      (initialLengthEntryTapes tapes)).retargetOutput
    (TM.binarySuccTM tapes.lifted.data.update.remaining) counted).mpr hcountHalt
  · refine ⟨?_, ?_, ?_⟩
    · change counted.input = inp₀
      exact hcountInput.trans hemitInput
    · refine
        { address := ?_
          value := ?_
          count := hcountValue
          buffer := ?_
          parked := ?_
          frame := ?_ }
      · change (counted.work tapes.liftedLhs).HasBinaryNat length
        rw [hcountFrame _ hlhsCount, hemitFrame _ hlhsBuffer]
        exact hready.address
      · change (counted.work tapes.lifted.data.rhs).HasBinaryNat 1
        rw [hcountFrame _ hrhsCount, hemitFrame _ hrhsBuffer]
        exact hready.value
      · change (counted.work tapes.buffer).HasBinaryPrefix
          ((entries ++ [(0, length)]).flatMap Entry.encode)
        rw [hcountFrame _ hcountBuffer.symm]
        simpa [List.flatMap_append] using! hemitBuffer
      · intro i
        change TM.Parked (counted.work i)
        exact hcountWorkParked i
      · intro i hlhs hrhs hcount hbuffer
        change counted.work i = TM.resetBinaryBlank
        rw [hcountFrame i hcount, hemitFrame i hbuffer]
        exact hready.frame i hlhs hrhs hcount hbuffer
    · change counted.output = out₀
      exact hcountOutput.trans hemitOutput'

/-- Optional length emission skips zero and appends exactly one nonzero
`R₀` entry otherwise. -/
theorem initialLengthTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (length count : ℕ)
    (entries : Store) (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (out₀ : Tape) (hready : InitialLoopReady tapes length count entries work₀)
    (hinput : TM.Parked inp₀) (houtput : out₀ = TM.resetBinaryBlank) :
    (initialLengthTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InitialLoopReady tapes length
          (count + if length = 0 then 0 else 1)
          (entries ++ if length = 0 then [] else [(0, length)]) work ∧
        out = out₀)
      (initialLengthTime length count) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  by_cases hlength : length = 0
  · subst length
    have hblank : (work₀ tapes.liftedLhs).read = Γ.blank :=
      hready.address.read_eq_blank_iff.mpr rfl
    have hskip := TM.skipTM_hoareTime_frame inp₀ work₀ out₀ hinput
      hready.parked (by
        rw [houtput]
        have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
          simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
        exact parked_of_binaryNat hblankNat)
    obtain ⟨skipDone, skipTime, hskipTime, hskipReach, hskipHalt,
        hskipInput, hskipWork, hskipOutput⟩ :=
      hskip inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
    obtain ⟨done, hreach, hhalt, hdoneInput, hdoneWork, hdoneOutput⟩ :=
      TM.branchWorkBlankTM_reachesIn_blank_frame tapes.liftedLhs
        (TM.skipTM (n := n + 1)) (initialLengthEmitTM tapes)
        inp₀ work₀ out₀ hblank hinput.read_ne_start
        (fun i => (hready.parked i).read_ne_start)
        (by
          rw [houtput]
          have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
            simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
          exact (parked_of_binaryNat hblankNat).read_ne_start)
        hskipReach hskipHalt
    refine ⟨done, skipTime + 1, ?_, hreach, hhalt, ?_⟩
    · simp [initialLengthTime]
      omega
    · refine ⟨?_, ?_, ?_⟩
      · exact hdoneInput.trans hskipInput
      · simpa [hdoneWork, hskipWork] using! hready
      · exact hdoneOutput.trans (hskipOutput.trans rfl)
  · have hnonblank : (work₀ tapes.liftedLhs).read ≠ Γ.blank := by
      intro hblank
      exact hlength (hready.address.read_eq_blank_iff.mp hblank)
    have hemit := initialLengthEmitTM_hoareTime_internal tapes length count
      entries inp₀ work₀ out₀ hready hinput houtput
    obtain ⟨emitDone, emitTime, hemitTime, hemitReach, hemitHalt,
        hemitInput, hemitReady, hemitOutput⟩ :=
      hemit inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
    obtain ⟨done, hreach, hhalt, hdoneInput, hdoneWork, hdoneOutput⟩ :=
      TM.branchWorkBlankTM_reachesIn_nonblank_frame tapes.liftedLhs
        (TM.skipTM (n := n + 1)) (initialLengthEmitTM tapes)
        inp₀ work₀ out₀ hnonblank hinput.read_ne_start
        (fun i => (hready.parked i).read_ne_start)
        (by
          rw [houtput]
          have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
            simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
          exact (parked_of_binaryNat hblankNat).read_ne_start)
        hemitReach hemitHalt
    refine ⟨done, emitTime + 1, ?_, hreach, hhalt, ?_⟩
    · simp [initialLengthTime, hlength]
      omega
    · refine ⟨?_, ?_, ?_⟩
      · exact hdoneInput.trans hemitInput
      · simpa [hlength, hdoneWork] using! hemitReady
      · exact hdoneOutput.trans hemitOutput

/-- Restore the post-loop address and install the optional length entry. -/
theorem initialLengthInstallTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (length count : ℕ)
    (entries : Store) (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape)
    (out₀ : Tape)
    (hready : InitialLoopReady tapes (length + 1) count entries work₀)
    (hinput : TM.Parked inp₀) (houtput : out₀ = TM.resetBinaryBlank) :
    (initialLengthInstallTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InitialLoopReady tapes length
          (count + if length = 0 then 0 else 1)
          (entries ++ if length = 0 then [] else [(0, length)]) work ∧
        out = out₀)
      (TM.binaryPredTime length + 1 + initialLengthTime length count) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hpred := TM.binaryPredTM_hoareTime_frame tapes.liftedLhs length
    inp₀ work₀ out₀ hready.address hinput.read_ne_start
    (fun i _ => (hready.parked i).read_ne_start)
    (by
      rw [houtput]
      have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
        simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
      exact (parked_of_binaryNat hblankNat).read_ne_start)
  obtain ⟨predDone, predTime, hpredTime, hpredReach, hpredHalt,
      hpredInput, hpredFrame, hpredValue, hpredOutput⟩ :=
    hpred inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have hpredInputParked : TM.Parked predDone.input := by
    rw [hpredInput]
    exact hinput
  have hpredOutputBlank : predDone.output = TM.resetBinaryBlank :=
    hpredOutput.trans houtput
  have hpredOutputParked : TM.Parked predDone.output := by
    rw [hpredOutputBlank]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hpredWorkParked : ∀ i, TM.Parked (predDone.work i) := by
    intro i
    by_cases hi : i = tapes.liftedLhs
    · subst i
      exact parked_of_binaryNat hpredValue
    · rw [hpredFrame i hi]
      exact hready.parked i
  have hrhsLhs : tapes.lifted.data.rhs ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  have hcountLhs : tapes.lifted.data.update.remaining ≠
      tapes.liftedLhs := tapes.lifted.data.ne (by decide)
  have hbufferLhs : tapes.buffer ≠ tapes.liftedLhs :=
    (tapes.liftedData_ne_buffer 13).symm
  have hpredReady : InitialLoopReady tapes length count entries predDone.work :=
    { address := hpredValue
      value := by
        rw [hpredFrame _ hrhsLhs]
        exact hready.value
      count := by
        rw [hpredFrame _ hcountLhs]
        exact hready.count
      buffer := by
        rw [hpredFrame _ hbufferLhs]
        exact hready.buffer
      parked := hpredWorkParked
      frame := by
        intro i hlhs hrhs hcount hbuffer
        rw [hpredFrame i hlhs]
        exact hready.frame i hlhs hrhs hcount hbuffer }
  have hlength := initialLengthTM_hoareTime_internal tapes length count entries
    predDone.input predDone.work predDone.output hpredReady hpredInputParked
    hpredOutputBlank
  obtain ⟨lengthDone, lengthTime, hlengthTime, hlengthReach,
      hlengthHalt, hlengthInput, hlengthReady, hlengthOutput⟩ :=
    hlength predDone.input predDone.work predDone.output ⟨rfl, rfl, rfl⟩
  obtain ⟨hpredInputTransition, hpredWorkTransition,
      hpredOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hpredInputParked.read_ne_start
      (fun i => (hpredWorkParked i).read_ne_start)
      hpredOutputParked.read_ne_start
  have hlengthReach' : (initialLengthTM tapes).reachesIn lengthTime
      { state := (initialLengthTM tapes).qstart
        input := TM.transitionInput predDone.input
        work := fun i => TM.transitionTape (predDone.work i)
        output := TM.transitionTape predDone.output }
      lengthDone := by
    simpa only [hpredInputTransition, hpredWorkTransition,
      hpredOutputTransition] using! hlengthReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (TM.binaryPredTM tapes.liftedLhs) (initialLengthTM tapes)
    hpredReach hpredHalt hlengthReach'
  let finalCfg := TM.phase2Wrap (TM.binaryPredTM tapes.liftedLhs)
    (initialLengthTM tapes) lengthDone
  refine ⟨finalCfg, predTime + 1 + lengthTime, by omega, hreach, ?_, ?_⟩
  · change (initialLengthInstallTM tapes).halted finalCfg
    unfold initialLengthInstallTM
    exact (TM.phase2Wrap_halted_iff (TM.binaryPredTM tapes.liftedLhs)
    (initialLengthTM tapes) lengthDone).mpr hlengthHalt
  · refine ⟨?_, ?_, ?_⟩
    · change lengthDone.input = inp₀
      exact hlengthInput.trans hpredInput
    · change InitialLoopReady tapes length
        (count + if length = 0 then 0 else 1)
        (entries ++ if length = 0 then [] else [(0, length)])
        lengthDone.work
      exact hlengthReady
    · change lengthDone.output = out₀
      exact hlengthOutput.trans hpredOutput

/-- Install the completed sparse buffer into the exact clean program-loop
snapshot image. -/
theorem initialAbiInstallTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (store : Store) (length : ℕ)
    (inp₀ : Tape) (work₀ : Fin (n + 1) → Tape) (out₀ : Tape)
    (hready : InitialLoopReady tapes length store.length store work₀)
    (hbufferStart : (work₀ tapes.buffer).cells 0 = Γ.start)
    (hinput : TM.Parked inp₀) (houtput : out₀ = TM.resetBinaryBlank) :
    (initialAbiInstallTM tapes).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = programSnapshotWork tapes { pc := 0, store := store } ∧
        out = out₀)
      (initialAbiInstallTime tapes store length) := by
  let storeBits := store.flatMap Entry.encode
  let W₁ := initialAbiCountWork tapes work₀ store.length
  let W₂ := initialAbiBufferWork tapes W₁ store
  let W₃ := initialAbiCopiedWork tapes W₂ store
  let W₄ := initialAbiSourceWork tapes W₃ store
  let W₅ := initialAbiBufferResetWork tapes W₄
  let W₆ := initialAbiFinalWork tapes W₅
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
  have houtputParked : TM.Parked out₀ := by
    rw [houtput]
    exact parked_of_binaryNat hblankNat
  have hremainingResult : tapes.lifted.data.update.remaining ≠
      tapes.lifted.data.update.resultCount :=
    tapes.lifted.data.ne (by decide)
  have hremainingFound : tapes.lifted.data.update.remaining ≠
      tapes.lifted.data.update.found := tapes.lifted.data.ne (by decide)
  have hresultFound : tapes.lifted.data.update.resultCount ≠
      tapes.lifted.data.update.found := tapes.lifted.data.ne (by decide)
  have hresultLhs : tapes.lifted.data.update.resultCount ≠
      tapes.liftedLhs := tapes.lifted.data.ne (by decide)
  have hresultRhs : tapes.lifted.data.update.resultCount ≠
      tapes.lifted.data.rhs := tapes.lifted.data.ne (by decide)
  have hresultBuffer : tapes.lifted.data.update.resultCount ≠
      tapes.buffer := tapes.liftedData_ne_buffer 12
  have hfoundLhs : tapes.lifted.data.update.found ≠
      tapes.liftedLhs := tapes.lifted.data.ne (by decide)
  have hfoundRhs : tapes.lifted.data.update.found ≠
      tapes.lifted.data.rhs := tapes.lifted.data.ne (by decide)
  have hfoundRemaining : tapes.lifted.data.update.found ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hfoundBuffer : tapes.lifted.data.update.found ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 11
  have hsourceLhs : tapes.liftedSource ≠ tapes.liftedLhs :=
    tapes.lifted.data.ne (by decide)
  have hsourceRhs : tapes.liftedSource ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hsourceRemaining : tapes.liftedSource ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hsourceResult : tapes.liftedSource ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hsourceBuffer : tapes.liftedSource ≠ tapes.buffer :=
    tapes.liftedSource_ne_buffer
  have hlhsRhs : tapes.liftedLhs ≠ tapes.lifted.data.rhs :=
    tapes.lifted.data.ne (by decide)
  have hlhsRemaining : tapes.liftedLhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hlhsResult : tapes.liftedLhs ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hlhsSource := hsourceLhs.symm
  have hlhsBuffer : tapes.liftedLhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 13
  have hrhsRemaining : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.remaining := tapes.lifted.data.ne (by decide)
  have hrhsResult : tapes.lifted.data.rhs ≠
      tapes.lifted.data.update.resultCount := tapes.lifted.data.ne (by decide)
  have hrhsSource := hsourceRhs.symm
  have hrhsBuffer : tapes.lifted.data.rhs ≠ tapes.buffer :=
    tapes.liftedData_ne_buffer 14
  have hremainingBuffer : tapes.lifted.data.update.remaining ≠
      tapes.buffer := tapes.liftedData_ne_buffer 9
  have hcountEq : work₀ tapes.lifted.data.update.remaining =
      programBinaryTape store.length.bits := by
    simpa only [programBinaryTape] using! hready.count.eq_init_move_right
  have hbufferEq : work₀ tapes.buffer = programBinaryPrefixTape storeBits := by
    exact eq_programBinaryPrefixTape_of_hasBinaryPrefix hready.buffer
      hbufferStart
  have hresultZero :
      (work₀ tapes.lifted.data.update.resultCount).HasBinaryNat 0 := by
    rw [hready.frame _ hresultLhs hresultRhs hremainingResult.symm
      hresultBuffer]
    exact hblankNat
  have hfoundZero :
      (work₀ tapes.lifted.data.update.found).HasBinaryNat 0 := by
    rw [hready.frame _ hfoundLhs hfoundRhs hfoundRemaining hfoundBuffer]
    exact hblankNat
  have hcopy := TM.binaryCopyIntoTM_hoareTime_frame
    tapes.lifted.data.update.remaining
    tapes.lifted.data.update.resultCount
    tapes.lifted.data.update.found hremainingResult hremainingFound
    hresultFound store.length 0 inp₀ work₀ out₀ hready.count
    hresultZero hfoundZero hinput
    (fun i _ _ _ => hready.parked i) houtputParked
  have hcopy' :
      (TM.binaryCopyIntoTM
        tapes.lifted.data.update.remaining
        tapes.lifted.data.update.resultCount
        tapes.lifted.data.update.found).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀)
        (TM.binaryCopyTime store.length 0) := by
    simpa only [W₁, initialAbiCountWork] using! hcopy
  have hW₁Parked : ∀ i, TM.Parked (W₁ i) := by
    exact parked_update hready.parked (binaryTape_parked store.length.bits)
  have hW₁Buffer : W₁ tapes.buffer = programBinaryPrefixTape storeBits := by
    simp [W₁, initialAbiCountWork, hresultBuffer.symm, hbufferEq]
  have hrewindBuffer := rewindPrefixWorkTM_exact_hoareTime tapes.buffer
    storeBits inp₀ W₁ out₀ hW₁Buffer hinput hW₁Parked houtputParked
  have hrewindBuffer' : (TM.rewindWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀)
      (storeBits.length + 1 + 2) := by
    simpa only [W₂, initialAbiBufferWork] using! hrewindBuffer
  have hW₂Parked : ∀ i, TM.Parked (W₂ i) := by
    exact parked_update hW₁Parked (binaryTape_parked storeBits)
  have hW₂Buffer : W₂ tapes.buffer = programBinaryTape storeBits := by
    simp [W₂, initialAbiBufferWork, storeBits]
  have hsourceBlank : work₀ tapes.liftedSource = TM.resetBinaryBlank := by
    exact hready.frame _ hsourceLhs hsourceRhs hsourceRemaining hsourceBuffer
  have hW₂Source : W₂ tapes.liftedSource = TM.resetBinaryBlank := by
    simp [W₂, W₁, initialAbiBufferWork, initialAbiCountWork,
      hsourceBuffer, hsourceResult, hsourceBlank]
  have hcopyStore := copyWorkToWorkTM_exact_hoareTime tapes.buffer
    tapes.liftedSource hsourceBuffer.symm storeBits inp₀ W₂ out₀
    hW₂Buffer hW₂Source hinput hW₂Parked houtputParked
  have hcopyStore' :
      (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = W₃ ∧ out = out₀)
        (storeBits.length + 1) := by
    simpa only [W₃, initialAbiCopiedWork] using! hcopyStore
  have hprefixParked : TM.Parked (programBinaryPrefixTape storeBits) :=
    programBinaryPrefixTape_parked storeBits
  have hW₃Parked : ∀ i, TM.Parked (W₃ i) := by
    exact parked_update (parked_update hW₂Parked hprefixParked)
      hprefixParked
  have hW₃Source :
      W₃ tapes.liftedSource = programBinaryPrefixTape storeBits := by
    simp [W₃, initialAbiCopiedWork, storeBits]
  have hrewindSource := rewindPrefixWorkTM_exact_hoareTime
    tapes.liftedSource storeBits inp₀ W₃ out₀ hW₃Source
    hinput hW₃Parked houtputParked
  have hrewindSource' : (TM.rewindWorkTM tapes.liftedSource).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₃ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₄ ∧ out = out₀)
      (storeBits.length + 1 + 2) := by
    simpa only [W₄, initialAbiSourceWork] using! hrewindSource
  have hW₄Parked : ∀ i, TM.Parked (W₄ i) := by
    exact parked_update hW₃Parked (binaryTape_parked storeBits)
  have hW₄Buffer :
      W₄ tapes.buffer = programBinaryPrefixTape storeBits := by
    simp [W₄, W₃, initialAbiSourceWork, initialAbiCopiedWork,
      hsourceBuffer.symm, storeBits]
  have hresetBuffer := TM.resetBinaryWorkTM_hoareTime_frame tapes.buffer
    storeBits (storeBits.length + 1) inp₀ W₄ out₀
    (by rw [hW₄Buffer]; exact
      (programBinaryPrefixTape_hasBinaryPrefix storeBits).2)
    (by rw [hW₄Buffer]; simp [programBinaryPrefixTape])
    (by rw [hW₄Buffer]; simp [programBinaryPrefixTape])
    hinput (fun i _ => hW₄Parked i) houtputParked
  have hresetBuffer' : (TM.resetBinaryWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₄ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₅ ∧ out = out₀)
      (TM.resetBinaryWorkTime (storeBits.length + 1) storeBits.length) := by
    simpa only [W₅, initialAbiBufferResetWork, TM.resetBinaryBlank]
      using! hresetBuffer
  have hW₅Parked : ∀ i, TM.Parked (W₅ i) := by
    exact parked_update hW₄Parked (parked_of_binaryNat hblankNat)
  have hW₅Lhs : W₅ tapes.liftedLhs = work₀ tapes.liftedLhs := by
    simp [W₅, W₄, W₃, W₂, W₁, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, hlhsBuffer, hlhsSource, hlhsResult]
  have hW₅Rhs :
      W₅ tapes.lifted.data.rhs = work₀ tapes.lifted.data.rhs := by
    simp [W₅, W₄, W₃, W₂, W₁, initialAbiBufferResetWork,
      initialAbiSourceWork, initialAbiCopiedWork, initialAbiBufferWork,
      initialAbiCountWork, hrhsBuffer, hrhsSource, hrhsResult]
  have htargetsNodup : (initialCleanupTargets tapes).Nodup := by
    simp [initialCleanupTargets, hlhsRhs]
  have htargetsContent : ∀ i, i ∈ initialCleanupTargets tapes →
      (W₅ i).HasBinaryContent (initialCleanupBits tapes length i) := by
    intro i hi
    simp [initialCleanupTargets] at hi
    rcases hi with rfl | rfl
    · rw [hW₅Lhs]
      simpa [initialCleanupBits] using! hready.address.2.hasBinaryContent
    · rw [hW₅Rhs]
      simpa [initialCleanupBits, hlhsRhs.symm] using!
        hready.value.2.hasBinaryContent
  have htargetsStart : ∀ i, i ∈ initialCleanupTargets tapes →
      (W₅ i).cells 0 = Γ.start := by
    intro i hi
    simp [initialCleanupTargets] at hi
    rcases hi with rfl | rfl
    · rw [hW₅Lhs]
      exact hready.address.1
    · rw [hW₅Rhs]
      exact hready.value.1
  have htargetsHead : ∀ i, i ∈ initialCleanupTargets tapes →
      (W₅ i).head ≤ 1 := by
    intro i hi
    simp [initialCleanupTargets] at hi
    rcases hi with rfl | rfl
    · rw [hW₅Lhs, hready.address.2.1]
    · rw [hW₅Rhs, hready.value.2.1]
  have hresetMany := TM.resetBinaryWorkManyTM_hoareTime_frame
    (initialCleanupTargets tapes) (initialCleanupBits tapes length)
    (fun _ => 1) inp₀ W₅ out₀ htargetsNodup htargetsContent
    htargetsStart htargetsHead hinput hW₅Parked houtputParked
  have hresetMany' :
      (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes)).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = W₅ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = W₆ ∧ out = out₀)
        (TM.resetBinaryWorkManyTime (initialCleanupBits tapes length)
          (fun _ => 1) (initialCleanupTargets tapes)) := by
    simpa only [W₆, initialAbiFinalWork] using! hresetMany
  have htail₅ := TM.seqTM_hoareTime
    (TM.resetBinaryWorkTM tapes.buffer)
    (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes))
    hresetBuffer'
    (exact_phaseTransition_of_parked inp₀ W₅ out₀ hinput
      hW₅Parked houtputParked)
    hresetMany'
  have htail₄ := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.liftedSource)
    (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
      (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes)))
    hrewindSource'
    (exact_phaseTransition_of_parked inp₀ W₄ out₀ hinput
      hW₄Parked houtputParked)
    htail₅
  have htail₃ := TM.seqTM_hoareTime
    (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
    (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
      (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
        (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes))))
    hcopyStore'
    (exact_phaseTransition_of_parked inp₀ W₃ out₀ hinput
      hW₃Parked houtputParked)
    htail₄
  have htail₂ := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.buffer)
    (TM.seqTM (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
      (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
        (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
          (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes)))))
    hrewindBuffer'
    (exact_phaseTransition_of_parked inp₀ W₂ out₀ hinput
      hW₂Parked houtputParked)
    htail₃
  have hfull := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM
      tapes.lifted.data.update.remaining
      tapes.lifted.data.update.resultCount
      tapes.lifted.data.update.found)
    (TM.seqTM (TM.rewindWorkTM tapes.buffer)
      (TM.seqTM (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
        (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
          (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
            (TM.resetBinaryWorkManyTM (initialCleanupTargets tapes))))))
    hcopy'
    (exact_phaseTransition_of_parked inp₀ W₁ out₀ hinput
      hW₁Parked houtputParked)
    htail₂
  have hfinal : W₆ =
      programSnapshotWork tapes { pc := 0, store := store } := by
    exact initialAbiFinalWork_eq_programSnapshotWork tapes store length
      work₀ hready
  apply hfull.consequence
  · exact fun _ _ _ h => h
  · rintro inp work out ⟨hinp, hwork, hout⟩
    exact ⟨hinp, hwork.trans hfinal, hout⟩
  · simp only [initialAbiInstallTime, storeBits]
    omega

private theorem inputBitStoreFrom_address_lower
    {start : ℕ} {input : List Bool} {entry : Entry}
    (hentry : entry ∈ inputBitStoreFrom start input) :
    start ≤ entry.1 := by
  induction input generalizing start with
  | nil => simp [inputBitStoreFrom] at hentry
  | cons bit rest ih =>
      by_cases hbit : bit
      · simp only [inputBitStoreFrom, hbit, if_true, List.singleton_append,
          List.mem_cons] at hentry
        rcases hentry with rfl | hentry
        · simp
        · exact le_trans (by omega) (ih hentry)
      · simp only [inputBitStoreFrom, hbit] at hentry
        exact le_trans (by omega) (ih hentry)

private theorem inputBitStoreFrom_addressesNodup
    (start : ℕ) (input : List Bool) :
    AddressesNodup (inputBitStoreFrom start input) := by
  induction input generalizing start with
  | nil => simp [inputBitStoreFrom, AddressesNodup]
  | cons bit rest ih =>
      by_cases hbit : bit
      · simp only [inputBitStoreFrom, hbit, if_true, List.singleton_append]
        change (start :: (inputBitStoreFrom (start + 1) rest).map Prod.fst).Nodup
        rw [List.nodup_cons]
        refine ⟨?_, ih (start + 1)⟩
        intro hmem
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
        have hlower := inputBitStoreFrom_address_lower hentry
        change entry.1 = start at heq
        omega
      · simpa [inputBitStoreFrom, hbit] using! ih (start + 1)

private theorem inputBitStoreFrom_valuesNonzero
    (start : ℕ) (input : List Bool) :
    ValuesNonzero (inputBitStoreFrom start input) := by
  induction input generalizing start with
  | nil => simp [inputBitStoreFrom, ValuesNonzero]
  | cons bit rest ih =>
      by_cases hbit : bit
      · simp only [inputBitStoreFrom, hbit, if_true, List.singleton_append]
        intro entry hentry
        simp only [List.mem_cons] at hentry
        rcases hentry with rfl | hentry
        · exact Nat.one_ne_zero
        · exact ih (start + 1) entry hentry
      · simpa [inputBitStoreFrom, hbit] using! ih (start + 1)

private theorem zero_not_mem_inputBitStoreFrom_addresses
    (input : List Bool) :
    0 ∉ (inputBitStoreFrom 1 input).map Prod.fst := by
  intro hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  have hlower := inputBitStoreFrom_address_lower hentry
  change entry.1 = 0 at heq
  omega

private theorem write_eq_append_of_address_not_mem
    (store : Store) (address value : ℕ)
    (haddress : address ∉ store.map Prod.fst) :
    RegisterStore.write store address value =
      store ++ if value = 0 then [] else [(address, value)] := by
  induction store with
  | nil => simp [RegisterStore.write]
  | cons entry rest ih =>
      have hhead : address ≠ entry.1 := by
        intro heq
        apply haddress
        simp [heq]
      have hrest : address ∉ rest.map Prod.fst := by
        intro hmem
        exact haddress (by simp [hmem])
      simp [RegisterStore.write, hhead, ih hrest]

theorem programInitialStore_eq_append_internal (input : List Bool) :
    programInitialStore input =
      inputBitStoreFrom 1 input ++
        if input.length = 0 then [] else [(0, input.length)] := by
  unfold programInitialStore
  exact write_eq_append_of_address_not_mem _ _ _
    (zero_not_mem_inputBitStoreFrom_addresses input)

private theorem inputBitStoreFrom_length (start : ℕ) (input : List Bool) :
    (inputBitStoreFrom start input).length = inputTrueCount input := by
  induction input generalizing start with
  | nil => simp [inputBitStoreFrom, inputTrueCount]
  | cons bit rest ih =>
      cases bit
      · simp [inputBitStoreFrom, inputTrueCount, ih]
      · simp [inputBitStoreFrom, inputTrueCount, ih]
        omega

theorem programInitialStore_length_internal (input : List Bool) :
    (programInitialStore input).length =
      inputTrueCount input + if input.length = 0 then 0 else 1 := by
  rw [programInitialStore_eq_append_internal, List.length_append,
    inputBitStoreFrom_length]
  split <;> simp_all

theorem programInitialStore_canonical_internal (input : List Bool) :
    Canonical (programInitialStore input) := by
  apply RegisterStore.write_canonical
  exact ⟨inputBitStoreFrom_addressesNodup 1 input,
    inputBitStoreFrom_valuesNonzero 1 input⟩

private theorem read_inputBitStoreFrom (start target : ℕ)
    (input : List Bool) :
    read (inputBitStoreFrom start input) target =
      if start ≤ target then
        match input[target - start]? with
        | some bit => if bit then 1 else 0
        | none => 0
      else 0 := by
  induction input generalizing start target with
  | nil => simp [inputBitStoreFrom, read]
  | cons bit rest ih =>
      cases bit
      · simp only [inputBitStoreFrom, Bool.false_eq_true, ite_false,
          List.nil_append]
        by_cases htarget : target = start
        · subst target
          rw [ih]
          simp
        · by_cases hlt : target < start
          · rw [ih]
            simp only [ite_eq_right (by omega : ¬start + 1 ≤ target),
              ite_eq_right (by omega : ¬start ≤ target)]
          · have hge : start + 1 ≤ target := by omega
            have hsub : target - start = (target - (start + 1)) + 1 := by
              omega
            rw [ih, ite_eq_left hge, ite_eq_left (by omega : start ≤ target)]
            simp [hsub]
      · simp only [inputBitStoreFrom, if_true, List.singleton_append]
        by_cases htarget : target = start
        · subst target
          simp [read]
        · by_cases hlt : target < start
          · rw [read, ite_eq_right htarget, ih]
            simp only [ite_eq_right (by omega : ¬start + 1 ≤ target),
              ite_eq_right (by omega : ¬start ≤ target)]
          · have hge : start + 1 ≤ target := by omega
            have hsub : target - start = (target - (start + 1)) + 1 := by
              omega
            rw [read, ite_eq_right htarget, ih, ite_eq_left hge,
              ite_eq_left (by omega : start ≤ target)]
            simp [hsub]

private theorem read_inputBitStoreFrom_zero (input : List Bool) :
    read (inputBitStoreFrom 1 input) 0 = 0 := by
  simp [read_inputBitStoreFrom]

private theorem read_programInitialStore (input : List Bool) (target : ℕ) :
    read (programInitialStore input) target = initRegs input target := by
  rw [programInitialStore, RegisterStore.read_write]
  by_cases htarget : target = 0
  · subst target
    simp [initRegs]
  · have hone : 1 ≤ target := Nat.one_le_iff_ne_zero.mpr htarget
    simp [Function.update, htarget, read_inputBitStoreFrom, hone, initRegs]
    rfl
  exact inputBitStoreFrom_addressesNodup 1 input

theorem programInitialSnapshot_represents_internal (input : List Bool) :
    (programInitialSnapshot input).Represents (RAM.initCfg input) := by
  refine ⟨programInitialStore_canonical_internal input, ?_⟩
  apply RAM.Cfg.ext
  · rfl
  · funext target
    exact read_programInitialStore input target

/-- Complete public-input initialization reaches the exact sparse snapshot
image consumed by the reusable program loop. -/
theorem programInitTM_hoareTime_internal
    (tapes : ControlInstructionTapes n) (input : List Bool) :
    (programInitTM tapes).HoareTime
      (fun inp work out =>
        inp = Tape.init (input.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp.HasBinarySuffix [] ∧
        work = programSnapshotWork tapes (programInitialSnapshot input) ∧
        out = TM.resetBinaryBlank)
      (programInitTime tapes input) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hsetup := initialSetupTM_hoareTime_internal tapes input
  obtain ⟨setupDone, setupTime, hsetupTime, hsetupReach, hsetupHalt,
      hsetupInput, _hsetupInputEq, hsetupReady, hsetupOutput⟩ :=
    hsetup _ _ _ ⟨rfl, rfl, rfl⟩
  have hsetupBufferStart :
      (setupDone.work tapes.buffer).cells 0 = Γ.start := by
    apply TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hsetupReach
    simp [Tape.init]
  have hsetupInputParked : TM.Parked setupDone.input :=
    parked_of_binarySuffix hsetupInput
  have hsetupOutputParked : TM.Parked setupDone.output := by
    rw [hsetupOutput]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hloop := initialInputLoopTM_hoareTime_internal tapes input 1 0 []
    setupDone.input setupDone.work setupDone.output hsetupInput hsetupReady
    hsetupOutput
  obtain ⟨loopDone, loopTime, hloopTime, hloopReach, hloopHalt,
      hloopInput, hloopReadyRaw, hloopOutput⟩ :=
    hloop _ _ _ ⟨rfl, rfl, rfl⟩
  have hloopBufferStart :
      (loopDone.work tapes.buffer).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hloopReach
      hsetupBufferStart
  have hloopReady : InitialLoopReady tapes (input.length + 1)
      (inputTrueCount input) (inputBitStoreFrom 1 input) loopDone.work := by
    simpa [Nat.add_comm] using! hloopReadyRaw
  have hloopInputParked : TM.Parked loopDone.input :=
    parked_of_binarySuffix hloopInput
  have hloopOutputBlank : loopDone.output = TM.resetBinaryBlank :=
    hloopOutput.trans hsetupOutput
  have hloopOutputParked : TM.Parked loopDone.output := by
    rw [hloopOutputBlank]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have hlength := initialLengthInstallTM_hoareTime_internal tapes
    input.length (inputTrueCount input) (inputBitStoreFrom 1 input)
    loopDone.input loopDone.work loopDone.output hloopReady hloopInputParked
    hloopOutputBlank
  obtain ⟨lengthDone, lengthTime, hlengthTime, hlengthReach,
      hlengthHalt, hlengthInput, hlengthReadyRaw, hlengthOutput⟩ :=
    hlength _ _ _ ⟨rfl, rfl, rfl⟩
  have hlengthBufferStart :
      (lengthDone.work tapes.buffer).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn tapes.buffer hlengthReach
      hloopBufferStart
  have hlengthReady : InitialLoopReady tapes input.length
      (programInitialStore input).length (programInitialStore input)
      lengthDone.work := by
    rw [programInitialStore_length_internal,
      programInitialStore_eq_append_internal]
    exact hlengthReadyRaw
  have hlengthInputParked : TM.Parked lengthDone.input := by
    rw [hlengthInput]
    exact hloopInputParked
  have hlengthOutputBlank : lengthDone.output = TM.resetBinaryBlank :=
    hlengthOutput.trans hloopOutputBlank
  have hlengthOutputParked : TM.Parked lengthDone.output := by
    rw [hlengthOutputBlank]
    have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
      simpa [TM.resetBinaryBlank] using! Tape.init_move_right_hasBinaryNat 0
    exact parked_of_binaryNat hblankNat
  have habi := initialAbiInstallTM_hoareTime_internal tapes
    (programInitialStore input) input.length lengthDone.input
    lengthDone.work lengthDone.output hlengthReady hlengthBufferStart
    hlengthInputParked hlengthOutputBlank
  obtain ⟨abiDone, abiTime, habiTime, habiReach, habiHalt,
      habiInput, habiWork, habiOutput⟩ :=
    habi _ _ _ ⟨rfl, rfl, rfl⟩
  obtain ⟨hlengthInputTransition, hlengthWorkTransition,
      hlengthOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hlengthInputParked.read_ne_start
      (fun i => (hlengthReady.parked i).read_ne_start)
      hlengthOutputParked.read_ne_start
  have habiReach' : (initialAbiInstallTM tapes).reachesIn abiTime
      { state := (initialAbiInstallTM tapes).qstart
        input := TM.transitionInput lengthDone.input
        work := fun i => TM.transitionTape (lengthDone.work i)
        output := TM.transitionTape lengthDone.output }
      abiDone := by
    simpa only [hlengthInputTransition, hlengthWorkTransition,
      hlengthOutputTransition] using! habiReach
  have hfinalizeReach := TM.seqTM_reachesIn_of_reachesIn
    (initialLengthInstallTM tapes) (initialAbiInstallTM tapes)
    hlengthReach hlengthHalt habiReach'
  let finalizeDone := TM.phase2Wrap (initialLengthInstallTM tapes)
    (initialAbiInstallTM tapes) abiDone
  have hfinalizeHalt : (initialFinalizeTM tapes).halted finalizeDone := by
    unfold initialFinalizeTM
    exact (TM.phase2Wrap_halted_iff (initialLengthInstallTM tapes)
      (initialAbiInstallTM tapes) abiDone).mpr habiHalt
  have hloopInputTransition :
      TM.transitionInput loopDone.input = loopDone.input :=
    TM.transitionInput_eq_self hloopInputParked.read_ne_start
  have hloopWorkTransition :
      (fun i => TM.transitionTape (loopDone.work i)) = loopDone.work :=
    funext fun i => TM.transitionTape_eq_self
      (hloopReady.parked i).read_ne_start
  have hloopOutputTransition :
      TM.transitionTape loopDone.output = loopDone.output :=
    TM.transitionTape_eq_self hloopOutputParked.read_ne_start
  have hfinalizeReach' : (initialFinalizeTM tapes).reachesIn
      (lengthTime + 1 + abiTime)
      { state := (initialFinalizeTM tapes).qstart
        input := TM.transitionInput loopDone.input
        work := fun i => TM.transitionTape (loopDone.work i)
        output := TM.transitionTape loopDone.output }
      finalizeDone := by
    simpa only [hloopInputTransition, hloopWorkTransition,
      hloopOutputTransition] using! hfinalizeReach
  have hloopTailReach := TM.seqTM_reachesIn_of_reachesIn
    (initialInputLoopTM tapes) (initialFinalizeTM tapes)
    hloopReach hloopHalt hfinalizeReach'
  let loopTailDone := TM.phase2Wrap (initialInputLoopTM tapes)
    (initialFinalizeTM tapes) finalizeDone
  have hloopTailHalt :
      (TM.seqTM (initialInputLoopTM tapes)
        (initialFinalizeTM tapes)).halted loopTailDone := by
    exact (TM.phase2Wrap_halted_iff (initialInputLoopTM tapes)
    (initialFinalizeTM tapes) finalizeDone).mpr hfinalizeHalt
  have hsetupInputTransition :
      TM.transitionInput setupDone.input = setupDone.input :=
    TM.transitionInput_eq_self hsetupInputParked.read_ne_start
  have hsetupWorkTransition :
      (fun i => TM.transitionTape (setupDone.work i)) = setupDone.work :=
    funext fun i => TM.transitionTape_eq_self
      (hsetupReady.parked i).read_ne_start
  have hsetupOutputTransition :
      TM.transitionTape setupDone.output = setupDone.output :=
    TM.transitionTape_eq_self hsetupOutputParked.read_ne_start
  have hloopTailReach' :
      (TM.seqTM (initialInputLoopTM tapes)
        (initialFinalizeTM tapes)).reachesIn
        (loopTime + 1 + (lengthTime + 1 + abiTime))
        { state := (TM.seqTM (initialInputLoopTM tapes)
            (initialFinalizeTM tapes)).qstart
          input := TM.transitionInput setupDone.input
          work := fun i => TM.transitionTape (setupDone.work i)
          output := TM.transitionTape setupDone.output }
        loopTailDone := by
    simpa only [hsetupInputTransition, hsetupWorkTransition,
      hsetupOutputTransition] using! hloopTailReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (initialSetupTM tapes)
    (TM.seqTM (initialInputLoopTM tapes) (initialFinalizeTM tapes))
    hsetupReach hsetupHalt hloopTailReach'
  let finalCfg := TM.phase2Wrap (initialSetupTM tapes)
    (TM.seqTM (initialInputLoopTM tapes) (initialFinalizeTM tapes))
    loopTailDone
  refine ⟨finalCfg,
    setupTime + 1 + (loopTime + 1 + (lengthTime + 1 + abiTime)),
    ?_, hreach, ?_, ?_⟩
  · unfold programInitTime
    omega
  · change (programInitTM tapes).halted finalCfg
    unfold programInitTM
    exact (TM.phase2Wrap_halted_iff (initialSetupTM tapes)
    (TM.seqTM (initialInputLoopTM tapes) (initialFinalizeTM tapes))
    loopTailDone).mpr hloopTailHalt
  · refine ⟨?_, ?_, ?_⟩
    · change abiDone.input.HasBinarySuffix []
      rw [habiInput, hlengthInput]
      exact hloopInput
    · change abiDone.work =
          programSnapshotWork tapes (programInitialSnapshot input)
      exact habiWork
    · change abiDone.output = TM.resetBinaryBlank
      exact habiOutput.trans hlengthOutputBlank

end Machine

end RegisterStore

end RAM

end Complexity
