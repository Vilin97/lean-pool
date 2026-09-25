/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.Sim.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany

/-!
# Fixed-program dispatch -- proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private theorem hasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : TM.Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem hasBinaryPrefix_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t := by
  refine ⟨by rw [h.1]; omega, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  by_cases hi : i < bits.length
  · rw [h.2.1 i hi]
    exact Γ.ofBool_ne_start _
  · rw [h.2.2 i (Nat.le_of_not_gt hi)]
    decide

private theorem instructionCleanupPrefixTape_hasBinaryPrefix
    (bits : List Bool) :
    (instructionCleanupPrefixTape bits).HasBinaryPrefix bits := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    exact Tape.init_ofBool_cells_ge bits i hi

private theorem instructionCleanupPrefixTape_start (bits : List Bool) :
    (instructionCleanupPrefixTape bits).cells 0 = Γ.start := by
  simp [instructionCleanupPrefixTape, Tape.init]

private theorem instructionCleanupPrefixTape_parked (bits : List Bool) :
    TM.Parked (instructionCleanupPrefixTape bits) :=
  hasBinaryPrefix_parked (instructionCleanupPrefixTape_hasBinaryPrefix bits)

private theorem hasBinaryString_parked {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : TM.Parked t := by
  exact ⟨by rw [h.1], Tape.cells_ne_start_of_hasBinaryString h⟩

private theorem blank_parked :
    TM.Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨by simp [Tape.move], ?_⟩
  intro j hj
  simp [Tape.move, Tape.init, show j ≠ 0 by omega]

private theorem phaseTransition_of_parked
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : TM.Parked inp) (hwork : ∀ i, TM.Parked (work i))
    (houtput : TM.Parked out) :
    TM.transitionInput inp = inp ∧
      (fun i => TM.transitionTape (work i)) = work ∧
      TM.transitionTape out = out :=
  TM.phaseTransition_eq_self_of_reads_ne_start hinput.read_ne_start
    (fun i => (hwork i).read_ne_start) houtput.read_ne_start

/-- Reset the dispatch selector and execute halt when the program list is empty. -/
private theorem dispatchEmptyProgramTM_hoareTime
    (tapes : ControlInstructionTapes n)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : DispatchReady tapes store pcValue selector cleanWork work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀)
    (hexecute : ∀ instruction,
      (executeInstructionTM tapes instruction).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = cleanWork ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionExecutionResult tapes instruction pcValue store work ∧
          out = out₀)
        (executeInstructionTime tapes instruction pcValue store)) :
    (dispatchProgramTM tapes ([] : Program)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (selectedInstruction ([] : Program) selector) pcValue store work ∧
        out = out₀)
      (dispatchProgramTime tapes store pcValue ([] : Program) selector) := by
  let blankTape := (Tape.init []).move Dir3.right
  have hselector : (work₀ tapes.liftedLhs).HasBinaryNat selector := by
    rw [hready.2]
    simp only [Function.update_self]
    exact Tape.init_move_right_hasBinaryNat selector
  have hcleanLhs : cleanWork tapes.liftedLhs = blankTape := by
    have hzero := hready.1.control.lookup.destination
    change (cleanWork tapes.liftedLhs).HasBinaryNat 0 at hzero
    simpa only [blankTape] using!
      Tape.HasBinaryNat.eq_init_move_right hzero
  have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
    intro i
    rw [hready.2]
    by_cases hi : i = tapes.liftedLhs
    · subst i
      simp only [Function.update_self]
      exact hasBinaryNat_parked (Tape.init_move_right_hasBinaryNat selector)
    · simp only [Function.update_of_ne hi]
      exact hready.1.control.lookup.scanner.parked i
  have hreset := TM.resetBinaryWorkTM_hoareTime_frame tapes.liftedLhs
    selector.bits 1 inp₀ work₀ out₀
    hselector.2.hasBinaryContent hselector.1
    ⟨by rw [hselector.2.1], by rw [hselector.2.1]⟩
    hinput (fun i _ => hwork₀Parked i) houtput
  have hreset' : (TM.resetBinaryWorkTM tapes.liftedLhs).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = cleanWork ∧ out = out₀)
      (TM.resetBinaryWorkTime 1 selector.bits.length) := by
    apply hreset.consequence
    · exact fun _ _ _ h => h
    · rintro inp work out ⟨hinp, hworkEq, hout⟩
      refine ⟨hinp, ?_, hout⟩
      rw [hworkEq, hready.2, Function.update_idem]
      change Function.update cleanWork tapes.liftedLhs blankTape = cleanWork
      rw [← hcleanLhs, Function.update_eq_self]
    · exact le_rfl
  have hseq := TM.seqTM_hoareTime
    (TM.resetBinaryWorkTM tapes.liftedLhs)
    (executeInstructionTM tapes .halt) hreset'
    (by
      rintro inp work out ⟨hinp, hworkEq, hout⟩
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
        (inp := inp) (work := work) (out := out)
        (by simpa [hinp] using hinput)
        (by simpa [hworkEq] using
          hready.1.control.lookup.scanner.parked)
        (by simpa [hout] using houtput)
      rw [hi, hw, ho]
      exact ⟨hinp, hworkEq, hout⟩)
    (hexecute .halt)
  simpa only [dispatchProgramTM, dispatchProgramTime,
    selectedInstruction] using hseq

/-- The finite decrementing branch tree selects the corresponding static
instruction, assuming the individual instruction kernels satisfy their common
semantic contract. -/
theorem dispatchProgramTM_hoareTime_of_execute_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue selector : ℕ)
    (cleanWork work₀ : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : DispatchReady tapes store pcValue selector cleanWork work₀)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀)
    (hexecute : ∀ instruction,
      (executeInstructionTM tapes instruction).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = cleanWork ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionExecutionResult tapes instruction pcValue store work ∧
          out = out₀)
        (executeInstructionTime tapes instruction pcValue store)) :
    (dispatchProgramTM tapes program).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (selectedInstruction program selector) pcValue store work ∧
        out = out₀)
      (dispatchProgramTime tapes store pcValue program selector) := by
  induction program generalizing selector work₀ with
  | nil =>
      exact dispatchEmptyProgramTM_hoareTime tapes store pcValue selector
        cleanWork work₀ inp₀ out₀ hready hinput houtput hexecute
  | cons instruction program ih =>
      let pre : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧ out = out₀
      let post : TM.TapePred (n + 1) := fun inp work out =>
        inp = inp₀ ∧
          InstructionExecutionResult tapes
            (selectedInstruction (instruction :: program) selector)
            pcValue store work ∧
          out = out₀
      let blankPre : TM.TapePred (n + 1) := fun inp work out =>
        pre inp work out ∧ selector = 0
      let nonblankPre : TM.TapePred (n + 1) := fun inp work out =>
        pre inp work out ∧ selector ≠ 0
      have hselector : (work₀ tapes.liftedLhs).HasBinaryNat selector := by
        rw [hready.2]
        simp only [Function.update_self]
        exact Tape.init_move_right_hasBinaryNat selector
      have hwork₀Parked : ∀ i, TM.Parked (work₀ i) := by
        intro i
        rw [hready.2]
        by_cases hi : i = tapes.liftedLhs
        · subst i
          simp only [Function.update_self]
          exact hasBinaryNat_parked (Tape.init_move_right_hasBinaryNat selector)
        · simp only [Function.update_of_ne hi]
          exact hready.1.control.lookup.scanner.parked i
      have hblank : (executeInstructionTM tapes instruction).HoareTime
          blankPre post
          (executeInstructionTime tapes instruction pcValue store) := by
        rintro inp work out ⟨⟨hinp, hworkEq, hout⟩, hzero⟩
        subst selector
        have hcleanLhs := Tape.HasBinaryNat.eq_init_move_right
          hready.1.control.lookup.destination
        change cleanWork tapes.liftedLhs =
          (Tape.init []).move Dir3.right at hcleanLhs
        have hworkClean : work = cleanWork := by
          rw [hworkEq, hready.2]
          funext i
          by_cases hi : i = tapes.liftedLhs
          · subst i
            simp only [Function.update_self]
            exact hcleanLhs.symm
          · simp only [Function.update_of_ne hi]
        obtain ⟨final, time, htime, hreach, hhalt, hfinalInput,
            hresult, hfinalOutput⟩ :=
          hexecute instruction inp cleanWork out ⟨hinp, rfl, hout⟩
        refine ⟨final, time, htime, ?_, hhalt, hfinalInput, ?_, hfinalOutput⟩
        · simpa [hworkClean] using hreach
        · simpa only [selectedInstruction] using hresult
      have hnonblank :
          (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
            (dispatchProgramTM tapes program)).HoareTime
          nonblankPre post
          (TM.binaryPredTime (selector - 1) + 1 +
            dispatchProgramTime tapes store pcValue program (selector - 1)) := by
        rintro inp work out ⟨⟨hinp, hworkEq, hout⟩, hnonzero⟩
        have hsucc : selector = (selector - 1) + 1 := by omega
        have hvalue : (work tapes.liftedLhs).HasBinaryNat
            ((selector - 1) + 1) := by
          rw [hworkEq]
          rw [hsucc] at hselector
          exact hselector
        have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
        have houtParked : TM.Parked out := by simpa [hout] using houtput
        have hworkParked : ∀ i, TM.Parked (work i) := by
          intro i
          simpa [hworkEq] using hwork₀Parked i
        have hpred := TM.binaryPredTM_hoareTime_frame tapes.liftedLhs
          (selector - 1) inp work out hvalue hinpParked.read_ne_start
          (fun i _ => (hworkParked i).read_ne_start)
          houtParked.read_ne_start
        let nextWork := Function.update cleanWork tapes.liftedLhs
          ((Tape.init ((selector - 1).bits.map Γ.ofBool)).move Dir3.right)
        have hpred' : (TM.binaryPredTM tapes.liftedLhs).HoareTime
            (fun inp' work' out' => inp' = inp ∧ work' = work ∧ out' = out)
            (fun inp' work' out' => inp' = inp ∧ work' = nextWork ∧ out' = out)
            (TM.binaryPredTime (selector - 1)) := by
          apply hpred.consequence
          · exact fun _ _ _ h => h
          · rintro inp' work' out' ⟨hinp', hframe, hvalue', hout'⟩
            refine ⟨hinp', ?_, hout'⟩
            funext i
            by_cases hi : i = tapes.liftedLhs
            · subst i
              simp only [nextWork, Function.update_self]
              exact Tape.HasBinaryNat.eq_init_move_right hvalue'
            · simp only [nextWork, Function.update_of_ne hi]
              rw [hframe i hi, hworkEq, hready.2,
                Function.update_of_ne hi]
          · exact le_rfl
        have hnextReady : DispatchReady tapes store pcValue (selector - 1)
            cleanWork nextWork := ⟨hready.1, rfl⟩
        have hrecursive := ih (selector - 1) nextWork hnextReady
        have hrecursive' : (dispatchProgramTM tapes program).HoareTime
            (fun inp' work' out' => inp' = inp ∧ work' = nextWork ∧ out' = out)
            post
            (dispatchProgramTime tapes store pcValue program
              (selector - 1)) := by
          apply hrecursive.consequence
          · rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            exact ⟨hinp'.trans hinp, hwork', hout'.trans hout⟩
          · rintro inp' work' out' ⟨hinp', hresult, hout'⟩
            have hselected :
                selectedInstruction (instruction :: program) selector =
                  selectedInstruction program (selector - 1) := by
              rw [hsucc]
              rfl
            exact ⟨hinp', by simpa only [hselected] using hresult, hout'⟩
          · exact le_rfl
        have hseq := TM.seqTM_hoareTime (TM.binaryPredTM tapes.liftedLhs)
          (dispatchProgramTM tapes program) hpred'
          (by
            rintro inp' work' out' ⟨hinp', hwork', hout'⟩
            obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked
              (inp := inp') (work := work') (out := out')
              (by simpa [hinp', hinp] using hinput)
              (by
                intro i
                rw [hwork']
                by_cases hidx : i = tapes.liftedLhs
                · subst i
                  simp only [nextWork, Function.update_self]
                  exact hasBinaryNat_parked
                    (Tape.init_move_right_hasBinaryNat (selector - 1))
                · simp only [nextWork, Function.update_of_ne hidx]
                  exact hready.1.control.lookup.scanner.parked i)
              (by simpa [hout', hout] using houtput)
            rw [hi, hw, ho]
            exact ⟨hinp', hwork', hout'⟩)
          hrecursive'
        exact hseq inp work out ⟨rfl, rfl, rfl⟩
      have hdispatch := TM.branchWorkBlankTM_hoareTime tapes.liftedLhs
        (executeInstructionTM tapes instruction)
        (TM.seqTM (TM.binaryPredTM tapes.liftedLhs)
          (dispatchProgramTM tapes program))
        (pre := pre) (blankPre := blankPre) (nonblankPre := nonblankPre)
        (blankPost := post) (nonblankPost := post)
        (fun inp work out hpre => by
          have hinpParked : TM.Parked inp := by simpa [hpre.1] using hinput
          have houtParked : TM.Parked out := by simpa [hpre.2.2] using houtput
          have hworkParked : ∀ i, TM.Parked (work i) := by
            intro i
            simpa [hpre.2.1] using hwork₀Parked i
          exact ⟨hinpParked.read_ne_start,
            fun i => (hworkParked i).read_ne_start,
            houtParked.read_ne_start⟩)
        (fun _ work _ hpre hread =>
          ⟨hpre, hselector.read_eq_blank_iff.mp (by simpa [hpre.2.1] using hread)⟩)
        (fun _ work _ hpre hread =>
          ⟨hpre, fun hzero => hread (by
            rw [hpre.2.1]
            exact hselector.read_eq_blank_iff.mpr hzero)⟩)
        hblank hnonblank
      simpa only [dispatchProgramTM, dispatchProgramTime, pre, post] using
        hdispatch.consequence (fun _ _ _ h => h)
          (fun _ _ _ h => h.elim id id) le_rfl

/-- Reset the seven cleanup targets while preserving the buffer and all other data roles. -/
private theorem bufferedCleanup_resetPhase
    (tapes : ControlInstructionTapes n)
    (oldStore : Store)
    (nextStore : Store)
    (nextPC : ℕ)
    (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (out₀ : Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀)
    (houtput : TM.Parked out₀)
    :
    let targets := instructionCleanupResetTargets tapes
    let resetBits := bufferedCleanupResetBitsAt tapes cleanupValues
      remainingValue oldStore
    let resetHeads :=
      instructionCleanupResetHeadBoundAt tapes sourceHeadBound
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    ((TM.resetBinaryWorkManyTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = resetWork ∧ out = out₀)
      (TM.resetBinaryWorkManyTime resetBits resetHeads targets)) ∧
    (∀ (role : Fin 18)
      (hrole : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      resetWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) ∧
    (resetWork tapes.buffer = initialWork tapes.buffer) ∧
    (∀ i, TM.Parked (resetWork i)) ∧
    (∀ (slot : Fin 7),
      resetWork (instructionCleanupResetTape tapes slot) =
        TM.resetBinaryBlank) := by
  dsimp only
  let targets := instructionCleanupResetTargets tapes
  let resetBits := bufferedCleanupResetBitsAt tapes cleanupValues
    remainingValue oldStore
  let resetHeads :=
    instructionCleanupResetHeadBoundAt tapes sourceHeadBound
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  have hresetContentIndexed : ∀ slot,
      (initialWork (instructionCleanupResetTape tapes slot)).HasBinaryContent
        (bufferedCleanupResetBits cleanupValues remainingValue oldStore
          slot) := by
    intro slot
    fin_cases slot
    · exact (hready.result.cleanup 0).2.hasBinaryContent
    · exact (hready.result.cleanup 1).2.hasBinaryContent
    · exact (hready.result.cleanup 2).2.hasBinaryContent
    · exact (hready.result.cleanup 3).2.hasBinaryContent
    · exact (hready.result.cleanup 4).2.hasBinaryContent
    · exact hready.result.remaining.2.hasBinaryContent
    · exact hready.result.sourceContent
  have hresetStartIndexed : ∀ slot,
      (initialWork (instructionCleanupResetTape tapes slot)).cells 0 =
        Γ.start := by
    intro slot
    fin_cases slot
    · exact (hready.result.cleanup 0).1
    · exact (hready.result.cleanup 1).1
    · exact (hready.result.cleanup 2).1
    · exact (hready.result.cleanup 3).1
    · exact (hready.result.cleanup 4).1
    · exact hready.result.remaining.1
    · exact hready.sourceStart
  have hresetHeadIndexed : ∀ slot,
      (initialWork (instructionCleanupResetTape tapes slot)).head ≤
        instructionCleanupResetHeadBound sourceHeadBound slot := by
    intro slot
    fin_cases slot
    · simpa using! (hready.result.cleanup 0).2.1.le
    · simpa using! (hready.result.cleanup 1).2.1.le
    · simpa using! (hready.result.cleanup 2).2.1.le
    · simpa using! (hready.result.cleanup 3).2.1.le
    · simpa using! (hready.result.cleanup 4).2.1.le
    · simpa using! hready.result.remaining.2.1.le
    · exact hready.sourceHead
  have hreset := TM.resetBinaryWorkManyTM_hoareTime_frame targets resetBits
    resetHeads inp₀ initialWork out₀
    (by
      exact List.nodup_ofFn_ofInjective
        (instructionCleanupResetTape_injective tapes))
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      change (initialWork (instructionCleanupResetTape tapes slot)).HasBinaryContent
        (bufferedCleanupResetBitsAt tapes cleanupValues remainingValue oldStore
          (instructionCleanupResetTape tapes slot))
      rw [bufferedCleanupResetBitsAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      exact hresetContentIndexed slot)
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      exact hresetStartIndexed slot)
    (by
      intro i hi
      obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hi
      change (initialWork (instructionCleanupResetTape tapes slot)).head ≤
        instructionCleanupResetHeadBoundAt tapes sourceHeadBound
          (instructionCleanupResetTape tapes slot)
      rw [instructionCleanupResetHeadBoundAt,
        (instructionCleanupResetTape_injective tapes).extend_apply]
      exact hresetHeadIndexed slot)
    hinput hready.result.parked houtput
  have hdataNotMem (role : Fin 18)
      (hrole : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot) :
      tapes.lifted.data.idx role ∉ targets := by
    intro hi
    obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
    exact tapes.lifted.data.ne (hrole slot) hslot.symm
  have hbufferNotMem : tapes.buffer ∉ targets := by
    intro hi
    obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
    exact tapes.liftedData_ne_buffer
      (instructionCleanupResetParentSlot slot) hslot
  have hresetDataOutside (role : Fin 18)
      (hrole : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot) :
      resetWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role) := by
    exact TM.resetBinaryWorkManyResult_eq_of_not_mem initialWork targets _
      (hdataNotMem role hrole)
  have hresetBuffer : resetWork tapes.buffer = initialWork tapes.buffer := by
    exact TM.resetBinaryWorkManyResult_eq_of_not_mem initialWork targets _
      hbufferNotMem
  have hresetParked : ∀ i, TM.Parked (resetWork i) := by
    exact TM.resetBinaryWorkManyResult_parked initialWork targets
      hready.result.parked
  have hresetTarget (slot : Fin 7) :
      resetWork (instructionCleanupResetTape tapes slot) =
        TM.resetBinaryBlank := by
    exact TM.resetBinaryWorkManyResult_eq_blank_of_mem initialWork targets _
      (List.mem_ofFn.mpr ⟨slot, rfl⟩)
  exact ⟨hreset, hresetDataOutside, hresetBuffer, hresetParked, hresetTarget⟩

/-- Rewind the preserved next-store buffer with the source blank and all tapes parked. -/
private theorem bufferedCleanup_rewindBufferPhase
    (tapes : ControlInstructionTapes n)
    (oldStore : Store)
    (nextStore : Store)
    (nextPC : ℕ)
    (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (out₀ : Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀)
    (houtput : TM.Parked out₀)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    (resetWork tapes.buffer = initialWork tapes.buffer) →
    (∀ i, TM.Parked (resetWork i)) →
    (∀ (slot : Fin 7),
      resetWork (instructionCleanupResetTape tapes slot) =
        TM.resetBinaryBlank) →
    ((TM.rewindWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = resetWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
      (nextBits.length + 1 + 2)) ∧
    (rewoundWork tapes.liftedSource = TM.resetBinaryBlank) ∧
    (∀ i, TM.Parked (rewoundWork i)) := by
  dsimp only
  intro hresetBuffer hresetParked hresetTarget
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  have hresetBufferContent :
      (resetWork tapes.buffer).HasBinaryContent nextBits := by
    rw [hresetBuffer]
    exact hready.result.buffer.2
  have hresetBufferStart : (resetWork tapes.buffer).cells 0 = Γ.start := by
    rw [hresetBuffer]
    exact hready.bufferStart
  have hresetBufferHead :
      (resetWork tapes.buffer).head = nextBits.length + 1 := by
    rw [hresetBuffer]
    exact hready.result.buffer.1
  have hrewindRaw := TM.rewindBinaryWorkTM_hoareTime_frame tapes.buffer
    nextBits (nextBits.length + 1) inp₀ resetWork out₀
    hresetBufferContent hresetBufferStart
    ⟨by rw [hresetBufferHead]; omega, hresetBufferHead.le⟩ hinput
    (fun i _ => hresetParked i) houtput
  have hrewind : (TM.rewindWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = resetWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
      (nextBits.length + 1 + 2) := hrewindRaw.strengthen_post (by
    rintro inp work out ⟨hinp, htarget, hframe, hout⟩
    have hwork : work = rewoundWork := by
      funext i
      by_cases hi : i = tapes.buffer
      · subst i
        simpa [rewoundWork, nextTape] using htarget
      · simp [rewoundWork, hi, hframe i hi]
    exact ⟨hinp, hwork, hout⟩)
  have hresetSource : resetWork tapes.liftedSource = TM.resetBinaryBlank := by
    simpa [instructionCleanupResetTape, instructionCleanupResetParentSlot,
      ControlInstructionTapes.liftedSource] using! hresetTarget 6
  have hrewoundSource :
      rewoundWork tapes.liftedSource = TM.resetBinaryBlank := by
    simp [rewoundWork, tapes.liftedSource_ne_buffer, hresetSource]
  have hrewoundParked : ∀ i, TM.Parked (rewoundWork i) := by
    intro i
    by_cases hi : i = tapes.buffer
    · subst i
      simp only [rewoundWork, Function.update_self, nextTape]
      exact hasBinaryString_parked
        (Tape.init_move_right_hasBinaryString nextBits)
    · simp only [rewoundWork, Function.update_of_ne hi]
      exact hresetParked i
  exact ⟨hrewind, hrewoundSource, hrewoundParked⟩

/-- Copy the next-store bits from the rewound buffer to the blank source with an exact frame. -/
private theorem bufferedCleanup_copyPhase
    (tapes : ControlInstructionTapes n)
    (nextStore : Store)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (out₀ : Tape)
    (hinput : TM.Parked inp₀)
    (houtput : TM.Parked out₀)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    (rewoundWork tapes.liftedSource = TM.resetBinaryBlank) →
    (∀ i, TM.Parked (rewoundWork i)) →
    ((TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
        (nextBits.length + 1)) ∧
    (copiedWork tapes.buffer = prefixTape) ∧
    (copiedWork tapes.liftedSource = prefixTape) ∧
    (∀ i, TM.Parked (copiedWork i)) := by
  dsimp only
  intro hrewoundSource hrewoundParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let copyFrame : TM.TapePred (n + 1) := fun inp work out =>
    inp = inp₀ ∧ out = out₀ ∧
      ∀ i, i ≠ tapes.buffer → i ≠ tapes.liftedSource →
        work i = rewoundWork i
  have hcopyBase := TM.copyWorkToWorkTM_hoareTime_frame_of_binaryString
    tapes.buffer tapes.liftedSource tapes.liftedSource_ne_buffer.symm
    nextBits (P := copyFrame)
    (by
      rintro inp work out inp' work' out'
        ⟨hinp, hout, hframe⟩ _ _ _ _ hinpEq houtEq hworkFrame
      refine ⟨hinpEq.trans hinp, houtEq.trans hout, ?_⟩
      intro i hiBuffer hiSource
      rw [hworkFrame i hiBuffer hiSource]
      exact hframe i hiBuffer hiSource)
  have hcopyReady :
      (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
        (fun inp work out =>
          (work tapes.buffer).cells =
              (Tape.init (nextBits.map Γ.ofBool)).cells ∧
          (work tapes.buffer).head = nextBits.length + 1 ∧
          (work tapes.liftedSource).HasBinaryPrefix nextBits ∧
          (work tapes.liftedSource).cells 0 = Γ.start ∧
          copyFrame inp work out)
        (nextBits.length + 1) := hcopyBase.consequence
      (by
        rintro inp work out ⟨hinp, hwork, hout⟩
        subst work
        refine ⟨?_, hrewoundSource, ?_, ?_, ?_, ?_, ?_⟩
        · simp [rewoundWork, nextTape]
        · simpa [hinp] using hinput.read_ne_start
        · simpa [hout] using houtput.read_ne_start
        · simpa [hout] using houtput.1
        · intro i _ _
          exact ⟨(hrewoundParked i).read_ne_start, (hrewoundParked i).1⟩
        · exact ⟨hinp, hout, fun _ _ _ => rfl⟩)
      (fun _ _ _ h => h) le_rfl
  have hcopy :
      (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = rewoundWork ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
        (nextBits.length + 1) := hcopyReady.strengthen_post (by
      rintro inp work out ⟨hsrcCells, hsrcHead, hdstPrefix, hdstStart,
        hinp, hout, hframe⟩
      have hsrc : work tapes.buffer = prefixTape := by
        exact Tape.ext (by simpa [prefixTape, instructionCleanupPrefixTape]
          using hsrcHead) (by simpa [prefixTape, instructionCleanupPrefixTape]
          using hsrcCells)
      have hdst : work tapes.liftedSource = prefixTape := by
        exact Tape.ext (by simpa [prefixTape, instructionCleanupPrefixTape]
          using hdstPrefix.1) (by
            simpa [prefixTape, instructionCleanupPrefixTape] using
              hdstPrefix.cells_eq_init hdstStart)
      have hwork : work = copiedWork := by
        funext i
        by_cases hiSource : i = tapes.liftedSource
        · subst i
          simp [copiedWork, hdst]
        by_cases hiBuffer : i = tapes.buffer
        · subst i
          simpa only [copiedWork,
            Function.update_of_ne tapes.liftedSource_ne_buffer.symm,
            Function.update_self] using hsrc
        · simp [copiedWork, hiSource, hiBuffer,
            hframe i hiBuffer hiSource]
      exact ⟨hinp, hwork, hout⟩)
  have hcopiedBuffer : copiedWork tapes.buffer = prefixTape := by
    simp [copiedWork, tapes.liftedSource_ne_buffer.symm]
  have hcopiedSource : copiedWork tapes.liftedSource = prefixTape := by
    simp [copiedWork]
  have hcopiedParked : ∀ i, TM.Parked (copiedWork i) := by
    intro i
    by_cases hiSource : i = tapes.liftedSource
    · subst i
      simpa [hcopiedSource] using
        instructionCleanupPrefixTape_parked nextBits
    by_cases hiBuffer : i = tapes.buffer
    · subst i
      simpa [hcopiedBuffer] using
        instructionCleanupPrefixTape_parked nextBits
    · simp [copiedWork, hiSource, hiBuffer]
      exact hrewoundParked i
  exact ⟨hcopy, hcopiedBuffer, hcopiedSource, hcopiedParked⟩

/-- Clear the copied buffer and rewind the source, preserving the other reset tapes. -/
private theorem bufferedCleanup_restoreSourcePhase
    (tapes : ControlInstructionTapes n)
    (nextStore : Store)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (out₀ : Tape)
    (hinput : TM.Parked inp₀)
    (houtput : TM.Parked out₀)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    (copiedWork tapes.buffer = prefixTape) →
    (copiedWork tapes.liftedSource = prefixTape) →
    (∀ i, TM.Parked (copiedWork i)) →
    (∀ i, TM.Parked (resetWork i)) →
    ((TM.resetBinaryWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = bufferResetWork ∧ out = out₀)
      (TM.resetBinaryWorkTime (nextBits.length + 1) nextBits.length)) ∧
    ((TM.rewindWorkTM tapes.liftedSource).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = bufferResetWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = sourceReadyWork ∧ out = out₀)
      (nextBits.length + 1 + 2)) ∧
    (∀ (i : Fin (n + 1))
      (hiSource : i ≠ tapes.liftedSource) (hiBuffer : i ≠ tapes.buffer),
      sourceReadyWork i = resetWork i) ∧
    (∀ i, TM.Parked (sourceReadyWork i)) ∧
    (∀ i, TM.Parked (bufferResetWork i)) := by
  dsimp only
  intro hcopiedBuffer hcopiedSource hcopiedParked hresetParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  have hresetBufferRaw := TM.resetBinaryWorkTM_hoareTime_frame tapes.buffer
    nextBits (nextBits.length + 1) inp₀ copiedWork out₀
    (by
      rw [hcopiedBuffer]
      exact (instructionCleanupPrefixTape_hasBinaryPrefix nextBits).2)
    (by
      rw [hcopiedBuffer]
      exact instructionCleanupPrefixTape_start nextBits)
    (by
      rw [hcopiedBuffer]
      exact ⟨by simp [prefixTape, instructionCleanupPrefixTape], le_rfl⟩)
    hinput (fun i _ => hcopiedParked i) houtput
  have hresetBufferPhase : (TM.resetBinaryWorkTM tapes.buffer).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = bufferResetWork ∧ out = out₀)
      (TM.resetBinaryWorkTime (nextBits.length + 1) nextBits.length) := by
    simpa only [bufferResetWork] using hresetBufferRaw
  have hbufferResetSource :
      bufferResetWork tapes.liftedSource = prefixTape := by
    simp [bufferResetWork, tapes.liftedSource_ne_buffer, hcopiedSource]
  have hbufferResetParked : ∀ i, TM.Parked (bufferResetWork i) := by
    intro i
    by_cases hi : i = tapes.buffer
    · subst i
      simp only [bufferResetWork, Function.update_self]
      exact hasBinaryString_parked
        (Tape.init_move_right_hasBinaryString [])
    · simp only [bufferResetWork, Function.update_of_ne hi]
      exact hcopiedParked i
  have hrewindSourceRaw := TM.rewindBinaryWorkTM_hoareTime_frame
    tapes.liftedSource nextBits (nextBits.length + 1) inp₀ bufferResetWork
    out₀
    (by
      rw [hbufferResetSource]
      exact (instructionCleanupPrefixTape_hasBinaryPrefix nextBits).2)
    (by
      rw [hbufferResetSource]
      exact instructionCleanupPrefixTape_start nextBits)
    (by
      rw [hbufferResetSource]
      exact ⟨by simp [prefixTape, instructionCleanupPrefixTape], le_rfl⟩)
    hinput (fun i _ => hbufferResetParked i) houtput
  have hrewindSource : (TM.rewindWorkTM tapes.liftedSource).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = bufferResetWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = sourceReadyWork ∧ out = out₀)
      (nextBits.length + 1 + 2) :=
    hrewindSourceRaw.strengthen_post (by
      rintro inp work out ⟨hinp, htarget, hframe, hout⟩
      have hwork : work = sourceReadyWork := by
        funext i
        by_cases hi : i = tapes.liftedSource
        · subst i
          simpa [sourceReadyWork, nextTape] using htarget
        · simp [sourceReadyWork, hi, hframe i hi]
      exact ⟨hinp, hwork, hout⟩)
  have hsourceReadyOutside (i : Fin (n + 1))
      (hiSource : i ≠ tapes.liftedSource) (hiBuffer : i ≠ tapes.buffer) :
      sourceReadyWork i = resetWork i := by
    simp [sourceReadyWork, bufferResetWork, copiedWork, rewoundWork,
      hiSource, hiBuffer]
  have hsourceReadyParked : ∀ i, TM.Parked (sourceReadyWork i) := by
    intro i
    by_cases hiSource : i = tapes.liftedSource
    · subst i
      simp only [sourceReadyWork, Function.update_self, nextTape]
      exact hasBinaryString_parked
        (Tape.init_move_right_hasBinaryString nextBits)
    by_cases hiBuffer : i = tapes.buffer
    · subst i
      simp only [sourceReadyWork, Function.update_of_ne
        tapes.liftedSource_ne_buffer.symm]
      exact hbufferResetParked tapes.buffer
    · rw [hsourceReadyOutside i hiSource hiBuffer]
      exact hresetParked i
  exact ⟨hresetBufferPhase, hrewindSource, hsourceReadyOutside,
    hsourceReadyParked, hbufferResetParked⟩

/-- Copy the next-store entry count into the cleared remaining-count tape. -/
private theorem bufferedCleanup_copyCountPhase
    (tapes : ControlInstructionTapes n)
    (oldStore : Store)
    (nextStore : Store)
    (nextPC : ℕ)
    (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (inp₀ : Tape)
    (out₀ : Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀)
    (houtput : TM.Parked out₀)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    let countTape :=
      (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
    let finalWork := Function.update sourceReadyWork
      tapes.lifted.data.update.remaining countTape
    (∀ (i : Fin (n + 1))
      (hiSource : i ≠ tapes.liftedSource) (hiBuffer : i ≠ tapes.buffer),
      sourceReadyWork i = resetWork i) →
    (∀ (role : Fin 18)
      (hrole : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      resetWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) →
    (∀ (slot : Fin 7),
      resetWork (instructionCleanupResetTape tapes slot) =
        TM.resetBinaryBlank) →
    (∀ i, TM.Parked (sourceReadyWork i)) →
    ((TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
        tapes.lifted.data.update.remaining
        tapes.lifted.data.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = sourceReadyWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = finalWork ∧ out = out₀)
      (TM.binaryCopyTime nextStore.length 0)) := by
  dsimp only
  intro hsourceReadyOutside hresetDataOutside hresetTarget hsourceReadyParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  have hresultCount :
      (sourceReadyWork tapes.lifted.data.update.resultCount).HasBinaryNat
        nextStore.length := by
    change (sourceReadyWork (tapes.lifted.data.idx 12)).HasBinaryNat _
    rw [hsourceReadyOutside _ (tapes.lifted.data.ne (by decide))
      (tapes.liftedData_ne_buffer 12),
      hresetDataOutside 12 (by intro slot; fin_cases slot <;> decide)]
    exact hready.result.resultCount
  have hremainingZero :
      (sourceReadyWork tapes.lifted.data.update.remaining).HasBinaryNat 0 := by
    change (sourceReadyWork (tapes.lifted.data.idx 9)).HasBinaryNat 0
    rw [hsourceReadyOutside _ (tapes.lifted.data.ne (by decide))
      (tapes.liftedData_ne_buffer 9)]
    have htarget : resetWork (tapes.lifted.data.idx 9) =
        TM.resetBinaryBlank := by
      simpa [instructionCleanupResetTape,
        instructionCleanupResetParentSlot] using hresetTarget 5
    rw [htarget]
    simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  have hfoundZero :
      (sourceReadyWork tapes.lifted.data.update.found).HasBinaryNat 0 := by
    change (sourceReadyWork (tapes.lifted.data.idx 11)).HasBinaryNat 0
    rw [hsourceReadyOutside _ (tapes.lifted.data.ne (by decide))
      (tapes.liftedData_ne_buffer 11)]
    have htarget : resetWork (tapes.lifted.data.idx 11) =
        TM.resetBinaryBlank := by
      simpa [instructionCleanupResetTape,
        instructionCleanupResetParentSlot] using hresetTarget 2
    rw [htarget]
    simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  have hcountCopyRaw := TM.binaryCopyIntoTM_hoareTime_frame
    tapes.lifted.data.update.resultCount
    tapes.lifted.data.update.remaining tapes.lifted.data.update.found
    (tapes.lifted.data.ne (by decide))
    (tapes.lifted.data.ne (by decide))
    (tapes.lifted.data.ne (by decide)) nextStore.length 0 inp₀
    sourceReadyWork out₀ hresultCount hremainingZero hfoundZero hinput
    (fun i _ _ _ => hsourceReadyParked i) houtput
  have hcountCopy :
      (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
        tapes.lifted.data.update.remaining
        tapes.lifted.data.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = sourceReadyWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = finalWork ∧ out = out₀)
      (TM.binaryCopyTime nextStore.length 0) := by
    simpa only [finalWork, countTape] using hcountCopyRaw
  exact hcountCopy

/-- Identify the preserved, cleared, and refreshed roles in the final work-tape frame. -/
private theorem bufferedCleanup_finalFrame
    (tapes : ControlInstructionTapes n)
    (nextStore : Store)
    (initialWork : Fin (n + 1) → Tape)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    let countTape :=
      (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
    let finalWork := Function.update sourceReadyWork
      tapes.lifted.data.update.remaining countTape
    (∀ (i : Fin (n + 1))
      (hiSource : i ≠ tapes.liftedSource) (hiBuffer : i ≠ tapes.buffer),
      sourceReadyWork i = resetWork i) →
    (∀ (role : Fin 18)
      (hrole : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      resetWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) →
    (∀ (slot : Fin 7),
      resetWork (instructionCleanupResetTape tapes slot) =
        TM.resetBinaryBlank) →
    (∀ i, TM.Parked (sourceReadyWork i)) →
    (∀ (role : Fin 18)
      (hremaining : role ≠ 9) (hsource : role ≠ 0)
      (hreset : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      finalWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) ∧
    (∀ (slot : Fin 5),
      finalWork (instructionCleanupTape tapes slot) =
        TM.resetBinaryBlank) ∧
    (TM.resetBinaryBlank.HasBinaryNat 0) ∧
    (finalWork tapes.liftedSource = nextTape) ∧
    (finalWork tapes.buffer = (Tape.init []).move Dir3.right) ∧
    (∀ i, TM.Parked (finalWork i)) := by
  dsimp only
  intro hsourceReadyOutside hresetDataOutside hresetTarget hsourceReadyParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  have hfinalDataOutside (role : Fin 18) (hremaining : role ≠ 9)
      (hsource : role ≠ 0) :
      finalWork (tapes.lifted.data.idx role) =
        resetWork (tapes.lifted.data.idx role) := by
    rw [show finalWork (tapes.lifted.data.idx role) =
        sourceReadyWork (tapes.lifted.data.idx role) from
      Function.update_of_ne (tapes.lifted.data.ne hremaining) _ _]
    exact hsourceReadyOutside _ (tapes.lifted.data.ne hsource)
      (tapes.liftedData_ne_buffer role)
  have hfinalPreservedData (role : Fin 18)
      (hremaining : role ≠ 9) (hsource : role ≠ 0)
      (hreset : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot) :
      finalWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role) := by
    rw [hfinalDataOutside role hremaining hsource,
      hresetDataOutside role hreset]
  have hfinalReset (slot : Fin 5) :
      finalWork (instructionCleanupTape tapes slot) =
        TM.resetBinaryBlank := by
    fin_cases slot
    · change finalWork (tapes.lifted.data.idx 7) = _
      rw [hfinalDataOutside 7 (by decide) (by decide)]
      simpa [instructionCleanupTape, instructionCleanupResetTape,
        instructionCleanupParentSlot, instructionCleanupResetParentSlot]
        using hresetTarget 0
    · change finalWork (tapes.lifted.data.idx 10) = _
      rw [hfinalDataOutside 10 (by decide) (by decide)]
      simpa [instructionCleanupTape, instructionCleanupResetTape,
        instructionCleanupParentSlot, instructionCleanupResetParentSlot]
        using hresetTarget 1
    · change finalWork (tapes.lifted.data.idx 11) = _
      rw [hfinalDataOutside 11 (by decide) (by decide)]
      simpa [instructionCleanupTape, instructionCleanupResetTape,
        instructionCleanupParentSlot, instructionCleanupResetParentSlot]
        using hresetTarget 2
    · change finalWork (tapes.lifted.data.idx 13) = _
      rw [hfinalDataOutside 13 (by decide) (by decide)]
      simpa [instructionCleanupTape, instructionCleanupResetTape,
        instructionCleanupParentSlot, instructionCleanupResetParentSlot]
        using hresetTarget 3
    · change finalWork (tapes.lifted.data.idx 14) = _
      rw [hfinalDataOutside 14 (by decide) (by decide)]
      simpa [instructionCleanupTape, instructionCleanupResetTape,
        instructionCleanupParentSlot, instructionCleanupResetParentSlot]
        using hresetTarget 4
  have hblankNat : TM.resetBinaryBlank.HasBinaryNat 0 := by
    simpa [TM.resetBinaryBlank] using Tape.init_move_right_hasBinaryNat 0
  have hfinalSource : finalWork tapes.liftedSource = nextTape := by
    change finalWork (tapes.lifted.data.idx 0) = nextTape
    rw [show finalWork (tapes.lifted.data.idx 0) =
        sourceReadyWork (tapes.lifted.data.idx 0) from
      Function.update_of_ne (tapes.lifted.data.ne (by decide)) _ _]
    exact Function.update_self _ _ _
  have hfinalBuffer :
      finalWork tapes.buffer = (Tape.init []).move Dir3.right := by
    rw [show finalWork tapes.buffer = sourceReadyWork tapes.buffer from
      Function.update_of_ne (tapes.liftedData_ne_buffer 9).symm _ _]
    rw [show sourceReadyWork tapes.buffer = bufferResetWork tapes.buffer from
      Function.update_of_ne tapes.liftedSource_ne_buffer.symm _ _]
    exact Function.update_self _ _ _
  have hfinalParked : ∀ i, TM.Parked (finalWork i) := by
    intro i
    by_cases hi : i = tapes.lifted.data.update.remaining
    · subst i
      simp only [finalWork, Function.update_self, countTape]
      exact hasBinaryNat_parked
        (Tape.init_move_right_hasBinaryNat nextStore.length)
    · simp only [finalWork, Function.update_of_ne hi]
      exact hsourceReadyParked i
  exact ⟨hfinalPreservedData, hfinalReset, hblankNat, hfinalSource, hfinalBuffer, hfinalParked⟩

/-- Restore the reusable entry-scanner contract from the final tape frame. -/
private theorem bufferedCleanup_finalScanner
    (tapes : ControlInstructionTapes n)
    (oldStore : Store)
    (nextStore : Store)
    (nextPC : ℕ)
    (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    let countTape :=
      (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
    let finalWork := Function.update sourceReadyWork
      tapes.lifted.data.update.remaining countTape
    (finalWork tapes.liftedSource = nextTape) →
    (∀ (role : Fin 18)
      (hremaining : role ≠ 9) (hsource : role ≠ 0)
      (hreset : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      finalWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) →
    (∀ (slot : Fin 5),
      finalWork (instructionCleanupTape tapes slot) =
        TM.resetBinaryBlank) →
    (TM.resetBinaryBlank.HasBinaryNat 0) →
    (∀ i, TM.Parked (finalWork i)) →
    (EntryScanReady tapes.lifted.data.update.entry
      nextBits [] finalWork finalWork) := by
  dsimp only
  intro hfinalSource hfinalPreservedData hfinalReset hblankNat hfinalParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  have hfinalScanner : EntryScanReady tapes.lifted.data.update.entry
      nextBits [] finalWork finalWork := by
    let entry := tapes.lifted.data.update.entry
    refine
      { source := by
          change (finalWork tapes.liftedSource).HasBinarySuffix nextBits
          rw [hfinalSource]
          exact (Tape.init_move_right_hasBinaryString nextBits).hasBinarySuffix
        address := by
          change (finalWork (tapes.lifted.data.idx 1)).HasBinaryPrefix []
          rw [hfinalPreservedData 1 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.address
        addressStart := by
          change (finalWork (tapes.lifted.data.idx 1)).cells 0 = Γ.start
          rw [hfinalPreservedData 1 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.addressStart
        value := by
          change (finalWork (tapes.lifted.data.idx 2)).HasBinaryPrefix []
          rw [hfinalPreservedData 2 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.value
        valueStart := by
          change (finalWork (tapes.lifted.data.idx 2)).cells 0 = Γ.start
          rw [hfinalPreservedData 2 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.valueStart
        addressCounter := by
          change (finalWork (tapes.lifted.data.idx 3)).HasBinaryNat 0
          rw [hfinalPreservedData 3 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.addressCounter
        addressWidth := by
          change (finalWork (tapes.lifted.data.idx 4)).HasBinaryNat 0
          rw [hfinalPreservedData 4 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.addressWidth
        valueCounter := by
          change (finalWork (tapes.lifted.data.idx 5)).HasBinaryNat 0
          rw [hfinalPreservedData 5 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.valueCounter
        valueWidth := by
          change (finalWork (tapes.lifted.data.idx 6)).HasBinaryNat 0
          rw [hfinalPreservedData 6 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.valueWidth
        query := by
          change (finalWork (instructionCleanupTape tapes 0)).HasBinaryString []
          rw [hfinalReset 0]
          exact hblankNat.2
        queryStart := by
          change (finalWork (instructionCleanupTape tapes 0)).cells 0 = Γ.start
          rw [hfinalReset 0]
          exact hblankNat.1
        result := by
          change (finalWork (tapes.lifted.data.idx 8)).HasBinaryPrefix []
          rw [hfinalPreservedData 8 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.result
        resultStart := by
          change (finalWork (tapes.lifted.data.idx 8)).cells 0 = Γ.start
          rw [hfinalPreservedData 8 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.scanner.resultStart
        parked := hfinalParked
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  exact hfinalScanner

/-- Preserve the program counter and transport the restored scanner to the lookup layout. -/
private theorem bufferedCleanup_finalLookup
    (tapes : ControlInstructionTapes n)
    (nextStore : Store)
    (initialWork : Fin (n + 1) → Tape)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    let countTape :=
      (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
    let finalWork := Function.update sourceReadyWork
      tapes.lifted.data.update.remaining countTape
    (∀ (i : Fin (n + 1))
      (hiSource : i ≠ tapes.liftedSource) (hiBuffer : i ≠ tapes.buffer),
      sourceReadyWork i = resetWork i) →
    (EntryScanReady tapes.lifted.data.update.entry
      nextBits [] finalWork finalWork) →
    (∀ i, TM.Parked (finalWork i)) →
    (finalWork tapes.liftedPC = initialWork tapes.liftedPC) ∧
    (EntryScanReady
      tapes.lifted.data.lhsLookup.scan.entry nextBits [] finalWork
        finalWork) := by
  dsimp only
  intro hsourceReadyOutside hfinalScanner hfinalParked
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  have hfinalPC : finalWork tapes.liftedPC = initialWork tapes.liftedPC := by
    rw [show finalWork tapes.liftedPC = sourceReadyWork tapes.liftedPC by
      exact Function.update_of_ne (tapes.lifted.pc_ne 9) _ _]
    rw [hsourceReadyOutside _ tapes.liftedPC_ne_source
      tapes.liftedPC_ne_buffer]
    exact TM.resetBinaryWorkManyResult_eq_of_not_mem initialWork targets _ (by
      intro hi
      obtain ⟨slot, hslot⟩ := List.mem_ofFn.mp hi
      exact tapes.lifted.pc_ne (instructionCleanupResetParentSlot slot)
        hslot.symm)
  have hfinalLookupScanner : EntryScanReady
      tapes.lifted.data.lhsLookup.scan.entry nextBits [] finalWork
        finalWork := by
    refine
      { source := by
          change (finalWork (tapes.lifted.data.idx 0)).HasBinarySuffix nextBits
          exact hfinalScanner.source
        address := by
          change (finalWork (tapes.lifted.data.idx 1)).HasBinaryPrefix []
          exact hfinalScanner.address
        addressStart := by
          change (finalWork (tapes.lifted.data.idx 1)).cells 0 = Γ.start
          exact hfinalScanner.addressStart
        value := by
          change (finalWork (tapes.lifted.data.idx 2)).HasBinaryPrefix []
          exact hfinalScanner.value
        valueStart := by
          change (finalWork (tapes.lifted.data.idx 2)).cells 0 = Γ.start
          exact hfinalScanner.valueStart
        addressCounter := by
          change (finalWork (tapes.lifted.data.idx 3)).HasBinaryNat 0
          exact hfinalScanner.addressCounter
        addressWidth := by
          change (finalWork (tapes.lifted.data.idx 4)).HasBinaryNat 0
          exact hfinalScanner.addressWidth
        valueCounter := by
          change (finalWork (tapes.lifted.data.idx 5)).HasBinaryNat 0
          exact hfinalScanner.valueCounter
        valueWidth := by
          change (finalWork (tapes.lifted.data.idx 6)).HasBinaryNat 0
          exact hfinalScanner.valueWidth
        query := by
          change (finalWork (tapes.lifted.data.idx 7)).HasBinaryString []
          exact hfinalScanner.query
        queryStart := by
          change (finalWork (tapes.lifted.data.idx 7)).cells 0 = Γ.start
          exact hfinalScanner.queryStart
        result := by
          change (finalWork (tapes.lifted.data.idx 8)).HasBinaryPrefix []
          exact hfinalScanner.result
        resultStart := by
          change (finalWork (tapes.lifted.data.idx 8)).cells 0 = Γ.start
          exact hfinalScanner.resultStart
        parked := hfinalParked
        frame := by intro i _ _ _ _ _ _ _ _ _; rfl }
  exact ⟨hfinalPC, hfinalLookupScanner⟩

/-- Assemble the complete clean instruction ABI from the restored scanner and final frame. -/
private theorem bufferedCleanup_finalReady
    (tapes : ControlInstructionTapes n)
    (oldStore : Store)
    (nextStore : Store)
    (nextPC : ℕ)
    (cleanupValues : Fin 5 → ℕ)
    (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    :
    let nextBits := nextStore.flatMap Entry.encode
    let targets := instructionCleanupResetTargets tapes
    let resetWork := TM.resetBinaryWorkManyResult initialWork targets
    let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
    let rewoundWork := Function.update resetWork tapes.buffer nextTape
    let prefixTape := instructionCleanupPrefixTape nextBits
    let copiedWork := Function.update
      (Function.update rewoundWork tapes.buffer prefixTape)
      tapes.liftedSource prefixTape
    let bufferResetWork := Function.update copiedWork tapes.buffer
      ((Tape.init []).move Dir3.right)
    let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
      nextTape
    let countTape :=
      (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
    let finalWork := Function.update sourceReadyWork
      tapes.lifted.data.update.remaining countTape
    (EntryScanReady
      tapes.lifted.data.lhsLookup.scan.entry nextBits [] finalWork
        finalWork) →
    (finalWork tapes.liftedSource = nextTape) →
    (∀ (role : Fin 18)
      (hremaining : role ≠ 9) (hsource : role ≠ 0)
      (hreset : ∀ slot : Fin 7,
        role ≠ instructionCleanupResetParentSlot slot),
      finalWork (tapes.lifted.data.idx role) =
        initialWork (tapes.lifted.data.idx role)) →
    (∀ (slot : Fin 5),
      finalWork (instructionCleanupTape tapes slot) =
        TM.resetBinaryBlank) →
    (TM.resetBinaryBlank.HasBinaryNat 0) →
    (finalWork tapes.liftedPC = initialWork tapes.liftedPC) →
    (finalWork tapes.buffer = (Tape.init []).move Dir3.right) →
    (InstructionExecutionReady tapes nextStore
      nextPC finalWork) := by
  dsimp only
  intro hfinalLookupScanner hfinalSource hfinalPreservedData hfinalReset
    hblankNat hfinalPC hfinalBuffer
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  have hfinalReady : InstructionExecutionReady tapes nextStore
      nextPC finalWork := by
    refine
      { canonical := hready.nextCanonical
        control :=
          { lookup :=
              { scanner := by simpa [nextBits] using hfinalLookupScanner
                sourceStart := by
                  change (finalWork tapes.liftedSource).cells 0 = Γ.start
                  rw [hfinalSource]
                  simp [nextTape, Tape.init, Tape.move]
                sourceHead := by
                  change (finalWork tapes.liftedSource).head = 1
                  rw [hfinalSource]
                  simp [nextTape, Tape.move]
                count := by
                  change (finalWork (tapes.lifted.data.idx 9)).HasBinaryNat _
                  rw [show finalWork (tapes.lifted.data.idx 9) = countTape from
                    Function.update_self _ _ _]
                  exact Tape.init_move_right_hasBinaryNat nextStore.length
                countSource := by
                  change (finalWork (tapes.lifted.data.idx 12)).HasBinaryNat _
                  rw [hfinalPreservedData 12 (by decide) (by decide)
                    (by intro slot; fin_cases slot <;> decide)]
                  exact hready.result.resultCount
                querySource := by
                  change (finalWork (tapes.lifted.data.idx 15)).HasBinaryNat 0
                  rw [hfinalPreservedData 15 (by decide) (by decide)
                    (by intro slot; fin_cases slot <;> decide)]
                  exact hready.result.shift
                destination := by
                  change (finalWork (instructionCleanupTape tapes 3)).HasBinaryNat 0
                  rw [hfinalReset 3]
                  exact hblankNat
                copyScratch := by
                  change (finalWork (instructionCleanupTape tapes 2)).HasBinaryNat 0
                  rw [hfinalReset 2]
                  exact hblankNat }
            pc := by
              change (finalWork tapes.liftedPC).HasBinaryNat _
              rw [hfinalPC]
              exact hready.result.pc }
        sourceContent := by
          rw [hfinalSource]
          exact (Tape.init_move_right_hasBinaryString nextBits).hasBinaryContent
        rhs := by
          rw [show tapes.lifted.data.rhs = instructionCleanupTape tapes 4 by rfl,
            hfinalReset 4]
          exact hblankNat
        replacement := by
          rw [show tapes.lifted.data.update.replacement =
              instructionCleanupTape tapes 1 by rfl,
            hfinalReset 1]
          exact hblankNat
        tmp := by
          change (finalWork (tapes.lifted.data.idx 16)).HasBinaryNat 0
          rw [hfinalPreservedData 16 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.tmp
        dbl := by
          change (finalWork (tapes.lifted.data.idx 17)).HasBinaryNat 0
          rw [hfinalPreservedData 17 (by decide) (by decide)
            (by intro slot; fin_cases slot <;> decide)]
          exact hready.result.dbl
        buffer := hfinalBuffer }
  exact hfinalReady

/-- Any buffered representation endpoint is restored to the reusable clean ABI. -/
theorem bufferedCleanupTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (oldStore nextStore : Store)
    (nextPC : ℕ) (cleanupValues : Fin 5 → ℕ) (remainingValue : ℕ)
    (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : BufferedCleanupReady tapes oldStore nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (instructionCleanupTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionReady tapes nextStore nextPC work ∧
        out = out₀)
      (bufferedCleanupTime tapes oldStore nextStore cleanupValues
        remainingValue sourceHeadBound) := by
  let nextBits := nextStore.flatMap Entry.encode
  let targets := instructionCleanupResetTargets tapes
  let resetBits := bufferedCleanupResetBitsAt tapes cleanupValues
    remainingValue oldStore
  let resetHeads :=
    instructionCleanupResetHeadBoundAt tapes sourceHeadBound
  let resetWork := TM.resetBinaryWorkManyResult initialWork targets
  let nextTape := (Tape.init (nextBits.map Γ.ofBool)).move Dir3.right
  obtain ⟨hreset, hresetDataOutside, hresetBuffer, hresetParked, hresetTarget⟩ :=
    bufferedCleanup_resetPhase
      (tapes := tapes)
      (oldStore := oldStore)
      (nextStore := nextStore)
      (nextPC := nextPC)
      (cleanupValues := cleanupValues)
      (remainingValue := remainingValue)
      (sourceHeadBound := sourceHeadBound)
      (initialWork := initialWork)
      (inp₀ := inp₀)
      (out₀ := out₀)
      (hready := hready)
      (hinput := hinput)
      (houtput := houtput)
  obtain ⟨hrewind, hrewoundSource, hrewoundParked⟩ :=
    bufferedCleanup_rewindBufferPhase
      (tapes := tapes)
      (oldStore := oldStore)
      (nextStore := nextStore)
      (nextPC := nextPC)
      (cleanupValues := cleanupValues)
      (remainingValue := remainingValue)
      (sourceHeadBound := sourceHeadBound)
      (initialWork := initialWork)
      (inp₀ := inp₀)
      (out₀ := out₀)
      (hready := hready)
      (hinput := hinput)
      (houtput := houtput)
      hresetBuffer hresetParked hresetTarget
  let rewoundWork := Function.update resetWork tapes.buffer nextTape
  obtain ⟨hcopy, hcopiedBuffer, hcopiedSource, hcopiedParked⟩ :=
    bufferedCleanup_copyPhase
      (tapes := tapes)
      (nextStore := nextStore)
      (initialWork := initialWork)
      (inp₀ := inp₀)
      (out₀ := out₀)
      (hinput := hinput)
      (houtput := houtput)
      hrewoundSource hrewoundParked
  let prefixTape := instructionCleanupPrefixTape nextBits
  let copiedWork := Function.update
    (Function.update rewoundWork tapes.buffer prefixTape)
    tapes.liftedSource prefixTape
  obtain ⟨hresetBufferPhase, hrewindSource, hsourceReadyOutside,
      hsourceReadyParked, hbufferResetParked⟩ :=
    bufferedCleanup_restoreSourcePhase
      (tapes := tapes)
      (nextStore := nextStore)
      (initialWork := initialWork)
      (inp₀ := inp₀)
      (out₀ := out₀)
      (hinput := hinput)
      (houtput := houtput)
      hcopiedBuffer hcopiedSource hcopiedParked hresetParked
  let bufferResetWork := Function.update copiedWork tapes.buffer
    ((Tape.init []).move Dir3.right)
  let sourceReadyWork := Function.update bufferResetWork tapes.liftedSource
    nextTape
  have hcountCopy :=
    bufferedCleanup_copyCountPhase
      (tapes := tapes)
      (oldStore := oldStore)
      (nextStore := nextStore)
      (nextPC := nextPC)
      (cleanupValues := cleanupValues)
      (remainingValue := remainingValue)
      (sourceHeadBound := sourceHeadBound)
      (initialWork := initialWork)
      (inp₀ := inp₀)
      (out₀ := out₀)
      (hready := hready)
      (hinput := hinput)
      (houtput := houtput)
      hsourceReadyOutside hresetDataOutside hresetTarget hsourceReadyParked
  let countTape :=
    (Tape.init (nextStore.length.bits.map Γ.ofBool)).move Dir3.right
  let finalWork := Function.update sourceReadyWork
    tapes.lifted.data.update.remaining countTape
  obtain ⟨hfinalPreservedData, hfinalReset, hblankNat, hfinalSource, hfinalBuffer, hfinalParked⟩ :=
    bufferedCleanup_finalFrame
      (tapes := tapes)
      (nextStore := nextStore)
      (initialWork := initialWork)
      hsourceReadyOutside hresetDataOutside hresetTarget hsourceReadyParked
  have hfinalScanner :=
    bufferedCleanup_finalScanner
      (tapes := tapes)
      (oldStore := oldStore)
      (nextStore := nextStore)
      (nextPC := nextPC)
      (cleanupValues := cleanupValues)
      (remainingValue := remainingValue)
      (sourceHeadBound := sourceHeadBound)
      (initialWork := initialWork)
      (hready := hready)
      hfinalSource hfinalPreservedData hfinalReset hblankNat hfinalParked
  obtain ⟨hfinalPC, hfinalLookupScanner⟩ :=
    bufferedCleanup_finalLookup
      (tapes := tapes)
      (nextStore := nextStore)
      (initialWork := initialWork)
      hsourceReadyOutside hfinalScanner hfinalParked
  have hfinalReady :=
    bufferedCleanup_finalReady
      (tapes := tapes)
      (oldStore := oldStore)
      (nextStore := nextStore)
      (nextPC := nextPC)
      (cleanupValues := cleanupValues)
      (remainingValue := remainingValue)
      (sourceHeadBound := sourceHeadBound)
      (initialWork := initialWork)
      (hready := hready)
      hfinalLookupScanner hfinalSource hfinalPreservedData hfinalReset
      hblankNat hfinalPC hfinalBuffer
  have hcountFinal :
      (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
        tapes.lifted.data.update.remaining
        tapes.lifted.data.update.found).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = sourceReadyWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionReady tapes nextStore nextPC work ∧
        out = out₀)
      (TM.binaryCopyTime nextStore.length 0) :=
    hcountCopy.strengthen_post (by
      rintro inp work out ⟨hinp, hwork, hout⟩
      subst work
      exact ⟨hinp, hfinalReady, hout⟩)
  have hseam (work₀ : Fin (n + 1) → Tape)
      (hwork₀ : ∀ i, TM.Parked (work₀ i)) :
      ∀ inp work out,
        (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
        TM.transitionInput inp = inp₀ ∧
        (fun i => TM.transitionTape (work i)) = work₀ ∧
        TM.transitionTape out = out₀ := by
    rintro inp work out ⟨hinp, hwork, hout⟩
    have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
    have houtParked : TM.Parked out := by simpa [hout] using houtput
    have hworkParked : ∀ i, TM.Parked (work i) := by
      simpa [hwork] using hwork₀
    obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked hinpParked
      hworkParked houtParked
    rw [hi, hw, ho]
    exact ⟨hinp, hwork, hout⟩
  have htail₀ := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.liftedSource)
    (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
      tapes.lifted.data.update.remaining tapes.lifted.data.update.found)
    hrewindSource (hseam sourceReadyWork hsourceReadyParked) hcountFinal
  have htail₁ := TM.seqTM_hoareTime
    (TM.resetBinaryWorkTM tapes.buffer)
    (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
      (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
        tapes.lifted.data.update.remaining tapes.lifted.data.update.found))
    hresetBufferPhase (hseam bufferResetWork hbufferResetParked) htail₀
  have htail₂ := TM.seqTM_hoareTime
    (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
    (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
      (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
        (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
          tapes.lifted.data.update.remaining tapes.lifted.data.update.found)))
    hcopy (hseam copiedWork hcopiedParked) htail₁
  have htail₃ := TM.seqTM_hoareTime
    (TM.rewindWorkTM tapes.buffer)
    (TM.seqTM (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
      (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
        (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
          (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
            tapes.lifted.data.update.remaining tapes.lifted.data.update.found))))
    hrewind (hseam rewoundWork hrewoundParked) htail₂
  have hall := TM.seqTM_hoareTime
    (TM.resetBinaryWorkManyTM targets)
    (TM.seqTM (TM.rewindWorkTM tapes.buffer)
      (TM.seqTM (TM.copyWorkToWorkTM tapes.buffer tapes.liftedSource)
        (TM.seqTM (TM.resetBinaryWorkTM tapes.buffer)
          (TM.seqTM (TM.rewindWorkTM tapes.liftedSource)
            (TM.binaryCopyIntoTM tapes.lifted.data.update.resultCount
              tapes.lifted.data.update.remaining
              tapes.lifted.data.update.found)))))
    hreset (hseam resetWork hresetParked) htail₃
  simpa only [instructionCleanupTM, bufferedCleanupTime,
    nextBits, targets, resetBits, resetHeads] using hall

/-- The ordinary sparse instruction endpoint is an instance of generic
buffered cleanup. -/
theorem instructionCleanupTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (instruction : Instr)
    (pcValue : ℕ) (store : Store) (sourceHeadBound : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ out₀ : Tape)
    (hready : InstructionCleanupReady tapes instruction pcValue store
      sourceHeadBound initialWork)
    (hinput : TM.Parked inp₀) (houtput : TM.Parked out₀) :
    (instructionCleanupTM tapes).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionReady tapes
          (instructionStore instruction pcValue store)
          (instructionPC instruction pcValue store) work ∧
        out = out₀)
      (instructionCleanupTime tapes instruction pcValue store
        sourceHeadBound) := by
  let nextStore := instructionStore instruction pcValue store
  let nextPC := instructionPC instruction pcValue store
  let cleanupValues := instructionCleanupValue instruction store
  let remainingValue := instructionRemainingValue instruction store
  have hgenericReady : BufferedCleanupReady tapes store nextStore nextPC
      cleanupValues remainingValue sourceHeadBound initialWork :=
    { nextCanonical := by
        simpa [nextStore, instructionStore] using
          Snapshot.stepInstr_canonical instruction
            { pc := pcValue, store := store } hready.canonical
      result :=
        { buffer := hready.result.buffer
          pc := hready.result.pc
          resultCount := hready.result.resultCount
          sourceContent := hready.result.sourceContent
          cleanup := hready.result.cleanup
          remaining := hready.result.remaining
          scanner := hready.result.scanner
          shift := hready.result.shift
          tmp := hready.result.tmp
          dbl := hready.result.dbl
          parked := hready.result.parked }
      sourceStart := hready.sourceStart
      bufferStart := hready.bufferStart
      sourceHead := hready.sourceHead }
  have hgeneric := bufferedCleanupTM_hoareTime_frame_internal tapes store
    nextStore nextPC cleanupValues remainingValue sourceHeadBound initialWork
    inp₀ out₀ hgenericReady hinput houtput
  simpa only [nextStore, nextPC, cleanupValues, remainingValue,
    instructionCleanupTime, bufferedCleanupTime,
    instructionCleanupResetBitsAt, bufferedCleanupResetBitsAt,
    instructionCleanupResetBits, bufferedCleanupResetBits] using! hgeneric

/-- One selected instruction followed by cleanup realizes the next reusable
sparse-snapshot boundary. -/
theorem programStepTM_hoareTime_frame_internal
    (tapes : ControlInstructionTapes n) (program : Program)
    (store : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape) (inp₀ : Tape)
    (hready : InstructionExecutionReady tapes store pcValue initialWork)
    (hinput : TM.Parked inp₀)
    (hprogram : (programInstructionTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionResult tapes
          (selectedInstruction program pcValue) pcValue store work ∧
        out = (Tape.init []).move Dir3.right)
      (programInstructionTime tapes program pcValue store)) :
    (programStepTM tapes program).HoareTime
      (fun inp work out =>
        inp = inp₀ ∧ work = initialWork ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        inp = inp₀ ∧
        InstructionExecutionReady tapes
          (instructionStore (selectedInstruction program pcValue)
            pcValue store)
          (instructionPC (selectedInstruction program pcValue)
            pcValue store) work ∧
        out = (Tape.init []).move Dir3.right)
      (programStepTime tapes program pcValue store) := by
  let instruction := selectedInstruction program pcValue
  let sourceBound :=
    programStepSourceHeadBound tapes program pcValue store
  let blank := (Tape.init []).move Dir3.right
  have hprogramCleanup :
      (programInstructionTM tapes program).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧ work = initialWork ∧ out = blank)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionCleanupReady tapes instruction pcValue store
            sourceBound work ∧
          out = blank)
        (programInstructionTime tapes program pcValue store) := by
    intro inp work out hpre
    obtain ⟨c, time, htime, hreach, hhalt, hinp, hresult, hout⟩ :=
      hprogram inp work out hpre
    have hsourceStart₀ :
        (work tapes.liftedSource).cells 0 = Γ.start := by
      simpa [hpre.2.1] using! hready.control.lookup.sourceStart
    have hsourceStart := TM.work_cells_zero_eq_start_of_reachesIn
      tapes.liftedSource hreach hsourceStart₀
    have hbufferStart₀ :
        (work tapes.buffer).cells 0 = Γ.start := by
      rw [hpre.2.1, hready.buffer]
      simp [Tape.move, Tape.init]
    have hbufferStart := TM.work_cells_zero_eq_start_of_reachesIn
      tapes.buffer hreach hbufferStart₀
    have hsourceHead :=
      (programInstructionTM tapes program).work_head_reachesIn_bound
        hreach tapes.liftedSource
    refine ⟨c, time, htime, hreach, hhalt, hinp, ?_, hout⟩
    refine
      { canonical := hready.canonical
        result := by simpa only [instruction] using hresult
        sourceStart := hsourceStart
        bufferStart := hbufferStart
        sourceHead := ?_ }
    have hsourceHead₀ : (work tapes.liftedSource).head = 1 := by
      simpa [hpre.2.1] using! hready.control.lookup.sourceHead
    rw [hsourceHead₀] at hsourceHead
    simp only [sourceBound, programStepSourceHeadBound]
    omega
  have hcleanup :
      (instructionCleanupTM tapes).HoareTime
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionCleanupReady tapes instruction pcValue store
            sourceBound work ∧
          out = blank)
        (fun inp work out =>
          inp = inp₀ ∧
          InstructionExecutionReady tapes
            (instructionStore instruction pcValue store)
            (instructionPC instruction pcValue store) work ∧
          out = blank)
        (instructionCleanupTime tapes instruction pcValue store
          sourceBound) := by
    intro inp work out hpre
    have hcleanupWork := instructionCleanupTM_hoareTime_frame_internal
      tapes instruction pcValue store sourceBound work inp₀ blank
      hpre.2.1 hinput blank_parked
    exact hcleanupWork inp work out ⟨hpre.1, rfl, hpre.2.2⟩
  have hseq := TM.seqTM_hoareTime
    (programInstructionTM tapes program) (instructionCleanupTM tapes)
    hprogramCleanup
    (by
      rintro inp work out ⟨hinp, hcleanupReady, hout⟩
      have hinpParked : TM.Parked inp := by simpa [hinp] using hinput
      have houtParked : TM.Parked out := by simpa [hout, blank] using blank_parked
      obtain ⟨hi, hw, ho⟩ := phaseTransition_of_parked hinpParked
        hcleanupReady.result.parked houtParked
      rw [hi, hw, ho]
      exact ⟨hinp, hcleanupReady, hout⟩)
    hcleanup
  simpa only [programStepTM, programStepTime, instruction, sourceBound,
    blank] using hseq

end Machine

end RegisterStore

end RAM

end Complexity
