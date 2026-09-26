/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordEncode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Self-delimiting word emission — proof internals
-/


@[expose] public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private def workEmitBit (mode : WorkEmitMode) (bit : Bool) : Bool :=
  match mode with
  | .width => true
  | .payload => bit

private theorem workEmitBits_cons (mode : WorkEmitMode)
    (bit : Bool) (bits : List Bool) :
    workEmitBits mode (bit :: bits) =
      workEmitBit mode bit :: workEmitBits mode bits := by
  cases mode <;> simp [workEmitBits, workEmitBit, List.replicate_succ]

private theorem parked_of_binarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : TM.Parked t :=
  ⟨h.1, h.2.2.2⟩

private theorem parked_of_binaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) : TM.Parked t :=
  ⟨by rw [h.1]; omega,
    (show t.HasBinaryContent bits from h.2).cells_ne_start⟩

private theorem cells_eq_init_of_binaryContent {t : Tape} {bits : List Bool}
    (h : t.HasBinaryContent bits) (hstart : t.cells 0 = Γ.start) :
    t.cells = (Tape.init (bits.map Γ.ofBool)).cells := by
  let parked : Tape := { head := bits.length + 1, cells := t.cells }
  have hprefix : parked.HasBinaryPrefix bits := ⟨rfl, h⟩
  simpa [parked] using hprefix.cells_eq_init hstart

theorem workEmitTM_reachesIn_frame_internal
    (idx : Fin n) (mode : WorkEmitMode) :
    ∀ (bits emitted : List Bool)
      (c : Complexity.Cfg n (workEmitTM idx mode).Q),
      c.state = WorkEmitPhase.scan →
      (c.work idx).HasBinarySuffix bits →
      TM.Parked c.input →
      (∀ i, i ≠ idx → TM.Parked (c.work i)) →
      c.output.HasBinaryPrefix emitted →
      ∃ c',
        (workEmitTM idx mode).reachesIn (workEmitTime bits) c c' ∧
        (workEmitTM idx mode).halted c' ∧
        c'.input = c.input ∧
        (c'.work idx).HasBinarySuffix [] ∧
        (c'.work idx).cells = (c.work idx).cells ∧
        (c'.work idx).head = (c.work idx).head + bits.length ∧
        (∀ i, i ≠ idx → c'.work i = c.work i) ∧
        c'.output.HasBinaryPrefix (emitted ++ workEmitBits mode bits) := by
  intro bits
  induction bits with
  | nil =>
      intro emitted c hstate hsource hinput hother houtput
      have hsourceRead : (c.work idx).read = Γ.blank := hsource.read_nil
      cases mode with
      | width =>
          let c' : Complexity.Cfg n (workEmitTM idx .width).Q :=
            { state := WorkEmitPhase.done
              input := TM.transitionInput c.input
              work := fun i => TM.transitionTape (c.work i)
              output := c.output.writeAndMove Γ.zero Dir3.right }
          have hstep : (workEmitTM idx .width).step c = some c' := by
            simp [TM.step, hstate, workEmitTM, hsourceRead, c',
              TM.transitionInput, TM.transitionTape]
          have hinputKeep : c'.input = c.input := by
            simpa [c'] using TM.transitionInput_eq_self hinput.read_ne_start
          have hsourceKeep : c'.work idx = c.work idx := by
            simpa [c'] using TM.transitionTape_eq_self (by
              rw [hsourceRead]
              decide)
          have hotherKeep (i) (hi : i ≠ idx) : c'.work i = c.work i := by
            simpa [c'] using TM.transitionTape_eq_self (hother i hi).read_ne_start
          have houtput' :
              c'.output.HasBinaryPrefix (emitted ++ [false]) := by
            simpa [c'] using! Tape.hasBinaryPrefix_write_bit false houtput
          refine ⟨c', .step hstep .zero, rfl, hinputKeep, ?_, ?_, ?_,
            hotherKeep, ?_⟩
          · rw [hsourceKeep]
            exact hsource
          · rw [hsourceKeep]
          · rw [hsourceKeep]
            simp
          · simpa [workEmitBits] using houtput'
      | payload =>
          let c' : Complexity.Cfg n (workEmitTM idx .payload).Q :=
            { state := WorkEmitPhase.done
              input := TM.transitionInput c.input
              work := fun i => TM.transitionTape (c.work i)
              output := TM.transitionTape c.output }
          have hstep : (workEmitTM idx .payload).step c = some c' := by
            simp [TM.step, hstate, workEmitTM, hsourceRead, c',
              TM.allReadBack, TM.transitionInput, TM.transitionTape]
          have hinputKeep : c'.input = c.input := by
            simpa [c'] using TM.transitionInput_eq_self hinput.read_ne_start
          have hsourceKeep : c'.work idx = c.work idx := by
            simpa [c'] using TM.transitionTape_eq_self (by
              rw [hsourceRead]
              decide)
          have hotherKeep (i) (hi : i ≠ idx) : c'.work i = c.work i := by
            simpa [c'] using TM.transitionTape_eq_self (hother i hi).read_ne_start
          have houtputKeep : c'.output = c.output := by
            simpa [c'] using TM.transitionTape_eq_self (by
              rw [houtput.read_blank]
              decide)
          refine ⟨c', .step hstep .zero, rfl, hinputKeep, ?_, ?_, ?_,
            hotherKeep, ?_⟩
          · rw [hsourceKeep]
            exact hsource
          · rw [hsourceKeep]
          · rw [hsourceKeep]
            simp
          · rw [houtputKeep]
            simpa [workEmitBits]
  | cons bit bits ih =>
      intro emitted c hstate hsource hinput hother houtput
      have hsourceRead : (c.work idx).read = Γ.ofBool bit :=
        hsource.read_cons
      let c₁ : Complexity.Cfg n (workEmitTM idx mode).Q :=
        { state := WorkEmitPhase.scan
          input := TM.transitionInput c.input
          work := fun i =>
            (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
              (if i = idx then Dir3.right else TM.idleDir (c.work i).read)
          output := c.output.writeAndMove
            (Γ.ofBool (workEmitBit mode bit)) Dir3.right }
      have hstep : (workEmitTM idx mode).step c = some c₁ := by
        cases mode <;> cases bit <;>
          simp [TM.step, hstate, workEmitTM, hsourceRead, c₁,
            TM.transitionInput, workEmitBit, Γ.ofBool]
      have hinputKeep : c₁.input = c.input := by
        simpa [c₁] using TM.transitionInput_eq_self hinput.read_ne_start
      have hsourceMove : c₁.work idx = (c.work idx).move Dir3.right := by
        rw [show c₁.work idx =
          (c.work idx).writeAndMove (TM.readBackWrite (c.work idx).read)
            Dir3.right by simp [c₁]]
        exact TM.writeAndMove_readBack _ hsource.read_ne_start Dir3.right
      have hotherKeep (i) (hi : i ≠ idx) : c₁.work i = c.work i := by
        have htransition : c₁.work i = TM.transitionTape (c.work i) := by
          simp [c₁, hi, TM.transitionTape]
        rw [htransition]
        exact TM.transitionTape_eq_self (hother i hi).read_ne_start
      have hsource₁ : (c₁.work idx).HasBinarySuffix bits := by
        rw [hsourceMove]
        exact hsource.move_right_cons
      have houtput₁ : c₁.output.HasBinaryPrefix
          (emitted ++ [workEmitBit mode bit]) := by
        simpa [c₁] using Tape.hasBinaryPrefix_write_bit
          (workEmitBit mode bit) houtput
      obtain ⟨c', hreach, hhalt, hinput', hsource', hsourceCells,
          hsourceHead, hother', houtput'⟩ :=
        ih (emitted ++ [workEmitBit mode bit]) c₁ rfl hsource₁
          (hinputKeep ▸ hinput)
          (fun i hi => hotherKeep i hi ▸ hother i hi) houtput₁
      refine ⟨c', ?_, hhalt, hinput'.trans hinputKeep, hsource', ?_, ?_,
        ?_, ?_⟩
      · simpa [workEmitTime] using TM.reachesIn.step hstep hreach
      · rw [hsourceCells, hsourceMove, Tape.move_cells]
      · rw [hsourceHead, hsourceMove]
        simp [Tape.move]
        omega
      · intro i hi
        exact (hother' i hi).trans (hotherKeep i hi)
      · rw [workEmitBits_cons]
        simpa [List.append_assoc] using houtput'

theorem workEmitTM_hoareTime_frame_internal
    (idx : Fin n) (mode : WorkEmitMode) (bits emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ idx).HasBinarySuffix bits)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (workEmitTM idx mode).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = (work₀ idx).head + bits.length ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ workEmitBits mode bits))
      (workEmitTime bits) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  obtain ⟨c', hreach, hhalt, hinput', hsource', hcells, hhead,
      hframe, houtput'⟩ :=
    workEmitTM_reachesIn_frame_internal idx mode bits emitted
      { state := WorkEmitPhase.scan
        input := inp₀
        work := work₀
        output := out₀ }
      rfl hsource hinput hother houtput
  exact ⟨c', workEmitTime bits, le_rfl, hreach, hhalt, hinput',
    hsource', hcells, hhead, hframe, houtput'⟩

theorem wordEncodeTM_hoareTime_frame_internal
    (idx : Fin n) (value : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (wordEncodeTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = value.bits.length + 1 ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ WordCode.encode value))
      (wordEncodeTime value) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hwidthContract := workEmitTM_hoareTime_frame_internal idx .width
    value.bits emitted inp₀ work₀ out₀ hvalue.2.hasBinarySuffix hinput
    hother houtput
  obtain ⟨widthDone, widthTime, hwidthTime, hwidthReach, hwidthHalt,
      hwidthInput, hwidthSuffix, hwidthCells, hwidthHead,
      hwidthFrame, hwidthOutput⟩ :=
    hwidthContract inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have hwidthSourceParked : TM.Parked (widthDone.work idx) :=
    parked_of_binarySuffix hwidthSuffix
  have hwidthWorkParked : ∀ i, TM.Parked (widthDone.work i) := by
    intro i
    by_cases hi : i = idx
    · subst i
      exact hwidthSourceParked
    · rw [hwidthFrame i hi]
      exact hother i hi
  have hwidthOutputParked : TM.Parked widthDone.output :=
    parked_of_binaryPrefix hwidthOutput
  obtain ⟨hwidthInputTransition, hwidthWorkTransition,
      hwidthOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      (hwidthInput ▸ hinput.read_ne_start)
      (fun i => (hwidthWorkParked i).read_ne_start)
      hwidthOutputParked.read_ne_start
  have hwidthContent :
      (widthDone.work idx).HasBinaryContent value.bits := by
    simpa only [Tape.HasBinaryContent, hwidthCells] using
      hvalue.2.hasBinaryContent
  have hwidthStart : (widthDone.work idx).cells 0 = Γ.start := by
    rw [hwidthCells]
    exact hvalue.1
  have hwidthHeadBound :
      1 ≤ (widthDone.work idx).head ∧
        (widthDone.work idx).head ≤ value.bits.length + 1 := by
    rw [hwidthHead, hvalue.2.1]
    omega
  have hrewindContract := TM.rewindBinaryWorkTM_hoareTime_frame idx
    value.bits (value.bits.length + 1) widthDone.input widthDone.work
    widthDone.output hwidthContent hwidthStart hwidthHeadBound
    (hwidthInput ▸ hinput) (fun i hi => hwidthWorkParked i)
    hwidthOutputParked
  obtain ⟨rewindDone, rewindTime, hrewindTime, hrewindReach,
      hrewindHalt, hrewindInput, hrewindTarget, hrewindFrame,
      hrewindOutput⟩ :=
    hrewindContract widthDone.input widthDone.work widthDone.output
      ⟨rfl, rfl, rfl⟩
  have hrewindSourceString :
      (rewindDone.work idx).HasBinaryString value.bits := by
    rw [hrewindTarget]
    exact Tape.init_move_right_hasBinaryString value.bits
  have hrewindWorkParked : ∀ i, TM.Parked (rewindDone.work i) := by
    intro i
    by_cases hi : i = idx
    · subst i
      exact ⟨by rw [hrewindSourceString.1],
        hrewindSourceString.hasBinaryContent.cells_ne_start⟩
    · rw [hrewindFrame i hi]
      exact hwidthWorkParked i
  have hrewindOutputPrefix : rewindDone.output.HasBinaryPrefix
      (emitted ++ workEmitBits .width value.bits) := by
    rw [hrewindOutput]
    exact hwidthOutput
  have hrewindOutputParked : TM.Parked rewindDone.output :=
    parked_of_binaryPrefix hrewindOutputPrefix
  have hrewindInputParked : TM.Parked rewindDone.input := by
    rw [hrewindInput, hwidthInput]
    exact hinput
  obtain ⟨hrewindInputTransition, hrewindWorkTransition,
      hrewindOutputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hrewindInputParked.read_ne_start
      (fun i => (hrewindWorkParked i).read_ne_start)
      hrewindOutputParked.read_ne_start
  have hpayloadContract := workEmitTM_hoareTime_frame_internal idx .payload
    value.bits (emitted ++ workEmitBits .width value.bits)
    rewindDone.input rewindDone.work rewindDone.output
    hrewindSourceString.hasBinarySuffix
    (by rw [hrewindInput, hwidthInput]; exact hinput)
    (fun i hi => hrewindWorkParked i) hrewindOutputPrefix
  obtain ⟨payloadDone, payloadTime, hpayloadTime, hpayloadReach,
      hpayloadHalt, hpayloadInput, hpayloadSuffix, hpayloadCells,
      hpayloadHead, hpayloadFrame, hpayloadOutput⟩ :=
    hpayloadContract rewindDone.input rewindDone.work rewindDone.output
      ⟨rfl, rfl, rfl⟩
  have hpayloadReach' : (workEmitTM idx .payload).reachesIn payloadTime
      { state := (workEmitTM idx .payload).qstart
        input := TM.transitionInput rewindDone.input
        work := fun i => TM.transitionTape (rewindDone.work i)
        output := TM.transitionTape rewindDone.output }
      payloadDone := by
    simpa [hrewindInputTransition, hrewindWorkTransition,
      hrewindOutputTransition] using hpayloadReach
  have hrestReach := TM.seqTM_reachesIn_of_reachesIn
    (TM.rewindWorkTM idx) (workEmitTM idx .payload)
    hrewindReach hrewindHalt hpayloadReach'
  have hrestReach' :
      (TM.seqTM (TM.rewindWorkTM idx) (workEmitTM idx .payload)).reachesIn
        (rewindTime + 1 + payloadTime)
        { state :=
            (TM.seqTM (TM.rewindWorkTM idx)
              (workEmitTM idx .payload)).qstart
          input := TM.transitionInput widthDone.input
          work := fun i => TM.transitionTape (widthDone.work i)
          output := TM.transitionTape widthDone.output }
        (TM.phase2Wrap (TM.rewindWorkTM idx)
          (workEmitTM idx .payload) payloadDone) := by
    simpa [hwidthInputTransition, hwidthWorkTransition,
      hwidthOutputTransition] using! hrestReach
  have hfullReach := TM.seqTM_reachesIn_of_reachesIn
    (workEmitTM idx .width)
    (TM.seqTM (TM.rewindWorkTM idx) (workEmitTM idx .payload))
    hwidthReach hwidthHalt hrestReach'
  let finalCfg := TM.phase2Wrap (workEmitTM idx .width)
    (TM.seqTM (TM.rewindWorkTM idx) (workEmitTM idx .payload))
    (TM.phase2Wrap (TM.rewindWorkTM idx)
      (workEmitTM idx .payload) payloadDone)
  refine ⟨finalCfg,
    widthTime + 1 + (rewindTime + 1 + payloadTime), ?_, ?_, ?_, ?_⟩
  · unfold wordEncodeTime workEmitTime at *
    omega
  · exact hfullReach
  · change
      (TM.seqTM (workEmitTM idx .width)
        (TM.seqTM (TM.rewindWorkTM idx)
          (workEmitTM idx .payload))).halted finalCfg
    exact (TM.phase2Wrap_halted_iff (workEmitTM idx .width)
      (TM.seqTM (TM.rewindWorkTM idx) (workEmitTM idx .payload)) _).mpr
      ((TM.phase2Wrap_halted_iff (TM.rewindWorkTM idx)
        (workEmitTM idx .payload) payloadDone).mpr hpayloadHalt)
  · refine ⟨?_, hpayloadSuffix, ?_, ?_, ?_, ?_⟩
    · simpa [finalCfg] using!
        hpayloadInput.trans (hrewindInput.trans hwidthInput)
    · have hcanonical :=
        Tape.eq_init_move_right_of_hasBinaryString hvalue.2 hvalue.1
      change (payloadDone.work idx).cells = (work₀ idx).cells
      rw [hpayloadCells, hrewindTarget]
      exact congrArg Tape.cells hcanonical.symm
    · have hrewindHead : (rewindDone.work idx).head = 1 := by
        rw [hrewindTarget]
        simp [Tape.move]
      simpa [finalCfg, hrewindHead, Nat.add_comm] using! hpayloadHead
    · intro i hi
      simpa [finalCfg] using!
        (hpayloadFrame i hi).trans
          ((hrewindFrame i hi).trans (hwidthFrame i hi))
    · simpa [finalCfg, WordCode.encode, workEmitBits, bitlen,
        Nat.toBitsLE_size, Nat.size_eq_bits_len, List.append_assoc] using!
        hpayloadOutput

theorem rewindWordEncodeTM_hoareTime_frame_internal
    (idx : Fin n) (value headBound : ℕ) (emitted : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcontent : (work₀ idx).HasBinaryContent value.bits)
    (hstart : (work₀ idx).cells 0 = Γ.start)
    (hhead : 1 ≤ (work₀ idx).head ∧ (work₀ idx).head ≤ headBound)
    (hinput : TM.Parked inp₀)
    (hother : ∀ i, i ≠ idx → TM.Parked (work₀ i))
    (houtput : out₀.HasBinaryPrefix emitted) :
    (rewindWordEncodeTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work idx).HasBinarySuffix [] ∧
        (work idx).cells = (work₀ idx).cells ∧
        (work idx).head = value.bits.length + 1 ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        out.HasBinaryPrefix (emitted ++ WordCode.encode value))
      (rewindWordEncodeTime value headBound) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hwork, hout⟩
  subst inp
  subst work
  subst out
  have hrewindContract := TM.rewindBinaryWorkTM_hoareTime_frame idx
    value.bits headBound inp₀ work₀ out₀ hcontent hstart hhead hinput
    hother (parked_of_binaryPrefix houtput)
  obtain ⟨rewindDone, rewindTime, hrewindTime, hrewindReach,
      hrewindHalt, hrewindInput, hrewindTarget, hrewindFrame,
      hrewindOutput⟩ :=
    hrewindContract inp₀ work₀ out₀ ⟨rfl, rfl, rfl⟩
  have hrewindString :
      (rewindDone.work idx).HasBinaryString value.bits := by
    rw [hrewindTarget]
    exact Tape.init_move_right_hasBinaryString value.bits
  have hrewindWorkParked : ∀ i, TM.Parked (rewindDone.work i) := by
    intro i
    by_cases hi : i = idx
    · subst i
      exact ⟨by rw [hrewindString.1],
        hrewindString.hasBinaryContent.cells_ne_start⟩
    · rw [hrewindFrame i hi]
      exact hother i hi
  have hrewindOutputPrefix : rewindDone.output.HasBinaryPrefix emitted := by
    rw [hrewindOutput]
    exact houtput
  have hrewindInputParked : TM.Parked rewindDone.input := by
    rw [hrewindInput]
    exact hinput
  obtain ⟨hinputTransition, hworkTransition, houtputTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start
      hrewindInputParked.read_ne_start
      (fun i => (hrewindWorkParked i).read_ne_start)
      (parked_of_binaryPrefix hrewindOutputPrefix).read_ne_start
  have hencodeContract := wordEncodeTM_hoareTime_frame_internal idx value emitted
    rewindDone.input rewindDone.work rewindDone.output
    ⟨by rw [hrewindTarget]; simp [Tape.init, Tape.move], hrewindString⟩
    (by rw [hrewindInput]; exact hinput)
    (fun i _ => hrewindWorkParked i) hrewindOutputPrefix
  obtain ⟨encodeDone, encodeTime, hencodeTime, hencodeReach,
      hencodeHalt, hencodeInput, hencodeSuffix, hencodeCells,
      hencodeHead, hencodeFrame, hencodeOutput⟩ :=
    hencodeContract rewindDone.input rewindDone.work rewindDone.output
      ⟨rfl, rfl, rfl⟩
  have hencodeReach' : (wordEncodeTM idx).reachesIn encodeTime
      { state := (wordEncodeTM idx).qstart
        input := TM.transitionInput rewindDone.input
        work := fun i => TM.transitionTape (rewindDone.work i)
        output := TM.transitionTape rewindDone.output }
      encodeDone := by
    simpa [hinputTransition, hworkTransition, houtputTransition] using
      hencodeReach
  have hreach := TM.seqTM_reachesIn_of_reachesIn
    (TM.rewindWorkTM idx) (wordEncodeTM idx)
    hrewindReach hrewindHalt hencodeReach'
  let finalCfg := TM.phase2Wrap (TM.rewindWorkTM idx)
    (wordEncodeTM idx) encodeDone
  refine ⟨finalCfg, rewindTime + 1 + encodeTime, ?_, hreach, ?_, ?_⟩
  · unfold rewindWordEncodeTime
    omega
  · change (rewindWordEncodeTM idx).halted finalCfg
    unfold rewindWordEncodeTM
    rw [TM.phase2Wrap_halted_iff]
    exact hencodeHalt
  · refine ⟨?_, hencodeSuffix, ?_, ?_, ?_, ?_⟩
    · simpa [finalCfg] using! hencodeInput.trans hrewindInput
    · change (encodeDone.work idx).cells = (work₀ idx).cells
      rw [hencodeCells, hrewindTarget]
      exact (cells_eq_init_of_binaryContent hcontent hstart).symm
    · simpa [finalCfg] using! hencodeHead
    · intro i hi
      change encodeDone.work i = work₀ i
      exact (hencodeFrame i hi).trans (hrewindFrame i hi)
    · simpa [finalCfg] using! hencodeOutput

end Machine

end RegisterStore

end RAM

end Complexity
