/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.DenseInputLookup.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForInput.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary

/-!
# Dense public-input lookup -- proof internals
-/


@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

theorem denseInputIdleTM_reachesIn_frame_internal {n : ℕ}
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
      c'.input = inp₀ ∧ c'.work = work₀ ∧ c'.output = out₀ := by
  let c' : Complexity.Cfg n (denseInputIdleTM (n := n)).Q :=
    { state := (denseInputIdleTM (n := n)).qhalt
      input := inp₀
      work := work₀
      output := out₀ }
  have hstep : (denseInputIdleTM (n := n)).step
      { state := (denseInputIdleTM (n := n)).qstart
        input := inp₀
        work := work₀
        output := out₀ } = some c' := by
    simp only [TM.step, denseInputIdleTM, reduceCtorEq, ↓reduceIte, c']
    refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact hinput.move_idle
    · funext i
      exact (hwork i).writeAndMove_readBack_idle
    · exact houtput.writeAndMove_readBack_idle
  exact ⟨c', .step hstep .zero, rfl, rfl, rfl, rfl⟩

theorem capturePreviousInputBitTM_reachesIn_frame_internal {n : ℕ}
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
      c'.output = out₀ := by
  have hinputRead : inp₀.read ≠ Γ.start :=
    hinput.read_ne_start (by omega)
  let inp₁ := inp₀.move Dir3.left
  have hinp₁Head : inp₁.head = inp₀.head - 1 := by
    simp [inp₁, Tape.move]
  have hinp₁Cells : inp₁.cells = inp₀.cells := Tape.move_cells _ _
  have hinp₁Read : inp₁.read = Γ.ofBool bit := by
    simp only [Tape.read, hinp₁Head, hinp₁Cells, hbit]
  let c₁ : Complexity.Cfg n (capturePreviousInputBitTM result).Q :=
    { state := .write, input := inp₁, work := work₀, output := out₀ }
  have hstep₁ : (capturePreviousInputBitTM result).step
      { state := (capturePreviousInputBitTM result).qstart
        input := inp₀
        work := work₀
        output := out₀ } = some c₁ := by
    simp only [TM.step, capturePreviousInputBitTM, reduceCtorEq,
      ↓reduceIte, c₁]
    refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · simp [inp₁, TM.moveLeftDir, hinputRead]
    · funext i
      exact (hwork i).writeAndMove_readBack_idle
    · exact houtput.writeAndMove_readBack_idle
  let finalWork := Function.update work₀ result (denseInputBitTape bit)
  let c₂ : Complexity.Cfg n (capturePreviousInputBitTM result).Q :=
    { state := .done, input := inp₀, work := finalWork, output := out₀ }
  have hstep₂ : (capturePreviousInputBitTM result).step c₁ = some c₂ := by
    simp only [TM.step, capturePreviousInputBitTM, reduceCtorEq,
      ↓reduceIte, c₁, c₂]
    refine congrArg some ((Complexity.Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · apply Tape.ext
      · simp [inp₁, Tape.move]
        omega
      · simp [inp₁, Tape.move_cells]
    · funext i
      by_cases hi : i = result
      · subst i
        simp only [finalWork, Function.update_self, hinp₁Read]
        rw [hresult]
        cases bit <;>
          simp [denseInputBitTape, TM.resetBinaryBlank, Tape.writeAndMove,
            Tape.write, Tape.move, TM.idleDir, Tape.read, Tape.init,
            Γ.ofBool]
      · simp only [finalWork, Function.update_of_ne hi, hi, ite_false]
        exact (hwork i).writeAndMove_readBack_idle
    · exact houtput.writeAndMove_readBack_idle
  exact ⟨c₂, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, rfl, rfl⟩

theorem denseInputBitTape_hasBinaryNat_internal (bit : Bool) :
    (denseInputBitTape bit).HasBinaryNat (if bit then 1 else 0) := by
  have heq : denseInputBitTape bit =
      (Tape.init ((if bit then 1 else 0).bits.map Γ.ofBool)).move
        Dir3.right := by
    cases bit with
    | false =>
        apply Tape.ext
        · simp [denseInputBitTape, TM.resetBinaryBlank,
            Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Nat.bits]
        · funext i
          by_cases hi0 : i = 0
          · subst i
            simp [denseInputBitTape, TM.resetBinaryBlank,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Nat.bits]
          · by_cases hi1 : i = 1
            · subst i
              simp [denseInputBitTape, TM.resetBinaryBlank,
                Tape.writeAndMove, Tape.write, Tape.move, Tape.init,
                Nat.bits]
            · simp [denseInputBitTape, TM.resetBinaryBlank,
                Tape.writeAndMove, Tape.write, Tape.move, Tape.init,
                Nat.bits, hi0, hi1]
    | true =>
        apply Tape.ext
        · simp [denseInputBitTape, TM.resetBinaryBlank,
            Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Nat.bits]
        · funext i
          by_cases hi0 : i = 0
          · subst i
            simp [denseInputBitTape, TM.resetBinaryBlank,
              Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Nat.bits]
          · by_cases hi1 : i = 1
            · subst i
              simp [denseInputBitTape, TM.resetBinaryBlank,
                Tape.writeAndMove, Tape.write, Tape.move, Tape.init,
                Nat.bits, Γ.ofBool]
            · have hnone : [Γ.one][i - 1]? = none := by
                apply List.getElem?_eq_none
                simp
                omega
              simp [denseInputBitTape, TM.resetBinaryBlank,
                Tape.writeAndMove, Tape.write, Tape.move, Tape.init,
                Nat.bits, hi0, hi1, hnone, Γ.ofBool]
  rw [heq]
  exact Tape.init_move_right_hasBinaryNat _

theorem denseInputBitTape_parked_internal (bit : Bool) :
    TM.Parked (denseInputBitTape bit) := by
  have h := denseInputBitTape_hasBinaryNat_internal bit
  exact ⟨by simp [Tape.HasBinaryNat, Tape.HasBinaryString] at h; omega,
    h.2.hasBinaryContent.cells_ne_start⟩

private def denseInputNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private def denseInputTape (input : List Bool) (head : ℕ) : Tape :=
  { head := head
    cells := (Tape.init (input.map Γ.ofBool)).cells }

private def denseInputResultTape (input : List Bool) (address processed : ℕ) :
    Tape :=
  if address = 0 then TM.resetBinaryBlank
  else if address ≤ processed then
    denseInputBitTape (input[address - 1]?.getD false)
  else TM.resetBinaryBlank

private def denseInputWork {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (input : List Bool) (address processed : ℕ) :
    Fin n → Tape :=
  Function.update
    (Function.update work₀ counter (denseInputNatTape (address - processed)))
    result (denseInputResultTape input address processed)

private theorem denseInputNatTape_hasBinaryNat (value : ℕ) :
    (denseInputNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem denseInputNatTape_parked (value : ℕ) :
    TM.Parked (denseInputNatTape value) := by
  have h := denseInputNatTape_hasBinaryNat value
  exact ⟨by simp [Tape.HasBinaryNat, Tape.HasBinaryString] at h; omega,
    h.2.hasBinaryContent.cells_ne_start⟩

private theorem denseInputResultTape_parked (input : List Bool)
    (address processed : ℕ) :
    TM.Parked (denseInputResultTape input address processed) := by
  unfold denseInputResultTape
  split
  · exact ⟨by simp [TM.resetBinaryBlank, Tape.move],
      by simpa [TM.resetBinaryBlank] using
        Tape.init_ofBool_move_right_cells_ne_start []⟩
  · split
    · exact denseInputBitTape_parked_internal _
    · exact ⟨by simp [TM.resetBinaryBlank, Tape.move],
        by simpa [TM.resetBinaryBlank] using
          Tape.init_ofBool_move_right_cells_ne_start []⟩

private theorem denseInputWork_counter {n : ℕ} (counter result : Fin n)
    (hne : counter ≠ result) (work₀ : Fin n → Tape)
    (input : List Bool) (address processed : ℕ) :
    denseInputWork counter result work₀ input address processed counter =
      denseInputNatTape (address - processed) := by
  simp [denseInputWork, hne]

private theorem denseInputWork_result {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (input : List Bool)
    (address processed : ℕ) :
    denseInputWork counter result work₀ input address processed result =
      denseInputResultTape input address processed := by
  simp [denseInputWork]

private theorem denseInputWork_other {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (input : List Bool) (address processed : ℕ)
    (i : Fin n) (hic : i ≠ counter) (hir : i ≠ result) :
    denseInputWork counter result work₀ input address processed i = work₀ i := by
  simp [denseInputWork, hic, hir]

private theorem denseInputWork_parked {n : ℕ} (counter result : Fin n)
    (hne : counter ≠ result) (work₀ : Fin n → Tape)
    (input : List Bool) (address processed : ℕ)
    (hwork : ∀ i, TM.Parked (work₀ i)) :
    ∀ i, TM.Parked
      (denseInputWork counter result work₀ input address processed i) := by
  intro i
  by_cases hic : i = counter
  · subst i
    rw [denseInputWork_counter counter result hne]
    exact denseInputNatTape_parked _
  · by_cases hir : i = result
    · subst i
      rw [denseInputWork_result]
      exact denseInputResultTape_parked input address processed
    · rw [denseInputWork_other counter result work₀ input address processed
        i hic hir]
      exact hwork i

private theorem denseInputTape_startInvariant (input : List Bool)
    (head : ℕ) : (denseInputTape input head).StartInvariant := by
  constructor
  · simp [denseInputTape]
  · intro j hj
    simpa [denseInputTape] using Tape.init_ofBool_cells_ne_start input j hj

private theorem denseInputTape_read_bit (input : List Bool) (processed : ℕ)
    (hprocessed : processed < input.length) :
    (denseInputTape input (processed + 1)).read =
      Γ.ofBool (input[processed]'hprocessed) := by
  exact Tape.init_ofBool_cells_lt input processed hprocessed

private theorem denseInputTape_read_blank (input : List Bool) :
    (denseInputTape input (input.length + 1)).read = Γ.blank := by
  exact Tape.init_ofBool_cells_ge input input.length le_rfl

private theorem denseInputStepResult_eq (input : List Bool)
    (address processed : ℕ) (haddress : address ≠ 0)
    (hprocessed : processed < input.length) :
    denseInputStepResult (address - processed)
        (input[processed]'hprocessed)
        (denseInputResultTape input address processed) =
      denseInputResultTape input address (processed + 1) := by
  by_cases hbefore : address ≤ processed
  · rw [denseInputStepResult, ite_eq_right (by omega)]
    unfold denseInputResultTape
    rw [ite_eq_right haddress, ite_eq_left hbefore, ite_eq_right haddress,
      ite_eq_left (le_trans hbefore (by omega))]
  · by_cases hcurrent : address = processed + 1
    · subst address
      have hremaining : processed + 1 - processed = 1 := by omega
      rw [denseInputStepResult, ite_eq_left hremaining]
      unfold denseInputResultTape
      rw [ite_eq_right haddress, ite_eq_left (le_refl (processed + 1))]
      congr 1
      have hindex : processed + 1 - 1 = processed := by omega
      rw [hindex]
      rw [List.getElem?_eq_getElem hprocessed]
      rfl
    · have hafter : processed + 1 < address := by omega
      have hremaining : address - processed ≠ 1 := by omega
      rw [denseInputStepResult, ite_eq_right hremaining]
      unfold denseInputResultTape
      rw [ite_eq_right haddress, ite_eq_right (by omega), ite_eq_right haddress,
        ite_eq_right (Nat.not_le_of_lt hafter)]

private def denseInputScanCfg {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) :
    Complexity.Cfg n (denseInputScanTM counter result).Q :=
  { state := .inl .scan
    input := denseInputTape input (processed + 1)
    work := denseInputWork counter result work₀ input address processed
    output := out₀ }

private def denseInputBodyStartCfg {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) :
    Complexity.Cfg n (denseInputStepTM counter result).Q :=
  { state := (denseInputStepTM counter result).qstart
    input := denseInputTape input (processed + 2)
    work := denseInputWork counter result work₀ input address processed
    output := out₀ }

private def denseInputBodyDoneCfg {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) :
    Complexity.Cfg n (denseInputStepTM counter result).Q :=
  { state := (denseInputStepTM counter result).qhalt
    input := denseInputTape input (processed + 2)
    work := denseInputWork counter result work₀ input address (processed + 1)
    output := out₀ }

private def denseInputDoneCfg {n : ℕ} (counter result : Fin n)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address : ℕ) : Complexity.Cfg n (denseInputScanTM counter result).Q :=
  { state := .inl .done
    input := denseInputTape input (input.length + 1)
    work := denseInputWork counter result work₀ input address input.length
    output := out₀ }

private theorem denseInputScanTM_scan_bit_step {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) (hprocessed : processed < input.length)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    (denseInputScanTM counter result).step
        (denseInputScanCfg counter result work₀ out₀ input address processed) =
      some (TM.forInputBodyWrap (denseInputStepTM counter result)
        (denseInputBodyStartCfg counter result work₀ out₀ input address
          processed)) := by
  have hread := denseInputTape_read_bit input processed hprocessed
  have hstep := TM.forInputTM_step_scan_bit_internal
    (denseInputStepTM counter result)
    (denseInputScanCfg counter result work₀ out₀ input address processed)
    rfl
    (by
      change (denseInputTape input (processed + 1)).read ≠ Γ.start
      rw [hread]
      exact Γ.ofBool_ne_start _)
    (by
      change (denseInputTape input (processed + 1)).read ≠ Γ.blank
      rw [hread]
      exact Γ.ofBool_ne_blank _)
    (fun i => (denseInputWork_parked counter result hne work₀ input
      address processed hwork i).read_ne_start)
    houtput.read_ne_start
  simpa [denseInputScanTM, denseInputScanCfg, denseInputBodyStartCfg,
    TM.forInputBodyWrap, denseInputTape, Tape.move] using hstep

private theorem denseInputScanTM_scan_blank_step {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address : ℕ) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (denseInputScanTM counter result).step
        (denseInputScanCfg counter result work₀ out₀ input address input.length) =
      some (denseInputDoneCfg counter result work₀ out₀ input address) := by
  have hstep := TM.forInputTM_step_scan_blank_internal
    (denseInputStepTM counter result)
    (denseInputScanCfg counter result work₀ out₀ input address input.length)
    rfl (denseInputTape_read_blank input)
    (fun i => (denseInputWork_parked counter result hne work₀ input
      address input.length hwork i).read_ne_start)
    houtput.read_ne_start
  simpa [denseInputScanTM, denseInputScanCfg, denseInputDoneCfg] using hstep

theorem denseInputStepTM_reachesIn_frame_internal {n : ℕ}
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
      c'.output = out₀ := by
  by_cases hzero : remaining = 0
  · subst remaining
    have hblank : (work₀ counter).read = Γ.blank :=
      hcounter.read_eq_blank_iff.mpr rfl
    obtain ⟨idleDone, hidleReach, hidleHalt, hidleInput,
        hidleWork, hidleOutput⟩ :=
      denseInputIdleTM_reachesIn_frame_internal inp₀ work₀ out₀
        ⟨by omega, hinput.2⟩ hwork houtput
    obtain ⟨done, hreach, hhalt, hdoneInput, hdoneWork, hdoneOutput⟩ :=
      TM.branchWorkBlankTM_reachesIn_blank_frame counter
        (denseInputIdleTM (n := n))
        (TM.seqTM (TM.binaryPredTM counter)
          (TM.branchWorkBlankTM counter
            (capturePreviousInputBitTM result) denseInputIdleTM))
        inp₀ work₀ out₀ hblank
        (hinput.read_ne_start (by omega))
        (fun i => (hwork i).read_ne_start) houtput.read_ne_start
        hidleReach hidleHalt
    refine ⟨done, ?_, hhalt, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [denseInputStepTM, denseInputStepTime]
    · exact hdoneInput.trans hidleInput
    · rw [hdoneWork, hidleWork]
      simpa using hcounter
    · rw [hdoneWork, hidleWork]
      simp [denseInputStepResult]
    · intro i _ _
      rw [hdoneWork, hidleWork]
    · exact hdoneOutput.trans hidleOutput
  · obtain ⟨predecessor, rfl⟩ : ∃ predecessor, remaining = predecessor + 1 :=
      ⟨remaining - 1, by omega⟩
    have hcounterPos : (work₀ counter).HasBinaryNat (predecessor + 1) :=
      hcounter
    have hnonblank : (work₀ counter).read ≠ Γ.blank := by
      exact fun h => by
        have := hcounterPos.read_eq_blank_iff.mp h
        omega
    obtain ⟨predDone, hpredReach, hpredHalt, hpredInput,
        hpredOther, hpredCounter, hpredOutput⟩ :=
      TM.binaryPredTM_reachesIn_frame counter predecessor inp₀ work₀ out₀
        hcounterPos (hinput.read_ne_start (by omega))
        (fun i _ => (hwork i).read_ne_start) houtput.read_ne_start
    have hpredResult : predDone.work result = work₀ result :=
      hpredOther result (Ne.symm hne)
    have hpredWorkParked : ∀ i, TM.Parked (predDone.work i) := by
      intro i
      by_cases hi : i = counter
      · subst i
        exact ⟨by
          simp [Tape.HasBinaryNat, Tape.HasBinaryString] at hpredCounter
          omega,
          hpredCounter.2.hasBinaryContent.cells_ne_start⟩
      · rw [hpredOther i hi]
        exact hwork i
    let inner := TM.branchWorkBlankTM counter
      (capturePreviousInputBitTM result) (denseInputIdleTM (n := n))
    by_cases hpredZero : predecessor = 0
    · subst predecessor
      have hinnerBlank : (predDone.work counter).read = Γ.blank :=
        hpredCounter.read_eq_blank_iff.mpr rfl
      have hresultBlank : predDone.work result = TM.resetBinaryBlank := by
        rw [hpredResult]
        exact hresult rfl
      obtain ⟨captureDone, hcaptureReach, hcaptureHalt,
          hcaptureInput, hcaptureWork, hcaptureOutput⟩ :=
        capturePreviousInputBitTM_reachesIn_frame_internal result bit
          predDone.input predDone.work predDone.output
          (by simpa [hpredInput] using hinput)
          (by simpa [hpredInput] using hhead)
          (by simpa [hpredInput] using hbit)
          hresultBlank hpredWorkParked (by simpa [hpredOutput] using houtput)
      obtain ⟨innerDone, hinnerReach, hinnerHalt, hinnerInput,
          hinnerWork, hinnerOutput⟩ :=
        TM.branchWorkBlankTM_reachesIn_blank_frame counter
          (capturePreviousInputBitTM result) (denseInputIdleTM (n := n))
          predDone.input predDone.work predDone.output hinnerBlank
          (by simpa [hpredInput] using hinput.read_ne_start (by omega))
          (fun i => (hpredWorkParked i).read_ne_start)
          (by simpa [hpredOutput] using houtput.read_ne_start)
          hcaptureReach hcaptureHalt
      have hpredInputRead : predDone.input.read ≠ Γ.start := by
        rw [hpredInput]
        exact hinput.read_ne_start (by omega)
      have hpredOutputRead : predDone.output.read ≠ Γ.start := by
        rw [hpredOutput]
        exact houtput.read_ne_start
      have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
        hpredInputRead (fun i => (hpredWorkParked i).read_ne_start)
        hpredOutputRead
      have hinnerReach' : inner.reachesIn 3
          { state := inner.qstart
            input := TM.transitionInput predDone.input
            work := fun i => TM.transitionTape (predDone.work i)
            output := TM.transitionTape predDone.output } innerDone := by
        simpa [inner, htransition.1, htransition.2.1, htransition.2.2] using
          hinnerReach
      have hseqReach := TM.seqTM_reachesIn_of_reachesIn
        (TM.binaryPredTM counter) inner hpredReach hpredHalt hinnerReach'
      have hseqHalt :
          (TM.seqTM (TM.binaryPredTM counter) inner).halted
            (TM.phase2Wrap (TM.binaryPredTM counter) inner innerDone) :=
        (TM.phase2Wrap_halted_iff _ _ _).mpr hinnerHalt
      obtain ⟨done, hreach, hhalt, hdoneInput, hdoneWork, hdoneOutput⟩ :=
        TM.branchWorkBlankTM_reachesIn_nonblank_frame counter
          (denseInputIdleTM (n := n))
          (TM.seqTM (TM.binaryPredTM counter) inner)
          inp₀ work₀ out₀ hnonblank
          (hinput.read_ne_start (by omega))
          (fun i => (hwork i).read_ne_start) houtput.read_ne_start
          hseqReach hseqHalt
      simp only [TM.phase2Wrap] at hdoneInput hdoneWork hdoneOutput
      refine ⟨done, ?_, hhalt, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [denseInputStepTM, denseInputStepTime, inner]
      · exact hdoneInput.trans
          (hinnerInput.trans (hcaptureInput.trans hpredInput))
      · rw [hdoneWork, hinnerWork, hcaptureWork,
          Function.update_of_ne hne]
        simpa using hpredCounter
      · rw [hdoneWork, hinnerWork, hcaptureWork, Function.update_self]
        simp [denseInputStepResult]
      · intro i hic hir
        rw [hdoneWork, hinnerWork, hcaptureWork,
          Function.update_of_ne hir]
        exact hpredOther i hic
      · exact hdoneOutput.trans
          (hinnerOutput.trans (hcaptureOutput.trans hpredOutput))
    · have hinnerNonblank : (predDone.work counter).read ≠ Γ.blank := by
        exact fun h => hpredZero (hpredCounter.read_eq_blank_iff.mp h)
      obtain ⟨idleDone, hidleReach, hidleHalt, hidleInput,
          hidleWork, hidleOutput⟩ :=
        denseInputIdleTM_reachesIn_frame_internal predDone.input
          predDone.work predDone.output
          (by
            rw [hpredInput]
            exact (⟨by omega, hinput.2⟩ : TM.Parked inp₀))
          hpredWorkParked (by simpa [hpredOutput] using houtput)
      obtain ⟨innerDone, hinnerReach, hinnerHalt, hinnerInput,
          hinnerWork, hinnerOutput⟩ :=
        TM.branchWorkBlankTM_reachesIn_nonblank_frame counter
          (capturePreviousInputBitTM result) (denseInputIdleTM (n := n))
          predDone.input predDone.work predDone.output hinnerNonblank
          (by simpa [hpredInput] using hinput.read_ne_start (by omega))
          (fun i => (hpredWorkParked i).read_ne_start)
          (by simpa [hpredOutput] using houtput.read_ne_start)
          hidleReach hidleHalt
      have hpredInputRead : predDone.input.read ≠ Γ.start := by
        rw [hpredInput]
        exact hinput.read_ne_start (by omega)
      have hpredOutputRead : predDone.output.read ≠ Γ.start := by
        rw [hpredOutput]
        exact houtput.read_ne_start
      have htransition := TM.phaseTransition_eq_self_of_reads_ne_start
        hpredInputRead (fun i => (hpredWorkParked i).read_ne_start)
        hpredOutputRead
      have hinnerReach' : inner.reachesIn 2
          { state := inner.qstart
            input := TM.transitionInput predDone.input
            work := fun i => TM.transitionTape (predDone.work i)
            output := TM.transitionTape predDone.output } innerDone := by
        simpa [inner, htransition.1, htransition.2.1, htransition.2.2] using
          hinnerReach
      have hseqReach := TM.seqTM_reachesIn_of_reachesIn
        (TM.binaryPredTM counter) inner hpredReach hpredHalt hinnerReach'
      have hseqHalt :
          (TM.seqTM (TM.binaryPredTM counter) inner).halted
            (TM.phase2Wrap (TM.binaryPredTM counter) inner innerDone) :=
        (TM.phase2Wrap_halted_iff _ _ _).mpr hinnerHalt
      obtain ⟨done, hreach, hhalt, hdoneInput, hdoneWork, hdoneOutput⟩ :=
        TM.branchWorkBlankTM_reachesIn_nonblank_frame counter
          (denseInputIdleTM (n := n))
          (TM.seqTM (TM.binaryPredTM counter) inner)
          inp₀ work₀ out₀ hnonblank
          (hinput.read_ne_start (by omega))
          (fun i => (hwork i).read_ne_start) houtput.read_ne_start
          hseqReach hseqHalt
      simp only [TM.phase2Wrap] at hdoneInput hdoneWork hdoneOutput
      refine ⟨done, ?_, hhalt, ?_, ?_, ?_, ?_, ?_⟩
      · have hnotOne : predecessor + 1 ≠ 1 := by omega
        simpa [denseInputStepTM, denseInputStepTime, inner, hnotOne,
          hpredZero]
      · exact hdoneInput.trans
          (hinnerInput.trans (hidleInput.trans hpredInput))
      · rw [hdoneWork, hinnerWork, hidleWork]
        simpa using hpredCounter
      · rw [hdoneWork, hinnerWork, hidleWork]
        simpa [denseInputStepResult, hpredZero] using hpredResult
      · intro i hic _
        rw [hdoneWork, hinnerWork, hidleWork]
        exact hpredOther i hic
      · exact hdoneOutput.trans
          (hinnerOutput.trans (hidleOutput.trans hpredOutput))

private theorem denseInputScanTM_body_run {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) (haddress : address ≠ 0)
    (hprocessed : processed < input.length)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    (denseInputStepTM counter result).reachesIn
        (denseInputStepTime (address - processed))
        (denseInputBodyStartCfg counter result work₀ out₀ input address
          processed)
        (denseInputBodyDoneCfg counter result work₀ out₀ input address
          processed) := by
  let initialWork := denseInputWork counter result work₀ input address processed
  obtain ⟨done, hreach, hhalt, hdoneInput, hdoneCounter,
      hdoneResult, hdoneOther, hdoneOutput⟩ :=
    denseInputStepTM_reachesIn_frame_internal counter result hne
      (address - processed) (input[processed]'hprocessed)
      (denseInputTape input (processed + 2)) initialWork out₀
      (denseInputTape_startInvariant input (processed + 2))
      (by simp [denseInputTape])
      (by
        change (Tape.init (input.map Γ.ofBool)).cells
          (processed + 2 - 1) = Γ.ofBool input[processed]
        have hindex : processed + 2 - 1 = processed + 1 := by omega
        rw [hindex]
        exact Tape.init_ofBool_cells_lt input processed hprocessed)
      (by
        change (denseInputWork counter result work₀ input address processed
          counter).HasBinaryNat (address - processed)
        rw [denseInputWork_counter counter result hne]
        exact denseInputNatTape_hasBinaryNat _)
      (by
        intro hremaining
        change denseInputWork counter result work₀ input address processed
          result = TM.resetBinaryBlank
        rw [denseInputWork_result]
        unfold denseInputResultTape
        rw [ite_eq_right haddress, ite_eq_right (by omega)])
      (denseInputWork_parked counter result hne work₀ input address
        processed hwork) houtput
  have hdone : done =
      denseInputBodyDoneCfg counter result work₀ out₀ input address processed := by
    apply Complexity.Cfg.ext hhalt
    · exact hdoneInput
    · funext i
      change done.work i = denseInputWork counter result work₀ input address
        (processed + 1) i
      by_cases hic : i = counter
      · subst i
        rw [denseInputWork_counter counter result hne]
        have hcanonical := hdoneCounter.eq_init_move_right
        have hsub : address - processed - 1 = address - (processed + 1) := by
          omega
        simpa [denseInputNatTape, hsub] using hcanonical
      · by_cases hir : i = result
        · subst i
          rw [denseInputWork_result]
          rw [hdoneResult]
          change denseInputStepResult (address - processed)
            (input[processed]'hprocessed)
              (denseInputWork counter result work₀ input address processed
                result) = denseInputResultTape input address (processed + 1)
          rw [denseInputWork_result]
          exact denseInputStepResult_eq input address processed haddress hprocessed
        · rw [denseInputWork_other counter result work₀ input address
            (processed + 1) i hic hir]
          rw [hdoneOther i hic hir]
          exact denseInputWork_other counter result work₀ input address
            processed i hic hir
    · exact hdoneOutput
  rw [← hdone]
  exact hreach

private theorem denseInputScanTM_loopback_step {n : ℕ}
    (counter result : Fin n) (hne : counter ≠ result)
    (work₀ : Fin n → Tape) (out₀ : Tape) (input : List Bool)
    (address processed : ℕ) (hwork : ∀ i, TM.Parked (work₀ i))
    (houtput : TM.Parked out₀) :
    (denseInputScanTM counter result).step
        (TM.forInputBodyWrap (denseInputStepTM counter result)
          (denseInputBodyDoneCfg counter result work₀ out₀ input address
            processed)) =
      some (denseInputScanCfg counter result work₀ out₀ input address
        (processed + 1)) := by
  have hstep := TM.forInputTM_step_body_halt_internal
    (denseInputStepTM counter result)
    (denseInputBodyDoneCfg counter result work₀ out₀ input address processed)
    rfl
    ((denseInputTape_startInvariant input (processed + 2)).read_ne_start
      (by simp [denseInputTape]))
    (fun i => (denseInputWork_parked counter result hne work₀ input
      address (processed + 1) hwork i).read_ne_start)
    houtput.read_ne_start
  simpa [denseInputScanTM, denseInputBodyDoneCfg, denseInputScanCfg,
    TM.forInputBodyWrap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hstep

private def denseInputLoopSpec {n : ℕ} (counter result : Fin n)
    (hne : counter ≠ result) (work₀ : Fin n → Tape) (out₀ : Tape)
    (input : List Bool) (address : ℕ) (haddress : address ≠ 0)
    (hwork : ∀ i, TM.Parked (work₀ i)) (houtput : TM.Parked out₀) :
    TM.ForInputLoopSpec (denseInputStepTM counter result)
      (fun processed => denseInputStepTime (address - processed))
      input.length where
  scanCfg := denseInputScanCfg counter result work₀ out₀ input address
  bodyStartCfg := fun processed =>
    TM.forInputBodyWrap (denseInputStepTM counter result)
      (denseInputBodyStartCfg counter result work₀ out₀ input address processed)
  bodyDoneCfg := fun processed =>
    TM.forInputBodyWrap (denseInputStepTM counter result)
      (denseInputBodyDoneCfg counter result work₀ out₀ input address processed)
  doneCfg := denseInputDoneCfg counter result work₀ out₀ input address
  scanStep := fun processed hprocessed =>
    denseInputScanTM_scan_bit_step counter result hne work₀ out₀ input
      address processed hprocessed hwork houtput
  bodyRun := fun processed hprocessed => by
    simpa [denseInputScanTM] using
      TM.forInputTM_body_reachesIn_internal (denseInputStepTM counter result)
        (denseInputScanTM_body_run counter result hne work₀ out₀ input
          address processed haddress hprocessed hwork houtput)
  loopbackStep := fun processed _ =>
    denseInputScanTM_loopback_step counter result hne work₀ out₀ input
      address processed hwork houtput
  blankStep := denseInputScanTM_scan_blank_step counter result hne work₀ out₀
    input address hwork houtput

private theorem denseInputResultTape_final_hasBinaryNat
    (input : List Bool) (address : ℕ) (haddress : address ≠ 0) :
    (denseInputResultTape input address input.length).HasBinaryNat
      (Complexity.RAM.initRegs input address) := by
  by_cases hindex : address ≤ input.length
  · have hlt : address - 1 < input.length := by omega
    rw [denseInputResultTape, ite_eq_right haddress, ite_eq_left hindex]
    rw [Complexity.RAM.initRegs, ite_eq_right haddress,
      List.getElem?_eq_getElem hlt]
    simpa using denseInputBitTape_hasBinaryNat_internal
      (input[address - 1]'hlt)
  · have hnone : input[address - 1]? = none :=
      List.getElem?_eq_none (by omega)
    rw [denseInputResultTape, ite_eq_right haddress, ite_eq_right hindex]
    simpa [Complexity.RAM.initRegs, haddress, hnone,
      TM.resetBinaryBlank] using
      Tape.init_move_right_hasBinaryNat 0

theorem denseInputScanTM_reachesIn_frame_internal {n : ℕ}
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
      c'.output = out₀ := by
  let spec := denseInputLoopSpec counter result hne work₀ out₀ input address
    haddress hwork houtput
  have hstart :
      { state := (denseInputScanTM counter result).qstart
        input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
        work := work₀
        output := out₀ } = spec.scanCfg 0 := by
    change
      { state := (denseInputScanTM counter result).qstart
        input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
        work := work₀
        output := out₀ } =
        denseInputScanCfg counter result work₀ out₀ input address 0
    apply Complexity.Cfg.ext
      (c :=
        { state := (denseInputScanTM counter result).qstart
          input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
          work := work₀
          output := out₀ })
      (c' := denseInputScanCfg counter result work₀ out₀ input address 0)
      rfl
    · apply Tape.ext
      · simp [denseInputScanCfg, denseInputTape, Tape.move]
      · simp [denseInputScanCfg, denseInputTape, Tape.move]
    · funext i
      change work₀ i = denseInputWork counter result work₀ input address 0 i
      by_cases hic : i = counter
      · subst i
        rw [denseInputWork_counter counter result hne]
        simpa [denseInputNatTape] using hcounter.eq_init_move_right
      · by_cases hir : i = result
        · subst i
          rw [denseInputWork_result, hresult]
          unfold denseInputResultTape
          rw [ite_eq_right haddress, ite_eq_right (by omega)]
        · rw [denseInputWork_other counter result work₀ input address 0
            i hic hir]
    · rfl
  have hrun := spec.reachesIn_internal input.length 0 (by omega)
  rw [← hstart] at hrun
  let done := denseInputDoneCfg counter result work₀ out₀ input address
  refine ⟨done, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [denseInputScanTime, spec, denseInputLoopSpec, done] using! hrun
  · rfl
  · rfl
  · rfl
  · change (denseInputWork counter result work₀ input address input.length
      counter).HasBinaryNat (address - input.length)
    rw [denseInputWork_counter counter result hne]
    exact denseInputNatTape_hasBinaryNat _
  · change (denseInputWork counter result work₀ input address input.length
      result).HasBinaryNat (Complexity.RAM.initRegs input address)
    rw [denseInputWork_result]
    exact denseInputResultTape_final_hasBinaryNat input address haddress
  · intro i hic hir
    change denseInputWork counter result work₀ input address input.length i =
      work₀ i
    exact denseInputWork_other counter result work₀ input address input.length
      i hic hir
  · rfl

private theorem denseInputStepTime_le_width (address processed : ℕ) :
    denseInputStepTime (address - processed) ≤ 2 * address.size + 7 := by
  by_cases hzero : address - processed = 0
  · simp [denseInputStepTime, hzero]
  · by_cases hone : address - processed = 1
    · have hpred := TM.binaryPredTime_le_internal 0
      have hsize : 1 ≤ address.size :=
        Nat.size_pos.mpr (by omega)
      simp [denseInputStepTime, hone] at hpred ⊢
      omega
    · have hpred :=
        TM.binaryPredTime_le_internal (address - processed - 1)
      have hwidth : (address - processed).size ≤ address.size :=
        Nat.size_le_size (Nat.sub_le address processed)
      rw [denseInputStepTime, ite_eq_right hzero, ite_eq_right hone]
      have hsucc : address - processed - 1 + 1 = address - processed := by
        omega
      rw [hsucc] at hpred
      omega

private theorem denseInputLoopTime_le_width (inputLength address processed : ℕ) :
    TM.forInputLoopTime
        (fun current => denseInputStepTime (address - current))
        processed inputLength ≤
      inputLength * (2 * address.size + 9) + 1 := by
  induction inputLength generalizing processed with
  | zero => simp [TM.forInputLoopTime]
  | succ count ih =>
      rw [TM.forInputLoopTime]
      have hbody := denseInputStepTime_le_width address processed
      have htail := ih (processed + 1)
      rw [Nat.add_mul, one_mul]
      omega

theorem denseInputScanTime_le_width_internal (inputLength address : ℕ) :
    denseInputScanTime inputLength address ≤
      inputLength * (2 * address.size + 9) + 1 := by
  exact denseInputLoopTime_le_width inputLength address 0

private theorem parked_of_hasBinaryNat {tape : Tape} {value : ℕ}
    (hvalue : tape.HasBinaryNat value) : TM.Parked tape :=
  ⟨by rw [hvalue.2.1], hvalue.2.hasBinaryContent.cells_ne_start⟩

/-- Resetting the scan counter preserves the lookup result and its untouched tape frame. -/
private theorem denseInputLookupResult_of_reset_counter {n : ℕ}
    (query counter result scratch : Fin n)
    (hqc : query ≠ counter) (hqr : query ≠ result) (hcr : counter ≠ result)
    (hcs : counter ≠ scratch) (hrs : result ≠ scratch)
    (input : List Bool) (address : ℕ) (initialWork work : Fin n → Tape)
    (hresult : (work result).HasBinaryNat (Complexity.RAM.initRegs input address))
    (hother : ∀ i, i ≠ counter → i ≠ result →
      work i = Function.update initialWork counter (denseInputNatTape address) i)
    (hparked : ∀ i, TM.Parked (work i)) :
    DenseInputLookupResult query counter result scratch input address initialWork
      (Function.update work counter ((Tape.init []).move Dir3.right)) := by
  let copiedWork := Function.update initialWork counter (denseInputNatTape address)
  have hblankNat : ((Tape.init []).move Dir3.right).HasBinaryNat 0 := by
    simpa using Tape.init_move_right_hasBinaryNat 0
  constructor
  · rw [Function.update_of_ne hqc]
    rw [hother query hqc hqr]
    simp [copiedWork, Function.update_of_ne hqc]
  · rw [Function.update_self]
    exact hblankNat
  · rw [Function.update_of_ne hcr.symm]
    exact hresult
  · rw [Function.update_of_ne hcs.symm]
    rw [hother scratch hcs.symm hrs.symm]
    simp [copiedWork, Function.update_of_ne hcs.symm]
  · intro i
    by_cases hi : i = counter
    · subst i
      rw [Function.update_self]
      exact parked_of_hasBinaryNat hblankNat
    · rw [Function.update_of_ne hi]
      exact hparked i
  · intro i _ hic hir _
    rw [Function.update_of_ne hic]
    rw [hother i hic hir]
    simp [copiedWork, Function.update_of_ne hic]

theorem denseInputLookupTM_hoareTime_internal {n : ℕ}
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
      (denseInputLookupTime input.length address) := by
  let inp₀ := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  let copiedWork := Function.update initialWork counter
    (denseInputNatTape address)
  have hinput : TM.Parked inp₀ := by
    refine ⟨by simp [inp₀, Tape.move], ?_⟩
    simpa [inp₀] using Tape.init_ofBool_move_right_cells_ne_start input
  have hcopiedCounter : (copiedWork counter).HasBinaryNat address := by
    simp only [copiedWork, Function.update_self]
    exact denseInputNatTape_hasBinaryNat address
  have hcopiedResult : copiedWork result = TM.resetBinaryBlank := by
    simp only [copiedWork, Function.update_of_ne hcr.symm]
    simpa [TM.resetBinaryBlank] using hready.result.eq_init_move_right
  have hcopiedParked : ∀ i, TM.Parked (copiedWork i) := by
    intro i
    by_cases hi : i = counter
    · subst i
      exact parked_of_hasBinaryNat hcopiedCounter
    · simp only [copiedWork, Function.update_of_ne hi]
      exact hready.parked i
  have hcopyRaw := TM.binaryCopyIntoTM_hoareTime_frame
    query counter scratch hqc hqs hcs address 0 inp₀ initialWork out₀
    hready.query hready.counter hready.scratch hinput
    (fun i _ _ _ => hready.parked i) houtput
  have hcopy : (TM.binaryCopyIntoTM query counter scratch).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initialWork ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
      (TM.binaryCopyTime address 0) := by
    simpa [copiedWork, denseInputNatTape] using hcopyRaw
  let scannedPost : TM.TapePred n := fun inp work out =>
    inp.head = input.length + 1 ∧ inp.cells = inp₀.cells ∧
    (work counter).HasBinaryNat (address - input.length) ∧
    (work result).HasBinaryNat (Complexity.RAM.initRegs input address) ∧
    (∀ i, i ≠ counter → i ≠ result → work i = copiedWork i) ∧
    (∀ i, TM.Parked (work i)) ∧ out = out₀
  have hscan : (denseInputScanTM counter result).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = copiedWork ∧ out = out₀)
      scannedPost (denseInputScanTime input.length address) := by
    intro inp work out ⟨hinp, hwork, hout⟩
    subst inp
    subst work
    subst out
    obtain ⟨done, hreach, hhalt, hdoneHead, hdoneCells,
        hdoneCounter, hdoneResult, hdoneOther, hdoneOutput⟩ :=
      denseInputScanTM_reachesIn_frame_internal counter result hcr input
        address copiedWork out₀ haddress hcopiedCounter hcopiedResult
        hcopiedParked houtput
    have hdoneParked : ∀ i, TM.Parked (done.work i) := by
      intro i
      by_cases hic : i = counter
      · subst i
        exact parked_of_hasBinaryNat hdoneCounter
      · by_cases hir : i = result
        · subst i
          exact parked_of_hasBinaryNat hdoneResult
        · rw [hdoneOther i hic hir]
          exact hcopiedParked i
    exact ⟨done, denseInputScanTime input.length address, le_rfl,
      hreach, hhalt, hdoneHead, by simpa [inp₀] using! hdoneCells,
      hdoneCounter, hdoneResult, hdoneOther, hdoneParked, hdoneOutput⟩
  let stablePost : TM.TapePred n := fun inp work out =>
    inp.cells = inp₀.cells ∧
    (work counter).HasBinaryNat (address - input.length) ∧
    (work result).HasBinaryNat (Complexity.RAM.initRegs input address) ∧
    (∀ i, i ≠ counter → i ≠ result → work i = copiedWork i) ∧
    (∀ i, TM.Parked (work i)) ∧ out = out₀
  let rewoundPost : TM.TapePred n := fun inp work out =>
    inp.head = 1 ∧ stablePost inp work out
  have hrewind : (TM.rewindInputTM (n := n)).HoareTime
      scannedPost rewoundPost (input.length + 3) := by
    have hraw := TM.rewindInputTM_hoareTime_frame (n := n)
      (input.length + 1) (P := stablePost)
      (by
        intro inp work out inp' work' out' hstable hcells hhead
          hwork hout
        subst work'
        subst out'
        exact ⟨hcells.trans hstable.1, hstable.2⟩)
    intro inp work out hscanned
    rcases hscanned with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hstart : inp.cells 0 = Γ.start := by
      rw [hcells]
      simp [inp₀, Tape.move]
    have hnostart : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start := by
      intro j hj
      rw [hcells]
      simpa [inp₀] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    exact hraw inp work out
      ⟨hstart, hnostart, by omega, hout ▸ houtput.read_ne_start,
        hout ▸ houtput.1,
        fun i => ⟨(hparked i).read_ne_start, (hparked i).1⟩,
        hcells, hcounter, hresult, hother, hparked, hout⟩
  have hscanTransition : ∀ inp work out, scannedPost inp work out →
      scannedPost (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hscanned
    rcases hscanned with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hinpParked : TM.Parked inp := by
      refine ⟨by omega, ?_⟩
      intro j hj
      rw [hcells]
      simpa [inp₀] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinpParked.read_ne_start (fun i => (hparked i).read_ne_start)
      (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hhead, hcells, hcounter, hresult, hother, hparked, hout⟩
  let finalPost : TM.TapePred n := fun inp work out =>
    inp = inp₀ ∧
    DenseInputLookupResult query counter result scratch input address
      initialWork work ∧
    out = out₀
  have hreset : (TM.resetBinaryWorkTM counter).HoareTime
      rewoundPost finalPost
      (TM.resetBinaryWorkTime 1
        (address - input.length).bits.length) := by
    intro inp work out hrewound
    rcases hrewound with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hinp : inp = inp₀ := by
      apply Tape.ext
      · simpa [inp₀, Tape.move] using hhead
      · exact hcells
    have hrun := TM.resetBinaryWorkTM_hoareTime_frame counter
      (address - input.length).bits 1 inp work out
      hcounter.2.hasBinaryContent hcounter.1
      ⟨by rw [hcounter.2.1], by rw [hcounter.2.1]⟩
      (by simpa [hinp] using hinput)
      (fun i _ => hparked i) (by simpa [hout] using houtput)
    obtain ⟨done, time, htime, hreach, hhalt, hdoneInput,
        hdoneWork, hdoneOutput⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    have hdoneResult : DenseInputLookupResult query counter result scratch
        input address initialWork done.work := by
      rw [hdoneWork]
      exact denseInputLookupResult_of_reset_counter query counter result scratch
        hqc hqr hcr hcs hrs input address initialWork work hresult hother hparked
    exact ⟨done, time, htime, hreach, hhalt,
      hdoneInput.trans hinp, hdoneResult, hdoneOutput.trans hout⟩
  have hrewindTransition : ∀ inp work out, rewoundPost inp work out →
      rewoundPost (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hrewound
    rcases hrewound with ⟨hhead, hcells, hcounter, hresult,
      hother, hparked, hout⟩
    have hinpParked : TM.Parked inp := by
      refine ⟨by omega, ?_⟩
      intro j hj
      rw [hcells]
      simpa [inp₀] using
        Tape.init_ofBool_move_right_cells_ne_start input j hj
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinpParked.read_ne_start (fun i => (hparked i).read_ne_start)
      (hout ▸ houtput.read_ne_start)
    rw [hi, hw, ho]
    exact ⟨hhead, hcells, hcounter, hresult, hother, hparked, hout⟩
  have hrewindReset := TM.seqTM_hoareTime
    (TM.rewindInputTM (n := n)) (TM.resetBinaryWorkTM counter)
    hrewind hrewindTransition hreset
  have hscanTail := TM.seqTM_hoareTime
    (denseInputScanTM counter result)
    (TM.seqTM (TM.rewindInputTM (n := n))
      (TM.resetBinaryWorkTM counter))
    hscan hscanTransition hrewindReset
  have hcopyTransition : ∀ inp work out,
      (inp = inp₀ ∧ work = copiedWork ∧ out = out₀) →
      (TM.transitionInput inp = inp₀ ∧
        (fun i => TM.transitionTape (work i)) = copiedWork ∧
        TM.transitionTape out = out₀) := by
    intro inp work out ⟨hinp, hwork, hout⟩
    subst inp
    subst work
    subst out
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      hinput.read_ne_start (fun i => (hcopiedParked i).read_ne_start)
      houtput.read_ne_start
    exact ⟨hi, hw, ho⟩
  have hall := TM.seqTM_hoareTime
    (TM.binaryCopyIntoTM query counter scratch)
    (TM.seqTM (denseInputScanTM counter result)
      (TM.seqTM (TM.rewindInputTM (n := n))
        (TM.resetBinaryWorkTM counter)))
    hcopy hcopyTransition hscanTail
  simpa [denseInputLookupTM, denseInputLookupTime, inp₀, finalPost] using hall

end Machine
end RegisterStore
end RAM
end Complexity
