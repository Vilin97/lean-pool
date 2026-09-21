/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Comparison
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Internal.Loop
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# RAM snapshot word-width decoder — proof internals

The proof constructs the exact scanner, successor-body, and loopback frames
needed by `TM.ForWorkOnesLoopSpec`. The only changed tapes are the source
cursor and the canonical binary width counter.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

theorem wordTargetRewind_reachesIn_frame_internal {n : ℕ}
    (targetIdx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (htarget : (work₀ targetIdx).HasBinaryPrefix bits)
    (htargetStart : (work₀ targetIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ targetIdx →
      (work₀ i).read ≠ Γ.start ∧ 1 ≤ (work₀ i).head)
    (houtput : out₀.read ≠ Γ.start) (houtputHead : 1 ≤ out₀.head) :
    ∃ c' t,
      t ≤ bits.length + 3 ∧
      (TM.rewindWorkTM targetIdx).reachesIn t
        { state := (TM.rewindWorkTM targetIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (TM.rewindWorkTM targetIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work targetIdx).HasBinaryString bits ∧
      (∀ i, i ≠ targetIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let Frame : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work targetIdx).HasBinaryContent bits ∧
    (∀ i, i ≠ targetIdx → work i = work₀ i) ∧
    out = out₀
  have hrewind := TM.rewindWorkTM_hoareTime_frame targetIdx (bits.length + 1)
    (P := Frame) (by
      intro inp work out inp' work' out' hframe htargetCells htargetHead
        hotherWork hinputEq houtputCells houtputHeadEq
      rcases hframe with ⟨hframeInput, hframeTarget, hframeOther, hframeOutput⟩
      refine ⟨hinputEq.trans hframeInput, ?_, ?_, ?_⟩
      · simpa only [Tape.HasBinaryContent, htargetCells] using hframeTarget
      · intro i hi
        exact (hotherWork i hi).trans (hframeOther i hi)
      · exact (Tape.ext houtputHeadEq houtputCells).trans hframeOutput)
  obtain ⟨c', t, htime, hreach, hhalt, hhead, hframe⟩ :=
    hrewind inp₀ work₀ out₀ (by
      refine ⟨htargetStart, Tape.cells_ne_start_of_hasBinaryPrefix htarget,
        ?_, hinput, houtput, houtputHead, hother, rfl, htarget.2,
        (fun _ _ => rfl), rfl⟩
      rw [htarget.1])
  rcases hframe with ⟨hfinalInput, hfinalTarget, hfinalOther, hfinalOutput⟩
  exact ⟨c', t, by omega, hreach, hhalt, hfinalInput,
    hfinalTarget.hasBinaryString hhead, hfinalOther, hfinalOutput⟩

private def advanceRight (tape : Tape) : ℕ → Tape
  | 0 => tape
  | steps + 1 => (advanceRight tape steps).move Dir3.right

private def binaryNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private def wordWidthWork (sourceIdx widthIdx : Fin n)
    (work₀ : Fin n → Tape) (sourceSteps value : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work₀ sourceIdx (advanceRight (work₀ sourceIdx) sourceSteps))
    widthIdx (binaryNatTape value)

private def scanCfg (sourceIdx widthIdx : Fin n) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (wordWidthTM sourceIdx widthIdx).Q :=
  { state := .inl .scan
    input := inp₀
    work := wordWidthWork sourceIdx widthIdx work₀ value value
    output := out₀ }

private def bodyStartCfg (sourceIdx widthIdx : Fin n) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (TM.binarySuccTM widthIdx).Q :=
  { state := (TM.binarySuccTM widthIdx).qstart
    input := inp₀
    work := wordWidthWork sourceIdx widthIdx work₀ (value + 1) value
    output := out₀ }

private def bodyDoneCfg (sourceIdx widthIdx : Fin n) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (TM.binarySuccTM widthIdx).Q :=
  { state := (TM.binarySuccTM widthIdx).qhalt
    input := inp₀
    work := wordWidthWork sourceIdx widthIdx work₀ (value + 1) (value + 1)
    output := out₀ }

private def doneCfg (sourceIdx widthIdx : Fin n) (width : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape) :
    Cfg n (wordWidthTM sourceIdx widthIdx).Q :=
  { state := .inl .done
    input := inp₀
    work := wordWidthWork sourceIdx widthIdx work₀ width width
    output := out₀ }

private theorem advanceRight_add (tape : Tape) (first second : ℕ) :
    advanceRight tape (first + second) =
      advanceRight (advanceRight tape first) second := by
  induction second with
  | zero => simp [advanceRight]
  | succ second ih =>
      simpa [advanceRight, Nat.add_assoc] using
        congrArg (fun t => t.move Dir3.right) ih

private theorem advanceRight_hasBinarySuffix_append (tape : Tape)
    (pre suffix : List Bool)
    (h : tape.HasBinarySuffix (pre ++ suffix)) :
    (advanceRight tape pre.length).HasBinarySuffix suffix := by
  induction pre generalizing tape with
  | nil => simpa [advanceRight] using h
  | cons bit pre ih =>
      have hmove : (tape.move Dir3.right).HasBinarySuffix (pre ++ suffix) :=
        h.move_right_cons
      have htail := ih (tape := tape.move Dir3.right) hmove
      change (advanceRight tape (pre.length + 1)).HasBinarySuffix suffix
      rw [Nat.add_comm pre.length 1, advanceRight_add tape 1 pre.length]
      simpa [advanceRight] using htail

private theorem replicate_split (width value : ℕ) (hvalue : value ≤ width) :
    List.replicate width true =
      List.replicate value true ++ List.replicate (width - value) true := by
  rw [← List.replicate_add]
  congr
  omega

private theorem source_suffix (sourceIdx : Fin n) (work₀ : Fin n → Tape)
    (width value : ℕ) (payload : List Bool) (hvalue : value ≤ width)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload)) :
    (advanceRight (work₀ sourceIdx) value).HasBinarySuffix
      (List.replicate (width - value) true ++ false :: payload) := by
  have hsplit :
      List.replicate width true ++ false :: payload =
        List.replicate value true ++
          (List.replicate (width - value) true ++ false :: payload) := by
    rw [replicate_split width value hvalue, List.append_assoc]
  rw [hsplit] at hsource
  simpa using advanceRight_hasBinarySuffix_append
    (work₀ sourceIdx) (List.replicate value true)
      (List.replicate (width - value) true ++ false :: payload) hsource

private theorem source_read_one (sourceIdx : Fin n) (work₀ : Fin n → Tape)
    (width value : ℕ) (payload : List Bool) (hvalue : value < width)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload)) :
    (advanceRight (work₀ sourceIdx) value).read = Γ.one := by
  have hsuffix := source_suffix sourceIdx work₀ width value payload
    (Nat.le_of_lt hvalue) hsource
  have hpositive : 0 < width - value := by omega
  have hshape : List.replicate (width - value) true =
      true :: List.replicate (width - value - 1) true := by
    cases hremaining : width - value with
    | zero => omega
    | succ remaining =>
        simp [List.replicate_succ]
  rw [hshape, List.cons_append] at hsuffix
  exact hsuffix.read_cons

private theorem source_final_suffix (sourceIdx : Fin n)
    (work₀ : Fin n → Tape) (width : ℕ) (payload : List Bool)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload)) :
    (advanceRight (work₀ sourceIdx) width).HasBinarySuffix
      (false :: payload) := by
  simpa using source_suffix sourceIdx work₀ width width payload le_rfl hsource

private theorem binaryNatTape_hasBinaryNat (value : ℕ) :
    (binaryNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem wordWidthWork_source (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (work₀ : Fin n → Tape)
    (sourceSteps value : ℕ) :
    wordWidthWork sourceIdx widthIdx work₀ sourceSteps value sourceIdx =
      advanceRight (work₀ sourceIdx) sourceSteps := by
  simp [wordWidthWork, hindices]

private theorem wordWidthWork_width (sourceIdx widthIdx : Fin n)
    (work₀ : Fin n → Tape) (sourceSteps value : ℕ) :
    wordWidthWork sourceIdx widthIdx work₀ sourceSteps value widthIdx =
      binaryNatTape value := by
  simp [wordWidthWork]

private theorem wordWidthWork_other (sourceIdx widthIdx : Fin n)
    (work₀ : Fin n → Tape) (sourceSteps value : ℕ) (i : Fin n)
    (hsourceIdx : i ≠ sourceIdx) (hwidthIdx : i ≠ widthIdx) :
    wordWidthWork sourceIdx widthIdx work₀ sourceSteps value i = work₀ i := by
  simp [wordWidthWork, hsourceIdx, hwidthIdx]

private theorem wordWidthWork_read_ne_start (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (work₀ : Fin n → Tape)
    (sourceSteps value : ℕ) (suffix : List Bool)
    (hsource : (advanceRight (work₀ sourceIdx) sourceSteps).HasBinarySuffix suffix)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start) :
    ∀ i, (wordWidthWork sourceIdx widthIdx work₀ sourceSteps value i).read ≠
      Γ.start := by
  intro i
  by_cases hiSource : i = sourceIdx
  · subst i
    rw [wordWidthWork_source sourceIdx widthIdx hindices]
    exact hsource.read_ne_start
  · by_cases hiWidth : i = widthIdx
    · subst i
      rw [wordWidthWork_width]
      exact Tape.init_ofBool_move_right_read_ne_start value.bits
    · rw [wordWidthWork_other sourceIdx widthIdx work₀ sourceSteps value i
          hiSource hiWidth]
      exact hother i hiSource hiWidth

private theorem scan_step (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (wordWidthTM sourceIdx widthIdx).step
      (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ value) =
      some (TM.forWorkOnesBodyWrap sourceIdx (TM.binarySuccTM widthIdx)
        (bodyStartCfg sourceIdx widthIdx inp₀ work₀ out₀ value)) := by
  have hsuffix := source_suffix sourceIdx work₀ width value payload
    (Nat.le_of_lt hvalue) hsource
  have hone := source_read_one sourceIdx work₀ width value payload hvalue hsource
  have hstep := TM.forWorkOnesTM_step_scan_one_internal sourceIdx
    (TM.binarySuccTM widthIdx)
    (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ value) rfl
    (by
      change
        (wordWidthWork sourceIdx widthIdx work₀ value value sourceIdx).read = Γ.one
      rw [wordWidthWork_source sourceIdx widthIdx hindices]
      exact hone)
    hinput
    (wordWidthWork_read_ne_start sourceIdx widthIdx hindices work₀ value value
      (List.replicate (width - value) true ++ false :: payload) hsuffix hother)
    houtput
  change
    (TM.forWorkOnesTM sourceIdx (TM.binarySuccTM widthIdx)).step
      (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ value) = _
  rw [hstep]
  congr 2
  funext i
  by_cases hi : i = sourceIdx
  · subst i
    simp [bodyStartCfg, scanCfg, wordWidthWork,
      hindices, advanceRight]
  · by_cases hiWidth : i = widthIdx
    · subst i
      simp [bodyStartCfg, scanCfg, wordWidthWork, hi]
    · simp [bodyStartCfg, scanCfg, wordWidthWork, hi, hiWidth]

private theorem body_run (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (TM.binarySuccTM widthIdx).reachesIn (TM.binarySuccTime value)
      (bodyStartCfg sourceIdx widthIdx inp₀ work₀ out₀ value)
      (bodyDoneCfg sourceIdx widthIdx inp₀ work₀ out₀ value) := by
  have hsuffix := source_suffix sourceIdx work₀ width (value + 1) payload
    (by omega) hsource
  let work := wordWidthWork sourceIdx widthIdx work₀ (value + 1) value
  obtain ⟨c', hreach, hhalt, hinput', hwork, hvalue', houtput'⟩ :=
    TM.binarySuccTM_reachesIn_frame widthIdx value inp₀ work out₀
      (by
        change (wordWidthWork sourceIdx widthIdx work₀ (value + 1) value
          widthIdx).HasBinaryNat value
        rw [wordWidthWork_width]
        exact binaryNatTape_hasBinaryNat value)
      hinput
      (by
        intro i hi
        exact wordWidthWork_read_ne_start sourceIdx widthIdx hindices work₀
          (value + 1) value
          (List.replicate (width - (value + 1)) true ++ false :: payload)
          hsuffix hother i)
      houtput
  have hc' : c' = bodyDoneCfg sourceIdx widthIdx inp₀ work₀ out₀ value := by
    refine Cfg.ext hhalt hinput' ?_ houtput'
    funext i
    by_cases hi : i = widthIdx
    · subst i
      change c'.work widthIdx =
        wordWidthWork sourceIdx widthIdx work₀ (value + 1) (value + 1) widthIdx
      rw [wordWidthWork_width]
      exact hvalue'.eq_init_move_right
    · change c'.work i =
        wordWidthWork sourceIdx widthIdx work₀ (value + 1) (value + 1) i
      rw [hwork i hi]
      dsimp [work]
      by_cases his : i = sourceIdx
      · subst i
        rw [wordWidthWork_source sourceIdx widthIdx hindices,
          wordWidthWork_source sourceIdx widthIdx hindices]
      · rw [wordWidthWork_other sourceIdx widthIdx work₀ (value + 1) value i
            his hi,
          wordWidthWork_other sourceIdx widthIdx work₀ (value + 1) (value + 1) i
            his hi]
  rw [← hc']
  simpa [bodyStartCfg, work] using hreach

private theorem loopback_step (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (wordWidthTM sourceIdx widthIdx).step
      (TM.forWorkOnesBodyWrap sourceIdx (TM.binarySuccTM widthIdx)
        (bodyDoneCfg sourceIdx widthIdx inp₀ work₀ out₀ value)) =
      some (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ (value + 1)) := by
  have hsuffix := source_suffix sourceIdx work₀ width (value + 1) payload
    (by omega) hsource
  have hstep := TM.forWorkOnesTM_step_body_halt_internal sourceIdx
    (TM.binarySuccTM widthIdx)
    (bodyDoneCfg sourceIdx widthIdx inp₀ work₀ out₀ value) rfl hinput
    (wordWidthWork_read_ne_start sourceIdx widthIdx hindices work₀
      (value + 1) (value + 1)
      (List.replicate (width - (value + 1)) true ++ false :: payload)
      hsuffix hother)
    houtput
  simpa [wordWidthTM, bodyDoneCfg, scanCfg, TM.forWorkOnesBodyWrap] using hstep

private theorem stop_step (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (wordWidthTM sourceIdx widthIdx).step
      (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ width) =
      some (doneCfg sourceIdx widthIdx width inp₀ work₀ out₀) := by
  have hsuffix := source_final_suffix sourceIdx work₀ width payload hsource
  have hstep := TM.forWorkOnesTM_step_scan_zero_internal sourceIdx
    (TM.binarySuccTM widthIdx)
    (scanCfg sourceIdx widthIdx inp₀ work₀ out₀ width) rfl
    (by
      change
        (wordWidthWork sourceIdx widthIdx work₀ width width sourceIdx).read = Γ.zero
      rw [wordWidthWork_source sourceIdx widthIdx hindices]
      exact hsuffix.read_cons)
    hinput
    (wordWidthWork_read_ne_start sourceIdx widthIdx hindices work₀ width width
      (false :: payload) hsuffix hother)
    houtput
  simpa [wordWidthTM, scanCfg, doneCfg] using hstep

private def loopSpec (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    TM.ForWorkOnesLoopSpec sourceIdx (TM.binarySuccTM widthIdx)
      TM.binarySuccTime width where
  scanCfg := scanCfg sourceIdx widthIdx inp₀ work₀ out₀
  bodyStartCfg := fun value =>
    TM.forWorkOnesBodyWrap sourceIdx (TM.binarySuccTM widthIdx)
      (bodyStartCfg sourceIdx widthIdx inp₀ work₀ out₀ value)
  bodyDoneCfg := fun value =>
    TM.forWorkOnesBodyWrap sourceIdx (TM.binarySuccTM widthIdx)
      (bodyDoneCfg sourceIdx widthIdx inp₀ work₀ out₀ value)
  doneCfg := doneCfg sourceIdx widthIdx width inp₀ work₀ out₀
  scanStep := scan_step sourceIdx widthIdx hindices width payload inp₀ work₀ out₀
    hsource hinput hother houtput
  bodyRun := fun value hvalue =>
    TM.forWorkOnesTM_body_reachesIn_internal sourceIdx (TM.binarySuccTM widthIdx)
      (body_run sourceIdx widthIdx hindices width payload inp₀ work₀ out₀
        hsource hinput hother houtput value hvalue)
  loopbackStep := loopback_step sourceIdx widthIdx hindices width payload inp₀ work₀
    out₀ hsource hinput hother houtput
  stopStep := stop_step sourceIdx widthIdx hindices width payload inp₀ work₀ out₀
    hsource hinput hother houtput

private theorem initial_work (sourceIdx widthIdx : Fin n)
    (hindices : sourceIdx ≠ widthIdx) (work₀ : Fin n → Tape)
    (hwidth : (work₀ widthIdx).HasBinaryNat 0) :
    wordWidthWork sourceIdx widthIdx work₀ 0 0 = work₀ := by
  funext i
  by_cases hiWidth : i = widthIdx
  · subst i
    rw [wordWidthWork_width]
    exact (hwidth.eq_init_move_right).symm
  · by_cases hiSource : i = sourceIdx
    · subst i
      rw [wordWidthWork_source sourceIdx widthIdx hindices]
      rfl
    · exact wordWidthWork_other sourceIdx widthIdx work₀ 0 0 i hiSource hiWidth

private def payloadBitWork (sourceIdx targetIdx : Fin n)
    (work₀ : Fin n → Tape) (bit : Bool) : Fin n → Tape :=
  fun i =>
    if i = sourceIdx then (work₀ i).move Dir3.right
    else if i = targetIdx then
      (work₀ i).writeAndMove (Γw.ofBool bit) Dir3.right
    else work₀ i

private theorem payloadBitTM_step (sourceIdx targetIdx : Fin n)
    (hindices : sourceIdx ≠ targetIdx) (bit : Bool) {suffix : List Bool}
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (bit :: suffix))
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (payloadBitTM sourceIdx targetIdx).step
      { state := (payloadBitTM sourceIdx targetIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (payloadBitTM sourceIdx targetIdx).qhalt
          input := inp₀
          work := payloadBitWork sourceIdx targetIdx work₀ bit
          output := out₀ } := by
  have hread := hsource.read_cons
  rw [TM.step, if_neg (by simp [payloadBitTM])]
  cases bit <;>
    simp only [payloadBitTM, hread, Γ.ofBool, reduceCtorEq]
  all_goals
    refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
    · dsimp only
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only
      funext i
      by_cases his : i = sourceIdx
      · subst i
        simpa [payloadBitWork, hindices] using
          TM.writeAndMove_readBack (work₀ sourceIdx) (hwork sourceIdx) Dir3.right
      · by_cases hit : i = targetIdx
        · subst i
          simp [payloadBitWork, his]
        · simpa [payloadBitWork, his, hit, TM.idleDir, hwork i, Tape.move] using
            TM.writeAndMove_readBack (work₀ i) (hwork i) Dir3.stay
    · dsimp only
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out₀ houtput Dir3.stay

theorem payloadBitTM_reachesIn_frame_internal {n : ℕ}
    (sourceIdx targetIdx : Fin n) (hindices : sourceIdx ≠ targetIdx)
    (bit : Bool) (suffix pre : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (bit :: suffix))
    (htarget : (work₀ targetIdx).HasBinaryPrefix pre)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (payloadBitTM sourceIdx targetIdx).reachesIn 1
        { state := (payloadBitTM sourceIdx targetIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (payloadBitTM sourceIdx targetIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix suffix ∧
      (c'.work targetIdx).HasBinaryPrefix (pre ++ [bit]) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let work' := payloadBitWork sourceIdx targetIdx work₀ bit
  have hwork : ∀ i, (work₀ i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hsource.read_ne_start
    · by_cases hit : i = targetIdx
      · subst i
        rw [htarget.read_blank]
        decide
      · exact hother i his hit
  have hstep :
      (payloadBitTM sourceIdx targetIdx).step
        { state := (payloadBitTM sourceIdx targetIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } =
        some
          { state := (payloadBitTM sourceIdx targetIdx).qhalt
            input := inp₀
            work := work'
            output := out₀ } := by
    apply payloadBitTM_step sourceIdx targetIdx hindices bit inp₀ work₀ out₀
      hsource hinput hwork houtput
  refine ⟨({ state := (payloadBitTM sourceIdx targetIdx).qhalt
             input := inp₀
             work := work'
             output := out₀ } : Cfg n (payloadBitTM sourceIdx targetIdx).Q),
    .step hstep .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · change (payloadBitWork sourceIdx targetIdx work₀ bit sourceIdx).HasBinarySuffix suffix
    simp [payloadBitWork]
    exact hsource.move_right_cons
  · change (payloadBitWork sourceIdx targetIdx work₀ bit targetIdx).HasBinaryPrefix
      (pre ++ [bit])
    simp [payloadBitWork, Ne.symm hindices]
    cases bit with
    | false =>
        simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
          Tape.hasBinaryPrefix_write_bit (t := work₀ targetIdx) false htarget
    | true =>
        simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
          Tape.hasBinaryPrefix_write_bit (t := work₀ targetIdx) true htarget
  · intro i his hit
    change payloadBitWork sourceIdx targetIdx work₀ bit i = work₀ i
    simp [payloadBitWork, his, hit]

private def wordSeparatorWork (sourceIdx : Fin n)
    (work₀ : Fin n → Tape) : Fin n → Tape :=
  Function.update work₀ sourceIdx ((work₀ sourceIdx).move Dir3.right)

private theorem wordSeparatorTM_step (sourceIdx : Fin n)
    (bits : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (false :: bits))
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (wordSeparatorTM sourceIdx).step
      { state := (wordSeparatorTM sourceIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (wordSeparatorTM sourceIdx).qhalt
          input := inp₀
          work := wordSeparatorWork sourceIdx work₀
          output := out₀ } := by
  have hread := hsource.read_cons
  have hzero : (work₀ sourceIdx).read = Γ.zero := by
    simpa [Γ.ofBool] using hread
  rw [TM.step, if_neg (by simp [wordSeparatorTM])]
  simp only [wordSeparatorTM, hzero, ↓reduceIte]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · dsimp only
    simp [TM.idleDir, hinput, Tape.move]
  · dsimp only
    funext i
    by_cases his : i = sourceIdx
    · subst i
      simpa [wordSeparatorWork] using
        TM.writeAndMove_readBack (work₀ sourceIdx) (hwork sourceIdx) Dir3.right
    · simpa [wordSeparatorWork, his, TM.idleDir, hwork i, Tape.move] using
        TM.writeAndMove_readBack (work₀ i) (hwork i) Dir3.stay
  · dsimp only
    simpa [TM.idleDir, houtput, Tape.move] using
      TM.writeAndMove_readBack out₀ houtput Dir3.stay

theorem wordSeparatorTM_reachesIn_frame_internal {n : ℕ}
    (sourceIdx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (false :: bits))
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordSeparatorTM sourceIdx).reachesIn 1
        { state := (wordSeparatorTM sourceIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordSeparatorTM sourceIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix bits ∧
      (∀ i, i ≠ sourceIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  have hwork : ∀ i, (work₀ i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hsource.read_ne_start
    · exact hother i his
  let c' : Cfg n (wordSeparatorTM sourceIdx).Q :=
    { state := (wordSeparatorTM sourceIdx).qhalt
      input := inp₀
      work := wordSeparatorWork sourceIdx work₀
      output := out₀ }
  have hstep := wordSeparatorTM_step sourceIdx bits inp₀ work₀ out₀ hsource
    hinput hwork houtput
  refine ⟨c', .step hstep .zero, rfl, rfl, ?_, ?_, rfl⟩
  · change (wordSeparatorWork sourceIdx work₀ sourceIdx).HasBinarySuffix bits
    simp [wordSeparatorWork]
    exact hsource.move_right_cons
  · intro i his
    change wordSeparatorWork sourceIdx work₀ i = work₀ i
    simp [wordSeparatorWork, his]

private def appendPayload (tape : Tape) : List Bool → Tape
  | [] => tape
  | bit :: bits =>
      appendPayload (tape.writeAndMove (Γw.ofBool bit) Dir3.right) bits

private theorem appendPayload_append (tape : Tape) (first second : List Bool) :
    appendPayload tape (first ++ second) =
      appendPayload (appendPayload tape first) second := by
  induction first generalizing tape with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.cons_append, appendPayload]
      exact ih _

private theorem appendPayload_hasBinaryPrefix (tape : Tape)
    (pre bits : List Bool) (hpre : tape.HasBinaryPrefix pre) :
    (appendPayload tape bits).HasBinaryPrefix (pre ++ bits) := by
  induction bits generalizing tape pre with
  | nil => simpa [appendPayload]
  | cons bit bits ih =>
      have hbit :
          (tape.writeAndMove (Γw.ofBool bit) Dir3.right).HasBinaryPrefix
            (pre ++ [bit]) := by
        cases bit with
        | false =>
            simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
              Tape.hasBinaryPrefix_write_bit (t := tape) false hpre
        | true =>
            simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
              Tape.hasBinaryPrefix_write_bit (t := tape) true hpre
      simpa [appendPayload, List.append_assoc] using
        ih (tape.writeAndMove (Γw.ofBool bit) Dir3.right) (pre ++ [bit]) hbit

private theorem appendPayload_take_succ (tape : Tape) (bits : List Bool)
    (value : ℕ) (hvalue : value < bits.length) :
    appendPayload tape (bits.take (value + 1)) =
      (appendPayload tape (bits.take value)).writeAndMove
        (Γw.ofBool bits[value]) Dir3.right := by
  rw [List.take_succ_eq_append_getElem hvalue, appendPayload_append]
  rfl

private def payloadLoopWork (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) : Fin n → Tape :=
  fun i =>
    if i = sourceIdx then advanceRight (work₀ i) copied
    else if i = targetIdx then appendPayload (work₀ i) (payload.take copied)
    else if i = counterIdx then binaryNatTape counterValue
    else if i = widthIdx then binaryNatTape width
    else work₀ i

private theorem payloadLoopWork_source
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      copied counterValue sourceIdx = advanceRight (work₀ sourceIdx) copied := by
  simp [payloadLoopWork]

private theorem payloadLoopWork_target
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      copied counterValue targetIdx =
        appendPayload (work₀ targetIdx) (payload.take copied) := by
  simp [payloadLoopWork, Ne.symm hdistinct.source_target]

private theorem payloadLoopWork_counter
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      copied counterValue counterIdx = binaryNatTape counterValue := by
  simp [payloadLoopWork, Ne.symm hdistinct.source_counter,
    Ne.symm hdistinct.target_counter]

private theorem payloadLoopWork_width
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      copied counterValue widthIdx = binaryNatTape width := by
  simp [payloadLoopWork, Ne.symm hdistinct.source_width,
    Ne.symm hdistinct.target_width, Ne.symm hdistinct.counter_width]

private theorem payloadLoopWork_other
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) (i : Fin n)
    (his : i ≠ sourceIdx) (hit : i ≠ targetIdx)
    (hic : i ≠ counterIdx) (hiw : i ≠ widthIdx) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      copied counterValue i = work₀ i := by
  simp [payloadLoopWork, his, hit, hic, hiw]

private theorem payloadSource_suffix (sourceIdx : Fin n)
    (payload rest : List Bool) (work₀ : Fin n → Tape) (value : ℕ)
    (hvalue : value ≤ payload.length)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest)) :
    (advanceRight (work₀ sourceIdx) value).HasBinarySuffix
      (payload.drop value ++ rest) := by
  have hsplit : payload ++ rest =
      payload.take value ++ (payload.drop value ++ rest) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit] at hsource
  have h := advanceRight_hasBinarySuffix_append (work₀ sourceIdx)
    (payload.take value) (payload.drop value ++ rest) hsource
  simpa [List.length_take, Nat.min_eq_left hvalue] using h

private theorem payloadTarget_prefix (targetIdx : Fin n)
    (payload : List Bool) (work₀ : Fin n → Tape) (value : ℕ)
    (htarget : (work₀ targetIdx).HasBinaryPrefix []) :
    (appendPayload (work₀ targetIdx) (payload.take value)).HasBinaryPrefix
      (payload.take value) := by
  simpa using appendPayload_hasBinaryPrefix (work₀ targetIdx) []
    (payload.take value) htarget

private theorem payloadLoopWork_read_ne_start
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) (hcopied : copied ≤ payload.length)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start) :
    ∀ i, (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ copied counterValue i).read ≠ Γ.start := by
  intro i
  by_cases his : i = sourceIdx
  · subst i
    rw [payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx]
    exact (payloadSource_suffix sourceIdx payload rest work₀ copied hcopied hsource).read_ne_start
  · by_cases hit : i = targetIdx
    · subst i
      rw [payloadLoopWork_target sourceIdx targetIdx counterIdx widthIdx hdistinct]
      rw [(payloadTarget_prefix targetIdx payload work₀ copied htarget).read_blank]
      decide
    · by_cases hic : i = counterIdx
      · subst i
        rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
        exact Tape.init_ofBool_move_right_read_ne_start counterValue.bits
      · by_cases hiw : i = widthIdx
        · subst i
          rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
          exact Tape.init_ofBool_move_right_read_ne_start width.bits
        · rw [payloadLoopWork_other sourceIdx targetIdx counterIdx widthIdx payload
              width work₀ copied counterValue i his hit hic hiw]
          exact hother i his hit hic hiw

private def payloadScanCfg
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).Q :=
  { state := .inl (.scan true)
    input := inp₀
    work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ value value
    output := out₀ }

private def payloadIterationStartCfg
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM (payloadBitTM sourceIdx targetIdx) counterIdx).qstart
    input := inp₀
    work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ value value
    output := out₀ }

private def payloadIterationDoneCfg
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) (value : ℕ) :
    Cfg n (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM (payloadBitTM sourceIdx targetIdx) counterIdx).qhalt
    input := inp₀
    work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ (value + 1) (value + 1)
    output := out₀ }

private def payloadDoneCfg
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (payload : List Bool) (width : ℕ) (inp₀ : Tape)
    (work₀ : Fin n → Tape) (out₀ : Tape) :
    Cfg n (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).Q :=
  { state := .inl .done
    input := inp₀
    work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ width width
    output := out₀ }

private theorem payloadBitWork_eq_next
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (copied counterValue : ℕ) (hcopied : copied < payload.length) :
    payloadBitWork sourceIdx targetIdx
        (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
          work₀ copied counterValue) payload[copied] =
      payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
        work₀ (copied + 1) counterValue := by
  funext i
  by_cases his : i = sourceIdx
  · subst i
    simp only [payloadBitWork, ↓reduceIte]
    rw [payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx,
      payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx]
    rfl
  · by_cases hit : i = targetIdx
    · subst i
      simp only [payloadBitWork, his, ↓reduceIte]
      rw [payloadLoopWork_target sourceIdx targetIdx counterIdx widthIdx hdistinct,
        payloadLoopWork_target sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact (appendPayload_take_succ (work₀ targetIdx) payload copied hcopied).symm
    · by_cases hic : i = counterIdx
      · subst i
        simp only [payloadBitWork, his, hit, ↓reduceIte]
        rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct,
          payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
      · by_cases hiw : i = widthIdx
        · subst i
          simp only [payloadBitWork, his, hit, ↓reduceIte]
          rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct,
            payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
        · simp only [payloadBitWork, his, hit, ↓reduceIte]
          rw [payloadLoopWork_other sourceIdx targetIdx counterIdx widthIdx payload
              width work₀ copied counterValue i his hit hic hiw,
            payloadLoopWork_other sourceIdx targetIdx counterIdx widthIdx payload
              width work₀ (copied + 1) counterValue i his hit hic hiw]

private theorem payloadTestRun
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
      (TM.binaryForCompareTime width)
      (payloadScanCfg sourceIdx targetIdx counterIdx widthIdx payload width inp₀
        work₀ out₀ value)
      (payloadIterationStartCfg sourceIdx targetIdx counterIdx widthIdx payload
        width inp₀ work₀ out₀ value) := by
  let work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
    work₀ value value
  have hwork := payloadLoopWork_read_ne_start sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width work₀ value value (by omega) hsource htarget hother
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_lt_internal
    (payloadBitTM sourceIdx targetIdx) counterIdx widthIdx hdistinct.counter_width
    value width hvalue inp₀ work out₀
    (by
      dsimp only [work]
      rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact binaryNatTape_hasBinaryNat value)
    (by
      dsimp only [work]
      rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact binaryNatTape_hasBinaryNat width)
    hinput
    (by
      intro i _ _
      exact hwork i)
    houtput
  simpa [wordPayloadTM, payloadScanCfg, payloadIterationStartCfg, work] using hrun

private theorem payloadDoneRun
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
      (TM.binaryForCompareTime width)
      (payloadScanCfg sourceIdx targetIdx counterIdx widthIdx payload width inp₀
        work₀ out₀ width)
      (payloadDoneCfg sourceIdx targetIdx counterIdx widthIdx payload width inp₀
        work₀ out₀) := by
  let work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
    work₀ width width
  have hwork := payloadLoopWork_read_ne_start sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width work₀ width width (by omega) hsource htarget hother
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_eq_internal
    (payloadBitTM sourceIdx targetIdx) counterIdx widthIdx hdistinct.counter_width
    width inp₀ work out₀
    (by
      dsimp only [work]
      rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact binaryNatTape_hasBinaryNat width)
    (by
      dsimp only [work]
      rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact binaryNatTape_hasBinaryNat width)
    hinput
    (by
      intro i _ _
      exact hwork i)
    houtput
  simpa [wordPayloadTM, payloadScanCfg, payloadDoneCfg, work] using hrun

private theorem payloadIterationRun
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
      (TM.binaryForIterationTime (fun _ => 1) value)
      (payloadIterationStartCfg sourceIdx targetIdx counterIdx widthIdx payload
        width inp₀ work₀ out₀ value)
      (payloadIterationDoneCfg sourceIdx targetIdx counterIdx widthIdx payload
        width inp₀ work₀ out₀ value) := by
  let body := payloadBitTM sourceIdx targetIdx
  let beforeWork := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx
    payload width work₀ value value
  let afterBodyWork := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx
    payload width work₀ (value + 1) value
  let afterWork := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx
    payload width work₀ (value + 1) (value + 1)
  have hvaluePayload : value < payload.length := by omega
  have hsourceAt := payloadSource_suffix sourceIdx payload rest work₀ value
    (Nat.le_of_lt hvaluePayload) hsource
  have hsourceShape : payload.drop value ++ rest =
      payload[value] :: (payload.drop (value + 1) ++ rest) := by
    rw [← List.cons_append, List.getElem_cons_drop hvaluePayload]
  rw [hsourceShape] at hsourceAt
  have hworkBefore := payloadLoopWork_read_ne_start sourceIdx targetIdx counterIdx
    widthIdx hdistinct payload rest width work₀ value value
      (Nat.le_of_lt hvaluePayload) hsource htarget hother
  have hbodyStep := payloadBitTM_step sourceIdx targetIdx hdistinct.source_target
    payload[value] inp₀ beforeWork out₀
    (by
      dsimp only [beforeWork]
      rw [payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx]
      exact hsourceAt)
    hinput hworkBefore houtput
  have hbodyWork : payloadBitWork sourceIdx targetIdx beforeWork payload[value] =
      afterBodyWork := by
    dsimp only [beforeWork, afterBodyWork]
    exact payloadBitWork_eq_next sourceIdx targetIdx counterIdx widthIdx hdistinct
      payload width work₀ value value hvaluePayload
  have hbodyReach : body.reachesIn 1
      { state := body.qstart
        input := inp₀
        work := beforeWork
        output := out₀ }
      { state := body.qhalt
        input := inp₀
        work := afterBodyWork
        output := out₀ } := by
    apply TM.reachesIn.step
    · simpa [body, hbodyWork] using hbodyStep
    · exact .zero
  have hworkAfterBody := payloadLoopWork_read_ne_start sourceIdx targetIdx counterIdx
    widthIdx hdistinct payload rest width work₀ (value + 1) value
      (by omega) hsource htarget hother
  obtain ⟨succDone, hsuccReach, hsuccHalt, hsuccInput, hsuccOther,
      hsuccCounter, hsuccOutput⟩ :=
    TM.binarySuccTM_reachesIn_frame counterIdx value inp₀ afterBodyWork out₀
      (by
        dsimp only [afterBodyWork]
        rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
        exact binaryNatTape_hasBinaryNat value)
      hinput (fun i _ => hworkAfterBody i) houtput
  have hsuccDoneEq : succDone =
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp₀
        work := afterWork
        output := out₀ } := by
    refine Cfg.ext hsuccHalt hsuccInput ?_ hsuccOutput
    funext i
    by_cases hic : i = counterIdx
    · subst i
      change succDone.work counterIdx = afterWork counterIdx
      dsimp only [afterWork]
      rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
      exact hsuccCounter.eq_init_move_right
    · rw [hsuccOther i hic]
      dsimp only [afterBodyWork, afterWork]
      simp [payloadLoopWork, hic]
  have htransitionInput : TM.transitionInput inp₀ = inp₀ :=
    TM.transitionInput_eq_self hinput
  have htransitionWork : (fun i => TM.transitionTape (afterBodyWork i)) =
      afterBodyWork := by
    funext i
    exact TM.transitionTape_eq_self (hworkAfterBody i)
  have htransitionOutput : TM.transitionTape out₀ = out₀ :=
    TM.transitionTape_eq_self houtput
  have hsuccReach' : (TM.binarySuccTM counterIdx).reachesIn
      (TM.binarySuccTime value)
      { state := (TM.binarySuccTM counterIdx).qstart
        input := TM.transitionInput inp₀
        work := fun i => TM.transitionTape (afterBodyWork i)
        output := TM.transitionTape out₀ }
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp₀
        work := afterWork
        output := out₀ } := by
    rw [htransitionInput, htransitionWork, htransitionOutput]
    simpa [hsuccDoneEq] using hsuccReach
  have hseq := TM.seqTM_reachesIn_of_reachesIn body
    (TM.binarySuccTM counterIdx) hbodyReach rfl hsuccReach'
  have hlift := TM.binaryForTM_iteration_reachesIn_internal body counterIdx
    widthIdx hseq
  simpa [body, wordPayloadTM, payloadIterationStartCfg,
    payloadIterationDoneCfg, TM.binaryForIterationTime,
    TM.binaryForIterationTM, TM.binaryForIterationWrap, TM.phase1Wrap,
    TM.phase2Wrap, beforeWork, afterWork] using hlift

private theorem payloadLoopbackStep
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) (value : ℕ) (hvalue : value < width) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).step
      (payloadIterationDoneCfg sourceIdx targetIdx counterIdx widthIdx payload
        width inp₀ work₀ out₀ value) =
      some (payloadScanCfg sourceIdx targetIdx counterIdx widthIdx payload width
        inp₀ work₀ out₀ (value + 1)) := by
  let body := payloadBitTM sourceIdx targetIdx
  let work := payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
    work₀ (value + 1) (value + 1)
  let cfg : Cfg n (TM.binaryForIterationTM body counterIdx).Q :=
    { state := (TM.binaryForIterationTM body counterIdx).qhalt
      input := inp₀
      work := work
      output := out₀ }
  have hwork := payloadLoopWork_read_ne_start sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width work₀ (value + 1) (value + 1)
      (by omega) hsource htarget hother
  have hstep := TM.binaryForTM_step_iteration_halt_internal body counterIdx widthIdx
    cfg rfl hinput hwork houtput
  simpa [body, cfg, work, wordPayloadTM, payloadIterationDoneCfg,
    payloadScanCfg, TM.binaryForIterationWrap] using hstep

private def payloadLoopSpec
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    TM.BinaryForLoopSpec (payloadBitTM sourceIdx targetIdx) counterIdx widthIdx
      (fun _ => 1) width where
  counter_ne_limit := hdistinct.counter_width
  scanCfg := payloadScanCfg sourceIdx targetIdx counterIdx widthIdx payload width
    inp₀ work₀ out₀
  iterationStartCfg := payloadIterationStartCfg sourceIdx targetIdx counterIdx
    widthIdx payload width inp₀ work₀ out₀
  iterationDoneCfg := payloadIterationDoneCfg sourceIdx targetIdx counterIdx
    widthIdx payload width inp₀ work₀ out₀
  doneCfg := payloadDoneCfg sourceIdx targetIdx counterIdx widthIdx payload width
    inp₀ work₀ out₀
  testRun := payloadTestRun sourceIdx targetIdx counterIdx widthIdx hdistinct
    payload rest width hwidth inp₀ work₀ out₀ hsource htarget hinput hother houtput
  iterationRun := payloadIterationRun sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width hwidth inp₀ work₀ out₀ hsource htarget hinput hother
      houtput
  loopbackStep := payloadLoopbackStep sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload rest width hwidth inp₀ work₀ out₀ hsource htarget hinput hother
      houtput
  doneRun := payloadDoneRun sourceIdx targetIdx counterIdx widthIdx hdistinct
    payload rest width hwidth inp₀ work₀ out₀ hsource htarget hinput hother houtput

private theorem payloadInitialWork
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload : List Bool) (width : ℕ) (work₀ : Fin n → Tape)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat width) :
    payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width work₀
      0 0 = work₀ := by
  funext i
  by_cases his : i = sourceIdx
  · subst i
    rw [payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx]
    rfl
  · by_cases hit : i = targetIdx
    · subst i
      rw [payloadLoopWork_target sourceIdx targetIdx counterIdx widthIdx hdistinct]
      rfl
    · by_cases hic : i = counterIdx
      · subst i
        rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
        exact (hcounter.eq_init_move_right).symm
      · by_cases hiw : i = widthIdx
        · subst i
          rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
          exact (hwidth.eq_init_move_right).symm
        · exact payloadLoopWork_other sourceIdx targetIdx counterIdx widthIdx
            payload width work₀ 0 0 i his hit hic hiw

theorem wordPayloadTM_reachesIn_frame_internal {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidthLength : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix (payload ++ rest))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat width)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
        (wordPayloadTime width)
        { state := (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work counterIdx).HasBinaryNat width ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
        i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let spec := payloadLoopSpec sourceIdx targetIdx counterIdx widthIdx hdistinct
    payload rest width hwidthLength inp₀ work₀ out₀ hsource htarget hinput hother houtput
  have hreach := spec.reachesIn_internal width 0 (by omega)
  have hinitial := payloadInitialWork sourceIdx targetIdx counterIdx widthIdx
    hdistinct payload width work₀ hcounter hwidth
  refine ⟨payloadDoneCfg sourceIdx targetIdx counterIdx widthIdx payload width
      inp₀ work₀ out₀, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [spec, payloadLoopSpec, wordPayloadTime, wordPayloadTM,
      payloadScanCfg, hinitial] using hreach
  · change (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ width width sourceIdx).HasBinarySuffix rest
    rw [payloadLoopWork_source sourceIdx targetIdx counterIdx widthIdx]
    have hsuffix := payloadSource_suffix sourceIdx payload rest work₀ width
      (by omega) hsource
    simpa [← hwidthLength] using hsuffix
  · change (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ width width targetIdx).HasBinaryPrefix payload
    rw [payloadLoopWork_target sourceIdx targetIdx counterIdx widthIdx hdistinct]
    have hprefix := payloadTarget_prefix targetIdx payload work₀ width htarget
    simpa [← hwidthLength] using hprefix
  · change (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ width width counterIdx).HasBinaryNat width
    rw [payloadLoopWork_counter sourceIdx targetIdx counterIdx widthIdx hdistinct]
    exact binaryNatTape_hasBinaryNat width
  · change (payloadLoopWork sourceIdx targetIdx counterIdx widthIdx payload width
      work₀ width width widthIdx).HasBinaryNat width
    rw [payloadLoopWork_width sourceIdx targetIdx counterIdx widthIdx hdistinct]
    exact binaryNatTape_hasBinaryNat width
  · intro i his hit hic hiw
    exact payloadLoopWork_other sourceIdx targetIdx counterIdx widthIdx payload
      width work₀ width width i his hit hic hiw

theorem wordWidthTM_reachesIn_frame_internal {n : ℕ}
    (sourceIdx widthIdx : Fin n) (hindices : sourceIdx ≠ widthIdx)
    (width : ℕ) (payload : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: payload))
    (hwidth : (work₀ widthIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordWidthTM sourceIdx widthIdx).reachesIn (wordWidthTime width)
        { state := (wordWidthTM sourceIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordWidthTM sourceIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix (false :: payload) ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let spec := loopSpec sourceIdx widthIdx hindices width payload inp₀ work₀ out₀
    hsource hinput hother houtput
  have hreach := spec.reachesIn_internal width 0 (by omega)
  have hinit := initial_work sourceIdx widthIdx hindices work₀ hwidth
  refine ⟨doneCfg sourceIdx widthIdx width inp₀ work₀ out₀, ?_, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simpa [spec, loopSpec, wordWidthTime, scanCfg, hinit] using hreach
  · change
      (wordWidthWork sourceIdx widthIdx work₀ width width sourceIdx).HasBinarySuffix
        (false :: payload)
    rw [wordWidthWork_source sourceIdx widthIdx hindices]
    exact source_final_suffix sourceIdx work₀ width payload hsource
  · change
      (wordWidthWork sourceIdx widthIdx work₀ width width widthIdx).HasBinaryNat width
    rw [wordWidthWork_width]
    exact binaryNatTape_hasBinaryNat width
  · intro i hiSource hiWidth
    exact wordWidthWork_other sourceIdx widthIdx work₀ width width i hiSource hiWidth

theorem wordDecodeTM_reachesIn_frame_internal {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n)
    (hdistinct : PayloadLoopDistinct sourceIdx targetIdx counterIdx widthIdx)
    (payload rest : List Bool) (width : ℕ) (hwidthLength : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: (payload ++ rest)))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hwidth : (work₀ widthIdx).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
      i ≠ widthIdx → (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).reachesIn
        (wordDecodeTime width)
        { state := (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work counterIdx).HasBinaryNat width ∧
      (c'.work widthIdx).HasBinaryNat width ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ counterIdx →
        i ≠ widthIdx → c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  let widthTM := wordWidthTM sourceIdx widthIdx
  let separatorTM := wordSeparatorTM sourceIdx
  let payloadTM := wordPayloadTM sourceIdx targetIdx counterIdx widthIdx
  let tailTM := TM.seqTM separatorTM payloadTM
  have hwidthOther : ∀ i, i ≠ sourceIdx → i ≠ widthIdx →
      (work₀ i).read ≠ Γ.start := by
    intro i his hiw
    by_cases hit : i = targetIdx
    · subst i
      rw [htarget.read_blank]
      decide
    · by_cases hic : i = counterIdx
      · subst i
        rw [hcounter.eq_init_move_right]
        exact Tape.init_ofBool_move_right_read_ne_start (0 : ℕ).bits
      · exact hother i his hit hic hiw
  obtain ⟨widthDone, hwidthReach, hwidthHalt, hwidthInput,
      hwidthSource, hwidthValue, hwidthFrame, hwidthOutput⟩ :=
    wordWidthTM_reachesIn_frame_internal sourceIdx widthIdx
      hdistinct.source_width width (payload ++ rest) inp₀ work₀ out₀ hsource
        hwidth hinput hwidthOther houtput
  have hwidthWork : ∀ i, (widthDone.work i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hwidthSource.read_ne_start
    · by_cases hiw : i = widthIdx
      · subst i
        rw [hwidthValue.eq_init_move_right]
        exact Tape.init_ofBool_move_right_read_ne_start width.bits
      · rw [hwidthFrame i his hiw]
        exact hwidthOther i his hiw
  obtain ⟨separatorDone, hseparatorReach, hseparatorHalt, hseparatorInput,
      hseparatorSource, hseparatorFrame, hseparatorOutput⟩ :=
    wordSeparatorTM_reachesIn_frame_internal sourceIdx (payload ++ rest)
      widthDone.input widthDone.work widthDone.output hwidthSource
      (by rw [hwidthInput]; exact hinput)
      (fun i _ => hwidthWork i)
      (by rw [hwidthOutput]; exact houtput)
  have hseparatorTarget :
      (separatorDone.work targetIdx).HasBinaryPrefix [] := by
    rw [hseparatorFrame targetIdx (Ne.symm hdistinct.source_target),
      hwidthFrame targetIdx (Ne.symm hdistinct.source_target)
        hdistinct.target_width]
    exact htarget
  have hseparatorCounter :
      (separatorDone.work counterIdx).HasBinaryNat 0 := by
    rw [hseparatorFrame counterIdx (Ne.symm hdistinct.source_counter),
      hwidthFrame counterIdx (Ne.symm hdistinct.source_counter)
        hdistinct.counter_width]
    exact hcounter
  have hseparatorWidth :
      (separatorDone.work widthIdx).HasBinaryNat width := by
    rw [hseparatorFrame widthIdx (Ne.symm hdistinct.source_width)]
    exact hwidthValue
  have hseparatorOther : ∀ i, i ≠ sourceIdx → i ≠ targetIdx →
      i ≠ counterIdx → i ≠ widthIdx → (separatorDone.work i).read ≠ Γ.start := by
    intro i his hit hic hiw
    rw [hseparatorFrame i his, hwidthFrame i his hiw]
    exact hother i his hit hic hiw
  obtain ⟨payloadDone, hpayloadReach, hpayloadHalt, hpayloadInput,
      hpayloadSource, hpayloadTarget, hpayloadCounter, hpayloadWidth,
      hpayloadFrame, hpayloadOutput⟩ :=
    wordPayloadTM_reachesIn_frame_internal sourceIdx targetIdx counterIdx widthIdx
      hdistinct payload rest width hwidthLength separatorDone.input
        separatorDone.work separatorDone.output hseparatorSource hseparatorTarget
        hseparatorCounter hseparatorWidth
        (by rw [hseparatorInput, hwidthInput]; exact hinput)
        hseparatorOther
        (by rw [hseparatorOutput, hwidthOutput]; exact houtput)
  have hseparatorWork : ∀ i, (separatorDone.work i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hseparatorSource.read_ne_start
    · exact hseparatorFrame i his ▸ hwidthWork i
  have hsepTransitionInput : TM.transitionInput separatorDone.input =
      separatorDone.input :=
    TM.transitionInput_eq_self (by rw [hseparatorInput, hwidthInput]; exact hinput)
  have hsepTransitionWork :
      (fun i => TM.transitionTape (separatorDone.work i)) = separatorDone.work := by
    funext i
    exact TM.transitionTape_eq_self (hseparatorWork i)
  have hsepTransitionOutput : TM.transitionTape separatorDone.output =
      separatorDone.output :=
    TM.transitionTape_eq_self
      (by rw [hseparatorOutput, hwidthOutput]; exact houtput)
  have hpayloadReach' : payloadTM.reachesIn (wordPayloadTime width)
      { state := payloadTM.qstart
        input := TM.transitionInput separatorDone.input
        work := fun i => TM.transitionTape (separatorDone.work i)
        output := TM.transitionTape separatorDone.output }
      payloadDone := by
    rw [hsepTransitionInput, hsepTransitionWork, hsepTransitionOutput]
    simpa [payloadTM] using hpayloadReach
  have htailReach := TM.seqTM_reachesIn_of_reachesIn separatorTM payloadTM
    (by simpa [separatorTM] using hseparatorReach) hseparatorHalt hpayloadReach'
  have hwidthTransitionInput : TM.transitionInput widthDone.input = widthDone.input :=
    TM.transitionInput_eq_self (by rw [hwidthInput]; exact hinput)
  have hwidthTransitionWork :
      (fun i => TM.transitionTape (widthDone.work i)) = widthDone.work := by
    funext i
    exact TM.transitionTape_eq_self (hwidthWork i)
  have hwidthTransitionOutput : TM.transitionTape widthDone.output =
      widthDone.output :=
    TM.transitionTape_eq_self (by rw [hwidthOutput]; exact houtput)
  have htailReach' : tailTM.reachesIn (1 + 1 + wordPayloadTime width)
      { state := tailTM.qstart
        input := TM.transitionInput widthDone.input
        work := fun i => TM.transitionTape (widthDone.work i)
        output := TM.transitionTape widthDone.output }
      (TM.phase2Wrap separatorTM payloadTM payloadDone) := by
    rw [hwidthTransitionInput, hwidthTransitionWork, hwidthTransitionOutput]
    simpa [tailTM, separatorTM, payloadTM, TM.phase1Wrap] using htailReach
  have hfull := TM.seqTM_reachesIn_of_reachesIn widthTM tailTM
    (by simpa [widthTM] using hwidthReach) hwidthHalt htailReach'
  let finalCfg := TM.phase2Wrap widthTM tailTM
    (TM.phase2Wrap separatorTM payloadTM payloadDone)
  refine ⟨finalCfg, ?_, ?_, hpayloadInput.trans (hseparatorInput.trans hwidthInput),
    hpayloadSource, hpayloadTarget, hpayloadCounter, hpayloadWidth, ?_,
    hpayloadOutput.trans (hseparatorOutput.trans hwidthOutput)⟩
  · simpa [finalCfg, wordDecodeTM, wordDecodeTime, widthTM, tailTM,
      separatorTM, payloadTM] using hfull
  · change finalCfg.state =
      (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).qhalt
    change Sum.inr (Sum.inr payloadDone.state) =
      Sum.inr (Sum.inr (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).qhalt)
    exact congrArg (fun q => Sum.inr (Sum.inr q)) hpayloadHalt
  · intro i his hit hic hiw
    change payloadDone.work i = work₀ i
    rw [hpayloadFrame i his hit hic hiw,
      hseparatorFrame i his, hwidthFrame i his hiw]

private theorem forWorkOnesLoopTime_succ_le_size
    (limit value count : ℕ) (hsum : value + count ≤ limit) :
    TM.forWorkOnesLoopTime TM.binarySuccTime value count ≤
      1 + count * (2 * limit.size + 4) := by
  induction count generalizing value with
  | zero => simp [TM.forWorkOnesLoopTime]
  | succ count ih =>
      rw [TM.forWorkOnesLoopTime]
      have hvalue : value ≤ limit := by omega
      have hsize : value.size ≤ limit.size := Nat.size_le_size hvalue
      have hsucc := TM.binarySuccTime_le value
      have htail := ih (value + 1) (by omega)
      rw [Nat.succ_mul]
      omega

private theorem binaryForLoopTime_one_le_size
    (limit value count : ℕ) (hsum : value + count ≤ limit) :
    TM.binaryForLoopTime (fun _ => 1) limit value count ≤
      (count + 1) * (4 * limit.size + 8) := by
  induction count generalizing value with
  | zero =>
      simp only [TM.binaryForLoopTime, TM.binaryForCompareTime]
      omega
  | succ count ih =>
      rw [TM.binaryForLoopTime]
      have hvalue : value ≤ limit := by omega
      have hsize : value.size ≤ limit.size := Nat.size_le_size hvalue
      have hsucc := TM.binarySuccTime_le value
      have htail := ih (value + 1) (by omega)
      simp only [TM.binaryForCompareTime, TM.binaryForIterationTime]
      nlinarith

theorem wordDecodeTime_le_size_internal (width : ℕ) :
    wordDecodeTime width ≤
      8 * (width + 1) * (width.size + 2) := by
  have hwidthLoop := forWorkOnesLoopTime_succ_le_size width 0 width (by omega)
  have hpayloadLoop := binaryForLoopTime_one_le_size width 0 width (by omega)
  have hwidth : wordWidthTime width ≤
      (width + 1) * (2 * width.size + 4) := by
    unfold wordWidthTime
    nlinarith
  have hpayload : wordPayloadTime width ≤
      (width + 1) * (4 * width.size + 8) := by
    unfold wordPayloadTime
    simpa only [Nat.zero_add] using hpayloadLoop
  unfold wordDecodeTime
  nlinarith

theorem wordWidthTM_isTransducer_internal {n : ℕ}
    (sourceIdx widthIdx : Fin n) :
    (wordWidthTM sourceIdx widthIdx).IsTransducer := by
  exact TM.IsTransducer.forWorkOnesTM_internal
    (TM.binarySuccTM_isTransducer widthIdx)

theorem payloadBitTM_isTransducer_internal {n : ℕ}
    (sourceIdx targetIdx : Fin n) :
    (payloadBitTM sourceIdx targetIdx).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | copy =>
      cases hsource : wHeads sourceIdx <;>
        cases oHead <;>
        simp [payloadBitTM, hsource, TM.allReadBack, TM.allIdle, TM.idleDir]
  | done =>
      cases oHead <;> simp [payloadBitTM, TM.allIdle, TM.idleDir]

theorem wordSeparatorTM_isTransducer_internal {n : ℕ} (sourceIdx : Fin n) :
    (wordSeparatorTM sourceIdx).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | skip =>
      by_cases hzero : wHeads sourceIdx = Γ.zero
      · cases oHead <;> simp [wordSeparatorTM, hzero, TM.idleDir]
      · by_cases hstart : wHeads sourceIdx = Γ.start
        · cases oHead <;>
            simp [wordSeparatorTM, hstart, TM.allIdle, TM.idleDir]
        · cases oHead <;>
            simp [wordSeparatorTM, hzero, hstart, TM.allReadBack, TM.idleDir]
  | done =>
      cases oHead <;> simp [wordSeparatorTM, TM.allIdle, TM.idleDir]

theorem wordPayloadTM_isTransducer_internal {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) :
    (wordPayloadTM sourceIdx targetIdx counterIdx widthIdx).IsTransducer := by
  exact TM.IsTransducer.binaryForTM_internal
    (payloadBitTM_isTransducer_internal sourceIdx targetIdx) counterIdx widthIdx

theorem wordDecodeTM_isTransducer_internal {n : ℕ}
    (sourceIdx targetIdx counterIdx widthIdx : Fin n) :
    (wordDecodeTM sourceIdx targetIdx counterIdx widthIdx).IsTransducer := by
  exact TM.IsTransducer.seqTM_internal
    (wordWidthTM_isTransducer_internal sourceIdx widthIdx)
    (TM.IsTransducer.seqTM_internal
      (wordSeparatorTM_isTransducer_internal sourceIdx)
      (wordPayloadTM_isTransducer_internal sourceIdx targetIdx counterIdx widthIdx))

end Machine

end RegisterStore

end RAM

end Complexity
