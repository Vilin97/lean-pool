/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.WordDecode.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Linear RAM snapshot word decoder — proof internals

This file proves the exact three-pass behavior of `wordDecodeLinearTM`: copy
the unary width to a marker tape, rewind those markers, then consume one marker
while copying one payload bit. Each pass is linear in the encoded word width.
-/


public section

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

variable {n : ℕ}

private def linearMarkWork (sourceIdx markerIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape := fun i =>
  if i = sourceIdx then (work i).move Dir3.right
  else if i = markerIdx then
    (work i).writeAndMove Γ.one Dir3.right
  else work i

private theorem linearMarkStep
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (suffix pre : List Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsource : (work sourceIdx).HasBinarySuffix (true :: suffix))
    (hmarker : (work markerIdx).HasBinaryPrefix pre)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let work' := linearMarkWork sourceIdx markerIdx work
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .mark, input := inp, work := work, output := out } = some c' ∧
      c'.state = .mark ∧ c'.input = inp ∧
      (c'.work sourceIdx).HasBinarySuffix suffix ∧
      (c'.work markerIdx).HasBinaryPrefix (pre ++ [true]) ∧
      (∀ i, i ≠ sourceIdx → i ≠ markerIdx → c'.work i = work i) ∧
      c'.work = work' ∧ c'.output = out := by
  dsimp only
  let work' := linearMarkWork sourceIdx markerIdx work
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .mark, input := inp, work := work', output := out }
  have hread : (work sourceIdx).read = Γ.one := hsource.read_cons
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .mark, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    simp only [wordDecodeLinearTM, hread]
    apply congrArg some
    refine Cfg.ext rfl ?_ ?_ ?_
    · dsimp only [c']
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only [c', work']
      funext i
      by_cases his : i = sourceIdx
      · subst i
        simpa [linearMarkWork, hdistinct.source_marker] using
          TM.writeAndMove_readBack (work sourceIdx) (hreads sourceIdx) Dir3.right
      · by_cases him : i = markerIdx
        · subst i
          simp [linearMarkWork, his]
        · simpa [linearMarkWork, his, him, TM.idleDir, hreads i,
            Tape.move] using
            TM.writeAndMove_readBack (work i) (hreads i) Dir3.stay
    · dsimp only [c']
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out houtput Dir3.stay
  refine ⟨c', hstep, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · dsimp only [c', work', linearMarkWork]
    rw [if_pos rfl]
    exact hsource.move_right_cons
  · dsimp only [c', work', linearMarkWork]
    rw [if_neg (Ne.symm hdistinct.source_marker), if_pos rfl]
    simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
      Tape.hasBinaryPrefix_write_bit true hmarker
  · intro i his him
    simp [c', work', linearMarkWork, his, him]

private theorem linearMarkLoop
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (width : ℕ) (payload rest pre : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsource : (work sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: (payload ++ rest)))
    (hmarker : (work markerIdx).HasBinaryPrefix pre)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn width
        { state := .mark, input := inp, work := work, output := out } c' ∧
      c'.state = .mark ∧ c'.input = inp ∧
      (c'.work sourceIdx).HasBinarySuffix (false :: (payload ++ rest)) ∧
      (c'.work markerIdx).HasBinaryPrefix
        (pre ++ List.replicate width true) ∧
      (∀ i, i ≠ sourceIdx → i ≠ markerIdx → c'.work i = work i) ∧
      c'.output = out := by
  induction width generalizing inp work out pre with
  | zero =>
      refine ⟨_, .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · simpa using hsource
      · simpa using hmarker
      · intro i _ _
        rfl
  | succ width ih =>
      have hshape :
          List.replicate (width + 1) true ++ false :: (payload ++ rest) =
            true :: (List.replicate width true ++ false :: (payload ++ rest)) := by
        simp [List.replicate_succ]
      rw [hshape] at hsource
      obtain ⟨first, hfirstStep, hfirstState, hfirstInput, hfirstSource,
          hfirstMarker, hfirstFrame, hfirstWork, hfirstOutput⟩ :=
        linearMarkStep sourceIdx targetIdx markerIdx hdistinct
          (List.replicate width true ++ false :: (payload ++ rest)) pre
          inp work out hsource hmarker hinput hreads houtput
      have hfirstReads : ∀ i, (first.work i).read ≠ Γ.start := by
        intro i
        by_cases his : i = sourceIdx
        · subst i
          exact hfirstSource.read_ne_start
        · by_cases him : i = markerIdx
          · subst i
            rw [hfirstMarker.read_blank]
            decide
          · rw [hfirstFrame i his him]
            exact hreads i
      obtain ⟨done, htailReach, hdoneState, hdoneInput, hdoneSource,
          hdoneMarker, hdoneFrame, hdoneOutput⟩ :=
        ih (pre ++ [true]) first.input first.work first.output hfirstSource
          hfirstMarker (by rw [hfirstInput]; exact hinput) hfirstReads
          (by rw [hfirstOutput]; exact houtput)
      refine ⟨done, TM.reachesIn.step hfirstStep ?_, hdoneState,
        hdoneInput.trans hfirstInput, hdoneSource, ?_, ?_,
        hdoneOutput.trans hfirstOutput⟩
      · have hfirstEq : first =
            { state := LinearWordPhase.mark
              input := first.input
              work := first.work
              output := first.output } :=
          Cfg.ext hfirstState rfl rfl rfl
        rw [hfirstEq]
        exact htailReach
      · simpa [List.replicate_succ, List.append_assoc] using hdoneMarker
      · intro i his him
        rw [hdoneFrame i his him, hfirstFrame i his him]

private def linearSeparatorWork (sourceIdx markerIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape := fun i =>
  if i = sourceIdx then (work i).move Dir3.right
  else if i = markerIdx then (work i).move Dir3.left
  else work i

private theorem linearSeparatorStep
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (payload rest : List Bool) (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsource : (work sourceIdx).HasBinarySuffix (false :: (payload ++ rest)))
    (hmarker : (work markerIdx).HasBinaryPrefix (List.replicate payload.length true))
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .mark, input := inp, work := work, output := out } = some c' ∧
      c'.state = .rewind ∧ c'.input = inp ∧
      (c'.work sourceIdx).HasBinarySuffix (payload ++ rest) ∧
      (c'.work markerIdx).head = payload.length ∧
      (c'.work markerIdx).cells = (work markerIdx).cells ∧
      (∀ i, i ≠ sourceIdx → i ≠ markerIdx → c'.work i = work i) ∧
      c'.output = out := by
  let work' := linearSeparatorWork sourceIdx markerIdx work
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .rewind, input := inp, work := work', output := out }
  have hread : (work sourceIdx).read = Γ.zero := hsource.read_cons
  have hmarkerRead : (work markerIdx).read = Γ.blank := hmarker.read_blank
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .mark, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    simp only [wordDecodeLinearTM, hread]
    apply congrArg some
    refine Cfg.ext rfl ?_ ?_ ?_
    · dsimp only [c']
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only [c', work']
      funext i
      by_cases his : i = sourceIdx
      · subst i
        simpa [linearSeparatorWork, hdistinct.source_marker] using
          TM.writeAndMove_readBack (work sourceIdx) (hreads sourceIdx) Dir3.right
      · by_cases him : i = markerIdx
        · subst i
          have hmarkerNe : (work markerIdx).read ≠ Γ.start := by
            rw [hmarkerRead]
            decide
          simpa [linearSeparatorWork, his, hmarkerRead, TM.moveLeftDir] using
            TM.writeAndMove_readBack (work markerIdx) hmarkerNe Dir3.left
        · simpa [linearSeparatorWork, his, him, TM.idleDir, hreads i,
            Tape.move] using
            TM.writeAndMove_readBack (work i) (hreads i) Dir3.stay
    · dsimp only [c']
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out houtput Dir3.stay
  refine ⟨c', hstep, rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · dsimp only [c', work', linearSeparatorWork]
    rw [if_pos rfl]
    exact hsource.move_right_cons
  · dsimp only [c', work', linearSeparatorWork]
    rw [if_neg (Ne.symm hdistinct.source_marker), if_pos rfl]
    simp only [Tape.move]
    rw [hmarker.1]
    simp
  · dsimp only [c', work', linearSeparatorWork]
    rw [if_neg (Ne.symm hdistinct.source_marker), if_pos rfl,
      Tape.move_cells]
  · intro i his him
    simp [c', work', linearSeparatorWork, his, him]

private def linearRewindLeftWork (markerIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape := fun i =>
  if i = markerIdx then (work i).move Dir3.left else work i

private theorem linearRewindLeftStep
    (sourceIdx targetIdx markerIdx : Fin n) (head : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hmarker : (work markerIdx).StartInvariant)
    (hhead : (work markerIdx).head = head + 1)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, i ≠ markerIdx → (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let work' := linearRewindLeftWork markerIdx work
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .rewind, input := inp, work := work, output := out } = some c' ∧
      c'.state = .rewind ∧ c'.input = inp ∧
      (c'.work markerIdx).head = head ∧
      (c'.work markerIdx).cells = (work markerIdx).cells ∧
      (∀ i, i ≠ markerIdx → c'.work i = work i) ∧
      c'.work = work' ∧ c'.output = out := by
  dsimp only
  let work' := linearRewindLeftWork markerIdx work
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .rewind, input := inp, work := work', output := out }
  have hmarkerRead : (work markerIdx).read ≠ Γ.start :=
    hmarker.read_ne_start (by omega)
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .rewind, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    simp only [wordDecodeLinearTM, hmarkerRead, ↓reduceIte]
    apply congrArg some
    refine Cfg.ext rfl ?_ ?_ ?_
    · dsimp only [c']
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only [c', work']
      funext i
      by_cases him : i = markerIdx
      · subst i
        simpa [linearRewindLeftWork, hmarkerRead, TM.moveLeftDir] using
          TM.writeAndMove_readBack (work markerIdx) hmarkerRead Dir3.left
      · simpa [linearRewindLeftWork, him, TM.idleDir, hreads i him,
          Tape.move] using
          TM.writeAndMove_readBack (work i) (hreads i him) Dir3.stay
    · dsimp only [c']
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out houtput Dir3.stay
  refine ⟨c', hstep, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [c', work', linearRewindLeftWork, Tape.move, hhead]
  · simp [c', work', linearRewindLeftWork, Tape.move_cells]
  · intro i him
    simp [c', work', linearRewindLeftWork, him]

private def linearRewindBaseWork (markerIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape := fun i =>
  if i = markerIdx then (work i).move Dir3.right else work i

private theorem linearRewindBaseStep
    (sourceIdx targetIdx markerIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hmarker : (work markerIdx).StartInvariant)
    (hhead : (work markerIdx).head = 0)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, i ≠ markerIdx → (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let work' := linearRewindBaseWork markerIdx work
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .rewind, input := inp, work := work, output := out } = some c' ∧
      c'.state = .copy ∧ c'.input = inp ∧
      (c'.work markerIdx).head = 1 ∧
      (c'.work markerIdx).cells = (work markerIdx).cells ∧
      (∀ i, i ≠ markerIdx → c'.work i = work i) ∧
      c'.work = work' ∧ c'.output = out := by
  dsimp only
  let work' := linearRewindBaseWork markerIdx work
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .copy, input := inp, work := work', output := out }
  have hmarkerRead : (work markerIdx).read = Γ.start := by
    rw [Tape.read, hhead]
    exact hmarker.1
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .rewind, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    simp only [wordDecodeLinearTM, hmarkerRead, ↓reduceIte]
    apply congrArg some
    refine Cfg.ext rfl ?_ ?_ ?_
    · dsimp only [c']
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only [c', work']
      funext i
      by_cases him : i = markerIdx
      · subst i
        simp [linearRewindBaseWork, Tape.writeAndMove, Tape.write,
          Tape.move, hhead]
      · simpa [linearRewindBaseWork, him, TM.idleDir, hreads i him,
          Tape.move] using
          TM.writeAndMove_readBack (work i) (hreads i him) Dir3.stay
    · dsimp only [c']
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out houtput Dir3.stay
  refine ⟨c', hstep, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [c', work', linearRewindBaseWork, Tape.move, hhead]
  · simp [c', work', linearRewindBaseWork, Tape.move_cells]
  · intro i him
    simp [c', work', linearRewindBaseWork, him]

private theorem linearRewindLoop
    (sourceIdx targetIdx markerIdx : Fin n) (head : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hmarker : (work markerIdx).StartInvariant)
    (hhead : (work markerIdx).head = head)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, i ≠ markerIdx → (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn (head + 1)
        { state := .rewind, input := inp, work := work, output := out } c' ∧
      c'.state = .copy ∧ c'.input = inp ∧
      (c'.work markerIdx).head = 1 ∧
      (c'.work markerIdx).cells = (work markerIdx).cells ∧
      (∀ i, i ≠ markerIdx → c'.work i = work i) ∧
      c'.output = out := by
  induction head generalizing inp work out with
  | zero =>
      obtain ⟨done, hstep, hstate, hdoneInput, hdoneHead, hdoneCells,
          hdoneFrame, _, hdoneOutput⟩ :=
        linearRewindBaseStep sourceIdx targetIdx markerIdx inp work out hmarker
          hhead hinput hreads houtput
      exact ⟨done, TM.reachesIn.step hstep .zero, hstate, hdoneInput,
        hdoneHead, hdoneCells, hdoneFrame, hdoneOutput⟩
  | succ head ih =>
      obtain ⟨first, hstep, hfirstState, hfirstInput, hfirstHead,
          hfirstCells, hfirstFrame, hfirstWork, hfirstOutput⟩ :=
        linearRewindLeftStep sourceIdx targetIdx markerIdx head inp work out
          hmarker hhead hinput hreads houtput
      have hfirstMarker : (first.work markerIdx).StartInvariant := by
        simpa only [Tape.StartInvariant, hfirstCells] using hmarker
      have hfirstReads : ∀ i, i ≠ markerIdx →
          (first.work i).read ≠ Γ.start := by
        intro i him
        rw [hfirstFrame i him]
        exact hreads i him
      obtain ⟨done, htail, hdoneState, hdoneInput, hdoneHead, hdoneCells,
          hdoneFrame, hdoneOutput⟩ :=
        ih first.input first.work first.output hfirstMarker hfirstHead
          (by rw [hfirstInput]; exact hinput) hfirstReads
          (by rw [hfirstOutput]; exact houtput)
      have hfirstEq : first =
          { state := LinearWordPhase.rewind
            input := first.input
            work := first.work
            output := first.output } :=
        Cfg.ext hfirstState rfl rfl rfl
      refine ⟨done, TM.reachesIn.step hstep ?_, hdoneState,
        hdoneInput.trans hfirstInput, hdoneHead, hdoneCells.trans hfirstCells,
        ?_, hdoneOutput.trans hfirstOutput⟩
      · rw [hfirstEq]
        exact htail
      · intro i him
        rw [hdoneFrame i him, hfirstFrame i him]

private def linearCopyWork (sourceIdx targetIdx markerIdx : Fin n)
    (bit : Bool) (work : Fin n → Tape) : Fin n → Tape := fun i =>
  if i = sourceIdx then (work i).move Dir3.right
  else if i = targetIdx then
    (work i).writeAndMove (Γw.ofBool bit) Dir3.right
  else if i = markerIdx then (work i).move Dir3.right
  else work i

private theorem linearCopyStep
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (bit : Bool) (payload markers pre : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsource : (work sourceIdx).HasBinarySuffix (bit :: payload))
    (hmarker : (work markerIdx).HasBinarySuffix (true :: markers))
    (htarget : (work targetIdx).HasBinaryPrefix pre)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    let work' := linearCopyWork sourceIdx targetIdx markerIdx bit work
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .copy, input := inp, work := work, output := out } = some c' ∧
      c'.state = .copy ∧ c'.input = inp ∧
      (c'.work sourceIdx).HasBinarySuffix payload ∧
      (c'.work markerIdx).HasBinarySuffix markers ∧
      (c'.work targetIdx).HasBinaryPrefix (pre ++ [bit]) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ markerIdx →
        c'.work i = work i) ∧
      c'.work = work' ∧ c'.output = out := by
  dsimp only
  let work' := linearCopyWork sourceIdx targetIdx markerIdx bit work
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .copy, input := inp, work := work', output := out }
  have hsourceRead : (work sourceIdx).read = Γ.ofBool bit := hsource.read_cons
  have hmarkerRead : (work markerIdx).read = Γ.one := hmarker.read_cons
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .copy, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    cases bit <;>
      simp only [wordDecodeLinearTM, hmarkerRead, hsourceRead, Γ.ofBool,
        reduceCtorEq]
    all_goals
      apply congrArg some
      refine Cfg.ext rfl ?_ ?_ ?_
      · dsimp only [c']
        simp [TM.idleDir, hinput, Tape.move]
      · dsimp only [c', work']
        funext i
        by_cases his : i = sourceIdx
        · subst i
          simpa [linearCopyWork, hdistinct.source_target,
              hdistinct.source_marker] using
            TM.writeAndMove_readBack (work sourceIdx) (hreads sourceIdx)
              Dir3.right
        · by_cases hit : i = targetIdx
          · subst i
            simp [linearCopyWork, his]
          · by_cases him : i = markerIdx
            · subst i
              simpa [linearCopyWork, his, Ne.symm hdistinct.target_marker] using
                TM.writeAndMove_readBack (work markerIdx) (hreads markerIdx)
                  Dir3.right
            · simpa [linearCopyWork, his, hit, him, TM.idleDir, hreads i,
                Tape.move] using
                TM.writeAndMove_readBack (work i) (hreads i) Dir3.stay
      · dsimp only [c']
        simpa [TM.idleDir, houtput, Tape.move] using
          TM.writeAndMove_readBack out houtput Dir3.stay
  refine ⟨c', hstep, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · dsimp only [c', work', linearCopyWork]
    rw [if_pos rfl]
    exact hsource.move_right_cons
  · dsimp only [c', work', linearCopyWork]
    rw [if_neg (Ne.symm hdistinct.source_marker),
      if_neg (Ne.symm hdistinct.target_marker), if_pos rfl]
    exact hmarker.move_right_cons
  · dsimp only [c', work', linearCopyWork]
    rw [if_neg (Ne.symm hdistinct.source_target), if_pos rfl]
    cases bit with
    | false =>
        simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
          Tape.hasBinaryPrefix_write_bit false htarget
    | true =>
        simpa [Γw.ofBool, Γ.ofBool, Γw.toΓ] using
          Tape.hasBinaryPrefix_write_bit true htarget
  · intro i his hit him
    simp [c', work', linearCopyWork, his, hit, him]

private theorem linearCopyDoneStep
    (sourceIdx targetIdx markerIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hmarker : (work markerIdx).HasBinarySuffix [])
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .copy, input := inp, work := work, output := out } = some c' ∧
      c'.state = .done ∧ c'.input = inp ∧ c'.work = work ∧
      c'.output = out := by
  let c' : Cfg n (wordDecodeLinearTM sourceIdx targetIdx markerIdx).Q :=
    { state := .done, input := inp, work := work, output := out }
  have hmarkerRead : (work markerIdx).read = Γ.blank := hmarker.read_nil
  have hstep :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).step
        { state := .copy, input := inp, work := work, output := out } = some c' := by
    rw [TM.step, if_neg (by simp [wordDecodeLinearTM])]
    simp only [wordDecodeLinearTM, hmarkerRead, TM.allReadBack]
    apply congrArg some
    refine Cfg.ext rfl ?_ ?_ ?_
    · dsimp only [c']
      simp [TM.idleDir, hinput, Tape.move]
    · dsimp only [c']
      funext i
      simpa [TM.idleDir, hreads i, Tape.move] using
        TM.writeAndMove_readBack (work i) (hreads i) Dir3.stay
    · dsimp only [c']
      simpa [TM.idleDir, houtput, Tape.move] using
        TM.writeAndMove_readBack out houtput Dir3.stay
  exact ⟨c', hstep, rfl, rfl, rfl, rfl⟩

private theorem linearCopyLoop
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (payload rest pre : List Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hsource : (work sourceIdx).HasBinarySuffix (payload ++ rest))
    (hmarker : (work markerIdx).HasBinarySuffix
      (List.replicate payload.length true))
    (htarget : (work targetIdx).HasBinaryPrefix pre)
    (hinput : inp.read ≠ Γ.start)
    (hreads : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (payload.length + 1)
        { state := .copy, input := inp, work := work, output := out } c' ∧
      c'.state = .done ∧ c'.input = inp ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work markerIdx).HasBinarySuffix [] ∧
      (c'.work markerIdx).head = (work markerIdx).head + payload.length ∧
      (c'.work markerIdx).cells = (work markerIdx).cells ∧
      (c'.work targetIdx).HasBinaryPrefix (pre ++ payload) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ markerIdx →
        c'.work i = work i) ∧
      c'.output = out := by
  induction payload generalizing inp work out pre with
  | nil =>
      have hsource' : (work sourceIdx).HasBinarySuffix rest := by
        simpa using hsource
      have hmarker' : (work markerIdx).HasBinarySuffix [] := by
        simpa using hmarker
      obtain ⟨done, hstep, hstate, hdoneInput, hdoneWork, hdoneOutput⟩ :=
        linearCopyDoneStep sourceIdx targetIdx markerIdx inp work out hmarker'
          hinput hreads houtput
      refine ⟨done, TM.reachesIn.step hstep .zero, hstate, hdoneInput,
        ?_, ?_, ?_, ?_, ?_, ?_, hdoneOutput⟩
      · rw [hdoneWork]
        exact hsource'
      · rw [hdoneWork]
        exact hmarker'
      · rw [hdoneWork]
        simp
      · rw [hdoneWork]
      · simpa [hdoneWork] using htarget
      · intro i _ _ _
        rw [hdoneWork]
  | cons bit payload ih =>
      have hsourceShape : (work sourceIdx).HasBinarySuffix
          (bit :: (payload ++ rest)) := by
        simpa [List.cons_append] using hsource
      have hmarkerShape : (work markerIdx).HasBinarySuffix
          (true :: List.replicate payload.length true) := by
        simpa [List.replicate_succ] using hmarker
      obtain ⟨first, hstep, hfirstState, hfirstInput, hfirstSource,
          hfirstMarker, hfirstTarget, hfirstFrame, hfirstWork, hfirstOutput⟩ :=
        linearCopyStep sourceIdx targetIdx markerIdx hdistinct bit
          (payload ++ rest)
          (List.replicate payload.length true) pre inp work out hsourceShape
          hmarkerShape htarget hinput hreads houtput
      have hfirstReads : ∀ i, (first.work i).read ≠ Γ.start := by
        intro i
        by_cases his : i = sourceIdx
        · subst i
          exact hfirstSource.read_ne_start
        · by_cases hit : i = targetIdx
          · subst i
            rw [hfirstTarget.read_blank]
            decide
          · by_cases him : i = markerIdx
            · subst i
              exact hfirstMarker.read_ne_start
            · rw [hfirstFrame i his hit him]
              exact hreads i
      obtain ⟨done, htail, hdoneState, hdoneInput, hdoneSource,
          hdoneMarker, hdoneMarkerHead, hdoneMarkerCells, hdoneTarget,
          hdoneFrame, hdoneOutput⟩ :=
        ih (pre ++ [bit]) first.input first.work first.output hfirstSource
          hfirstMarker hfirstTarget (by rw [hfirstInput]; exact hinput)
          hfirstReads (by rw [hfirstOutput]; exact houtput)
      have hfirstEq : first =
          { state := LinearWordPhase.copy
            input := first.input
            work := first.work
            output := first.output } :=
        Cfg.ext hfirstState rfl rfl rfl
      refine ⟨done, TM.reachesIn.step hstep ?_, hdoneState,
        hdoneInput.trans hfirstInput, hdoneSource, hdoneMarker, ?_, ?_, ?_,
        ?_, hdoneOutput.trans hfirstOutput⟩
      · rw [hfirstEq]
        exact htail
      · rw [hdoneMarkerHead]
        rw [hfirstWork]
        simp [linearCopyWork, Ne.symm hdistinct.source_marker,
          Ne.symm hdistinct.target_marker, Tape.move]
        omega
      · rw [hdoneMarkerCells]
        rw [hfirstWork]
        simp [linearCopyWork, Ne.symm hdistinct.source_marker,
          Ne.symm hdistinct.target_marker, Tape.move_cells]
      · simpa [List.append_assoc] using hdoneTarget
      · intro i his hit him
        rw [hdoneFrame i his hit him, hfirstFrame i his hit him]

theorem wordDecodeLinearTM_reachesIn_frame_internal
    (sourceIdx targetIdx markerIdx : Fin n)
    (hdistinct : LinearWordDistinct sourceIdx targetIdx markerIdx)
    (payload rest : List Bool) (width : ℕ) (hwidth : payload.length = width)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ sourceIdx).HasBinarySuffix
      (List.replicate width true ++ false :: (payload ++ rest)))
    (htarget : (work₀ targetIdx).HasBinaryPrefix [])
    (hmarker : (work₀ markerIdx).HasBinaryPrefix [])
    (hmarkerStart : (work₀ markerIdx).cells 0 = Γ.start)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (wordDecodeLinearTime width)
        { state := (wordDecodeLinearTM sourceIdx targetIdx markerIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work sourceIdx).HasBinarySuffix rest ∧
      (c'.work targetIdx).HasBinaryPrefix payload ∧
      (c'.work markerIdx).HasBinaryPrefix (List.replicate width true) ∧
      (∀ i, i ≠ sourceIdx → i ≠ targetIdx → i ≠ markerIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ := by
  obtain ⟨marked, hmarkReach, hmarkedState, hmarkedInput, hmarkedSource,
      hmarkedMarker, hmarkedFrame, hmarkedOutput⟩ :=
    linearMarkLoop sourceIdx targetIdx markerIdx hdistinct width payload rest []
      inp₀ work₀ out₀ hsource hmarker hinput hreads houtput
  have hmarkedMarker' : (marked.work markerIdx).HasBinaryPrefix
      (List.replicate payload.length true) := by
    simpa [hwidth] using hmarkedMarker
  have hmarkedReads : ∀ i, (marked.work i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hmarkedSource.read_ne_start
    · by_cases him : i = markerIdx
      · subst i
        rw [hmarkedMarker.read_blank]
        decide
      · rw [hmarkedFrame i his him]
        exact hreads i
  obtain ⟨separated, hseparatorStep, hseparatedState, hseparatedInput,
      hseparatedSource, hseparatedMarkerHead, hseparatedMarkerCells,
      hseparatedFrame, hseparatedOutput⟩ :=
    linearSeparatorStep sourceIdx targetIdx markerIdx hdistinct payload rest
      marked.input marked.work marked.output hmarkedSource hmarkedMarker'
      (by rw [hmarkedInput]; exact hinput) hmarkedReads
      (by rw [hmarkedOutput]; exact houtput)
  have hmarkedEq : marked =
      { state := LinearWordPhase.mark
        input := marked.input
        work := marked.work
        output := marked.output } :=
    Cfg.ext hmarkedState rfl rfl rfl
  have hseparatorReach :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn 1 marked
        separated := by
    rw [hmarkedEq]
    exact TM.reachesIn.step hseparatorStep .zero
  have hmarkedMarkerStart : (marked.work markerIdx).cells 0 = Γ.start :=
    TM.work_cells_zero_eq_start_of_reachesIn markerIdx hmarkReach hmarkerStart
  have hseparatedMarkerInv : (separated.work markerIdx).StartInvariant := by
    constructor
    · rw [hseparatedMarkerCells]
      exact hmarkedMarkerStart
    · intro j hj
      rw [hseparatedMarkerCells]
      exact Tape.cells_ne_start_of_hasBinaryPrefix hmarkedMarker j hj
  have hseparatedReads : ∀ i, i ≠ markerIdx →
      (separated.work i).read ≠ Γ.start := by
    intro i him
    by_cases his : i = sourceIdx
    · subst i
      exact hseparatedSource.read_ne_start
    · rw [hseparatedFrame i his him]
      exact hmarkedReads i
  obtain ⟨rewound, hrewindReach, hrewoundState, hrewoundInput,
      hrewoundMarkerHead, hrewoundMarkerCells, hrewoundFrame,
      hrewoundOutput⟩ :=
    linearRewindLoop sourceIdx targetIdx markerIdx payload.length
      separated.input separated.work separated.output hseparatedMarkerInv
      hseparatedMarkerHead
      (by rw [hseparatedInput, hmarkedInput]; exact hinput)
      hseparatedReads
      (by rw [hseparatedOutput, hmarkedOutput]; exact houtput)
  have hseparatedEq : separated =
      { state := LinearWordPhase.rewind
        input := separated.input
        work := separated.work
        output := separated.output } :=
    Cfg.ext hseparatedState rfl rfl rfl
  have hrewindReach' :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (payload.length + 1) separated rewound := by
    rw [hseparatedEq]
    exact hrewindReach
  have hrewoundSource : (rewound.work sourceIdx).HasBinarySuffix
      (payload ++ rest) := by
    rw [hrewoundFrame sourceIdx hdistinct.source_marker]
    exact hseparatedSource
  have hrewoundTarget : (rewound.work targetIdx).HasBinaryPrefix [] := by
    rw [hrewoundFrame targetIdx hdistinct.target_marker,
      hseparatedFrame targetIdx (Ne.symm hdistinct.source_target)
        hdistinct.target_marker,
      hmarkedFrame targetIdx (Ne.symm hdistinct.source_target)
        hdistinct.target_marker]
    exact htarget
  have hrewoundMarkerString : (rewound.work markerIdx).HasBinaryString
      (List.replicate width true) := by
    apply Tape.hasBinaryString_of_hasBinaryPrefix hmarkedMarker hrewoundMarkerHead
    exact hrewoundMarkerCells.trans hseparatedMarkerCells
  have hrewoundMarkerSuffix := hrewoundMarkerString.hasBinarySuffix
  have hrewoundReads : ∀ i, (rewound.work i).read ≠ Γ.start := by
    intro i
    by_cases him : i = markerIdx
    · subst i
      exact hrewoundMarkerSuffix.read_ne_start
    · rw [hrewoundFrame i him]
      exact hseparatedReads i him
  obtain ⟨done, hcopyReach, hdoneState, hdoneInput, hdoneSource,
      hdoneMarkerSuffix, hdoneMarkerHead, hdoneMarkerCells, hdoneTarget,
      hdoneFrame, hdoneOutput⟩ :=
    linearCopyLoop sourceIdx targetIdx markerIdx hdistinct payload rest []
      rewound.input rewound.work rewound.output hrewoundSource
      (by simpa [hwidth] using hrewoundMarkerSuffix) hrewoundTarget
      (by rw [hrewoundInput, hseparatedInput, hmarkedInput]; exact hinput)
      hrewoundReads
      (by rw [hrewoundOutput, hseparatedOutput, hmarkedOutput]; exact houtput)
  have hrewoundEq : rewound =
      { state := LinearWordPhase.copy
        input := rewound.input
        work := rewound.work
        output := rewound.output } :=
    Cfg.ext hrewoundState rfl rfl rfl
  have hcopyReach' :
      (wordDecodeLinearTM sourceIdx targetIdx markerIdx).reachesIn
        (payload.length + 1) rewound done := by
    rw [hrewoundEq]
    exact hcopyReach
  let tm := wordDecodeLinearTM sourceIdx targetIdx markerIdx
  have hfull := TM.reachesIn_trans tm
    (TM.reachesIn_trans tm (TM.reachesIn_trans tm hmarkReach hseparatorReach)
      hrewindReach') hcopyReach'
  have htime :
      width + 1 + (payload.length + 1) + (payload.length + 1) =
        wordDecodeLinearTime width := by
    simp only [wordDecodeLinearTime, hwidth]
    omega
  have hdoneMarker : (done.work markerIdx).HasBinaryPrefix
      (List.replicate width true) := by
    apply Tape.hasBinaryPrefix_of_hasBinaryString hrewoundMarkerString
    · rw [hdoneMarkerHead, hrewoundMarkerHead, hwidth]
      simp
      omega
    · exact hdoneMarkerCells
  refine ⟨done, ?_, hdoneState, ?_, hdoneSource, ?_, hdoneMarker, ?_, ?_⟩
  · rw [← htime]
    exact hfull
  · exact hdoneInput.trans
      (hrewoundInput.trans (hseparatedInput.trans hmarkedInput))
  · simpa using hdoneTarget
  · intro i his hit him
    rw [hdoneFrame i his hit him, hrewoundFrame i him,
      hseparatedFrame i his him, hmarkedFrame i his him]
  · exact hdoneOutput.trans
      (hrewoundOutput.trans (hseparatedOutput.trans hmarkedOutput))

theorem wordDecodeLinearTM_isTransducer_internal
    (sourceIdx targetIdx markerIdx : Fin n) :
    (wordDecodeLinearTM sourceIdx targetIdx markerIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | mark =>
      cases hsource : wHeads sourceIdx <;>
        cases oHead <;>
        simp [wordDecodeLinearTM, hsource, TM.allReadBack, TM.allIdle,
          TM.idleDir]
  | rewind =>
      by_cases hmarker : wHeads markerIdx = Γ.start <;>
        cases oHead <;>
        simp [wordDecodeLinearTM, hmarker, TM.idleDir]
  | copy =>
      cases hmarker : wHeads markerIdx with
      | one =>
          cases hsource : wHeads sourceIdx <;>
            cases oHead <;>
            simp [wordDecodeLinearTM, hmarker, hsource, TM.allReadBack,
              TM.idleDir]
      | zero | blank =>
          cases oHead <;>
            simp [wordDecodeLinearTM, hmarker, TM.allReadBack, TM.idleDir]
      | start =>
          cases oHead <;>
            simp [wordDecodeLinearTM, hmarker, TM.idleDir]
  | done =>
      cases oHead <;> simp [wordDecodeLinearTM, TM.allIdle, TM.idleDir]

end Machine

end RegisterStore

end RAM

end Complexity
