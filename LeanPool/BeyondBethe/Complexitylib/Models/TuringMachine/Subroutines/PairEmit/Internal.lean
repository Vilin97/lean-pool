/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.PairEmit.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Pair emission from the input and a work tape — proof internals

This module verifies the exact two-pass controller in `PairEmit.Defs`.
-/


public section

namespace Complexity

namespace TM

/-- Bits emitted for the first component of the pairing codec. -/
private def doubled (bits : List Bool) : List Bool :=
  bits.flatMap fun bit => [bit, bit]

@[simp] private theorem doubled_cons (bit : Bool) (bits : List Bool) :
    doubled (bit :: bits) = bit :: bit :: doubled bits := by
  simp [doubled]

/-- Emit the doubled first component and the two-bit separator. -/
private theorem pairInputWorkTM_first_loop {n : ℕ} (firstIdx : Fin n) :
    ∀ (first emitted : List Bool)
      (c : Cfg n (pairInputWorkTM firstIdx).Q),
      c.state = PairInputWorkPhase.first →
      (c.work firstIdx).HasBinarySuffix first →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ firstIdx → (c.work i).read ≠ Γ.start) →
      c.output.HasBinaryPrefix emitted →
      ∃ c',
        (pairInputWorkTM firstIdx).reachesIn (2 * first.length + 2) c c' ∧
        c'.state = PairInputWorkPhase.second ∧
        c'.input = c.input ∧
        (c'.work firstIdx).HasBinarySuffix [] ∧
        (c'.work firstIdx).cells = (c.work firstIdx).cells ∧
        (∀ i, i ≠ firstIdx → c'.work i = c.work i) ∧
        c'.output.HasBinaryPrefix (emitted ++ doubled first ++ [false, true]) := by
  intro first
  induction first with
  | nil =>
      intro emitted c hstate hsource hinput hother houtput
      have hsourceRead : (c.work firstIdx).read = Γ.blank := hsource.read_nil
      let c₁ : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.separator
          input := transitionInput c.input
          work := fun i => transitionTape (c.work i)
          output := c.output.writeAndMove Γ.zero Dir3.right }
      have hstep₁ : (pairInputWorkTM firstIdx).step c = some c₁ := by
        simp [TM.step, hstate, pairInputWorkTM, hsourceRead, c₁, transitionInput,
          transitionTape]
      have hinputKeep₁ : c₁.input = c.input := by
        simpa [c₁] using transitionInput_eq_self hinput
      have hsourceKeep₁ : c₁.work firstIdx = c.work firstIdx := by
        simpa [c₁] using transitionTape_eq_self (by rw [hsourceRead]; decide)
      have hotherKeep₁ (i) (hi : i ≠ firstIdx) : c₁.work i = c.work i := by
        simpa [c₁] using transitionTape_eq_self (hother i hi)
      have houtput₁ : c₁.output.HasBinaryPrefix (emitted ++ [false]) := by
        simpa [Γ.ofBool, transitionTape, Γw.toΓ, c₁] using Tape.hasBinaryPrefix_write_bit false houtput
      let c₂ : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.second
          input := transitionInput c₁.input
          work := fun i => transitionTape (c₁.work i)
          output := c₁.output.writeAndMove Γ.one Dir3.right }
      have hstep₂ : (pairInputWorkTM firstIdx).step c₁ = some c₂ := by
        simp [TM.step, c₁, pairInputWorkTM, c₂, transitionInput, transitionTape]
      have hinputKeep₂ : c₂.input = c.input := by
        have hstable : transitionInput c₁.input = c₁.input :=
          transitionInput_eq_self (by rw [hinputKeep₁]; exact hinput)
        rw [show c₂.input = transitionInput c₁.input by rfl, hstable,
          hinputKeep₁]
      have hsourceKeep₂ : c₂.work firstIdx = c.work firstIdx := by
        have hstable : transitionTape (c₁.work firstIdx) = c₁.work firstIdx :=
          transitionTape_eq_self (by rw [hsourceKeep₁, hsourceRead]; decide)
        rw [show c₂.work firstIdx = transitionTape (c₁.work firstIdx) by rfl,
          hstable, hsourceKeep₁]
      have hotherKeep₂ (i) (hi : i ≠ firstIdx) : c₂.work i = c.work i := by
        have hstable : transitionTape (c₁.work i) = c₁.work i :=
          transitionTape_eq_self (by rw [hotherKeep₁ i hi]; exact hother i hi)
        rw [show c₂.work i = transitionTape (c₁.work i) by rfl,
          hstable, hotherKeep₁ i hi]
      have houtput₂ : c₂.output.HasBinaryPrefix (emitted ++ [false, true]) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit true houtput₁
        simpa [Γ.ofBool, transitionTape, Γw.toΓ, c₂, List.append_assoc] using hwrite
      refine ⟨c₂, ?_, rfl, hinputKeep₂, ?_, ?_, hotherKeep₂, ?_⟩
      · simpa using TM.reachesIn.step hstep₁ (TM.reachesIn.step hstep₂ .zero)
      · rw [hsourceKeep₂]
        exact hsource
      · rw [hsourceKeep₂]
      · simpa [doubled] using houtput₂
  | cons bit bits ih =>
      intro emitted c hstate hsource hinput hother houtput
      have hsourceRead : (c.work firstIdx).read = Γ.ofBool bit :=
        hsource.read_cons
      let c₁ : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.firstAgain bit
          input := transitionInput c.input
          work := fun i => transitionTape (c.work i)
          output := c.output.writeAndMove (Γ.ofBool bit) Dir3.right }
      have hstep₁ : (pairInputWorkTM firstIdx).step c = some c₁ := by
        cases bit <;>
          simp [TM.step, hstate, pairInputWorkTM, hsourceRead, c₁, transitionInput,
            transitionTape, Γ.ofBool, Γw.toΓ, readBackWrite]
      have hinputKeep₁ : c₁.input = c.input := by
        simpa [c₁] using transitionInput_eq_self hinput
      have hsourceKeep₁ : c₁.work firstIdx = c.work firstIdx := by
        simpa [c₁] using transitionTape_eq_self hsource.read_ne_start
      have hotherKeep₁ (i) (hi : i ≠ firstIdx) : c₁.work i = c.work i := by
        simpa [c₁] using transitionTape_eq_self (hother i hi)
      have houtput₁ : c₁.output.HasBinaryPrefix (emitted ++ [bit]) := by
        simpa [c₁] using Tape.hasBinaryPrefix_write_bit bit houtput
      let c₂ : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.first
          input := transitionInput c₁.input
          work := fun i =>
            (c₁.work i).writeAndMove (readBackWrite (c₁.work i).read)
              (if i = firstIdx then Dir3.right else idleDir (c₁.work i).read)
          output := c₁.output.writeAndMove (Γ.ofBool bit) Dir3.right }
      have hstep₂ : (pairInputWorkTM firstIdx).step c₁ = some c₂ := by
        cases bit <;>
          simp [TM.step, c₁, pairInputWorkTM, c₂, transitionInput, Γ.ofBool,
            Γw.ofBool, Γw.toΓ]
      have hinputKeep₂ : c₂.input = c.input := by
        have hstable : transitionInput c₁.input = c₁.input :=
          transitionInput_eq_self (by rw [hinputKeep₁]; exact hinput)
        rw [show c₂.input = transitionInput c₁.input by rfl, hstable,
          hinputKeep₁]
      have hsourceMove : c₂.work firstIdx = (c.work firstIdx).move Dir3.right := by
        rw [show c₂.work firstIdx =
          (c₁.work firstIdx).writeAndMove (readBackWrite (c₁.work firstIdx).read)
            Dir3.right by simp [c₂]]
        rw [writeAndMove_readBack _ (by rw [hsourceKeep₁]; exact hsource.read_ne_start)]
        rw [hsourceKeep₁]
      have hotherKeep₂ (i) (hi : i ≠ firstIdx) : c₂.work i = c.work i := by
        have hstable : transitionTape (c₁.work i) = c₁.work i :=
          transitionTape_eq_self (by rw [hotherKeep₁ i hi]; exact hother i hi)
        have hc₂ : c₂.work i = transitionTape (c₁.work i) := by
          simp [c₂, hi, transitionTape]
        rw [hc₂, hstable, hotherKeep₁ i hi]
      have hsource₂ : (c₂.work firstIdx).HasBinarySuffix bits := by
        rw [hsourceMove]
        exact hsource.move_right_cons
      have houtput₂ : c₂.output.HasBinaryPrefix (emitted ++ [bit, bit]) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit bit houtput₁
        simpa [c₂, List.append_assoc] using hwrite
      obtain ⟨c', hreach, hstate', hinput', hsource', hsourceCells', hother',
          houtput'⟩ :=
        ih (emitted ++ [bit, bit]) c₂ rfl hsource₂
          (by rw [hinputKeep₂]; exact hinput)
          (by intro i hi
              rw [hotherKeep₂ i hi]
              exact hother i hi)
          houtput₂
      refine ⟨c', ?_, hstate', ?_, hsource', ?_, ?_, ?_⟩
      · simpa [Nat.mul_add, Nat.add_assoc] using! TM.reachesIn.step hstep₁ (TM.reachesIn.step hstep₂ hreach)
      · exact hinput'.trans hinputKeep₂
      · rw [hsourceCells', hsourceMove, Tape.move_cells]
      · intro i hi
        exact (hother' i hi).trans (hotherKeep₂ i hi)
      · simpa [List.append_assoc] using houtput'

/-- Copy the second component verbatim and halt at its delimiter. -/
private theorem pairInputWorkTM_second_loop {n : ℕ} (firstIdx : Fin n) :
    ∀ (second emitted : List Bool)
      (c : Cfg n (pairInputWorkTM firstIdx).Q),
      c.state = PairInputWorkPhase.second →
      c.input.HasBinarySuffix second →
      (∀ i, (c.work i).read ≠ Γ.start) →
      c.output.HasBinaryPrefix emitted →
      ∃ c',
        (pairInputWorkTM firstIdx).reachesIn (second.length + 1) c c' ∧
        (pairInputWorkTM firstIdx).halted c' ∧
        c'.input.HasBinarySuffix [] ∧
        c'.input.cells = c.input.cells ∧
        c'.work = c.work ∧
        c'.output.HasBinaryPrefix (emitted ++ second) := by
  intro second
  induction second with
  | nil =>
      intro emitted c hstate hinput hwork houtput
      have hinputRead : c.input.read = Γ.blank := hinput.read_nil
      have houtputRead : c.output.read = Γ.blank := houtput.read_blank
      let c' : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.done
          input := transitionInput c.input
          work := fun i => transitionTape (c.work i)
          output := transitionTape c.output }
      have hstep : (pairInputWorkTM firstIdx).step c = some c' := by
        simp [TM.step, hstate, pairInputWorkTM, hinputRead, c', transitionInput,
          transitionTape]
      have hinputKeep : c'.input = c.input := by
        simpa [c'] using transitionInput_eq_self (by rw [hinputRead]; decide)
      have hworkKeep : c'.work = c.work := by
        funext i
        simpa [c'] using transitionTape_eq_self (hwork i)
      have houtputKeep : c'.output = c.output := by
        simpa [c'] using transitionTape_eq_self (by rw [houtputRead]; decide)
      refine ⟨c', .step hstep .zero, rfl, ?_, ?_, hworkKeep, ?_⟩
      · rw [hinputKeep]
        exact hinput
      · rw [hinputKeep]
      · simpa [houtputKeep] using houtput
  | cons bit bits ih =>
      intro emitted c hstate hinput hwork houtput
      have hinputRead : c.input.read = Γ.ofBool bit := hinput.read_cons
      let c₁ : Cfg n (pairInputWorkTM firstIdx).Q :=
        { state := PairInputWorkPhase.second
          input := c.input.move Dir3.right
          work := fun i => transitionTape (c.work i)
          output := c.output.writeAndMove (Γ.ofBool bit) Dir3.right }
      have hstep : (pairInputWorkTM firstIdx).step c = some c₁ := by
        cases bit <;>
          simp [TM.step, hstate, pairInputWorkTM, hinputRead, c₁, transitionTape,
            Γ.ofBool, Γw.toΓ, readBackWrite]
      have hinput₁ : c₁.input.HasBinarySuffix bits := by
        simpa [c₁] using hinput.move_right_cons
      have hworkKeep : c₁.work = c.work := by
        funext i
        simpa [c₁] using transitionTape_eq_self (hwork i)
      have hwork₁ (i) : (c₁.work i).read ≠ Γ.start := by
        rw [hworkKeep]
        exact hwork i
      have houtput₁ : c₁.output.HasBinaryPrefix (emitted ++ [bit]) := by
        simpa [c₁] using Tape.hasBinaryPrefix_write_bit bit houtput
      obtain ⟨c', hreach, hhalt, hinput', hinputCells', hwork', houtput'⟩ :=
        ih (emitted ++ [bit]) c₁ rfl hinput₁ hwork₁ houtput₁
      refine ⟨c', ?_, hhalt, hinput', ?_, ?_, ?_⟩
      · simpa using TM.reachesIn.step hstep hreach
      · rw [hinputCells']
        simpa [c₁] using Tape.move_cells c.input Dir3.right
      · exact hwork'.trans hworkKeep
      · simpa [List.append_assoc] using houtput'

/-- Exact execution from the concrete tape boundary used by the generic
fanout combinator. -/
theorem pairInputWorkTM_reachesIn_internal {n : ℕ}
    (firstIdx : Fin n) (first second : List Bool)
    {inp out : Tape} {work : Fin n → Tape}
    (hinput : inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right)
    (hsourceHead : (work firstIdx).head = 1)
    (hsourceOutput : (work firstIdx).HasOutput first)
    (hwork : ∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head)
    (houtput : out = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairInputWorkTM firstIdx).reachesIn (pairInputWorkTime first second)
        { state := (pairInputWorkTM firstIdx).qstart,
          input := inp, work := work, output := out } c' ∧
      (pairInputWorkTM firstIdx).halted c' ∧
      c'.input.HasBinarySuffix [] ∧
      c'.input.cells = inp.cells ∧
      (c'.work firstIdx).HasBinarySuffix [] ∧
      (c'.work firstIdx).cells = (work firstIdx).cells ∧
      (c'.work firstIdx).HasOutput first ∧
      (∀ i, i ≠ firstIdx → c'.work i = work i) ∧
      c'.output.HasBinaryPrefix (pair first second) := by
  have hsourceSuffix : (work firstIdx).HasBinarySuffix first :=
    hsourceOutput.hasBinarySuffix hsourceHead (hwork firstIdx).1
  let c₀ : Cfg n (pairInputWorkTM firstIdx).Q :=
    { state := (pairInputWorkTM firstIdx).qstart,
      input := inp, work := work, output := out }
  obtain ⟨c₁, hreach₁, hstate₁, hinput₁, hsource₁, hsourceCells₁,
      hother₁, houtput₁⟩ :=
    pairInputWorkTM_first_loop firstIdx first [] c₀ rfl
      (by simpa [c₀] using hsourceSuffix)
      (by rw [show c₀.input = inp by rfl, hinput]
          exact Tape.init_ofBool_move_right_read_ne_start second)
      (by
        intro i hi
        show (work i).cells (work i).head ≠ Γ.start
        exact (hwork i).1.2 (work i).head (hwork i).2)
      (by rw [show c₀.output = out by rfl, houtput]
          exact Tape.init_nil_move_right_hasBinaryPrefix_nil)
  have hinputSuffix₁ : c₁.input.HasBinarySuffix second := by
    rw [hinput₁]
    change inp.HasBinarySuffix second
    rw [hinput]
    exact Tape.init_move_right_hasBinarySuffix second
  have hworkRead₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by
    intro i
    by_cases hi : i = firstIdx
    · subst i
      exact hsource₁.read_ne_start
    · rw [hother₁ i hi]
      show (work i).cells (work i).head ≠ Γ.start
      exact (hwork i).1.2 (work i).head (hwork i).2
  obtain ⟨c₂, hreach₂, hhalt₂, hinput₂, hinputCells₂, hwork₂,
      houtput₂⟩ :=
    pairInputWorkTM_second_loop firstIdx second
      (doubled first ++ [false, true]) c₁ hstate₁ hinputSuffix₁
      hworkRead₁ (by simpa using houtput₁)
  refine ⟨c₂, ?_, hhalt₂, hinput₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htime : 2 * first.length + 2 + (second.length + 1) =
        pairInputWorkTime first second := by
      simp only [pairInputWorkTime]
      omega
    rw [← htime]
    simpa only [c₀] using
      reachesIn_trans (pairInputWorkTM firstIdx) hreach₁ hreach₂
  · rw [hinputCells₂, hinput₁]
  · rw [hwork₂]
    exact hsource₁
  · rw [hwork₂]
    exact hsourceCells₁
  · apply (Tape.hasOutput_congr ?_ first).mpr hsourceOutput
    rw [hwork₂]
    exact hsourceCells₁
  · intro i hi
    rw [hwork₂]
    exact hother₁ i hi
  · simpa [pair, delimit, doubled, List.append_assoc] using houtput₂

/-- Internal compact Hoare contract for pair emission. -/
theorem pairInputWorkTM_hoareTime_internal {n : ℕ}
    (firstIdx : Fin n) (first second : List Bool) :
    (pairInputWorkTM firstIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right ∧
        (work firstIdx).head = 1 ∧
        (work firstIdx).HasOutput first ∧
        (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
        out = (Tape.init []).move Dir3.right)
      (fun _inp _work out => out.HasOutput (pair first second))
      (pairInputWorkTime first second) := by
  intro inp work out hpre
  rcases hpre with ⟨hinput, hsourceHead, hsourceOutput, hwork, houtput⟩
  obtain ⟨c', hreach, hhalt, _hinput, _hinputCells, _hsource,
      _hsourceCells, _hsourceOutput, _hother, hprefix⟩ :=
    pairInputWorkTM_reachesIn_internal firstIdx first second hinput
      hsourceHead hsourceOutput hwork houtput
  exact ⟨c', pairInputWorkTime first second, le_rfl, hreach, hhalt,
    hprefix.hasOutput⟩

end TM

end Complexity
