/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub.Internal.Pure
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Linear-time canonical binary subtraction -- backward cleanup

This module proves the exact backward half of `TM.binaryRippleSubCoreTM`.
Underflow erases the entire fixed-width result. Otherwise the machine erases
only redundant high zeros, preserves the significant suffix after its first
high one, and returns the result head to cell one. All other tapes are framed
literally throughout the run.
-/


@[expose] public section

namespace Complexity

namespace Tape

/-- Blanking the final represented cell shortens canonical binary contents by
one bit. The erased bit may have either value. -/
theorem HasBinaryContent.write_blank_last_internal {t : Tape}
    {bitsPrefix : List Bool} {bit : Bool}
    (h : t.HasBinaryContent (bitsPrefix ++ [bit]))
    (hhead : t.head = bitsPrefix.length + 1) :
    (t.write Γ.blank).HasBinaryContent bitsPrefix := by
  have hhead0 : t.head ≠ 0 := by omega
  constructor
  · intro i hi
    rw [Tape.write, ite_eq_right hhead0]
    simp only
    rw [hhead, Function.update_of_ne (by omega)]
    have hcell := h.1 i (by simp; omega)
    simpa [List.getElem_append, hi] using hcell
  · intro i hi
    rw [Tape.write, ite_eq_right hhead0]
    simp only
    rw [hhead]
    by_cases heq : i = bitsPrefix.length
    · subst i
      rw [Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact h.2 i (by simp; omega)

end Tape

namespace TM

variable {n : ℕ} {lhsIdx rhsIdx resultIdx : Fin n}

private theorem binaryRippleSubCoreTM_ne_halt
    {phase : BinaryRippleSubPhase}
    (hne : phase ≠ .done)
    {c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q}
    (hstate : c.state = phase) :
    c.state ≠ (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).qhalt := by
  rw [hstate]
  exact hne

private theorem binaryRippleSubCoreTM_step_erase
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .erase)
    (hread : (c.work resultIdx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .erase
        input := c.input
        work := Function.update c.work resultIdx
          (((c.work resultIdx).write Γ.blank).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by simp) hstate)]
  simp only [binaryRippleSubCoreTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = resultIdx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      simp [moveLeftDir, hread]
    · rw [Function.update_of_ne hi]
      simpa only [ite_eq_right hi] using! transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

private theorem binaryRippleSubCoreTM_step_trim_false_zero
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .trim false)
    (hread : (c.work resultIdx).read = Γ.zero)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .trim false
        input := c.input
        work := Function.update c.work resultIdx
          (((c.work resultIdx).write Γ.blank).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by decide) hstate)]
  simp only [binaryRippleSubCoreTM, hstate]
  simp [hread]
  refine ⟨transitionInput_eq_self hinput, ?_, transitionTape_eq_self houtput⟩
  funext i
  by_cases hi : i = resultIdx
  · subst i
    simp only [↓reduceIte, Function.update_self]
    simp [moveLeftDir]
  · rw [Function.update_of_ne hi]
    simpa only [ite_eq_right hi] using! transitionTape_eq_self (hother i hi)

private theorem binaryRippleSubCoreTM_step_trim_false_one
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .trim false)
    (hread : (c.work resultIdx).read = Γ.one)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .trim true
        input := c.input
        work := Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by decide) hstate)]
  simp only [binaryRippleSubCoreTM, hstate]
  simp [hread]
  refine ⟨transitionInput_eq_self hinput, ?_, transitionTape_eq_self houtput⟩
  funext i
  by_cases hi : i = resultIdx
  · subst i
    rw [ite_eq_left rfl, Function.update_self]
    change (c.work resultIdx).writeAndMove
      (readBackWrite (c.work resultIdx).read) (moveLeftDir Γ.one) = _
    rw [writeAndMove_readBack _ (by rw [hread]; decide)]
    simp [moveLeftDir]
  · rw [ite_eq_right hi, Function.update_of_ne hi]
    exact transitionTape_eq_self (hother i hi)

private theorem binaryRippleSubCoreTM_step_trim_true
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .trim true)
    (hread : (c.work resultIdx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .trim true
        input := c.input
        work := Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by decide) hstate)]
  simp only [binaryRippleSubCoreTM, hstate]
  simp [hread]
  refine ⟨transitionInput_eq_self hinput, ?_, transitionTape_eq_self houtput⟩
  funext i
  by_cases hi : i = resultIdx
  · subst i
    rw [ite_eq_left rfl, Function.update_self]
    change (c.work resultIdx).writeAndMove
      (readBackWrite (c.work resultIdx).read)
        (moveLeftDir (c.work resultIdx).read) = _
    rw [writeAndMove_readBack _ hread]
    simp [moveLeftDir, hread]
  · rw [ite_eq_right hi, Function.update_of_ne hi]
    exact transitionTape_eq_self (hother i hi)

private theorem binaryRippleSubCoreTM_step_erase_start
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .erase)
    (hread : (c.work resultIdx).read = Γ.start)
    (hhead : (c.work resultIdx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .done
        input := c.input
        work := Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by simp) hstate)]
  simp only [binaryRippleSubCoreTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = resultIdx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      show (((c.work resultIdx).write _).move Dir3.right) =
        (c.work resultIdx).move Dir3.right
      rw [Tape.write, ite_eq_left hhead]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

private theorem binaryRippleSubCoreTM_step_trim_start
    (seenOne : Bool)
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .trim seenOne)
    (hread : (c.work resultIdx).read = Γ.start)
    (hhead : (c.work resultIdx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).step c = some
      { state := .done
        input := c.input
        work := Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binaryRippleSubCoreTM_ne_halt (by simp) hstate)]
  simp only [binaryRippleSubCoreTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = resultIdx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      show (((c.work resultIdx).write _).move Dir3.right) =
        (c.work resultIdx).move Dir3.right
      rw [Tape.write, ite_eq_left hhead]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-! ## Exact backward runs -/

private theorem binaryRippleSubCoreTM_trim_true_run
    (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ head (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q),
      c.state = .trim true →
      c.input = inp₀ →
      (∀ i, i ≠ resultIdx → c.work i = work₀ i) →
      (c.work resultIdx).HasBinaryContent bits →
      (c.work resultIdx).cells 0 = Γ.start →
      (c.work resultIdx).head = head →
      c.output = out₀ →
      ∃ c',
        (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
          (head + 1) c c' ∧
        (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ resultIdx → c'.work i = work₀ i) ∧
        (c'.work resultIdx).HasBinaryString bits ∧
        (c'.work resultIdx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro head
  induction head with
  | zero =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work resultIdx).read = Γ.start := by
        rw [Tape.read, hhead]
        exact hcell0
      have hstep := binaryRippleSubCoreTM_step_trim_start true c hstate hread
        hhead (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
        { state := .done
          input := c.input
          work := Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right)
          output := c.output }
      refine ⟨c₁, .step hstep .zero, rfl, hinput, ?_, ?_, ?_, houtput⟩
      · intro i hi
        show Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).HasBinaryString bits
        rw [Function.update_self]
        apply Tape.HasBinaryContent.hasBinaryString
        · exact hcontent.move Dir3.right
        · simp [Tape.move, hhead]
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).cells 0 = _
        rw [Function.update_self, Tape.move_cells]
        exact hcell0
  | succ head ih =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work resultIdx).read ≠ Γ.start := by
        rw [Tape.read, hhead]
        exact hcontent.cells_ne_start (head + 1) (by omega)
      have hstep := binaryRippleSubCoreTM_step_trim_true c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
        { state := .trim true
          input := c.input
          work := Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.left)
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        ih c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work resultIdx
              ((c.work resultIdx).move Dir3.left) i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work resultIdx
              ((c.work resultIdx).move Dir3.left) resultIdx).HasBinaryContent bits
            rw [Function.update_self]
            exact hcontent.move Dir3.left)
          (by
            show (Function.update c.work resultIdx
              ((c.work resultIdx).move Dir3.left) resultIdx).cells 0 = _
            rw [Function.update_self, Tape.move_cells]
            exact hcell0)
          (by
            show (Function.update c.work resultIdx
              ((c.work resultIdx).move Dir3.left) resultIdx).head = head
            rw [Function.update_self]
            simp [Tape.move, hhead])
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (TM.reachesIn.step hstep hreach)

private theorem binaryRippleSubCoreTM_erase_run
    (raw : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .erase)
    (hinput : c.input = inp₀)
    (hwork : ∀ i, i ≠ resultIdx → c.work i = work₀ i)
    (hcontent : (c.work resultIdx).HasBinaryContent raw)
    (hcell0 : (c.work resultIdx).cells 0 = Γ.start)
    (hhead : (c.work resultIdx).head = raw.length)
    (houtput : c.output = out₀) :
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (raw.length + 1) c c' ∧
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ resultIdx → c'.work i = work₀ i) ∧
      (c'.work resultIdx).HasBinaryString [] ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      c'.output = out₀ := by
  induction raw using List.reverseRecOn generalizing c with
  | nil =>
      have hread : (c.work resultIdx).read = Γ.start := by
        rw [Tape.read, hhead]
        exact hcell0
      have hstep := binaryRippleSubCoreTM_step_erase_start c hstate hread
        hhead (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
        { state := .done
          input := c.input
          work := Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right)
          output := c.output }
      refine ⟨c₁, .step hstep .zero, rfl, hinput, ?_, ?_, ?_, houtput⟩
      · intro i hi
        show Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).HasBinaryString []
        rw [Function.update_self]
        exact (hcontent.move Dir3.right).hasBinaryString (by simp [Tape.move, hhead])
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).cells 0 = _
        rw [Function.update_self, Tape.move_cells]
        exact hcell0
  | append_singleton bitsPrefix bit ih =>
      have hread : (c.work resultIdx).read = Γ.ofBool bit := by
        rw [Tape.read, hhead]
        have hcell := hcontent.1 bitsPrefix.length (by simp)
        simpa using hcell
      have hreadNe : (c.work resultIdx).read ≠ Γ.start := by
        rw [hread]
        exact Γ.ofBool_ne_start bit
      have hstep := binaryRippleSubCoreTM_step_erase c hstate hreadNe
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let target₁ : Tape :=
        ((c.work resultIdx).write Γ.blank).move Dir3.left
      let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
        { state := .erase
          input := c.input
          work := Function.update c.work resultIdx target₁
          output := c.output }
      have hshort :
          ((c.work resultIdx).write Γ.blank).HasBinaryContent bitsPrefix :=
        hcontent.write_blank_last_internal (by simpa using hhead)
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        ih c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work resultIdx target₁ i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work resultIdx target₁ resultIdx)
              |>.HasBinaryContent bitsPrefix
            rw [Function.update_self]
            exact hshort.move Dir3.left)
          (by
            show (Function.update c.work resultIdx target₁ resultIdx).cells 0 = _
            rw [Function.update_self]
            exact Tape.write_move_cell0 Γ.blank Dir3.left hcell0)
          (by
            show (Function.update c.work resultIdx target₁ resultIdx).head =
              bitsPrefix.length
            rw [Function.update_self]
            simp [target₁, Tape.move, Tape.write_head, hhead])
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩
      simpa [List.length_append, Nat.add_assoc] using
        (TM.reachesIn.step hstep hreach)

private theorem binaryRippleSubCoreTM_trim_false_run
    (raw : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (c : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q)
    (hstate : c.state = .trim false)
    (hinput : c.input = inp₀)
    (hwork : ∀ i, i ≠ resultIdx → c.work i = work₀ i)
    (hcontent : (c.work resultIdx).HasBinaryContent raw)
    (hcell0 : (c.work resultIdx).cells 0 = Γ.start)
    (hhead : (c.work resultIdx).head = raw.length)
    (houtput : c.output = out₀) :
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (raw.length + 1) c c' ∧
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ resultIdx → c'.work i = work₀ i) ∧
      (c'.work resultIdx).HasBinaryString
        (BinaryRippleSub.trimHighZeros raw) ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      c'.output = out₀ := by
  induction raw using List.reverseRecOn generalizing c with
  | nil =>
      have hread : (c.work resultIdx).read = Γ.start := by
        rw [Tape.read, hhead]
        exact hcell0
      have hstep := binaryRippleSubCoreTM_step_trim_start false c hstate hread
        hhead (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
        { state := .done
          input := c.input
          work := Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right)
          output := c.output }
      refine ⟨c₁, .step hstep .zero, rfl, hinput, ?_, ?_, ?_, houtput⟩
      · intro i hi
        show Function.update c.work resultIdx
          ((c.work resultIdx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).HasBinaryString
          (BinaryRippleSub.trimHighZeros [])
        rw [Function.update_self]
        simpa [BinaryRippleSub.trimHighZeros] using
          (hcontent.move Dir3.right).hasBinaryString (by simp [Tape.move, hhead])
      · show (Function.update c.work resultIdx
            ((c.work resultIdx).move Dir3.right) resultIdx).cells 0 = _
        rw [Function.update_self, Tape.move_cells]
        exact hcell0
  | append_singleton bitsPrefix bit ih =>
      have hread : (c.work resultIdx).read = Γ.ofBool bit := by
        rw [Tape.read, hhead]
        have hcell := hcontent.1 bitsPrefix.length (by simp)
        simpa using hcell
      cases bit with
      | false =>
          have hreadZero : (c.work resultIdx).read = Γ.zero := by
            simpa [Γ.ofBool] using hread
          have hstep := binaryRippleSubCoreTM_step_trim_false_zero c hstate
            hreadZero (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target₁ : Tape :=
            ((c.work resultIdx).write Γ.blank).move Dir3.left
          let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
            { state := .trim false
              input := c.input
              work := Function.update c.work resultIdx target₁
              output := c.output }
          have hshort :
              ((c.work resultIdx).write Γ.blank).HasBinaryContent bitsPrefix :=
            hcontent.write_blank_last_internal (by simpa using hhead)
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            ih c₁ rfl hinput
              (fun i hi => by
                show Function.update c.work resultIdx target₁ i = work₀ i
                rw [Function.update_of_ne hi]
                exact hwork i hi)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx)
                  |>.HasBinaryContent bitsPrefix
                rw [Function.update_self]
                exact hshort.move Dir3.left)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx).cells 0 = _
                rw [Function.update_self]
                exact Tape.write_move_cell0 Γ.blank Dir3.left hcell0)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx).head =
                  bitsPrefix.length
                rw [Function.update_self]
                simp [target₁, Tape.move, Tape.write_head, hhead])
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · simpa [List.length_append, Nat.add_assoc] using
              (TM.reachesIn.step hstep hreach)
          · simpa [BinaryRippleSub.trimHighZeros_append_false_internal] using hstring
      | true =>
          have hreadOne : (c.work resultIdx).read = Γ.one := by
            simpa [Γ.ofBool] using hread
          have hstep := binaryRippleSubCoreTM_step_trim_false_one c hstate
            hreadOne (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target₁ : Tape := (c.work resultIdx).move Dir3.left
          let c₁ : Cfg n (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).Q :=
            { state := .trim true
              input := c.input
              work := Function.update c.work resultIdx target₁
              output := c.output }
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            binaryRippleSubCoreTM_trim_true_run (lhsIdx := lhsIdx)
              (rhsIdx := rhsIdx) (resultIdx := resultIdx) (bitsPrefix ++ [true])
              inp₀ work₀ out₀ hinp hother hout bitsPrefix.length c₁ rfl hinput
              (fun i hi => by
                show Function.update c.work resultIdx target₁ i = work₀ i
                rw [Function.update_of_ne hi]
                exact hwork i hi)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx)
                  |>.HasBinaryContent (bitsPrefix ++ [true])
                rw [Function.update_self]
                exact hcontent.move Dir3.left)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx).cells 0 = _
                rw [Function.update_self, Tape.move_cells]
                exact hcell0)
              (by
                show (Function.update c.work resultIdx target₁ resultIdx).head =
                  bitsPrefix.length
                rw [Function.update_self]
                simp [target₁, Tape.move, hhead])
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · simpa [List.length_append, Nat.add_assoc] using
              (TM.reachesIn.step hstep hreach)
          · simpa [BinaryRippleSub.trimHighZeros_append_true_internal] using hstring

/-- Exact framed backward cleanup after the forward scan has turned the result
head left. A final borrow erases the entire raw result; otherwise all and only
its redundant high zeros are erased. -/
theorem binaryRippleSubCoreTM_cleanup_run_internal
    (lhsIdx rhsIdx resultIdx : Fin n)
    (raw : List Bool) (borrow : Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ resultIdx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hcontent : (work₀ resultIdx).HasBinaryContent raw)
    (hcell0 : (work₀ resultIdx).cells 0 = Γ.start)
    (hhead : (work₀ resultIdx).head = raw.length) :
    ∃ c',
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).reachesIn
        (raw.length + 1)
        { state := if borrow then .erase else .trim false
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryRippleSubCoreTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ resultIdx → c'.work i = work₀ i) ∧
      (c'.work resultIdx).HasBinaryString
        (if borrow then [] else BinaryRippleSub.trimHighZeros raw) ∧
      (c'.work resultIdx).cells 0 = Γ.start ∧
      c'.output = out₀ := by
  cases borrow with
  | false =>
      simpa using binaryRippleSubCoreTM_trim_false_run
        (lhsIdx := lhsIdx) (rhsIdx := rhsIdx) (resultIdx := resultIdx)
        raw inp₀ work₀ out₀ hinp hother hout
        { state := .trim false, input := inp₀, work := work₀, output := out₀ }
        rfl rfl (fun _ _ => rfl) hcontent hcell0 hhead rfl
  | true =>
      simpa using binaryRippleSubCoreTM_erase_run
        (lhsIdx := lhsIdx) (rhsIdx := rhsIdx) (resultIdx := resultIdx)
        raw inp₀ work₀ out₀ hinp hother hout
        { state := .erase, input := inp₀, work := work₀, output := out₀ }
        rfl rfl (fun _ _ => rfl) hcontent hcell0 hhead rfl

end TM

end Complexity
