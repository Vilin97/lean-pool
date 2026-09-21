/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic

/-!
# Little-endian binary predecessor — proof internals

This file proves pure ripple-borrow semantics and the exact full-frame
execution of `TM.binaryPredTM`. The machine proof tracks the already-borrowed
low-order prefix independently of the target head, including the canonical
high-bit erasure needed when decrementing a power of two.
-/


public section

namespace Complexity

namespace BinaryPred

/-- Internal proof that ripple borrow on a positive canonical value computes
its predecessor. -/
theorem ripple_succ_natBits_internal (value : ℕ) :
    ripple (value + 1).bits = value.bits := by
  induction value using Nat.binaryRec' with
  | zero => simp [ripple]
  | bit bit value hcanonical ih =>
      rw [Nat.bits_append_bit value bit hcanonical]
      cases bit with
      | false =>
          have hvalue : value ≠ 0 := by
            intro hzero
            have := hcanonical hzero
            contradiction
          rw [show Nat.bit false value + 1 = Nat.bit true value by
            simp [Nat.bit]]
          rw [Nat.bits_append_bit value true (fun _ => rfl)]
          cases hbits : value.bits with
          | nil =>
              exfalso
              apply hvalue
              have hdecoded := Nat.fromBitsLE_bits value
              rw [hbits] at hdecoded
              simpa [Nat.fromBitsLE, Nat.fromBits] using hdecoded.symm
          | cons first rest => simp [ripple]
      | true =>
          rw [show Nat.bit true value + 1 = Nat.bit false (value + 1) by
            simp [Nat.bit]
            omega]
          rw [Nat.bits_append_bit (value + 1) false (by omega)]
          simp only [ripple]
          rw [ih]

/-- Internal worst-case bound for predecessor's exact transition count. -/
theorem steps_le_internal (bits : List Bool) :
    steps bits ≤ 2 * bits.length + 2 := by
  induction bits with
  | nil => simp [steps]
  | cons bit bits ih =>
      cases bit
      · simp only [steps, List.length_cons]
        omega
      · simp [steps]

end BinaryPred

namespace Tape

private theorem HasBinaryContent.binaryPred_read_cons {t : Tape} {done : ℕ}
    {bit : Bool} {rest : List Bool}
    (h : t.HasBinaryContent (List.replicate done true ++ bit :: rest))
    (hhead : t.head = done + 1) : t.read = Γ.ofBool bit := by
  rw [Tape.read, hhead]
  have hcell := h.1 done (by simp)
  simpa using hcell

private theorem HasBinaryContent.binaryPred_read_nil {t : Tape} {done : ℕ}
    (h : t.HasBinaryContent (List.replicate done true))
    (hhead : t.head = done + 1) : t.read = Γ.blank := by
  rw [Tape.read, hhead]
  exact h.2 done (by simp)

/-- Replacing the last represented bit by blank shortens canonical contents. -/
private theorem HasBinaryContent.binaryPred_erase_last {t : Tape}
    {bitsPrefix : List Bool}
    (h : t.HasBinaryContent (bitsPrefix ++ [false]))
    (hhead : t.head = bitsPrefix.length + 1) :
    (t.write Γ.blank).HasBinaryContent bitsPrefix := by
  have hhead0 : t.head ≠ 0 := by omega
  constructor
  · intro i hi
    rw [Tape.write, if_neg hhead0]
    simp only
    rw [hhead, Function.update_of_ne (by omega)]
    have hcell := h.1 i (by simp; omega)
    simpa [List.getElem_append, hi] using hcell
  · intro i hi
    rw [Tape.write, if_neg hhead0]
    simp only
    rw [hhead]
    by_cases heq : i = bitsPrefix.length
    · subst i
      rw [Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact h.2 i (by simp; omega)

end Tape

namespace BinaryPred

private theorem set_false_to_true (done : ℕ) (rest : List Bool) :
    (List.replicate done true ++ false :: rest).set done true =
      List.replicate (done + 1) true ++ rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change true :: (List.replicate done true ++ false :: rest).set done true =
        true :: true :: (List.replicate done true ++ rest)
      congr 1

private theorem set_true_to_false (done : ℕ) (rest : List Bool) :
    (List.replicate done true ++ true :: rest).set done false =
      List.replicate done true ++ false :: rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change true :: (List.replicate done true ++ true :: rest).set done false =
        true :: (List.replicate done true ++ false :: rest)
      congr 1

end BinaryPred

namespace TM

variable {n : ℕ} {idx : Fin n}

private theorem binaryPredTM_ne_halt {phase : BinaryPredPhase}
    (hne : phase ≠ .done) {c : Cfg n (binaryPredTM idx).Q}
    (hstate : c.state = phase) :
    c.state ≠ (binaryPredTM idx).qhalt := by
  rw [hstate]
  exact hne

/-- Propagate borrow over one low-order zero. -/
private theorem binaryPredTM_step_zero (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .borrow) (hread : (c.work idx).read = Γ.zero)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .borrow
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.one).move Dir3.right)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [if_neg hi] using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Resolve borrow at the first one and advance to lookahead. -/
private theorem binaryPredTM_step_one (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .borrow) (hread : (c.work idx).read = Γ.one)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .check
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.zero).move Dir3.right)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [if_neg hi] using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Define zero underflow by turning left from the terminating blank. -/
private theorem binaryPredTM_step_borrow_blank
    (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .borrow) (hread : (c.work idx).read = Γ.blank)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      rw [if_pos rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hread]; decide)]
    · rw [if_neg hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- A nonblank lookahead turns left and begins rewinding. -/
private theorem binaryPredTM_step_check_bit (bit : Bool)
    (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .check)
    (hread : (c.work idx).read = Γ.ofBool bit)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  cases bit <;> simp only [Γ.ofBool, binaryPredTM, hstate, hread]
  all_goals
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
    · exact transitionInput_eq_self hinput
    · funext i
      by_cases hi : i = idx
      · subst i
        rw [if_pos rfl, Function.update_self,
          writeAndMove_readBack _ (by rw [hread]; decide)]
      · rw [if_neg hi, Function.update_of_ne hi]
        exact transitionTape_eq_self (hother i hi)
    · exact transitionTape_eq_self houtput

/-- A blank lookahead identifies a vacated unique high bit. -/
private theorem binaryPredTM_step_check_blank
    (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .check) (hread : (c.work idx).read = Γ.blank)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .erase
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      rw [if_pos rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hread]; decide)]
    · rw [if_neg hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Erase the vacated high zero and turn left. -/
private theorem binaryPredTM_step_erase (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .erase) (hread : (c.work idx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.blank).move Dir3.left)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [if_neg hi] using transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Rewind one ordinary target cell to the left. -/
private theorem binaryPredTM_step_rewind (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      rw [if_pos rfl, Function.update_self,
        writeAndMove_readBack _ hread]
    · rw [if_neg hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Bounce right from the left marker and halt. -/
private theorem binaryPredTM_step_start (c : Cfg n (binaryPredTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read = Γ.start)
    (hhead : (c.work idx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binaryPredTM idx).step c = some
      { state := .done
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, if_neg (binaryPredTM_ne_halt (by decide) hstate)]
  simp only [binaryPredTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      show (((c.work idx).write _).move Dir3.right) =
        (c.work idx).move Dir3.right
      rw [Tape.write, if_pos hhead]
    · rw [if_neg hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-! ## Exact rewind and borrow runs -/

private theorem binaryPredTM_rewind_run (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ head (c : Cfg n (binaryPredTM idx).Q),
      c.state = .rewind →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent bits →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = head →
      c.output = out₀ →
      ∃ c',
        (binaryPredTM idx).reachesIn (head + 1) c c' ∧
        (binaryPredTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).HasBinaryString bits ∧
        (c'.work idx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro head
  induction head with
  | zero =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work idx).read = Γ.start := by
        rw [Tape.read, hhead]
        exact hcell0
      have hstep := binaryPredTM_step_start c hstate hread hhead
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryPredTM idx).Q :=
        { state := .done
          input := c.input
          work := Function.update c.work idx ((c.work idx).move Dir3.right)
          output := c.output }
      refine ⟨c₁, .step hstep .zero, rfl, hinput, ?_, ?_, ?_, houtput⟩
      · intro i hi
        show Function.update c.work idx ((c.work idx).move Dir3.right) i = work₀ i
        rw [Function.update_of_ne hi]
        exact hwork i hi
      · show (Function.update c.work idx ((c.work idx).move Dir3.right) idx)
            |>.HasBinaryString bits
        rw [Function.update_self]
        apply Tape.HasBinaryContent.hasBinaryString
        · simpa only [Tape.HasBinaryContent, Tape.move_cells] using hcontent
        · simp [Tape.move, hhead]
      · show (Function.update c.work idx ((c.work idx).move Dir3.right) idx).cells 0 = _
        rw [Function.update_self, Tape.move_cells]
        exact hcell0
  | succ head ih =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hread : (c.work idx).read ≠ Γ.start := by
        rw [Tape.read, hhead]
        exact hcontent.cells_ne_start (head + 1) (by omega)
      have hstep := binaryPredTM_step_rewind c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binaryPredTM idx).Q :=
        { state := .rewind
          input := c.input
          work := Function.update c.work idx ((c.work idx).move Dir3.left)
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        ih c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work idx ((c.work idx).move Dir3.left) i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx)
              |>.HasBinaryContent bits
            rw [Function.update_self]
            simpa only [Tape.HasBinaryContent, Tape.move_cells] using hcontent)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx).cells 0 = _
            rw [Function.update_self, Tape.move_cells]
            exact hcell0)
          (by
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx).head =
              head
            rw [Function.update_self]
            simp [Tape.move, hhead])
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (TM.reachesIn.step hstep hreach)

private theorem binaryPredTM_borrow_run
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ done bits (c : Cfg n (binaryPredTM idx).Q),
      c.state = .borrow →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent (List.replicate done true ++ bits) →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = done + 1 →
      c.output = out₀ →
      ∃ c',
        (binaryPredTM idx).reachesIn (done + BinaryPred.steps bits) c c' ∧
        (binaryPredTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).HasBinaryString
          (List.replicate done true ++ BinaryPred.ripple bits) ∧
        (c'.work idx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro done bits
  induction bits generalizing done with
  | nil =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hcontent' :
          (c.work idx).HasBinaryContent (List.replicate done true) := by
        simpa using hcontent
      have hread : (c.work idx).read = Γ.blank :=
        hcontent'.binaryPred_read_nil hhead
      have hstep := binaryPredTM_step_borrow_blank c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let target : Tape := (c.work idx).move Dir3.left
      have htargetContent :
          target.HasBinaryContent (List.replicate done true) := by
        simpa only [target] using hcontent'.move Dir3.left
      have htargetCell0 : target.cells 0 = Γ.start := by
        simpa [target, Tape.move_cells] using hcell0
      have htargetHead : target.head = done := by
        simp [target, Tape.move, hhead]
      let c₁ : Cfg n (binaryPredTM idx).Q :=
        { state := .rewind
          input := c.input
          work := Function.update c.work idx target
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        binaryPredTM_rewind_run (idx := idx) (List.replicate done true)
          inp₀ work₀ out₀ hinp hother hout done c₁ rfl hinput
          (fun i hi => by
            show Function.update c.work idx target i = work₀ i
            rw [Function.update_of_ne hi]
            exact hwork i hi)
          (by
            show (Function.update c.work idx target idx).HasBinaryContent _
            rw [Function.update_self]
            exact htargetContent)
          (by
            show (Function.update c.work idx target idx).cells 0 = _
            rw [Function.update_self]
            exact htargetCell0)
          (by
            show (Function.update c.work idx target idx).head = done
            rw [Function.update_self]
            exact htargetHead)
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
      · simpa [BinaryPred.steps, Nat.add_assoc] using
          (TM.reachesIn.step hstep hreach)
      · simpa [BinaryPred.ripple] using hstring
  | cons bit rest ih =>
      cases bit with
      | false =>
          intro c hstate hinput hwork hcontent hcell0 hhead houtput
          have hread : (c.work idx).read = Γ.zero :=
            hcontent.binaryPred_read_cons hhead
          have hstep := binaryPredTM_step_zero c hstate hread
            (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target : Tape := ((c.work idx).write Γ.one).move Dir3.right
          have htargetContent : target.HasBinaryContent
              (List.replicate (done + 1) true ++ rest) := by
            have hwrite := hcontent.write_set true hhead (by simp)
            rw [BinaryPred.set_false_to_true] at hwrite
            simpa only [target, Tape.HasBinaryContent, Tape.move_cells] using
              hwrite
          have htargetCell0 : target.cells 0 = Γ.start := by
            exact Tape.write_move_cell0 Γ.one Dir3.right hcell0
          have htargetHead : target.head = (done + 1) + 1 := by
            simp [target, Tape.move, Tape.write_head, hhead]
          let c₁ : Cfg n (binaryPredTM idx).Q :=
            { state := .borrow
              input := c.input
              work := Function.update c.work idx target
              output := c.output }
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            ih (done + 1) c₁ rfl hinput
              (fun i hi => by
                show Function.update c.work idx target i = work₀ i
                rw [Function.update_of_ne hi]
                exact hwork i hi)
              (by
                show (Function.update c.work idx target idx).HasBinaryContent _
                rw [Function.update_self]
                exact htargetContent)
              (by
                show (Function.update c.work idx target idx).cells 0 = _
                rw [Function.update_self]
                exact htargetCell0)
              (by
                show (Function.update c.work idx target idx).head =
                  (done + 1) + 1
                rw [Function.update_self]
                exact htargetHead)
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · convert TM.reachesIn.step hstep hreach using 1
            all_goals simp [BinaryPred.steps, Nat.add_assoc]
            all_goals omega
          · simpa [BinaryPred.ripple, List.replicate_add,
              List.append_assoc] using hstring
      | true =>
          cases rest with
          | nil =>
              intro c hstate hinput hwork hcontent hcell0 hhead houtput
              have hread : (c.work idx).read = Γ.one :=
                hcontent.binaryPred_read_cons hhead
              have hstep := binaryPredTM_step_one c hstate hread
                (by rw [hinput]; exact hinp)
                (fun i hi => by rw [hwork i hi]; exact hother i hi)
                (by rw [houtput]; exact hout)
              let target₁ : Tape :=
                ((c.work idx).write Γ.zero).move Dir3.right
              have htarget₁Content : target₁.HasBinaryContent
                  (List.replicate done true ++ [false]) := by
                have hwrite := hcontent.write_set false hhead (by simp)
                rw [BinaryPred.set_true_to_false] at hwrite
                simpa only [target₁, Tape.HasBinaryContent, Tape.move_cells]
                  using hwrite
              have htarget₁Cell0 : target₁.cells 0 = Γ.start := by
                exact Tape.write_move_cell0 Γ.zero Dir3.right hcell0
              have htarget₁Head : target₁.head = done + 2 := by
                simp [target₁, Tape.move, Tape.write_head, hhead]
              have htarget₁Read : target₁.read = Γ.blank := by
                rw [Tape.read, htarget₁Head]
                exact htarget₁Content.2 (done + 1) (by simp)
              let c₁ : Cfg n (binaryPredTM idx).Q :=
                { state := .check
                  input := c.input
                  work := Function.update c.work idx target₁
                  output := c.output }
              have hcheck := binaryPredTM_step_check_blank c₁ rfl
                (by simpa [c₁] using htarget₁Read)
                (by rw [hinput]; exact hinp)
                (fun i hi => by
                  simp only [c₁, Function.update_of_ne hi]
                  rw [hwork i hi]
                  exact hother i hi)
                (by rw [houtput]; exact hout)
              let target₂ : Tape := target₁.move Dir3.left
              have htarget₂Content : target₂.HasBinaryContent
                  (List.replicate done true ++ [false]) := by
                simpa only [target₂] using htarget₁Content.move Dir3.left
              have htarget₂Cell0 : target₂.cells 0 = Γ.start := by
                simpa [target₂, Tape.move_cells] using htarget₁Cell0
              have htarget₂Head : target₂.head = done + 1 := by
                simp [target₂, Tape.move, htarget₁Head]
              have htarget₂Read : target₂.read ≠ Γ.start :=
                htarget₂Content.cells_ne_start target₂.head (by
                  rw [htarget₂Head]
                  omega)
              let c₂ : Cfg n (binaryPredTM idx).Q :=
                { state := .erase
                  input := c.input
                  work := Function.update c.work idx target₂
                  output := c.output }
              have herase := binaryPredTM_step_erase c₂ rfl
                (by simpa [c₂] using htarget₂Read)
                (by rw [hinput]; exact hinp)
                (fun i hi => by
                  simp only [c₂, Function.update_of_ne hi]
                  rw [hwork i hi]
                  exact hother i hi)
                (by rw [houtput]; exact hout)
              let target₃ : Tape :=
                (target₂.write Γ.blank).move Dir3.left
              have htarget₃Content :
                  target₃.HasBinaryContent (List.replicate done true) := by
                have herased := htarget₂Content.binaryPred_erase_last (by
                  simpa using htarget₂Head)
                simpa only [target₃] using herased.move Dir3.left
              have htarget₃Cell0 : target₃.cells 0 = Γ.start := by
                exact Tape.write_move_cell0 Γ.blank Dir3.left htarget₂Cell0
              have htarget₃Head : target₃.head = done := by
                simp [target₃, Tape.move, Tape.write_head, htarget₂Head]
              let c₃ : Cfg n (binaryPredTM idx).Q :=
                { state := .rewind
                  input := c.input
                  work := Function.update c.work idx target₃
                  output := c.output }
              have hcheck' : (binaryPredTM idx).step c₁ = some c₂ := by
                simpa [c₁, c₂, target₂] using hcheck
              have herase' : (binaryPredTM idx).step c₂ = some c₃ := by
                simpa [c₂, c₃, target₃] using herase
              obtain ⟨c', hreach, hhalt, hinput', hwork', hstring,
                  hcell0', houtput'⟩ :=
                binaryPredTM_rewind_run (idx := idx)
                  (List.replicate done true) inp₀ work₀ out₀ hinp hother
                  hout done c₃ rfl hinput
                  (fun i hi => by
                    show Function.update c.work idx target₃ i = work₀ i
                    rw [Function.update_of_ne hi]
                    exact hwork i hi)
                  (by
                    show (Function.update c.work idx target₃ idx)
                      |>.HasBinaryContent _
                    rw [Function.update_self]
                    exact htarget₃Content)
                  (by
                    show (Function.update c.work idx target₃ idx).cells 0 = _
                    rw [Function.update_self]
                    exact htarget₃Cell0)
                  (by
                    show (Function.update c.work idx target₃ idx).head = done
                    rw [Function.update_self]
                    exact htarget₃Head)
                  houtput
              have hprefix : (binaryPredTM idx).reachesIn 3 c c₃ := by
                exact .step hstep (.step hcheck' (.step herase' .zero))
              refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
              · have hrun := reachesIn_trans (binaryPredTM idx) hprefix hreach
                convert hrun using 1
                all_goals simp [BinaryPred.steps]
                all_goals omega
              · simpa [BinaryPred.ripple] using hstring
          | cons next rest =>
              intro c hstate hinput hwork hcontent hcell0 hhead houtput
              have hread : (c.work idx).read = Γ.one :=
                hcontent.binaryPred_read_cons hhead
              have hstep := binaryPredTM_step_one c hstate hread
                (by rw [hinput]; exact hinp)
                (fun i hi => by rw [hwork i hi]; exact hother i hi)
                (by rw [houtput]; exact hout)
              let target₁ : Tape :=
                ((c.work idx).write Γ.zero).move Dir3.right
              have htarget₁Content : target₁.HasBinaryContent
                  (List.replicate done true ++ false :: next :: rest) := by
                have hwrite := hcontent.write_set false hhead (by simp)
                rw [BinaryPred.set_true_to_false] at hwrite
                simpa only [target₁, Tape.HasBinaryContent, Tape.move_cells]
                  using hwrite
              have htarget₁Cell0 : target₁.cells 0 = Γ.start := by
                exact Tape.write_move_cell0 Γ.zero Dir3.right hcell0
              have htarget₁Head : target₁.head = done + 2 := by
                simp [target₁, Tape.move, Tape.write_head, hhead]
              have htarget₁Read : target₁.read = Γ.ofBool next := by
                rw [Tape.read, htarget₁Head]
                have hcell := htarget₁Content.1 (done + 1) (by simp)
                simpa [List.getElem_append] using hcell
              let c₁ : Cfg n (binaryPredTM idx).Q :=
                { state := .check
                  input := c.input
                  work := Function.update c.work idx target₁
                  output := c.output }
              have hcheck := binaryPredTM_step_check_bit next c₁ rfl
                (by simpa [c₁] using htarget₁Read)
                (by rw [hinput]; exact hinp)
                (fun i hi => by
                  simp only [c₁, Function.update_of_ne hi]
                  rw [hwork i hi]
                  exact hother i hi)
                (by rw [houtput]; exact hout)
              let target₂ : Tape := target₁.move Dir3.left
              have htarget₂Content : target₂.HasBinaryContent
                  (List.replicate done true ++ false :: next :: rest) := by
                simpa only [target₂] using htarget₁Content.move Dir3.left
              have htarget₂Cell0 : target₂.cells 0 = Γ.start := by
                simpa [target₂, Tape.move_cells] using htarget₁Cell0
              have htarget₂Head : target₂.head = done + 1 := by
                simp [target₂, Tape.move, htarget₁Head]
              let c₂ : Cfg n (binaryPredTM idx).Q :=
                { state := .rewind
                  input := c.input
                  work := Function.update c.work idx target₂
                  output := c.output }
              have hcheck' : (binaryPredTM idx).step c₁ = some c₂ := by
                simpa [c₁, c₂, target₂] using hcheck
              obtain ⟨c', hreach, hhalt, hinput', hwork', hstring,
                  hcell0', houtput'⟩ :=
                binaryPredTM_rewind_run (idx := idx)
                  (List.replicate done true ++ false :: next :: rest)
                  inp₀ work₀ out₀ hinp hother hout (done + 1) c₂ rfl hinput
                  (fun i hi => by
                    show Function.update c.work idx target₂ i = work₀ i
                    rw [Function.update_of_ne hi]
                    exact hwork i hi)
                  (by
                    show (Function.update c.work idx target₂ idx)
                      |>.HasBinaryContent _
                    rw [Function.update_self]
                    exact htarget₂Content)
                  (by
                    show (Function.update c.work idx target₂ idx).cells 0 = _
                    rw [Function.update_self]
                    exact htarget₂Cell0)
                  (by
                    show (Function.update c.work idx target₂ idx).head = done + 1
                    rw [Function.update_self]
                    exact htarget₂Head)
                  houtput
              have hprefix : (binaryPredTM idx).reachesIn 2 c c₂ := by
                exact .step hstep (.step hcheck' .zero)
              refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
              · have hrun := reachesIn_trans (binaryPredTM idx) hprefix hreach
                convert hrun using 1
                all_goals simp [BinaryPred.steps]
                all_goals omega
              · simpa [BinaryPred.ripple] using hstring

/-! ## Public-theorem internals -/

theorem binaryPredTime_le_internal (value : ℕ) :
    binaryPredTime value ≤ 2 * (value + 1).size + 2 := by
  simpa [binaryPredTime, Nat.size_eq_bits_len] using
    BinaryPred.steps_le_internal (value + 1).bits

theorem binaryPredTM_reachesIn_frame_internal
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryPredTM idx).reachesIn (binaryPredTime value)
        { state := (binaryPredTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryPredTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryNat value ∧
      c'.output = out₀ := by
  let c₀ : Cfg n (binaryPredTM idx).Q :=
    { state := (binaryPredTM idx).qstart
      input := inp₀
      work := work₀
      output := out₀ }
  obtain ⟨c', hreach, hhalt, hinput, hwork, hstring, hcell0, houtput⟩ :=
    binaryPredTM_borrow_run (idx := idx) inp₀ work₀ out₀ hinp hother hout
      0 (value + 1).bits c₀ (by rfl) (by rfl) (fun _ _ => rfl)
      (by simpa [c₀] using hvalue.2.hasBinaryContent) hvalue.1
      (by simpa [c₀] using hvalue.2.1) (by rfl)
  refine ⟨c', ?_, hhalt, hinput, hwork, ?_, houtput⟩
  · simpa [c₀, binaryPredTime] using hreach
  · exact ⟨hcell0, by
      simpa [BinaryPred.ripple_succ_natBits_internal] using hstring⟩

theorem binaryPredTM_hoareTime_frame_internal
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryPredTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat value ∧
        out = out₀)
      (binaryPredTime value) := by
  rintro inp work out ⟨hinput₀, hwork₀, houtput₀⟩
  obtain ⟨c', hreach, hhalt, hinput, hwork, hvalue', houtput⟩ :=
    binaryPredTM_reachesIn_frame_internal idx value inp₀ work₀ out₀
      hvalue hinp hother hout
  refine ⟨c', binaryPredTime value, le_rfl, ?_, hhalt,
    hinput, hwork, hvalue', houtput⟩
  simpa [hinput₀, hwork₀, houtput₀] using hreach

theorem binaryPredTM_hoareTimeSpace_frame_internal
    (idx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat (value + 1))
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binaryPredTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binaryPredTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (binaryPredTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat value ∧
        out = out₀)
      (binaryPredTime value) inputLength
      (binaryPredSpace initialSpace value) := by
  have htimeSpace :=
    (binaryPredTM_hoareTime_frame_internal idx value inp₀ work₀ out₀
      hvalue hinp hother hout).toHoareTimeSpace (by
        rintro inp work out ⟨hinput₀, hwork₀, houtput₀⟩
        simpa [hinput₀, hwork₀, houtput₀] using hinitial)
  refine htimeSpace.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    le_rfl le_rfl ?_
  have htime := binaryPredTime_le_internal value
  simp only [binaryPredSpace]
  omega

theorem binaryPredTM_isTransducer_internal (idx : Fin n) :
    (binaryPredTM idx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | borrow =>
      cases hread : wHeads idx <;>
        simp [binaryPredTM, hread, idleDir] <;>
        split <;> decide
  | check =>
      cases hread : wHeads idx <;>
        simp [binaryPredTM, hread, idleDir] <;>
        split <;> decide
  | erase =>
      simp only [binaryPredTM]
      split <;> simp [idleDir] <;> split <;> decide
  | rewind =>
      simp only [binaryPredTM]
      split <;> simp [idleDir] <;> split <;> decide
  | done =>
      simp [binaryPredTM, allIdle, idleDir]
      split <;> decide

end TM

end Complexity
