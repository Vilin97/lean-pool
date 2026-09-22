/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
public import Mathlib.Data.Nat.Size

/-!
# Little-endian binary successor — proof internals

This file proves the pure ripple semantics and the exact full-frame execution
of `TM.binarySuccTM`. The carry proof uses a private head-independent binary
content predicate, generalized over the already-zeroed low-order prefix.
-/


public section

namespace Complexity

namespace BinarySucc

/-- Internal proof that ripple carry computes successor on canonical
little-endian natural-number bits. -/
theorem ripple_natBits_internal (value : ℕ) :
    ripple value.bits = (value + 1).bits := by
  induction value using Nat.binaryRec' with
  | zero => simp [ripple]
  | bit bit value hvalue ih =>
      rw [Nat.bits_append_bit value bit hvalue]
      cases bit
      · simp [ripple, Nat.bit]
      · simp only [ripple]
        rw [show Nat.bit true value + 1 = 2 * (value + 1) by
          simp [Nat.bit, Nat.mul_add]]
        rw [Nat.bit0_bits (value + 1) (Nat.succ_ne_zero value)]
        rw [ih]

/-- Internal worst-case bound for the exact successor step count. -/
theorem steps_le_internal (bits : List Bool) :
    steps bits ≤ 2 * bits.length + 2 := by
  induction bits with
  | nil => simp [steps]
  | cons bit bits ih =>
      cases bit
      · simp [steps]
      · simp only [steps, List.length_cons]
        omega

end BinarySucc

namespace Tape

private theorem HasBinaryContent.read_cons {t : Tape} {done : ℕ}
    {bit : Bool} {rest : List Bool}
    (h : t.HasBinaryContent (List.replicate done false ++ bit :: rest))
    (hhead : t.head = done + 1) : t.read = Γ.ofBool bit := by
  rw [Tape.read, hhead]
  have hcell := h.1 done (by simp)
  simpa using hcell

private theorem HasBinaryContent.read_nil {t : Tape} {done : ℕ}
    (h : t.HasBinaryContent (List.replicate done false))
    (hhead : t.head = done + 1) : t.read = Γ.blank := by
  rw [Tape.read, hhead]
  exact h.2 done (by simp)

end Tape

namespace BinarySucc

private theorem set_true_to_false (done : ℕ) (rest : List Bool) :
    (List.replicate done false ++ true :: rest).set done false =
      List.replicate (done + 1) false ++ rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change false :: (List.replicate done false ++ true :: rest).set done false =
        false :: false :: (List.replicate done false ++ rest)
      congr 1

private theorem set_false_to_true (done : ℕ) (rest : List Bool) :
    (List.replicate done false ++ false :: rest).set done true =
      List.replicate done false ++ true :: rest := by
  induction done with
  | zero => rfl
  | succ done ih =>
      change false :: (List.replicate done false ++ false :: rest).set done true =
        false :: (List.replicate done false ++ true :: rest)
      congr 1

end BinarySucc

namespace TM

variable {n : ℕ} {idx : Fin n}

private theorem binarySuccTM_ne_halt {phase : BinarySuccPhase}
    (hne : phase ≠ .done) {c : Cfg n (binarySuccTM idx).Q}
    (hstate : c.state = phase) :
    c.state ≠ (binarySuccTM idx).qhalt := by
  rw [hstate]
  exact hne

/-- Carry over one low-order one: write zero and advance right. -/
private theorem binarySuccTM_step_one (c : Cfg n (binarySuccTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.one)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binarySuccTM idx).step c = some
      { state := .carry
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.zero).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binarySuccTM_ne_halt (by decide) hstate)]
  simp only [binarySuccTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [ite_eq_right hi] using! transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Resolve a carry on zero: write one and turn left. -/
private theorem binarySuccTM_step_zero (c : Cfg n (binarySuccTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.zero)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binarySuccTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.one).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binarySuccTM_ne_halt (by decide) hstate)]
  simp only [binarySuccTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [ite_eq_right hi] using! transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Resolve overflow on the terminating blank: append one and turn left. -/
private theorem binarySuccTM_step_blank (c : Cfg n (binarySuccTM idx).Q)
    (hstate : c.state = .carry) (hread : (c.work idx).read = Γ.blank)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binarySuccTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx
          (((c.work idx).write Γ.one).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binarySuccTM_ne_halt (by decide) hstate)]
  simp only [binarySuccTM, hstate, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      rfl
    · rw [Function.update_of_ne hi]
      simpa only [ite_eq_right hi] using! transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Rewind one ordinary target cell to the left. -/
private theorem binarySuccTM_step_rewind (c : Cfg n (binarySuccTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read ≠ Γ.start)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binarySuccTM idx).step c = some
      { state := .rewind
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.left)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binarySuccTM_ne_halt (by decide) hstate)]
  simp only [binarySuccTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ hread]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-- Bounce right from the left marker and halt. -/
private theorem binarySuccTM_step_start (c : Cfg n (binarySuccTM idx).Q)
    (hstate : c.state = .rewind) (hread : (c.work idx).read = Γ.start)
    (hhead : (c.work idx).head = 0)
    (hinput : c.input.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (binarySuccTM idx).step c = some
      { state := .done
        input := c.input
        work := Function.update c.work idx ((c.work idx).move Dir3.right)
        output := c.output } := by
  rw [TM.step, ite_eq_right (binarySuccTM_ne_halt (by decide) hstate)]
  simp only [binarySuccTM, hstate, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    by_cases hi : i = idx
    · subst i
      simp only [↓reduceIte, Function.update_self]
      show (((c.work idx).write _).move Dir3.right) =
        (c.work idx).move Dir3.right
      rw [Tape.write, ite_eq_left hhead]
    · rw [ite_eq_right hi, Function.update_of_ne hi]
      exact transitionTape_eq_self (hother i hi)
  · exact transitionTape_eq_self houtput

/-! ## Exact rewind and carry runs -/

private theorem binarySuccTM_rewind_run (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ head (c : Cfg n (binarySuccTM idx).Q),
      c.state = .rewind →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent bits →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = head →
      c.output = out₀ →
      ∃ c',
        (binarySuccTM idx).reachesIn (head + 1) c c' ∧
        (binarySuccTM idx).halted c' ∧
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
      have hstep := binarySuccTM_step_start c hstate hread hhead
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binarySuccTM idx).Q :=
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
      have hstep := binarySuccTM_step_rewind c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let c₁ : Cfg n (binarySuccTM idx).Q :=
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
            show (Function.update c.work idx ((c.work idx).move Dir3.left) idx).head = head
            rw [Function.update_self]
            simp [Tape.move, hhead])
          houtput
      refine ⟨c', ?_, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        (TM.reachesIn.step hstep hreach)

private theorem binarySuccTM_carry_run
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∀ done bits (c : Cfg n (binarySuccTM idx).Q),
      c.state = .carry →
      c.input = inp₀ →
      (∀ i, i ≠ idx → c.work i = work₀ i) →
      (c.work idx).HasBinaryContent (List.replicate done false ++ bits) →
      (c.work idx).cells 0 = Γ.start →
      (c.work idx).head = done + 1 →
      c.output = out₀ →
      ∃ c',
        (binarySuccTM idx).reachesIn (done + BinarySucc.steps bits) c c' ∧
        (binarySuccTM idx).halted c' ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
        (c'.work idx).HasBinaryString
          (List.replicate done false ++ BinarySucc.ripple bits) ∧
        (c'.work idx).cells 0 = Γ.start ∧
        c'.output = out₀ := by
  intro done bits
  induction bits generalizing done with
  | nil =>
      intro c hstate hinput hwork hcontent hcell0 hhead houtput
      have hcontent' : (c.work idx).HasBinaryContent (List.replicate done false) := by
        simpa using hcontent
      have hread : (c.work idx).read = Γ.blank :=
        hcontent'.read_nil hhead
      have hstep := binarySuccTM_step_blank c hstate hread
        (by rw [hinput]; exact hinp)
        (fun i hi => by rw [hwork i hi]; exact hother i hi)
        (by rw [houtput]; exact hout)
      let target : Tape := ((c.work idx).write Γ.one).move Dir3.left
      have htargetContent : target.HasBinaryContent
          (List.replicate done false ++ [true]) := by
        have hwrite := hcontent'.write_append true (by simpa using hhead)
        simpa only [target, Tape.HasBinaryContent, Tape.move_cells] using! hwrite
      have htargetCell0 : target.cells 0 = Γ.start := by
        exact Tape.write_move_cell0 Γ.one Dir3.left hcell0
      have htargetHead : target.head = done := by
        simp [target, Tape.move, Tape.write_head, hhead]
      let c₁ : Cfg n (binarySuccTM idx).Q :=
        { state := .rewind
          input := c.input
          work := Function.update c.work idx target
          output := c.output }
      obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
        binarySuccTM_rewind_run (idx := idx)
          (List.replicate done false ++ [true]) inp₀ work₀ out₀ hinp hother hout
          done c₁ rfl hinput
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
      · simpa [BinarySucc.steps, Nat.add_assoc] using
          (TM.reachesIn.step hstep hreach)
      · simpa [BinarySucc.ripple] using hstring
  | cons bit rest ih =>
      cases bit with
      | false =>
          intro c hstate hinput hwork hcontent hcell0 hhead houtput
          have hread : (c.work idx).read = Γ.zero :=
            hcontent.read_cons hhead
          have hstep := binarySuccTM_step_zero c hstate hread
            (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target : Tape := ((c.work idx).write Γ.one).move Dir3.left
          have htargetContent : target.HasBinaryContent
              (List.replicate done false ++ true :: rest) := by
            have hwrite := hcontent.write_set true hhead (by simp)
            rw [BinarySucc.set_false_to_true] at hwrite
            simpa only [target, Tape.HasBinaryContent, Tape.move_cells] using! hwrite
          have htargetCell0 : target.cells 0 = Γ.start := by
            exact Tape.write_move_cell0 Γ.one Dir3.left hcell0
          have htargetHead : target.head = done := by
            simp [target, Tape.move, Tape.write_head, hhead]
          let c₁ : Cfg n (binarySuccTM idx).Q :=
            { state := .rewind
              input := c.input
              work := Function.update c.work idx target
              output := c.output }
          obtain ⟨c', hreach, hhalt, hinput', hwork', hstring, hcell0', houtput'⟩ :=
            binarySuccTM_rewind_run (idx := idx)
              (List.replicate done false ++ true :: rest)
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
          · simpa [BinarySucc.steps, Nat.add_assoc] using
              (TM.reachesIn.step hstep hreach)
          · simpa [BinarySucc.ripple] using hstring
      | true =>
          intro c hstate hinput hwork hcontent hcell0 hhead houtput
          have hread : (c.work idx).read = Γ.one :=
            hcontent.read_cons hhead
          have hstep := binarySuccTM_step_one c hstate hread
            (by rw [hinput]; exact hinp)
            (fun i hi => by rw [hwork i hi]; exact hother i hi)
            (by rw [houtput]; exact hout)
          let target : Tape := ((c.work idx).write Γ.zero).move Dir3.right
          have htargetContent : target.HasBinaryContent
              (List.replicate (done + 1) false ++ rest) := by
            have hwrite := hcontent.write_set false hhead (by simp)
            rw [BinarySucc.set_true_to_false] at hwrite
            simpa only [target, Tape.HasBinaryContent, Tape.move_cells] using! hwrite
          have htargetCell0 : target.cells 0 = Γ.start := by
            exact Tape.write_move_cell0 Γ.zero Dir3.right hcell0
          have htargetHead : target.head = (done + 1) + 1 := by
            simp [target, Tape.move, Tape.write_head, hhead]
          let c₁ : Cfg n (binarySuccTM idx).Q :=
            { state := .carry
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
                show (Function.update c.work idx target idx).head = (done + 1) + 1
                rw [Function.update_self]
                exact htargetHead)
              houtput
          refine ⟨c', ?_, hhalt, hinput', hwork', ?_, hcell0', houtput'⟩
          · convert! TM.reachesIn.step hstep hreach using 1
            all_goals simp [BinarySucc.steps, Nat.add_assoc]
            all_goals omega
          · simpa [BinarySucc.ripple, List.replicate_add,
              List.append_assoc] using hstring

/-! ## Public-theorem internals -/

theorem binarySuccTime_le_internal (value : ℕ) :
    binarySuccTime value ≤ 2 * value.size + 2 := by
  simpa [binarySuccTime, Nat.size_eq_bits_len] using
    BinarySucc.steps_le_internal value.bits

theorem binarySuccTM_reachesIn_frame_internal
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binarySuccTM idx).reachesIn (binarySuccTime value)
        { state := (binarySuccTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binarySuccTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryNat (value + 1) ∧
      c'.output = out₀ := by
  let c₀ : Cfg n (binarySuccTM idx).Q :=
    { state := (binarySuccTM idx).qstart
      input := inp₀
      work := work₀
      output := out₀ }
  obtain ⟨c', hreach, hhalt, hinput, hwork, hstring, hcell0, houtput⟩ :=
    binarySuccTM_carry_run (idx := idx) inp₀ work₀ out₀ hinp hother hout
      0 value.bits c₀ (by rfl) (by rfl) (fun _ _ => rfl)
      (by simpa [c₀] using hvalue.2.hasBinaryContent) hvalue.1
      (by simpa [c₀] using hvalue.2.1) (by rfl)
  refine ⟨c', ?_, hhalt, hinput, hwork, ?_, houtput⟩
  · simpa [c₀, binarySuccTime] using hreach
  · exact ⟨hcell0, by
      simpa [BinarySucc.ripple_natBits_internal] using hstring⟩

theorem binarySuccTM_hoareTime_frame_internal
    (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binarySuccTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat (value + 1) ∧
        out = out₀)
      (binarySuccTime value) := by
  rintro inp work out ⟨hinput₀, hwork₀, houtput₀⟩
  obtain ⟨c', hreach, hhalt, hinput, hwork, hvalue', houtput⟩ :=
    binarySuccTM_reachesIn_frame_internal idx value inp₀ work₀ out₀
      hvalue hinp hother hout
  refine ⟨c', binarySuccTime value, le_rfl, ?_, hhalt,
    hinput, hwork, hvalue', houtput⟩
  simpa [hinput₀, hwork₀, houtput₀] using hreach

theorem binarySuccTM_hoareTimeSpace_frame_internal
    (idx : Fin n) (value inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binarySuccTM idx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (binarySuccTM idx).Q).WithinAuxSpace inputLength initialSpace) :
    (binarySuccTM idx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryNat (value + 1) ∧
        out = out₀)
      (binarySuccTime value) inputLength
      (initialSpace + binarySuccTime value) := by
  apply (binarySuccTM_hoareTime_frame_internal idx value inp₀ work₀ out₀
    hvalue hinp hother hout).toHoareTimeSpace
  rintro inp work out ⟨hinput₀, hwork₀, houtput₀⟩
  simpa [hinput₀, hwork₀, houtput₀] using hinitial

theorem binarySuccTM_isTransducer_internal (idx : Fin n) :
    (binarySuccTM idx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | carry =>
      cases hread : wHeads idx <;>
        simp [binarySuccTM, hread, idleDir] <;>
        split <;> decide
  | rewind =>
      simp only [binarySuccTM]
      split <;> simp [idleDir] <;> split <;> decide
  | done =>
      simp [binarySuccTM, allIdle, idleDir]
      split <;> decide

end TM

end Complexity
