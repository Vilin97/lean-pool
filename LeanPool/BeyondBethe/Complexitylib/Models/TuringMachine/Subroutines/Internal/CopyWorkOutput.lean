/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Copy a raw work-tape output — proof internals

`Tape.HasOutput` deliberately leaves cells after the terminating blank
unconstrained. This module proves that `TM.copyWorkToWorkTM` nevertheless
copies such an output to a fresh work tape: it reads only the advertised bits
and their first blank delimiter.

Public statements are in
`Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput`.
-/


public section

namespace Complexity

namespace TM

/-! ## Exact copy loop -/

/-- Copy the unread suffix of a raw output while preserving the source cells. -/
private theorem copyWorkOutput_loop {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) (source : Tape) :
    ∀ rem k (c : Cfg n (copyWorkToWorkTM src dst).Q) (dstCell0 : Γ),
      rem = x.length - k →
      c.state = CopyPhase.copying →
      (c.work src).cells = source.cells →
      (c.work src).head = k + 1 →
      source.HasOutput x →
      (c.work dst).HasBinaryPrefix (x.take k) →
      (c.work dst).cells 0 = dstCell0 →
      k ≤ x.length →
      ∃ c',
        (copyWorkToWorkTM src dst).reachesIn (rem + 1) c c' ∧
        (copyWorkToWorkTM src dst).halted c' ∧
        (c'.work src).cells = source.cells ∧
        (c'.work src).head = x.length + 1 ∧
        (c'.work src).HasOutput x ∧
        (c'.work dst).HasBinaryPrefix x ∧
        (c'.work dst).cells 0 = dstCell0 := by
  intro rem
  induction rem with
  | zero =>
      intro k c dstCell0 hrem hstate hsrcCells hsrcHead hsource hprefix hdst0 hk
      have hkEq : k = x.length := by omega
      subst hkEq
      have hsrcRead : (c.work src).read = Γ.blank := by
        rw [Tape.read, hsrcHead, hsrcCells]
        exact hsource.2
      have hprefixFull : (c.work dst).HasBinaryPrefix x := by
        simpa using hprefix
      have hdstRead : (c.work dst).read = Γ.blank := by
        rw [Tape.read, hprefixFull.1]
        exact hprefixFull.2.2 x.length le_rfl
      let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
        { state := CopyPhase.done
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
      have hstep : (copyWorkToWorkTM src dst).step c = some c1 := by
        simp [TM.step, hstate, copyWorkToWorkTM, hsrcRead, c1, allIdle]
      have hsrcKeep : c1.work src = c.work src := by
        have hneStart : (c.work src).read ≠ Γ.start := by
          rw [hsrcRead]
          decide
        simpa [c1, hsrcRead, transitionTape] using
          (transitionTape_eq_self (t := c.work src) hneStart)
      have hdstKeep : c1.work dst = c.work dst := by
        have hneStart : (c.work dst).read ≠ Γ.start := by
          rw [hdstRead]
          decide
        simpa [c1, hdstRead, transitionTape] using
          (transitionTape_eq_self (t := c.work dst) hneStart)
      refine ⟨c1, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsrcKeep]
        exact hsrcCells
      · rw [hsrcKeep, hsrcHead]
      · rw [hsrcKeep]
        exact (Tape.hasOutput_congr hsrcCells x).mpr hsource
      · rw [hdstKeep]
        exact hprefixFull
      · rw [hdstKeep]
        exact hdst0
  | succ rem ih =>
      intro k c dstCell0 hrem hstate hsrcCells hsrcHead hsource hprefix hdst0 hk
      have hkLt : k < x.length := by omega
      let bit := x[k]'hkLt
      have hsrcRead : (c.work src).read = Γ.ofBool bit := by
        rw [Tape.read, hsrcHead, hsrcCells]
        exact hsource.1 k hkLt
      have hprefixNext :
          ((c.work dst).writeAndMove (Γ.ofBool bit) Dir3.right).HasBinaryPrefix
            (x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit bit hprefix
        simpa [bit, List.take_concat_get' x k hkLt] using hwrite
      let c1 : Cfg n (copyWorkToWorkTM src dst).Q :=
        { state := CopyPhase.copying
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove
              (if i = dst then (Γw.ofBool bit).toΓ
               else (readBackWrite (c.work i).read).toΓ)
              (if i = dst then Dir3.right
               else if i = src then Dir3.right else idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
            (idleDir c.output.read) }
      have hstep : (copyWorkToWorkTM src dst).step c = some c1 := by
        cases hbit : bit
        · simp [TM.step, hstate, copyWorkToWorkTM, hsrcRead, hbit, bit, c1,
            Γ.ofBool, Γw.ofBool, Γw.toΓ, readBackWrite]
          funext i
          by_cases hi : i = dst <;> simp [hi]
        · simp [TM.step, hstate, copyWorkToWorkTM, hsrcRead, hbit, bit, c1,
            Γ.ofBool, Γw.ofBool, Γw.toΓ, readBackWrite]
          funext i
          by_cases hi : i = dst <;> simp [hi]
      have hsrcCells1 : (c1.work src).cells = source.cells := by
        have hneStart : (c.work src).read ≠ Γ.start := by
          rw [hsrcRead]
          exact Γ.ofBool_ne_start bit
        have hpres : (c1.work src).cells = (c.work src).cells := by
          simpa [c1, hne, hsrcRead] using
            (tape_readBackWrite_preserves (c.work src) Dir3.right (Or.inr hneStart))
        rw [hpres]
        exact hsrcCells
      have hsrcHead1 : (c1.work src).head = k + 2 := by
        simp [c1, hsrcHead, hne, Tape.writeAndMove, Tape.move, Tape.write_head]
      have hdstTape :
          c1.work dst = (c.work dst).writeAndMove (Γ.ofBool bit) Dir3.right := by
        dsimp only [c1]
        simp only [ite_eq_left]
        rw [Γw.ofBool_toΓ]
      have hdstPrefix1 : (c1.work dst).HasBinaryPrefix (x.take (k + 1)) := by
        rw [hdstTape]
        exact hprefixNext
      have hdst01 : (c1.work dst).cells 0 = dstCell0 := by
        rw [hdstTape]
        simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
        rw [ite_eq_right (by rw [hprefix.1]; omega)]
        change Function.update (c.work dst).cells (c.work dst).head
          (Γ.ofBool bit) 0 = dstCell0
        rw [Function.update_of_ne (by rw [hprefix.1]; omega)]
        exact hdst0
      have hrem1 : rem = x.length - (k + 1) := by omega
      obtain ⟨c', hreach, hhalt, hsrcCells', hsrcHead', hsrcOutput', hprefix',
        hdst0'⟩ :=
        ih (k + 1) c1 dstCell0 hrem1 rfl hsrcCells1 hsrcHead1 hsource
          hdstPrefix1 hdst01 (by omega)
      exact ⟨c', .step hstep hreach, hhalt, hsrcCells', hsrcHead', hsrcOutput',
        hprefix', hdst0'⟩

/-! ## Hoare specification -/

/-- Exact raw-output copy from a concrete tape configuration. -/
theorem copyWorkToWorkTM_reachesIn_of_hasOutput_internal {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool)
    {inp out : Tape} {work : Fin n → Tape}
    (hsrcHead : (work src).head = 1)
    (hsrcOutput : (work src).HasOutput x)
    (hdst : (work dst).HasBinaryPrefix []) :
    ∃ c',
      (copyWorkToWorkTM src dst).reachesIn (x.length + 1)
        { state := (copyWorkToWorkTM src dst).qstart,
          input := inp, work := work, output := out } c' ∧
      (copyWorkToWorkTM src dst).halted c' ∧
      (c'.work src).cells = (work src).cells ∧
      (c'.work src).head = x.length + 1 ∧
      (c'.work src).HasOutput x ∧
      (c'.work dst).HasBinaryPrefix x ∧
      (c'.work dst).cells 0 = (work dst).cells 0 := by
  exact copyWorkOutput_loop src dst hne x (work src) x.length 0
    { state := CopyPhase.copying, input := inp, work := work, output := out }
    ((work dst).cells 0) (by simp) rfl rfl hsrcHead hsrcOutput
    (by simpa using hdst) rfl (Nat.zero_le _)

/-- A raw `HasOutput` source is copied exactly through its first blank.
Arbitrary source cells after that delimiter are preserved and ignored. -/
theorem copyWorkToWorkTM_hoareTime_of_hasOutput_internal {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) (source : Tape) :
    (copyWorkToWorkTM src dst).HoareTime
      (fun _inp work _out =>
        work src = source ∧ source.head = 1 ∧ source.HasOutput x ∧
          (work dst).HasBinaryPrefix [])
      (fun _inp work _out =>
        (work src).cells = source.cells ∧
        (work src).head = x.length + 1 ∧
        (work src).HasOutput x ∧
        (work dst).HasBinaryPrefix x)
      (x.length + 1) := by
  intro inp work out hpre
  rcases hpre with ⟨hsrc, hsourceHead, hsourceOutput, hdst⟩
  have hsrcCells : (work src).cells = source.cells := by rw [hsrc]
  have hsrcHead : (work src).head = 1 := by rw [hsrc, hsourceHead]
  obtain ⟨c', hreach, hhalt, hsrcCells', hsrcHead', hsrcOutput', hprefix', _⟩ :=
    copyWorkOutput_loop src dst hne x source x.length 0
      { state := CopyPhase.copying, input := inp, work := work, output := out }
      ((work dst).cells 0) (by simp) rfl hsrcCells hsrcHead hsourceOutput
      (by simpa using hdst) rfl (Nat.zero_le _)
  exact ⟨c', x.length + 1, le_rfl, hreach, hhalt, hsrcCells', hsrcHead',
    hsrcOutput', hprefix'⟩

/-! ## Exact frame preservation -/

/-- A stable tape is unchanged by the copy machine's idle action. -/
private theorem idle_writeBack_eq (t : Tape)
    (hread : t.read ≠ Γ.start) (hhead : 1 ≤ t.head) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hread, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hread ⊢
    rw [toΓ_readBackWrite_of_ne_start hread, Function.update_eq_self]

/-- A stable read-only tape is unchanged by the input idle action. -/
private theorem idle_input_eq (t : Tape) (hread : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  simp [idleDir, hread, Tape.move]

/-- One copy step preserves the input, output, and every unrelated work tape
when those tapes are already off the left-end marker. -/
private theorem copyWorkOutput_step_frame {n : ℕ} (src dst : Fin n)
    {c c' : Cfg n (copyWorkToWorkTM src dst).Q}
    (hstep : (copyWorkToWorkTM src dst).step c = some c')
    (hin : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houtHead : 1 ≤ c.output.head)
    (hother : ∀ i, i ≠ src → i ≠ dst →
      (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) :
    c'.input = c.input ∧ c'.output = c.output ∧
      ∀ i, i ≠ src → i ≠ dst → c'.work i = c.work i := by
  have hneHalt := state_ne_qhalt_of_step hstep
  cases hstate : c.state with
  | done =>
      exfalso
      exact hneHalt (by simpa [copyWorkToWorkTM] using hstate)
  | copying =>
      unfold TM.step at hstep
      rw [ite_eq_right hneHalt] at hstep
      have hc := Option.some.inj hstep
      rw [← hc]
      rw [hstate]
      dsimp only [copyWorkToWorkTM]
      split
      · refine ⟨idle_input_eq c.input hin, idle_writeBack_eq c.output hout houtHead, ?_⟩
        intro i hiSrc hiDst
        exact idle_writeBack_eq (c.work i) (hother i hiSrc hiDst).1
          (hother i hiSrc hiDst).2
      · refine ⟨idle_input_eq c.input hin, idle_writeBack_eq c.output hout houtHead, ?_⟩
        intro i hiSrc hiDst
        simp only [hiDst, hiSrc, ↓reduceIte]
        exact idle_writeBack_eq (c.work i) (hother i hiSrc hiDst).1
          (hother i hiSrc hiDst).2

/-- Exact frame preservation over an arbitrary finite copy run. -/
private theorem copyWorkOutput_reachesIn_frame {n : ℕ} (src dst : Fin n)
    {t : ℕ} {c c' : Cfg n (copyWorkToWorkTM src dst).Q}
    (hreach : (copyWorkToWorkTM src dst).reachesIn t c c')
    (hin : c.input.read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) (houtHead : 1 ≤ c.output.head)
    (hother : ∀ i, i ≠ src → i ≠ dst →
      (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) :
    c'.input = c.input ∧ c'.output = c.output ∧
      ∀ i, i ≠ src → i ≠ dst → c'.work i = c.work i := by
  induction hreach with
  | zero => exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
  | @step c0 c1 _ _ hstep _ ih =>
      obtain ⟨hin1, hout1, hwork1⟩ :=
        copyWorkOutput_step_frame src dst hstep hin hout houtHead hother
      have hother1 : ∀ i, i ≠ src → i ≠ dst →
          (c1.work i).read ≠ Γ.start ∧ 1 ≤ (c1.work i).head := by
        intro i hiSrc hiDst
        rw [hwork1 i hiSrc hiDst]
        exact hother i hiSrc hiDst
      have ih' := ih (by rw [hin1]; exact hin) (by rw [hout1]; exact hout)
        (by rw [hout1]; exact houtHead) hother1
      exact ⟨ih'.1.trans hin1, ih'.2.1.trans hout1, fun i hiSrc hiDst =>
        (ih'.2.2 i hiSrc hiDst).trans (hwork1 i hiSrc hiDst)⟩

/-- Frame-rich raw-output copy. The input tape, output tape, and unrelated work
tapes are preserved exactly, allowing an arbitrary predicate to be threaded
through the copy. -/
theorem copyWorkToWorkTM_hoareTime_frame_of_hasOutput_internal {n : ℕ}
    (src dst : Fin n) (hne : src ≠ dst) (x : List Bool) (source : Tape)
    {P : Tape → (Fin n → Tape) → Tape → Prop}
    (hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      P inp work out →
      (work' src).cells = source.cells →
      (work' src).head = x.length + 1 →
      (work' src).HasOutput x →
      (work' dst).HasBinaryPrefix x →
      (work' dst).cells 0 = Γ.start →
      inp' = inp → out' = out →
      (∀ i, i ≠ src → i ≠ dst → work' i = work i) →
      P inp' work' out') :
    (copyWorkToWorkTM src dst).HoareTime
      (fun inp work out =>
        work src = source ∧ source.head = 1 ∧ source.HasOutput x ∧
        work dst = (Tape.init []).move Dir3.right ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ 1 ≤ out.head ∧
        (∀ i, i ≠ src → i ≠ dst →
          (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head) ∧
        P inp work out)
      (fun inp work out =>
        (work src).cells = source.cells ∧
        (work src).head = x.length + 1 ∧
        (work src).HasOutput x ∧
        (work dst).HasBinaryPrefix x ∧
        (work dst).cells 0 = Γ.start ∧
        P inp work out)
      (x.length + 1) := by
  intro inp work out hpre
  rcases hpre with
    ⟨hsrc, hsourceHead, hsourceOutput, hdst, hin, hout, houtHead, hother, hPred⟩
  have hsrcCells0 : (work src).cells = source.cells := by rw [hsrc]
  have hsrcHead0 : (work src).head = 1 := by rw [hsrc, hsourceHead]
  have hdstPrefix0 : (work dst).HasBinaryPrefix [] := by
    rw [hdst]
    exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hdst0Start : (work dst).cells 0 = Γ.start := by rw [hdst]; rfl
  obtain ⟨c', hreach, hhalt, hsrcCells, hsrcHead, hsrcOutput, hdstPrefix,
    hdst0⟩ :=
    copyWorkOutput_loop src dst hne x source x.length 0
      { state := CopyPhase.copying, input := inp, work := work, output := out }
      Γ.start (by simp) rfl hsrcCells0 hsrcHead0 hsourceOutput hdstPrefix0
      hdst0Start (Nat.zero_le _)
  obtain ⟨hinFrame, houtFrame, hworkFrame⟩ :=
    copyWorkOutput_reachesIn_frame src dst hreach hin hout houtHead hother
  refine ⟨c', x.length + 1, le_rfl, hreach, hhalt, hsrcCells, hsrcHead, hsrcOutput,
    hdstPrefix, hdst0, ?_⟩
  exact hP inp work out c'.input c'.work c'.output hPred hsrcCells hsrcHead
    hsrcOutput hdstPrefix hdst0 hinFrame houtFrame hworkFrame

end TM

end Complexity
