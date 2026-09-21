/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.NatBits
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.WorkBranch.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Direct work-symbol branch combinator -- proof internals
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a blank-branch configuration into the combined controller. -/
def workBranchBlankWrap (idx : Fin n) (onBlank onNonblank : TM n)
    (c : Cfg n onBlank.Q) : Cfg n (branchWorkBlankTM idx onBlank onNonblank).Q where
  state := workBranchBlankState onBlank onNonblank c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a nonblank-branch configuration into the combined controller. -/
def workBranchNonblankWrap (idx : Fin n) (onBlank onNonblank : TM n)
    (c : Cfg n onNonblank.Q) :
    Cfg n (branchWorkBlankTM idx onBlank onNonblank).Q where
  state := workBranchNonblankState onBlank onNonblank c.state
  input := c.input
  work := c.work
  output := c.output

theorem workBranchBlankWrap_halted_iff_internal
    (idx : Fin n) (onBlank onNonblank : TM n) (c : Cfg n onBlank.Q) :
    (branchWorkBlankTM idx onBlank onNonblank).halted
        (workBranchBlankWrap idx onBlank onNonblank c) ↔
      onBlank.halted c := by
  change (workBranchBlankWrap idx onBlank onNonblank c).state =
      (branchWorkBlankTM idx onBlank onNonblank).qhalt ↔
    c.state = onBlank.qhalt
  by_cases hhalt : c.state = onBlank.qhalt
  · simp [workBranchBlankWrap, workBranchBlankState, branchWorkBlankTM,
      hhalt]
  · simp [workBranchBlankWrap, workBranchBlankState, branchWorkBlankTM,
      hhalt]

theorem workBranchNonblankWrap_halted_iff_internal
    (idx : Fin n) (onBlank onNonblank : TM n) (c : Cfg n onNonblank.Q) :
    (branchWorkBlankTM idx onBlank onNonblank).halted
        (workBranchNonblankWrap idx onBlank onNonblank c) ↔
      onNonblank.halted c := by
  change (workBranchNonblankWrap idx onBlank onNonblank c).state =
      (branchWorkBlankTM idx onBlank onNonblank).qhalt ↔
    c.state = onNonblank.qhalt
  by_cases hhalt : c.state = onNonblank.qhalt
  · simp [workBranchNonblankWrap, workBranchNonblankState,
      branchWorkBlankTM, hhalt]
  · simp [workBranchNonblankWrap, workBranchNonblankState,
      branchWorkBlankTM, hhalt]

theorem branchWorkBlankTM_blank_step_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {c c' : Cfg n onBlank.Q} (hstep : onBlank.step c = some c') :
    (branchWorkBlankTM idx onBlank onNonblank).step
        (workBranchBlankWrap idx onBlank onNonblank c) =
      some (workBranchBlankWrap idx onBlank onNonblank c') := by
  have hne : c.state ≠ onBlank.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by
    simp [workBranchBlankWrap, workBranchBlankState, branchWorkBlankTM,
      hne])]
  simp only [workBranchBlankWrap, workBranchBlankState, hne, ↓reduceIte,
    branchWorkBlankTM]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : onBlank.δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

theorem branchWorkBlankTM_nonblank_step_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {c c' : Cfg n onNonblank.Q} (hstep : onNonblank.step c = some c') :
    (branchWorkBlankTM idx onBlank onNonblank).step
        (workBranchNonblankWrap idx onBlank onNonblank c) =
      some (workBranchNonblankWrap idx onBlank onNonblank c') := by
  have hne : c.state ≠ onNonblank.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by
    simp [workBranchNonblankWrap, workBranchNonblankState,
      branchWorkBlankTM, hne])]
  simp only [workBranchNonblankWrap, workBranchNonblankState, hne,
    ↓reduceIte, branchWorkBlankTM]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize haction : onNonblank.δ c.state c.input.read
    (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  simp only [haction]
  intro hstep
  cases Option.some.inj hstep
  rfl

theorem branchWorkBlankTM_blank_reachesIn_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {t : ℕ} {c c' : Cfg n onBlank.Q}
    (hreach : onBlank.reachesIn t c c') :
    (branchWorkBlankTM idx onBlank onNonblank).reachesIn t
      (workBranchBlankWrap idx onBlank onNonblank c)
      (workBranchBlankWrap idx onBlank onNonblank c') :=
  reachesIn_map (workBranchBlankWrap idx onBlank onNonblank)
    (fun _ _ => branchWorkBlankTM_blank_step_internal idx onBlank onNonblank)
    hreach

theorem branchWorkBlankTM_nonblank_reachesIn_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {t : ℕ} {c c' : Cfg n onNonblank.Q}
    (hreach : onNonblank.reachesIn t c c') :
    (branchWorkBlankTM idx onBlank onNonblank).reachesIn t
      (workBranchNonblankWrap idx onBlank onNonblank c)
      (workBranchNonblankWrap idx onBlank onNonblank c') :=
  reachesIn_map (workBranchNonblankWrap idx onBlank onNonblank)
    (fun _ _ => branchWorkBlankTM_nonblank_step_internal idx onBlank onNonblank)
    hreach

theorem branchWorkBlankTM_dispatch_blank_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hblank : (work idx).read = Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkBlankTM idx onBlank onNonblank).step
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } =
      some (workBranchBlankWrap idx onBlank onNonblank
        { state := onBlank.qstart
          input := inp
          work := work
          output := out }) := by
  rw [TM.step, if_neg (by simp [branchWorkBlankTM])]
  simp only [branchWorkBlankTM, hblank, allReadBack, ↓reduceIte,
    workBranchBlankWrap]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · exact transitionInput_eq_self hinp
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self hout

theorem branchWorkBlankTM_dispatch_nonblank_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hnonblank : (work idx).read ≠ Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start) :
    (branchWorkBlankTM idx onBlank onNonblank).step
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } =
      some (workBranchNonblankWrap idx onBlank onNonblank
        { state := onNonblank.qstart
          input := inp
          work := work
          output := out }) := by
  rw [TM.step, if_neg (by simp [branchWorkBlankTM])]
  simp only [branchWorkBlankTM, hnonblank, allReadBack, ↓reduceIte,
    workBranchNonblankWrap]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · exact transitionInput_eq_self hinp
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self hout

theorem branchWorkBlankTM_reachesIn_blank_frame_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onBlank.Q}
    (hblank : (work idx).read = Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onBlank.reachesIn t
      { state := onBlank.qstart, input := inp, work := work, output := out } c')
    (hhalt : onBlank.halted c') :
    ∃ C,
      (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkBlankTM idx onBlank onNonblank).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output := by
  let C := workBranchBlankWrap idx onBlank onNonblank c'
  refine ⟨C, .step
    (branchWorkBlankTM_dispatch_blank_internal idx onBlank onNonblank
      inp work out hblank hinp hwork hout)
    (branchWorkBlankTM_blank_reachesIn_internal idx onBlank onNonblank
      hreach), ?_, rfl, rfl, rfl⟩
  exact (workBranchBlankWrap_halted_iff_internal idx onBlank onNonblank c').2
    hhalt

theorem branchWorkBlankTM_reachesIn_nonblank_frame_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {t : ℕ} {c' : Cfg n onNonblank.Q}
    (hnonblank : (work idx).read ≠ Γ.blank)
    (hinp : inp.read ≠ Γ.start) (hwork : ∀ i, (work i).read ≠ Γ.start)
    (hout : out.read ≠ Γ.start)
    (hreach : onNonblank.reachesIn t
      { state := onNonblank.qstart, input := inp, work := work, output := out } c')
    (hhalt : onNonblank.halted c') :
    ∃ C,
      (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
        { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
          input := inp
          work := work
          output := out } C ∧
      (branchWorkBlankTM idx onBlank onNonblank).halted C ∧
      C.input = c'.input ∧ C.work = c'.work ∧ C.output = c'.output := by
  let C := workBranchNonblankWrap idx onBlank onNonblank c'
  refine ⟨C, .step
    (branchWorkBlankTM_dispatch_nonblank_internal idx onBlank onNonblank
      inp work out hnonblank hinp hwork hout)
    (branchWorkBlankTM_nonblank_reachesIn_internal idx onBlank onNonblank
      hreach), ?_, rfl, rfl, rfl⟩
  exact (workBranchNonblankWrap_halted_iff_internal idx onBlank onNonblank c').2
    hhalt

theorem branchWorkBlankTM_hoareTime_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {pre blankPre nonblankPre blankPost nonblankPost : TapePred n}
    {blankTime nonblankTime : ℕ}
    (hframe : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧
        out.read ≠ Γ.start)
    (hblankPre : ∀ inp work out, pre inp work out →
      (work idx).read = Γ.blank → blankPre inp work out)
    (hnonblankPre : ∀ inp work out, pre inp work out →
      (work idx).read ≠ Γ.blank → nonblankPre inp work out)
    (hblank : onBlank.HoareTime blankPre blankPost blankTime)
    (hnonblank : onNonblank.HoareTime nonblankPre nonblankPost nonblankTime) :
    (branchWorkBlankTM idx onBlank onNonblank).HoareTime pre
      (fun inp work out =>
        blankPost inp work out ∨ nonblankPost inp work out)
      (branchWorkBlankTime blankTime nonblankTime) := by
  intro inp work out hpre
  obtain ⟨hinp, hwork, hout⟩ := hframe inp work out hpre
  by_cases hread : (work idx).read = Γ.blank
  · obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
      hblank inp work out (hblankPre inp work out hpre hread)
    obtain ⟨C, hrun, hhaltC, hinput, hworkC, houtput⟩ :=
      branchWorkBlankTM_reachesIn_blank_frame_internal idx onBlank
        onNonblank inp work out hread hinp hwork hout hreach hhalt
    refine ⟨C, t + 1, ?_, hrun, hhaltC, ?_⟩
    · unfold branchWorkBlankTime
      omega
    · left
      simpa [hinput, hworkC, houtput] using hpost
  · obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
      hnonblank inp work out (hnonblankPre inp work out hpre hread)
    obtain ⟨C, hrun, hhaltC, hinput, hworkC, houtput⟩ :=
      branchWorkBlankTM_reachesIn_nonblank_frame_internal idx onBlank
        onNonblank inp work out hread hinp hwork hout hreach hhalt
    refine ⟨C, t + 1, ?_, hrun, hhaltC, ?_⟩
    · unfold branchWorkBlankTime
      omega
    · right
      simpa [hinput, hworkC, houtput] using hpost

theorem branchWorkBlankTM_hoareTimeSpace_internal
    (idx : Fin n) (onBlank onNonblank : TM n)
    {pre blankPre nonblankPre blankPost nonblankPost : TapePred n}
    {blankTime nonblankTime inputLength blankSpace nonblankSpace : ℕ}
    (hframe : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧
        out.read ≠ Γ.start)
    (hblankPre : ∀ inp work out, pre inp work out →
      (work idx).read = Γ.blank → blankPre inp work out)
    (hnonblankPre : ∀ inp work out, pre inp work out →
      (work idx).read ≠ Γ.blank → nonblankPre inp work out)
    (hblank : onBlank.HoareTimeSpace blankPre blankPost blankTime
      inputLength blankSpace)
    (hnonblank : onNonblank.HoareTimeSpace nonblankPre nonblankPost
      nonblankTime inputLength nonblankSpace) :
    (branchWorkBlankTM idx onBlank onNonblank).HoareTimeSpace pre
      (fun inp work out =>
        blankPost inp work out ∨ nonblankPost inp work out)
      (branchWorkBlankTime blankTime nonblankTime) inputLength
      (max blankSpace nonblankSpace) := by
  constructor
  · exact branchWorkBlankTM_hoareTime_internal idx onBlank onNonblank
      hframe hblankPre hnonblankPre hblank.1 hnonblank.1
  · intro inp work out hpre C hreach
    obtain ⟨hinp, hwork, hout⟩ := hframe inp work out hpre
    obtain ⟨u, hreachU⟩ :=
      (branchWorkBlankTM idx onBlank onNonblank).reaches_to_reachesIn hreach
    by_cases hread : (work idx).read = Γ.blank
    · have hbranchPre := hblankPre inp work out hpre hread
      obtain ⟨cHalt, t, _ht, hbranch, hhalt, _hpost⟩ :=
        hblank.1 inp work out hbranchPre
      have hfull :
          (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
            { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
              input := inp
              work := work
              output := out }
            (workBranchBlankWrap idx onBlank onNonblank cHalt) :=
        .step
          (branchWorkBlankTM_dispatch_blank_internal idx onBlank onNonblank
            inp work out hread hinp hwork hout)
          (branchWorkBlankTM_blank_reachesIn_internal idx onBlank onNonblank
            hbranch)
      have hfullHalt :
          (branchWorkBlankTM idx onBlank onNonblank).halted
            (workBranchBlankWrap idx onBlank onNonblank cHalt) :=
        (workBranchBlankWrap_halted_iff_internal idx onBlank onNonblank
          cHalt).2 hhalt
      have hu : u ≤ t + 1 :=
        (branchWorkBlankTM idx onBlank onNonblank).reachesIn_le_halt
          hreachU hfull hfullHalt
      cases u with
      | zero =>
          cases hreachU
          have hspace := hblank.2 inp work out hbranchPre _ .refl
          exact hspace.mono le_rfl (le_max_left _ _)
      | succ v =>
          have hv : v ≤ t := by omega
          obtain ⟨d, hprefix, _hsuffix⟩ :=
            reachesIn_prefix_internal hbranch hv
          have hcanonical :
              (branchWorkBlankTM idx onBlank onNonblank).reachesIn (v + 1)
                { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
                  input := inp
                  work := work
                  output := out }
                (workBranchBlankWrap idx onBlank onNonblank d) :=
            .step
              (branchWorkBlankTM_dispatch_blank_internal idx onBlank
                onNonblank inp work out hread hinp hwork hout)
              (branchWorkBlankTM_blank_reachesIn_internal idx onBlank
                onNonblank hprefix)
          have hC : C = workBranchBlankWrap idx onBlank onNonblank d :=
            (branchWorkBlankTM idx onBlank onNonblank).reachesIn_right_unique
              hreachU hcanonical
          rw [hC]
          have hspace := hblank.2 inp work out hbranchPre d
            (reaches_of_reachesIn hprefix)
          exact (hspace.mono le_rfl (le_max_left _ _))
    · have hbranchPre := hnonblankPre inp work out hpre hread
      obtain ⟨cHalt, t, _ht, hbranch, hhalt, _hpost⟩ :=
        hnonblank.1 inp work out hbranchPre
      have hfull :
          (branchWorkBlankTM idx onBlank onNonblank).reachesIn (t + 1)
            { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
              input := inp
              work := work
              output := out }
            (workBranchNonblankWrap idx onBlank onNonblank cHalt) :=
        .step
          (branchWorkBlankTM_dispatch_nonblank_internal idx onBlank
            onNonblank inp work out hread hinp hwork hout)
          (branchWorkBlankTM_nonblank_reachesIn_internal idx onBlank
            onNonblank hbranch)
      have hfullHalt :
          (branchWorkBlankTM idx onBlank onNonblank).halted
            (workBranchNonblankWrap idx onBlank onNonblank cHalt) :=
        (workBranchNonblankWrap_halted_iff_internal idx onBlank onNonblank
          cHalt).2 hhalt
      have hu : u ≤ t + 1 :=
        (branchWorkBlankTM idx onBlank onNonblank).reachesIn_le_halt
          hreachU hfull hfullHalt
      cases u with
      | zero =>
          cases hreachU
          have hspace := hnonblank.2 inp work out hbranchPre _ .refl
          exact hspace.mono le_rfl (le_max_right _ _)
      | succ v =>
          have hv : v ≤ t := by omega
          obtain ⟨d, hprefix, _hsuffix⟩ :=
            reachesIn_prefix_internal hbranch hv
          have hcanonical :
              (branchWorkBlankTM idx onBlank onNonblank).reachesIn (v + 1)
                { state := (branchWorkBlankTM idx onBlank onNonblank).qstart
                  input := inp
                  work := work
                  output := out }
                (workBranchNonblankWrap idx onBlank onNonblank d) :=
            .step
              (branchWorkBlankTM_dispatch_nonblank_internal idx onBlank
                onNonblank inp work out hread hinp hwork hout)
              (branchWorkBlankTM_nonblank_reachesIn_internal idx onBlank
                onNonblank hprefix)
          have hC : C = workBranchNonblankWrap idx onBlank onNonblank d :=
            (branchWorkBlankTM idx onBlank onNonblank).reachesIn_right_unique
              hreachU hcanonical
          rw [hC]
          have hspace := hnonblank.2 inp work out hbranchPre d
            (reaches_of_reachesIn hprefix)
          exact (hspace.mono le_rfl (le_max_right _ _))

theorem IsTransducer.branchWorkBlankTM_internal
    {idx : Fin n} {onBlank onNonblank : TM n}
    (hblank : onBlank.IsTransducer)
    (hnonblank : onNonblank.IsTransducer) :
    (branchWorkBlankTM idx onBlank onNonblank).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase with
      | dispatch =>
          simp only [branchWorkBlankTM]
          split <;> cases oHead <;> simp [allReadBack, idleDir]
      | done => cases oHead <;> simp [branchWorkBlankTM, allIdle, idleDir]
  | inr branchState =>
      cases branchState with
      | inl q =>
          simp only [branchWorkBlankTM]
          split
          · cases oHead <;> simp [allIdle, idleDir]
          · exact hblank q iHead wHeads oHead
      | inr q =>
          simp only [branchWorkBlankTM]
          split
          · cases oHead <;> simp [allIdle, idleDir]
          · exact hnonblank q iHead wHeads oHead

end TM

namespace Tape

/-- A canonical little-endian natural reads blank exactly at zero. -/
theorem HasBinaryNat.read_eq_blank_iff_internal {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) :
    t.read = Γ.blank ↔ value = 0 := by
  constructor
  · intro hread
    by_contra hvalue
    have hbits : value.bits ≠ [] := by
      intro hnil
      apply hvalue
      rw [← Nat.fromBitsLE_bits value, hnil]
      rfl
    obtain ⟨bit, bits, hcons⟩ := List.exists_cons_of_ne_nil hbits
    have hcell : t.cells 1 = Γ.ofBool bit := by
      have hfirst := h.2.2.1 0 (by simp [hcons])
      simpa [hcons] using hfirst
    rw [Tape.read, h.2.1, hcell] at hread
    cases bit <;> simp [Γ.ofBool] at hread
  · intro hvalue
    subst value
    rw [Tape.read, h.2.1]
    exact h.2.2.2 0 (by simp)

end Tape

end Complexity
