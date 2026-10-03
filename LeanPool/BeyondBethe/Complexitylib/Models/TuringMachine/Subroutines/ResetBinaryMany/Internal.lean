/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Defs

/-!
# Resetting several binary work tapes — proof internals
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

theorem resetBinaryWorkManyTime_le_internal
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (headBound : Fin n → ℕ) (maxHead maxWidth : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead)
    (hwidth : ∀ i, i ∈ targets → (bits i).length ≤ maxWidth) :
    resetBinaryWorkManyTime bits headBound targets ≤
      targets.length * (maxHead + 2 * maxWidth + 9) + 1 := by
  induction targets with
  | nil => simp [resetBinaryWorkManyTime]
  | cons idx rest ih =>
      have hheadIdx := hhead idx (by simp)
      have hwidthIdx := hwidth idx (by simp)
      have ih' := ih
        (fun i hi => hhead i (by simp [hi]))
        (fun i hi => hwidth i (by simp [hi]))
      simp only [resetBinaryWorkManyTime, resetBinaryWorkTime,
        clearWorkTimeBound, List.length_cons]
      calc
        headBound idx + 2 + 1 + (2 * (bits idx).length + 5) + 1 +
            resetBinaryWorkManyTime bits headBound rest ≤
          (maxHead + 2 * maxWidth + 9) +
            resetBinaryWorkManyTime bits headBound rest := by omega
        _ ≤ (maxHead + 2 * maxWidth + 9) +
            (rest.length * (maxHead + 2 * maxWidth + 9) + 1) :=
          Nat.add_le_add_left ih' _
        _ = (rest.length + 1) * (maxHead + 2 * maxWidth + 9) + 1 := by
          rw [Nat.add_mul]
          omega

private theorem resetBinaryBlank_parked : Parked resetBinaryBlank := by
  constructor
  · simp [resetBinaryBlank, Tape.init, Tape.move]
  · intro j hj
    simpa [resetBinaryBlank, Tape.init, Tape.move] using
      (show j ≠ 0 by omega)

theorem resetBinaryWorkManyResult_parked_internal
    (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (resetBinaryWorkManyResult work₀ targets i) := by
  induction targets generalizing work₀ with
  | nil => exact hwork
  | cons idx rest ih =>
      apply ih
      intro i
      by_cases hi : i = idx
      · subst i
        rw [Function.update_self]
        exact resetBinaryBlank_parked
      · simpa [Function.update_of_ne hi] using hwork i

theorem resetBinaryWorkManyResult_eq_of_not_mem_internal
    (work₀ : Fin n → Tape) (targets : List (Fin n)) (idx : Fin n)
    (hidx : idx ∉ targets) :
    resetBinaryWorkManyResult work₀ targets idx = work₀ idx := by
  induction targets generalizing work₀ with
  | nil => rfl
  | cons target rest ih =>
      have hne : idx ≠ target := by
        intro heq
        exact hidx (by simp [heq])
      have hrest : idx ∉ rest := by
        intro hmem
        exact hidx (by simp [hmem])
      simpa [resetBinaryWorkManyResult, Function.update_of_ne hne] using
        ih (Function.update work₀ target resetBinaryBlank) hrest

theorem resetBinaryWorkManyResult_eq_blank_of_mem_internal
    (work₀ : Fin n → Tape) (targets : List (Fin n)) (idx : Fin n)
    (hidx : idx ∈ targets) :
    resetBinaryWorkManyResult work₀ targets idx = resetBinaryBlank := by
  induction targets generalizing work₀ with
  | nil => simp at hidx
  | cons target rest ih =>
      by_cases heq : idx = target
      · subst idx
        by_cases hmem : target ∈ rest
        · exact ih (Function.update work₀ target resetBinaryBlank) hmem
        · exact resetBinaryWorkManyResult_eq_of_not_mem_internal
            (Function.update work₀ target resetBinaryBlank) rest target hmem
            |>.trans (Function.update_self ..)
      · have hrest : idx ∈ rest := by
          simpa [heq] using hidx
        exact ih (Function.update work₀ target resetBinaryBlank) hrest

theorem resetBinaryWorkManyTime_congr_headBound_internal
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (left right : Fin n → ℕ)
    (heq : ∀ i, i ∈ targets → left i = right i) :
    resetBinaryWorkManyTime bits left targets =
      resetBinaryWorkManyTime bits right targets := by
  induction targets with
  | nil => rfl
  | cons idx rest ih =>
      simp only [resetBinaryWorkManyTime]
      rw [heq idx (by simp)]
      exact congrArg
        (fun time => resetBinaryWorkTime (right idx) (bits idx).length + 1 + time)
        (ih fun i hi => heq i (by simp [hi]))

theorem resetBinaryWorkManyTM_hoareTime_frame_internal
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (headBound : Fin n → ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hnodup : targets.Nodup)
    (htarget : ∀ i, i ∈ targets → (work₀ i).HasBinaryContent (bits i))
    (htargetStart : ∀ i, i ∈ targets → (work₀ i).cells 0 = Γ.start)
    (htargetHead : ∀ i, i ∈ targets → (work₀ i).head ≤ headBound i)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (resetBinaryWorkManyTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = resetBinaryWorkManyResult work₀ targets ∧
        out = out₀)
      (resetBinaryWorkManyTime bits headBound targets) := by
  induction targets generalizing work₀ with
  | nil =>
      simpa [resetBinaryWorkManyTM, resetBinaryWorkManyResult,
        resetBinaryWorkManyTime] using
        skipTM_hoareTime_frame inp₀ work₀ out₀ hinput hwork houtput
  | cons idx rest ih =>
      have hidxNotMem : idx ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      let work₁ := Function.update work₀ idx resetBinaryBlank
      have hreset := resetBinaryWorkTM_hoareTime_frame idx (bits idx)
        (headBound idx) inp₀ work₀ out₀
        (htarget idx (by simp)) (htargetStart idx (by simp))
        ⟨(hwork idx).1, htargetHead idx (by simp)⟩ hinput
        (fun i _ => hwork i) houtput
      have hwork₁ : ∀ i, Parked (work₁ i) := by
        intro i
        by_cases hi : i = idx
        · subst i
          simpa [work₁, resetBinaryBlank] using resetBinaryBlank_parked
        · simpa [work₁, Function.update_of_ne hi] using hwork i
      have htarget₁ : ∀ i, i ∈ rest →
          (work₁ i).HasBinaryContent (bits i) := by
        intro i hi
        have hne : i ≠ idx := fun hieq => hidxNotMem (hieq ▸ hi)
        simpa [work₁, Function.update_of_ne hne] using
          htarget i (by simp [hi])
      have htargetStart₁ : ∀ i, i ∈ rest →
          (work₁ i).cells 0 = Γ.start := by
        intro i hi
        have hne : i ≠ idx := fun hieq => hidxNotMem (hieq ▸ hi)
        simpa [work₁, Function.update_of_ne hne] using
          htargetStart i (by simp [hi])
      have htargetHead₁ : ∀ i, i ∈ rest →
          (work₁ i).head ≤ headBound i := by
        intro i hi
        have hne : i ≠ idx := fun hieq => hidxNotMem (hieq ▸ hi)
        simpa [work₁, Function.update_of_ne hne] using
          htargetHead i (by simp [hi])
      have hrest := ih work₁ hrestNodup htarget₁ htargetStart₁
        htargetHead₁ hwork₁
      have hseq := seqTM_hoareTime (resetBinaryWorkTM idx)
        (resetBinaryWorkManyTM rest) hreset
        (by
          intro inp work out hmid
          rcases hmid with ⟨hinp, hworkEq, hout⟩
          have hworkParked : ∀ i, Parked (work i) := by
            intro i
            rw [hworkEq]
            exact hwork₁ i
          obtain ⟨hinpTransition, hworkTransition, houtTransition⟩ :=
            phaseTransition_eq_self_of_reads_ne_start
              (hinp ▸ hinput.read_ne_start)
              (fun i => (hworkParked i).read_ne_start)
              (hout ▸ houtput.read_ne_start)
          rw [hinpTransition, hworkTransition, houtTransition]
          exact ⟨hinp, hworkEq, hout⟩)
        hrest
      simpa [resetBinaryWorkManyTM, resetBinaryWorkManyResult,
        resetBinaryWorkManyTime, work₁] using hseq

theorem resetBinaryWorkManyTM_isTransducer_internal
    (targets : List (Fin n)) :
    (resetBinaryWorkManyTM targets).IsTransducer := by
  induction targets with
  | nil =>
      intro state iHead wHeads oHead
      cases state <;> cases oHead <;> simp [resetBinaryWorkManyTM, skipTM,
        idleDir]
  | cons idx rest ih =>
      simpa [resetBinaryWorkManyTM] using
        (resetBinaryWorkTM_isTransducer idx).seqTM ih

end TM

end Complexity
