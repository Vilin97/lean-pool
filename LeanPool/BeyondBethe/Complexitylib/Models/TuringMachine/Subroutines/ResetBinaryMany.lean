/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany.Internal

/-!
# Resetting several binary work tapes

This module exposes a framed compositional contract for resetting a fixed list
of distinct canonical binary work tapes.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A reset list has a uniform linear bound when every target head and
represented bit string is bounded uniformly. -/
theorem resetBinaryWorkManyTime_le
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (headBound : Fin n → ℕ) (maxHead maxWidth : ℕ)
    (hhead : ∀ i, i ∈ targets → headBound i ≤ maxHead)
    (hwidth : ∀ i, i ∈ targets → (bits i).length ≤ maxWidth) :
    resetBinaryWorkManyTime bits headBound targets ≤
      targets.length * (maxHead + 2 * maxWidth + 9) + 1 :=
  resetBinaryWorkManyTime_le_internal targets bits headBound maxHead maxWidth
    hhead hwidth

/-- Every targeted work tape is the standard parked blank after the reset
sequence. -/
theorem resetBinaryWorkManyResult_eq_blank_of_mem
    (work₀ : Fin n → Tape) (targets : List (Fin n)) (idx : Fin n)
    (hidx : idx ∈ targets) :
    resetBinaryWorkManyResult work₀ targets idx = resetBinaryBlank :=
  resetBinaryWorkManyResult_eq_blank_of_mem_internal work₀ targets idx hidx

/-- Work tapes outside the target list are preserved literally. -/
theorem resetBinaryWorkManyResult_eq_of_not_mem
    (work₀ : Fin n → Tape) (targets : List (Fin n)) (idx : Fin n)
    (hidx : idx ∉ targets) :
    resetBinaryWorkManyResult work₀ targets idx = work₀ idx :=
  resetBinaryWorkManyResult_eq_of_not_mem_internal work₀ targets idx hidx

/-- Resetting a list of work tapes preserves parkedness of the whole work
family. -/
theorem resetBinaryWorkManyResult_parked
    (work₀ : Fin n → Tape) (targets : List (Fin n))
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (resetBinaryWorkManyResult work₀ targets i) :=
  resetBinaryWorkManyResult_parked_internal work₀ targets hwork

/-- The reset-sequence time depends on head bounds only at named targets. -/
theorem resetBinaryWorkManyTime_congr_headBound
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (left right : Fin n → ℕ)
    (heq : ∀ i, i ∈ targets → left i = right i) :
    resetBinaryWorkManyTime bits left targets =
      resetBinaryWorkManyTime bits right targets :=
  resetBinaryWorkManyTime_congr_headBound_internal targets bits left right heq

/-- Sequentially reset a distinct list of canonical binary work tapes while
preserving the complete external frame. -/
theorem resetBinaryWorkManyTM_hoareTime_frame
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
      (resetBinaryWorkManyTime bits headBound targets) :=
  resetBinaryWorkManyTM_hoareTime_frame_internal targets bits headBound inp₀
    work₀ out₀ hnodup htarget htargetStart htargetHead hinput hwork houtput

/-- Resetting several binary work tapes preserves one-way output safety. -/
theorem resetBinaryWorkManyTM_isTransducer (targets : List (Fin n)) :
    (resetBinaryWorkManyTM targets).IsTransducer :=
  resetBinaryWorkManyTM_isTransducer_internal targets

/-- Coarse all-prefix auxiliary-space envelope for a reset sequence. -/
theorem resetBinaryWorkManyTM_prefix_withinAuxSpace
    (targets : List (Fin n)) (bits : Fin n → List Bool)
    (headBound : Fin n → ℕ) (inputLength initialSpace time : ℕ)
    (start current : Cfg n (resetBinaryWorkManyTM targets).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (resetBinaryWorkManyTM targets).reachesIn time start current)
    (htime : time ≤ resetBinaryWorkManyTime bits headBound targets) :
    current.WithinAuxSpace inputLength
      (initialSpace + resetBinaryWorkManyTime bits headBound targets) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

end TM

end Complexity
