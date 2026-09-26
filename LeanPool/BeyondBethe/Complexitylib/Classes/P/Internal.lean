/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Union

/-!
# P closure properties — proof internals

This file contains the proof helpers used by `DTIME_union` (stated in `P.lean`).
The key simulation theorem `unionTM_decidesInTime` establishes that the
composite machine from `TM.unionTM` correctly decides `L₁ ∪ L₂`.
-/


@[expose] public section

namespace Complexity

open Complexity Asymptotics Filter

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Core simulation theorem
-- ════════════════════════════════════════════════════════════════════════

/-- The union TM correctly decides `L₁ ∪ L₂` with time bound `10·f₁ + f₂`.

    The factor 10 arises from Phase 1 (f₁ steps), transition (≤ 2·f₁ + 7 steps
    absorbed into 9·f₁ since f₁ ≥ 1), and Phase 2 (f₂ steps). -/
theorem unionTM_decidesInTime {tm₁ : TM n₁} {tm₂ : TM n₂}
    {L₁ L₂ : Language} {f₁ f₂ : ℕ → ℕ}
    (h₁ : tm₁.DecidesInTime L₁ f₁) (h₂ : tm₂.DecidesInTime L₂ f₂) :
    (unionTM tm₁ tm₂).DecidesInTime (L₁ ∪ L₂) (fun n => 10 * f₁ n + f₂ n) := by
  have hne₁ := qstart_ne_qhalt_of_decidesInTime _ h₁
  have hne₂ := qstart_ne_qhalt_of_decidesInTime _ h₂
  intro x
  obtain ⟨c₁, t₁, ht₁, hreach₁, hhalt₁, hmem₁, hnmem₁⟩ := h₁ x
  obtain ⟨c₂, t₂, ht₂, hreach₂, hhalt₂, hmem₂, hnmem₂⟩ := h₂ x
  -- t₁ ≥ 1 since qstart ≠ qhalt (halting at step 0 means qstart = qhalt)
  have ht₁_pos : t₁ ≥ 1 := by
    rcases t₁ with _ | t₁
    · cases hreach₁; exact absurd hhalt₁ hne₁
    · omega
  have ht₂_pos : t₂ ≥ 1 := by
    rcases t₂ with _ | t₂
    · cases hreach₂; exact absurd hhalt₂ hne₂
    · omega
  -- Head bounds: tape heads are ≤ t₁ after Phase 1
  have hbounds := head_le_of_reachesIn tm₁ hreach₁
  -- Phase 1: union machine simulates tm₁ for t₁ steps
  have hphase1 := unionTM_phase1_simulation tm₁ tm₂ x hreach₁ ht₁_pos
  -- Case split on whether tm₁ accepted
  by_cases hx₁ : x ∈ L₁
  · -- tm₁ accepted: output cell 1 = Γ.one
    have hcell := hmem₁ hx₁
    -- Derive output tape invariants from reachesIn
    have hcell0_out := output_cells_zero_eq_start_of_reachesIn hreach₁ (Tape.init_cells_zero _)
    have hnostart_out := output_cells_ne_start_of_reachesIn hreach₁
      (fun i hi => Tape.init_nil_cells_ne_start i hi)
    -- Transition: rewind fake output, check, write Γ.one to real output, halt
    obtain ⟨t_tr, c_final, htrans, hhalt_f, hout_f, htr_bound⟩ :=
      unionTM_transition_accept tm₁ tm₂ hhalt₁ hcell hcell0_out hnostart_out
    -- Combine Phase 1 + transition
    have hoh := hbounds.2.1  -- c₁.output.head ≤ t₁
    refine ⟨c_final, t₁ + t_tr, ?_, reachesIn_trans _ hphase1 htrans, hhalt_f, ?_, ?_⟩
    · show t₁ + t_tr ≤ 10 * f₁ x.length + f₂ x.length; omega
    · exact fun _ => hout_f
    · intro hx; exfalso; exact hx (Or.inl hx₁)
  · -- tm₁ rejected: output cell 1 = Γ.zero
    have hcell := hnmem₁ hx₁
    -- Derive output tape and input tape invariants from reachesIn
    have hcell0_out := output_cells_zero_eq_start_of_reachesIn hreach₁ (Tape.init_cells_zero _)
    have hnostart_out := output_cells_ne_start_of_reachesIn hreach₁
      (fun i hi => Tape.init_nil_cells_ne_start i hi)
    have hinput_cells := input_cells_eq_of_reachesIn hreach₁
    -- Transition: full transition to Phase 2
    obtain ⟨t_tr, c_mid, htrans, hmid_state, hmid_input, hmid_work, hmid_output, htr_bound⟩ :=
      unionTM_transition_reject tm₁ tm₂ x hhalt₁ hcell hcell0_out hnostart_out hinput_cells
    -- Phase 2: union machine simulates tm₂ for t₂ steps
    obtain ⟨c_end, hphase2, hend_state, hend_output⟩ :=
      unionTM_phase2_simulation tm₁ tm₂ x hreach₂ hmid_state hmid_input hmid_work hmid_output
    -- Combine Phase 1 + transition + Phase 2
    have hfull := reachesIn_trans _ (reachesIn_trans _ hphase1 htrans) hphase2
    -- The final config is halted
    have hfinal_halted : (unionTM tm₁ tm₂).halted c_end := by
      show c_end.state = Sum.inr (Sum.inr tm₂.qhalt)
      rw [hend_state, hhalt₂]
    have hih := hbounds.1    -- c₁.input.head ≤ t₁
    have hoh := hbounds.2.1  -- c₁.output.head ≤ t₁
    refine ⟨c_end, t₁ + t_tr + t₂, ?_, hfull, hfinal_halted, ?_, ?_⟩
    · show t₁ + t_tr + t₂ ≤ 10 * f₁ x.length + f₂ x.length; omega
    · intro hx; rw [hend_output]; cases hx with
      | inl h => exact absurd h hx₁
      | inr h => exact hmem₂ h
    · intro hx; rw [hend_output]
      have : x ∉ L₂ := fun h => hx (Set.mem_union_right _ h)
      exact hnmem₂ this

end TM

-- ════════════════════════════════════════════════════════════════════════
-- BigO arithmetic: 10·f₁ + f₂ =O (T₁ + T₂)
-- ════════════════════════════════════════════════════════════════════════

/-- If `f₁ =O T₁` and `f₂ =O T₂`, then `10·f₁ + f₂ =O (T₁ + T₂)`. -/
theorem bigO_union_bound {f₁ f₂ T₁ T₂ : ℕ → ℕ}
    (ho₁ : f₁ =O T₁) (ho₂ : f₂ =O T₂) :
    (fun n => 10 * f₁ n + f₂ n) =O (fun n => T₁ n + T₂ n) :=
  BigO.const_mul_add 10 ho₁ ho₂

end Complexity
