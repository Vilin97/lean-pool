/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# seqTM simulation — proof internals

This file contains the simulation lemmas for `seqTM tm₁ tm₂`.

## Key definitions

- `phase1Wrap` — embed a `tm₁` config into the `seqTM` config space
- `phase2Wrap` — embed a `tm₂` config into the `seqTM` config space
- Tape transformations use the shared `transitionTape` / `transitionInput`
-/


@[expose] public section

namespace Complexity

variable {n : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Config wrapping
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a `tm₁` configuration into the `seqTM` config space (Phase 1).
    State is wrapped in `Sum.inl`; tapes are shared. -/
def phase1Wrap (tm₁ : TM n) (tm₂ : TM n) (c₁ : Cfg n tm₁.Q) :
    Cfg n (SeqQ tm₁.Q tm₂.Q) where
  state := Sum.inl c₁.state
  input := c₁.input
  work := c₁.work
  output := c₁.output

/-- Embed a `tm₂` configuration into the `seqTM` config space (Phase 2).
    State is wrapped in `Sum.inr`; tapes are shared. -/
def phase2Wrap (tm₁ : TM n) (tm₂ : TM n) (c₂ : Cfg n tm₂.Q) :
    Cfg n (SeqQ tm₁.Q tm₂.Q) where
  state := Sum.inr c₂.state
  input := c₂.input
  work := c₂.work
  output := c₂.output

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: seqTM simulates tm₁ (via generic simulation lifting)
-- ════════════════════════════════════════════════════════════════════════

/-- One step of `tm₁` corresponds to one step of `seqTM` during Phase 1. -/
theorem seqTM_phase1_step (tm₁ tm₂ : TM n) {c₁ c₁' : Cfg n tm₁.Q}
    (hstep : tm₁.step c₁ = some c₁') :
    (seqTM tm₁ tm₂).step (phase1Wrap tm₁ tm₂ c₁) = some (phase1Wrap tm₁ tm₂ c₁') := by
  classical
  have hne := state_ne_qhalt_of_step hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  unfold step
  simp only [phase1Wrap, seqTM, ite_eq_right Sum.inl_ne_inr, ite_eq_right hne]

/-- Multi-step Phase 1 simulation. -/
theorem seqTM_reachesIn_phase1Wrap (tm₁ tm₂ : TM n) {t : ℕ}
    {c₁_start c₁_end : Cfg n tm₁.Q}
    (hreach : tm₁.reachesIn t c₁_start c₁_end) :
    (seqTM tm₁ tm₂).reachesIn t
      (phase1Wrap tm₁ tm₂ c₁_start) (phase1Wrap tm₁ tm₂ c₁_end) :=
  reachesIn_map (tm' := seqTM tm₁ tm₂) (phase1Wrap tm₁ tm₂)
    (fun _ _ => seqTM_phase1_step tm₁ tm₂) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Transition step
-- ════════════════════════════════════════════════════════════════════════

/-- When `tm₁` halts, one step of `seqTM` transitions to Phase 2. -/
theorem seqTM_transition_step (tm₁ tm₂ : TM n) {c₁ : Cfg n tm₁.Q}
    (hhalt : c₁.state = tm₁.qhalt) :
    (seqTM tm₁ tm₂).step (phase1Wrap tm₁ tm₂ c₁) =
      some (phase2Wrap tm₁ tm₂
        { state := tm₂.qstart,
          input := transitionInput c₁.input,
          work := fun i => transitionTape (c₁.work i),
          output := transitionTape c₁.output }) := by
  classical
  unfold step
  simp only [phase1Wrap, seqTM, ite_eq_right Sum.inl_ne_inr, hhalt, ↓reduceIte]
  congr 1

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: seqTM simulates tm₂ (via generic simulation lifting)
-- ════════════════════════════════════════════════════════════════════════

/-- One step of `tm₂` corresponds to one step of `seqTM` during Phase 2. -/
theorem seqTM_phase2_step (tm₁ tm₂ : TM n) {c₂ c₂' : Cfg n tm₂.Q}
    (hstep : tm₂.step c₂ = some c₂') :
    (seqTM tm₁ tm₂).step (phase2Wrap tm₁ tm₂ c₂) = some (phase2Wrap tm₁ tm₂ c₂') := by
  classical
  have hne := state_ne_qhalt_of_step hstep
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  unfold step
  simp only [phase2Wrap, seqTM, ite_eq_right (Sum.inr_injective.ne hne), ite_eq_right hne]

/-- Multi-step Phase 2 simulation. -/
theorem seqTM_reachesIn_phase2Wrap (tm₁ tm₂ : TM n) {t : ℕ}
    {c₂_start c₂_end : Cfg n tm₂.Q}
    (hreach : tm₂.reachesIn t c₂_start c₂_end) :
    (seqTM tm₁ tm₂).reachesIn t
      (phase2Wrap tm₁ tm₂ c₂_start) (phase2Wrap tm₁ tm₂ c₂_end) :=
  reachesIn_map (tm' := seqTM tm₁ tm₂) (phase2Wrap tm₁ tm₂)
    (fun _ _ => seqTM_phase2_step tm₁ tm₂) hreach

-- ════════════════════════════════════════════════════════════════════════
-- Full simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Full `seqTM` simulation combining all three phases. -/
theorem seqTM_reachesIn_of_reachesIn (tm₁ tm₂ : TM n)
    {t₁ : ℕ} {c₁_start c₁_end : Cfg n tm₁.Q}
    (hreach₁ : tm₁.reachesIn t₁ c₁_start c₁_end)
    (hhalt₁ : c₁_end.state = tm₁.qhalt)
    {t₂ : ℕ} {c₂_end : Cfg n tm₂.Q}
    (hreach₂ : tm₂.reachesIn t₂
      { state := tm₂.qstart,
        input := transitionInput c₁_end.input,
        work := fun i => transitionTape (c₁_end.work i),
        output := transitionTape c₁_end.output }
      c₂_end) :
    (seqTM tm₁ tm₂).reachesIn (t₁ + 1 + t₂)
      (phase1Wrap tm₁ tm₂ c₁_start)
      (phase2Wrap tm₁ tm₂ c₂_end) := by
  have hp1 := seqTM_reachesIn_phase1Wrap tm₁ tm₂ hreach₁
  have htrans := seqTM_transition_step tm₁ tm₂ hhalt₁
  have hp2 := seqTM_reachesIn_phase2Wrap tm₁ tm₂ hreach₂
  have h_tr : (seqTM tm₁ tm₂).reachesIn 1
      (phase1Wrap tm₁ tm₂ c₁_end) (phase2Wrap tm₁ tm₂ _) :=
    .step htrans .zero
  exact reachesIn_trans _ (reachesIn_trans _ hp1 h_tr) hp2

-- ════════════════════════════════════════════════════════════════════════
-- Halting and output in Phase 2
-- ════════════════════════════════════════════════════════════════════════

/-- A Phase-2 wrapped configuration is halted in `seqTM` iff the underlying `tm₂`
    configuration is halted. -/
theorem phase2Wrap_halted_iff (tm₁ tm₂ : TM n) (c₂ : Cfg n tm₂.Q) :
    (seqTM tm₁ tm₂).halted (phase2Wrap tm₁ tm₂ c₂) ↔ tm₂.halted c₂ := by
  simp [phase2Wrap, seqTM, halted, Cfg.isHalted]

/-- Wrapping a `tm₂` configuration into the `seqTM` config space leaves the output
    tape unchanged. -/
theorem phase2Wrap_output (tm₁ tm₂ : TM n) (c₂ : Cfg n tm₂.Q) :
    (phase2Wrap tm₁ tm₂ c₂).output = c₂.output := rfl

end TM

end Complexity
