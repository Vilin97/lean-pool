/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal

/-!
# unionTM simulation — proof internals

This file contains the simulation lemmas needed to prove that `unionTM tm₁ tm₂`
correctly decides `L₁ ∪ L₂` when `tm₁` decides `L₁` and `tm₂` decides `L₂`.

## Strategy

The proof proceeds in three phases:

1. **Phase 1 simulation**: Show that the union machine faithfully simulates
   `tm₁` for `t₁` steps, with tm₁'s output redirected to the fake output
   tape (work tape `n₁`).

2. **Transition phase**: After Phase 1, the machine rewinds the fake output
   to check tm₁'s result. If tm₁ accepted (cell 1 = `Γ.one`), write `Γ.one`
   to the real output and halt. Otherwise, rewind the input and start Phase 2.

3. **Phase 2 simulation**: Simulate `tm₂` using the real output tape.

## Key definitions

- `unionIdleTape` — the steady-state of an idle tape (head at 1, cells from `Tape.init []`)
- `unionPhase1Cfg` — embedding of a tm₁ config into the union machine's config space
-/


public section

namespace Complexity

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Idle tape
-- ════════════════════════════════════════════════════════════════════════

/-- The steady-state tape for an idle tape during Phase 1.
    After the first step (where `δ_right_of_start` forces a right move from
    cell 0), idle tapes remain at head position 1 with blank cells. -/
def unionIdleTape : Tape :=
  { head := 1, cells := (Tape.init ([] : List Γ)).cells }

private theorem idleTape_read : unionIdleTape.read = Γ.blank := by
  simp [unionIdleTape, Tape.read, Tape.init]

/-- Writing blank to an idle tape at position 1 is a no-op. -/
private theorem idleTape_write_blank : unionIdleTape.write Γ.blank = unionIdleTape := by
  simp [unionIdleTape, Tape.write, Tape.init, Function.update_eq_self_iff]

/-- An idle tape stays idle when written with blank and moved by idleDir. -/
private theorem idleTape_step_idle :
    (unionIdleTape.write Γw.blank.toΓ).move (idleDir unionIdleTape.read) = unionIdleTape := by
  show (unionIdleTape.write Γ.blank).move (idleDir unionIdleTape.read) = unionIdleTape
  rw [idleTape_read, idleDir, if_neg (by decide)]
  simp [idleTape_write_blank, Tape.move]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1 config embedding
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a tm₁ configuration into the union machine's config space.
    Active tapes (input, work 0..n₁-1, fake output at n₁) come from `c`.
    Idle tapes (work n₁+1..n₁+n₂ and real output) use `unionIdleTape`. -/
def unionPhase1Cfg (tm₁ : TM n₁) (tm₂ : TM n₂) (c : Cfg n₁ tm₁.Q) :
    Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) where
  state := Sum.inl c.state
  input := c.input
  work := fun i =>
    if h : i.val < n₁ then c.work ⟨i.val, h⟩
    else if i.val = n₁ then c.output
    else unionIdleTape
  output := unionIdleTape

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1: one-step correspondence
-- ════════════════════════════════════════════════════════════════════════

/-- Key computation: unionTM.δ for a Phase 1 non-halted state delegates to tm₁.δ. -/
private theorem unionTM_delta_inl (tm₁ : TM n₁) (tm₂ : TM n₂) {q : tm₁.Q}
    (hne : q ≠ tm₁.qhalt) (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ) :
    (unionTM tm₁ tm₂).δ (Sum.inl q) iHead wHeads oHead =
    let r := tm₁.δ q iHead (phase1WorkReads wHeads) (wHeads fakeOutIdx)
    (Sum.inl r.1,
     fun i => if h : i.val < n₁ then r.2.1 ⟨i.val, h⟩ else if i.val = n₁ then r.2.2.1 else .blank,
     .blank, r.2.2.2.1,
     fun i => if h : i.val < n₁ then r.2.2.2.2.1 ⟨i.val, h⟩
              else if i.val = n₁ then r.2.2.2.2.2 else idleDir (wHeads i),
     idleDir oHead) := by
  simp only [unionTM, if_neg hne]

private theorem unionTM_qhalt (tm₁ : TM n₁) (tm₂ : TM n₂) :
    (unionTM tm₁ tm₂).qhalt = Sum.inr (Sum.inr tm₂.qhalt) := rfl

/-- Key computation: unionTM.δ for a Phase 2 non-halted state delegates to tm₂.δ. -/
private theorem unionTM_delta_inr_inr (tm₁ : TM n₁) (tm₂ : TM n₂) {q : tm₂.Q}
    (hne : q ≠ tm₂.qhalt) (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inr q)) iHead wHeads oHead =
    let r := tm₂.δ q iHead (phase2WorkReads wHeads) oHead
    (Sum.inr (Sum.inr r.1),
     fun i => if h : i.val ≤ n₁ then (Γw.blank : Γw) else r.2.1 ⟨i.val - (n₁ + 1), by omega⟩,
     r.2.2.1, r.2.2.2.1,
     fun i => if h : i.val ≤ n₁ then idleDir (wHeads i)
              else r.2.2.2.2.1 ⟨i.val - (n₁ + 1), by omega⟩,
     r.2.2.2.2.2) := by
  simp only [unionTM, if_neg hne]

private theorem phase1Cfg_state (tm₁ : TM n₁) (tm₂ : TM n₂) (c : Cfg n₁ tm₁.Q) :
    (unionPhase1Cfg tm₁ tm₂ c).state = Sum.inl c.state := rfl

private theorem phase1_step_corr (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c c' : Cfg n₁ tm₁.Q} (hstep : tm₁.step c = some c') :
    (unionTM tm₁ tm₂).step (unionPhase1Cfg tm₁ tm₂ c) = some (unionPhase1Cfg tm₁ tm₂ c') := by
  have hne := state_ne_qhalt_of_step hstep
  -- Extract c' from tm₁.step
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  -- Unfold step for unionTM on unionPhase1Cfg
  simp only [step, phase1Cfg_state, unionTM_qhalt]
  simp only [reduceCtorEq, ↓reduceIte]
  apply congrArg some
  -- Rewrite the δ call using our helper
  simp only [unionTM_delta_inl tm₁ tm₂ hne]
  -- Now unfold unionPhase1Cfg on both sides and simplify
  dsimp only [unionPhase1Cfg]
  -- Establish that the δ calls produce the same result
  have hfake_read : (if h : (n₁ : ℕ) < n₁ then c.work ⟨n₁, h⟩
      else if (n₁ : ℕ) = n₁ then c.output else unionIdleTape).read = c.output.read := by
    rw [dif_neg (Nat.lt_irrefl n₁), if_pos rfl]
  have hwork_reads : (phase1WorkReads fun i : Fin (n₁ + 1 + n₂) =>
      (if h : i.val < n₁ then c.work ⟨i.val, h⟩
       else if i.val = n₁ then c.output else unionIdleTape).read) =
      fun j => (c.work j).read := by
    ext ⟨j, hj⟩; simp only [phase1WorkReads]; rw [dif_pos (show j < n₁ from hj)]
  -- Simplify fakeOutIdx to ⟨n₁, _⟩ and reduce the dite conditions
  simp only [fakeOutIdx] at hfake_read ⊢
  -- Rewrite the work reads and fake output read
  simp_rw [hwork_reads, hfake_read]
  -- State and input match by rfl; work and output need case analysis
  have hcfg : ∀ (a b : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
      a.state = b.state → a.input = b.input → a.work = b.work → a.output = b.output → a = b := by
    intros a b hs hi hw ho; cases a; cases b; simp_all
  apply hcfg
  · rfl  -- state
  · rfl  -- input
  · -- work tapes: case split on i
    funext i; dsimp only []; split
    · rfl  -- i < n₁: active work tape
    · split
      · rfl  -- i = n₁: fake output
      · -- i > n₁: idle tape stays idle
        exact idleTape_step_idle
  · -- output: idle tape stays idle
    exact idleTape_step_idle

-- ════════════════════════════════════════════════════════════════════════
-- Phase 1 simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Multi-step Phase 1: if tm₁ takes t steps from c to c', the union machine
    takes t steps from unionPhase1Cfg c to unionPhase1Cfg c'. -/
private theorem phase1_steps (tm₁ : TM n₁) (tm₂ : TM n₂)
    {t : ℕ} {c c' : Cfg n₁ tm₁.Q}
    (hreach : tm₁.reachesIn t c c') :
    (unionTM tm₁ tm₂).reachesIn t (unionPhase1Cfg tm₁ tm₂ c) (unionPhase1Cfg tm₁ tm₂ c') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (phase1_step_corr tm₁ tm₂ hstep) ih

/-- The first step of unionTM on initCfg produces unionPhase1Cfg of tm₁'s first step result.
    At step 0, all tapes are at cell 0 with ▷, so δ_right_of_start forces right moves.
    After this step, idle tapes become unionIdleTape (head=1, blank cells). -/
private theorem phase1_init_step (tm₁ : TM n₁) (tm₂ : TM n₂) (x : List Bool)
    {c_mid : Cfg n₁ tm₁.Q} (hstep : tm₁.step (tm₁.initCfg x) = some c_mid) :
    (unionTM tm₁ tm₂).step ((unionTM tm₁ tm₂).initCfg x) = some (unionPhase1Cfg tm₁ tm₂ c_mid) := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [step] at hstep ⊢
  rw [if_neg hne] at hstep
  simp only [Option.some.injEq] at hstep
  subst hstep
  -- Unfold unionTM qstart/qhalt
  rw [show (unionTM tm₁ tm₂).qstart = Sum.inl tm₁.qstart from rfl,
      show (unionTM tm₁ tm₂).qhalt = Sum.inr (Sum.inr tm₂.qhalt) from rfl]
  simp only [reduceCtorEq, ↓reduceIte]
  apply congrArg some
  -- Rewrite the unionTM δ call
  simp only [unionTM_delta_inl tm₁ tm₂ hne]
  -- The phase1WorkReads of fixedValue function is a fixedValue function
  have hwork_reads :
      phase1WorkReads (fun (_ : Fin (n₁ + 1 + n₂)) => (Tape.init ([] : List Γ)).read) =
      fun _ => (Tape.init ([] : List Γ)).read := by ext; rfl
  simp_rw [hwork_reads]
  -- Now the δ calls match; show Cfg equality field by field
  have hcfg : ∀ (a b : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
      a.state = b.state → a.input = b.input → a.work = b.work → a.output = b.output → a = b := by
    intros a b hs hi hw ho; cases a; cases b; simp_all
  apply hcfg
  · rfl  -- state
  · rfl  -- input
  · -- work tapes
    funext i; dsimp only [unionPhase1Cfg]; split
    · -- i < n₁: all tapes start at Tape.init [], write at head 0 is no-op
      simp [Tape.init, Tape.read]
    · split
      · -- i = n₁
        simp [Tape.init, Tape.read]
      · -- i > n₁: becomes unionIdleTape
        simp [Tape.init, Tape.write, Tape.read, unionIdleTape, idleDir, Tape.move]
  · -- output: becomes unionIdleTape (unionPhase1Cfg always has unionIdleTape as output)
    simp only [unionPhase1Cfg]
    simp [Tape.init, Tape.write, Tape.read, idleDir, Tape.move, unionIdleTape]

/-- **Phase 1 simulation**: if `tm₁` reaches `c₁` from `initCfg x` in `t₁ ≥ 1`
    steps, the union machine reaches the embedded config `unionPhase1Cfg c₁`
    from its own `initCfg x` in the same number of steps. -/
theorem unionTM_phase1_simulation (tm₁ : TM n₁) (tm₂ : TM n₂) (x : List Bool)
    {t₁ : ℕ} {c₁ : Cfg n₁ tm₁.Q}
    (hreach : tm₁.reachesIn t₁ (tm₁.initCfg x) c₁)
    (ht₁ : t₁ ≥ 1) :
    (unionTM tm₁ tm₂).reachesIn t₁ ((unionTM tm₁ tm₂).initCfg x)
      (unionPhase1Cfg tm₁ tm₂ c₁) := by
  -- Split the first step off
  cases hreach with
  | zero => omega  -- contradicts t₁ ≥ 1
  | step hstep hrest =>
    exact .step (phase1_init_step tm₁ tm₂ x hstep) (phase1_steps tm₁ tm₂ hrest)

/-- If a tape has head ≥ 1 and cells[≥1] ≠ start, idleDir gives stay (head unchanged). -/
private theorem idleDir_stay_of_ge_one (t : Tape)
    (hhead : t.head ≥ 1) (hno : ∀ i, i ≥ 1 → t.cells i ≠ Γ.start) :
    idleDir t.read = Dir3.stay := by
  rw [idleDir, if_neg]; rw [Tape.read]; exact hno _ hhead

/-- Input head stays fixedValue when moved by idleDir if head ≥ 1 and cells[≥1] ≠ start. -/
private theorem idle_move_preserves_head (t : Tape)
    (hhead : t.head ≥ 1) (hno : ∀ i, i ≥ 1 → t.cells i ≠ Γ.start) :
    (t.move (idleDir t.read)).head = t.head := by
  rw [idleDir_stay_of_ge_one t hhead hno]; rfl

-- ════════════════════════════════════════════════════════════════════════
-- Union TM delta helpers for UnionPhase states
-- ════════════════════════════════════════════════════════════════════════

/-- Delta computation for rewindOut when fake output is not at start. -/
private theorem unionTM_delta_rewindOut_nostart (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : wHeads fakeOutIdx ≠ Γ.start) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.rewindOut)) iHead wHeads oHead =
    ( Sum.inr (Sum.inl UnionPhase.rewindOut),
      fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
      .blank, idleDir iHead,
      fun i => if i.val = n₁ then Dir3.left else idleDir (wHeads i),
      idleDir oHead ) := by
  unfold unionTM; simp only [if_neg hread]

/-- Delta computation for rewindOut when fake output is at start. -/
private theorem unionTM_delta_rewindOut_start (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : wHeads fakeOutIdx = Γ.start) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.rewindOut)) iHead wHeads oHead =
    ( Sum.inr (Sum.inl UnionPhase.checkResult),
      fun _ => .blank, .blank, idleDir iHead,
      fun i => if i.val = n₁ then Dir3.right else idleDir (wHeads i),
      idleDir oHead ) := by
  unfold unionTM; simp only [if_pos hread]

/-- Delta computation for checkResult when fake output reads Γ.one. -/
private theorem unionTM_delta_checkResult_one (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : wHeads fakeOutIdx = Γ.one) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.checkResult)) iHead wHeads oHead =
    ( Sum.inr (Sum.inr tm₂.qhalt),
      fun _ => .blank, .one, idleDir iHead,
      fun i => idleDir (wHeads i),
      idleDir oHead ) := by
  unfold unionTM; simp only [if_pos hread]

/-- Delta computation for checkResult when fake output does not read Γ.one. -/
private theorem unionTM_delta_checkResult_notone (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : wHeads fakeOutIdx ≠ Γ.one) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.checkResult)) iHead wHeads oHead =
    allIdle (Sum.inr (Sum.inl UnionPhase.rewindIn)) iHead wHeads oHead := by
  unfold unionTM; simp only [if_neg hread]

/-- Delta computation for rewindIn when input is not at start. -/
private theorem unionTM_delta_rewindIn_nostart (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : iHead ≠ Γ.start) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.rewindIn)) iHead wHeads oHead =
    ( Sum.inr (Sum.inl UnionPhase.rewindIn),
      fun _ => .blank, .blank, Dir3.left,
      fun i => idleDir (wHeads i),
      idleDir oHead ) := by
  simp only [unionTM, if_neg hread]

/-- Delta computation for rewindIn when input is at start. -/
private theorem unionTM_delta_rewindIn_start (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ)
    (hread : iHead = Γ.start) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.rewindIn)) iHead wHeads oHead =
    ( Sum.inr (Sum.inl UnionPhase.setup2),
      fun _ => .blank, .blank, Dir3.right,
      fun i => idleDir (wHeads i),
      idleDir oHead ) := by
  simp only [unionTM, if_pos hread]

/-- Delta computation for setup2. -/
private theorem unionTM_delta_setup2 (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ) :
    (unionTM tm₁ tm₂).δ (Sum.inr (Sum.inl UnionPhase.setup2)) iHead wHeads oHead =
    ( Sum.inr (Sum.inr tm₂.qstart),
      fun _ => .blank, .blank, moveLeftDir iHead,
      fun i => if i.val ≤ n₁ then idleDir (wHeads i) else moveLeftDir (wHeads i),
      moveLeftDir oHead ) := by
  unfold unionTM; rfl

/-- Delta computation for Phase 1 halted state (transition to rewindOut). -/
private theorem unionTM_delta_inl_qhalt (tm₁ : TM n₁) (tm₂ : TM n₂)
    (iHead : Γ) (wHeads : Fin (n₁ + 1 + n₂) → Γ) (oHead : Γ) :
    (unionTM tm₁ tm₂).δ (Sum.inl tm₁.qhalt) iHead wHeads oHead =
    ( Sum.inr (Sum.inl UnionPhase.rewindOut),
      fun i => if i.val = n₁ then readBackWrite (wHeads fakeOutIdx) else .blank,
      .blank,
      idleDir iHead,
      fun i => idleDir (wHeads i),
      idleDir oHead ) := by
  simp only [unionTM, ite_true]

-- ════════════════════════════════════════════════════════════════════════
-- One-step lemmas for union TM
-- ════════════════════════════════════════════════════════════════════════

/-- The union machine is not halted in any UnionPhase state. -/
private theorem unionTM_mid_not_halted (tm₁ : TM n₁) (tm₂ : TM n₂) (m : UnionPhase)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl m)) :
    c.state ≠ (unionTM tm₁ tm₂).qhalt := by
  rw [hstate]; exact fun h => nomatch h

/-- The union machine is not halted when in a Phase 1 state. -/
private theorem unionTM_inl_not_halted (tm₁ : TM n₁) (tm₂ : TM n₂) (q : tm₁.Q)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inl q) :
    c.state ≠ (unionTM tm₁ tm₂).qhalt := by
  rw [hstate]; exact fun h => nomatch h

/-- Step the union machine from a rewindOut state with non-start fake output read. -/
private theorem step_rewindOut_nostart_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.rewindOut))
    (hread : (c.work fakeOutIdx).read ≠ Γ.start) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.rewindOut),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write
          ((if i.val = n₁ then readBackWrite (c.work fakeOutIdx).read else .blank) : Γw).toΓ).move
          (if i.val = n₁ then Dir3.left else idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_neg hread]; rfl

/-- Step the union machine from a rewindOut state when fake output reads start. -/
private theorem step_rewindOut_start_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.rewindOut))
    (hread : (c.work fakeOutIdx).read = Γ.start) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.checkResult),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move
          (if i.val = n₁ then Dir3.right else idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_pos hread]; rfl

/-- Step the union machine from checkResult with Γ.one → halted. -/
private theorem step_checkResult_one_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.checkResult))
    (hread : (c.work fakeOutIdx).read = Γ.one) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inr tm₂.qhalt),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c.work i).read),
        output := (c.output.write Γw.one.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_pos hread]; rfl

/-- Step the union machine from checkResult when not Γ.one → rewindIn (allIdle). -/
private theorem step_checkResult_notone_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.checkResult))
    (hread : (c.work fakeOutIdx).read ≠ Γ.one) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.rewindIn),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_neg hread, allIdle]; rfl

/-- Step the union machine from rewindIn with non-start input. -/
private theorem step_rewindIn_nostart_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.rewindIn))
    (hread : c.input.read ≠ Γ.start) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.rewindIn),
        input := c.input.move Dir3.left,
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_neg hread]; rfl

/-- Step the union machine from rewindIn when input reads start. -/
private theorem step_rewindIn_start_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.rewindIn))
    (hread : c.input.read = Γ.start) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.setup2),
        input := c.input.move Dir3.right,
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, if_pos hread]; rfl

/-- Step the union machine from setup2. -/
private theorem step_setup2_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inr (Sum.inl UnionPhase.setup2)) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inr tm₂.qstart),
        input := c.input.move (moveLeftDir c.input.read),
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move
          (if i.val ≤ n₁ then idleDir (c.work i).read else moveLeftDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (moveLeftDir c.output.read) } := by
  simp only [step]; rw [hstate]; rfl

/-- Step the union machine from unionPhase1Cfg when tm₁ halted. -/
private theorem step_inl_qhalt_cfg (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hstate : c.state = Sum.inl tm₁.qhalt) :
    (unionTM tm₁ tm₂).step c = some
      { state := Sum.inr (Sum.inl UnionPhase.rewindOut),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write
          ((if i.val = n₁ then readBackWrite (c.work fakeOutIdx).read else .blank) : Γw).toΓ).move
          (idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) } := by
  simp only [step]; rw [hstate]; simp only [unionTM, ite_true]; rfl

-- ════════════════════════════════════════════════════════════════════════
-- Rewind fake output loop
-- ════════════════════════════════════════════════════════════════════════

/-- readBackWrite preserves cells at non-zero head positions. -/
private theorem write_readBack_cells_eq (t : Tape) (hne : t.read ≠ Γ.start) :
    (t.write (readBackWrite t.read).toΓ).cells = t.cells := by
  rw [toΓ_readBackWrite_of_ne_start hne]
  simp only [Tape.write]
  split
  · rfl
  · ext i; simp only [Function.update]; split
    · next heq => subst heq; rfl
    · rfl

-- ════════════════════════════════════════════════════════════════════════
-- Transition phase: accept path (x ∈ L₁)
-- ════════════════════════════════════════════════════════════════════════

/-- unionPhase1Cfg output is unionIdleTape. -/
private theorem phase1Cfg_output (tm₁ : TM n₁) (tm₂ : TM n₂) (c : Cfg n₁ tm₁.Q) :
    (unionPhase1Cfg tm₁ tm₂ c).output = unionIdleTape := rfl

/-- unionPhase1Cfg fake output tape is c.output. -/
private theorem phase1Cfg_fakeOut (tm₁ : TM n₁) (tm₂ : TM n₂) (c : Cfg n₁ tm₁.Q) :
    (unionPhase1Cfg tm₁ tm₂ c).work fakeOutIdx = c.output := by
  simp [unionPhase1Cfg, fakeOutIdx]

/-- One step from unionPhase1Cfg when tm₁ is halted transitions to rewindOut. -/
private theorem step_phase1_halted (tm₁ : TM n₁) (tm₂ : TM n₂)
    (c₁ : Cfg n₁ tm₁.Q) (hhalt : tm₁.halted c₁)
    (hnostart_out : ∀ i, i ≥ 1 → c₁.output.cells i ≠ Γ.start) :
    ∃ c', (unionTM tm₁ tm₂).step (unionPhase1Cfg tm₁ tm₂ c₁) = some c' ∧
      c'.state = Sum.inr (Sum.inl UnionPhase.rewindOut) ∧
      (c'.work fakeOutIdx).cells = c₁.output.cells ∧
      c'.output = (unionIdleTape.write Γw.blank.toΓ).move (idleDir unionIdleTape.read) := by
  have hstate : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
    show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
  have hstep := step_inl_qhalt_cfg tm₁ tm₂ hstate
  -- The result config
  set c' : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inl UnionPhase.rewindOut),
      input := (unionPhase1Cfg tm₁ tm₂ c₁).input.move
        (idleDir (unionPhase1Cfg tm₁ tm₂ c₁).input.read),
      work := fun i => (((unionPhase1Cfg tm₁ tm₂ c₁).work i).write
        ((if i.val = n₁ then readBackWrite ((unionPhase1Cfg tm₁ tm₂ c₁).work fakeOutIdx).read
          else .blank) : Γw).toΓ).move
        (idleDir ((unionPhase1Cfg tm₁ tm₂ c₁).work i).read),
      output := ((unionPhase1Cfg tm₁ tm₂ c₁).output.write Γw.blank.toΓ).move
        (idleDir (unionPhase1Cfg tm₁ tm₂ c₁).output.read) } with hc'_def
  refine ⟨c', hstep, rfl, ?_, ?_⟩
  · -- fake output cells preserved
    simp only [hc'_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
    rw [phase1Cfg_fakeOut]
    rw [Tape.move_cells]
    simp only [Tape.write]
    split
    · rfl  -- head = 0: write is no-op
    · next hne =>
      -- head ≠ 0: readBackWrite writes back the same value
      have hread_ne : c₁.output.read ≠ Γ.start := by
        rw [Tape.read]; exact hnostart_out _ (by omega)
      rw [toΓ_readBackWrite_of_ne_start hread_ne, Tape.read]
      exact Function.update_eq_self _ _
  · -- output is unionIdleTape write blank / move idle
    simp only [hc'_def, phase1Cfg_output]

/-- Rewind the fake output tape, tracking all loop invariants:
    state, fakeOut head/cells, output = unionIdleTape, and conditionally
    input head preservation and work tape idleness for tapes > n₁. -/
private theorem rewind_fakeOut_loop (tm₁ : TM n₁) (tm₂ : TM n₂) :
    ∀ (h : ℕ) (c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
    c.state = Sum.inr (Sum.inl UnionPhase.rewindOut) →
    c.output = unionIdleTape →
    (c.work fakeOutIdx).head = h →
    (c.work fakeOutIdx).cells 0 = Γ.start →
    (∀ i, i ≥ 1 → (c.work fakeOutIdx).cells i ≠ Γ.start) →
    ∃ c', (unionTM tm₁ tm₂).reachesIn h c c' ∧
      c'.state = Sum.inr (Sum.inl UnionPhase.rewindOut) ∧
      (c'.work fakeOutIdx).head = 0 ∧
      (c'.work fakeOutIdx).cells = (c.work fakeOutIdx).cells ∧
      c'.output = unionIdleTape ∧
      (c.input.head ≥ 1 → (∀ i, i ≥ 1 → c.input.cells i ≠ Γ.start) →
        c'.input.head = c.input.head) ∧
      (∀ i : Fin (n₁ + 1 + n₂), i.val > n₁ → c.work i = unionIdleTape →
        c'.work i = unionIdleTape) := by
  intro h
  induction h with
  | zero =>
    intro c hst hout hhead _ _
    exact ⟨c, .zero, hst, hhead, rfl, hout, fun _ _ => rfl, fun _ _ h => h⟩
  | succ n ih =>
    intro c hst hout hhead hcell0 hnostart
    have hread_ne : (c.work fakeOutIdx).read ≠ Γ.start := by
      rw [Tape.read]; exact hnostart _ (by omega)
    have hstep := step_rewindOut_nostart_cfg tm₁ tm₂ hst hread_ne
    set c' : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
      { state := Sum.inr (Sum.inl UnionPhase.rewindOut),
        input := c.input.move (idleDir c.input.read),
        work := fun i => ((c.work i).write
          ((if i.val = n₁ then readBackWrite (c.work fakeOutIdx).read else .blank) : Γw).toΓ).move
          (if i.val = n₁ then Dir3.left else idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) }
      with hc'_def
    have hout' : c'.output = unionIdleTape := by
      simp only [hc'_def]; rw [hout, idleTape_step_idle]
    have hhead' : (c'.work fakeOutIdx).head = n := by
      simp only [hc'_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
      rw [toΓ_readBackWrite_of_ne_start hread_ne]; simp only [Tape.write]
      split
      · omega
      · simp [Tape.move, hhead]
    have hcells' : (c'.work fakeOutIdx).cells = (c.work fakeOutIdx).cells := by
      simp only [hc'_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
      rw [Tape.move_cells, write_readBack_cells_eq _ hread_ne]
    obtain ⟨c'', hreach, hst'', hhead'', hcells'', hout'', hinp'', hwork''⟩ :=
      ih c' rfl hout' hhead'
        (by rw [hcells']; exact hcell0)
        (by intro i hi; rw [hcells']; exact hnostart i hi)
    refine ⟨c'', .step hstep hreach, hst'', hhead'', by rw [hcells'', hcells'], hout'',
      fun hih hino => ?_, fun i hi hidle => ?_⟩
    · -- Input head: chain c → c' → c''
      have hih' : c'.input.head = c.input.head := idle_move_preserves_head _ hih hino
      have hino' : ∀ i, i ≥ 1 → c'.input.cells i ≠ Γ.start := by
        intro i hi; show (c.input.move _).cells i ≠ _; rw [Tape.move_cells]; exact hino i hi
      rw [hinp'' (by omega) hino', hih']
    · -- Work tapes: chain c → c' → c''
      have hidle' : c'.work i = unionIdleTape := by
        simp only [hc'_def, show (i : ℕ) ≠ n₁ from by omega, ↓reduceIte]
        rw [hidle]; exact idleTape_step_idle
      exact hwork'' i hi hidle'

/-- After Phase 1, if tm₁ accepted (output cell 1 = `Γ.one`), the union
    machine rewinds the fake output, checks the result, writes `Γ.one` to
    the real output, and halts. -/
theorem unionTM_transition_accept (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c₁ : Cfg n₁ tm₁.Q}
    (hhalt : tm₁.halted c₁)
    (haccept : c₁.output.cells 1 = Γ.one)
    (hcell0 : c₁.output.cells 0 = Γ.start)
    (hnostart : ∀ i, i ≥ 1 → c₁.output.cells i ≠ Γ.start) :
    ∃ (t_tr : ℕ) (c_final : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
      (unionTM tm₁ tm₂).reachesIn t_tr (unionPhase1Cfg tm₁ tm₂ c₁) c_final ∧
      (unionTM tm₁ tm₂).halted c_final ∧
      c_final.output.cells 1 = Γ.one ∧
      t_tr ≤ c₁.output.head + 4 := by
  -- Step 1: unionPhase1Cfg → rewindOut (1 step)
  obtain ⟨c_rw, hstep1, hst_rw, hcells_rw, hout_rw⟩ :=
    step_phase1_halted tm₁ tm₂ c₁ hhalt hnostart
  -- Head bound for the fake output after step 1
  have hfo_head_bound : (c_rw.work fakeOutIdx).head ≤ c₁.output.head + 1 := by
    have hstate : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
      show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
    have hexp := (step_inl_qhalt_cfg tm₁ tm₂ hstate).symm.trans hstep1
    rw [Option.some.injEq] at hexp
    rw [← hexp]
    simp only [phase1Cfg_fakeOut]
    have hmv : ∀ (t : Tape) (d : Dir3), (t.move d).head ≤ t.head + 1 := by
      intro t d; cases d <;> simp [Tape.move]; omega
    have hwh : ∀ (t : Tape) (s : Γ), (t.write s).head = t.head := by
      intro t s; simp [Tape.write]; split <;> rfl
    calc ((c₁.output.write _).move _).head ≤ (c₁.output.write _).head + 1 := hmv _ _
      _ = c₁.output.head + 1 := by rw [hwh]
  -- Fake output cells preserved
  have hcell0_rw : (c_rw.work fakeOutIdx).cells 0 = Γ.start := by
    rw [hcells_rw]; exact hcell0
  have hnostart_rw : ∀ i, i ≥ 1 → (c_rw.work fakeOutIdx).cells i ≠ Γ.start := by
    intro i hi; rw [hcells_rw]; exact hnostart i hi
  -- c_rw.output = unionIdleTape
  have hout_rw_eq : c_rw.output = unionIdleTape := by
    rw [hout_rw]; exact idleTape_step_idle
  -- Step 2: Rewind loop (h_rw steps), also preserving output = unionIdleTape
  set h_rw := (c_rw.work fakeOutIdx).head with hh_rw_def
  obtain ⟨c_at0, hreach_rw, hst_at0, hhead_at0, hcells_at0, hout_at0, -, -⟩ :=
    rewind_fakeOut_loop tm₁ tm₂ h_rw c_rw hst_rw hout_rw_eq rfl hcell0_rw hnostart_rw
  -- Step 3: rewindOut at head 0 → checkResult (1 step)
  have hread_start : (c_at0.work fakeOutIdx).read = Γ.start := by
    rw [Tape.read, hhead_at0, hcells_at0, hcells_rw]; exact hcell0
  have hstep3 := step_rewindOut_start_cfg tm₁ tm₂ hst_at0 hread_start
  set c_cr : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inl UnionPhase.checkResult),
      input := c_at0.input.move (idleDir c_at0.input.read),
      work := fun i => ((c_at0.work i).write (Γw.blank : Γw).toΓ).move
        (if i.val = n₁ then Dir3.right else idleDir (c_at0.work i).read),
      output := (c_at0.output.write Γw.blank.toΓ).move (idleDir c_at0.output.read) }
    with hc_cr_def
  -- c_cr fake output head = 1 (moved right from head 0)
  have hcr_fo_head : (c_cr.work fakeOutIdx).head = 1 := by
    simp only [hc_cr_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
    simp only [Tape.write, hhead_at0, ↓reduceIte, Tape.move]
  -- c_cr fake output cells preserved (write blank at head 0 is no-op)
  have hcr_fo_cells : (c_cr.work fakeOutIdx).cells = (c_at0.work fakeOutIdx).cells := by
    simp only [hc_cr_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
    rw [Tape.move_cells]; simp only [Tape.write, if_pos hhead_at0]
  -- c_cr fake output reads cell 1 = Γ.one
  have hcr_read : (c_cr.work fakeOutIdx).read = Γ.one := by
    rw [Tape.read, hcr_fo_head, hcr_fo_cells, hcells_at0, hcells_rw]; exact haccept
  -- c_cr output = unionIdleTape
  have hout_cr : c_cr.output = unionIdleTape := by
    show (c_at0.output.write Γw.blank.toΓ).move (idleDir c_at0.output.read) = unionIdleTape
    rw [hout_at0]; exact idleTape_step_idle
  -- Step 4: checkResult with Γ.one → halt (1 step)
  have hst_cr : c_cr.state = Sum.inr (Sum.inl UnionPhase.checkResult) := rfl
  have hstep4 := step_checkResult_one_cfg tm₁ tm₂ hst_cr hcr_read
  set c_final : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inr tm₂.qhalt),
      input := c_cr.input.move (idleDir c_cr.input.read),
      work := fun i => ((c_cr.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c_cr.work i).read),
      output := (c_cr.output.write Γw.one.toΓ).move (idleDir c_cr.output.read) }
    with hc_final_def
  -- c_final is halted
  have hhalt_final : (unionTM tm₁ tm₂).halted c_final := rfl
  -- c_final output cell 1 = Γ.one
  have hcells_final : c_final.output.cells 1 = Γ.one := by
    show ((c_cr.output.write Γw.one.toΓ).move (idleDir c_cr.output.read)).cells 1 = Γ.one
    rw [Tape.move_cells, hout_cr]
    simp [Tape.write, unionIdleTape, Γw.toΓ, Function.update, Tape.init]
  -- Compose all steps: 1 + h_rw + 1 + 1 steps total
  have htotal : (unionTM tm₁ tm₂).reachesIn (1 + (h_rw + (1 + 1)))
      (unionPhase1Cfg tm₁ tm₂ c₁) c_final :=
    reachesIn_trans _ (.step hstep1 .zero)
      (reachesIn_trans _ hreach_rw
        (.step hstep3 (.step hstep4 .zero)))
  have heq : 1 + (h_rw + (1 + 1)) = 1 + h_rw + 1 + 1 := by omega
  exact ⟨1 + h_rw + 1 + 1, c_final, heq ▸ htotal, hhalt_final, hcells_final, by omega⟩

-- ════════════════════════════════════════════════════════════════════════
-- Transition phase: reject path (x ∉ L₁) → Phase 2 ready
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind the input tape from head position `h` to head position 0,
    preserving output = unionIdleTape. -/
private theorem rewind_input_loop (tm₁ : TM n₁) (tm₂ : TM n₂) :
    ∀ (h : ℕ) (c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
    c.state = Sum.inr (Sum.inl UnionPhase.rewindIn) →
    c.input.head = h →
    (∀ i, i ≥ 1 → c.input.cells i ≠ Γ.start) →
    c.input.cells 0 = Γ.start →
    c.output = unionIdleTape →
    ∃ c', (unionTM tm₁ tm₂).reachesIn h c c' ∧
      c'.state = Sum.inr (Sum.inl UnionPhase.rewindIn) ∧
      c'.input.head = 0 ∧
      c'.input.cells = c.input.cells ∧
      c'.output = unionIdleTape := by
  intro h
  induction h with
  | zero =>
    intro c hst hhead _ _ hout
    exact ⟨c, .zero, hst, hhead, rfl, hout⟩
  | succ n ih =>
    intro c hst hhead hnostart hcell0 hout
    have hread_ne : c.input.read ≠ Γ.start := by
      rw [Tape.read]; exact hnostart _ (by omega)
    have hstep := step_rewindIn_nostart_cfg tm₁ tm₂ hst hread_ne
    set c' : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
      { state := Sum.inr (Sum.inl UnionPhase.rewindIn),
        input := c.input.move Dir3.left,
        work := fun i => ((c.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c.work i).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) }
      with hc'_def
    have hst' : c'.state = Sum.inr (Sum.inl UnionPhase.rewindIn) := rfl
    have hhead' : c'.input.head = n := by
      show (c.input.move Dir3.left).head = n; simp [Tape.move, hhead]
    have hcells' : c'.input.cells = c.input.cells := Tape.move_cells _ _
    have hcell0' : c'.input.cells 0 = Γ.start := by rw [hcells']; exact hcell0
    have hnostart' : ∀ i, i ≥ 1 → c'.input.cells i ≠ Γ.start := by
      intro i hi; rw [hcells']; exact hnostart i hi
    have hout' : c'.output = unionIdleTape := by
      show (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) = unionIdleTape
      rw [hout]; exact idleTape_step_idle
    obtain ⟨c'', hreach, hst'', hhead'', hcells'', hout''⟩ :=
      ih c' hst' hhead' hnostart' hcell0' hout'
    exact ⟨c'', .step hstep hreach, hst'', hhead'', by rw [hcells'', hcells'], hout''⟩

/-- Writing blank to unionIdleTape and moving left yields Tape.init []. -/
private theorem idleTape_moveLeft :
    (unionIdleTape.write Γw.blank.toΓ).move (moveLeftDir unionIdleTape.read) = Tape.init [] := by
  simp [unionIdleTape, moveLeftDir, Tape.write, Tape.move, Tape.read, Tape.init]

/-- unionIdleTape stays unionIdleTape when written with blank and moved by idleDir (on any tape). -/
private theorem tape_idle_step (t : Tape) (ht : t = unionIdleTape) :
    (t.write Γw.blank.toΓ).move (idleDir t.read) = unionIdleTape := by
  rw [ht]; exact idleTape_step_idle

/-- Input cells are preserved through any reachesIn (input tape is read-only). -/
private theorem union_input_cells_of_step (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c c' : Cfg (n₁ + 1 + n₂) (unionTM tm₁ tm₂).Q}
    (hs : (unionTM tm₁ tm₂).step c = some c') : c'.input.cells = c.input.cells := by
  have hne := state_ne_qhalt_of_step hs
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hs; subst hs
  exact Tape.move_cells _ _

private theorem union_input_cells_of_reachesIn (tm₁ : TM n₁) (tm₂ : TM n₂)
    {t : ℕ} {c₀ c : Cfg (n₁ + 1 + n₂) (unionTM tm₁ tm₂).Q}
    (h : (unionTM tm₁ tm₂).reachesIn t c₀ c) : c.input.cells = c₀.input.cells := by
  induction h with
  | zero => rfl
  | step hs _ ih => rw [ih, union_input_cells_of_step tm₁ tm₂ hs]

/-- Work tapes at index `> n₁` get write blank + move idle in any step
    from `inl q`, `rewindOut`, `checkResult`, or `rewindIn` states. -/
private theorem phase2_work_step_idle (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c c' : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hs : (unionTM tm₁ tm₂).step c = some c')
    (hstate : (∃ q, c.state = Sum.inl q) ∨
              c.state = Sum.inr (Sum.inl UnionPhase.rewindOut) ∨
              c.state = Sum.inr (Sum.inl UnionPhase.checkResult) ∨
              c.state = Sum.inr (Sum.inl UnionPhase.rewindIn))
    {i : Fin (n₁ + 1 + n₂)} (hi : i.val > n₁) :
    c'.work i = ((c.work i).write Γw.blank.toΓ).move (idleDir (c.work i).read) := by
  have hne : c.state ≠ (unionTM tm₁ tm₂).qhalt := by
    rcases hstate with ⟨q, hq⟩ | hq | hq | hq <;> rw [hq] <;> exact fun h => nomatch h
  simp only [step] at hs
  split at hs
  · exact absurd ‹_› hne
  injection hs with hs; subst hs
  have hine : (i : ℕ) ≠ n₁ := by omega
  rcases hstate with ⟨q, hq⟩ | hq | hq | hq
  · dsimp only []; rw [hq]; dsimp only [unionTM]; split
    · -- qhalt: write (if i = n₁ then ... else blank), dir idleDir
      congr 1; simp only [hine, ↓reduceIte]
    · -- q ≠ qhalt: write/dir have dif/if structure
      congr 1
      · congr 1
        show (if h : (i : ℕ) < n₁ then _ else if (i : ℕ) = n₁ then _ else Γw.blank) = Γw.blank
        rw [dif_neg (show ¬((i : ℕ) < n₁) from by omega), if_neg hine]
      · show (if h : (i : ℕ) < n₁ then _
          else if (i : ℕ) = n₁ then _ else idleDir (c.work i).read) = _
        rw [dif_neg (show ¬((i : ℕ) < n₁) from by omega), if_neg hine]
  · rw [hq]; dsimp only [unionTM]; split
    · congr 1; simp only [hine, ↓reduceIte]
    · congr 1
      · congr 1; simp only [hine, ↓reduceIte]
      · simp only [hine, ↓reduceIte]
  · rw [hq]; dsimp only [unionTM]; split <;> rfl
  · rw [hq]; dsimp only [unionTM]; split <;> rfl

/-- Rewind input loop also preserves phase 2 work tapes. -/
private theorem rewind_input_work_idle (tm₁ : TM n₁) (tm₂ : TM n₂)
    {i : Fin (n₁ + 1 + n₂)} (_hi : i.val > n₁) :
    ∀ (h : ℕ) (c : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
    c.state = Sum.inr (Sum.inl UnionPhase.rewindIn) →
    c.input.head = h →
    (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
    c.input.cells 0 = Γ.start →
    c.work i = unionIdleTape →
    ∃ c', (unionTM tm₁ tm₂).reachesIn h c c' ∧
      c'.work i = unionIdleTape := by
  intro h
  induction h with
  | zero =>
    intro c _ _ _ _ hidle; exact ⟨c, .zero, hidle⟩
  | succ n ih =>
    intro c hst hhead hnostart hcell0 hidle
    have hread_ne : c.input.read ≠ Γ.start := by
      rw [Tape.read]; exact hnostart _ (by omega)
    have hstep := step_rewindIn_nostart_cfg tm₁ tm₂ hst hread_ne
    set c' : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
      { state := Sum.inr (Sum.inl UnionPhase.rewindIn),
        input := c.input.move Dir3.left,
        work := fun j => ((c.work j).write (Γw.blank : Γw).toΓ).move (idleDir (c.work j).read),
        output := (c.output.write Γw.blank.toΓ).move (idleDir c.output.read) }
      with hc'_def
    have hidle' : c'.work i = unionIdleTape := by
      show ((c.work i).write _).move _ = _; rw [hidle]; exact idleTape_step_idle
    obtain ⟨c'', hreach, hidle''⟩ := ih c' rfl
      (by show (c.input.move Dir3.left).head = n; simp [Tape.move, hhead])
      (by intro j hj; show (c.input.move Dir3.left).cells j ≠ _
          rw [Tape.move_cells]; exact hnostart j hj)
      (by show (c.input.move Dir3.left).cells 0 = _; rw [Tape.move_cells]; exact hcell0)
      hidle'
    exact ⟨c'', .step hstep hreach, hidle''⟩

/-- After Phase 1, if tm₁ rejected, the union machine transitions to a
    config ready for Phase 2: state is `Sum.inr (Sum.inr tm₂.qstart)`,
    input/output/active work tapes match `tm₂.initCfg x`. -/
theorem unionTM_transition_reject (tm₁ : TM n₁) (tm₂ : TM n₂) (x : List Bool)
    {c₁ : Cfg n₁ tm₁.Q}
    (hhalt : tm₁.halted c₁)
    (hreject : c₁.output.cells 1 = Γ.zero)
    (hcell0_out : c₁.output.cells 0 = Γ.start)
    (hnostart_out : ∀ i, i ≥ 1 → c₁.output.cells i ≠ Γ.start)
    (hinput_cells : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells) :
    ∃ (t_tr : ℕ) (c_mid : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)),
      (unionTM tm₁ tm₂).reachesIn t_tr (unionPhase1Cfg tm₁ tm₂ c₁) c_mid ∧
      c_mid.state = Sum.inr (Sum.inr tm₂.qstart) ∧
      c_mid.input = Tape.init (x.map Γ.ofBool) ∧
      (∀ j : Fin n₂, c_mid.work ⟨n₁ + 1 + j.val, by omega⟩ = Tape.init []) ∧
      c_mid.output = Tape.init [] ∧
      t_tr ≤ c₁.output.head + c₁.input.head + 7 := by
  -- Step 1: unionPhase1Cfg halted → rewindOut (1 step)
  obtain ⟨c_rw, hstep1, hst_rw, hcells_rw, hout_rw⟩ :=
    step_phase1_halted tm₁ tm₂ c₁ hhalt hnostart_out
  -- Head bounds
  have hfo_head_bound : (c_rw.work fakeOutIdx).head ≤ c₁.output.head + 1 := by
    have hstate : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
      show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
    have hexp := (step_inl_qhalt_cfg tm₁ tm₂ hstate).symm.trans hstep1
    rw [Option.some.injEq] at hexp
    rw [← hexp]
    simp only [phase1Cfg_fakeOut]
    have hmv : ∀ (t : Tape) (d : Dir3), (t.move d).head ≤ t.head + 1 := by
      intro t d; cases d <;> simp [Tape.move]; omega
    have hwh : ∀ (t : Tape) (s : Γ), (t.write s).head = t.head := by
      intro t s; simp [Tape.write]; split <;> rfl
    calc ((c₁.output.write _).move _).head ≤ (c₁.output.write _).head + 1 := hmv _ _
      _ = c₁.output.head + 1 := by rw [hwh]
  -- c_rw properties
  have hcell0_rw : (c_rw.work fakeOutIdx).cells 0 = Γ.start := by rw [hcells_rw]; exact hcell0_out
  have hnostart_rw : ∀ i, i ≥ 1 → (c_rw.work fakeOutIdx).cells i ≠ Γ.start := by
    intro i hi; rw [hcells_rw]; exact hnostart_out i hi
  have hout_rw_eq : c_rw.output = unionIdleTape := by rw [hout_rw]; exact idleTape_step_idle
  -- Step 2: Rewind fake output (h_rw steps)
  set h_rw := (c_rw.work fakeOutIdx).head with hh_rw_def
  obtain ⟨c_at0, hreach_rw, hst_at0, hhead_at0, hcells_at0, hout_at0, hinp_at0, hwork_at0⟩ :=
    rewind_fakeOut_loop tm₁ tm₂ h_rw c_rw hst_rw hout_rw_eq rfl hcell0_rw hnostart_rw
  -- Step 3: rewindOut at head 0 → checkResult (1 step)
  have hread_start : (c_at0.work fakeOutIdx).read = Γ.start := by
    rw [Tape.read, hhead_at0, hcells_at0, hcells_rw]; exact hcell0_out
  have hstep3 := step_rewindOut_start_cfg tm₁ tm₂ hst_at0 hread_start
  set c_cr : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inl UnionPhase.checkResult),
      input := c_at0.input.move (idleDir c_at0.input.read),
      work := fun i => ((c_at0.work i).write (Γw.blank : Γw).toΓ).move
        (if i.val = n₁ then Dir3.right else idleDir (c_at0.work i).read),
      output := (c_at0.output.write Γw.blank.toΓ).move (idleDir c_at0.output.read) }
    with hc_cr_def
  have hout_cr : c_cr.output = unionIdleTape := by
    show (c_at0.output.write Γw.blank.toΓ).move (idleDir c_at0.output.read) = unionIdleTape
    rw [hout_at0]; exact idleTape_step_idle
  -- c_cr fake output reads Γ.zero (not Γ.one)
  have hcr_fo_head : (c_cr.work fakeOutIdx).head = 1 := by
    simp only [hc_cr_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
    simp only [Tape.write, hhead_at0, ↓reduceIte, Tape.move]
  have hcr_fo_cells : (c_cr.work fakeOutIdx).cells = (c_at0.work fakeOutIdx).cells := by
    simp only [hc_cr_def, show (fakeOutIdx : Fin (n₁ + 1 + n₂)).val = n₁ from rfl, ite_true]
    rw [Tape.move_cells]; simp only [Tape.write, if_pos hhead_at0]
  have hcr_read_ne_one : (c_cr.work fakeOutIdx).read ≠ Γ.one := by
    rw [Tape.read, hcr_fo_head, hcr_fo_cells, hcells_at0, hcells_rw, hreject]; decide
  -- Step 4: checkResult ≠ Γ.one → rewindIn (1 step)
  have hstep4 := step_checkResult_notone_cfg tm₁ tm₂ rfl hcr_read_ne_one
  set c_ri : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inl UnionPhase.rewindIn),
      input := c_cr.input.move (idleDir c_cr.input.read),
      work := fun i => ((c_cr.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c_cr.work i).read),
      output := (c_cr.output.write Γw.blank.toΓ).move (idleDir c_cr.output.read) }
    with hc_ri_def
  have hout_ri : c_ri.output = unionIdleTape := by
    show (c_cr.output.write Γw.blank.toΓ).move (idleDir c_cr.output.read) = unionIdleTape
    rw [hout_cr]; exact idleTape_step_idle
  -- Input cells chain: input is read-only, so cells are preserved through all steps.
  -- unionPhase1Cfg → c_rw → (rewind) → c_at0 → c_cr → c_ri all preserve input.cells
  have hin_cells_chain : c_ri.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    -- c_ri.input.cells = c_cr.input.cells (move)
    show (c_cr.input.move _).cells = _; rw [Tape.move_cells]
    -- c_cr.input.cells = c_at0.input.cells (move)
    show (c_at0.input.move _).cells = _; rw [Tape.move_cells]
    -- c_at0.input.cells = c_rw.input.cells (reachesIn)
    rw [union_input_cells_of_reachesIn tm₁ tm₂ hreach_rw]
    -- c_rw.input.cells = unionPhase1Cfg.input.cells (step)
    have hstate : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
      show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
    have hexp := (step_inl_qhalt_cfg tm₁ tm₂ hstate).symm.trans hstep1
    rw [Option.some.injEq] at hexp
    rw [← hexp, Tape.move_cells]; exact hinput_cells
  -- Input cells ≥ 1 ≠ Γ.start
  have hin_nostart_ri : ∀ i, i ≥ 1 → c_ri.input.cells i ≠ Γ.start := by
    intro i hi; rw [hin_cells_chain]
    simp only [Tape.init, show i ≠ 0 from by omega, ↓reduceIte]
    intro heq
    have : (x.map Γ.ofBool)[i - 1]?.getD Γ.blank = Γ.start := heq
    cases hget : (x.map Γ.ofBool)[i - 1]? with
    | none => simp [hget, Option.getD] at this
    | some v =>
      simp [hget, Option.getD] at this; subst this
      have hmem := List.mem_of_getElem? hget
      simp [List.mem_map] at hmem
      rcases hmem with ⟨_, hb⟩ | ⟨_, hb⟩ <;> simp [Γ.ofBool] at hb
  -- Input cell 0 = Γ.start
  have hin_cell0_ri : c_ri.input.cells 0 = Γ.start := by
    rw [hin_cells_chain]; simp [Tape.init]
  -- Input head bound for c_ri
  -- c_ri.input goes through: unionPhase1Cfg.input → move → (h_rw moves) → move → move → move
  -- Each move adds at most 1, so total head ≤ initial + (1 + h_rw + 1 + 1 + 1)
  -- But we need a tighter bound. Let's compute it through the reachesIn chain.
  -- Actually, we just need c_ri.input.head for the rewind loop bound.
  -- Let's compose: steps 1..4 give reachesIn (1 + h_rw + 1 + 1) from unionPhase1Cfg to c_ri
  have hreach_to_ri : (unionTM tm₁ tm₂).reachesIn (1 + (h_rw + (1 + 1)))
      (unionPhase1Cfg tm₁ tm₂ c₁) c_ri :=
    reachesIn_trans _ (.step hstep1 .zero)
      (reachesIn_trans _ hreach_rw (.step hstep3 (.step hstep4 .zero)))
  -- Input head bound: through all steps, head changes by at most 1 per step
  -- total steps so far = 1 + h_rw + 2, so head ≤ initial + (1 + h_rw + 2)
  -- unionPhase1Cfg.input.head = c₁.input.head
  -- But we need a precise bound. Let's just track c_ri.input.head.
  -- Actually for rewind_input_loop we need h_ri = c_ri.input.head and the
  -- total t_tr ≤ c₁.output.head + c₁.input.head + 7
  -- We don't need a tight head bound; we just use the loop count.
  -- Step 5: Rewind input (h_ri steps)
  set h_ri := c_ri.input.head with hh_ri_def
  obtain ⟨c_ri0, hreach_ri, hst_ri0, hhead_ri0, hcells_ri0, hout_ri0⟩ :=
    rewind_input_loop tm₁ tm₂ h_ri c_ri rfl rfl hin_nostart_ri hin_cell0_ri hout_ri
  -- Step 6: rewindIn at head 0 → setup2 (1 step)
  have hread_start_ri : c_ri0.input.read = Γ.start := by
    rw [Tape.read, hhead_ri0, hcells_ri0, hin_cells_chain]; simp [Tape.init]
  have hstep6 := step_rewindIn_start_cfg tm₁ tm₂ hst_ri0 hread_start_ri
  set c_s2 : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inl UnionPhase.setup2),
      input := c_ri0.input.move Dir3.right,
      work := fun i =>
        ((c_ri0.work i).write (Γw.blank : Γw).toΓ).move (idleDir (c_ri0.work i).read),
      output := (c_ri0.output.write Γw.blank.toΓ).move (idleDir c_ri0.output.read) }
    with hc_s2_def
  -- Step 7: setup2 → Phase 2 start (1 step)
  have hstep7 := step_setup2_cfg tm₁ tm₂
    (show c_s2.state = Sum.inr (Sum.inl UnionPhase.setup2) from rfl)
  set c_mid : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q) :=
    { state := Sum.inr (Sum.inr tm₂.qstart),
      input := c_s2.input.move (moveLeftDir c_s2.input.read),
      work := fun i => ((c_s2.work i).write (Γw.blank : Γw).toΓ).move
        (if i.val ≤ n₁ then idleDir (c_s2.work i).read else moveLeftDir (c_s2.work i).read),
      output := (c_s2.output.write Γw.blank.toΓ).move (moveLeftDir c_s2.output.read) }
    with hc_mid_def
  -- Now prove all properties of c_mid.
  -- c_mid.state
  have hst_mid : c_mid.state = Sum.inr (Sum.inr tm₂.qstart) := rfl
  -- c_mid.input = Tape.init (x.map Γ.ofBool)
  -- c_mid.input = c_s2.input.move (moveLeftDir c_s2.input.read)
  -- c_s2.input = c_ri0.input.move Dir3.right
  -- c_ri0.input.head = 0, so moving right gives head = 1
  -- c_s2.input.head = 1, c_s2.input.cells = c_ri0.input.cells (move preserves)
  -- c_s2.input.read = cells[1] which is from Tape.init, not start
  -- moveLeftDir(non-start) = left, so head goes from 1 to 0
  -- c_mid.input = { head := 0, cells := Tape.init cells } = Tape.init (x.map Γ.ofBool)
  have hcells_ri0_eq : c_ri0.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    rw [hcells_ri0, hin_cells_chain]
  have hin_mid : c_mid.input = Tape.init (x.map Γ.ofBool) := by
    -- c_mid.input.cells = Tape.init cells
    have h2 : c_mid.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
      show (c_s2.input.move _).cells = _
      rw [Tape.move_cells]; show (c_ri0.input.move Dir3.right).cells = _
      rw [Tape.move_cells]; exact hcells_ri0_eq
    -- c_s2.input = c_ri0.input.move Dir3.right, head = 1
    have hs2_head : c_s2.input.head = 1 := by
      show (c_ri0.input.move Dir3.right).head = 1
      simp [Tape.move, hhead_ri0]
    have hs2_cells : c_s2.input.cells = c_ri0.input.cells := Tape.move_cells _ _
    -- c_s2.input.read ≠ Γ.start (cells[1] is from Tape.init, not start)
    have hs2_read_ne : c_s2.input.read ≠ Γ.start := by
      rw [Tape.read, hs2_head, hs2_cells, hcells_ri0]
      exact hin_nostart_ri 1 (by omega)
    -- c_mid.input.head = 0 (moveLeftDir of non-start = left, from head 1 → 0)
    have h1 : c_mid.input.head = 0 := by
      show (c_s2.input.move (moveLeftDir c_s2.input.read)).head = 0
      rw [moveLeftDir, if_neg hs2_read_ne]; simp [Tape.move, hs2_head]
    -- Combine
    have hcfg : ∀ (a b : Tape), a.head = b.head → a.cells = b.cells → a = b := by
      intros a b hh hc; cases a; cases b; simp only [Tape.mk.injEq] at *; exact ⟨hh, hc⟩
    exact hcfg _ _ (by rw [h1]; rfl) h2
  -- c_mid.output = Tape.init []
  -- c_mid.output = (c_s2.output.write blank).move (moveLeftDir c_s2.output.read)
  -- c_s2.output = (c_ri0.output.write blank).move (idleDir c_ri0.output.read)
  -- c_ri0.output = unionIdleTape
  -- c_s2.output = unionIdleTape (write blank + move idle on unionIdleTape)
  -- c_mid.output = (unionIdleTape.write blank).move (moveLeftDir unionIdleTape.read) = Tape.init []
  have hout_s2 : c_s2.output = unionIdleTape := by
    show (c_ri0.output.write Γw.blank.toΓ).move (idleDir c_ri0.output.read) = unionIdleTape
    rw [hout_ri0]; exact idleTape_step_idle
  have hout_mid : c_mid.output = Tape.init [] := by
    show (c_s2.output.write Γw.blank.toΓ).move (moveLeftDir c_s2.output.read) = Tape.init []
    rw [hout_s2]; exact idleTape_moveLeft
  -- Phase 2 work tapes = Tape.init []
  -- Strategy: show work tapes at > n₁ indices stay unionIdleTape through each phase,
  -- then setup2 sends unionIdleTape to Tape.init [].
  -- Step 1: c_rw.work at > n₁ = unionIdleTape (from phase1_halted step)
  have hwork_rw_idle : ∀ (j : Fin n₂),
      c_rw.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j
    have hstateq : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
      show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
    have hstep' := phase2_work_step_idle tm₁ tm₂ hstep1
      (Or.inl ⟨tm₁.qhalt, hstateq⟩) (i := ⟨n₁ + 1 + j.val, by omega⟩)
      (by omega : n₁ + 1 + j.val > n₁)
    rw [hstep']
    have hp1 : (unionPhase1Cfg tm₁ tm₂ c₁).work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
      simp [unionPhase1Cfg, show ¬(n₁ + 1 + j.val < n₁) from by omega,
            show ¬(n₁ + 1 + j.val = n₁) from by omega]
    rw [hp1]; exact idleTape_step_idle
  -- Step 2: Through rewind_fakeOut (hreach_rw), work tapes > n₁ stay unionIdleTape
  have hwork_at0_idle : ∀ (j : Fin n₂),
      c_at0.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j; exact hwork_at0 ⟨n₁ + 1 + j.val, by omega⟩
      (show n₁ + 1 + j.val > n₁ by omega) (hwork_rw_idle j)
  -- Step 3 (rewindOut→checkResult): c_cr.work at > n₁ = unionIdleTape
  have hwork_cr_idle : ∀ (j : Fin n₂),
      c_cr.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j
    show ((c_at0.work ⟨n₁ + 1 + j.val, by omega⟩).write _).move
      (if (n₁ + 1 + j.val) = n₁ then _ else _) = _
    rw [if_neg (show n₁ + 1 + j.val ≠ n₁ from by omega), hwork_at0_idle j]
    exact idleTape_step_idle
  -- Step 4 (checkResult→rewindIn): c_ri.work at > n₁ = unionIdleTape
  have hwork_ri_idle : ∀ (j : Fin n₂),
      c_ri.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j
    show ((c_cr.work ⟨n₁ + 1 + j.val, by omega⟩).write _).move _ = _
    rw [hwork_cr_idle j]; exact idleTape_step_idle
  -- Step 5: Through rewind_input (hreach_ri), work tapes > n₁ stay unionIdleTape
  have hwork_ri0_idle : ∀ (j : Fin n₂),
      c_ri0.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j
    obtain ⟨c_ri0', hreach', hidle'⟩ := rewind_input_work_idle tm₁ tm₂
      (show n₁ + 1 + j.val > n₁ from by omega)
      h_ri c_ri rfl rfl hin_nostart_ri hin_cell0_ri (hwork_ri_idle j)
    have hdet := TM.reachesIn_right_unique hreach_ri hreach'
    rw [hdet]; exact hidle'
  -- Step 6 (rewindIn→setup2): c_s2.work at > n₁ = unionIdleTape
  have hwork_s2_idle : ∀ (j : Fin n₂),
      c_s2.work ⟨n₁ + 1 + j.val, by omega⟩ = unionIdleTape := by
    intro j
    show ((c_ri0.work ⟨n₁ + 1 + j.val, by omega⟩).write _).move _ = _
    rw [hwork_ri0_idle j]; exact idleTape_step_idle
  -- Step 7 (setup2→phase2_start): c_mid.work at > n₁ = Tape.init []
  have hwork_mid : ∀ (j : Fin n₂),
      c_mid.work ⟨n₁ + 1 + j.val, by omega⟩ = Tape.init [] := by
    intro j
    show ((c_s2.work ⟨n₁ + 1 + j.val, by omega⟩).write _).move
      (if (n₁ + 1 + j.val) ≤ n₁ then _ else _) = _
    rw [if_neg (show ¬(n₁ + 1 + j.val ≤ n₁) from by omega), hwork_s2_idle j]
    exact idleTape_moveLeft
  -- Compose all reachesIn steps
  have hreach_total : (unionTM tm₁ tm₂).reachesIn
      (1 + (h_rw + (1 + 1)) + (h_ri + (1 + 1)))
      (unionPhase1Cfg tm₁ tm₂ c₁) c_mid :=
    reachesIn_trans _ hreach_to_ri
      (reachesIn_trans _ hreach_ri (.step hstep6 (.step hstep7 .zero)))
  -- Time bound
  -- h_rw ≤ c₁.output.head + 1 (hfo_head_bound)
  -- h_ri = c_ri.input.head ≤ c₁.input.head + 1 (input moves by idleDir, which is stay for head ≥ 1)
  -- Need: 1 + (h_rw + 2) + (h_ri + 2) = h_rw + h_ri + 5 ≤ c₁.output.head + c₁.input.head + 7
  -- Suffices: h_rw + h_ri ≤ c₁.output.head + c₁.input.head + 2, which holds.
  -- Prove h_ri ≤ c₁.input.head + 1:
  have hri_bound : h_ri ≤ c₁.input.head + 1 := by
    -- c_rw.input.cells = c₁.input.cells (input cells preserved through step)
    have hcrw_cells : c_rw.input.cells = c₁.input.cells := by
      have := union_input_cells_of_step tm₁ tm₂ hstep1
      rw [this]; rfl
    -- c_rw.input cells[≥1] ≠ Γ.start
    have hcrw_ino : ∀ i, i ≥ 1 → c_rw.input.cells i ≠ Γ.start := by
      intro i hi; rw [hcrw_cells, hinput_cells]
      simp only [Tape.init, show i ≠ 0 from by omega, ↓reduceIte]
      intro heq
      cases hget : (x.map Γ.ofBool)[i - 1]? with
      | none => simp [hget, Option.getD] at heq
      | some v =>
        simp [hget, Option.getD] at heq; subst heq
        have hmem := List.mem_of_getElem? hget
        simp [List.mem_map] at hmem; rcases hmem with ⟨_, hb⟩ | ⟨_, hb⟩ <;> simp [Γ.ofBool] at hb
    -- c_rw.input.head ≤ c₁.input.head + 1
    -- From step_inl_qhalt_cfg, the input direction is idleDir(input.read)
    -- Use step_inl_qhalt_cfg to get the exact form of c_rw.input
    have hstateq : (unionPhase1Cfg tm₁ tm₂ c₁).state = Sum.inl tm₁.qhalt := by
      show Sum.inl c₁.state = Sum.inl tm₁.qhalt; rw [hhalt]
    have hstep_eq := step_inl_qhalt_cfg tm₁ tm₂ hstateq
    -- c_rw.input = c₁.input.move (idleDir c₁.input.read) since unionPhase1Cfg.input = c₁.input
    have hcrw_input_eq : c_rw.input = c₁.input.move (idleDir c₁.input.read) := by
      have heq : some c_rw = some _ := hstep1.symm.trans hstep_eq
      simp only [Option.some.injEq] at heq
      rw [heq]; rfl
    -- c_rw.input.head ≤ c₁.input.head + 1
    have hcrw_head : c_rw.input.head ≤ c₁.input.head + 1 := by
      rw [hcrw_input_eq]; cases (idleDir c₁.input.read) <;> simp [Tape.move]; omega
    -- c_rw.input.head ≥ 1
    have hcrw_hge : c_rw.input.head ≥ 1 := by
      rw [hcrw_input_eq]
      by_cases hh : c₁.input.head = 0
      · have hread0 : c₁.input.read = Γ.start := by
          rw [Tape.read, hh, hinput_cells]; simp [Tape.init]
        rw [hread0, idleDir, if_pos rfl]; simp [Tape.move, hh]
      · have hge : c₁.input.head ≥ 1 := by omega
        have hc1_ino : ∀ i, i ≥ 1 → c₁.input.cells i ≠ Γ.start := by
          intro i hi; rw [← hcrw_cells]; exact hcrw_ino i hi
        rw [idleDir_stay_of_ge_one _ hge hc1_ino]; simp [Tape.move]; omega
    -- Through rewind_fakeOut loop: input head preserved
    have hat0_head : c_at0.input.head = c_rw.input.head :=
      hinp_at0 hcrw_hge hcrw_ino
    -- c_at0.input.cells[≥1] ≠ start (preserved through reachesIn)
    have hat0_ino : ∀ i, i ≥ 1 → c_at0.input.cells i ≠ Γ.start := by
      intro i hi; rw [union_input_cells_of_reachesIn tm₁ tm₂ hreach_rw]; exact hcrw_ino i hi
    -- c_cr.input.head = c_at0.input.head (idleDir step from head ≥ 1)
    have hcr_head : c_cr.input.head = c_at0.input.head := by
      show (c_at0.input.move (idleDir c_at0.input.read)).head = _
      exact idle_move_preserves_head _ (by omega) hat0_ino
    -- c_ri.input.head = c_cr.input.head (idleDir step from head ≥ 1)
    have hcr_ino : ∀ i, i ≥ 1 → c_cr.input.cells i ≠ Γ.start := by
      intro i hi; show (c_at0.input.move _).cells i ≠ _; rw [Tape.move_cells]; exact hat0_ino i hi
    have hri_head : c_ri.input.head = c_cr.input.head := by
      show (c_cr.input.move (idleDir c_cr.input.read)).head = _
      exact idle_move_preserves_head _ (by omega) hcr_ino
    -- Chain: h_ri = c_ri.input.head = c_rw.input.head ≤ c₁.input.head + 1
    omega
  have htime : 1 + (h_rw + (1 + 1)) + (h_ri + (1 + 1)) ≤ c₁.output.head + c₁.input.head + 7 := by
    omega
  refine ⟨1 + (h_rw + (1 + 1)) + (h_ri + (1 + 1)), c_mid, ?_, hst_mid, hin_mid, hwork_mid,
    hout_mid, htime⟩
  exact hreach_total

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: one-step correspondence
-- ════════════════════════════════════════════════════════════════════════

/-- Phase 2 compatibility: a union machine config agrees with a tm₂ config
    on the active components (state, input, Phase 2 work tapes, output). -/
structure UnionPhase2Compat (tm₁ : TM n₁) (tm₂ : TM n₂)
    (c_u : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q))
    (c₂ : Cfg n₂ tm₂.Q) : Prop where
  state_eq : c_u.state = Sum.inr (Sum.inr c₂.state)
  input_eq : c_u.input = c₂.input
  work_eq : ∀ j : Fin n₂, c_u.work ⟨n₁ + 1 + j.val, by omega⟩ = c₂.work j
  output_eq : c_u.output = c₂.output

/-- One step of the union machine on a Phase 2 compatible config preserves
    compatibility. -/
private theorem phase2_step_corr (tm₁ : TM n₁) (tm₂ : TM n₂)
    {c₂ c₂' : Cfg n₂ tm₂.Q} (hstep : tm₂.step c₂ = some c₂')
    {c_u : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hcompat : UnionPhase2Compat tm₁ tm₂ c_u c₂) :
    ∃ c_u', (unionTM tm₁ tm₂).step c_u = some c_u' ∧
      UnionPhase2Compat tm₁ tm₂ c_u' c₂' := by
  have hne := state_ne_qhalt_of_step hstep
  -- Extract c₂' from tm₂.step
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep; subst hstep
  -- c_u is not halted in the union machine
  have hne_u : c_u.state ≠ (unionTM tm₁ tm₂).qhalt := by
    rw [hcompat.state_eq, unionTM_qhalt]; exact fun h => hne (Sum.inr.inj (Sum.inr.inj h))
  -- Unfold the union step; `split` reduces the halting ite (the stored
  -- decidability instance blocks `simp`/`rw [if_neg]` here), then pin the
  -- explicit step-result config as the existential witness via `rfl`.
  simp only [step]
  split
  · exact absurd ‹_› hne_u
  refine ⟨_, rfl, ?_⟩
  -- Rewrite reads using UnionPhase2Compat
  have hwork_reads : phase2WorkReads (fun i => (c_u.work i).read) =
      fun j => (c₂.work j).read := by
    ext ⟨j, hj⟩; simp only [phase2WorkReads]; exact congrArg Tape.read (hcompat.work_eq ⟨j, hj⟩)
  -- Construct UnionPhase2Compat (state_eq, input_eq, output_eq all close;
  -- work_eq needs dif reduction)
  refine ⟨?_, ?_, fun ⟨j, hj⟩ => ?_, ?_⟩ <;> dsimp only [] <;> rw [hcompat.state_eq] <;>
    simp only [unionTM_delta_inr_inr tm₁ tm₂ hne, hcompat.input_eq, hcompat.output_eq, hwork_reads]
  have hgt : ¬((n₁ + 1 + j) ≤ n₁) := by omega
  rw [dif_neg hgt]
  have hfin : ∀ (p : n₁ + 1 + j - (n₁ + 1) < n₂),
      (⟨n₁ + 1 + j - (n₁ + 1), p⟩ : Fin n₂) = ⟨j, hj⟩ := by
    intro p; apply Fin.ext; show n₁ + 1 + j - (n₁ + 1) = j; omega
  simp only [hfin, hcompat.work_eq ⟨j, hj⟩, dif_neg hgt]

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2 simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Multi-step Phase 2 simulation via step correspondence. -/
private theorem phase2_steps (tm₁ : TM n₁) (tm₂ : TM n₂)
    {t : ℕ} {c₂_start c₂_end : Cfg n₂ tm₂.Q}
    (hreach : tm₂.reachesIn t c₂_start c₂_end)
    {c_start : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hcompat : UnionPhase2Compat tm₁ tm₂ c_start c₂_start) :
    ∃ c_end, (unionTM tm₁ tm₂).reachesIn t c_start c_end ∧
      UnionPhase2Compat tm₁ tm₂ c_end c₂_end := by
  induction hreach generalizing c_start with
  | zero => exact ⟨c_start, .zero, hcompat⟩
  | step hstep _ ih =>
    obtain ⟨c_mid, hstep_u, hcompat_mid⟩ := phase2_step_corr tm₁ tm₂ hstep hcompat
    obtain ⟨c_end, hreach_u, hcompat_end⟩ := ih hcompat_mid
    exact ⟨c_end, .step hstep_u hreach_u, hcompat_end⟩

/-- **Phase 2 simulation**: if `tm₂` reaches `c₂` from `initCfg x` in
    `t₂` steps, and the starting union config is compatible with `initCfg x`,
    then the union machine reaches a config compatible with `c₂` in `t₂` steps. -/
theorem unionTM_phase2_simulation (tm₁ : TM n₁) (tm₂ : TM n₂) (x : List Bool)
    {t₂ : ℕ} {c₂ : Cfg n₂ tm₂.Q}
    (hreach : tm₂.reachesIn t₂ (tm₂.initCfg x) c₂)
    {c_start : Cfg (n₁ + 1 + n₂) (UnionQ tm₁.Q tm₂.Q)}
    (hss : c_start.state = Sum.inr (Sum.inr tm₂.qstart))
    (hsi : c_start.input = Tape.init (x.map Γ.ofBool))
    (hsw : ∀ j : Fin n₂, c_start.work ⟨n₁ + 1 + j.val, by omega⟩ = Tape.init [])
    (hso : c_start.output = Tape.init []) :
    ∃ c_end, (unionTM tm₁ tm₂).reachesIn t₂ c_start c_end ∧
      c_end.state = Sum.inr (Sum.inr c₂.state) ∧
      c_end.output = c₂.output := by
  have hcompat : UnionPhase2Compat tm₁ tm₂ c_start (tm₂.initCfg x) :=
    ⟨by rw [hss], hsi, hsw, hso⟩
  obtain ⟨c_end, hreach_u, hcompat_end⟩ := phase2_steps tm₁ tm₂ hreach hcompat
  exact ⟨c_end, hreach_u, hcompat_end.state_eq, hcompat_end.output_eq⟩

-- ════════════════════════════════════════════════════════════════════════

end TM

end Complexity
