/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Counter
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# retargetInput simulation — proof internals

This file contains the simulation lemmas for `retargetInput M`, showing
that `retargetInput M` on a configuration where work tape `k` holds the
"virtual input" `z` faithfully simulates `M` on input `z`.

## Key definitions and lemmas

- `retargetWrap` — embed a config of `M : TM k` into a config of
  `retargetInput M : TM (k+1)`, given a choice of real-input tape.
- `retargetInput_step_commute` — one step of `M` corresponds to one step
  of `retargetInput M` under the wrap (assuming a structural invariant on
  `c.input`: cells ≥ 1 are never `Γ.start`).
- `retargetInput_reachesIn_of_reachesIn` — multi-step simulation lifting.
- `retargetInput_reachesIn_halted_of_decidesInTime` — user-facing: if `M` decides `L` in
  time `T`, then `retargetInput M` started with `z` on work tape `k`
  reaches a halting configuration within `T(|z|)` steps with the correct
  output.

## The `startedCfg` family

For phase-composed machines, the interesting entry point is not `initCfg`
but the configuration reached after `M`'s forced first move off the `▷`
cells. `startedCfg M z hne` names that configuration (well-defined once
`qstart ≠ qhalt`, which `qstart_ne_qhalt_of_decidesInTime` guarantees for
any deciding machine), and the `startedCfg_*` lemmas pin down each field:
state, work, and output are input-independent, while every tape sits one
cell right of `▷`. `retargetInput_decidesVirtual_started` restates the
user-facing simulation from this post-start configuration.

## Hoare liftings

- `retargetInput_hoareTime` — a `HoareTime` triple for `M` lifts to a
  triple for `retargetInput M` in which the precondition reads `M`'s input
  off work tape `k` and the postcondition existentially recovers `M`'s
  final tapes.
- `retargetInput_copyInputToWorkTM_started_hoareTime`,
  `retargetInput_inputLengthPlusOneCounterTM_started_hoareTime`,
  `retargetInput_inputLengthPlusOneCounterTM_started_tracksInput_hoareTime`
  — virtual-input instantiations of the corresponding subroutine triples.

## The structural invariant

Because `retargetInput M` writes back the read symbol on work tape `k`
(to preserve cells), the simulation only goes through cleanly when the
current write is a no-op. This requires:

  head = 0  OR  read ≠ Γ.start

The second disjunct is equivalent to "cells at positions ≥ 1 never
contain `Γ.start`". This is a *structural* invariant of any DTM run
(since `δ` writes only `Γw`, which excludes `Γ.start`, and writes at
cell 0 are no-ops) — captured by `Tape.StartInvariant` below and preserved
across `TM.step` by `Tape.StartInvariant.step`.
-/


@[expose] public section

namespace Complexity

variable {k : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Config wrapping
-- ════════════════════════════════════════════════════════════════════════

/-- Embed a `Cfg k M.Q` into `Cfg (k+1) (retargetInput M).Q` by:
    - putting `realInput` on the real input tape (ignored by the machine),
    - putting `c.work i` on work tape `i` for `i < k`,
    - putting `c.input` on work tape `k` (the virtual input).
    State and output are shared. -/
def retargetWrap (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    Cfg (k + 1) (retargetInput M).Q where
  state := c.state
  input := realInput
  work := fun i =>
    if h : i.val < k then c.work ⟨i.val, h⟩
    else c.input
  output := c.output

/-- The state of a wrapped configuration is the state of the wrapped `M`-configuration. -/
@[simp] theorem retargetWrap_state (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).state = c.state := rfl

/-- The output tape of a wrapped configuration is the output tape of the
    wrapped `M`-configuration. -/
@[simp] theorem retargetWrap_output (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).output = c.output := rfl

/-- The (ignored) real input tape of a wrapped configuration is exactly the
    supplied `realInput`. -/
@[simp] theorem retargetWrap_input (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).input = realInput := rfl

/-- For an index `i < k`, work tape `i` of a wrapped configuration is work
    tape `i` of the wrapped `M`-configuration. -/
theorem retargetWrap_work_lt (M : TM k) (realInput : Tape) (c : Cfg k M.Q)
    (i : Fin (k + 1)) (h : i.val < k) :
    (retargetWrap M realInput c).work i = c.work ⟨i.val, h⟩ := by
  simp [retargetWrap, h]

/-- The last work tape (index `k`) of a wrapped configuration holds the
    wrapped `M`-configuration's input tape — the virtual input. -/
theorem retargetWrap_work_last (M : TM k) (realInput : Tape) (c : Cfg k M.Q) :
    (retargetWrap M realInput c).work ⟨k, by omega⟩ = c.input := by
  simp [retargetWrap]

-- ════════════════════════════════════════════════════════════════════════
-- Core step commute
-- ════════════════════════════════════════════════════════════════════════

/-- Auxiliary: `writeAndMove` with `readBackWrite` of the current read
    symbol equals `move` when the tape has either head = 0 or read ≠ start. -/
private theorem tape_writeBack_eq_move (t : Tape) (d : Dir3)
    (h : t.head = 0 ∨ t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ d = t.move d := by
  show (t.write (readBackWrite t.read).toΓ).move d = t.move d
  have hwrite : t.write (readBackWrite t.read).toΓ = t := by
    simp only [Tape.write]
    rcases h with hh | hne
    · simp [hh]
    · split
      · rfl
      · rw [toΓ_readBackWrite_of_ne_start hne]
        simp [Tape.read, Function.update_eq_self]
  rw [hwrite]

/-- One step of `M` corresponds to one step of `retargetInput M` through
    `retargetWrap`. The real-input tape drifts by `move (idleDir · )`.
    Requires the structural invariant on `c.input` (cells ≥ 1 ≠ start). -/
theorem retargetInput_step_commute (M : TM k) {c c' : Cfg k M.Q}
    (hstep : M.step c = some c') (realInput : Tape)
    (hinp : Tape.StartInvariant c.input) :
    (retargetInput M).step (retargetWrap M realInput c) =
    some (retargetWrap M (realInput.move (idleDir realInput.read)) c') := by
  have hne : c.state ≠ M.qhalt := state_ne_qhalt_of_step hstep
  -- Extract c' from M.step c.
  simp only [step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  -- Key fact 1: wHeads ⟨k, _⟩ = c.input.read.
  have hwHead_last : ((retargetWrap M realInput c).work ⟨k, by omega⟩).read
      = c.input.read := by
    show (if h : k < k then c.work ⟨k, h⟩ else c.input).read = c.input.read
    simp
  -- Key fact 2: fun i : Fin k => wHeads ⟨i.val, _⟩ equals fun i => (c.work i).read.
  have hinner : (fun i : Fin k =>
      ((retargetWrap M realInput c).work ⟨i.val, by omega⟩).read)
        = (fun i => (c.work i).read) := by
    funext i
    show (if h : i.val < k then c.work ⟨i.val, h⟩ else c.input).read = (c.work i).read
    rw [dif_pos i.isLt]
  -- Unfold step on the LHS. `split` reduces the halting ite (the stored
  -- decidability instance blocks `simp`/`ite_eq_right` post-v4.30).
  simp only [step, show (retargetWrap M realInput c).state = c.state from rfl,
             show (retargetInput M).qhalt = M.qhalt from rfl,
             retargetWrap_input, retargetWrap_output]
  split
  · exact absurd ‹_› hne
  simp only [Option.some.injEq]
  -- Unfold retargetInput's δ.
  dsimp only [retargetInput]
  rw [hwHead_last, hinner]
  -- Now show the Cfg equality field-by-field.
  refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
  funext i
  by_cases hik : i.val < k
  · -- i.val < k: matches M's work tape i.
    -- LHS: ((retargetWrap...).work i).writeAndMove (M.workWrites ⟨i.val, _⟩).toΓ
    --   (M.workDirs ⟨i.val, _⟩)
    -- RHS: (retargetWrap... c').work i where c'.work ⟨i.val, _⟩ is the updated tape.
    rw [retargetWrap_work_lt _ _ _ _ hik]
    show (_ : Tape).writeAndMove _ _ = (if h : i.val < k then _ else _)
    rw [dif_pos hik, dif_pos hik, dif_pos hik]
  · -- i.val = k: virtual input case.
    have hik_eq : i.val = k := by have := i.isLt; omega
    have hwork_k : (retargetWrap M realInput c).work i = c.input := by
      show (if h : i.val < k then c.work ⟨i.val, h⟩ else c.input) = c.input
      rw [dite_eq_right hik]
    have hcond : c.input.head = 0 ∨ c.input.read ≠ Γ.start := by
      by_cases hh : c.input.head = 0
      · left; exact hh
      · right
        show c.input.cells c.input.head ≠ Γ.start
        exact hinp.2 c.input.head (by omega)
    -- Rewrite LHS via hwork_k, then use tape_writeBack_eq_move.
    rw [hwork_k]
    show _ = (if h : i.val < k then _ else _)
    rw [dite_eq_right hik, dite_eq_right hik, dite_eq_right hik]
    exact tape_writeBack_eq_move c.input _ hcond

-- ════════════════════════════════════════════════════════════════════════
-- Multi-step simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Multi-step version: if `M` reaches `c'` in `t` steps, then
    `retargetInput M` reaches *some* config (differing from `retargetWrap`
    only in the real-input tape drift) in the same `t` steps. -/
theorem retargetInput_reachesIn_of_reachesIn (M : TM k)
    {c c' : Cfg k M.Q} {t : ℕ} (hreach : M.reachesIn t c c')
    (hinp : Tape.StartInvariant c.input) (hwork : ∀ i, Tape.StartInvariant (c.work i))
    (hout : Tape.StartInvariant c.output) (realInput : Tape) :
    ∃ finalReal : Tape,
      (retargetInput M).reachesIn t
        (retargetWrap M realInput c)
        (retargetWrap M finalReal c') := by
  induction hreach generalizing realInput with
  | zero => exact ⟨realInput, .zero⟩
  | @step c₀ c_mid _ _ hstep hrest ih =>
    obtain ⟨hinp', hwork', hout'⟩ :=
      Tape.StartInvariant.step M hstep hinp hwork hout
    have hcommute := retargetInput_step_commute M hstep realInput hinp
    obtain ⟨finalReal', hreach'⟩ := ih hinp' hwork' hout'
      (realInput.move (idleDir realInput.read))
    exact ⟨finalReal', .step hcommute hreach'⟩

-- ════════════════════════════════════════════════════════════════════════
-- User-facing: retargetInput M decides on a virtual input
-- ════════════════════════════════════════════════════════════════════════

/-- Initial configuration for `retargetInput M` with virtual input `z` on
    work tape `k` and an arbitrary `realInput` on the (ignored) real
    input tape. Work tapes `0..k-1` are empty; output is empty. -/
def retargetInitCfg (M : TM k) (z : List Bool) (realInput : Tape) :
    Cfg (k + 1) (retargetInput M).Q where
  state := M.qstart
  input := realInput
  work := fun i =>
    if i.val < k then Tape.init []
    else Tape.init (z.map Γ.ofBool)
  output := Tape.init []

/-- `retargetInitCfg M z realInput` is exactly the `retargetWrap` of `M`'s
    ordinary initial configuration on input `z`. -/
theorem retargetInitCfg_eq_retargetWrap (M : TM k) (z : List Bool) (realInput : Tape) :
    retargetInitCfg M z realInput = retargetWrap M realInput (M.initCfg z) := by
  simp only [retargetInitCfg, retargetWrap]
  refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
  funext i
  by_cases hik : i.val < k
  · simp only [hik, ↓reduceIte, ↓reduceDIte]
  · simp only [hik, ↓reduceIte, ↓reduceDIte]

/-- **User-facing simulation**: if `M` decides `L` in time `T`, then
    `retargetInput M` started with `z` on work tape `k` reaches a halted
    configuration within `T(|z|)` steps whose output cell 1 indicates
    membership of `z` in `L`. -/
theorem retargetInput_reachesIn_halted_of_decidesInTime (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (z : List Bool) (realInput : Tape) :
    ∃ c' t, t ≤ T z.length ∧
      (retargetInput M).reachesIn t (retargetInitCfg M z realInput) c' ∧
      (retargetInput M).halted c' ∧
      (z ∈ L → c'.output.cells 1 = Γ.one) ∧
      (z ∉ L → c'.output.cells 1 = Γ.zero) := by
  obtain ⟨c_M, t, ht, hreach, hhalt, hyes, hno⟩ := hM z
  have hinp : Tape.StartInvariant (M.initCfg z).input := by
    exact Tape.StartInvariant.init_ofBool z
  have hwork : ∀ i, Tape.StartInvariant ((M.initCfg z).work i) := fun i => by
    exact Tape.StartInvariant.init_nil
  have hout : Tape.StartInvariant (M.initCfg z).output := by
    exact Tape.StartInvariant.init_nil
  obtain ⟨finalReal, hreachSim⟩ :=
    retargetInput_reachesIn_of_reachesIn M hreach hinp hwork hout realInput
  refine ⟨retargetWrap M finalReal c_M, t, ht, ?_, ?_, ?_, ?_⟩
  · rw [retargetInitCfg_eq_retargetWrap]; exact hreachSim
  · show (retargetWrap M finalReal c_M).state = (retargetInput M).qhalt
    show c_M.state = M.qhalt
    exact hhalt
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.one
    exact hyes hz
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.zero
    exact hno hz

/-- A verifier that decides a language cannot have `qstart = qhalt`, because
    the initial output cell is blank, not an accepting or rejecting bit. -/
theorem qstart_ne_qhalt_of_decidesInTime (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) : M.qstart ≠ M.qhalt := by
  intro hstart
  obtain ⟨c', t, _ht, hreach, _hhalt, hyes, hno⟩ := hM []
  have hinit_halt : M.halted (M.initCfg []) := by
    simpa [TM.halted, Cfg.isHalted, Cfg.init] using hstart
  have ht0 : t = 0 := by
    have hle := M.reachesIn_le_halt hreach
      (TM.reachesIn.zero : M.reachesIn 0 (M.initCfg []) (M.initCfg []))
      hinit_halt
    omega
  subst ht0
  cases hreach
  by_cases hmem : ([] : List Bool) ∈ L
  · have hcell := hyes hmem
    simp [Tape.init] at hcell
  · have hcell := hno hmem
    simp [Tape.init] at hcell

/-- The verifier configuration after its forced first move off the start cells.
    For a deciding machine this is well-defined by `qstart_ne_qhalt_of_decidesInTime`. -/
noncomputable def startedCfg (M : TM k) (z : List Bool) (hne : M.qstart ≠ M.qhalt) :
    Cfg k M.Q :=
  (M.step (M.initCfg z)).get (by
    simp [TM.step, hne])

/-- `startedCfg` is the result of one deterministic verifier step from
    `M.initCfg z`. -/
theorem step_initCfg_startedCfg (M : TM k) (z : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    M.step (M.initCfg z) = some (startedCfg M z hne) := by
  simp [startedCfg, TM.step, hne]

/-- The verifier state immediately after the forced first move off `▷` is
    independent of the concrete input string: the first step reads only the
    start symbols on every tape. -/
theorem startedCfg_state_eq (M : TM k) (z₁ z₂ : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    (startedCfg M z₁ hne).state = (startedCfg M z₂ hne).state := by
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init]

/-- The verifier work tapes immediately after the forced first move off `▷`
    are independent of the concrete input string. -/
theorem startedCfg_work_eq (M : TM k) (z₁ z₂ : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    (startedCfg M z₁ hne).work = (startedCfg M z₂ hne).work := by
  funext i
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init]

/-- The verifier output tape immediately after the forced first move off `▷`
    is independent of the concrete input string. -/
theorem startedCfg_output_eq (M : TM k) (z₁ z₂ : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    (startedCfg M z₁ hne).output = (startedCfg M z₂ hne).output := by
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init]

/-- The verifier input tape immediately after the forced first move off `▷`
    is the ordinary initialized input moved right to cell 1. -/
theorem startedCfg_input_eq (M : TM k) (z : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    (startedCfg M z hne).input = (Tape.init (z.map Γ.ofBool)).move Dir3.right := by
  have hinDir :
      (M.δ M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.1 =
        Dir3.right :=
    (M.δ_right_of_start M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).1 rfl
  change (M.6 M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.1 =
    Dir3.right at hinDir
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init]
  rw [hinDir]

/-- Each verifier work tape immediately after the forced first move off `▷`
    is a blank initialized tape moved right to cell 1. -/
theorem startedCfg_work_eq_init_move_right (M : TM k) (z : List Bool)
    (hne : M.qstart ≠ M.qhalt) (i : Fin k) :
    (startedCfg M z hne).work i = (Tape.init []).move Dir3.right := by
  have hworkDir :
      (M.δ M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.2.1 i =
        Dir3.right :=
    (M.δ_right_of_start M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.1 i rfl
  change (M.6 M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.2.1 i =
    Dir3.right at hworkDir
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init, Tape.writeAndMove, Tape.write]
  rw [hworkDir]

/-- The verifier output tape immediately after the forced first move off `▷`
    is a blank initialized tape moved right to cell 1. -/
theorem startedCfg_output_eq_init_move_right (M : TM k) (z : List Bool)
    (hne : M.qstart ≠ M.qhalt) :
    (startedCfg M z hne).output = (Tape.init []).move Dir3.right := by
  have houtDir :
      (M.δ M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.2.2 =
        Dir3.right :=
    (M.δ_right_of_start M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2 rfl
  change (M.6 M.qstart Γ.start (fun _ : Fin k => Γ.start) Γ.start).2.2.2.2.2 =
    Dir3.right at houtDir
  simp [startedCfg, TM.step, hne, Tape.read, Tape.init, Tape.writeAndMove, Tape.write]
  rw [houtDir]

/-- User-facing simulation from the post-start verifier configuration.

    If `M` decides `L`, then `retargetInput M` can start from `retargetWrap`
    of the verifier state immediately after `M`'s first step on `z`, and it
    reaches the same accepting/rejecting output. This is the form needed by
    phase-composed machines whose earlier phases have already moved every
    tape off `▷`. -/
theorem retargetInput_decidesVirtual_started (M : TM k) {L : Language} {T : ℕ → ℕ}
    (hM : M.DecidesInTime L T) (z : List Bool) (realInput : Tape) :
    ∃ c' t, t + 1 ≤ T z.length ∧
      (retargetInput M).reachesIn t
        (retargetWrap M realInput (startedCfg M z (qstart_ne_qhalt_of_decidesInTime M hM))) c' ∧
      (retargetInput M).halted c' ∧
      (z ∈ L → c'.output.cells 1 = Γ.one) ∧
      (z ∉ L → c'.output.cells 1 = Γ.zero) := by
  let hne := qstart_ne_qhalt_of_decidesInTime M hM
  obtain ⟨c_M, t, ht, hreach, hhalt, hyes, hno⟩ := hM z
  have ht_ne : t ≠ 0 := by
    intro ht0
    subst ht0
    cases hreach
    exact hne hhalt
  obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht_ne
  subst ht'
  obtain ⟨c_mid, hstep, hrest⟩ : ∃ c_mid,
      M.step (M.initCfg z) = some c_mid ∧ M.reachesIn t' c_mid c_M := by
    cases hreach with
    | step hstep hrest => exact ⟨_, hstep, hrest⟩
  have hstarted : c_mid = startedCfg M z hne := by
    have hs : some c_mid = some (startedCfg M z hne) := by
      rw [← hstep, step_initCfg_startedCfg M z hne]
    exact Option.some.inj hs
  subst hstarted
  have hinp : Tape.StartInvariant (startedCfg M z hne).input := by
    have hinit : Tape.StartInvariant (M.initCfg z).input := Tape.StartInvariant.init_ofBool z
    have hwork : ∀ i, Tape.StartInvariant ((M.initCfg z).work i) :=
      fun _ => Tape.StartInvariant.init_nil
    have hout : Tape.StartInvariant (M.initCfg z).output := Tape.StartInvariant.init_nil
    obtain ⟨hinp', _, _⟩ :=
      Tape.StartInvariant.step M (step_initCfg_startedCfg M z hne) hinit hwork hout
    exact hinp'
  have hwork : ∀ i, Tape.StartInvariant ((startedCfg M z hne).work i) := by
    have hinit : Tape.StartInvariant (M.initCfg z).input := Tape.StartInvariant.init_ofBool z
    have hwork : ∀ i, Tape.StartInvariant ((M.initCfg z).work i) :=
      fun _ => Tape.StartInvariant.init_nil
    have hout : Tape.StartInvariant (M.initCfg z).output := Tape.StartInvariant.init_nil
    obtain ⟨_, hwork', _⟩ :=
      Tape.StartInvariant.step M (step_initCfg_startedCfg M z hne) hinit hwork hout
    exact hwork'
  have hout : Tape.StartInvariant (startedCfg M z hne).output := by
    have hinit : Tape.StartInvariant (M.initCfg z).input := Tape.StartInvariant.init_ofBool z
    have hwork : ∀ i, Tape.StartInvariant ((M.initCfg z).work i) :=
      fun _ => Tape.StartInvariant.init_nil
    have hout : Tape.StartInvariant (M.initCfg z).output := Tape.StartInvariant.init_nil
    obtain ⟨_, _, hout'⟩ :=
      Tape.StartInvariant.step M (step_initCfg_startedCfg M z hne) hinit hwork hout
    exact hout'
  obtain ⟨finalReal, hreachSim⟩ :=
    retargetInput_reachesIn_of_reachesIn M hrest hinp hwork hout realInput
  refine ⟨retargetWrap M finalReal c_M, t', by omega, hreachSim, ?_, ?_, ?_⟩
  · show (retargetWrap M finalReal c_M).state = (retargetInput M).qhalt
    show c_M.state = M.qhalt
    exact hhalt
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.one
    exact hyes hz
  · intro hz
    show (retargetWrap M finalReal c_M).output.cells 1 = Γ.zero
    exact hno hz

/-- Hoare lifting for `retargetInput`: if a deterministic TM satisfies a
    Hoare triple on its ordinary input tape, then `retargetInput` satisfies
    the corresponding triple when that input is supplied on the last work
    tape. The real input tape is ignored. -/
theorem retargetInput_hoareTime (M : TM k)
    {pre post : TapePred k} {b : ℕ}
    (hM : M.HoareTime pre post b)
    (hpre_inp : ∀ inp work out, pre inp work out → Tape.StartInvariant inp)
    (hpre_work : ∀ inp work out, pre inp work out → ∀ i, Tape.StartInvariant (work i))
    (hpre_out : ∀ inp work out, pre inp work out → Tape.StartInvariant out) :
    (retargetInput M).HoareTime
      (fun _inp work out =>
        pre (work ⟨k, by omega⟩) (fun i => work ⟨i.val, by omega⟩) out)
      (fun _inp work out =>
        ∃ vin : Tape, ∃ innerWork : Fin k → Tape,
          post vin innerWork out ∧
          (∀ i : Fin k, work ⟨i.val, by omega⟩ = innerWork i) ∧
          work ⟨k, by omega⟩ = vin)
      b := by
  intro realInput work out hpre
  let vin : Tape := work ⟨k, by omega⟩
  let innerWork : Fin k → Tape := fun i => work ⟨i.val, by omega⟩
  have hpreM : pre vin innerWork out := hpre
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := hM vin innerWork out hpreM
  have hinp : Tape.StartInvariant vin := hpre_inp vin innerWork out hpreM
  have hwork : ∀ i, Tape.StartInvariant (innerWork i) := hpre_work vin innerWork out hpreM
  have hout : Tape.StartInvariant out := hpre_out vin innerWork out hpreM
  obtain ⟨finalReal, hreachSim⟩ :=
    retargetInput_reachesIn_of_reachesIn M hreach hinp hwork hout realInput
  let c0 : Cfg k M.Q :=
    { state := M.qstart, input := vin, work := innerWork, output := out }
  have hworkField : (retargetWrap M realInput c0).work = work := by
    funext j
    by_cases hj : j.val < k
    · simp [retargetWrap, c0, vin, innerWork, hj]
    · have hjval : j.val = k := by
        omega
      have hjk : j = ⟨k, by omega⟩ := by
        apply Fin.ext
        simp [hjval]
      simp [retargetWrap, c0, vin, innerWork, hjk]
  have hstart :
      retargetWrap M realInput c0 =
        ({ state := (retargetInput M).qstart, input := realInput, work := work, output := out } :
          Cfg (k + 1) (retargetInput M).Q) := by
    refine Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩
    simpa [retargetInput] using hworkField
  refine ⟨retargetWrap M finalReal c', t, ht, ?_, ?_, ?_⟩
  · rw [← hstart]
    exact hreachSim
  · show (retargetWrap M finalReal c').state = (retargetInput M).qhalt
    simpa [retargetInput, retargetWrap] using hhalt
  · refine ⟨c'.input, c'.work, hpost, ?_, ?_⟩
    · intro i
      simp [retargetWrap_work_lt]
    · simp [retargetWrap_work_last]

/-- Virtual-input version of `copyInputToWorkTM_started_hoareTime`: if the
virtual input is a Boolean string at head `1` and work tape `idx` is a blank
started tape, then `retargetInput (copyInputToWorkTM idx)` copies that virtual
input onto work tape `idx` within `|x| + 1` steps. -/
theorem retargetInput_copyInputToWorkTM_started_hoareTime (idx : Fin k) (x : List Bool) :
    (retargetInput (copyInputToWorkTM idx)).HoareTime
      (fun _inp work out =>
        work ⟨k, by omega⟩ = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work ⟨idx.val, by omega⟩ = (Tape.init []).move Dir3.right ∧
        Tape.StartInvariant out ∧
        (∀ i : Fin k, i ≠ idx → Tape.StartInvariant (work ⟨i.val, by omega⟩)))
      (fun _inp work _out =>
        (work ⟨k, by omega⟩).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work ⟨k, by omega⟩).head = x.length + 1 ∧
        (work ⟨idx.val, by omega⟩).HasBinaryPrefix x)
      (x.length + 1) := by
  have hmove_right_invariant : ∀ {t : Tape},
      Tape.StartInvariant t → Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hcopy :
      (copyInputToWorkTM idx).HoareTime
        (fun inp work out =>
          inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
          work idx = (Tape.init []).move Dir3.right ∧
          Tape.StartInvariant out ∧
          (∀ i : Fin k, i ≠ idx → Tape.StartInvariant (work i)))
        (fun inp work _out =>
          inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
          inp.head = x.length + 1 ∧
          (work idx).HasBinaryPrefix x)
        (x.length + 1) :=
    (copyInputToWorkTM_started_hoareTime idx x).weaken_pre (by
      intro inp work out hpre
      refine ⟨hpre.1, ?_⟩
      rw [hpre.2.1]
      exact Tape.init_nil_move_right_hasBinaryPrefix_nil)
  have hret := retargetInput_hoareTime (M := copyInputToWorkTM idx) hcopy
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hidx, _hout, _hrest⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool x))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hidx, _hout, hrest⟩
      by_cases hi : i = idx
      · subst hi
        rw [hidx]
        exact hmove_right_invariant Tape.StartInvariant.init_nil
      · exact hrest i hi)
    (hpre_out := by
      intro _inp work out hpre
      exact hpre.2.2.1)
  refine hret.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨by simpa [hvin] using hinner.1,
    by simpa [hvin] using hinner.2.1,
    by simpa [hmap idx] using hinner.2.2⟩

/-- Virtual-input version of `inputLengthPlusOneCounterTM_started_hoareTime`:
if the virtual input is a started Boolean string and work tape `counterIdx`
is a started blank tape, then `retargetInput (inputLengthPlusOneCounterTM
counterIdx)` materializes a unary counter of length `|x| + 1` on that tape. -/
theorem retargetInput_inputLengthPlusOneCounterTM_started_hoareTime
    (counterIdx : Fin k) (x : List Bool) :
    (retargetInput (inputLengthPlusOneCounterTM counterIdx)).HoareTime
      (fun _inp work out =>
        work ⟨k, by omega⟩ = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work ⟨counterIdx.val, by omega⟩ = (Tape.init []).move Dir3.right ∧
        Tape.StartInvariant out ∧
        (∀ i : Fin k, i ≠ counterIdx → Tape.StartInvariant (work ⟨i.val, by omega⟩)))
      (fun _inp work _out =>
        (work ⟨counterIdx.val, by omega⟩).HasUnaryCounter (x.length + 1) ∧
        (work ⟨counterIdx.val, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨counterIdx.val, by omega⟩).cells j ≠ Γ.start))
      (inputLengthPlusOneCounterTime x.length) := by
  have hmove_right_invariant : ∀ {t : Tape},
      Tape.StartInvariant t → Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hcounter :
      (inputLengthPlusOneCounterTM counterIdx).HoareTime
        (fun inp work _out =>
          inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
          work counterIdx = (Tape.init []).move Dir3.right ∧
          Tape.StartInvariant _out ∧
          (∀ i : Fin k, i ≠ counterIdx → Tape.StartInvariant (work i)))
        (fun _inp work _out =>
          (work counterIdx).HasUnaryCounter (x.length + 1) ∧
          (work counterIdx).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start))
        (inputLengthPlusOneCounterTime x.length) :=
    (inputLengthPlusOneCounterTM_started_hoareTime counterIdx x).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1⟩)
  have hret := retargetInput_hoareTime (M := inputLengthPlusOneCounterTM counterIdx) hcounter
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hidx, _hout, _hrest⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool x))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hidx, _hout, hrest⟩
      by_cases hi : i = counterIdx
      · subst hi
        rw [hidx]
        exact hmove_right_invariant Tape.StartInvariant.init_nil
      · exact hrest i hi)
    (hpre_out := by
      intro _inp work out hpre
      exact hpre.2.2.1)
  refine hret.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨by simpa [hmap counterIdx] using hinner.1,
    by simpa [hmap counterIdx] using hinner.2.1,
    by simpa [hmap counterIdx] using hinner.2.2⟩

/-- Virtual-input version of
`inputLengthPlusOneCounterTM_started_tracksInput_hoareTime`: besides building
the unary counter on work tape `counterIdx`, the postcondition also records
the final cells and head of the virtual-input tape itself. -/
theorem retargetInput_inputLengthPlusOneCounterTM_started_tracksInput_hoareTime
    (counterIdx : Fin k) (x : List Bool) :
    (retargetInput (inputLengthPlusOneCounterTM counterIdx)).HoareTime
      (fun _inp work out =>
        work ⟨k, by omega⟩ = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work ⟨counterIdx.val, by omega⟩ = (Tape.init []).move Dir3.right ∧
        Tape.StartInvariant out ∧
        (∀ i : Fin k, i ≠ counterIdx → Tape.StartInvariant (work ⟨i.val, by omega⟩)))
      (fun _inp work _out =>
        (work ⟨k, by omega⟩).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work ⟨k, by omega⟩).head = x.length + 1 ∧
        (work ⟨counterIdx.val, by omega⟩).HasUnaryCounter (x.length + 1) ∧
        (work ⟨counterIdx.val, by omega⟩).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work ⟨counterIdx.val, by omega⟩).cells j ≠ Γ.start))
      (inputLengthPlusOneCounterTime x.length) := by
  have hmove_right_invariant : ∀ {t : Tape},
      Tape.StartInvariant t → Tape.StartInvariant (t.move Dir3.right) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simpa [Tape.move_cells] using ht.1
    · intro j hj
      simpa [Tape.move_cells] using ht.2 j hj
  have hcounter :
      (inputLengthPlusOneCounterTM counterIdx).HoareTime
        (fun inp work _out =>
          inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
          work counterIdx = (Tape.init []).move Dir3.right ∧
          Tape.StartInvariant _out ∧
          (∀ i : Fin k, i ≠ counterIdx → Tape.StartInvariant (work i)))
        (fun inp work _out =>
          inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
          inp.head = x.length + 1 ∧
          (work counterIdx).HasUnaryCounter (x.length + 1) ∧
          (work counterIdx).cells 0 = Γ.start ∧
          (∀ j, j ≥ 1 → (work counterIdx).cells j ≠ Γ.start))
        (inputLengthPlusOneCounterTime x.length) :=
    (inputLengthPlusOneCounterTM_started_tracksInput_hoareTime counterIdx x).weaken_pre (by
      intro inp work out hpre
      exact ⟨hpre.1, hpre.2.1⟩)
  have hret := retargetInput_hoareTime (M := inputLengthPlusOneCounterTM counterIdx) hcounter
    (hpre_inp := by
      intro _inp work out hpre
      rcases hpre with ⟨hvin, _hidx, _hout, _hrest⟩
      rw [hvin]
      exact hmove_right_invariant (Tape.StartInvariant.init_ofBool x))
    (hpre_work := by
      intro _inp work out hpre i
      rcases hpre with ⟨_hvin, hidx, _hout, hrest⟩
      by_cases hi : i = counterIdx
      · subst hi
        rw [hidx]
        exact hmove_right_invariant Tape.StartInvariant.init_nil
      · exact hrest i hi)
    (hpre_out := by
      intro _inp work out hpre
      exact hpre.2.2.1)
  refine hret.strengthen_post ?_
  intro _inp work out hpost
  rcases hpost with ⟨vin, innerWork, hinner, hmap, hvin⟩
  exact ⟨by rw [hvin]; exact hinner.1,
    by rw [hvin]; exact hinner.2.1,
    by simpa [hmap counterIdx] using hinner.2.2.1,
    by simpa [hmap counterIdx] using hinner.2.2.2.1,
    by simpa [hmap counterIdx] using hinner.2.2.2.2⟩

end TM

end Complexity
