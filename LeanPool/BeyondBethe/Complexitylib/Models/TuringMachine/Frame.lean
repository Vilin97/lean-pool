/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Placement
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers

/-!
# Frame rules for composite machines

Two things a machine built out of sub-machines needs to know: that a
sub-machine's Hoare triple still holds once its tapes are embedded in a larger
tape space (`TM.placeWorkTM_hoareTime_frame`), and that a run of bounded length
cannot have touched cells far from where its heads started
(`TM.reachesIn_work_cells_far`). The second is what lets a *bounded* wipe reset
an opaque machine's scratch completely.

## Main results

- `TM.placeWorkTM_hoareTime_frame` — a Hoare triple survives tape embedding
- `TM.reachesIn_work_cells_far` — a `t`-step run leaves cells beyond `head + t` alone
- `TM.reachesIn_startInvariant` — runs preserve `Tape.StartInvariant`
- `TM.seqTM_det` — sequential composition is deterministic on its components
- `TM.IdlesInput` — machines that never move their input head
-/


@[expose] public section

namespace Complexity

namespace TM

/-- The parked blank tape every scratch tape starts and ends at. -/
def parkedBlank : Tape := (Tape.init []).move Dir3.right

/-! ## Embedding a Hoare triple in a larger tape space

A composite machine runs sub-machines that each own a fixed number of work
tapes, while carrying persistent state (running values, fuel registers) on tapes
those sub-machines never touch. `TM.placeWorkTM` already gives the exact
frame-preserving simulation
(`placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant`); the lemma below turns
that into a Hoare-triple-level tool, so each embedding is a single lemma
application instead of a fresh `reachesIn` argument. -/

/-- **Placing a Hoare triple.** If `tm : TM n` satisfies a Hoare triple, then
`placeWorkTM pre post tm` satisfies the triple obtained by reindexing `tm`'s
work-tape predicate through the middle block, with an arbitrary `Parked`-style
frame (`extras`) held exactly fixed outside it. -/
theorem placeWorkTM_hoareTime_frame {n pre post : ℕ} (tm : TM n)
    {preSmall postSmall : TapePred n} {b : ℕ}
    (h : tm.HoareTime preSmall postSmall b)
    (extras : Fin (pre + n + post) → Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).HoareTime
      (fun inp work out => preSmall inp (fun i => work (placeWorkIdx pre post i)) out ∧
        ∀ i, ¬placeWorkInMiddle pre n i → work i = extras i)
      (fun inp work out => postSmall inp (fun i => work (placeWorkIdx pre post i)) out ∧
        ∀ i, ¬placeWorkInMiddle pre n i → work i = extras i)
      b := by
  rintro inp work out ⟨hpre, hextra⟩
  set wSmall : Fin n → Tape := fun i => work (placeWorkIdx pre post i) with hwSmall
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp wSmall out hpre
  have hweq : work = (placeWorkCfg tm pre post extras
      { state := tm.qstart, input := inp, work := wSmall, output := out }).work := by
    funext i
    by_cases hmid : placeWorkInMiddle pre n i
    · rw [show i = placeWorkIdx pre post (placeWorkCoord pre n i hmid) from
        (placeWorkIdx_placeWorkCoord i hmid).symm, placeWorkCfg_work_middle]
    · rw [placeWorkCfg_work_extra tm pre post extras _ i hmid]
      exact hextra i hmid
  refine ⟨placeWorkCfg tm pre post extras c', t, ht, ?_,
    (placeWorkCfg_halted_iff tm pre post extras c').mpr hhalt, ?_, ?_⟩
  · rw [hweq]
    exact placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant tm pre post extras hreach
      hinv hhead
  · show postSmall c'.input (fun i => (placeWorkCfg tm pre post extras c').work
      (placeWorkIdx pre post i)) c'.output
    simp only [placeWorkCfg_work_middle]
    exact hpost
  · intro i hi
    exact placeWorkCfg_work_extra tm pre post extras c' i hi

/-! ## What a bounded run can have disturbed

Resetting an opaque machine's scratch tapes between calls needs
to know *how far out* the machine could possibly have written. Since each head
moves by at most one cell per step and a machine only ever writes under its
heads, a `t`-step run leaves every cell beyond `head + t` exactly as it found
it. That is what makes the bounded wipe of `TM.resetTapesTM` complete rather
than merely partial. -/

/-- One step leaves every work-tape cell other than that tape's own head
unchanged: a machine writes only under its heads. -/
theorem work_cells_ne_of_step {n : ℕ} {tm : TM n} {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') (i : Fin n) {j : ℕ} (hj : j ≠ (c.work i).head) :
    (c'.work i).cells j = (c.work i).cells j := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    simp only [Tape.move_cells, Tape.write]
    split
    · rfl
    · change Function.update (c.work i).cells (c.work i).head _ j = (c.work i).cells j
      rw [Function.update_of_ne hj]

/-- **Cells beyond a work head's maximum reach are never touched.** -/
theorem reachesIn_work_cells_far {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      ∀ (i : Fin n) (j : ℕ), (c.work i).head + t < j →
        (c'.work i).cells j = (c.work i).cells j := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach i j _
      cases hreach
      rfl
  | succ t ih =>
      intro c c' hreach i j hj
      cases hreach with
      | step hstep hrest =>
          next c'' =>
            have hhead : (c''.work i).head ≤ (c.work i).head + 1 :=
              (head_le_start_add_of_reachesIn tm (TM.reachesIn.step hstep TM.reachesIn.zero)).2.2 i
            have hcell : (c''.work i).cells j = (c.work i).cells j :=
              work_cells_ne_of_step hstep i (by omega)
            rw [ih hrest i j (by omega), hcell]

/-- The standing left-marker invariant survives an entire run, on every tape. -/
theorem reachesIn_startInvariant {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c.input.StartInvariant → (∀ i, (c.work i).StartInvariant) → c.output.StartInvariant →
      c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
        c'.output.StartInvariant := by
  intro t c c' hreach
  induction hreach with
  | zero => exact fun hi hw ho => ⟨hi, hw, ho⟩
  | step hstep _ ih =>
      intro hi hw ho
      obtain ⟨hi', hw', ho'⟩ := Tape.StartInvariant.step _ hstep hi hw ho
      exact ih hi' hw' ho'

/-- A fully parked tape frame passes through a combinator seam unchanged —
the boundary obligation of `TM.seqTM_hoareTime` in the common case where every
tape is parked on both sides of the seam. -/
theorem parked_transition {n : ℕ} {inp₀ out₀ : Tape} {W : Fin n → Tape}
    (hinp : Parked inp₀) (hW : ∀ i, Parked (W i)) (hout : Parked out₀) :
    transitionInput inp₀ = inp₀ ∧
      (fun i => transitionTape (W i)) = W ∧ transitionTape out₀ = out₀ :=
  ⟨transitionInput_eq_self hinp.read_ne_start,
    funext fun i => transitionTape_eq_self (hW i).read_ne_start,
    transitionTape_eq_self hout.read_ne_start⟩

/-- **Chaining two fully-determined phases.** When each phase pins down the
entire tape family and every intermediate tape is parked, sequential
composition needs no boundary reasoning at all. -/
theorem seqTM_det {n : ℕ} (m₁ m₂ : TM n) {inp₀ out₀ : Tape} {W₀ W₁ W₂ : Fin n → Tape}
    {b₁ b₂ : ℕ} (hinp : Parked inp₀) (hout : Parked out₀) (hW₁ : ∀ i, Parked (W₁ i))
    (h₁ : m₁.HoareTime (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀) b₁)
    (h₂ : m₂.HoareTime (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀) b₂) :
    (seqTM m₁ m₂).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀)
      (b₁ + 1 + b₂) := by
  refine seqTM_hoareTime m₁ m₂ h₁ ?_ h₂
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact parked_transition hinp hW₁ hout

/-- A machine that never moves its real input head off a parked position: its
transition function always returns `idleDir` for the input tape. Machines that
read their input from a work tape instead (`TM.retargetInput` and everything
built on it) satisfy this. -/
def IdlesInput {n : ℕ} (tm : TM n) : Prop :=
  ∀ q iHead wHeads oHead, (tm.δ q iHead wHeads oHead).2.2.2.1 = idleDir iHead

/-- An input-idling machine preserves a parked real input tape exactly, for
any number of steps. -/
theorem reachesIn_input_eq_of_idlesInput {n : ℕ} {tm : TM n} (hidle : IdlesInput tm) :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' → Parked c.input →
      c'.input = c.input := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach _
      cases hreach
      rfl
  | succ t ih =>
      intro c c' hreach hp
      cases hreach with
      | step hstep hrest =>
          next c'' =>
            have hc'' : c''.input = c.input := by
              simp only [TM.step] at hstep
              split at hstep
              · simp at hstep
              · simp only [Option.some.injEq] at hstep
                rw [← hstep]
                show c.input.move _ = c.input
                rw [hidle, hp.move_idle]
            rw [ih hrest (by rw [hc'']; exact hp), hc'']

/-- The blank tape satisfies the left-marker invariant. -/
theorem startInvariant_initNil : Tape.StartInvariant (Tape.init ([] : List Γ)) := by
  refine ⟨Tape.init_cells_zero [], fun j hj => ?_⟩
  rw [show j = (j - 1) + 1 from by omega, Tape.init_cells_ge [] (j - 1) (by simp)]
  decide

/-- A tape initialized with a Boolean string satisfies the left-marker
invariant: `Γ.ofBool` never produces `▷`. -/
theorem startInvariant_initOfBool (y : List Bool) :
    Tape.StartInvariant (Tape.init (y.map Γ.ofBool)) := by
  refine ⟨Tape.init_cells_zero _, fun j hj => ?_⟩
  have hj1 : j = (j - 1) + 1 := by omega
  by_cases hlt : j - 1 < y.length
  · rw [hj1, Tape.init_ofBool_cells_lt y (j - 1) hlt]
    cases y[j - 1]'hlt <;> decide
  · rw [hj1, Tape.init_ofBool_cells_ge y (j - 1) (by omega)]
    decide

end TM

end Complexity
