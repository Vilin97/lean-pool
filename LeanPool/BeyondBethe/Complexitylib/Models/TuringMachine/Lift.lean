/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Tape-layout combinators: extra work tapes and output retargeting

Two DTM combinators that change a machine's tape layout without changing
its behavior:

- `TM.liftTM tm m` — pad `tm : TM n` with `m` never-used work tapes, giving
  a `TM (n + m)` that decides/computes exactly as `tm` does, in the same
  time bound. The extra tapes bounce off `▷` on the first step (respecting
  `δ_right_of_start`) and then park at cell 1 forever, writing `□` over the
  `□` already there.
- `TM.retargetOutput tm` — redirect the output actions of `tm : TM n` to a
  fresh work tape `n` (the `Fin.last n` tape), giving a `TM (n + 1)` whose
  real output tape is idled. Used to "compute a value onto a work tape",
  e.g. materializing a clock value for downstream composition.

## Correspondence proofs

Both combinators are proved correct by a step-commutation lemma through a
configuration embedding (`liftCfg` / `retargetCfg`): one step of the
derived machine on an embedded configuration equals one step of `tm`,
embedded. The embeddings park the dummy tapes at cell 1 with blank cells;
the initial configuration instead has dummy heads at cell 0 (on `▷`), so
the step lemma is stated for any dummy tape with `cells = Tape.init []` and
`head ≤ 1` — covering both the initial bounce and the parked steady state
(mirroring `NTM.pad0`).

The time bounds are preserved *exactly* (no `+ 1`): the dummy-tape bounce
happens during the simulated machine's own first step.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Dummy-tape dynamics
-- ════════════════════════════════════════════════════════════════════════

/-- One idle action (`readBackWrite` of the read + `idleDir`) sends any
    blank tape with head at cell 0 or 1 to the canonical *parked* tape
    `(Tape.init []).move Dir3.right` (head 1, blank cells): at cell 0 the
    write is a structural no-op and the head bounces right off `▷`; at
    cell 1 it writes `□` over `□` and stays. -/
private theorem dummy_writeAndMove (w : Tape)
    (hc : w.cells = (Tape.init []).cells) (hh : w.head ≤ 1) :
    w.writeAndMove (readBackWrite w.read).toΓ (idleDir w.read)
      = (Tape.init []).move Dir3.right := by
  have hread : w.read = (Tape.init []).cells w.head := by rw [Tape.read, hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with h0 | h1
  · -- head at cell 0: `w` *is* `Tape.init []`, and the action is the bounce
    have hw : w = Tape.init [] := by
      calc w = ⟨w.head, w.cells⟩ := rfl
        _ = Tape.init [] := by rw [h0, hc]; rfl
    subst hw
    rfl
  · -- head at cell 1: write `□` over `□` and stay
    have hr : w.read = Γ.blank := by rw [hread, h1]; rfl
    rw [hr]
    show w.write (readBackWrite Γ.blank).toΓ = (Tape.init []).move Dir3.right
    rw [Tape.write, ite_eq_right (show ¬ w.head = 0 by omega), h1, hc]
    rw [show (readBackWrite Γ.blank).toΓ = (Tape.init []).cells 1 from rfl,
      Function.update_eq_self]
    rfl

-- ════════════════════════════════════════════════════════════════════════
-- liftTM: extra never-used work tapes
-- ════════════════════════════════════════════════════════════════════════

/-- Pad `tm : TM n` with `m` never-used work tapes. Work tapes `0..n-1`
    (indexed by `Fin.castAdd m i`) behave exactly as `tm`'s; the extra
    tapes `n..n+m-1` write back what they read (`readBackWrite`) and idle
    (`idleDir`): they bounce off `▷` at the first step and then park at
    cell 1 forever. Input and output behavior is unchanged. -/
def liftTM (tm : TM n) (m : ℕ) : TM (n + m) where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun q iHead wHeads oHead =>
    let r := tm.δ q iHead (fun i => wHeads (Fin.castAdd m i)) oHead
    ( r.1,
      fun i => if h : i.val < n then r.2.1 ⟨i.val, h⟩ else readBackWrite (wHeads i),
      r.2.2.1,
      r.2.2.2.1,
      fun i => if h : i.val < n then r.2.2.2.2.1 ⟨i.val, h⟩ else idleDir (wHeads i),
      r.2.2.2.2.2 )
  δ_right_of_start := by
    intro q iHead wHeads oHead
    obtain ⟨hin, hwork, hout⟩ :=
      tm.δ_right_of_start q iHead (fun i => wHeads (Fin.castAdd m i)) oHead
    refine ⟨hin, fun i hi => ?_, hout⟩
    dsimp only
    split
    · next hlt => exact hwork ⟨i.val, hlt⟩ hi
    · next hlt => exact idleDir_right_of_start hi

/-- Embed a configuration of `tm : TM n` into one of `tm.liftTM m`:
    work tapes `i < n` are `c`'s, the extras are the canonical parked
    blank tape (head 1, blank cells). State, input, and output are
    shared. -/
def liftCfg (tm : TM n) (m : ℕ) (c : Cfg n tm.Q) : Cfg (n + m) tm.Q where
  state := c.state
  input := c.input
  work := fun i =>
    if h : i.val < n then c.work ⟨i.val, h⟩ else (Tape.init []).move Dir3.right
  output := c.output

/-- `liftCfg` leaves the state unchanged. -/
@[simp] theorem liftCfg_state (tm : TM n) (m : ℕ) (c : Cfg n tm.Q) :
    (tm.liftCfg m c).state = c.state := rfl

/-- `liftCfg` leaves the input tape unchanged. -/
@[simp] theorem liftCfg_input (tm : TM n) (m : ℕ) (c : Cfg n tm.Q) :
    (tm.liftCfg m c).input = c.input := rfl

/-- `liftCfg` leaves the output tape unchanged. -/
@[simp] theorem liftCfg_output (tm : TM n) (m : ℕ) (c : Cfg n tm.Q) :
    (tm.liftCfg m c).output = c.output := rfl

/-- `liftCfg` maps the first `n` work tapes to `c`'s work tapes. -/
theorem liftCfg_work_lt (tm : TM n) (m : ℕ) (c : Cfg n tm.Q)
    (i : Fin (n + m)) (h : i.val < n) :
    (tm.liftCfg m c).work i = c.work ⟨i.val, h⟩ := dif_pos h

/-- `liftCfg` maps the extra work tapes to the parked blank tape. -/
theorem liftCfg_work_ge (tm : TM n) (m : ℕ) (c : Cfg n tm.Q)
    (i : Fin (n + m)) (h : n ≤ i.val) :
    (tm.liftCfg m c).work i = (Tape.init []).move Dir3.right :=
  dite_eq_right (Nat.not_lt.mpr h)

/-- **Unified step commutation** for `liftTM`. If the extra work tapes of
    `C` are blank with head at cell 0 or 1 and the rest of `C` matches `c`,
    then one step of `tm.liftTM m` from `C` is one step of `tm` from `c`,
    embedded via `liftCfg` (extras parked). This covers both the initial
    bounce (extra heads at 0, on `▷`) and the parked steady state. -/
private theorem liftTM_step_of_extras (tm : TM n) (m : ℕ) {c : Cfg n tm.Q}
    {C : Cfg (n + m) tm.Q}
    (hs : C.state = c.state) (hi : C.input = c.input) (ho : C.output = c.output)
    (hw : ∀ (i : Fin (n + m)) (h : i.val < n), C.work i = c.work ⟨i.val, h⟩)
    (hd : ∀ i : Fin (n + m), n ≤ i.val →
      (C.work i).cells = (Tape.init []).cells ∧ (C.work i).head ≤ 1) :
    (tm.liftTM m).step C = (tm.step c).map (tm.liftCfg m) := by
  by_cases hh : c.state = tm.qhalt
  · -- both machines are halted
    have h1 : (tm.liftTM m).step C = none := by
      simp only [step, hs, hh, show (tm.liftTM m).qhalt = tm.qhalt from rfl,
        ↓reduceIte]
    have h2 : tm.step c = none := by
      simp only [step, hh, ↓reduceIte]
    rw [h1, h2]; rfl
  · cases hstep : tm.step c with
    | none => exact absurd hstep (by simp [step, hh])
    | some c' =>
      -- extract the explicit stepped configuration
      simp only [step, hh, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hinner : (fun i : Fin n => (C.work (Fin.castAdd m i)).read)
          = fun i => (c.work i).read :=
        funext fun i => by rw [hw (Fin.castAdd m i) i.isLt]; rfl
      simp only [step, Option.map_some]
      dsimp only [liftTM, liftCfg]
      rw [hs, hi, ho, hinner, ite_eq_right hh]
      refine congrArg some (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩)
      funext i
      by_cases hik : i.val < n
      · rw [hw i hik, dif_pos hik, dif_pos hik, dif_pos hik]
      · have hdi := hd i (Nat.le_of_not_lt hik)
        rw [dite_eq_right hik, dite_eq_right hik, dite_eq_right hik]
        exact dummy_writeAndMove (C.work i) hdi.1 hdi.2

/-- **Step commutation** on embedded configurations: once the extra tapes
    are parked, `tm.liftTM m` steps exactly as `tm` does through
    `liftCfg`. -/
theorem liftTM_step_liftCfg (tm : TM n) (m : ℕ) (c : Cfg n tm.Q) :
    (tm.liftTM m).step (tm.liftCfg m c) = (tm.step c).map (tm.liftCfg m) :=
  liftTM_step_of_extras tm m rfl rfl rfl (fun _ h => dif_pos h)
    (fun i h => by
      rw [liftCfg_work_ge tm m c i h]
      exact ⟨rfl, Nat.le_refl 1⟩)

/-- The first step out of the lifted initial configuration: the extra
    tapes bounce off `▷` into the parked position while `tm` performs its
    own first step. -/
private theorem liftTM_step_initCfg (tm : TM n) (m : ℕ) (x : List Bool) :
    (tm.liftTM m).step ((tm.liftTM m).initCfg x)
      = (tm.step (tm.initCfg x)).map (tm.liftCfg m) :=
  liftTM_step_of_extras tm m rfl rfl rfl (fun _ _ => rfl)
    (fun _ _ => ⟨rfl, Nat.zero_le 1⟩)

/-- Multi-step commutation through `liftCfg`. -/
private theorem liftTM_reachesIn_liftCfg (tm : TM n) (m : ℕ) {t : ℕ}
    {c c' : Cfg n tm.Q} (h : tm.reachesIn t c c') :
    (tm.liftTM m).reachesIn t (tm.liftCfg m c) (tm.liftCfg m c') := by
  induction h with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by rw [liftTM_step_liftCfg, hstep]; rfl) ih

/-- Multi-step simulation from the initial configuration: the lifted run
    tracks `tm`'s run in the same number of steps, agreeing on state and
    output. -/
private theorem liftTM_reachesIn_init (tm : TM n) (m : ℕ) (x : List Bool)
    {t : ℕ} {c' : Cfg n tm.Q} (h : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (n + m) tm.Q,
      (tm.liftTM m).reachesIn t ((tm.liftTM m).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.output = c'.output := by
  cases h with
  | zero => exact ⟨(tm.liftTM m).initCfg x, .zero, rfl, rfl⟩
  | step hstep hrest =>
    exact ⟨tm.liftCfg m c',
      .step (by rw [liftTM_step_initCfg, hstep]; rfl)
        (liftTM_reachesIn_liftCfg tm m hrest),
      rfl, rfl⟩

/-- A positive-length run of a lifted machine from genuine initialization has
the exact `liftCfg` endpoint of the underlying run. The positivity hypothesis
excludes the sole mismatch at time zero, when the extra tapes have not yet
bounced from cell `0` to their canonical parked position at cell `1`. -/
theorem liftTM_reachesIn_initCfg_of_pos (tm : TM n) (m : ℕ) (x : List Bool)
    {t : ℕ} {c' : Cfg n tm.Q} (ht : 0 < t)
    (h : tm.reachesIn t (tm.initCfg x) c') :
    (tm.liftTM m).reachesIn t ((tm.liftTM m).initCfg x) (tm.liftCfg m c') := by
  cases h with
  | zero => omega
  | step hstep hrest =>
      exact .step (by rw [liftTM_step_initCfg, hstep]; rfl)
        (liftTM_reachesIn_liftCfg tm m hrest)

/-- Unbounded-reachability commutation through `liftCfg`. -/
private theorem liftTM_reaches_liftCfg (tm : TM n) (m : ℕ) {c c' : Cfg n tm.Q}
    (h : tm.reaches c c') :
    (tm.liftTM m).reaches (tm.liftCfg m c) (tm.liftCfg m c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c₂ _ hbc ih =>
    refine ih.tail ?_
    show (tm.liftTM m).step (tm.liftCfg m b) = some (tm.liftCfg m c₂)
    have hb : tm.step b = some c₂ := hbc
    rw [liftTM_step_liftCfg, hb]; rfl

/-- Unbounded simulation from the initial configuration, agreeing on state
    and output. -/
private theorem liftTM_reaches_init (tm : TM n) (m : ℕ) (x : List Bool)
    {c' : Cfg n tm.Q} (h : tm.reaches (tm.initCfg x) c') :
    ∃ C' : Cfg (n + m) tm.Q,
      (tm.liftTM m).reaches ((tm.liftTM m).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.output = c'.output := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c₁, hstep, hrest⟩
  · subst heq
    exact ⟨(tm.liftTM m).initCfg x, Relation.ReflTransGen.refl, rfl, rfl⟩
  · refine ⟨tm.liftCfg m c',
      Relation.ReflTransGen.head ?_ (liftTM_reaches_liftCfg tm m hrest), rfl, rfl⟩
    show (tm.liftTM m).step ((tm.liftTM m).initCfg x) = some (tm.liftCfg m c₁)
    have h1 : tm.step (tm.initCfg x) = some c₁ := hstep
    rw [liftTM_step_initCfg, h1]; rfl

/-- Every configuration the lifted machine reaches from its initial
    configuration is either that initial configuration or the `liftCfg`
    image of a configuration `tm` reaches. -/
private theorem liftTM_reaches_init_inv (tm : TM n) (m : ℕ) (x : List Bool)
    {C' : Cfg (n + m) tm.Q}
    (h : (tm.liftTM m).reaches ((tm.liftTM m).initCfg x) C') :
    C' = (tm.liftTM m).initCfg x ∨
      ∃ c' : Cfg n tm.Q, tm.reaches (tm.initCfg x) c' ∧ C' = tm.liftCfg m c' := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b C₂ _ hbc ih =>
    have hstep' : (tm.liftTM m).step b = some C₂ := hbc
    rcases ih with rfl | ⟨c₀, hc₀, rfl⟩
    · rw [liftTM_step_initCfg] at hstep'
      cases hmc : tm.step (tm.initCfg x) with
      | none => rw [hmc] at hstep'; simp at hstep'
      | some c₁ =>
        rw [hmc] at hstep'
        exact Or.inr ⟨c₁, Relation.ReflTransGen.single hmc,
          (Option.some.inj hstep').symm⟩
    · rw [liftTM_step_liftCfg] at hstep'
      cases hmc : tm.step c₀ with
      | none => rw [hmc] at hstep'; simp at hstep'
      | some c₁ =>
        rw [hmc] at hstep'
        exact Or.inr ⟨c₁, hc₀.tail hmc, (Option.some.inj hstep').symm⟩

/-- **Lifting preserves deciding, with the same time bound.** The extra
    work tapes never interfere: the lifted machine's run tracks `tm`'s run
    step for step. -/
theorem liftTM_decidesInTime (tm : TM n) (m : ℕ) {L : Language} {T : ℕ → ℕ}
    (h : tm.DecidesInTime L T) : (tm.liftTM m).DecidesInTime L T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hyes, hno⟩ := h x
  obtain ⟨C', hR, hstate, hout⟩ := liftTM_reachesIn_init tm m x hreach
  refine ⟨C', t, ht, hR, ?_, fun hx => ?_, fun hx => ?_⟩
  · show C'.state = (tm.liftTM m).qhalt
    rw [hstate]; exact hhalt
  · rw [hout]; exact hyes hx
  · rw [hout]; exact hno hx

/-- **Lifting preserves function computation, with the same time bound.** -/
theorem liftTM_computesInTime (tm : TM n) (m : ℕ) {f : List Bool → List Bool}
    {T : ℕ → ℕ} (h : tm.ComputesInTime f T) :
    (tm.liftTM m).ComputesInTime f T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := h x
  obtain ⟨C', hR, hstate, houtC⟩ := liftTM_reachesIn_init tm m x hreach
  refine ⟨C', t, ht, hR, ?_, ?_⟩
  · show C'.state = (tm.liftTM m).qhalt
    rw [hstate]; exact hhalt
  · rw [houtC]; exact hout

/-- **Lifting preserves space bounds up to the parked cell.** The extra
    work tapes' heads never move past cell 1, so `tm.liftTM m` decides `L`
    in space `max (S ·) 1`. -/
theorem liftTM_decidesInSpace (tm : TM n) (m : ℕ) {L : Language} {S : ℕ → ℕ}
    (h : tm.DecidesInSpace L S) :
    (tm.liftTM m).DecidesInSpace L (fun k => max (S k) 1) := by
  obtain ⟨hspace, hdec⟩ := h
  constructor
  · intro x C' hreach
    rcases liftTM_reaches_init_inv tm m x hreach with rfl | ⟨c', hc', rfl⟩
    · simp [Cfg.WithinDecisionSpace, Cfg.WithinAuxSpace]
    · obtain ⟨⟨hwork, hin⟩, hout⟩ := hspace x c' hc'
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro j
        by_cases hj : j.val < n
        · rw [liftCfg_work_lt tm m c' j hj]
          exact (hwork ⟨j.val, hj⟩).trans (le_max_left _ _)
        · rw [liftCfg_work_ge tm m c' j (Nat.le_of_not_lt hj)]
          exact le_max_right _ _
      · simp only [liftCfg_input]
        have := le_max_left (S x.length) 1
        omega
      · simp only [liftCfg_output]
        have := le_max_left (S x.length) 1
        omega
  · intro x
    obtain ⟨c', hreach, hhalt, hyes, hno⟩ := hdec x
    obtain ⟨C', hR, hstate, hout⟩ := liftTM_reaches_init tm m x hreach
    refine ⟨C', hR, ?_, fun hx => ?_, fun hx => ?_⟩
    · show C'.state = (tm.liftTM m).qhalt
      rw [hstate]; exact hhalt
    · rw [hout]; exact hyes hx
    · rw [hout]; exact hno hx

-- ════════════════════════════════════════════════════════════════════════
-- retargetOutput: write the output onto a fresh work tape
-- ════════════════════════════════════════════════════════════════════════

/-- Redirect `tm`'s output actions to a fresh work tape. `retargetOutput
    tm : TM (n + 1)` behaves like `tm`, except that the output write and
    direction are applied to work tape `n` (the `Fin.last n` tape), whose
    read is fed to `tm.δ` as the virtual output head; the real output tape
    is idled (`readBackWrite`/`idleDir`). Work tapes `0..n-1` (indexed by
    `Fin.castSucc i`) and the input tape behave as before. -/
def retargetOutput (tm : TM n) : TM (n + 1) where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun q iHead wHeads oHead =>
    let r := tm.δ q iHead (fun i => wHeads (Fin.castSucc i)) (wHeads (Fin.last n))
    ( r.1,
      fun i => if h : i.val < n then r.2.1 ⟨i.val, h⟩ else r.2.2.1,
      readBackWrite oHead,
      r.2.2.2.1,
      fun i => if h : i.val < n then r.2.2.2.2.1 ⟨i.val, h⟩ else r.2.2.2.2.2,
      idleDir oHead )
  δ_right_of_start := by
    intro q iHead wHeads oHead
    obtain ⟨hin, hwork, hout⟩ :=
      tm.δ_right_of_start q iHead (fun i => wHeads (Fin.castSucc i))
        (wHeads (Fin.last n))
    refine ⟨hin, fun i hi => ?_, fun hoh => idleDir_right_of_start hoh⟩
    dsimp only
    split
    · next hlt => exact hwork ⟨i.val, hlt⟩ hi
    · next hlt =>
      have hi_last : i = Fin.last n := by
        apply Fin.ext
        have := i.isLt
        simp only [Fin.val_last]
        omega
      exact hout (hi_last ▸ hi)

/-- Embed a configuration of `tm : TM n` into one of `tm.retargetOutput`:
    work tapes `i < n` are `c`'s, work tape `n` is `c`'s output tape, and
    the real output tape is the canonical parked blank tape. -/
def retargetCfg (tm : TM n) (c : Cfg n tm.Q) : Cfg (n + 1) tm.Q where
  state := c.state
  input := c.input
  work := fun i => if h : i.val < n then c.work ⟨i.val, h⟩ else c.output
  output := (Tape.init []).move Dir3.right

/-- `retargetCfg` leaves the state unchanged. -/
@[simp] theorem retargetCfg_state (tm : TM n) (c : Cfg n tm.Q) :
    (tm.retargetCfg c).state = c.state := rfl

/-- `retargetCfg` leaves the input tape unchanged. -/
@[simp] theorem retargetCfg_input (tm : TM n) (c : Cfg n tm.Q) :
    (tm.retargetCfg c).input = c.input := rfl

/-- `retargetCfg` maps the first `n` work tapes to `c`'s work tapes. -/
theorem retargetCfg_work_lt (tm : TM n) (c : Cfg n tm.Q)
    (i : Fin (n + 1)) (h : i.val < n) :
    (tm.retargetCfg c).work i = c.work ⟨i.val, h⟩ := dif_pos h

/-- `retargetCfg` maps the last work tape to `c`'s output tape. -/
theorem retargetCfg_work_last (tm : TM n) (c : Cfg n tm.Q) :
    (tm.retargetCfg c).work (Fin.last n) = c.output := dite_eq_right (Nat.lt_irrefl n)

/-- **Unified step commutation** for `retargetOutput`: if `C`'s real
    output tape is blank with head at cell 0 or 1, work tape `n` matches
    `c`'s output tape, and the rest of `C` matches `c`, then one step of
    `tm.retargetOutput` from `C` is one step of `tm` from `c`, embedded
    via `retargetCfg`. -/
private theorem retargetOutput_step_of_extras (tm : TM n) {c : Cfg n tm.Q}
    {C : Cfg (n + 1) tm.Q}
    (hs : C.state = c.state) (hi : C.input = c.input)
    (hw : ∀ (i : Fin (n + 1)) (h : i.val < n), C.work i = c.work ⟨i.val, h⟩)
    (hlast : C.work (Fin.last n) = c.output)
    (ho : C.output.cells = (Tape.init []).cells ∧ C.output.head ≤ 1) :
    (tm.retargetOutput).step C = (tm.step c).map tm.retargetCfg := by
  by_cases hh : c.state = tm.qhalt
  · -- both machines are halted
    have h1 : (tm.retargetOutput).step C = none := by
      simp only [step, hs, hh, show (tm.retargetOutput).qhalt = tm.qhalt from rfl,
        ↓reduceIte]
    have h2 : tm.step c = none := by
      simp only [step, hh, ↓reduceIte]
    rw [h1, h2]; rfl
  · cases hstep : tm.step c with
    | none => exact absurd hstep (by simp [step, hh])
    | some c' =>
      -- extract the explicit stepped configuration
      simp only [step, hh, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hinner : (fun i : Fin n => (C.work (Fin.castSucc i)).read)
          = fun i => (c.work i).read :=
        funext fun i => by rw [hw (Fin.castSucc i) i.isLt]; rfl
      have hvirt : (C.work (Fin.last n)).read = c.output.read := by rw [hlast]
      simp only [step, Option.map_some]
      dsimp only [retargetOutput, retargetCfg]
      rw [hs, hi, hinner, hvirt, ite_eq_right hh]
      refine congrArg some (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, ?_⟩)
      · funext i
        by_cases hik : i.val < n
        · rw [hw i hik, dif_pos hik, dif_pos hik, dif_pos hik]
        · have hi_last : i = Fin.last n := by
            apply Fin.ext
            have := i.isLt
            simp only [Fin.val_last]
            omega
          rw [dite_eq_right hik, dite_eq_right hik, dite_eq_right hik, hi_last, hlast]
      · exact dummy_writeAndMove C.output ho.1 ho.2

/-- **Step commutation** on embedded configurations: once the real output
    tape is parked, `tm.retargetOutput` steps exactly as `tm` does through
    `retargetCfg`. -/
theorem retargetOutput_step_retargetCfg (tm : TM n) (c : Cfg n tm.Q) :
    (tm.retargetOutput).step (tm.retargetCfg c) = (tm.step c).map tm.retargetCfg :=
  retargetOutput_step_of_extras tm rfl rfl (fun _ h => dif_pos h)
    (retargetCfg_work_last tm c)
    ⟨rfl, Nat.le_refl 1⟩

/-- The first step out of the retargeted initial configuration: the real
    output tape bounces off `▷` into the parked position while `tm`
    performs its own first step (work tape `n` mirrors `tm`'s output tape,
    which also starts at `Tape.init []`). -/
private theorem retargetOutput_step_initCfg (tm : TM n) (x : List Bool) :
    (tm.retargetOutput).step ((tm.retargetOutput).initCfg x)
      = (tm.step (tm.initCfg x)).map tm.retargetCfg :=
  retargetOutput_step_of_extras tm rfl rfl (fun _ _ => rfl) rfl
    ⟨rfl, Nat.zero_le 1⟩

/-- Multi-step commutation through `retargetCfg`. -/
private theorem retargetOutput_reachesIn_retargetCfg (tm : TM n) {t : ℕ}
    {c c' : Cfg n tm.Q} (h : tm.reachesIn t c c') :
    (tm.retargetOutput).reachesIn t (tm.retargetCfg c) (tm.retargetCfg c') := by
  induction h with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by rw [retargetOutput_step_retargetCfg, hstep]; rfl) ih

/-- Redirecting output to a fresh work tape preserves every exact run through
the canonical configuration embedding. -/
theorem retargetOutput_reachesIn_retargetCfg_frame (tm : TM n) {t : ℕ}
    {c c' : Cfg n tm.Q} (h : tm.reachesIn t c c') :
    (tm.retargetOutput).reachesIn t (tm.retargetCfg c) (tm.retargetCfg c') :=
  retargetOutput_reachesIn_retargetCfg tm h

/-- Multi-step simulation from the initial configuration: the retargeted
    run tracks `tm`'s run in the same number of steps, with work tape `n`
    holding `tm`'s output tape. -/
private theorem retargetOutput_reachesIn_init (tm : TM n) (x : List Bool)
    {t : ℕ} {c' : Cfg n tm.Q} (h : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (n + 1) tm.Q,
      (tm.retargetOutput).reachesIn t ((tm.retargetOutput).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.work (Fin.last n) = c'.output := by
  cases h with
  | zero => exact ⟨(tm.retargetOutput).initCfg x, .zero, rfl, rfl⟩
  | step hstep hrest =>
    exact ⟨tm.retargetCfg c',
      .step (by rw [retargetOutput_step_initCfg, hstep]; rfl)
        (retargetOutput_reachesIn_retargetCfg tm hrest),
      rfl, retargetCfg_work_last tm c'⟩

/-- A run of an output-retargeted machine leaves the virtual output on the
last work tape and keeps the real output blank with its head at cell zero or
one. A subsequent combinator transition therefore parks it at cell one. -/
theorem retargetOutput_reachesIn_init_boundary (tm : TM n) (x : List Bool)
    {t : ℕ} {c' : Cfg n tm.Q} (h : tm.reachesIn t (tm.initCfg x) c') :
    ∃ C' : Cfg (n + 1) tm.Q,
      (tm.retargetOutput).reachesIn t ((tm.retargetOutput).initCfg x) C' ∧
      C'.state = c'.state ∧ C'.work (Fin.last n) = c'.output ∧
      C'.output.cells = (Tape.init []).cells ∧ C'.output.head ≤ 1 := by
  cases h with
  | zero =>
      exact ⟨(tm.retargetOutput).initCfg x, .zero, rfl, rfl, rfl,
        Nat.zero_le 1⟩
  | step hstep hrest =>
      refine ⟨tm.retargetCfg c',
        .step (by rw [retargetOutput_step_initCfg, hstep]; rfl)
          (retargetOutput_reachesIn_retargetCfg tm hrest),
        rfl, retargetCfg_work_last tm c', rfl, le_rfl⟩

/-- **Output retargeting preserves computation, with the same time
    bound.** If `tm` computes `f` within time `T`, then `retargetOutput
    tm` halts within `T(|x|)` steps with `f x` written on work tape `n`
    (the `Fin.last n` tape). This is the form needed to compose "compute a
    clock value onto a work tape". -/
theorem retargetOutput_computesInTime (tm : TM n) {f : List Bool → List Bool}
    {T : ℕ → ℕ} (h : tm.ComputesInTime f T) (x : List Bool) :
    ∃ (c' : Cfg (n + 1) tm.Q) (t : ℕ), t ≤ T x.length ∧
      (tm.retargetOutput).reachesIn t ((tm.retargetOutput).initCfg x) c' ∧
      (tm.retargetOutput).halted c' ∧
      (c'.work (Fin.last n)).HasOutput (f x) := by
  obtain ⟨c₀, t, ht, hreach, hhalt, hout⟩ := h x
  obtain ⟨C', hR, hstate, hwork⟩ := retargetOutput_reachesIn_init tm x hreach
  refine ⟨C', t, ht, hR, ?_, ?_⟩
  · show C'.state = (tm.retargetOutput).qhalt
    rw [hstate]; exact hhalt
  · rw [hwork]; exact hout

/-- Output retargeting with the blank real-output frame exposed. This is the
form used by sequential function composition. -/
theorem retargetOutput_computesInTime_boundary (tm : TM n)
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (h : tm.ComputesInTime f T) (x : List Bool) :
    ∃ (c' : Cfg (n + 1) tm.Q) (t : ℕ), t ≤ T x.length ∧
      (tm.retargetOutput).reachesIn t ((tm.retargetOutput).initCfg x) c' ∧
      (tm.retargetOutput).halted c' ∧
      (c'.work (Fin.last n)).HasOutput (f x) ∧
      c'.output.cells = (Tape.init []).cells ∧ c'.output.head ≤ 1 := by
  obtain ⟨c₀, t, ht, hreach, hhalt, hout⟩ := h x
  obtain ⟨C', hR, hstate, hwork, houtCells, houtHead⟩ :=
    retargetOutput_reachesIn_init_boundary tm x hreach
  refine ⟨C', t, ht, hR, ?_, ?_, houtCells, houtHead⟩
  · show C'.state = (tm.retargetOutput).qhalt
    rw [hstate]
    exact hhalt
  · rw [hwork]
    exact hout

/-- Padding by unused work tapes preserves one-way output behavior. -/
theorem IsTransducer.liftTM {tm : TM n} (h : tm.IsTransducer) (m : ℕ) :
    (tm.liftTM m).IsTransducer := by
  intro q iHead wHeads oHead
  simpa only [liftTM] using h q iHead
    (fun i => wHeads (Fin.castAdd m i)) oHead

/-- Redirecting output to a work tape leaves the real output direction idle,
so the resulting machine is always a one-way-output transducer. -/
theorem retargetOutput_isTransducer (tm : TM n) :
    tm.retargetOutput.IsTransducer := by
  intro q iHead wHeads oHead
  simp only [retargetOutput]
  unfold idleDir
  split <;> decide

end TM

end Complexity
