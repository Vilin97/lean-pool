/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Internal

/-!
# Hoare-style specifications for Turing machines

This file defines Hoare triples for reasoning about TM behavior in terms of
tape preconditions and postconditions. This provides a compositional framework
for building and verifying complex machines from simpler components.

## Main definitions

- `TapePred` — a predicate on the tape configuration (input, work, output)
- `TM.HoareTime` — time-bounded Hoare triple: `{pre} tm {post} [≤ bound]`
- `TM.Hoare` — unbounded Hoare triple: `{pre} tm {post}`

## Design notes

Hoare triples abstract away the internal state `Q`, reasoning purely about
tape contents and head positions. This makes them ideal for compositional
reasoning: the pre/postconditions of composed machines can be stated without
reference to the internal state types of the components.

The precondition must imply that the starting configuration has the machine's
`qstart` state. The postcondition holds at halting.
-/


@[expose] public section

namespace Complexity

/-- A predicate on the tape configuration: input tape, work tapes, output tape. -/
abbrev TapePred (n : ℕ) := Tape → (Fin n → Tape) → Tape → Prop

namespace TM

variable {n : ℕ}

@[inherit_doc Complexity.TapePred]
abbrev TapePred (n : ℕ) := Complexity.TapePred n

/-- **Time-bounded Hoare triple**: for any tapes satisfying `pre`, starting
    from `qstart`, the machine halts within `bound` steps with tapes satisfying
    `post`.

    This is the core specification type for compositional TM reasoning.
    Captures both correctness (pre/post) and efficiency (time bound). -/
def HoareTime (tm : TM n) (pre post : TapePred n) (bound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∃ c' t, t ≤ bound ∧
      tm.reachesIn t { state := tm.qstart, input := inp, work := work, output := out } c' ∧
      tm.halted c' ∧ post c'.input c'.work c'.output

/-- **Unbounded Hoare triple**: the machine halts with tapes satisfying `post`,
    without a time bound. Useful when only correctness matters. -/
def Hoare (tm : TM n) (pre post : TapePred n) : Prop :=
  ∀ inp work out, pre inp work out →
    ∃ c', tm.reaches { state := tm.qstart, input := inp, work := work, output := out } c' ∧
      tm.halted c' ∧ post c'.input c'.work c'.output

-- ════════════════════════════════════════════════════════════════════════
-- Structural rules
-- ════════════════════════════════════════════════════════════════════════

/-- **Consequence rule**: weaken the precondition and strengthen the postcondition. -/
theorem HoareTime.consequence {tm : TM n}
    {pre pre' post post' : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (hbound : b ≤ b') :
    tm.HoareTime pre' post' b' := by
  intro inp work out hpre'
  obtain ⟨c', t, ht, hreach, hhalt, hpost_c⟩ := h inp work out (hpre _ _ _ hpre')
  exact ⟨c', t, le_trans ht hbound, hreach, hhalt, hpost _ _ _ hpost_c⟩

/-- **Precondition weakening**: if `pre'` implies `pre`, lift the Hoare triple. -/
theorem HoareTime.weaken_pre {tm : TM n}
    {pre pre' post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareTime pre' post b :=
  h.consequence hpre (fun _ _ _ h => h) le_rfl

/-- **Postcondition strengthening**: if `post` implies `post'`, lift the triple. -/
theorem HoareTime.strengthen_post {tm : TM n}
    {pre post post' : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpost : ∀ inp work out, post inp work out → post' inp work out) :
    tm.HoareTime pre post' b :=
  h.consequence (fun _ _ _ h => h) hpost le_rfl

/-- **Time monotonicity**: increase the time bound. -/
theorem HoareTime.mono_bound {tm : TM n}
    {pre post : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b) (hle : b ≤ b') :
    tm.HoareTime pre post b' :=
  h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) hle

/-- Bounded implies unbounded. -/
theorem HoareTime.toHoare {tm : TM n}
    {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) :
    tm.Hoare pre post := by
  intro inp work out hpre
  obtain ⟨c', t, _, hreach, hhalt, hpost⟩ := h inp work out hpre
  exact ⟨c', TM.reaches_of_reachesIn hreach, hhalt, hpost⟩

-- ════════════════════════════════════════════════════════════════════════
-- Connection to DecidesInTime
-- ════════════════════════════════════════════════════════════════════════

/-- `DecidesInTime` implies a family of Hoare triples, one per input. -/
theorem hoareTime_of_decidesInTime {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (h : tm.DecidesInTime L T) (x : List Bool) :
    tm.HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
                           (work = fun _ => Tape.init []) ∧
                           out = Tape.init [])
      (fun _ _ out => (x ∈ L → out.cells 1 = Γ.one) ∧
                      (x ∉ L → out.cells 1 = Γ.zero))
      (T x.length) := by
  intro inp work out ⟨hinp, hwork, hout⟩
  subst hinp; subst hout; subst hwork
  obtain ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩ := h x
  exact ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩

end TM

namespace NTM

variable {n : ℕ}

@[inherit_doc Complexity.TapePred]
abbrev TapePred (n : ℕ) := Complexity.TapePred n

/-- Time-bounded Hoare triple for nondeterministic machines: every choice
    sequence of the given length reaches a halted configuration satisfying
    `post`. `NTM.trace` already keeps halted configurations fixed, so this
    also covers machines that halt earlier than the bound. -/
def HoareTime (tm : NTM n) (pre post : TapePred n) (bound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∀ choices : Fin bound → Bool,
      let c' := tm.trace bound choices
        { state := tm.qstart, input := inp, work := work, output := out }
      tm.halted c' ∧ post c'.input c'.work c'.output

/-- Consequence rule for NTM Hoare triples. -/
theorem HoareTime.consequence {tm : NTM n}
    {pre pre' post post' : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out) :
    tm.HoareTime pre' post' b := by
  intro inp work out hpre' choices
  exact (h inp work out (hpre _ _ _ hpre') choices).imp
    (fun hhalt => hhalt) (fun hp => hpost _ _ _ hp)

/-- Precondition weakening for NTM Hoare triples. -/
theorem HoareTime.weaken_pre {tm : NTM n}
    {pre pre' post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareTime pre' post b :=
  h.consequence hpre (fun _ _ _ h => h)

/-- Postcondition strengthening for NTM Hoare triples. -/
theorem HoareTime.strengthen_post {tm : NTM n}
    {pre post post' : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpost : ∀ inp work out, post inp work out → post' inp work out) :
    tm.HoareTime pre post' b :=
  h.consequence (fun _ _ _ h => h) hpost

/-- Time monotonicity for NTM Hoare triples. Since `NTM.trace` is fixed after
    halting, a proof for `b` steps also gives a proof for any larger bound. -/
theorem HoareTime.mono_bound {tm : NTM n}
    {pre post : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b) (hle : b ≤ b') :
    tm.HoareTime pre post b' := by
  intro inp work out hpre choices'
  let c0 : Cfg n tm.Q := { state := tm.qstart, input := inp, work := work, output := out }
  let choices : Fin b → Bool := fun i => choices' ⟨i.val, by omega⟩
  obtain ⟨hhalt, hpost⟩ := h inp work out hpre choices
  have heq := tm.trace_mono hle (choices := choices) (choices' := choices') (c := c0)
    (by intro i; rfl) hhalt
  constructor
  · change tm.halted (tm.trace b' choices' c0)
    rw [heq]
    exact hhalt
  · change post (tm.trace b' choices' c0).input (tm.trace b' choices' c0).work
      (tm.trace b' choices' c0).output
    rw [heq]
    exact hpost

/-- Consequence rule plus time-bound weakening for NTM Hoare triples. -/
theorem HoareTime.consequence_bound {tm : NTM n}
    {pre pre' post post' : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (hbound : b ≤ b') :
    tm.HoareTime pre' post' b' :=
  (h.consequence hpre hpost).mono_bound hbound

/-- If a finite NTM trace is halted at time `T`, then it has a least halted
    prefix time. This is useful for phase-composed machines: Hoare-time facts
    give halting by a fixed bound, while phase exits need the first local halt
    time. -/
theorem exists_first_halt_time_of_trace_halted (tm : NTM n) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg n tm.Q)
    (hhalt : tm.halted (tm.trace T choices c)) :
    ∃ t, ∃ ht : t ≤ T,
      tm.halted (tm.trace t (fun i => choices (Fin.castLE ht i)) c) ∧
      ∀ s, (hs : s < t) →
        ¬ tm.halted (tm.trace s
          (fun i => choices (Fin.castLE (le_trans (Nat.le_of_lt hs) ht) i)) c) := by
  classical
  let P : ℕ → Prop := fun t =>
    ∃ ht : t ≤ T, tm.halted (tm.trace t (fun i => choices (Fin.castLE ht i)) c)
  have hP : ∃ t, P t := by
    refine ⟨T, le_rfl, ?_⟩
    simpa using hhalt
  let t := Nat.find hP
  obtain ⟨ht, hhalt_t⟩ : P t := Nat.find_spec hP
  refine ⟨t, ht, hhalt_t, ?_⟩
  intro s hs hhalts
  have hsP : P s := by
    exact ⟨le_trans (Nat.le_of_lt hs) ht, hhalts⟩
  exact (Nat.find_min hP hs) hsP

/-- Hoare-time corollary of `exists_first_halt_time_of_trace_halted`: every
    all-path halting proof yields a least halting prefix for each fixed choice
    sequence. -/
theorem HoareTime.exists_first_halt_time {tm : NTM n}
    {pre post : TapePred n} {bound : ℕ}
    (h : tm.HoareTime pre post bound)
    {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (hpre : pre inp work out) (choices : Fin bound → Bool) :
    ∃ t, ∃ ht : t ≤ bound,
      tm.halted (tm.trace t (fun i => choices (Fin.castLE ht i))
        { state := tm.qstart, input := inp, work := work, output := out }) ∧
      ∀ s, (hs : s < t) →
        ¬ tm.halted (tm.trace s
          (fun i => choices (Fin.castLE (le_trans (Nat.le_of_lt hs) ht) i))
          { state := tm.qstart, input := inp, work := work, output := out }) := by
  have hhalt := (h inp work out hpre choices).1
  exact exists_first_halt_time_of_trace_halted tm bound choices
    { state := tm.qstart, input := inp, work := work, output := out } hhalt

/-- Hoare-time first-halt extraction, preserving the Hoare postcondition at the
    first halted prefix. -/
theorem HoareTime.exists_first_halt_time_with_post {tm : NTM n}
    {pre post : TapePred n} {bound : ℕ}
    (h : tm.HoareTime pre post bound)
    {inp : Tape} {work : Fin n → Tape} {out : Tape}
    (hpre : pre inp work out) (choices : Fin bound → Bool) :
    ∃ t, ∃ ht : t ≤ bound,
      let c0 : Cfg n tm.Q :=
        { state := tm.qstart, input := inp, work := work, output := out }
      tm.halted (tm.trace t (fun i => choices (Fin.castLE ht i)) c0) ∧
      post (tm.trace t (fun i => choices (Fin.castLE ht i)) c0).input
        (tm.trace t (fun i => choices (Fin.castLE ht i)) c0).work
        (tm.trace t (fun i => choices (Fin.castLE ht i)) c0).output ∧
      ∀ s, (hs : s < t) →
        ¬ tm.halted (tm.trace s
          (fun i => choices (Fin.castLE (le_trans (Nat.le_of_lt hs) ht) i)) c0) := by
  obtain ⟨t, ht, hhalt_t, hfirst⟩ :=
    h.exists_first_halt_time hpre choices
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · simpa using hhalt_t
  · let c0 : Cfg n tm.Q :=
      { state := tm.qstart, input := inp, work := work, output := out }
    let choicesT : Fin t → Bool := fun i => choices (Fin.castLE ht i)
    have hpost_bound := (h inp work out hpre choices).2
    have heq := tm.trace_mono ht (choices := choicesT) (choices' := choices)
      (c := c0) (by intro i; rfl) (by simpa [c0, choicesT] using hhalt_t)
    rw [heq] at hpost_bound
    simpa [c0, choicesT] using hpost_bound
  · intro s hs
    simpa using hfirst s hs

end NTM

namespace TM

variable {n : ℕ}

/-- A deterministic Hoare triple lifts to an NTM Hoare triple for `TM.toNTM`.
    The bound is unchanged because `toNTM` ignores the choice bit. -/
theorem HoareTime.toNTM {tm : TM n} {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) :
    tm.toNTM.HoareTime pre post b := by
  intro inp work out hpre choices
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp work out hpre
  have htrace := tm.toNTM_trace_of_reachesIn hreach hhalt ht choices
  constructor
  · change (tm.toNTM.trace b choices
      { state := tm.qstart, input := inp, work := work, output := out }).state = tm.qhalt
    exact htrace ▸ hhalt
  · change post
      (tm.toNTM.trace b choices
        { state := tm.qstart, input := inp, work := work, output := out }).input
      (tm.toNTM.trace b choices
        { state := tm.qstart, input := inp, work := work, output := out }).work
      (tm.toNTM.trace b choices
        { state := tm.qstart, input := inp, work := work, output := out }).output
    exact htrace ▸ hpost

end TM

end Complexity
