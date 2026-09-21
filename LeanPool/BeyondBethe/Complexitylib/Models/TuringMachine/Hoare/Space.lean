/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space.Defs
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Hoare.Space.Internal

/-!
# Space-aware Hoare specifications

`TM.HoareSpace` states the all-reachable auxiliary-space invariant required by
`TM.ComputesInSpace`; `TM.HoareTimeSpace` pairs it with a terminating
time-bounded Hoare triple.
The public API includes structural rules, sequential composition, transducer
closure, and a fresh-start computation bridge.

## Main results

- `TM.HoareTimeSpace.consequence` — weaken/strengthen every contract component.
- `TM.HoareSpace.weaken_pre`, `TM.HoareSpace.mono` — structural space rules.
- `Cfg.WithinAuxSpace.reachesIn` — bound head growth along a concrete run.
- `TM.HoareTime.and_hoareSpace` — pair existing endpoint and safety proofs.
- `TM.HoareTime.toHoareTimeSpace` — derive all-reachable space from time and
  an initial head bound.
- `TM.seqTM_hoareTimeSpace` — compose two phases at one space budget.
- `TM.IsTransducer.seqTM` — sequential composition remains append-only.
- `TM.computesInSpace_of_hoareTimeSpace` — package per-input contracts.
-/


public section

namespace Complexity

namespace Cfg

/-- Enlarging the logical input region and work-space budget preserves an
auxiliary-space bound. -/
theorem WithinAuxSpace.mono {c : Cfg n Q}
    {inputLength inputLength' space space' : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    c.WithinAuxSpace inputLength' space' :=
  h.mono_internal hinput hspace

/-- The standard combinator phase transition moves input and work heads by at
most one, so one additional auxiliary-space cell covers the seam. -/
theorem WithinAuxSpace.transition {c : Cfg n Q}
    {inputLength space : ℕ} (h : c.WithinAuxSpace inputLength space) :
    ({ state := c.state,
       input := TM.transitionInput c.input,
       work := fun i => TM.transitionTape (c.work i),
       output := TM.transitionTape c.output } : Cfg n Q).WithinAuxSpace
      inputLength (space + 1) :=
  h.transition_internal

/-- A `time`-step run can increase every charged head position by at most
`time`, so adding that many cells preserves the auxiliary-space bound. -/
theorem WithinAuxSpace.reachesIn {tm : TM n}
    {c c' : Cfg n tm.Q} {time inputLength space : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hreach : tm.reachesIn time c c') :
    c'.WithinAuxSpace inputLength (space + time) :=
  h.reachesIn_internal hreach

end Cfg

namespace TM

variable {n : ℕ}

/-- Strengthening the precondition preserves an all-reachable space contract. -/
theorem HoareSpace.weaken_pre {tm : TM n}
    {pre pre' : TapePred n} {inputLength space : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareSpace pre' inputLength space :=
  h.weaken_pre_internal hpre

/-- Enlarging the logical input region and auxiliary-space budget preserves a
space contract. -/
theorem HoareSpace.mono {tm : TM n}
    {pre : TapePred n} {inputLength inputLength' space space' : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    tm.HoareSpace pre inputLength' space' :=
  h.mono_internal hinput hspace

/-- Pair an existing terminating Hoare proof with an all-reachable space
proof. This is the main entry point for upgrading established subroutine
contracts without reproving their endpoint behavior. -/
theorem HoareTime.and_hoareSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (htime : tm.HoareTime pre post time)
    (hspace : tm.HoareSpace pre inputLength space) :
    tm.HoareTimeSpace pre post time inputLength space :=
  ⟨htime, hspace⟩

/-- Upgrade a terminating time-bounded Hoare triple to an all-reachable
time-and-space contract. If every starting configuration fits in
`initialSpace`, then at most one additional cell per machine step gives the
uniform bound `initialSpace + time`. -/
theorem HoareTime.toHoareTimeSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength initialSpace : ℕ}
    (htime : tm.HoareTime pre post time)
    (hinitial : ∀ inp work out, pre inp work out →
      ({ state := tm.qstart, input := inp, work := work, output := out } :
        Cfg n tm.Q).WithinAuxSpace inputLength initialSpace) :
    tm.HoareTimeSpace pre post time inputLength (initialSpace + time) :=
  htime.toHoareTimeSpace_internal hinitial

/-- A time-and-space contract exposes its ordinary time-bounded Hoare triple. -/
theorem HoareTimeSpace.toHoareTime {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space) :
    tm.HoareTime pre post time :=
  h.1

/-- A time-and-space contract exposes its all-reachable space component. -/
theorem HoareTimeSpace.toHoareSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space) :
    tm.HoareSpace pre inputLength space :=
  h.2

/-- Consequence rule: strengthen the precondition, weaken the postcondition,
and enlarge any of the three numerical bounds. -/
theorem HoareTimeSpace.consequence {tm : TM n}
    {pre pre' post post' : TapePred n}
    {time time' inputLength inputLength' space space' : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (htime : time ≤ time') (hinput : inputLength ≤ inputLength')
    (hspace : space ≤ space') :
    tm.HoareTimeSpace pre' post' time' inputLength' space' :=
  h.consequence_internal hpre hpost htime hinput hspace

/-- Sequentially composing one-way-output machines preserves the transducer
discipline. -/
theorem IsTransducer.seqTM {tm₁ tm₂ : TM n}
    (h₁ : tm₁.IsTransducer) (h₂ : tm₂.IsTransducer) :
    (seqTM tm₁ tm₂).IsTransducer :=
  h₁.seqTM_internal h₂

/-- Sequential composition of time-and-space Hoare contracts. -/
theorem seqTM_hoareTimeSpace (tm₁ tm₂ : TM n)
    {pre mid mid' post : TapePred n}
    {b₁ b₂ inputLength space₁ space₂ : ℕ}
    (h₁ : tm₁.HoareTimeSpace pre mid b₁ inputLength space₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out))
    (h₂ : tm₂.HoareTimeSpace mid' post b₂ inputLength space₂) :
    (seqTM tm₁ tm₂).HoareTimeSpace pre post (b₁ + 1 + b₂)
      inputLength (max space₁ space₂) :=
  seqTM_hoareTimeSpace_internal tm₁ tm₂ h₁ htrans h₂

/-- Per-input fresh-start time-and-space contracts package a total function
transducer satisfying `TM.ComputesInSpace`. -/
theorem computesInSpace_of_hoareTimeSpace
    {tm : TM n} {f : List Bool → List Bool} {T S : ℕ → ℕ}
    (htrans : tm.IsTransducer)
    (h : ∀ x, tm.HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput (f x))
      (T x.length) x.length (S x.length)) :
    tm.ComputesInSpace f S :=
  computesInSpace_of_hoareTimeSpace_internal htrans h

end TM

end Complexity
