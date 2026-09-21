/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Read-only-input loop combinator — definitions

`TM.forInputTM body` scans the Boolean input from left to right and invokes
`body` after each bit. When `body` preserves the input tape, this is exactly one
invocation per original input bit. The input itself is the loop fuel, so the
combinator does not materialize a linear-size unary counter on an auxiliary tape.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Driver states for the read-only-input loop. -/
inductive ForInputPhase where
  | scan
  | done
  deriving DecidableEq

/-- `ForInputPhase` has exactly two states. -/
instance instFintypeForInputPhase : Fintype ForInputPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- Advance over a Boolean input symbol and run `body`.

The driver skips an initial left-end marker, advances the read-only input by
one cell before each body invocation, and halts whenever scanning encounters a
blank. Work and output tapes take the structurally safe read-back/idle action in
driver states. Nonhalting body transitions are embedded exactly, so the usual
once-per-original-symbol behavior requires the body to preserve the input tape. -/
def forInputTM {n : ℕ} (body : TM n) : TM n where
  Q := ForInputPhase ⊕ body.Q
  qstart := .inl .scan
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .scan =>
        if iHead = Γ.start then
          (.inl .scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        else if iHead = Γ.blank then
          allReadBack (.inl .done) iHead wHeads oHead
        else
          (.inr body.qstart, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .inl .done => allIdle (.inl .done) iHead wHeads oHead
    | .inr q =>
        if q = body.qhalt then
          allReadBack (.inl .scan) iHead wHeads oHead
        else
          ((Sum.inr (body.δ q iHead wHeads oHead).1 : ForInputPhase ⊕ body.Q),
            (body.δ q iHead wHeads oHead).2.1,
            (body.δ q iHead wHeads oHead).2.2.1,
            (body.δ q iHead wHeads oHead).2.2.2.1,
            (body.δ q iHead wHeads oHead).2.2.2.2.1,
            (body.δ q iHead wHeads oHead).2.2.2.2.2)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .scan =>
        dsimp only
        split
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · split
          · exact rightOfStart_allReadBack iHead wHeads oHead
          · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
              idleDir_right_of_start⟩
    | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
    | .inr q =>
        dsimp only
        split
        · exact rightOfStart_allReadBack iHead wHeads oHead
        · exact body.δ_right_of_start q iHead wHeads oHead

/-- Exact remaining time for an input-driven loop whose body takes
`bodyTime value` steps on iteration `value`. The terminal input-blank exit
takes one step. Each nonterminal iteration takes one scanner step, the body
run, and one loopback step. -/
def forInputLoopTime (bodyTime : ℕ → ℕ) (value : ℕ) : ℕ → ℕ
  | 0 => 1
  | count + 1 =>
      1 + bodyTime value + 1 + forInputLoopTime bodyTime (value + 1) count

/-- Wrapper-free certificate for the exact control flow of an input-driven
loop. All configurations use the public state type of `forInputTM body`, so
clients need not mention the internal body-state embedding.

`total` is the first scanner index whose input symbol is blank. -/
structure ForInputLoopSpec {n : ℕ} (body : TM n) (bodyTime : ℕ → ℕ)
    (total : ℕ) where
  /-- Canonical scanner configuration at iteration `value`. -/
  scanCfg : ℕ → Cfg n (forInputTM body).Q
  /-- Canonical combined-machine configuration at the start of the body. -/
  bodyStartCfg : ℕ → Cfg n (forInputTM body).Q
  /-- Canonical combined-machine configuration after the exact body run. -/
  bodyDoneCfg : ℕ → Cfg n (forInputTM body).Q
  /-- Canonical final driver configuration. -/
  doneCfg : Cfg n (forInputTM body).Q
  /-- A nonterminal scanner step enters the body. -/
  scanStep : ∀ value, value < total →
    (forInputTM body).step (scanCfg value) = some (bodyStartCfg value)
  /-- The body has the advertised exact runtime. -/
  bodyRun : ∀ value, value < total →
    (forInputTM body).reachesIn (bodyTime value)
      (bodyStartCfg value) (bodyDoneCfg value)
  /-- The preserving seam step advances to the next scanner configuration. -/
  loopbackStep : ∀ value, value < total →
    (forInputTM body).step (bodyDoneCfg value) = some (scanCfg (value + 1))
  /-- The scanner exits on the first blank. -/
  blankStep :
    (forInputTM body).step (scanCfg total) = some doneCfg

/-- Space obligations needed to turn a `ForInputLoopSpec` into an
all-prefix auxiliary-space certificate. The body obligation concerns only
prefixes of its advertised exact run; later combined-machine execution may
already have crossed the loopback seam. -/
structure ForInputLoopSpaceSpec {n : ℕ} {body : TM n} {bodyTime : ℕ → ℕ}
    {total : ℕ} (spec : ForInputLoopSpec body bodyTime total)
    (inputLength spaceBound : ℕ) where
  /-- Every canonical scanner configuration is within the space budget. -/
  scanWithin : ∀ value, value ≤ total →
    (spec.scanCfg value).WithinAuxSpace inputLength spaceBound
  /-- The canonical final configuration is within the space budget. -/
  doneWithin : spec.doneCfg.WithinAuxSpace inputLength spaceBound
  /-- Every prefix of each exact body run is within the space budget. -/
  bodyPrefixWithin : ∀ value t c, value < total → t ≤ bodyTime value →
    (forInputTM body).reachesIn t (spec.bodyStartCfg value) c →
    c.WithinAuxSpace inputLength spaceBound

end TM

end Complexity
