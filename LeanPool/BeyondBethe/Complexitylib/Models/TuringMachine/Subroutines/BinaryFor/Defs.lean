/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Canonical binary count-up loops — definitions

This module defines an output-safe loop driver for a body indexed by a
canonical little-endian binary counter. A second, distinct work tape stores a
preserved limit. Before each iteration, the driver compares the two tapes in
lockstep, remembers whether every scanned symbol agreed, and rewinds both
heads to cell one. Equality halts the loop; inequality runs the body and then
increments the counter with `TM.binarySuccTM`.

The comparison deliberately scans through the full limit width even after a
mismatch. Under the intended invariant `counter ≤ limit`, this gives the
value-independent exact comparison time `2 * limit.size + 2`. The controller
never moves the output head left and does not alter its contents; output
behavior during an iteration is entirely delegated to the body.

The wrapper-free certificate structures at the end of the file separate the
executable controller from later correctness and all-prefix space proofs.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Controller phases for a canonical binary count-up loop.

The Boolean carried by `scan` and `rewind` records whether the counter and
limit symbols seen so far were equal. -/
inductive BinaryForPhase where
  | scan (equalSoFar : Bool)
  | rewind (equalSoFar : Bool)
  | done
  deriving DecidableEq

/-- `BinaryForPhase` is finite, as required by the concrete machine model. -/
instance instFintypeBinaryForPhase : Fintype BinaryForPhase where
  elems := {.scan false, .scan true, .rewind false, .rewind true, .done}
  complete := by
    intro phase
    cases phase with
    | scan equalSoFar => cases equalSoFar <;> simp
    | rewind equalSoFar => cases equalSoFar <;> simp
    | done => simp

/-- One count-up iteration: run `body`, take the `seqTM` seam, and increment
the designated canonical binary counter. -/
def binaryForIterationTM {n : ℕ} (body : TM n) (counterIdx : Fin n) : TM n :=
  seqTM body (binarySuccTM counterIdx)

/-- Count upward from a canonical binary counter to a preserved canonical
binary limit.

The intended correctness interface assumes `counterIdx ≠ limitIdx`. In the
driver phases both work heads move in lockstep. A complete scan records tape
equality without writing a verdict, and a complete rewind either halts or
enters `binaryForIterationTM body counterIdx`. When that composite iteration
halts, one content-preserving seam returns to a fresh equality scan.

Input, unrelated work tapes, and output use read-back/idle actions throughout
the controller. In particular, the driver itself is compatible with
append-only output; any output writes come only from `body`. -/
def binaryForTM {n : ℕ} (body : TM n) (counterIdx limitIdx : Fin n) : TM n :=
  let iteration := binaryForIterationTM body counterIdx
  haveI : Fintype iteration.Q := iteration.finQ
  haveI : DecidableEq iteration.Q := iteration.decEq
  { Q := BinaryForPhase ⊕ iteration.Q
    qstart := .inl (.scan true)
    qhalt := .inl .done
    δ := fun state iHead wHeads oHead =>
      match state with
      | .inl (.scan equalSoFar) =>
          if wHeads counterIdx = Γ.blank ∧ wHeads limitIdx = Γ.blank then
            (.inl (.rewind equalSoFar),
              fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i =>
                if i = counterIdx then Dir3.left
                else if i = limitIdx then Dir3.left
                else idleDir (wHeads i),
              idleDir oHead)
          else
            let equal' :=
              equalSoFar && decide (wHeads counterIdx = wHeads limitIdx)
            (.inl (.scan equal'),
              fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i =>
                if i = counterIdx then Dir3.right
                else if i = limitIdx then Dir3.right
                else idleDir (wHeads i),
              idleDir oHead)
      | .inl (.rewind equalSoFar) =>
          if wHeads counterIdx = Γ.start ∧ wHeads limitIdx = Γ.start then
            let nextState : BinaryForPhase ⊕ iteration.Q :=
              if equalSoFar then .inl .done else .inr iteration.qstart
            (nextState,
              fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i =>
                if i = counterIdx then Dir3.right
                else if i = limitIdx then Dir3.right
                else idleDir (wHeads i),
              idleDir oHead)
          else
            (.inl (.rewind equalSoFar),
              fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead,
              fun i =>
                if i = counterIdx then moveLeftDir (wHeads i)
                else if i = limitIdx then moveLeftDir (wHeads i)
                else idleDir (wHeads i),
              idleDir oHead)
      | .inl .done => allIdle (.inl .done) iHead wHeads oHead
      | .inr q =>
          if q = iteration.qhalt then
            allReadBack (.inl (.scan true)) iHead wHeads oHead
          else
            let (q', workWrite, outputWrite, inputDir, workDir, outputDir) :=
              iteration.δ q iHead wHeads oHead
            (.inr q', workWrite, outputWrite, inputDir, workDir, outputDir)
    δ_right_of_start := by
      intro state iHead wHeads oHead
      match state with
      | .inl (.scan equalSoFar) =>
          dsimp only
          split
          · next hblank =>
            refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            dsimp only
            by_cases hic : i = counterIdx
            · subst i
              rw [hblank.1] at hi
              exact absurd hi (by decide)
            · rw [if_neg hic]
              by_cases hil : i = limitIdx
              · subst i
                rw [hblank.2] at hi
                exact absurd hi (by decide)
              · rw [if_neg hil]
                exact idleDir_right_of_start hi
          · refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            dsimp only
            by_cases hic : i = counterIdx
            · rw [if_pos hic]
            · rw [if_neg hic]
              by_cases hil : i = limitIdx
              · rw [if_pos hil]
              · rw [if_neg hil]
                exact idleDir_right_of_start hi
      | .inl (.rewind equalSoFar) =>
          dsimp only
          split
          · refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            dsimp only
            by_cases hic : i = counterIdx
            · rw [if_pos hic]
            · rw [if_neg hic]
              by_cases hil : i = limitIdx
              · rw [if_pos hil]
              · rw [if_neg hil]
                exact idleDir_right_of_start hi
          · refine ⟨idleDir_right_of_start, fun i hi => ?_,
              idleDir_right_of_start⟩
            dsimp only
            by_cases hic : i = counterIdx
            · rw [if_pos hic]
              exact moveLeftDir_right_of_start hi
            · rw [if_neg hic]
              by_cases hil : i = limitIdx
              · rw [if_pos hil]
                exact moveLeftDir_right_of_start hi
              · rw [if_neg hil]
                exact idleDir_right_of_start hi
      | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
      | .inr q =>
          dsimp only
          split
          · exact rightOfStart_allReadBack iHead wHeads oHead
          · exact iteration.δ_right_of_start q iHead wHeads oHead }

/-- Exact time for one full-width equality scan and synchronized rewind when
the counter is bounded by `limit`. -/
def binaryForCompareTime (limit : ℕ) : ℕ :=
  2 * limit.size + 2

/-- Exact time of the composite iteration before the outer loopback seam:
the body run, one `seqTM` transition, and canonical binary successor. -/
def binaryForIterationTime (bodyTime : ℕ → ℕ) (value : ℕ) : ℕ :=
  bodyTime value + 1 + binarySuccTime value

/-- Exact remaining count-up-loop time.

`value` is the current counter and `count` is the number of nonterminal
iterations remaining. The zero case performs the final successful comparison.
Each successor case performs one unsuccessful comparison, one composite
iteration, one outer loopback seam, and the remaining loop. Intended uses
supply `value + count = limit`. -/
def binaryForLoopTime (bodyTime : ℕ → ℕ) (limit value : ℕ) : ℕ → ℕ
  | 0 => binaryForCompareTime limit
  | count + 1 =>
      binaryForCompareTime limit + binaryForIterationTime bodyTime value + 1 +
        binaryForLoopTime bodyTime limit (value + 1) count

/-- Wrapper-free certificate for exact control flow of a canonical binary
count-up loop.

All configurations use the public state type of
`binaryForTM body counterIdx limitIdx`. The client supplies the intended
canonical configuration family and proves that a nonterminal test reaches the
composite iteration, which runs the body and successor before one loopback
step advances to the next scanner configuration. At `limitValue`, the client
supplies the final comparison run. -/
structure BinaryForLoopSpec {n : ℕ} (body : TM n)
    (counterIdx limitIdx : Fin n) (bodyTime : ℕ → ℕ)
    (limitValue : ℕ) where
  /-- The counter and preserved-limit tapes are distinct. -/
  counter_ne_limit : counterIdx ≠ limitIdx
  /-- Client-supplied canonical combined-machine configuration before testing
  `value`. -/
  scanCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Client-supplied canonical configuration at the composite iteration start. -/
  iterationStartCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Client-supplied canonical configuration after the exact composite iteration. -/
  iterationDoneCfg : ℕ → Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- Client-supplied canonical final driver configuration. -/
  doneCfg : Cfg n (binaryForTM body counterIdx limitIdx).Q
  /-- A nonterminal comparison and rewind enter the composite iteration. -/
  testRun : ∀ value, value < limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue) (scanCfg value)
      (iterationStartCfg value)
  /-- The body, `seqTM` seam, and successor have the advertised exact runtime. -/
  iterationRun : ∀ value, value < limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForIterationTime bodyTime value) (iterationStartCfg value)
      (iterationDoneCfg value)
  /-- The preserving outer seam returns to the next comparison. -/
  loopbackStep : ∀ value, value < limitValue →
    (binaryForTM body counterIdx limitIdx).step (iterationDoneCfg value) =
      some (scanCfg (value + 1))
  /-- Equality at the limit completes one final comparison and rewind. -/
  doneRun :
    (binaryForTM body counterIdx limitIdx).reachesIn
      (binaryForCompareTime limitValue) (scanCfg limitValue) doneCfg

/-- All-prefix auxiliary-space obligations for a certified binary count-up
loop. The comparison and composite-iteration obligations concern prefixes of
their advertised exact runs; later execution may already have crossed the
corresponding seam. -/
structure BinaryForLoopSpaceSpec {n : ℕ} {body : TM n}
    {counterIdx limitIdx : Fin n} {bodyTime : ℕ → ℕ}
    {limitValue : ℕ}
    (spec : BinaryForLoopSpec body counterIdx limitIdx bodyTime limitValue)
    (inputLength spaceBound : ℕ) where
  /-- Every prefix of each full-width comparison and rewind respects the budget. -/
  testPrefixWithin : ∀ value time cfg, value ≤ limitValue →
    time ≤ binaryForCompareTime limitValue →
    (binaryForTM body counterIdx limitIdx).reachesIn time
      (spec.scanCfg value) cfg →
    cfg.WithinAuxSpace inputLength spaceBound
  /-- Every prefix of each body-plus-successor iteration respects the budget. -/
  iterationPrefixWithin : ∀ value time cfg, value < limitValue →
    time ≤ binaryForIterationTime bodyTime value →
    (binaryForTM body counterIdx limitIdx).reachesIn time
      (spec.iterationStartCfg value) cfg →
    cfg.WithinAuxSpace inputLength spaceBound

end TM

end Complexity
