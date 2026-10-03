/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Binary work-tape loop combinator -- definitions

`TM.forBinaryWorkTM driverIdx body` invokes `body` once for each `0` or `1`
under a designated work-tape cursor and stops on the first blank. The body sees
the current bit; the loopback seam advances the driver by one cell. This is the
width-driven control needed by bitwise algorithms such as schoolbook
multiplication, without a numeric-value counter.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Scanner and terminal states outside the nested body machine. -/
inductive ForBinaryWorkPhase where
  | scan
  | done
  deriving DecidableEq

/-- `ForBinaryWorkPhase` has exactly two states. -/
instance instFintypeForBinaryWorkPhase : Fintype ForBinaryWorkPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- Iterate `body` over the Boolean cells of work tape `driverIdx`.

The scanner skips an initial left marker, halts on blank, and enters `body`
without moving on either Boolean symbol. When the body halts, one preserving
seam step advances only the driver and resumes scanning. Exact once-per-bit
semantics therefore requires the body to preserve the driver tape and head. -/
def forBinaryWorkTM {n : ℕ} (driverIdx : Fin n) (body : TM n) : TM n where
  Q := ForBinaryWorkPhase ⊕ body.Q
  qstart := .inl .scan
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .scan =>
        if wHeads driverIdx = Γ.start then
          (.inl .scan, fun i => readBackWrite (wHeads i),
            readBackWrite oHead, idleDir iHead,
            fun i => if i = driverIdx then Dir3.right
              else idleDir (wHeads i),
            idleDir oHead)
        else if wHeads driverIdx = Γ.blank then
          allReadBack (.inl .done) iHead wHeads oHead
        else
          allReadBack (.inr body.qstart) iHead wHeads oHead
    | .inl .done => allIdle (.inl .done) iHead wHeads oHead
    | .inr state =>
        if state = body.qhalt then
          (.inl .scan, fun i => readBackWrite (wHeads i),
            readBackWrite oHead, idleDir iHead,
            fun i => if i = driverIdx then Dir3.right
              else idleDir (wHeads i),
            idleDir oHead)
        else
          ((Sum.inr (body.δ state iHead wHeads oHead).1 :
              ForBinaryWorkPhase ⊕ body.Q),
            (body.δ state iHead wHeads oHead).2.1,
            (body.δ state iHead wHeads oHead).2.2.1,
            (body.δ state iHead wHeads oHead).2.2.2.1,
            (body.δ state iHead wHeads oHead).2.2.2.2.1,
            (body.δ state iHead wHeads oHead).2.2.2.2.2)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .inl .scan =>
        dsimp only
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          split
          · rfl
          · exact idleDir_right_of_start hi
        · split <;> exact rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
    | .inr state =>
        dsimp only
        split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hi
          simp only
          split
          · rfl
          · exact idleDir_right_of_start hi
        · exact body.δ_right_of_start state iHead wHeads oHead

/-- Exact remaining time for a bit-driven work loop. Each live iteration takes
one scanner step, the body run, and one advancing loopback step; the terminal
blank exit takes one step. -/
def forBinaryWorkLoopTime (bodyTime : ℕ → ℕ) (value : ℕ) : ℕ → ℕ
  | 0 => 1
  | count + 1 =>
      1 + bodyTime value + 1 +
        forBinaryWorkLoopTime bodyTime (value + 1) count

/-- Wrapper-free exact-control certificate for a binary work-tape loop. -/
structure ForBinaryWorkLoopSpec {n : ℕ} (driverIdx : Fin n) (body : TM n)
    (bodyTime : ℕ → ℕ) (total : ℕ) where
  /-- Canonical scanner configuration at iteration `value`. -/
  scanCfg : ℕ → Cfg n (forBinaryWorkTM driverIdx body).Q
  /-- Canonical combined-machine configuration at body entry. -/
  bodyStartCfg : ℕ → Cfg n (forBinaryWorkTM driverIdx body).Q
  /-- Canonical combined-machine configuration after the exact body run. -/
  bodyDoneCfg : ℕ → Cfg n (forBinaryWorkTM driverIdx body).Q
  /-- Canonical final driver configuration. -/
  doneCfg : Cfg n (forBinaryWorkTM driverIdx body).Q
  /-- One scanner step on a Boolean cell enters the body. -/
  scanStep : ∀ value, value < total →
    (forBinaryWorkTM driverIdx body).step (scanCfg value) =
      some (bodyStartCfg value)
  /-- The body has the advertised exact runtime. -/
  bodyRun : ∀ value, value < total →
    (forBinaryWorkTM driverIdx body).reachesIn (bodyTime value)
      (bodyStartCfg value) (bodyDoneCfg value)
  /-- The preserving loopback advances the driver to the next cell. -/
  loopbackStep : ∀ value, value < total →
    (forBinaryWorkTM driverIdx body).step (bodyDoneCfg value) =
      some (scanCfg (value + 1))
  /-- The scanner exits on the first blank. -/
  stopStep :
    (forBinaryWorkTM driverIdx body).step (scanCfg total) = some doneCfg

/-- Space obligations turning an exact binary-work loop certificate into an
all-prefix auxiliary-space certificate. -/
structure ForBinaryWorkLoopSpaceSpec {n : ℕ} {driverIdx : Fin n}
    {body : TM n} {bodyTime : ℕ → ℕ} {total : ℕ}
    (spec : ForBinaryWorkLoopSpec driverIdx body bodyTime total)
    (inputLength spaceBound : ℕ) where
  /-- Every canonical scanner configuration is within the space budget. -/
  scanWithin : ∀ value, value ≤ total →
    (spec.scanCfg value).WithinAuxSpace inputLength spaceBound
  /-- The canonical terminal configuration is within the space budget. -/
  doneWithin : spec.doneCfg.WithinAuxSpace inputLength spaceBound
  /-- Every prefix of each exact body run remains within the budget. -/
  bodyPrefixWithin : ∀ value t c, value < total → t ≤ bodyTime value →
    (forBinaryWorkTM driverIdx body).reachesIn t
      (spec.bodyStartCfg value) c →
    c.WithinAuxSpace inputLength spaceBound

end TM

end Complexity
