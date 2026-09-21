/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# One-prefix work-tape loop combinator — definitions

`TM.forWorkOnesTM driverIdx body` scans a work tape from left to right and
invokes `body` once for each consecutive `1` symbol. The driver advances before
each invocation and halts with its head on the first non-`1` symbol. This is the
machine-level control needed to consume the unary-width prefix of a
self-delimiting binary word without materializing the prefix elsewhere.

Exact iteration semantics require `body` to preserve the already-advanced
driver tape and head. The combinator itself is a concrete `TM`; loop
certificates and proofs live in the adjacent internal and surface modules.
-/


@[expose] public section

namespace Complexity

namespace TM

/-- Driver states for a consecutive-one work-tape loop. -/
inductive ForWorkOnesPhase where
  | scan
  | done
  deriving DecidableEq

/-- `ForWorkOnesPhase` has exactly two states. -/
instance instFintypeForWorkOnesPhase : Fintype ForWorkOnesPhase where
  elems := {.scan, .done}
  complete := fun phase => by cases phase <;> simp

/-- Advance over one `1` on work tape `driverIdx` and invoke `body`; halt on
the first non-`1` symbol. An initial left marker is skipped safely. -/
def forWorkOnesTM {n : ℕ} (driverIdx : Fin n) (body : TM n) : TM n where
  Q := ForWorkOnesPhase ⊕ body.Q
  qstart := .inl .scan
  qhalt := .inl .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .inl .scan =>
        if wHeads driverIdx = Γ.start then
          (.inl .scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = driverIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else if wHeads driverIdx = Γ.one then
          (.inr body.qstart, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead,
            fun i => if i = driverIdx then Dir3.right else idleDir (wHeads i),
            idleDir oHead)
        else
          allReadBack (.inl .done) iHead wHeads oHead
    | .inl .done => allIdle (.inl .done) iHead wHeads oHead
    | .inr state =>
        if state = body.qhalt then
          allReadBack (.inl .scan) iHead wHeads oHead
        else
          ((Sum.inr (body.δ state iHead wHeads oHead).1 :
              ForWorkOnesPhase ⊕ body.Q),
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
          intro i hwi
          simp only
          split
          · rfl
          · exact idleDir_right_of_start hwi
        · split
          · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
            intro i hwi
            simp only
            split
            · rfl
            · exact idleDir_right_of_start hwi
          · exact rightOfStart_allReadBack iHead wHeads oHead
    | .inl .done => exact rightOfStart_allIdle iHead wHeads oHead
    | .inr state =>
        dsimp only
        split
        · exact rightOfStart_allReadBack iHead wHeads oHead
        · exact body.δ_right_of_start state iHead wHeads oHead

/-- Exact remaining time for a one-prefix loop whose body takes
`bodyTime value` steps on iteration `value`. The terminal non-one exit takes
one step. -/
def forWorkOnesLoopTime (bodyTime : ℕ → ℕ) (value : ℕ) : ℕ → ℕ
  | 0 => 1
  | count + 1 =>
      1 + bodyTime value + 1 + forWorkOnesLoopTime bodyTime (value + 1) count

/-- Wrapper-free exact-control certificate for a consecutive-one work loop. -/
structure ForWorkOnesLoopSpec {n : ℕ} (driverIdx : Fin n) (body : TM n)
    (bodyTime : ℕ → ℕ) (total : ℕ) where
  /-- Canonical scanner configuration at iteration `value`. -/
  scanCfg : ℕ → Cfg n (forWorkOnesTM driverIdx body).Q
  /-- Canonical combined-machine configuration at body entry. -/
  bodyStartCfg : ℕ → Cfg n (forWorkOnesTM driverIdx body).Q
  /-- Canonical combined-machine configuration after the exact body run. -/
  bodyDoneCfg : ℕ → Cfg n (forWorkOnesTM driverIdx body).Q
  /-- Canonical final driver configuration. -/
  doneCfg : Cfg n (forWorkOnesTM driverIdx body).Q
  /-- One scanner step consumes a `1` and enters the body. -/
  scanStep : ∀ value, value < total →
    (forWorkOnesTM driverIdx body).step (scanCfg value) =
      some (bodyStartCfg value)
  /-- The body has the advertised exact runtime. -/
  bodyRun : ∀ value, value < total →
    (forWorkOnesTM driverIdx body).reachesIn (bodyTime value)
      (bodyStartCfg value) (bodyDoneCfg value)
  /-- The preserving seam returns to the scanner. -/
  loopbackStep : ∀ value, value < total →
    (forWorkOnesTM driverIdx body).step (bodyDoneCfg value) =
      some (scanCfg (value + 1))
  /-- The scanner exits on the first non-`1` symbol. -/
  stopStep :
    (forWorkOnesTM driverIdx body).step (scanCfg total) = some doneCfg

end TM

end Complexity
