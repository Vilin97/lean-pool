/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Foundation

/-!
# V7 statement-layer foundations

This module contains transparent data carriers only.  It deliberately does
not import any historical O3 result or concrete O3 dispatcher.
-/

@[expose] public section

namespace V7

/-- The finite-dimensional real vector space used by the parameter-free method. -/
abbrev Point := O3.Point
/-- An oracle supplying objective values and gradients at query points. -/
abbrev PairOracle := O3.PairOracle
/-- A query point together with its observed value and gradient. -/
abbrev Observation := O3.Observation
/-- The coordinatewise real pairing of two vectors. -/
abbrev pairing {d : ℕ} (x y : Point d) : ℝ := O3.pairing x y
/-- The finite-dimensional real `ℓp` norm used in the method's bounds. -/
noncomputable abbrev lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := O3.lpNorm p x
/-- The Hölder-conjugate exponent `p / (p - 1)`. -/
noncomputable abbrev conjugateExponent (p : ℝ) : ℝ := O3.conjugateExponent p

/-- The primitive numerical input of the positive secant model. -/
structure MethodInput (d : ℕ) where
  /-- The exponent of the norm used by the method. -/
  p : ℝ
  /-- The requested gradient accuracy. -/
  eps : ℝ
  /-- The initial optimization point. -/
  x0 : Point d
  /-- The second point of the supplied nondegenerate secant pair. -/
  z0 : Point d
  /-- The initial smoothness estimate. -/
  M0 : ℝ

/-- Chronological post-initialization result data. -/
structure PairRunResult (d : ℕ) where
  /-- The point returned after the method finishes. -/
  returned : Point d
  /-- The chronological observations made after initialization. -/
  trace : List (Observation d)

/-- The number of oracle calls recorded after initialization. -/
def PairRunResult.postInitializationCallCount (run : PairRunResult d) : ℕ :=
  run.trace.length

/-- Every trace entry equals the exact oracle observation at its recorded point. -/
def TraceExact (oracle : PairOracle d) (trace : List (Observation d)) : Prop :=
  ∀ obs ∈ trace, obs = oracle.observe obs.point

/-- The point occurs among the recorded oracle queries. -/
def WasQueried (trace : List (Observation d)) (x : Point d) : Prop :=
  ∃ obs ∈ trace, obs.point = x

/-- The point was queried at the specified chronological trace index. -/
def QueriedAt (trace : List (Observation d)) (k : ℕ) (x : Point d) : Prop :=
  ∃ obs, (trace.drop k).head? = some obs ∧ obs.point = x

/-- The returned point occurs in the run's query trace. -/
def PairRunResult.returnedWasQueried (run : PairRunResult d) : Prop :=
  WasQueried run.trace run.returned

/-- The numerical input viewed in the underlying causal machine interface. -/
def MethodInput.toO3 (input : MethodInput d) : O3.MethodInput d :=
  ⟨input.p, input.eps, input.x0, input.z0, input.M0⟩

/-- A single causal machine family selected before `p`, dimension, or
instance data.  Objective information reaches it only through `query`. -/
abbrev RuntimeMethodFamily := (d : ℕ) → O3.FirstOrderMethod d

/-- A finite-fuel execution of the underlying method produces the specified result and trace. -/
def Executes (method : O3.FirstOrderMethod d) (input : MethodInput d)
    (oracle : PairOracle d) (run : PairRunResult d) : Prop :=
  ∃ (fuel : ℕ) (oldRun : O3.RunResult d),
    method.run oracle input.toO3 fuel = some oldRun ∧
    run.returned = oldRun.returned ∧ run.trace = oldRun.queries

/-- A supplied nondegenerate secant relation; discovery is outside the count. -/
def SecantInitialization (input : MethodInput d) (oracle : PairOracle d) : Prop :=
  input.z0 ≠ input.x0 ∧
  oracle.gradient input.z0 ≠ oracle.gradient input.x0 ∧
  input.M0 =
    lpNorm (conjugateExponent input.p)
      (oracle.gradient input.z0 - oracle.gradient input.x0) /
      lpNorm input.p (input.z0 - input.x0) ∧
  0 < input.M0

end V7
