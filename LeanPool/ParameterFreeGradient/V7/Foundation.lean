/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Foundation

/-!
# V7 statement-layer foundations

This module contains transparent data carriers only.  It deliberately does
not import any historical O3 result or concrete O3 dispatcher.
-/

namespace V7

abbrev Point := O3.Point
abbrev PairOracle := O3.PairOracle
abbrev Observation := O3.Observation
abbrev pairing {d : ℕ} (x y : Point d) : ℝ := O3.pairing x y
noncomputable abbrev lpNorm (p : ℝ) {d : ℕ} (x : Point d) : ℝ := O3.lpNorm p x
noncomputable abbrev conjugateExponent (p : ℝ) : ℝ := O3.conjugateExponent p

/-- The primitive numerical input of the positive secant model. -/
structure MethodInput (d : ℕ) where
  p : ℝ
  eps : ℝ
  x0 : Point d
  z0 : Point d
  M0 : ℝ

/-- Chronological post-initialization result data. -/
structure PairRunResult (d : ℕ) where
  returned : Point d
  trace : List (Observation d)

def PairRunResult.postInitializationCallCount (run : PairRunResult d) : ℕ :=
  run.trace.length

def TraceExact (oracle : PairOracle d) (trace : List (Observation d)) : Prop :=
  ∀ obs ∈ trace, obs = oracle.observe obs.point

def WasQueried (trace : List (Observation d)) (x : Point d) : Prop :=
  ∃ obs ∈ trace, obs.point = x

def QueriedAt (trace : List (Observation d)) (k : ℕ) (x : Point d) : Prop :=
  ∃ obs, (trace.drop k).head? = some obs ∧ obs.point = x

def PairRunResult.returnedWasQueried (run : PairRunResult d) : Prop :=
  WasQueried run.trace run.returned

def MethodInput.toO3 (input : MethodInput d) : O3.MethodInput d :=
  ⟨input.p, input.eps, input.x0, input.z0, input.M0⟩

/-- A single causal machine family selected before `p`, dimension, or
instance data.  Objective information reaches it only through `query`. -/
abbrev RuntimeMethodFamily := (d : ℕ) → O3.FirstOrderMethod d

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
