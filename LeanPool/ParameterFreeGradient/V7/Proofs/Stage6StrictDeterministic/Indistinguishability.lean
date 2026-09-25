/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.HardInstance

/-!
Finite affine transcripts are indistinguishable from a sufficiently distant hard-family
instance.
-/

@[expose] public section

namespace V7.Stage6StrictDeterministic

/-- On the whole pre-transition half-line, both exact oracle fields coincide. -/
theorem hard_affine_observation_eq {eps H : ℝ} (x0 : StrictPoint)
    (x : StrictPoint) (hx : x 0 - x0 0 < H) :
    (hardOracle eps x0 H).observe x = (strictAffineOracle eps x0).observe x := by
  unfold O3.PairOracle.observe
  congr 1
  · simp [hardOracle, strictHardFamily, strictAffineOracle, hx.le]
  · funext i
    fin_cases i
    simp [hardOracle, strictHardDerivative, strictAffineOracle, hx.le]

/-- Exact transcript coupling: exactness is transported observation by
observation, while the causal prefix/query equations are literally unchanged. -/
theorem hard_runConsistent_of_affine {method : StrictLocalMethod} {eps H : ℝ}
    {trace : StrictTranscript}
    (haffine : StrictRunConsistent method (strictAffineOracle eps method.x0) trace)
    (hleft : ∀ obs ∈ trace, obs.point 0 - method.x0 0 < H) :
    StrictRunConsistent method (hardOracle eps method.x0 H) trace := by
  constructor
  · intro obs hobs
    calc
      obs = (strictAffineOracle eps method.x0).observe obs.point := haffine.1 obs hobs
      _ = (hardOracle eps method.x0 H).observe obs.point :=
        (hard_affine_observation_eq method.x0 obs.point (hleft obs hobs)).symm
  · exact haffine.2

theorem all_queries_fail_of_left {eps H : ℝ} (heps : 0 < eps)
    (x0 : StrictPoint) {trace : StrictTranscript} {N : ℕ}
    (hlen : trace.length = N)
    (hleft : ∀ obs ∈ trace, obs.point 0 - x0 0 < H) :
    StrictAllFirstNQueriesFail eps (hardOracle eps x0 H) trace N := by
  refine ⟨hlen, ?_⟩
  intro obs hobs
  have hz := hleft obs hobs
  change eps < |hardSlope eps H (obs.point 0 - x0 0)|
  rw [hardSlope_of_le hz.le, abs_neg, abs_of_pos (by linarith : 0 < 2 * eps)]
  linarith

theorem finite_output_fails_of_left {method : StrictLocalMethod} {eps H : ℝ}
    (heps : 0 < eps) (heq : method.eps = eps)
    (trace : StrictTranscript) (N : ℕ)
    (hleft : method.output N trace 0 - method.x0 0 < H) :
    StrictFiniteOutputFails method (hardOracle eps method.x0 H) trace N := by
  change method.eps < |hardSlope eps H
    (method.output N trace 0 - method.x0 0)|
  rw [heq, hardSlope_of_le hleft.le, abs_neg,
    abs_of_pos (by linarith : 0 < 2 * eps)]
  linarith

end V7.Stage6StrictDeterministic
