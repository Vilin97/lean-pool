/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage6StrictDeterministic.Indistinguishability

namespace V7

open Stage6StrictDeterministic

/-- U04--U07, with the hard transition and instance selected only after the
complete affine transcript and its finite output are fixed. -/
theorem deterministicFiniteHorizonImpossibility :
    DeterministicFiniteHorizonImpossibilityStatement := by
  intro p eps hp heps method heq N hN
  let trace : StrictTranscript := affineTrace method eps N
  have hlen : trace.length = N := by
    dsimp [trace]
    exact affineTrace_length method eps N
  have haffine : StrictRunConsistent method (strictAffineOracle eps method.x0) trace := by
    dsimp [trace]
    exact affineTrace_runConsistent method eps N
  refine ⟨trace, hlen, haffine, ?_⟩
  let H : ℝ := postTranscriptH method N trace
  have hH : 0 < H := postTranscriptH_pos method N trace
  have htrace : ∀ obs ∈ trace, obs.point 0 - method.x0 0 < H :=
    trace_displacement_lt_postTranscriptH method N trace
  have houtput : method.output N trace 0 - method.x0 0 < H :=
    output_displacement_lt_postTranscriptH method N trace
  refine ⟨H, (2 * eps) / H, 2 * H, hardOracle eps method.x0 H,
    hardMinimizer method.x0 H, htrace, houtput, ?_, ?_, ?_, ?_⟩
  · exact strictHardInstance eps method.x0 H heps hH
  · exact hard_runConsistent_of_affine haffine htrace
  · exact all_queries_fail_of_left heps method.x0 hlen htrace
  · exact finite_output_fails_of_left heps heq trace N houtput

end V7
