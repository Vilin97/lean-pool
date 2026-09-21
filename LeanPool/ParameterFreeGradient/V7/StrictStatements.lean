/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import LeanPool.ParameterFreeGradient.V7.StrictModel

open MeasureTheory

namespace V7

/-- U04--U07: `eps` is fixed before the method; the hard transition length
and objective are existential only after the finite transcript/output map. -/
noncomputable def DeterministicFiniteHorizonImpossibilityStatement : Prop :=
  ∀ (p eps : ℝ), 1 < p → 0 < eps →
    ∀ (method : StrictLocalMethod), method.eps = eps →
    ∀ (N : ℕ), 0 < N →
      ∃ affineTrace : StrictTranscript,
        affineTrace.length = N ∧
        StrictRunConsistent method (strictAffineOracle eps method.x0) affineTrace ∧
        ∃ (H L R : ℝ) (oracle : PairOracle 1) (xstar : StrictPoint),
          (∀ obs ∈ affineTrace, obs.point 0 - method.x0 0 < H) ∧
          method.output N affineTrace 0 - method.x0 0 < H ∧
          StrictHardInstance eps method.x0 H L R oracle xstar ∧
          StrictRunConsistent method oracle affineTrace ∧
          StrictAllFirstNQueriesFail eps oracle affineTrace N ∧
          StrictFiniteOutputFails method oracle affineTrace N

/-- U08: a single deterministic `H` and hard instance is chosen after the
whole seed-indexed method, never separately for each seed. -/
noncomputable def RandomizedFiniteHorizonImpossibilityStatement : Prop :=
  ∀ (p eps : ℝ), 1 < p → 0 < eps →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint),
      (∀ ω, (method ω).eps = eps ∧ (method ω).x0 = x0) →
      ∀ (N : ℕ) (delta : ℝ), 0 < N → 0 < delta → delta < 1 →
        ∃ affineTraces : Ω → StrictTranscript,
          (∀ ω, (affineTraces ω).length = N ∧
            StrictRunConsistent (method ω) (strictAffineOracle eps x0) (affineTraces ω)) ∧
          ∃ (H L R : ℝ) (oracle : PairOracle 1) (xstar : StrictPoint),
            StrictHardInstance eps x0 H L R oracle xstar ∧
            ∃ hardTraces : Ω → StrictTranscript,
              (∀ ω, (hardTraces ω).length = N ∧
                StrictRunConsistent (method ω) oracle (hardTraces ω)) ∧
              MeasurableSet {ω | (∀ obs ∈ affineTraces ω,
                  obs.point 0 - x0 0 < H) ∧
                (method ω).output N (affineTraces ω) 0 - x0 0 < H} ∧
              MeasurableSet {ω |
                StrictSuccessThrough (method ω) oracle (hardTraces ω) N} ∧
              ENNReal.ofReal (1 - delta) ≤ μ {ω |
                (∀ obs ∈ affineTraces ω, obs.point 0 - x0 0 < H) ∧
                (method ω).output N (affineTraces ω) 0 - x0 0 < H} ∧
              (∀ ω,
                ((∀ obs ∈ affineTraces ω, obs.point 0 - x0 0 < H) ∧
                  (method ω).output N (affineTraces ω) 0 - x0 0 < H) →
                hardTraces ω = affineTraces ω) ∧
              μ {ω | StrictSuccessThrough (method ω) oracle (hardTraces ω) N} ≤
                ENNReal.ofReal delta

/-- U09: the supremum of the actual expected queried-or-returned hitting
time over normalized strict instances is infinite. -/
noncomputable def InfiniteWorstCaseExpectedHittingTimeStatement : Prop :=
  ∀ (p eps : ℝ), 1 < p → 0 < eps →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (method : RandomizedStrictLocalMethod Ω) (x0 : StrictPoint),
      (∀ ω, (method ω).eps = eps ∧ (method ω).x0 = x0) →
      sSup {E : ENNReal |
        ∃ (L R : ℝ) (oracle : PairOracle 1) (xstar : StrictPoint)
          (traces : Ω → ℕ → StrictTranscript),
          StrictNormalizedInstance eps x0 L R oracle xstar ∧
          (∀ ω N, (traces ω N).length = N ∧
            StrictRunConsistent (method ω) oracle (traces ω N)) ∧
          (∀ ω N, traces ω N = (traces ω (N + 1)).take N) ∧
          Measurable (fun ω => strictHittingTime (method ω) oracle (traces ω)) ∧
          E = ∫⁻ ω, strictHittingTime (method ω) oracle (traces ω) ∂μ} = ⊤

/-- U10: the real-line obstruction applies for every fixed interior exponent
because the one-dimensional `ell_p` and `ell_q` norms are absolute value. -/
noncomputable def OneDimensionalInteriorLpTransferStatement : Prop :=
  ∀ (p : ℝ), 1 < p →
    (∀ x : StrictPoint, lpNorm p x = |x 0|) ∧
    (∀ x : StrictPoint, lpNorm (conjugateExponent p) x = |x 0|)

/-- Source carrier for `thm:impossibility`; its deterministic, randomized,
expectation, and all-`p` clauses remain separate conjuncts. -/
noncomputable def ScaleIdentificationImpossibilityStatement : Prop :=
  DeterministicFiniteHorizonImpossibilityStatement ∧
  RandomizedFiniteHorizonImpossibilityStatement ∧
  InfiniteWorstCaseExpectedHittingTimeStatement ∧
  OneDimensionalInteriorLpTransferStatement

end V7
