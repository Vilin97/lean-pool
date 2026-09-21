/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Torus.RealizableMetrics
import LeanPool.NashEmbedding.NashEmbedding.Torus.Approximation.SmoothMetricApprox

/-!
# NashEmbedding witness tests: realizable metrics + Theorem A

Concrete witness checks for `NashEmbedding/Torus/RealizableMetrics.lean` and
`NashEmbedding/Torus/Approximation/SmoothMetricApprox.lean`:
- **TN1** — closure under addition (`realizable_sum`).
- **TN2** — closure under non-negative scaling (`realizable_nonneg_smul`).
- **TN3** — `injRealizable_posDef`: injectively realizable ⟹ pos-def smooth.
- **TN4** — `convex_combination_approx` invocation on the flat metric.
-/

open scoped BigOperators ContDiff
open NashEmbedding NashEmbedding.Sobolev Matrix

namespace RealizableMetricsTests

noncomputable section

variable {n : ℕ}

/-- **TN1** — Closure under sum: the sum of two copies of `flatMetric` is
    realizable. Uses `flatTorusEmb_injRealizes` (concrete witness) +
    `IsInjRealizable.toIsRealizable` (forgetful) + `realizable_sum` (closure). -/
example : IsRealizable (flatMetric n + flatMetric n) :=
  realizable_sum flatTorusEmb_injRealizes.toIsRealizable
                 flatTorusEmb_injRealizes.toIsRealizable

/-- **TN2** — Closure under non-negative scaling: `2 • flatMetric` is
    realizable. -/
example : IsRealizable ((2 : ℝ) • flatMetric n) :=
  realizable_nonneg_smul flatTorusEmb_injRealizes.toIsRealizable (by norm_num)

/-- **TN3** — `injRealizable_posDef` applied to the flat metric: injective
    realizability via `flatTorusEmb` yields positive-definite smoothness.
    (Note: `flatMetric_isPosDefSmoothMetric` proves the same conclusion
    directly; this test exercises the alternative path through the
    injective-realizability machinery.) -/
example : IsPosDefSmoothMetric (flatMetric n) :=
  injRealizable_posDef flatTorusEmb_injRealizes

/-- **TN4** — `convex_combination_approx` invokable on `flatMetric` with
    any tolerance `η > 0`. Witnesses the headline theorem on a concrete
    smooth metric input. -/
example (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℕ, 0 < M := by
  obtain ⟨M, hM, _, _, _, _, _, _, _⟩ :=
    convex_combination_approx hn
      (flatMetric_isPosDefSmoothMetric.toIsSmoothMetric) hs hη
  exact ⟨M, hM⟩

end

end RealizableMetricsTests
