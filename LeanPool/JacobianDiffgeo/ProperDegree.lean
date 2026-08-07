/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.ProperDegree.ChallengeDegree
import LeanPool.JacobianDiffgeo.ProperDegree.DivisorDegreeZero
import LeanPool.JacobianDiffgeo.ProperDegree.GenusZeroFinisher

/-!
# proper-map-degree: the challenge degree, `deg(div f) = 0`, and the genus-0 finisher

API summary (see `docs/design/proper-map-degree.md`). A small consolidation unit: the hard
mathematics (the mapping degree, sheet counting, multiplicity patching, degree-1 ⇒ homeomorphism)
is already built in `Jacobian/MappingDegree/`, and the order↔multiplicity bridge to a meromorphic
function's zeros/poles is already built in `Jacobian/MeromorphicTrace/`. This unit's own content is
three pieces of glue.

**DAG correction** (recorded per the design doc §2, mirroring corrections already filed by
`meromorphic-trace`/`mapping-degree`): the blueprint's `Builds on: monodromy` is spurious — nothing
here needs continuation-of-primitives/monodromy machinery. The real dependency edges are
`mapping-degree, meromorphic-and-divisors, meromorphic-trace, projective-line`.

* **`ChallengeDegree.lean`**: `_root_.ContMDiff.degree (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
  ℕ` — the EXACT challenge signature (`docs/Jacobian_challenge.lean:147`), a `rfl`-wrapper over
  `RS.degree f`; plus `ContMDiff.degree_eq`/`degree_of_forall_eq`/`degree_comp` restated in wrapper
  form. `f` is **explicit** (matching the challenge file's own `variable (f : X → Y) (hf : ...)`
  and its call site `ContMDiff.degree f hf` in `pushforward_pullback`) — a deviation from the
  design doc's implicit-`f` sketch, corrected here to match the target verbatim.

* **`DivisorDegreeZero.lean`**: `RS.divisor_degree_eq_zero (φ : ℳ X) (hφ : φ ≠ 0) :
  (divisor φ).degree = 0` — THE argument principle in `Divisor`/`ℳ X` vocabulary, citing
  `MeromorphicTrace.ArgumentPrinciple`'s `finsum_ordAtX_eq_zero'` (which had landed by build time,
  so the design's "cite instead of reprove" short route was used, not its self-contained
  fallback). Also `RS.sum_ord_eq_zero_of_finite` (Finset padding corollary) and
  `RS.linSys_eq_bot_of_degree_neg'` — the **unconditional** discharge of
  `Meromorphic/LinearSystem.lean`'s conditional `linSys_eq_bot_of_degree_neg` (primed to avoid a
  name clash in the shared `RS` namespace; that file's declaration could not be renamed).

* **`GenusZeroFinisher.lean`**: `RS.homeoSphere_of_exists_simple_pole (φ : ℳ X) (Q : X)
  (hpole : φ.ord Q = -1) (hreg : ∀ x, x ≠ Q → 0 ≤ φ.ord x) :
  Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` — a single simple pole forces
  the induced `ℙ¹`-map to have degree `1` (via `MappingDegree`'s degree-1-⇒-homeomorphism family
  applied to `RS.MTrace.toP1 f`), hence `X ≃ₜ ℙ¹ ≃ₜ S²`. Independent of `ArgumentPrinciple`
  (nonconstancy is witnessed directly by the pole location `Q`, not by the general codiscrete
  argument) — the safest file in the unit, built without depending on mtrace's timing.

Downstream: `serre-duality-tails`/`riemann-roch` consume `divisor_degree_eq_zero`/
`linSys_eq_bot_of_degree_neg'`; `genus-zero-headline` consumes `homeoSphere_of_exists_simple_pole`
directly for its forward direction (recommend the orchestrator add `proper-map-degree` to that
unit's `Builds on:` list, per the design doc's non-blocking flag); final assembly consumes
`_root_.ContMDiff.degree` and friends verbatim.
-/
