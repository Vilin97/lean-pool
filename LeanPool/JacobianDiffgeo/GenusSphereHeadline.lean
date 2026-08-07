/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.GenusSphereHeadline.Basic

/-!
# genus-zero-headline (#30): `genus X = 0 ↔ X ≃ₜ S²`

API summary (see `Basic.lean`'s own docstring). Builds on `riemann-roch` (BUILT, forward
direction's seed: `RS.riemann_inequality`) and `sphere-topology` (BUILT, backward direction:
`RS.SphereTopology.genus_eq_zero_of_homeo_sphere`) and `proper-map-degree` (BUILT, forward
direction's finisher: `RS.homeoSphere_of_exists_simple_pole`). **Unit COMPLETE**: zero sorries,
`scripts/check.sh Jacobian/GenusSphereHeadline` passes. **NOT registered in `Jacobian.lean`**
(orchestrator's job).

## Exports

* `RS.GenusSphereHeadline.exists_simple_pole_of_genus_eq_zero` — the forward-direction finisher
  (genus `0` ⇒ a meromorphic function with exactly one simple pole).
* **`genus_eq_zero_iff_homeo`** (root level — no namespace, matching
  `docs/Jacobian_challenge.lean:54-56` verbatim, at the challenge's own standing variables: `{X}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]`, no extra `[T1Space X]`/`[DecidableEq X]` hypotheses needed —
  `T1Space X` comes for free from `T2Space X`, `DecidableEq X` is supplied internally via
  `classical`). **This is a direct alias target for final assembly**: no further wrapping should
  be needed to slot it into the challenge file.
-/
