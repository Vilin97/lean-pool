/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.SphereTopology.SimplyConnectedP1
import LeanPool.JacobianDiffgeo.SphereTopology.GlobalPrimitive
import LeanPool.JacobianDiffgeo.SphereTopology.Headline

/-!
# sphere-topology: `SimplyConnectedSpace (OnePoint ℂ)` and `genus X = 0` for simply connected `X`

API summary (see `docs/design/sphere-topology.md`), namespace `RS.SphereTopology` unless noted.
Builds on projective-line (CC5) and paths-and-integrals (CC6); no van Kampen, no universal cover,
no covering-space monodromy anywhere — the two headline results are assembled from more
elementary mathlib pieces (contractibility/local-path-connectedness/open-embedding transport) plus
paths-and-integrals' own loop-perturbation and homotopy-invariance lemmas.

* **Topology** (`SimplyConnectedP1.lean`): `isSimplyConnected_compl_infty`/
  `isSimplyConnected_compl_coeZero` (the two polar caps of `OnePoint ℂ`'s atlas, each ≃ₜ `ℂ`,
  hence simply connected), `instance : PathConnectedSpace (OnePoint ℂ)`, the headline
  `instance simplyConnectedSpace_onePoint : SimplyConnectedSpace (OnePoint ℂ)` (via
  paths-and-integrals' `RS.Loop.exists_homotopic_avoiding`, basepoint-split on `∞` vs `↑0`),
  `simplyConnectedSpace_of_homeoOnePoint` (generic homeomorphism transfer), and
  `instance simplyConnectedSpace_sphere : SimplyConnectedSpace (Metric.sphere ... 1)` (the
  literal challenge sphere model, via `RS.P1.homeoSphere`).

  (Development note: this unit was built while `RS.Loop.exists_homotopic_avoiding`
  (`Jacobian/Path/Perturb.lean`) still carried one documented upstream placeholder step, design
  risk R4 of paths-and-integrals; that step has since been resolved upstream — see
  `docs/build-log.md`, "Perturb.lean FIXED" — so no downstream change was needed here.)

* **Analysis — the genus-0 engine** (`GlobalPrimitive.lean`, standing surface variables per
  `CONVENTIONS.md`): `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` (a primitive of
  `η` along `id : X → X` is a genuine holomorphic global primitive with `mdifferential = η` —
  reusable verbatim by the monodromy unit, see that file's docstring),
  `exists_isPrimitiveAlongMap_id`
  (constructs the global primitive on simply connected `X` via `pathIntegral` from a base point),
  `form1_eq_zero_of_simplyConnectedSpace` (Forster 10.5: every holomorphic 1-form vanishes on a
  simply connected compact surface), the `Subsingleton (Form1 X)` instance, and the headline
  `genus_eq_zero_of_simplyConnectedSpace : genus X = 0`.

* **Assembly** (`Headline.lean`): `genus_eq_zero_of_homeo_sphere` — the exact backward-headline
  signature `Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) → genus X = 0`,
  consumed by `genus-zero-headline` alongside Riemann–Roch's forward half.

Downstream consumers: `genus-zero-headline` (consumes `genus_eq_zero_of_homeo_sphere` directly);
`monodromy` (may reuse `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` verbatim, or
re-derive the same conclusion from its own chain-continuation `IsPrimitiveAlongMap id η F univ`
fact — both routes agree, no dependency is required either way).
-/
