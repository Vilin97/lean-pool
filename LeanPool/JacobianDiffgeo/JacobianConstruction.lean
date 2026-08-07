/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacobianConstruction.ChartedSpaceKitV
import LeanPool.JacobianDiffgeo.JacobianConstruction.Torus
import LeanPool.JacobianDiffgeo.JacobianConstruction.Periods
import LeanPool.JacobianDiffgeo.JacobianConstruction.ULift
import LeanPool.JacobianDiffgeo.JacobianConstruction.Basic
import LeanPool.JacobianDiffgeo.JacobianConstruction.OfCurve
import LeanPool.JacobianDiffgeo.JacobianConstruction.Functorial

/-!
# jacobian-construction (CC9): the `Jacobian` type, its scaffolding, and `ofCurve`

API summary (see `docs/design/jacobian-construction.md`). Owner of CC9
(`docs/design/core-choices.md`). Builds the challenge's `Jacobian` type
(`docs/Jacobian_challenge.lean:58-96`) via `Jac₀ X := (Fin (genus X) → ℂ) ⧸ Λ.topologicalClosure`
(`Type 0`) wrapped in a `ULift` shell to match the challenge's universe-polymorphic signature, and
assembles every instance/definition available with no input from period-lattice-rank, plus the
*gated* instances/theorems that become available the moment period-lattice-rank supplies
discreteness (and, for compactness, full rank) of the period subgroup.

## File plan

* `ChartedSpaceKitV.lean` (namespace `RS`) — Surface's `chartedSpaceOfFamily`/`isManifold_of_family`
  generalized from hardcoded codomain `ℂ` to an arbitrary `NormedSpace ℂ` codomain (needed for
  charts into `Fin (genus X) → ℂ`); request filed to surfaces-and-charts, non-blocking.
* `Torus.lean` (namespace `RS`) — the abstract layer, for any `[NormedAddCommGroup V]
  [NormedSpace ℂ V]` and `L : AddSubgroup V`: `AddCommGroup`/`TopologicalSpace`/`T2Space (V ⧸ L)`
  **unconditionally** (the T2-via-closure trick, works at every rank including `0`);
  `ChartedSpace V (V ⧸ L)`/`IsManifold 𝓘(ℂ, V) ω (V ⧸ L)`/`LieAddGroup 𝓘(ℂ, V) ω (V ⧸ L)` gated by
  `[DiscreteTopology L]`; `CompactSpace (V ⧸ L.toAddSubgroup)` gated by `[IsZLattice ℝ L]`
  (`L : Submodule ℤ V`); the `→ₜ+` substrate `inducedHom`/`contMDiff_inducedHom` for a `ℂ`-linear
  map `T` respecting two subgroups.
* `Periods.lean` (namespace `RS`) — `basis X := Module.finBasis ℂ (Form1 X)` and
  `periodSubgroup X := AddSubgroup.closure (range (periodVector (basis X)))` over based loops at
  a fixed basepoint.
* `ULift.lean` (namespace `RS`) — transports `ChartedSpace`/`IsManifold`/`LieAddGroup` across
  `Homeomorph.ulift : ULift (V ⧸ L) ≃ₜ V ⧸ L` (specialized to the torus, per the design's R1
  fallback): `ULift.up`/`ULift.down` are themselves `ω`-smooth (chart composite is the identity
  at aligned representatives), so `LieAddGroup` transfers by composition; `IsManifold` transfers
  by an exact (not just eventual) transition function-and-source identity.
* `Basic.lean` (root level) — `RS.Jac₀ X` and `Jacobian (X : Type u) [...] : Type u` (both
  `abbrev`s, for instance-search transparency), plus the challenge's instance block under
  `namespace Jacobian` — see the LEDGER below.
* `OfCurve.lean` (`namespace Jacobian`, plus `Compat` path-connectedness instances at root) —
  `ofCurve`, `ofCurve_eq_of_path` (well-definedness / any-path recipe), `ofCurve_self`, and
  `ofCurve_contMDiff` (holomorphy — gated, see LEDGER).
* `Functorial.lean` (`namespace Jacobian`) — `inducedHom`/`contMDiff_inducedHom`, the `→ₜ+`
  substrate wrapped through the `ULift` shell, for an abstract `ℂ`-linear `T` respecting the two
  period subgroups. **Not** the actual `pushforward`/`pullback` for a real holomorphic `f` — see
  the "not this unit's job" note below.

## Instance/definition ledger (ground truth; mirrors `Basic.lean`'s docstring)

Built **now**, no hypotheses beyond the standing Riemann-surface ones:
`AddCommGroup (Jacobian X)`, `TopologicalSpace (Jacobian X)`, `T2Space (Jacobian X)` (every genus,
including `g = 0` — no discreteness needed), `Jacobian.ofCurve`, `Jacobian.ofCurve_eq_of_path`,
`Jacobian.ofCurve_self`.

Built **now**, but the statement itself needs `[DiscreteTopology (periodSubgroup
X).topologicalClosure]`
to typecheck (its codomain's manifold structure is gated — see below), so it is stated with that
extra hypothesis rather than at the challenge's bare signature:
`Jacobian.ofCurve_contMDiff`, `Jacobian.inducedHom`, `Jacobian.contMDiff_inducedHom`.

**Gated** (typeclass hypotheses, not sorries — become `instance`-available automatically once
period-lattice-rank registers the hypotheses as instances for the real period subgroup):
`Jacobian.instChartedSpace`/`instIsManifold`/`instLieAddGroup` need
`[DiscreteTopology (periodSubgroup X).topologicalClosure]`; `Jacobian.instCompactSpace`
additionally needs `[IsZLattice ℝ (periodSubgroup X).topologicalClosure.toIntSubmodule]`.

**Not this unit's job** (per the design doc and blueprint):
`genus_eq_zero_iff_homeo`, `Jacobian.ofCurve_inj` (abel-theorem, needs `g ≥ 1`),
`ContMDiff.degree`, `Jacobian.pushforward_pullback`, and — a genuine **blueprint gap** flagged for
the orchestrator — the construction of the *actual* linear map `T` underlying `pushforward`/
`pullback` for a real holomorphic `f : X → Y` (needs "pullback of holomorphic `1`-forms along a
holomorphic map", which no unit in the 30-unit blueprint currently owns; natural candidates:
abel-theorem, since it already needs period-naturality for its two-point argument, or a
final-assembly addendum).
-/
