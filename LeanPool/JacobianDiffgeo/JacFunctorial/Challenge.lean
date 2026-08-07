/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.PeriodMaps

/-!
# Challenge-signature pushforward exports (jacobian-functoriality §9, pushforward half)

Unit: jacobian-functoriality. `Jacobian.pushforward_contMDiff` — holomorphy of the pushforward
map, free from `jacobian-construction`'s `Jacobian.contMDiff_inducedHom`, inheriting its
`[DiscreteTopology (periodSubgroup _).topologicalClosure]` gate transparently (the same gate
every other `Jacobian _` manifold instance and `ofCurve_contMDiff` already need — no new gate
introduced here).

Same-universe convention as `PeriodMaps.lean`'s `Jacobian.pushforward` (see the universe warning
there): both surfaces live in one `Type u`, matching `JacobianConstruction/Functorial.lean`.

**Scope note**: `pushforward_id_apply`/`pushforward_comp_apply` (needing `Torus.inducedHom_id`/
`_comp`, not built upstream — confirmed absent from `Jacobian/JacobianConstruction/Torus.lean` by
this unit's own research; request now actually filed at `docs/requests/jacobian-construction.md`)
and the full pullback-direction exports (`Jacobian.pullback`, `pullback_contMDiff`,
`pullback_id_apply`, `pullback_comp_apply`, `pushforward_pullback`) are **not built in this
unit** — see the root file's LEDGER and this builder's final report for the precise gap
(`Form1.trace`'s branch-point analyticity and the trace–path-integral relation).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The pushforward map on Jacobians is holomorphic (§9.1 — free from
`Jacobian.contMDiff_inducedHom`; gated by `[DiscreteTopology (periodSubgroup _).topologicalClosure]`
exactly as `ofCurve_contMDiff` and every `ChartedSpace`/`IsManifold` instance on `Jacobian _`
already are). -/
theorem Jacobian.pushforward_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (Jacobian.pushforward f hf) :=
  Jacobian.contMDiff_inducedHom (periodSubgroup_le_comap_pushforwardT f hf)

end RS

end
