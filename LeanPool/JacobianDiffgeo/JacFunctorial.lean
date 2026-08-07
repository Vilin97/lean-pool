/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.JacFunctorial.Pullback
import LeanPool.JacobianDiffgeo.JacFunctorial.PullbackIntegral
import LeanPool.JacobianDiffgeo.JacFunctorial.Density
import LeanPool.JacobianDiffgeo.JacFunctorial.PeriodMaps
import LeanPool.JacobianDiffgeo.JacFunctorial.Challenge
import LeanPool.JacobianDiffgeo.JacFunctorial.TraceCoeff
import LeanPool.JacobianDiffgeo.JacFunctorial.Trace
import LeanPool.JacobianDiffgeo.JacFunctorial.TraceLaws
import LeanPool.JacobianDiffgeo.JacFunctorial.TraceIntegral
import LeanPool.JacobianDiffgeo.JacFunctorial.PullbackMaps
import LeanPool.JacobianDiffgeo.JacFunctorial.ChallengeLaws

/-!
# `jacobian-functoriality` (unit root)

Task #33 (blueprint-gap unit, flagged by `jacobian-construction`'s `Functorial.lean` §9.4/R4).
Target: `Jacobian.pushforward`, `Jacobian.pullback`, and the functoriality laws /
`pushforward_pullback` demanded by `docs/Jacobian_challenge.lean:104-153`, built from pullback
and trace of holomorphic `1`-forms.

## LEDGER — what is built (zero sorries; `scripts/check.sh Jacobian/JacFunctorial` covers all)

### Pushforward half (first build)

* **`Jacobian/JacFunctorial/Pullback.lean`**: `RS.Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X`
  (chain-rule pullback along *any* holomorphic `f`), `RS.coeffAt_pullback`/`RS.coeffIn_pullback`,
  `RS.Form1.pullback_id`, `RS.Form1.pullback_comp`, plus a `Compat` section
  (`RS.analyticAt_of_mem_maximalAtlas`, `RS.mfderiv_chartAt_self`,
  `RS.tangentCoord_mfderiv_chart_comp`).
* **`Jacobian/JacFunctorial/PullbackIntegral.lean`**: `RS.IsPrimitiveAlongMap.pullback_comp`,
  `RS.pathIntegral_pullback` (naturality of `pathIntegral` under pullback).
* **`Jacobian/JacFunctorial/Density.lean`**: `RS.Form1.eq_of_eqOn_dense` ("Lemma A") via a
  fixed-reference-chart cancellation (no tangent-bundle continuity needed; see §0 below), plus
  the reusable planar `RS.ContinuousOn.eqOn_of_subset_closure`.
* **`Jacobian/JacFunctorial/PeriodMaps.lean`**: `RS.periodCoordEquiv`, `RS.pushforwardT`,
  `RS.pushforwardT_periodVector`, `RS.periodSubgroup_le_comap_pushforwardT` (exact membership),
  **`Jacobian.pushforward`** via `Jacobian.inducedHom`. **UNIVERSE WARNING** (hard-won):
  `Jacobian.inducedHom` demands both surfaces in ONE `Type u`; instantiating at distinct
  universe metavariables sends the elaborator into a >40-minute `ULift`/quotient defeq grind
  instead of a clean error. Every `Jacobian X`+`Jacobian Y` declaration here fixes one shared
  `u`.
* **`Jacobian/JacFunctorial/Challenge.lean`**: `Jacobian.pushforward_contMDiff` (gated on
  `[DiscreteTopology (periodSubgroup _).topologicalClosure]`, inherited transparently).

### Trace/pullback half (this build — the previous builder's diagnosed blocker, closed)

* **`Jacobian/JacFunctorial/TraceCoeff.lean`** (the repaired planar trace coefficient — the
  precise fix for the diagnosed defect that `traceZkForm h k`'s literal value at the branch
  coordinate `0` is junk): `RS.traceCoeff h k := toMeromorphicNFAt (traceZkForm h k) 0`, with
  `RS.traceCoeff_apply_of_ne_zero` (literal off `0`), `RS.analyticAt_traceCoeff_zero` (via the
  Laurent route: `laurentCoeffAt_traceZkForm` + `forall_neg_laurentCoeffAt_eq_zero_iff` +
  `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`),
  **`RS.analyticOnNhd_traceCoeff`** (analytic on `ball 0 (ρ^k)`, branch point included),
  `RS.traceCoeff_one`, `RS.traceCoeff_fun_add`, `RS.traceCoeff_const_mul`, and the `k = 1` /
  linearity API for `traceZk`/`traceZkForm` (`traceZk_one`, `traceZkForm_one`,
  `traceZkForm_fun_add`, `traceZkForm_const_mul`).
* **`Jacobian/JacFunctorial/Trace.lean`** (**`RS.Form1.trace (f : X → Y) (hf) :
  Form1 X →ₗ[ℂ] Form1 Y`**, zero map for constant `f`): coefficient data over the chart family
  `ι := Y` (`RS.stackAt`/`RS.traceChart`/`RS.branchTrans`/`RS.traceCoeffFun`), assembled by
  `Form1.ofCoeffs` as `RS.traceForm hf hne`. Well-definedness/`compat` via the canonical
  per-fibre-point coefficient `RS.qCoeff` (`traceCoeffFun_eq_qSum` off the chart center,
  `qSum_trans` chart transition, extended over the whole overlap by continuity + density of the
  non-center locus). Key evaluation exports: `RS.coeffAt_traceForm` and
  **`RS.coeffAt_traceForm_of_isRegularValue`** (`coeffAt yhat (Tr_f η) = ∑ᶠ x ∈ f⁻¹{yhat},
  qCoeff f η (chartAt ℂ yhat) x` at regular values). Chart helpers `RS.deriv_transition_mul`,
  `RS.deriv_chartRead_eq_of_adapted`, `RS.open_subset_closure_diff`.
* **`Jacobian/JacFunctorial/TraceLaws.lean`**: `RS.Form1.trace_id`, `RS.Form1.trace_comp`
  (doubly-regular density argument), **`RS.Form1.trace_pullback`** (the projection formula
  `Tr_f (f^* η) = (ContMDiff.degree f hf : ℂ) • η`, via `RS.qCoeff_pullback` +
  `RS.ncard_fiber_of_isRegularValue` + density), `RS.deriv_chartRead_ne_zero`,
  `RS.qCoeff_comp`, `RS.not_exists_const_id`.
* **`Jacobian/JacFunctorial/TraceIntegral.lean`** (the trace–period relation, period-level form
  — deliberately cheaper than the design's full `FiberChain`/monodromy construction, same
  conclusion): local sections `RS.sectionAt` over regular stacks, the **segment lemma**
  `RS.pathIntegral_traceForm_segment` (`∫ Tr_f η = ∑ sheets ∫ (section ∘ path) η` over one trace
  chart, by exhibiting the summed per-sheet disc primitives as a primitive of the trace),
  `RS.TraceChain` (Lebesgue subdivision through regular values) + `RS.exists_traceChain`,
  `RS.Path.segMap`/`RS.pathIntegral_segMap` (telescoping a fixed primitive), and the
  **loop decomposition** `RS.pathIntegral_traceForm_eq_sum_loops`: `∫_δ Tr_f η = ∑ (k,i)
  ∫_{loop k i} η` with η-independent based loops obtained by conjugating each lifted sheet with
  fixed connecting paths — the correction terms are stack-independent fibre-set sums that
  telescope to `0` around the loop (no monodromy-cycle bookkeeping needed). Corollary:
  **`RS.periodVector_traceForm_mem`** (exact membership in `periodSubgroup X`).
* **`Jacobian/JacFunctorial/PullbackMaps.lean`**: `RS.pullbackT` (dual of `Form1.trace` in
  period coordinates), `RS.pullbackT_periodVector`,
  **`RS.periodSubgroup_le_comap_pullbackT`** (`hT`, exact membership: conjugate the generator
  loop to a regular basepoint via `period_conj`, perturb it off the finite branch locus via
  `Loop.exists_homotopic_avoiding`/`period_congr_homotopic`, then apply
  `periodVector_traceForm_mem`), and **`Jacobian.pullback`** via `Jacobian.inducedHom`
  (same-universe convention).
* **`Jacobian/JacFunctorial/ChallengeLaws.lean`**: **`Jacobian.pullback_contMDiff`** (same
  inherited discreteness gate as the pushforward), `RS.Jacobian.exists_rep` +
  `RS.Jacobian.inducedHom_apply_up_mk` (representative-level computation),
  `RS.pushforwardT_id`/`RS.pullbackT_id`/`RS.pushforwardT_comp`/`RS.pullbackT_comp`/
  `RS.pushforwardT_pullbackT_apply`, and the challenge laws
  **`Jacobian.pushforward_id_apply`**, **`Jacobian.pushforward_comp_apply`**,
  **`Jacobian.pullback_id_apply`**, **`Jacobian.pullback_comp_apply`**,
  **`Jacobian.pushforward_pullback`** (`pushforward f hf (pullback f hf P) =
  (ContMDiff.degree f hf) • P`).
* **`Jacobian/JacobianConstruction/Torus.lean`** (authorized upstream addition, request
  `docs/requests/jacobian-construction.md` now FULFILLED): `RS.inducedHom_id`,
  `RS.inducedHom_comp` (functoriality of the abstract `V ⧸ L →ₜ+ V' ⧸ L'` substrate). The
  challenge laws above are proved by representative-level computation and do not depend on
  them, but they are now available upstream as requested.

### §0: why `Form1.continuous_coeffAt` was replaced, not merely worked around

The design's `Density.lean` sketch routes "Lemma A" through a standalone
`Form1.continuous_coeffAt`; that needs continuity of `mfderiv (chartAt ℂ x)` *in the base
point* — not built anywhere. `Form1.eq_of_eqOn_dense` instead compares against one *fixed*
reference chart and cancels a provably-nonzero transition factor. Anyone needing
`Form1.continuous_coeffAt` itself should know it remains open.

## Gate inheritance

`Jacobian.pushforward_contMDiff`/`Jacobian.pullback_contMDiff` inherit
`[DiscreteTopology (periodSubgroup _).topologicalClosure]` transparently from
`jacobian-construction`'s `Jacobian.contMDiff_inducedHom` — the same gate every
`ChartedSpace`/`IsManifold`/`LieAddGroup`/`CompactSpace (Jacobian _)` instance and
`ofCurve_contMDiff` already need. Everything else in this unit (both maps, all four
functoriality laws, `pushforward_pullback`) is gate-free.
-/
