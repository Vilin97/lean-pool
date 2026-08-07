/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Monodromy.OpenLocus
import LeanPool.JacobianDiffgeo.Monodromy.LogContinuation

/-!
# monodromy (namespace `RS.Monodromy`)

API summary (see `docs/design/monodromy.md`). The blueprint's literal ask — local primitives on
disks, chain-of-charts discrete continuation, homotopy invariance, and "simply connected ⇒ global
primitive" — is **already fully built** in `Jacobian/Path/{LocalPrimitive,Chain,Continuation,
HomotopySquare}.lean` and `Jacobian/SphereTopology/GlobalPrimitive.lean`; nothing here re-proves
any of it. What this unit adds is genuinely new: continuation of a **meromorphic** logarithmic
derivative along a pole/zero-avoiding path — the piece `abel-weak-solutions` actually needs from
Forster §20.1–20.5 that no upstream unit provides.

* **The open locus** (`Monodromy/OpenLocus.lean`): `RS.Monodromy.openLocus`/`openLocusOfFinite`
  turn a closed/finite "bad set" of a Riemann surface `X` into an `Opens X`; mathlib gives this
  open submanifold the *same* `ChartedSpace ℂ`/`IsManifold 𝓘(ℂ) ω` instances as `X` itself, for
  free (`TopologicalSpace.Opens.instChartedSpace` and its derived `IsManifold` instance) — so
  `Jacobian/Path/`'s entire per-path API (`RS.IsPrimitiveAlong`, `RS.exists_isPrimitiveAlong`,
  `RS.pathIntegral`, `RS.pathIntegral_congr_homotopic`, …) applies to the open locus by direct
  instantiation, no wrapper layer, no new lemmas (spike-verified, `scratch_mono.lean`, project
  root). `RS.Monodromy.Path.liftOpenLocus`/`.liftOpenLocus_extend` lift a bad-set-avoiding path of
  `X` into the locus.
* **Continuation of `log f`** (`Monodromy/LogContinuation.lean`): for `f : ℳ X`, `f ≠ 0`,
  `RS.Monodromy.poleZeroLocus f` is the open locus where `f` has neither a zero nor a pole
  (`(divisor f).support` is finite by compactness, hence closed). `RS.Monodromy.dlogForm f hf` is
  the logarithmic-derivative 1-form `df/f` there, assembled by *reusing* (not re-proving)
  `Jacobian/Forms/MDifferential.lean`'s `RS.mdifferential`/`RS.Form1.smulFun` instantiated with
  `X := poleZeroLocus f` — sidestepping any chart-transition/`subtypeRestr` bookkeeping a
  from-scratch `Form1CoeffData` would need, since `f.holoRepr` restricted to the locus is
  `ContMDiff` and everywhere nonvanishing there by construction. `RS.Monodromy.coeffIn_dlogForm`
  gives its chart-coefficient formula (the familiar `(f'/f)`-shape).

  The DAG-critical deliverable, `RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong`: any primitive
  `F` of `dlogForm f hf` along a pole/zero-avoiding path, normalized so `exp (F 0) = f.holoRepr x`,
  satisfies `exp (F t) = f.holoRepr (γ.extend t)` for every `t` — an honest continuous branch of
  `log f` along the path, established via a zero-derivative/local-constancy argument
  (`H t := f.holoRepr (γ.extend t) * exp (-(F t))` is locally constant, hence constant on
  preconnected `ℝ`), **not** by any case analysis on `Complex.log`/`Complex.arg` branch cuts.
  `RS.Monodromy.exists_logBranchAlong` packages existence with a prescribed initial branch value
  (via `RS.exists_isPrimitiveAlong` shifted by `.add_const`), and
  `RS.Monodromy.logBranchAlong_unique` is a direct citation of `RS.IsPrimitiveAlongMap.sub_eq_sub`
  (uniqueness up to the initial choice — no new proof).

  Paths are lifted into `poleZeroLocus f` via the dedicated `RS.Monodromy.Path.liftPoleZeroLocus`/
  `.liftPoleZeroLocus_extend` (a thin specialization of `Path.liftOpenLocus` landing directly in
  `poleZeroLocus f`, needed to avoid a `synthInstance` confusion between that type and the
  definitionally-equal-but-syntactically-different `openLocusOfFinite (finite_support_divisor f)`
  when both appear in the same elaboration problem — see the docstring at its declaration).

## Downstream consumers

`abel-weak-solutions` gets a continuous, honestly-`exp`-compatible branch of `log f` along any
pole/zero-avoiding path it can produce (e.g. via `Path/Perturb.lean`'s `exists_homotopic_avoiding`)
without re-deriving Forster's own annulus-plus-cutoff/winding-number argument by hand:
`RS.Monodromy.exists_logBranchAlong`, `RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong`,
`RS.Monodromy.logBranchAlong_unique`. `period-lattice-rank` has no direct edge to this unit (any
relevance is transitive, through `abel-weak-solutions`).

## Deferred

The general "continuation of a primitive of an arbitrary `MForm X` along pole-avoiding paths" (the
task brief's item 1 in full generality) is **not** built: it needs `canonical-forms`'s `MForm X`
type, which does not exist on disk yet, and no currently-designed consumer needs it (`abel-weak-
solutions` needs only the function-level `dlog f` case above). See `docs/design/monodromy.md` §5
for the sketch, should a future unit ever need it.
-/
