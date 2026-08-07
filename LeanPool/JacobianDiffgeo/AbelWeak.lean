/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.AbelWeak.PlanarLogBranch
import LeanPool.JacobianDiffgeo.AbelWeak.WeakSolution
import LeanPool.JacobianDiffgeo.AbelWeak.SingleChart
import LeanPool.JacobianDiffgeo.AbelWeak.ChainAssembly
import LeanPool.JacobianDiffgeo.AbelWeak.Rechart
import LeanPool.JacobianDiffgeo.AbelWeak.GeneralChain

/-!
# abel-weak-solutions: weak solutions, the planar log-branch, and chain assembly (Forster
§20.1–20.4)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md`). Builds the weak-solution
machinery Forster's Abel's-theorem proof (§20.5–20.7) needs, staying in planar pieces glued by
explicit chart formulas (no monodromy/homotopy machinery). Namespace `RS.AbelWeak` unless noted.
NOT registered in `Jacobian.lean` (orchestrator's job, per this unit's task hard rules).

## API summary

* **`WeakSolution.lean`** (Forster §20.1–20.2, D1):
  `IsWeakSolutionAt f a k` — the local model `f = ψ(e·)·(e· − e a)^k` near `a` in some
  `maximalAtlas` chart `e`, `ψ` smooth (`ℝ`-`C^∞`, i.e. `ContDiffAt ℝ ∞`) and non-vanishing near
  `e a`. `IsWeakSolutionOfPair f P Q` — the two-point structure this unit's deliverable produces
  (`ℝ`-smooth off `Q`, non-vanishing off `{P, Q}`, local model `+1` at `P`, `-1` at `Q`).
  **SCOPE ADDITION** (`docs/design/abel-theorem.md` §1.4/§4.1's finding that Thm 21.4(b) needs
  the `k`-point case): `IsWeakSolutionOfFinset f a x` (Finset-indexed generalization) and
  `isWeakSolutionOfFinset_prod` (Forster's Lemma 20.1 — weak solutions of pairwise-disjoint pairs
  multiply). Also: the `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` ↔ planar `ContDiffAt ℝ ∞` chart bridges
  (`contMDiffAt_finsetProd_real`, `contDiffAt_comp_symm_of_contMDiffAt`,
  `contMDiffAt_comp_of_contDiffAt`) and the multiplicativity step
  `IsWeakSolutionAt.mul_of_contMDiffAt`.

* **`PlanarLogBranch.lean`** (§6.1, no manifold imports, pure `ℂ → ℂ`):
  `exists_logBranch_disk` (disk case: a log branch of any non-vanishing holomorphic `h` on a
  ball, via mathlib's disk-Morera primitive + a zero-derivative uniqueness argument — no
  `Complex.log`/`Complex.arg` branch-cut case analysis) and `exists_exteriorLogBranch` (the
  engine Forster's construction needs: a log branch of `(z−b)/(z−a)` on `{ρ < ‖z‖}` for
  `a, b ∈ ball 0 ρ`, via the inversion `w = 1/z` transporting the exterior region to a genuine
  disk with no excluded point at all).

* **`SingleChart.lean`** (§6.2–6.3): `exists_weakSolutionOfPair_chart` — the single-chart weak
  solution: given `P, Q` inside a common chart `e`, both within `ball c ρ`, and a
  `ContDiffBump (0 : ℂ)` cutoff interpolating the rational function `(z−eP)/(z−eQ)` (near `c`) to
  the constant `1` (outside `closedBall c ψ.rOut`), produces `f` with `IsWeakSolutionOfPair f P Q`,
  equal to `1` outside the open set `e.symm '' ball c ψ.rOut` (compact closure).

* **`ChainAssembly.lean`** (§7): three deliverables —
  * `exists_weakSolutionOfFinset` — the **SCOPE ADDITION** `k`-point layer, assembled directly
    from `exists_weakSolutionOfPair_chart` (one call per pairwise-disjoint pair, each already
    living inside its own chart neighbourhood — exactly the shape `abel-theorem`'s own Thm
    21.4(a) disjoint-chart construction produces, per its design's own §1.4 account) plus
    `isWeakSolutionOfFinset_prod`.
  * `pathIntegral_eq_sum_chartChain` — the CC6-compliant telescoped path-integral identity
    (§7.1's `(1/2πi) ∫∫_X (df/f) ∧ ω` replacement, D5): for any `ChartChain` `C` and holomorphic
    `η`, `pathIntegral γ η` equals the finite sum of chart-local primitive differences. Pure
    `Path`-API bookkeeping, no Stokes.
  * `residue_identity_two_point` / `logDeriv_rat_eq` — the Lemma-20.3-specialized residue
    identity (Stokes-driven): for the two-puncture kernel `(w−b)⁻¹ − (w−a)⁻¹` (a weak solution's
    own log-derivative shape, `logDeriv_rat_eq`) and any `C¹` compactly-supported `g`, the area
    integral of `dbarg` against that kernel recovers `g b − g a` — no local-constancy hypothesis on
    `g` needed (citing `planar-stokes-atoms`' own hypothesis-free two-puncture export
    `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` directly).

## Status: the general multi-chart `exists_weakSolutionOfPair` is NOW BUILT (`Rechart.lean` +
`GeneralChain.lean`, closed by the `abel-theorem` builder, authorized to edit this unit for
exactly this gap)

The design's §6.3/§7.1 deliverable — a weak solution of `(P, Q)` for an **arbitrary** path
`γ : Path Q P` not confined to one chart — is now built in full, zero sorries.

* **`Rechart.lean`** (the missing "rechart" lemma this unit's original pass flagged as the gap):
  `exists_localModel_of_isWeakSolutionAt` — `IsWeakSolutionAt`'s local model, witnessed in one
  `maximalAtlas` chart, can be re-witnessed in ANY OTHER `maximalAtlas` chart at the same point.
  Proved via mathlib's removable-singularity theorem: the transition map `S := e ∘ e'.symm`
  between two charts is holomorphic (`IsManifold`'s groupoid compatibility, transported through
  `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` and mathlib's generic `contMDiffAt_iff_contDiffAt`), its "divided
  difference" `H := dslope S (e' a)` is analytic too
  (`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`) and NONZERO at the transition point
  (`S` has a two-sided holomorphic inverse — the reverse transition — so the chain rule on
  `T ∘ S = id` forces `deriv S (e' a) ≠ 0`), and the unconditional identity `sub_smul_dslope`
  gives the exact factorisation `e x - e a = (e' x - e' a) * H (e' x)` needed to rewrite the local
  model, with `H` supplying the new nonvanishing smooth cofactor. Consumer: `IsWeakSolutionAt.mul`
  — fully general order-additive multiplication (subsuming `WeakSolution.lean`'s
  `IsWeakSolutionAt.mul_of_contMDiffAt`'s `k2 = 0` case), combining `IsWeakSolutionAt f a k1` and
  `IsWeakSolutionAt g a k2` (witnessed by POSSIBLY DIFFERENT charts, aligned via the rechart
  lemma) into `h` equal to `f * g` everywhere except possibly at `a`, with
  `IsWeakSolutionAt h a (k1 + k2)`. The "possibly except at `a`" `Function.update` is not a
  cosmetic detail: at the cancelling case `k1 = -k2 ≠ 0` (a `+1`-order zero meeting a `-1`-order
  pole — exactly what happens at every interior `ChartChain` breakpoint), the naive product
  `f * g` genuinely disagrees with the correct weak solution AT the point `a` itself, because
  `IsWeakSolutionAt`'s local model pins down `f`'s/`g`'s literal (junk-convention) value there via
  `zpow`-at-zero (`0 ^ k = 0` for `k ≠ 0`, so `(f * g) a = 0`, but the removable-singularity limit
  is `ψ (e a) * φ (e a) ≠ 0`); `Function.update` at the single point `a` repairs this uniformly
  for every `k1, k2` (documented in the file's own docstring in full).

* **`GeneralChain.lean`** (the chain induction, using `Rechart.lean`'s two exports as the engine):
  `exists_weakSolutionOfPair {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P) : ∃ f U, IsWeakSolutionOfPair
  f P Q ∧ IsOpen U ∧ IsCompact (closure U) ∧ P ∈ U ∧ Q ∈ U ∧ (∀ x ∉ U, f x = 1)` — the fully
  general two-point deliverable, matching `abel-theorem`'s design's expected signature exactly
  (§6.3/§7.1). Built by strong induction along a `RS.ChartChain δ` (`Jacobian.Path.Chain`,
  breakpoints `M k := δ.extend (C.t k)`), gluing one fresh `SingleChart` piece per chain link at
  each step via `IsWeakSolutionAt.mul`, applied at up to THREE points per step (the chain's fixed
  basepoint `M 0`, the outgoing old endpoint `M m`, and the new endpoint `M (m + 1)`, since
  `M 0` can coincide with either of the other two — handled by three exhaustive cases via the
  file's own `merge_two`/`merge_two'`/`chainFinish`/`chainFinishSame` helper lemmas, INCLUDING the
  case where the path revisits its own basepoint `Q` at an interior time before reaching `P`).
  Also exports the small standalone lemmas `isWeakSolutionAt_zero_of_ne`,
  `IsWeakSolutionAt.contMDiffAt_and_ne_zero_of_zero`, `IsWeakSolutionAt.contMDiffAt_of_nonneg`,
  `IsWeakSolutionAt.apply_eq_zero_of_ne_zero`, `IsWeakSolutionAt.congr_of_eventuallyEq`,
  `isWeakSolutionAt_one_zero` (all small, reusable "order ↔ smoothness/vanishing" bridges built
  along the way; none of these needed a manifold-specific `ContMDiffMul` instance — the file's own
  `contMDiffAt_mul_real` Compat, mirroring `WeakSolution.lean`'s `contMDiffAt_finsetProd_real`,
  routes every product through planar `ContDiffAt ℝ` in `extChartAt 𝓘(ℂ) x` instead).

**Consumer impact** (`abel-theorem`, #29): both the `k`-point/Finset use (§1.4,
`RS.Abel.exists_mero_of_periodVector_mem`, via the already-existing `exists_weakSolutionOfFinset`)
and the two-point sufficiency direction (§2.1, `RS.Abel.exists_mero_of_pathIntegral_mem`, via the
now-built `exists_weakSolutionOfPair` above) have everything they need from this unit.

## DAG audit (confirmed at build time)

`paths-and-integrals` (`Jacobian.Path`, now including `Jacobian.Path.Chain` for `ChartChain`) and
`planar-stokes-atoms` (`Jacobian.PlanarStokes`) are imported, matching the design's recommended
tightened `Builds on:` line (§2.5) plus the `ChartChain` dependency the general-chain gap closure
needed. No file here imports `Jacobian.Monodromy`, `Jacobian.FormTrace`, or `Jacobian.Meromorphic`.
-/
