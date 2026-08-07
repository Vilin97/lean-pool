/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PeriodLattice.Membership
import LeanPool.JacobianDiffgeo.PeriodLattice.GenericPoints
import LeanPool.JacobianDiffgeo.PeriodLattice.Segment
import LeanPool.JacobianDiffgeo.PeriodLattice.FormIdentity
import LeanPool.JacobianDiffgeo.PeriodLattice.Nondegeneracy
import LeanPool.JacobianDiffgeo.PeriodLattice.Discreteness
import LeanPool.JacobianDiffgeo.PeriodLattice.FullRank

/-!
# period-lattice-rank: the period lattice is discrete and spans (Forster §21.1–21.4)

Unit: period-lattice-rank (`docs/design/period-lattice-rank.md`). The final deep analytic unit:
`Λ := RS.periodSubgroup X` is discrete and spans `Fin (genus X) → ℂ` over `ℝ`, i.e. `Λ` is a real
lattice of rank `2·genus X` — the two facts `jacobian-construction`'s instance ledger
(`Jacobian/JacobianConstruction/Basic.lean:104-121`) needs to fire `ChartedSpace`/`IsManifold`/
`LieAddGroup`/`CompactSpace (Jacobian X)` unconditionally.

## Route (dissection-free, per the blueprint's ⚠)

* **Discreteness** (Forster 21.3–21.4(a)(b)): `genus X` *generic points* `a : Fin (genus X) → X`
  (`GenericPoints.lean`) give disjoint coordinate charts; the **local Jacobi map**
  `𝔉 : ℂ^g → ℂ^g` (planar primitives of the basis forms) has invertible derivative at the center
  (the generic-point matrix, Cramer/`det_genericMatrix_ne_zero`), so the inverse function theorem
  makes `𝔉` open at `0`. If a period landed in the image without being `0`, Abel's `k`-point
  sufficiency direction produces a meromorphic function with prescribed simple zeros/poles there,
  and the residue theorem applied to `f • ωᵢ` contradicts invertibility of that same matrix
  (`Discreteness.lean`).
* **Nondegeneracy** (Forster 21.4(c)): the **maximum principle**, *not* Forster's `L²`-orthogonality
  chain (19.4–19.8, which needs a chart-independent 2-form integral this project does not build):
  a real primitive of a form with vanishing real periods attains a max on compact `X`; the complex
  open mapping theorem forces the local holomorphic primitive to be locally constant there, and the
  identity theorem (`FormIdentity.lean`) propagates this to the whole form (`Nondegeneracy.lean`).
  **Ungated** — no Hodge, no de Rham, no dissection, no 2-form integral, no partition of unity.
* **Full rank** (`FullRank.lean`): the linear-algebra shell around nondegeneracy (a nonzero real
  functional vanishing on `Λ` would complexify to a nonzero form with vanishing real periods).
  **Ungated.**

## Hypothesis-gating status (read before consuming any theorem below)

Discreteness is the **only** gated content in this unit, on `RS.Abel.WeakSolutionUpgradeFinset`
(abel-theorem's own remaining, precisely-isolated, non-external hypothesis — the external
`serre-duality-tails` blocker has already cleared; see `Jacobian/Abel.lean`'s docstring). Since
`WeakSolutionUpgradeFinset X ι` needs its index type `ι` explicit (a universe gotcha: binding it
under an inner `∀ {ι}` inside a `def` gives it a fresh, unrelated universe — documented in
`Jacobian/Abel/Sufficiency.lean`), this unit threads it as:
```
abbrev RS.DiscretenessHyp (X) [...] : Prop :=
  ∀ S : Finset (Fin (genus X)), RS.Abel.WeakSolutionUpgradeFinset X (↥S : Type)
```
Every theorem taking `(hupgrade : DiscretenessHyp X)` is gated **exactly** by this hypothesis and
nothing else; discharges automatically, no further code, the moment a sibling pass proves
`DiscretenessHyp X` unconditionally for every `X`.

**Gated** (take `hupgrade : DiscretenessHyp X`): `exists_isolating_nhds_periodSubgroup`,
`discreteTopology_periodSubgroup`, `periodSubgroup_topologicalClosure_eq`,
`discreteTopology_periodSubgroup_topologicalClosure`, `isZLattice_periodSubgroup_topologicalClosure`
(also needs the closure's `DiscreteTopology` in scope for its very statement to elaborate — see
that theorem's `haveI`-in-type shape), `finrank_int_periodSubgroup`.

**Ungated**: everything in `Membership.lean`, `GenericPoints.lean`, `Segment.lean`,
`FormIdentity.lean`, `Nondegeneracy.lean` (in particular `form1_eq_zero_of_re_period_eq_zero`), and
`FullRank.lean`'s `span_real_periodSubgroup`.

## Statement bank (file map)

* `Membership.lean`: `RS.periodRange`, `RS.periodSubgroup_eq_periodRange`,
  `RS.mem_periodSubgroup_iff` (a period-subgroup element is the period vector of a *single* loop —
  needed so Stage C of `Discreteness.lean` gets one loop to feed Abel, not an abstract closure
  element). Ungated.
* `GenericPoints.lean` (Forster 21.3): `RS.evalAtₗ`, `RS.isOpen_coeffAt_ne_zero`,
  `RS.exists_coeffAt_ne_zero_notMem`, `RS.genericKernel` (+ `mem_genericKernel`/`_anti`/`_empty`),
  `RS.exists_finset_card_finrank_le`, `RS.exists_genericPoints`, `RS.det_genericMatrix_ne_zero`.
  Ungated.
* `Segment.lean`: `RS.segmentPath`, `RS.pathIntegral_segmentPath` — the shared in-chart
  straight-segment helper used by both `Discreteness.lean` (Stage C) and `Nondegeneracy.lean`
  (step 2). Ungated.
* `FormIdentity.lean`: `RS.form1_eq_zero_of_eventually_coeffIn_zero` (clopen propagation of local
  vanishing to global vanishing). Ungated.
* `Nondegeneracy.lean`: `RS.form1_eq_zero_of_re_period_eq_zero` (Forster 21.4(c), the maximum
  principle route). Ungated.
* `Discreteness.lean`: `RS.DiscretenessHyp`, `RS.exists_isolating_nhds_periodSubgroup`,
  `RS.discreteTopology_periodSubgroup`, `RS.periodSubgroup_topologicalClosure_eq`,
  `RS.discreteTopology_periodSubgroup_topologicalClosure`. All gated on `DiscretenessHyp X`.
* `FullRank.lean`: `RS.span_real_periodSubgroup` (ungated), `RS.isZLattice_periodSubgroup_
  topologicalClosure` (gated), `RS.finrank_int_periodSubgroup` (gated, the blueprint's "real basis
  of rank `2g`" bonus, via mathlib's `ZLattice.rank`).

## Final-assembly-facing discharge shape

Once a sibling pass proves `hproof : RS.DiscretenessHyp X` unconditionally (for the actual `X` in
play, or `∀ X, ...`), final assembly registers exactly:
```lean
instance : DiscreteTopology (RS.periodSubgroup X).topologicalClosure :=
  RS.discreteTopology_periodSubgroup_topologicalClosure hproof
instance : IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule :=
  RS.isZLattice_periodSubgroup_topologicalClosure hproof
```
and `jacobian-construction`'s `Jacobian.instChartedSpace`/`instIsManifold`/`instLieAddGroup`/
`instCompactSpace` (`docs/Jacobian_challenge.lean:78-89`) all fire by instance search alone — no
further code in this unit or in `jacobian-construction`. No other unit consumes this one (a DAG
leaf apart from final assembly), except that `periodSubgroup_topologicalClosure_eq` is also of
direct interest to `abel-theorem`'s `ofCurve_inj`/`ofCurve_eq_of_path` consumers, who want to strip
`.topologicalClosure` from `Jac₀`'s defining quotient once discreteness is unconditional.
-/
