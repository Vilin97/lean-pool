/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LaurentTail.TailSpace
import LeanPool.JacobianDiffgeo.LaurentTail.Truncation
import LeanPool.JacobianDiffgeo.LaurentTail.Comparison
import LeanPool.JacobianDiffgeo.LaurentTail.RiemannRoch

/-!
# laurent-tails: Miranda's Laurent-tail calculus for `H¹(D)` (namespace `RS.LaurentTail`)

API summary (see `docs/design/laurent-tails.md`). Builds on `cech-cohomology` (BUILT) and
`meromorphic-and-divisors` (BUILT) only — the blueprint's listed `canonical-forms`/
`meromorphic-trace` edge is unused by this unit (§0 of the design doc; a DAG-imprecision note,
not a missing dependency). **NOT registered in `Jacobian.lean`** (orchestrator's job).

* **`TailSpace.lean`** (D1/D2/D4, zero sorries): `TailAt p D` (**`abbrev`**, germs at the chart
  source of `p` modulo `Cech.ordGe p (-(D p))`) + `TailAt.mk`/`mk_eq_zero_iff`/`mk_surjective`;
  `windowAtToTailAt`/`exists_windowAt_repr` (Cech's finite window embeds, every class has *some*
  finite representative); `T D := Π₀ p, TailAt p D` (**`abbrev`**, `[DecidableEq X]`) + `T.mk`/
  `mk_apply_mem`/`mk_apply_not_mem`; `windowToT` (the finite skyscraper `Window D D'` embeds in
  `T D`, `[CompactSpace X]`). `mulTailAt`/`mulTail`/`mulTailEquiv` (design §2 D5) are **not
  built** — `serre-duality-tails` explicitly de-scopes them (their own `mulInto`, built directly
  on this file's carrier, supersedes it; a genuine scope relief, not a shortfall).
* **`Truncation.lean`** (D3, zero sorries): `alphaFinset`/`alpha`/`alphaL : ℳ X →ₗ[ℂ] T D`
  (Miranda's truncation map, `[CompactSpace X][ConnectedSpace X][T1Space X][DecidableEq X]`),
  `alpha_apply` (the pointwise-everywhere formula, not just on the witness `Finset`),
  `alpha_apply_eq_zero_iff`, `ker_alphaL_eq_linSys` (Miranda PDF 192: `L(D) = ker(α_D)`),
  `H1Tail D := T D ⧸ range(alphaL D)` + `H1Tail.mk`/`mk_surjective`/`mk_eq_zero_iff`.
* **`Comparison.lean`** (CC8's deliverable — **three of four original deferrals now CLOSED**, see
  that file's own detailed file-end note for the exact account). `tailToH1 : T D →ₗ[ℂ] Cech.H1 D`
  is fully constructed (zero sorries) via a from-scratch per-point Mittag-Leffler class
  `mlClassAt`/`mlClassAtOf` (a 2-member-cover construction, independent of every choice via
  `mlClassAtOf_agree`). **`tailToH1_alpha`** (well-definedness on `alphaL`'s image, via a from-
  scratch multi-point Mittag-Leffler combination specialized to one global function) and
  **`H1Tail.toH1`/`H1Tail.toH1_injective`** (via a *second*, independent multi-point
  construction for an arbitrary tail datum, landing on `Cech.mlClass_eq_zero_iff`'s `⇒` half,
  Forster 12.4, confirmed landed) are now **fully proved, zero sorries, unconditional**.
  **Still deferred**: surjectivity of `tailToH1` — per the file-end note's detailed risk writeup,
  this is a *proven-hard* analytic fact (a Mittag-Leffler/Cousin-I-style existence theorem)
  genuinely beyond this unit's own `Jacobian/LaurentTail/`-only edit surface, **not** a
  bookkeeping gap despite `dolbeault-comparison`'s Leray theorem (`toH1_surjective_of_isGood`)
  having landed in the interim — Leray gets a good-cover representative but does not by itself
  collapse it to marked-point-supported Mittag-Leffler data. `H1Tail.equivOfSurjective` ships
  as an honest conditional equivalence (`Function.Surjective (tailToH1 D) → H1Tail D ≃ₗ[ℂ]
  Cech.H1 D`), ready the moment surjectivity lands. Reusable byproducts: a registered
  `AddCommGroup (Cech.H1 D)` instance (`instAddCommGroupH1`), `mlClass_congr` (dependent-argument
  transport for `Cech.mlClass`), and a documented build-engineering gotcha (composing an
  `Opens X`-level `≤` with a `Set X`-level `⊆` via bare `.trans` causes catastrophic `isDefEq`
  slowdown; coerce to `Set`-level first) worth knowing for any future large proof in this style.
* **`RiemannRoch.lean`** (design §4.4 — **still empty of declarations, but only one gate left**):
  `finiteness-and-chi`'s `Chi.lean` has **landed** (that gate is open); the sole remaining gate is
  `Comparison.lean`'s own `H1Tail.equiv` (blocked on surjectivity, see above). Every export it
  would provide (`g0`, `h1tail`, `h1tail_eq_h1`, `firstFormRR`, the tail-level six-term
  restatement) remains a one-line transport once that lands — no new mathematics — per that
  file's own completion recipe (verbatim, unchanged).

## Consumer notes (for `serre-duality-tails` and downstream)

The frozen bank this unit was asked to supply (`docs/design/serre-duality-tails.md` §0.1's own
audit already reconciled against these exact names): `T D`, `TailAt p D`, `alphaL D`,
`H1Tail D := T D ⧸ range(alphaL D)` are **all available now**, zero sorries, and match the frozen
shapes exactly. `H1Tail.toH1 : H1Tail D →ₗ[ℂ] Cech.H1 D` is now **unconditionally injective**
(`H1Tail.toH1_injective`, zero sorries) — only the full `H1Tail.equiv : H1Tail D ≃ₗ[ℂ] Cech.H1 D`
(needing surjectivity too) remains gated; `Comparison.lean` ships the conditional
`H1Tail.equivOfSurjective` (an honest, non-vacuous, hypothesis-parametrized equivalence) in the
meantime. `serre-duality-tails` should build everything that only needs `T D`/`TailAt p D`/
`alphaL`/`H1Tail D` now (per its own design doc §4's build-wave note: "file 1 gates only on
`TailSpace.lean`/`Truncation.lean` — NOT on `Comparison.lean`"), and revisit the full `H1Tail.equiv`
once surjectivity lands (see `Comparison.lean`'s file-end note for the exact analytic obstruction
and recommended next steps — this is now THE single blocking item for that unit's own
dimension-counting endgame). `mulTail`/`mulTailEquiv` are deliberately not built (see
`TailSpace.lean`'s note above); `serre-duality-tails`'s own `mulInto` supersedes them, already
accounted for in that unit's design. `firstFormRR`/`g0` remain gated on `H1Tail.equiv` too.
-/
