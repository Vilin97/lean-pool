/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.MeromorphicTrace.ToP1
import LeanPool.JacobianDiffgeo.MeromorphicTrace.OrderMultiplicity
import LeanPool.JacobianDiffgeo.MeromorphicTrace.ArgumentPrinciple
import LeanPool.JacobianDiffgeo.MeromorphicTrace.PlanarTrace
import LeanPool.JacobianDiffgeo.MeromorphicTrace.FunctionTrace

/-!
# meromorphic-trace: the argument principle and the fibre trace of functions (namespace `RS.MTrace`)

API summary (see `docs/design/meromorphic-trace.md`). Standing surface hypotheses throughout
(`CONVENTIONS.md`); `f g : X → ℂ`, `h : ℂ → ℂ` for the planar atom.

* **`toP1`** (`ToP1.lean`): `toP1 f : X → OnePoint ℂ` lifts a raw meromorphic `f` to a holomorphic
  map into `ℙ¹` (`∞` at poles, the punctured limit elsewhere); `toP1_contMDiff` is the honest
  holomorphy proof, routed through `meromorphic-and-divisors`'s `MeroGermOn.holoRepr` (built after
  this unit's design was frozen, so the proof is shorter than originally planned — see the file's
  deviation note). `NotEventuallyConstX`/`toP1_not_const` (D3) translate raw-`f`-side
  nonconstancy into `toP1 f`'s. Reusable `holoRepr`/`toP1` facts are exported for
  `OrderMultiplicity.lean`'s and `ArgumentPrinciple.lean`'s own use.
* **`OrderMultiplicity.lean`**: `multiplicity_toP1_of_ordAtX_pos`/`_neg` — the order↔multiplicity
  bridges at zeros/poles of `f` (CC4's multiplicity of `toP1 f`, read in `coeChart`/`invChart`,
  equals `f`'s vanishing order/pole order). The design's third claimed lemma
  (`ordAtX f x = 0 → multiplicity (toP1 f) x = 1`) is **mathematically false**
  (`f = 1 + z²` at `0`: order `0`, multiplicity `2`) and is not proved — see the file's deviation
  note; it is flagged in the design itself as non-essential.
* **`ArgumentPrinciple.lean`**: **THE argument principle**, `finsum_ordAtX_eq_zero` — for `f`
  meromorphic everywhere and nonconstant on compact connected `X`,
  `∑ᶠ x, (ordAtX f x).untop₀ = 0` (zeros cancel poles), via `fiberMultSum_eq_degree` at `0`/`∞` on
  `ℙ¹` (mapping-degree's counting engine — **not** the residue theorem/Stokes, per the design's
  routing warning). `sum_ordAtX_eq_zero_of_finite` is the `Finset` form; `finsum_ordAtX_eq_zero'`
  takes the raw `NotEventuallyConstX` hypothesis. This is the engine `proper-map-degree` needs for
  `deg(divisor f) = 0` — see the downstream note below for the exact repackaging.
* **`PlanarTrace.lean`** (pure planar, independent of the above): `traceZk h k w`, the trace of
  `h` along `z ↦ z ^ k` at `w`. `analyticAt_traceZk` (analyticity away from `0`, via local root
  branches, no monodromy), `meromorphicAt_traceZk` (meromorphy at `0`, via a norm/`zpow` growth
  bound + Riemann's removable-singularity theorem, the unit's hardest theorem),
  `traceZk_zpow` (closed form for monomial traces — the geometric-sum collapse, computed on the
  abstract root set, purely algebraically), and `laurentCoeffAt_traceZk` (P6, the
  Laurent-coefficient formula `laurentCoeffAt (traceZk h k) 0 m = k · laurentCoeffAt h 0 (k·m)`),
  proved `tsum`-free: exact finite Taylor remainder of the unit factor with the cutoff chosen so
  the remainder exponent is an exact multiple of `k` (so the remainder trace factors EXACTLY as
  `w^{s'} · traceZk r k w`, no second growth bound), `traceZk_zpow` on the finitely many
  monomials, and residue-calculus's presentation-independent `laurentCoeffAt_of_eventuallyEq`.
  **Zero sorries.**
* **`FunctionTrace.lean`**: `trace F h y₀` (`Tr_F h`, D7), the surface-level fibre trace, defined
  totally via an `if`-dispatch on `Nonempty (FiberStack F y₀)`. `trace_of_forall_eq` (the
  constant-`F` junk guard) is proved in full, including the case the design worried might need to
  stay an "open sub-case" (resolved via a short infiniteness-of-`X` argument).
  **Well-definedness (design risk R1) is resolved**: `trace_eq_finsum` identifies `trace F h y₀`
  with the naive fibre sum `∑ᶠ x ∈ F⁻¹{y₀}, h x` whenever ANY stack exists (so the
  `Classical.choice` of stack is immaterial), via `sum_traceZk_stack`, the `h`-weighted
  planar-to-fibre reindexing along the adapted-chart bijection (mapping-degree's `bijOn_e`
  pattern), valid over the stack's whole neighborhood `S.V`. `trace_eq_finsum'` (every point,
  holomorphic nonconstant `F`), `trace_eq_stack_sum` (read `trace` through an arbitrary stack on
  `S.V` — form-trace-tower's consumption shape), `trace_of_regular` (the design's sanity anchor),
  and `meromorphicAtX_trace` (P7, the design's centerpiece: `Tr_F h` is `MeromorphicAtX`
  everywhere on `Y`, via the stack formula + P5 + CC3 chart invariance) are all proved.

## Downstream notes

* **proper-map-degree** needs `deg(divisor f) = 0`: take `finsum_ordAtX_eq_zero`/
  `sum_ordAtX_eq_zero_of_finite` and repackage `(ordAtX f x).untop₀` as `divisor f` values (their
  own `Divisor`/`degree` bookkeeping) — the finsum/Finset-sum identity here is *exactly*
  `Divisor.degree`'s shape (`Function.locallyFinsuppWithin.degree`), so the repackaging is a
  rewrite, not a re-derivation.
* **form-trace-tower** needs the planar trace atom + its Laurent behavior, and `Tr_F h` as a
  black box: ALL of it is now ready — `traceZk`, `analyticAt_traceZk`, `meromorphicAt_traceZk`,
  `traceZk_zpow`, `laurentCoeffAt_traceZk` (P6, was the one blocked lemma; now proved);
  `RS.MTrace.trace`, `trace_of_forall_eq`, `trace_eq_finsum`/`trace_eq_finsum'`,
  `trace_eq_stack_sum` (the "fix one stack, read `trace` through it near `y₀`" shape its
  `resAtP1_trace_eq_sum` plan step 1 consumes), `trace_of_regular`, and `meromorphicAtX_trace`
  (needed for `Tr_F(h·ω)`'s own meromorphy).
* **laurent-tails (CC8)**: no direct edge (per the design, nothing here is laurent-tails-facing
  beyond what `residue-calculus`/`form-trace-tower` already mediate).
-/
