/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.FormTrace.PairForm
import LeanPool.JacobianDiffgeo.FormTrace.TraceZkForm
import LeanPool.JacobianDiffgeo.FormTrace.ResidueTraceCompat

/-!
# form-trace-tower: pair-form residues and residue-trace compatibility (namespace `RS.FormTrace`)

Unit: form-trace-tower (`docs/design/form-trace-tower.md`). Builds on `meromorphic-trace`
(complete). Fibrewise trace tower for pair-forms `h·F^*(dz)` along `F : X → Y`: pair-form
residues, chart handling, and residue-trace compatibility (Miranda Lemma 3.2 globalized).

**Three design bugs were found and corrected/documented during construction — read before use:**

1. **`resAtX`'s target-chart invariance is FALSE in general** (`PairForm.lean`). The design's
   `resAtX_eq_of_mem_source` claimed `resAtX` may be recomputed in an arbitrary pair of
   maximal-atlas charts with no correction. Counterexample: `X=Y=ℂ`, `F=id`, `h=1/z`, comparing
   target chart `id` vs `y↦2y` gives residue `1` vs `2`. Only the SOURCE-chart half survives as
   a general, exported fact: `resAtX_eq_of_mem_source_left`.
2. **The main theorem needs an explicit calibration hypothesis** (`ResidueTraceCompat.lean`).
   `resAtP1_trace_eq_sum` (Miranda Lemma 3.2 globalized) is proved, but — because of finding
   (1) — it takes an extra hypothesis `hcal` asserting the `FiberStack`'s adapted target charts
   are translates of `chartAt ℂ y₀`. This is satisfied by any stack from `exists_fiberStack`
   (verified by reading `exists_adaptedChartsAt`'s construction directly), but is NOT derivable
   from the abstract `FiberStack`/`AdaptedChartsAt` structure fields alone.
3. **`trace_eq_zero_of_holomorphic` (design's `HolomorphicVanishing.lean`) is FALSE, and was NOT
   built.** `RS.MTrace.trace` is the UNWEIGHTED fibre sum (`trace_eq_finsum'`, mtrace, zero
   sorries, unconditional). For constant `h ≡ 1` (globally holomorphic on compact `X` — such `h`
   is automatically constant by the maximum-modulus principle, so this is not a degenerate case)
   and ANY nonconstant `F : X → ℙ¹`, `trace F h` equals `degree F` at regular values but only the
   (strictly smaller, by Riemann–Hurwitz, since branch points always exist for `deg ≥ 2` maps to
   `ℙ¹`) fibre CARDINALITY at branch values — i.e. `trace F h` is not even continuous at a branch
   point unless `h` vanishes there, let alone identically `0`. This is a genuine defect in the
   design's plan for Miranda's "integration of a trace" ingredient (Item 5), not a proof-effort
   gap: fixing it would need a materially different object (a genuinely Jacobian-weighted trace
   of the FORM, not the bare function trace `D1` deliberately avoided introducing) — flagged
   LOUDLY for the orchestrator / a future builder, not attempted here. `RationalOnP1.lean` (the
   other file gated behind similar bonus/non-load-bearing status, §0.3 of the design) was also
   not built, for time-budget reasons (lowest priority per the design itself).

## What IS here, zero sorries

* `PairForm.lean`: `resAtX F h x` (D2, the residue of `h·F^*(dz)` at `x`, preferred charts),
  `resAtX_eq_of_mem_source_left` (source-chart invariance, task item 1's true content),
  `resAtX_congr`/`resAtX_add`/`resAtX_const_mul`.
* `TraceZkForm.lean`: `traceZkForm h k w` (D3, the Jacobian-weighted planar trace atom),
  `traceZkForm_hAdapted_eq_apply` (the cancellation identity, `w ≠ 0` form),
  `meromorphicAt_traceZkForm`, `laurentCoeffAt_traceZkForm`, `resAt_traceZkForm` (all
  unconditional now that mtrace's P6 has landed).
* `ResidueTraceCompat.lean`: `resAtP1` (D4), `resAtP1_eq_resAtX_id`, **`resAtP1_trace_eq_sum`**
  (THE main theorem, Miranda Lemma 3.2 globalized, with the `hcal` hypothesis above),
  `trace_const_mul_pullback` (Miranda Problem VIII.3.D, unconditional — no chart issue),
  `trace_pullback_eq_degree_smul_of_regular` (the `Tr∘F^* = deg·id` projection formula,
  restricted to regular values — the design's unconditional claim is ALSO false at branch points,
  same root cause as finding 3 above, but the regular-value case is clean and still useful).

## Notes for downstream consumers

* **`abel-weak-solutions`** (the only DAG-wired consumer): gets `resAtX`,
`resAtX_eq_of_mem_source_left`,
  `resAtP1`, `resAtP1_trace_eq_sum` (with `hcal`), `trace_const_mul_pullback`. Does **NOT** get
  `trace_eq_zero_of_holomorphic` — if the "necessity of Abel's theorem via genus-0" route is
  actually needed, it must be re-derived against a corrected object (see finding 3); check with
  the orchestrator before assuming this gap is filled elsewhere.
* **`jacobian-functoriality`** (`#33`, not a current blueprint unit): `trace_const_mul_pullback`
  and `trace_pullback_eq_degree_smul_of_regular` are the projection-formula facts requested;
  the latter is regular-value-only (see finding 3's twin issue).
* **`serre-duality-tails`**: nothing from this unit is DAG-wired to it (confirmed by the design's
  own §0.3 audit; unaffected by any of the findings above).
-/
