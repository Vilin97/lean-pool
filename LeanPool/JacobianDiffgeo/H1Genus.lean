/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.H1Genus.Basic

/-!
# cech-h1-genus (#27): `dim H¹(X, 𝒪) = g` (namespace `RS`)

API summary (see `Basic.lean`'s own docstring and `docs/design/serre-duality-tails.md` §9.2).
Builds on `serre-duality-tails` (BUILT). **Unit COMPLETE** (thin re-export, per the orchestrator's
own framing — the blueprint's suggested cup-product/monotonicity machinery is unnecessary on the
Laurent-tail route this project took): zero sorries, `scripts/check.sh Jacobian/H1Genus` passes.
**NOT registered in `Jacobian.lean`** (orchestrator's job).

## Exports

* **`RS.finrank_H1Tail_zero_eq_genus : Module.finrank ℂ (RS.LaurentTail.H1Tail
  (0 : RS.Divisor X)) = genus X`** — the tail-level `dim H¹(X, 𝒪) = g`, re-exported from
  `RS.TailDuality.h1T_zero_eq_genus`.

**Documented as open/optional** (does not block anything downstream — the challenge API never
mentions Čech cohomology): the literal Čech-level statement `RS.Finiteness.h1 0 = genus X` is not
produced, since it needs `H1Tail.equiv`'s full (unconditional) comparison, itself gated on
`tailToH1`'s surjectivity — a hard, out-of-scope analytic fact per `serre-duality-tails`'s own
addendum. See `Basic.lean`'s docstring for the full account.
-/
