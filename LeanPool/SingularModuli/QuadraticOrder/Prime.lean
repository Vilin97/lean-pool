/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Prime.PolyMod
import LeanPool.SingularModuli.QuadraticOrder.Prime.QuotientIso
import LeanPool.SingularModuli.QuadraticOrder.Prime.Inert
import LeanPool.SingularModuli.QuadraticOrder.Prime.Ramified
import LeanPool.SingularModuli.QuadraticOrder.Prime.Split

/-!
# Layer 2a: Prime classification in `QuadraticOrder d`

**Thesis.** §3.2, Proposition 3.2.1 and Remark 3.2.3 — the split / inert /
ramified trichotomy of a rational prime `p` in the order `O_d`, governed by the
Kronecker / Legendre symbol `(d/p)`.

This module is the aggregator for the prime-classification development, which
is split one-result-per-concern across `Prime/`:

| file | content | thesis |
|------|---------|--------|
| `Prime/PolyMod`     | `polyMod d p`, root ↔ Legendre bridge | Prop 3.2.1 (poly) |
| `Prime/QuotientIso` | `O/(p) ≅ 𝔽ₚ[X]/(polyMod)`, `≅ 𝔽ₚ[X]/(X²)` | proof device |
| `Prime/Inert`       | `(p)` maximal ↔ `(d/p) = -1` | Prop 3.2.1 inert |
| `Prime/Ramified`    | `(p)` not radical ↔ `p ∣ d` | Prop 3.2.1 ramified |
| `Prime/Split`       | `(p)` radical, not maximal ↔ `(d/p) = 1` | Prop 3.2.1 split |

See `Prime/QuotientIso.lean` for the main *divergence from the thesis*: the
whole trichotomy is routed through one ring isomorphism rather than the
thesis's explicit index computations.
-/
