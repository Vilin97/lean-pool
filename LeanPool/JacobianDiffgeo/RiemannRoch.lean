/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.RiemannRoch.Basic

/-!
# riemann-roch (#28): Riemann–Roch (namespace `RS`)

API summary (see `docs/design/serre-duality-tails.md` §9.1). Builds on `serre-duality-tails`
(BUILT, including its chiT-ledger closure — `TailDuality.chiT_eq_chiT_zero_add_degree`, the one
prerequisite this pass discharged). **Unit COMPLETE**: zero sorries, `scripts/check.sh
Jacobian/RiemannRoch` passes. **NOT registered in `Jacobian.lean`** (orchestrator's job).

A thin assembly unit — every proof is `omega`-level ℤ-arithmetic over `TailDuality`'s tail ledger
and Serre-duality export bank; no new mathematics, no reference to `T D`/`pairT`/`chi`'s internals.

## Exports (all in namespace `RS`)

* `chiT_zero : RS.TailDuality.chiT (0 : RS.Divisor X) = 1 - (genus X : ℤ)`.
* **`riemannRoch {ω₀ : RS.MForm X} (h₀ : ω₀ ≠ 0) (D : RS.Divisor X) : (RS.l D : ℤ) -
  (RS.l (RS.canonicalDivisorOf ω₀ - D) : ℤ) = D.degree + 1 - (genus X : ℤ)`** — Riemann–Roch.
* `l_K_eq_genus {ω₀} (h₀) : RS.l (RS.canonicalDivisorOf ω₀) = genus X`.
* `deg_canonical {ω₀} (h₀) : (RS.canonicalDivisorOf ω₀).degree = 2 * (genus X : ℤ) - 2`.
* **`riemann_inequality (D : RS.Divisor X) : (D.degree + 1 - (genus X : ℤ)) ≤ (RS.l D : ℤ)`** —
  unconditional (no reference form needed); the forward-headline seed `genus-zero-headline` (#30)
  consumes directly, at `D := single P 1` under `genus X = 0`.

## Consumer notes

* **cech-h1-genus (#27)**: does not need anything from here — it re-exports
  `TailDuality.h1T_zero_eq_genus` directly.
* **genus-zero-headline (#30)**: consumes `riemann_inequality` (forward direction: genus `0` ⇒
  `l(single P 1) ≥ 2`, extracting a function with a single simple pole).
-/
