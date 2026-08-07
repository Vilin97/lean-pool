/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LaurentTail.Comparison
import LeanPool.JacobianDiffgeo.Finiteness

/-!
# The Riemann–Roch bridge (laurent-tails, design §4.4) — DEFERRED, gated on `H1Tail.equiv` only

Unit: laurent-tails (`docs/design/laurent-tails.md` §4.4, §0).

**Status update (FINISHER pass): one of the two original gates is now open.**

1. **`Jacobian/Finiteness/Chi.lean` has landed** (confirmed: `Jacobian/Finiteness.lean`'s own root
   docstring records "Unit COMPLETE: all 7 design files are written, zero sorries"). The exact
   identifiers this file's completion recipe needs are all present and match the design doc's
   §4.4 plan verbatim: `RS.Finiteness.h1 (D : RS.Divisor X) : ℕ` and
   `RS.Finiteness.chi_eq_chi_zero_add_degree` (`Jacobian/Finiteness/Chi.lean`), plus
   `RS.Finiteness.finiteDimensional_H1` (`Jacobian/Finiteness/H1Finite.lean`, a global instance —
   registered there, so `H1Tail.finiteDimensional` below can cite it directly instead of
   re-deriving finite-dimensionality). This import is now safe to add (no cycle: `Finiteness`
   does not depend on `LaurentTail`).
2. **`Comparison.lean`'s `H1Tail.equiv` remains deferred** — but *only* on surjectivity of
   `tailToH1` now. This pass closed `tailToH1_alpha`, `H1Tail.toH1`, and
   `H1Tail.toH1_injective` (all unconditional, zero sorries); the sole remaining piece is
   `Function.Surjective (tailToH1 D)`, which `Comparison.lean`'s own file-end note now documents
   as a **proven-hard** analytic fact (comparable to a Mittag-Leffler/Cousin-I existence theorem,
   genuinely outside this unit's `Jacobian/LaurentTail/`-only edit surface — see that note for the
   full risk writeup and recommended next steps), not a bookkeeping gap. `Comparison.lean` ships
   a conditional `H1Tail.equivOfSurjective : Function.Surjective (tailToH1 D) →
   (H1Tail D ≃ₗ[ℂ] Cech.H1 D)` as an honest (non-vacuous, `CONVENTIONS.md` rule 3) placeholder for
   this file's own bridge to key off once surjectivity lands.

Since gate 2 is still closed, this file remains **empty of content** (a stub restating §4.4 now,
keyed off `H1Tail.equivOfSurjective` plus an unproved surjectivity hypothesis, would just move
the same open hypothesis here without discharging it — no more usable than leaving it absent, and
`CONVENTIONS.md` rule 3 prefers absence to a hypothesis-parametrized restatement that
adds a layer of indirection for zero benefit here, since the true blocker is identical either way).

**Completion recipe for whoever closes gate 2** (verbatim from the original design, still exactly
right — Chi.lean's landed names slot in directly, no changes needed):
```lean
noncomputable def g0 : ℕ := RS.Finiteness.h1 (0 : RS.Divisor X)
instance H1Tail.finiteDimensional (D) : FiniteDimensional ℂ (H1Tail D) :=
  Module.Finite.equiv (H1Tail.equiv D).symm
noncomputable def h1tail (D) : ℕ := Module.finrank ℂ (H1Tail D)
theorem h1tail_eq_h1 (D) : h1tail D = RS.Finiteness.h1 D := LinearEquiv.finrank_eq (H1Tail.equiv D)
theorem firstFormRR (D) : (RS.l D : ℤ) - (h1tail D : ℤ) = D.degree + 1 - (g0 : ℤ) := …
```
plus the tail-level six-term sequence (`exact_windowToT_H1Tail_mk`/`exact_H1Tail_mk_incl`,
conjugating `Cech`'s own six-term fragment by `H1Tail.equiv`) — every proof is a direct citation,
no new analysis, per the design doc §0/§6's own explicit recommendation not to re-derive
Miranda's finiteness route independently.
-/
