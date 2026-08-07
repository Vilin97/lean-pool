/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.TailDuality

/-!
# cech-h1-genus (#27): `dim H¹(X, 𝒪) = g` at the tail level

Unit: cech-h1-genus (#27), per the orchestrator addendum recorded in
`docs/design/serre-duality-tails.md` §9.2 and the `TailDuality` root docstring's consumer notes.

**A thin re-export, per the orchestrator's framing.** The blueprint's own suggested machinery
(cup-product kill, monotonicity, effective-divisor vanishing comparison, Forster §17.4–17.5) is
**unnecessary** on the route this project took: `serre-duality-tails` already proves the numerical
identification `finrank (H1Tail 0) = genus X` (`RS.TailDuality.h1T_zero_eq_genus`) directly, as
part of its Serre-duality export bank (`i_neg_eq_h1T` at `D = 0`, composed with canonical-forms'
`genus_eq_finrank_omegaSpace_zero`). This file just restates that fact at cech-h1-genus's own
"headline" name.

**Open/optional** (documented, not blocking): the literal Čech-cohomology statement
`RS.Finiteness.h1 (0 : RS.Divisor X) = genus X` is **not** produced here — it would need
`RS.LaurentTail.H1Tail.equiv : H1Tail D ≃ₗ RS.Cech.H1 D` (the full, unconditional comparison),
which is gated on `tailToH1`'s surjectivity, a genuinely hard (classically Serre-circular / Cousin
I-flavored) analytic fact that `laurent-tails`'s own build pass left open and which is out of
scope for this challenge (per the orchestrator's 2026-07-08 addendum). Only the CONDITIONAL
`RS.LaurentTail.H1Tail.equivOfSurjective` exists upstream. The challenge API itself never
mentions Čech `H¹` — this gap does not block anything else in this project.
-/

open scoped ContDiff Manifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-- **`dim H¹(X, 𝒪) = g`**, at the tail level: `finrank (H1Tail 0) = genus X`. Re-exported at the
unit's own headline name (`RS.TailDuality.h1T_zero_eq_genus` is the underlying fact, unfolding
`RS.TailDuality.h1T (0 : RS.Divisor X) := Module.finrank ℂ (RS.LaurentTail.H1Tail 0)`). -/
theorem finrank_H1Tail_zero_eq_genus :
    Module.finrank ℂ (RS.LaurentTail.H1Tail (0 : RS.Divisor X)) = genus X :=
  RS.TailDuality.h1T_zero_eq_genus

end RS
