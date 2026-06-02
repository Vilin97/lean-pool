/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/

import LeanPool.TwoColoringOneRound.LowerBound.Defs
import LeanPool.TwoColoringOneRound.LowerBound.N1000000Main

/-!
# Public interface: the `n = 1_000_000` lower bound

This file is a **human-facing entry point**.

If you want a single module to import (or open in an editor) to see what is proved and what the
objects mean, use this file.

## The graph family

All combinatorial objects live in `Distributed2Coloring.LowerBound.Defs`:

* `Vertex n` is an injective triple of symbols `(a,b,c)` with values in `{0,1,…,n-1}`.
* `Edge n` is an injective quadruple `(a,b,c,d)` encoding the directed edge
  `(a,b,c) → (b,c,d)` via `Edge.src` and `Edge.dst`.
* `Coloring n := Vertex n → Bool` is a 2-coloring of vertices.
* `monoFraction f : ℚ` is the fraction of edges whose endpoints have equal color.

## The main theorem

The main claim proved in this project is:

* `Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879`

It states that for `n = 1_000_000`, every coloring has monochromatic-edge fraction at least
`23879/100000 = 0.23879`.
-/

namespace Distributed2Coloring.LowerBound


namespace N1000000Interface

/-- The concrete parameter used in the main theorem: `n = 1_000_000`. -/
abbrev n₀ : Nat := N1000000Data.n

/--
Convenience wrapper for the main theorem (to avoid re-declaring names from
`Distributed2Coloring.LowerBound.N1000000`).

See `Distributed2Coloring.LowerBound.N1000000.monoFraction_ge_23879`.
-/
theorem monoFraction_ge_23879 (f : Coloring n₀) :
    (23879 : ℚ) / 100000 ≤ monoFraction f := by
  simpa [n₀] using (N1000000.monoFraction_ge_23879 (f := f))

end N1000000Interface

end Distributed2Coloring.LowerBound
