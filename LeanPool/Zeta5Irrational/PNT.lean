/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.NumberTheory.Chebyshev
import LeanPool.MooreBound.PrimeNumberTheoremAnd.Consequences

/-! # The prime number theorem, imported from `PrimeNumberTheoremAnd`

The normalisation step (Proposition 5.2 of the paper) needs the prime number theorem in the
form `θ(x) ~ x` for Chebyshev's function `θ`. Mathlib does not contain it; the
`PrimeNumberTheoremAnd` development already preserved in `LeanPool.MooreBound` does.
-/

public section

open Filter Asymptotics

namespace Zeta5Irrational

/-- Chebyshev's function `θ(x) = ∑_{p ≤ x} log p` is asymptotic to `x`. -/
theorem theta_asymptotic : Chebyshev.theta ~[atTop] id :=
  MooreBound.chebyshev_asymptotic

end Zeta5Irrational
