/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesGCD
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.HahnSeriesGCDProof

/-! # Hahn Series GCDProof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn

universe u

namespace SeriesHasGCDs

/-- Every pair of series in `K((ℝ^{≤0}))` has a greatest common divisor. -/
theorem proof (K : Type u) [Field K] : SeriesHasGCDs K := by
  exact of_polynomiality K

end SeriesHasGCDs

namespace SeriesIsPrimal

/-- Every series in `K((ℝ^{≤0}))` is primal. -/
theorem proof (K : Type u) [Field K] : SeriesIsPrimal K := by
  exact of_gcds K

end SeriesIsPrimal

namespace SeriesIrreduciblesArePrime

/-- Every irreducible series is prime. -/
theorem proof (K : Type u) [Field K] : SeriesIrreduciblesArePrime K := by
  exact of_primality K

end SeriesIrreduciblesArePrime

namespace SeriesFactorizationsAreUnique

/-- Irreducible factorisations are unique up to order and units. -/
theorem proof (K : Type u) [Field K] : SeriesFactorizationsAreUnique K := by
  exact of_primality K

end SeriesFactorizationsAreUnique

end ConwayRefinement.Standalone.Hahn
