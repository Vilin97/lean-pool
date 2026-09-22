/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesGCD
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Support.SeriesConsequences
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality

/-!
# Proofs of the Mathlib-only gcd and primality statements

The standalone ring `nonpos K` is `K((ℝ^{≤0}))`, the type `Berarducci.Series K` used by the proof
modules. The polynomial presentation supplies its GCD structure. The gcd operation proves
`SeriesHasGCDs`; Mathlib then turns the existence of gcds into a
`DecompositionMonoid`, proving `SeriesIsPrimal`.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn

universe u

namespace SeriesHasGCDs

/-- Every pair of series in `K((ℝ^{≤0}))` has a greatest common divisor. -/
theorem of_polynomiality (K : Type u) [Field K] : SeriesHasGCDs K := by
  intro hK
  letI := hK
  obtain ⟨hGCD⟩ := Berarducci.nonemptyGCDMonoid (K := K)
  letI : GCDMonoid (nonpos K) := hGCD
  intro a b
  refine ⟨gcd a b, fun e ↦ ?_⟩
  constructor
  · rintro ⟨hea, heb⟩
    exact dvd_gcd hea heb
  · intro hed
    exact ⟨hed.trans (gcd_dvd_left a b), hed.trans (gcd_dvd_right a b)⟩

end SeriesHasGCDs

namespace SeriesIsPrimal

/-- Every series in `K((ℝ^{≤0}))` is primal, as a consequence of the existence of gcds. -/
theorem of_gcds (K : Type u) [Field K] : SeriesIsPrimal K := by
  intro hK
  letI := hK
  letI : DecidableEq (nonpos K) := Classical.decEq _
  letI : GCDMonoid (nonpos K) :=
    gcdMonoidOfExistsGCD (SeriesHasGCDs.of_polynomiality K inferInstance)
  intro a
  exact DecompositionMonoid.primal a

end SeriesIsPrimal

namespace SeriesIrreduciblesArePrime

/-- Every irreducible series is prime. -/
theorem of_primality (K : Type u) [Field K] :
    SeriesIrreduciblesArePrime K := by
  intro hK
  letI := hK
  intro a ha
  exact prime_of_irreducible_of (SeriesIsPrimal.of_gcds K) ha

end SeriesIrreduciblesArePrime

namespace SeriesFactorizationsAreUnique

/-- Irreducible factorisations are unique up to order and units. -/
theorem of_primality (K : Type u) [Field K] :
    SeriesFactorizationsAreUnique K := by
  intro hK
  letI := hK
  intro f g hf hg hfg
  exact factorization_unique_of (SeriesIsPrimal.of_gcds K) hf hg hfg

end SeriesFactorizationsAreUnique

/-- The pre-Schreier, or `DecompositionMonoid`, structure on `K((ℝ^{≤0}))`. -/
instance (K : Type u) [Field K] [CharZero K] : DecompositionMonoid (nonpos K) :=
  decompositionMonoid_of (SeriesIsPrimal.of_gcds K)

end ConwayRefinement.Standalone.Hahn
