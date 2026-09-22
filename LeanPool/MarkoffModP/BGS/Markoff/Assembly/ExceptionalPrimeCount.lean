/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Order.Interval.Set.Nat
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.DivisibleOrbitTransitivity
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.GiantOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Assembly.TransitivitySurjectivity

/-!
# Exceptional-prime consequences of Chen orbit divisibility

Chen's component-divisibility theorem, formalized here through Martin's later elementary proof,
upgrades the giant-orbit half of Theorem 1 to strong approximation at every sufficiently large
prime.  This file records the resulting finite exceptional-prime set and derives the subpower
exceptional-prime bound of Theorem 2.
-/

namespace BGS.Markoff

open Filter
open scoped Topology

/-- If strong approximation holds at every prime beyond `p0`, then at most `p0` primes are
exceptional below any cutoff. -/
theorem exceptionalPrimeCount_le_of_eventually_strongApproximationAt
    (p0 : ℕ)
    (hstrong : ∀ (p : ℕ), p.Prime → p0 ≤ p → StrongApproximationAt p)
    (T : ℕ) :
    exceptionalPrimeCount T ≤ p0 := by
  rw [exceptionalPrimeCount]
  calc
    {p : ℕ | p ≤ T ∧ IsExceptionalPrime p}.ncard ≤ (Set.Iio p0).ncard := by
      refine Set.ncard_le_ncard ?_ (Set.toFinite (Set.Iio p0))
      intro p hp
      change p ≤ T ∧ IsExceptionalPrime p at hp
      rcases hp.2 with ⟨hpPrime, hpFailure⟩
      change p < p0
      by_contra hpNotLt
      exact hpFailure (hstrong p hpPrime (Nat.le_of_not_gt hpNotLt))
    _ = p0 := Set.ncard_Iio_nat p0

/-- Eventual strong approximation implies the subpower exceptional-prime estimate of
`TheoremTwoStatement`. -/
theorem theoremTwoStatement_of_eventually_strongApproximationAt
    (hstrong : ∃ p0 : ℕ, ∀ (p : ℕ), p.Prime → p0 ≤ p → StrongApproximationAt p) :
    TheoremTwoStatement := by
  obtain ⟨p0, hp0⟩ := hstrong
  intro epsilon hepsilon
  have hEventually :
      ∀ᶠ T : ℕ in atTop, (p0 : ℝ) ≤ (T : ℝ) ^ epsilon :=
    ((tendsto_rpow_atTop hepsilon).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (p0 : ℝ))
  rw [eventually_atTop] at hEventually
  obtain ⟨T0, hT0⟩ := hEventually
  refine ⟨T0, fun T hT => ?_⟩
  have hcount : exceptionalPrimeCount T ≤ p0 :=
    exceptionalPrimeCount_le_of_eventually_strongApproximationAt p0 hp0 T
  have hcountReal : (exceptionalPrimeCount T : ℝ) ≤ p0 := by
    exact_mod_cast hcount
  exact hcountReal.trans (hT0 T hT)

/-- The giant-orbit half of Theorem 1 and Chen orbit divisibility, via Martin's proof, imply
eventual punctured finite-field transitivity. -/
theorem eventually_puncturedMarkoffTransitiveAt_of_theoremOneStatement
    (hOne : TheoremOneStatement) :
    ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p →
      PuncturedMarkoffTransitiveAt p hp := by
  exact eventually_puncturedMarkoffTransitiveAt_of_giantOrbit
    (1 / 2 : ℝ) (by norm_num) (hOne.1 (1 / 2 : ℝ) (by norm_num))

/-- Theorem 1 and Chen orbit divisibility, through Martin's proof, imply eventual strong
approximation after applying natural Markoff connectivity. -/
theorem eventually_strongApproximationAt_of_theoremOneStatement
    (hOne : TheoremOneStatement) :
    ∃ p0 : ℕ, ∀ (p : ℕ), p.Prime → p0 ≤ p → StrongApproximationAt p := by
  obtain ⟨p0, hp0⟩ :=
    eventually_puncturedMarkoffTransitiveAt_of_theoremOneStatement hOne
  refine ⟨p0, fun p hp hple => ?_⟩
  exact (puncturedMarkoffTransitiveAt_iff_strongApproximationAt p hp).mp
    (hp0 p hp hple)

/-- The general-interface form of eventual BGS Conjecture 1.

Theorem 1 and Chen's orbit-divisibility theorem, via Martin's proof, imply
strong approximation at every sufficiently large prime.  The parameter-free endpoint is
`BGS.Markoff.eventually_strongApproximationAt`. -/
theorem eventually_strongApproximationAt_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    ∃ p0 : ℕ, ∀ (p : ℕ), p.Prime → p0 ≤ p → StrongApproximationAt p :=
  eventually_strongApproximationAt_of_theoremOneStatement
    (theoremOneStatement_of_generalHasseWeil hHasse)

/-- Theorem 1 together with Chen's orbit-divisibility theorem, via Martin's elementary proof,
implies Theorem 2. -/
theorem theoremTwoStatement_of_theoremOneStatement
    (hOne : TheoremOneStatement) :
    TheoremTwoStatement :=
  theoremTwoStatement_of_eventually_strongApproximationAt
    (eventually_strongApproximationAt_of_theoremOneStatement hOne)

/-- The general-interface form of BGS Theorem 2.

The completed Theorem 1 assembly supplies the in-repository Corvaja--Zannier
estimate.  The parameter-free endpoint is
`BGS.Markoff.theoremTwoStatement`. -/
theorem theoremTwoStatement_of_generalHasseWeil
    (hHasse : BGS.External.GeneralBivariateAffineHasseWeilTheorem) :
    TheoremTwoStatement :=
  theoremTwoStatement_of_theoremOneStatement
    (theoremOneStatement_of_generalHasseWeil hHasse)

end BGS.Markoff
