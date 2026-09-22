/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.SemiringFunctor

/-!
# Formal statements of the main results

This file fixes the logical meaning of the two main theorems before their proofs are attempted.
In particular, the threshold in the giant-orbit assertion may depend on `epsilon`, while the
constant in the lower bound for every orbit is absolute.
-/

namespace BGS.Markoff

/-- Punctured Markoff transitivity at a prime `p`: the Markoff group has one orbit on the
nonzero solutions modulo `p`. -/
def PuncturedMarkoffTransitiveAt (p : ℕ) (hp : p.Prime) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ x y : PuncturedMarkoffSurface (ZMod p), ∃ g : Gamma (ZMod p), g • x = y

/-- The complement size of the orbit of `x` inside the punctured surface over `ZMod p`. -/
noncomputable def orbitComplementCard {p : ℕ} [Fact p.Prime]
    (x : PuncturedMarkoffSurface (ZMod p)) : ℕ :=
  (Set.univ \ puncturedGammaOrbit x).ncard

/-- At `p`, there is an orbit whose complement has at most `p ^ epsilon` points. -/
def HasGiantOrbitAt (p : ℕ) (hp : p.Prime) (epsilon : ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∃ x : PuncturedMarkoffSurface (ZMod p),
    (orbitComplementCard x : ℝ) ≤ Real.rpow p epsilon

/-- A finite set containing an orbit complement bounds that complement's cardinality. -/
theorem orbitComplementCard_le_finset_of_subset
    {p : ℕ} [Fact p.Prime] (x : PuncturedMarkoffSurface (ZMod p))
    (bad : Finset (PuncturedMarkoffSurface (ZMod p)))
    (hbad : Set.univ \ puncturedGammaOrbit x ⊆ (bad : Set _)) :
    orbitComplementCard x ≤ bad.card := by
  rw [orbitComplementCard, ← Set.ncard_coe_finset bad]
  exact Set.ncard_le_ncard hbad

/-- The final giant-orbit conclusion once the complement has been put inside a counted set. -/
theorem hasGiantOrbitAt_of_complement_subset_finset
    (p : ℕ) (hp : p.Prime) (epsilon : ℝ)
    (x : PuncturedMarkoffSurface (ZMod p))
    (bad : Finset (PuncturedMarkoffSurface (ZMod p)))
    (hbad : Set.univ \ puncturedGammaOrbit x ⊆ (bad : Set _))
    (hcard : (bad.card : ℝ) ≤ Real.rpow p epsilon) :
    HasGiantOrbitAt p hp epsilon := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨x, ?_⟩
  have hnat := orbitComplementCard_le_finset_of_subset x bad hbad
  have hreal : (orbitComplementCard x : ℝ) ≤ bad.card := by
    exact_mod_cast hnat
  exact hreal.trans hcard

/-- At `p`, every punctured Markoff orbit has the asserted logarithmic lower bound. -/
def EveryOrbitLargeAt (p : ℕ) (hp : p.Prime) (c : ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ x : PuncturedMarkoffSurface (ZMod p),
    c * Real.rpow (Real.log p) (1 / ((3 : ℕ) : ℝ)) ≤ (puncturedGammaOrbit x).ncard

/-- The exact quantifier structure of Theorem 1 in arXiv:1607.01530v1. -/
def TheoremOneStatement : Prop :=
  (∀ epsilon : ℝ, 0 < epsilon →
      ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → HasGiantOrbitAt p hp epsilon) ∧
    ∃ c : ℝ, 0 < c ∧
      ∃ p0 : ℕ, ∀ (p : ℕ) (hp : p.Prime), p0 ≤ p → EveryOrbitLargeAt p hp c

/-- A prime is exceptional when strong approximation fails at that prime. -/
def IsExceptionalPrime (p : ℕ) : Prop :=
  p.Prime ∧ ¬ StrongApproximationAt p

/-- The number of exceptional primes at most `T`. -/
noncomputable def exceptionalPrimeCount (T : ℕ) : ℕ :=
  {p : ℕ | p ≤ T ∧ IsExceptionalPrime p}.ncard

/-- The exact quantifier structure of Theorem 2 in arXiv:1607.01530v1. -/
def TheoremTwoStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
      (exceptionalPrimeCount T : ℝ) ≤ Real.rpow T epsilon

end BGS.Markoff
