/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnSeriesGCD
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# What follows from the primality of every series, in Mathlib's vocabulary

Every theorem below follows from the proposition `SeriesIsPrimal K` using Mathlib alone.

The consequences are the forms in which the theorem is used or quoted: `K((ℝ^{≤0}))` is
pre-Schreier (Mathlib's `DecompositionMonoid`); every irreducible series is prime; and any two
factorisations of a series into irreducibles agree up to order and units, the two multisets of
factors being related by association.
-/

public section

namespace ConwayRefinement.Standalone.Hahn

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- `K((ℝ^{≤0}))` is pre-Schreier: every element is primal, Mathlib's `DecompositionMonoid`. -/
theorem decompositionMonoid_of (h : SeriesIsPrimal K) : DecompositionMonoid (nonpos K) := by
  exact ⟨h inferInstance⟩

/-- Every irreducible series is prime. -/
theorem prime_of_irreducible_of (h : SeriesIsPrimal K) {a : nonpos K} (hirr : Irreducible a) :
    Prime a := by
  exact hirr.prime_of_isPrimal (h inferInstance a)

/-- Unique factorisation: two products of irreducibles that agree up to a unit have the same
factors up to order and association. -/
theorem factorization_unique_of (h : SeriesIsPrimal K) {f g : Multiset (nonpos K)}
    (hf : ∀ x ∈ f, Irreducible x) (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g := by
  exact prime_factors_unique (fun x hx ↦ prime_of_irreducible_of h (hf x hx))
    (fun x hx ↦ prime_of_irreducible_of h (hg x hx)) hfg

end ConwayRefinement.Standalone.Hahn

end
