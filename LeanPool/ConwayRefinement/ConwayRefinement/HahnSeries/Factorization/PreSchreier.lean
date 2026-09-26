/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.FiniteSupportFactorUniqueness
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Pre-Schreier reduction from LM24 factorisation

This module proves the factorisation-theoretic reduction used in LM24, Corollary 6.4.2. If every
finite-support factor is primal, every irreducible infinite-support factor is prime, and every
nonzero series has the factorisation supplied by Theorem 6.4.1, then the full Hahn-series ring is
a decomposition monoid, equivalently a pre-Schreier domain in the terminology of the paper.
-/

open scoped HahnSeries

universe v

namespace Berarducci

public noncomputable section

variable {K : Type v} [Field K]

/-- A product list of prime elements is primal. -/
theorem list_prod_isPrimal_of_prime
    (factors : List (Series K))
    (hfactors : ∀ c ∈ factors, Prime c) :
    IsPrimal factors.prod := by
  induction factors with
  | nil => simpa using isUnit_one.isPrimal
  | cons c factors ih =>
      rw [List.prod_cons]
      exact (hfactors c (by simp)).isPrimal.mul
        (ih (fun d hd ↦ hfactors d (by simp [hd])))

/-- Factorisation into a primal finite-support factor and prime infinite-support factors makes
every series primal. -/
theorem decompositionMonoid_of_infiniteSupportFactorization
    (hfinitePrimal : ∀ p : FiniteSupportRing (K := K), IsPrimal (p : Series K))
    (hfactorization : ∀ b : Series K, b ≠ 0 →
      ∃ (p : FiniteSupportRing (K := K)) (factors : List (Series K)),
        IsInfiniteSupportIrreducibleFactorization b p factors)
    (hinfinitePrime : ∀ c : Series K,
      Irreducible c → (c : K⟦ℝ⟧).support.Infinite → Prime c) :
    DecompositionMonoid (Series K) := by
  constructor
  intro b
  by_cases hb : b = 0
  · subst b
    exact isPrimal_zero
  · obtain ⟨p, factors, hfactorization⟩ := hfactorization b hb
    have hfactorization' :=
      (isInfiniteSupportIrreducibleFactorization_iff b p factors).mp hfactorization
    rw [hfactorization'.1]
    exact (hfinitePrimal p).mul
      (list_prod_isPrimal_of_prime factors fun c hc ↦
        hinfinitePrime c (hfactorization'.2 c hc).1 (hfactorization'.2 c hc).2)

end

end Berarducci
