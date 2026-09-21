/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Support

/-!
# Existence of a minimal support prime

A nontrivial finite module over a commutative Noetherian ring has a prime in
its support which is minimal among the support primes.
-/

namespace AlgebraicAnalysis.MinimalSupportExistence

noncomputable section

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
theorem exists_minimal_support_prime
     [Module.Finite R U] [Nontrivial U] :
    ∃ q : PrimeSpectrum R,
      q ∈ Module.support R U ∧
        ∀ p ∈ Module.support R U, p.asIdeal ≤ q.asIdeal →
          q.asIdeal ≤ p.asIdeal := by
  have hann : Module.annihilator R U ≠ ⊤ := by
    intro h
    have hs : Subsingleton U := Module.annihilator_eq_top_iff.mp h
    exact not_subsingleton_iff_nontrivial.mpr inferInstance hs
  obtain ⟨q, hq⟩ :=
    (Module.annihilator R U).nonempty_minimalPrimes hann
  let Q : PrimeSpectrum R := ⟨q, hq.1.1⟩
  refine ⟨Q, Module.mem_support_iff_of_finite.mpr hq.1.2, ?_⟩
  intro p hp hpq
  exact hq.2
    ⟨p.isPrime, Module.mem_support_iff_of_finite.mp hp⟩ hpq


end
end AlgebraicAnalysis.MinimalSupportExistence
