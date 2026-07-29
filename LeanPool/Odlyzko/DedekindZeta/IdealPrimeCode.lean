/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealEncoding
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain UniqueFactorizationMonoid

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- An ideal prime code used in the Odlyzko-bound argument. -/
noncomputable def idealPrimeCode (I : NonzeroIdeal K) : ℕ :=
  ((idealPrimeFactors K I).map (primeIdealCode K)).prod

lemma prime_mem_idealPrimeCode_factors (I : NonzeroIdeal K) :
    ∀ p ∈ (idealPrimeFactors K I).map (primeIdealCode K), p.Prime := by
  intro p hp
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.mp hp
  exact prime_primeIdealCode K P

lemma normalizedFactors_idealPrimeCode (I : NonzeroIdeal K) :
    normalizedFactors (idealPrimeCode K I) =
      (idealPrimeFactors K I).map (primeIdealCode K) := by
  apply normalizedFactors_prod_of_prime
  intro p hp
  exact Nat.prime_iff.mp (prime_mem_idealPrimeCode_factors K I p hp)

lemma idealPrimeCode_injective :
    Function.Injective (idealPrimeCode K) := by
  intro I J h
  apply (nonzeroIdealEquivPrimeFactors K).injective
  change idealPrimeFactors K I = idealPrimeFactors K J
  apply Multiset.map_injective (primeIdealCode_injective K)
  rw [← normalizedFactors_idealPrimeCode K I,
    ← normalizedFactors_idealPrimeCode K J, h]

end NumberField.Odlyzko
