/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeFactorization
public import Mathlib.Data.Nat.Prime.Nth

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable instance countableIdealRingOfIntegers :
    Countable (Ideal (𝓞 K)) := by
  letI (n : ℕ) : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  exact Countable.of_equiv
    ((n : ℕ) × {I : Ideal (𝓞 K) // absNorm I = n})
    (Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ))

noncomputable instance countableHeightOneSpectrum :
    Countable (HeightOneSpectrum (𝓞 K)) :=
  HeightOneSpectrum.asIdeal_injective.countable

noncomputable instance encodableHeightOneSpectrum :
    Encodable (HeightOneSpectrum (𝓞 K)) :=
  Encodable.ofCountable _

/-- A prime ideal code used in the Odlyzko-bound argument. -/
noncomputable def primeIdealCode (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.nth Nat.Prime (Encodable.encode P)

lemma prime_primeIdealCode (P : HeightOneSpectrum (𝓞 K)) :
    Nat.Prime (primeIdealCode K P) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

lemma primeIdealCode_injective :
    Function.Injective (primeIdealCode K) :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).injective.comp
    Encodable.encode_injective

/-- A prime ideal code embedding used in the Odlyzko-bound argument. -/
noncomputable def primeIdealCodeEmbedding :
    HeightOneSpectrum (𝓞 K) ↪ Nat.Primes where
  toFun P := ⟨primeIdealCode K P, prime_primeIdealCode K P⟩
  inj' := fun _ _ h ↦ primeIdealCode_injective K (Subtype.ext_iff.mp h)

end NumberField.Odlyzko
