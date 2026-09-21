/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import LeanPool.NagataFactoriality.NagataFactoriality.Nagata.Lemmas

/-!
# Theorem

Supporting results for Nagata’s factoriality theorem.
-/

namespace NagataFactoriality

theorem nagata_theorem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          let : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  let : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  let : UniqueFactorizationMonoid (Localization S) := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_primeGenerated_isLocalization
      (S := S) (β := Localization S) hS hp)

theorem nagata_theorem_isLocalization {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) [CommRing T] [Algebra R T] [_root_.IsLocalization S T]
    [IsDomain T] (hS : PrimeGenerated S) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  let : UniqueFactorizationMonoid T := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_primeGenerated_isLocalization (S := S) (β := T) hS hp)

theorem nagata_theorem_of_prime_generators {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure s))
        (by
          let hS : PrimeGenerated (Submonoid.closure s) := primeGenerated_closure_of_primes hs
          let : Fact ((0 : R) ∉ Submonoid.closure s) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem (R := R) (Submonoid.closure s) (primeGenerated_closure_of_primes hs) hUFD

theorem nagata_theorem_of_prime_generators_isLocalization {R T : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure s) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_isLocalization (R := R) (T := T) (Submonoid.closure s)
    (primeGenerated_closure_of_primes hs) hUFD

theorem nagata_theorem_of_finite_prime_generators {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Finset R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure (↑s : Set R)))
        (by
          let hS : PrimeGenerated (Submonoid.closure (↑s : Set R)) :=
            primeGenerated_closure_finset_of_primes s hs
          let : Fact ((0 : R) ∉ Submonoid.closure (↑s : Set R)) :=
            ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_of_prime_generators (R := R) (s := (↑s : Set R)) (fun q hq => hs q hq) hUFD

theorem nagata_theorem_of_finite_prime_generators_isLocalization {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : Finset R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure (↑s : Set R)) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_of_prime_generators_isLocalization (R := R) (T := T) (s := (↑s : Set R))
    (fun q hq => hs q hq) hUFD

theorem nagata_theorem_of_prime_or_unit {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          let : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  let : Fact ((0 : R) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
  let : UniqueFactorizationMonoid (Localization S) := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_isLocalization
      (S := S) (β := Localization S) hS hp)

theorem nagata_theorem_of_prime_or_unit_isLocalization {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Submonoid R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization S T] [IsDomain T]
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  let : UniqueFactorizationMonoid T := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_isLocalization (S := S) (β := T) hS hp)

theorem ufd_of_factorization_and_prime_irreducibles {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) :
    UniqueFactorizationMonoid α :=
  ufd_of_factorization_and_primes hfac hprime

end NagataFactoriality
