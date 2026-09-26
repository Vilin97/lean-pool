/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import LeanPool.NagataFactoriality.NagataFactoriality.Basic.Noetherian


/-!
# UFD

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

theorem ufd_iff_factorization_and_irreducibles_prime {α : Type*} [CommRing α] [IsDomain α] :
    UniqueFactorizationMonoid α ↔ WfDvdMonoid α ∧ ∀ p : α, Irreducible p → Prime p := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · let : UniqueFactorizationMonoid α := h
      exact (inferInstance : WfDvdMonoid α)
    · intro p hp
      let : UniqueFactorizationMonoid α := h
      exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hp
  · rintro ⟨hfac, hprime⟩
    exact UniqueFactorizationMonoid.of_exists_prime_factors (fun a ha => by
      let : WfDvdMonoid α := hfac
      obtain ⟨f, hf, hassoc⟩ := WfDvdMonoid.exists_factors a ha
      refine ⟨f, ?_, hassoc⟩
      intro b hb
      exact hprime b (hf b hb))

theorem prime_iff_irreducible_of_ufd {α : Type*} [CommRing α]
    [UniqueFactorizationMonoid α] {p : α} : Prime p ↔ Irreducible p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.symm

theorem ufd_of_factorization_and_primes {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) : UniqueFactorizationMonoid α := by
  exact (ufd_iff_factorization_and_irreducibles_prime (α := α)).2 ⟨hfac, hprime⟩

/-- Two factorizations are equivalent when they differ only by associates and permutation. -/
abbrev FactorizationEquivalent {α : Type*} [Monoid α] (f g : Multiset α) : Prop :=
  Multiset.Rel Associated f g

theorem factorizationEquivalent_iff_map_eq_map {α : Type*} [CommMonoid α] {f g : Multiset α} :
    FactorizationEquivalent f g ↔ f.map Associates.mk = g.map Associates.mk :=
  Associates.rel_associated_iff_map_eq_map

theorem factorization_unique {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p)
    {f g : Multiset α}
    (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    FactorizationEquivalent f g := by
  let : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
  exact UniqueFactorizationMonoid.factors_unique hf hg hfg

theorem factors_unique {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p)
    {a : α} (ha : a ≠ 0) {f : Multiset α}
    (hf : ∀ x ∈ f, Irreducible x)
    (hfa : Associated f.prod a) :
    let : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
    FactorizationEquivalent f (UniqueFactorizationMonoid.factors a) := by
  let : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
  exact UniqueFactorizationMonoid.factors_unique hf UniqueFactorizationMonoid.irreducible_of_factor
    (hfa.trans (UniqueFactorizationMonoid.factors_prod ha).symm)

end NagataFactoriality
