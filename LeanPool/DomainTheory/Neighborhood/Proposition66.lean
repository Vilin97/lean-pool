/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition63

/-!
# Lecture VI — Proposition 6.6 (Scott 1981, PRG-19): initial algebras are uniquely
isomorphic

**Proposition 6.6.** Any two initial `T`-algebras are uniquely isomorphic.

The proof is the standard diagram chase. If `A` and `B` are both initial,
initiality gives unique
homomorphisms `f : A → B` and `g : B → A`. Their composites `g ∘ f : A → A` and `f
∘ g : B → B` are
homomorphisms, and by uniqueness of homomorphisms out of an initial algebra they
must equal the
identity homomorphisms. Hence the underlying morphisms of `f` and `g` are mutually
inverse, giving an
isomorphism `A.carrier ≅ B.carrier`. The isomorphism is *unique* in that the
homomorphism `A → B`
realising it is the only one (`iso_hom_unique`).

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj} {A B : TAlgebra T}

/-- Composing the two unique homomorphisms `A → B → A` gives the identity
homomorphism on the
initial
algebra `A`. -/
theorem comp_desc_eq_id (hA : IsInitial A) (hB : IsInitial B) :
    (hB.desc A).comp (hA.desc B) = AlgHom.id A := by
  rw [hA.uniq A ((hB.desc A).comp (hA.desc B)), hA.uniq A (AlgHom.id A)]

/-- **Proposition 6.6 (Scott 1981, PRG-19).** Any two initial `T`-algebras have
isomorphic carriers;
the isomorphism is built from the unique homomorphisms in both directions. -/
def initialIso (hA : IsInitial A) (hB : IsInitial B) : Iso A.carrier B.carrier where
  hom := (hA.desc B).hom
  inv := (hB.desc A).hom
  hom_inv_id := by
    have h := comp_desc_eq_id hA hB
    have := congrArg AlgHom.hom h
    simpa using this
  inv_hom_id := by
    have h := comp_desc_eq_id hB hA
    have := congrArg AlgHom.hom h
    simpa using this

/-- The isomorphism of Proposition 6.6 is **unique**: the homomorphism `A → B`
realising it is the
only homomorphism between the two initial algebras. -/
theorem iso_hom_unique (hA : IsInitial A) (h : AlgHom A B) : h = hA.desc B :=
  hA.uniq B h

end Domain.Neighborhood
