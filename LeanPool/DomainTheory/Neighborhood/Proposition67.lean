/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition63

/-!
# Lecture VI — Proposition 6.7 (Scott 1981, PRG-19): Lambek's lemma

**Proposition 6.7.** If `i : T(D) → D` is an initial `T`-algebra, then so is `T(i)
: T²(D) → T(D)`
and `i` is the isomorphism from `T(D)` to `D`.

We formalise the second (and decisive) half: the structure map of an initial
algebra is an
isomorphism. Writing `A = (D, i)`, the functor turns `i` into a new algebra
`(T(D), T(i))` (`tStr`),
and `i` itself is a homomorphism `(T(D), T(i)) → (D, i)` (`strHom`). Initiality
supplies a
homomorphism `j : (D,i) → (T(D),T(i))`, and the composite `i ∘ j : (D,i) → (D,i)`
must be the
identity (`str_comp_desc`). Functoriality then gives `T(i) ∘ T(j) = T(i ∘ j) = I`,
and the
homomorphism square for `j` yields `j ∘ i = I`. Hence `i` and `j` are mutually
inverse: `i` is an
isomorphism (`lambek`).

This is exactly Scott's remark that "if we are going to have initial algebras at
all we have to
satisfy the domain equation `D ≅ T(D)`".

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

universe u

variable {Obj : Type u} [Category Obj] {T : Endofunctor Obj}

/-- For an algebra `A = (D, i)`, the functor turns the structure map into a new
`T`-algebra
`(T(D), T(i))`. -/
def tStr (A : TAlgebra T) : TAlgebra T where
  carrier := T.obj A.carrier
  str := T.map A.str

/-- The structure map `i : T(D) → D` is itself a homomorphism `(T(D), T(i)) → (D,
i)`: the square
`i ∘ T(i) = i ∘ T(i)` commutes trivially. -/
def strHom (A : TAlgebra T) : AlgHom (tStr A) A where
  hom := A.str
  comm := rfl

/-- The composite `i ∘ j` of `i` with the descent homomorphism `j : (D,i) →
(T(D),T(i))` is the
identity on `D`. -/
theorem str_comp_desc (A : TAlgebra T) (hA : IsInitial A) :
    A.str ⊚ (hA.desc (tStr A)).hom = Category.id A.carrier := by
  have h : (strHom A).comp (hA.desc (tStr A)) = AlgHom.id A := by
    rw [hA.uniq A ((strHom A).comp (hA.desc (tStr A))), hA.uniq A (AlgHom.id A)]
  have := congrArg AlgHom.hom h
  exact this

/-- **Proposition 6.7 (Lambek's lemma; Scott 1981, PRG-19).** The structure map `i
: T(D) → D` of an
initial `T`-algebra is an isomorphism `T(D) ≅ D`, with inverse the descent
homomorphism `j`. -/
def lambek (A : TAlgebra T) (hA : IsInitial A) : Iso (T.obj A.carrier) A.carrier where
  hom := A.str
  inv := (hA.desc (tStr A)).hom
  inv_hom_id := str_comp_desc A hA
  hom_inv_id :=
    calc (hA.desc (tStr A)).hom ⊚ A.str
        = (tStr A).str ⊚ T.map (hA.desc (tStr A)).hom := (hA.desc (tStr A)).comm
      _ = T.map A.str ⊚ T.map (hA.desc (tStr A)).hom := rfl
      _ = T.map (A.str ⊚ (hA.desc (tStr A)).hom) := (T.map_comp _ _).symm
      _ = T.map (Category.id A.carrier) := by rw [str_comp_desc A hA]
      _ = Category.id (T.obj A.carrier) := T.map_id _

end Domain.Neighborhood
