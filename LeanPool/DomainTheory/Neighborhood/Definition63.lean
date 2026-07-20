/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Approximable

/-!
# Lecture VI — Definitions 6.3–6.5 (Scott 1981, PRG-19): functors, `T`-algebras,
initial algebras

To state domain equations `D ≅ T(D)` and single out their *canonical* solutions,
Scott introduces
"a small amount of the terminology of category theory" and stresses that the next
few definitions
"could be given for any category". This module sets up a small, self-contained
category abstraction
and formalises that vocabulary:

* **Definition 6.3** — a *functor* `T` on a category into itself (an
*endofunctor*), preserving
  identities and composition.
* **Definition 6.4** — a *`T`-algebra* `k : T(E) → E` and a *homomorphism* of
`T`-algebras.
* **Definition 6.5** — an *initial* `T`-algebra: one with a unique homomorphism
into every algebra.

Everything is generic over an arbitrary `Category`, exactly as Scott emphasises.
As Scott also notes
in the prose preceding Definition 6.3 ("[the systems] form quite an interesting
category with respect
to the approximable maps"), the neighbourhood systems and approximable maps of the
project *are* a
category; that instance (`DomainObj`) is provided here as a witness that the
abstract definitions are
not vacuous.

Auxiliary categorical lemmas (identity and composition of algebra homomorphisms,
`Iso`) needed for
Propositions 6.6 and 6.7 are developed here as well.

All definitions and lemmas are constructive and **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the underlying composition laws are the
project's
`idMap_comp`/`comp_idMap`/`comp_assoc` (Theorem 2.5).

## Why a bespoke `Category` rather than Mathlib's `CategoryTheory.Category`?

Mathlib *does* have a fully developed category theory: `CategoryTheory.Category`
(structurally
identical to the class below — separate object/morphism universes, `Hom`, `id`,
`comp`, and the three
laws), functors `C ⥤ D`, `Iso`, `CategoryTheory.Endofunctor.Algebra`/`Algebra.Hom`
with the category
of algebras, `Limits.IsInitial`, and even Lambek's lemma as
`Endofunctor.Algebra.Initial.strInv` /
`left_inv` / `right_inv`. So Mathlib is *expressive enough* to state every one of
Definitions 6.3–6.5
(and Propositions 6.6–6.7) verbatim — it is not a question of missing vocabulary.

It is nonetheless the wrong tool *here*, and the reason is this project's headline
invariant, not
taste. The trade-off was checked empirically:

* The bare instance is fine: a `Category DomainObj` built on `ApproximableMap`
(Theorem 2.5 laws)
  is **choice-free**, `#print axioms = [propext, Quot.sound]`.
* But the *only reason* to import Mathlib's hierarchy is to reuse its downstream
content — functor
  algebras and the initial-algebra fixed-point theorem — and that content is
  **choice-bound**:
  `Mathlib.CategoryTheory.Endofunctor.Algebra.Initial.left_inv` (the inverse half
  of Lambek's lemma,
  i.e. Scott's Proposition 6.7) reports `[propext, Classical.choice, Quot.sound]`,
  because Mathlib's
  `IsInitial` rides on the `Limits` framework.
* By contrast, the project's own `initialIso` (Proposition 6.6) and `lambek`
(Proposition 6.7), built
  on the class below, depend on **no axioms whatsoever** (`#print axioms` reports
  *"does not depend on
  any axioms"*).

So adopting Mathlib would force one of two losing choices: (a) consume its
initial-algebra API and
thereby inject `Classical.choice` into the project's flagship Lecture VI results,
breaking the
`#print axioms ⊆ {propext, Quot.sound}` discipline that is the whole point; or (b)
take only the bare
class and re-prove 6.6–6.7 by hand anyway — paying a heavy transitive import and
the `≫`
(diagrammatic, "`f` then `g`") vs `⊚` (Scott's "`g` after `f`") convention clash
for no reusable
content. Since Scott asks only for "a small amount of the terminology of category
theory", the
~50-line self-contained class below supplies exactly that vocabulary while keeping
every proof
constructive and choice-free. The Mathlib `Category` is therefore *usable but
counterproductive* for
this development, and is deliberately not used.
-/

namespace Domain.Neighborhood

universe u v w

/-- A category: objects (a type `Obj`), hom-sets `Hom X Y`, identities,
composition, and the three
category laws. We bundle it as a class so a fixed object type can carry its
categorical structure.
The composition `comp g f` reads "`g` after `f`" (the same convention as
`ApproximableMap.comp`). -/
class Category (Obj : Type u) where
  /-- The morphisms from `X` to `Y`. -/
  Hom : Obj → Obj → Type v
  /-- The identity morphism on each object. -/
  id : (X : Obj) → Hom X X
  /-- Composition: `comp g f` is "`g` after `f`". -/
  comp : {X Y Z : Obj} → Hom Y Z → Hom X Y → Hom X Z
  /-- Left identity law `I ∘ f = f`. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id Y) f = f
  /-- Right identity law `f ∘ I = f`. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id X) = f
  /-- Associativity `(h ∘ g) ∘ f = h ∘ (g ∘ f)`. -/
  assoc : ∀ {W X Y Z : Obj} (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp (comp h g) f = comp h (comp g f)

@[inherit_doc] infixr:80 " ⊚ " => Category.comp

/-! ### The category of neighbourhood systems and approximable maps

Scott's running category (prose before Definition 6.3). Objects bundle a token
type with a system;
morphisms are approximable maps; the laws are Theorem 2.5. -/

/-- An object of the category of domains: a token type together with a
neighbourhood system on
it. -/
structure DomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system (the "domain"). -/
  sys : NeighborhoodSystem carrier

/-- **The category of domains and approximable maps** (Scott's prose preceding
Definition 6.3):
identities and associative composition come from Theorem 2.5 (`idMap_comp`,
`comp_idMap`,
`comp_assoc`). -/
instance : Category DomainObj where
  Hom D E := ApproximableMap D.sys E.sys
  id D := ApproximableMap.idMap D.sys
  comp g f := g.comp f
  id_comp f := ApproximableMap.idMap_comp f
  comp_id f := ApproximableMap.comp_idMap f
  assoc h g f := ApproximableMap.comp_assoc h g f

variable {Obj : Type u} [Category Obj]

/-! ### Definition 6.3 — functors -/

/-- **Definition 6.3 (Scott 1981, PRG-19).** A *functor* on a category into itself
(an
*endofunctor*): an assignment `obj` on objects and `map` on morphisms preserving
identities
(`map_id`) and composition (`map_comp`). -/
structure Endofunctor (Obj : Type u) [Category Obj] where
  /-- The action on objects. -/
  obj : Obj → Obj
  /-- The action on morphisms. -/
  map : {X Y : Obj} → Category.Hom X Y → Category.Hom (obj X) (obj Y)
  /-- `T(I_X) = I_{T(X)}`. -/
  map_id : ∀ (X : Obj), map (Category.id X) = Category.id (obj X)
  /-- `T(g ∘ f) = T(g) ∘ T(f)`. -/
  map_comp : ∀ {X Y Z : Obj} (g : Category.Hom Y Z) (f : Category.Hom X Y),
    map (g ⊚ f) = (map g) ⊚ (map f)

/-! ### Definition 6.4 — `T`-algebras and their homomorphisms -/

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *`T`-algebra*: a domain `carrier`
together with a
structure map `str : T(carrier) → carrier`. -/
structure TAlgebra (T : Endofunctor Obj) where
  /-- The underlying object `E`. -/
  carrier : Obj
  /-- The structure map `k : T(E) → E`. -/
  str : Category.Hom (T.obj carrier) carrier

variable {T : Endofunctor Obj}

/-- **Definition 6.4 (Scott 1981, PRG-19).** A *homomorphism* of `T`-algebras
`(E,k) → (F,m)`: a map
`hom : E → F` making the square commute, i.e. `hom ∘ k = m ∘ T(hom)`. -/
structure AlgHom (A B : TAlgebra T) where
  /-- The underlying morphism `h : E → F`. -/
  hom : Category.Hom A.carrier B.carrier
  /-- The homomorphism square `h ∘ k = m ∘ T(h)`. -/
  comm : hom ⊚ A.str = B.str ⊚ T.map hom

namespace AlgHom

/-- The identity is a homomorphism: `I ∘ k = k ∘ T(I)`. -/
def id (A : TAlgebra T) : AlgHom A A where
  hom := Category.id A.carrier
  comm := by rw [Category.id_comp, T.map_id, Category.comp_id]

/-- Composition of `T`-algebra homomorphisms (the `T`-algebras and homomorphisms
form a category —
the remark after Definition 6.4). -/
def comp {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) : AlgHom A C where
  hom := β.hom ⊚ α.hom
  comm := by
    rw [Category.assoc, α.comm, ← Category.assoc, β.comm, Category.assoc, ← T.map_comp]

@[simp] theorem id_hom (A : TAlgebra T) : (AlgHom.id A).hom = Category.id A.carrier := rfl

@[simp] theorem comp_hom {A B C : TAlgebra T} (β : AlgHom B C) (α : AlgHom A B) :
    (β.comp α).hom = β.hom ⊚ α.hom := rfl

end AlgHom

/-! ### Definition 6.5 — initial `T`-algebras -/

/-- **Definition 6.5 (Scott 1981, PRG-19).** A `T`-algebra `A` is *initial* iff
there is a (unique)
homomorphism from `A` into every `T`-algebra. We package the homomorphism as the
data `desc` and its
uniqueness as `uniq`. -/
structure IsInitial (A : TAlgebra T) where
  /-- The chosen homomorphism into any algebra `B`. -/
  desc : (B : TAlgebra T) → AlgHom A B
  /-- It is the only homomorphism `A → B`. -/
  uniq : ∀ (B : TAlgebra T) (h : AlgHom A B), h = desc B

/-- An isomorphism in the category: a pair of mutually inverse morphisms. -/
structure Iso (X Y : Obj) where
  /-- The forward morphism. -/
  hom : Category.Hom X Y
  /-- The inverse morphism. -/
  inv : Category.Hom Y X
  /-- `inv ∘ hom = I_X`. -/
  hom_inv_id : inv ⊚ hom = Category.id X
  /-- `hom ∘ inv = I_Y`. -/
  inv_hom_id : hom ⊚ inv = Category.id Y

end Domain.Neighborhood
