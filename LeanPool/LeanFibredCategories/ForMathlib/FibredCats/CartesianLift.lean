/-
Copyright (c) 2026 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Sigma.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import LeanPool.LeanFibredCategories.ForMathlib.Data.Fiber
import LeanPool.LeanFibredCategories.ForMathlib.FibredCats.Basic

/-!
# Cartesian Lifts

For a functor `P : E ⥤ C`, the structure `BasedLift` provides the type of lifts
of a given morphism in the base with fixed source and target in the fibers of `P`:
More precisely, `BasedLift P f` is the type of morphisms in the domain category `E`
which are lifts of `f`.

We provide various useful constructors:
* `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
  based-lift of its image `P g` under functor `P`.
* `BasedLift.id` and `BasedLift.comp` provide the identity and composition of
  based-lifts, respectively.
* We can cast a based-lift along an equality of the base morphisms using the
  equivalence `BasedLift.cast`.

There are also typeclasses `BasedLift.Cartesian` and `BasedLift.CoCartesian`
carrying data witnessing that a given based-lift is cartesian and cocartesian,
respectively.

For a functor `P : E ⥤ C`, we provide the class `CartMor` of cartesian morphisms in
`E`. The type `CartMor P` is defined in terms of the predicate `isCartesianMorphism`.

We prove the following closure properties of the class `CartMor` of cartesian
morphisms:
- `cart_id` proves that the identity morphism is cartesian.
- `cart_comp` proves that the composition of cartesian morphisms is cartesian.
- `cart_iso_closed` proves that the class of cartesian morphisms is closed under
  isomorphisms.
- `cart_pullback` proves that, if `P` preserves pullbacks, then the pullback of a
  cartesian morphism is cartesian.

`instCatCart` provides a category instance for the class of cartesian morphisms,
and `Cart.forget` provides the forgetful functor from the category of cartesian
morphisms to the domain category `E`.

Finally, we provide the following notations:
* `x ⟶[f] y` for `BasedLift P f x y`
* `f ≫[l] g` for the composition of based-lifts given by `BasedLift.comp f g`
-/

namespace CategoryTheory

open Category Opposite Functor

variable {C E : Type*} [Category C] [Category E]

/-- The type of lifts of a given morphism in the base
with fixed source and target in the fibers of the domain and codomain
respectively. -/
@[ext]
structure BasedLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P ⁻¹ c) (tgt : P ⁻¹ d) where
  /-- The underlying morphism in the domain category `E`. -/
  hom : (src : E) ⟶ (tgt : E)
  /-- The lift compatibility equation. -/
  over : (P.map hom) ≫ eqToHom (tgt.over) = eqToHom (src.2) ≫ f

@[inherit_doc] notation x " ⟶[" f "] " y => BasedLift (P := _) f x y

/-- The type `Lift P f tgt` of lifts of `f` with target `tgt` consists of an object
in the fiber of the domain of `f` and a based-lift of `f` starting at this object
and ending at `tgt`. -/
@[ext]
structure Lift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (tgt : P ⁻¹ d) where
  /-- The source object in the fiber of the domain. -/
  src : P ⁻¹ c
  /-- The based-lift from the source to the fixed target. -/
  based_lift : BasedLift P f src tgt

/-- A lift of a morphism in the base with a fixed source in the fiber of
the domain. -/
@[ext]
structure CoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P ⁻¹ c) where
  /-- The target object in the fiber of the codomain. -/
  tgt : P ⁻¹ d
  /-- The based-lift from the fixed source to the target. -/
  based_colift : BasedLift P f src tgt

/-- `HasLift P f y` represents the mere existence of a lift of the morphism `f`
with target `y`. -/
def HasLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (y : P ⁻¹ d) := Nonempty (Lift P f y)

/-- `HasColift P f x` represents the mere existence of a lift of the morphism `f`
with source `x`. -/
def HasCoLift (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P ⁻¹ c) := Nonempty (CoLift P f x)

namespace BasedLift

variable {P : E ⥤ C}

/-- Two based-lifts of the same base morphism are equal if their underlying
morphisms are equal in the domain category. -/
lemma hom_ext {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} {g₁ g₂ : x ⟶[f] y}
    (h : g₁.hom = g₂.hom) : g₁ = g₂ := by
  cases g₁; cases g₂; congr

@[simp]
lemma over_base {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} (g : BasedLift P f x y) :
    P.map g.hom = eqToHom (x.2) ≫ f ≫ (eqToHom (y.over).symm) := by
  simp only [← Category.assoc _ _ _, ← g.over, assoc, eqToHom_trans, eqToHom_refl, comp_id]

/-- Coercion from BasedLift to the domain category. -/
instance (P : E ⥤ C) {c d : C} (f : c ⟶ d) (x : P ⁻¹ c) (y : P ⁻¹ d) :
    CoeOut (BasedLift P f x y) ((x : E) ⟶ (y : E)) where
  coe := fun l ↦ l.hom

/-- `BasedLift.tauto` regards a morphism `g` of the domain category `E` as a
based-lift of its image `P g` under functor `P`. -/
@[simps]
def tauto {e e' : E} (g : e ⟶ e') : (Fiber.tauto e) ⟶[P.map g] (Fiber.tauto e') :=
  ⟨g, by simp only [Fiber.tauto, eqToHom_refl, id_comp, comp_id]⟩

lemma tauto_over_base (f : (P.obj x) ⟶ (P.obj y))
    (e : (Fiber.tauto x) ⟶[f] (Fiber.tauto y)) : P.map e.hom = f := by
  simp [over_base]

/-- A tautological based-lift associated to a given morphism in the domain `E`. -/
@[simps]
instance instCoeTautoBasedLift {e e' : E} {g : e ⟶ e'} :
    CoeDep (e ⟶ e') (g) (Fiber.tauto e  ⟶[P.map g] Fiber.tauto e') where
  coe := tauto g

/-- The identity based-lift. -/
def id (x : P ⁻¹ c) : BasedLift P (𝟙 c) x x := ⟨𝟙 _, by simp⟩

@[simp]
lemma id_hom {x : P ⁻¹ c} : (id x).hom = 𝟙 x.1 := rfl

/-- The composition of based-lifts. -/
def comp {c d d' : C} {f : c ⟶ d} {f' : d ⟶ d'} {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    (g : x ⟶[f] y) (g' : y ⟶[f'] z) : x ⟶[f ≫ f'] z :=
  ⟨g.hom ≫ g'.hom, by
    simp only [P.map_comp]; rw [assoc, over_base g, over_base g']; simp⟩

/-- Notation for the composition of based-lifts. -/
scoped infixr:80 " ≫[l] " => BasedLift.comp

/-- The underlying morphism of a composition of based-lifts is the composition
of the underlying morphisms. -/
@[simp]
lemma comp_hom {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'}
    {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    (g₁ : x ⟶[f₁] y) (g₂ : y ⟶[f₂] z) :
    (g₁ ≫[l] g₂).hom = g₁.hom ≫ g₂.hom := rfl

lemma comp_hom' {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'}
    {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} {h : x ⟶[f₁ ≫ f₂] z} :
    (g₁ ≫[l] g₂) = h ↔ g₁.hom ≫ g₂.hom = h.hom := by
  constructor
  · intro H; rw [← H]; simp
  · intro H; ext; simp [H]

lemma tauto_comp_hom {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} :
    (tauto (P := P) g ≫[l] tauto g').hom = g ≫ g' := rfl

lemma comp_tauto_hom {x y z : E} {f : P.obj x ⟶ P.obj y}
    {l : Fiber.tauto x ⟶[f] (Fiber.tauto y)} {g : y ⟶ z} :
    (l ≫[l] tauto g).hom = l.hom ≫ g := rfl

/-- Casting a based-lift along an equality of the base morphisms. -/
@[simps!]
def cast {c d : C} {f f' : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} (h : f = f') (g : x ⟶[f] y) :
    x ⟶[f'] y := ⟨g.hom, by rw [←h, g.over]⟩

/-- Casting a based-lift along an equality of the base morphisms induces an
equivalence of the based-lifts. -/
@[simps!]
def castEquiv {c d : C} {f f' : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} (h : f = f') :
    (x ⟶[f] y) ≃ (x ⟶[f'] y) where
  toFun := fun g ↦ g.cast h
  invFun := fun g ↦ g.cast h.symm
  left_inv := by intro g; simp [cast]
  right_inv := by intro g; simp [cast]

lemma eq_id_of_hom_eq_id {c : C} {x : P ⁻¹ c} {g : x ⟶[𝟙 c] x} :
    (g.hom = 𝟙 x.1) ↔ (g = id x) := by
  aesop

lemma hom_comp_cast {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'} {f : c ⟶ d'}
    {h₁ : f = f₁ ≫ f₂} {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} {g : x ⟶[f] z} :
    g₁.hom ≫ g₂.hom = g.hom ↔ g₁ ≫[l] g₂ = cast h₁ g := by
  constructor
  · intro
    simp_all only [comp]
    rfl
  · intro h
    rw [← comp_hom, h, cast_hom]

lemma id_comp_cast {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d}
    {g : x ⟶[f] y} : id x  ≫[l] g = (cast ((id_comp f).symm : f = 𝟙 c ≫ f)) g := by
  ext
  simp [comp, id]

/-- Casting equivalence along postcomposition with the identity morphism. -/
@[simp]
def castIdComp {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} :
    (x ⟶[(𝟙 c) ≫ f] y) ≃ (x ⟶[f] y) := castEquiv (id_comp f)

/-- Casting equivalence along precomposition with the identity morphism. -/
@[simp]
def castCompId {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} :
    (x ⟶[f ≫ (𝟙 d)] y) ≃ (x ⟶[f] y) := castEquiv (comp_id f)

/-- Casting equivalence along associativity of the base morphisms. -/
@[simp]
def castAssoc {c' c d d' : C} {u' : c' ⟶ c} {f : c ⟶ d} {u : d ⟶ d'} {x : P ⁻¹ c'}
    {y : P ⁻¹ d'} : (x ⟶[(u' ≫ f) ≫ u] y) ≃ (x ⟶[u' ≫ (f ≫ u)] y) :=
  castEquiv (Category.assoc u' f u)

/-- Casting equivalence along the `eqToHom` of the fiber. -/
def castOfeqToHom {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d} :
    (x ⟶[f] y) ≃ (x.1 ⟶[(eqToHom x.2) ≫ f] y) where
  toFun := fun g => ⟨g.hom, by simp⟩
  invFun := fun g => ⟨g.hom, by simp⟩
  left_inv := by intro g; cases g; rfl
  right_inv := by intro g; cases g; rfl

/-- The composition of based-lifts is associative up to casting along equalities
of the base morphisms. -/
lemma assoc {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'}
    {w : P ⁻¹ c'} {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :
    ((g₁ ≫[l] g₂) ≫[l] g₃) = castAssoc.invFun (g₁ ≫[l] g₂ ≫[l] g₃) := by
  ext
  simp [comp]

lemma assoc_inv {c' c d d' : C} {f₁ : c' ⟶ c} {f₂ : c ⟶ d} {f₃ : d ⟶ d'} {w : P ⁻¹ c'}
    {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    (g₁ : w ⟶[f₁] x) (g₂ : x ⟶[f₂] y) (g₃ : y ⟶[f₃] z) :
    castAssoc.toFun ((g₁ ≫[l] g₂) ≫[l] g₃) =  (g₁ ≫[l] (g₂ ≫[l] g₃)) := by
  ext
  simp [comp]

lemma tauto_comp_cast {e e' e'' : E} {g : e ⟶ e'} {g' : e' ⟶ e''} :
    tauto (g ≫ g') = cast (P.map_comp g g').symm (tauto g ≫[l] tauto g') := rfl

end BasedLift

namespace Lift

variable {P : E ⥤ C}

instance : CoeOut (Lift P f y) (Σ x : E, (x : E) ⟶ y) where
  coe := fun l ↦ ⟨l.src, l.based_lift.hom⟩

lemma over_base (f : c ⟶ d) (y : P ⁻¹ d) (g : Lift P f y) :
    P.map g.based_lift.hom = (eqToHom (g.src.over)) ≫ f ≫ eqToHom (y.over).symm := by
  simp only [BasedLift.over_base]

/-- The underlying morphism of a lift in the domain category. -/
def homOf (g : Lift P f y) : (g.src : E) ⟶ y := g.based_lift.hom

/-- Regarding a morphism in Lift P f as a morphism in the total category E. -/
instance {g : Lift P f y} : CoeDep (Lift P f y) (g) ((g.src : E) ⟶ (y : E)) where
  coe := g.based_lift.hom

/-- The identity lift. -/
def id {c : C} (x : P ⁻¹ c) : Lift P (𝟙 c) x := ⟨x, BasedLift.id x⟩

end Lift

/-- The type of iso-based-lifts of an isomorphism in the base with fixed source
and target. -/
class IsoBasedLift {C E : Type*} [Category C] [Category E] {P : E ⥤ C} {c d : C}
    (f : c ⟶ d) [IsIso f] (x : P ⁻¹ c) (y : P ⁻¹ d) extends (x ⟶[f] y) where
  /-- The underlying morphism is an isomorphism. -/
  is_iso_hom : IsIso hom

namespace IsoBasedLift

variable {P : E ⥤ C} {c d : C} {f : c ⟶ d} [IsIso f] {x : P ⁻¹ c} {y : P ⁻¹ d}

@[inherit_doc] notation x " ⟶[≅" f "] " y => IsoBasedLift (P := _) f x y

/-- Any iso-based-lift is in particular an isomorphism. -/
instance instIsoOfIsoBasedLift (g : (x ⟶[≅f] y)) : IsIso g.hom := g.is_iso_hom

/-- Coercion from IsoBasedLift to BasedLift. -/
instance : Coe (x ⟶[≅f] y) (x ⟶[f] y) where
  coe := fun l => ⟨l.hom, l.over⟩

/-- The inverse of an iso-based-lift, regarded as an iso-based-lift of the inverse. -/
@[reducible]
noncomputable
def Inv (g : x ⟶[≅f] y) : (y ⟶[≅ inv f] x) where
  hom := inv g.hom
  over := by
    simp only [Functor.map_inv, BasedLift.over_base, IsIso.inv_comp, inv_eqToHom,
      assoc, eqToHom_trans, eqToHom_refl, comp_id]
  is_iso_hom := IsIso.inv_isIso

end IsoBasedLift

namespace BasedLift

/-- A based-lift `g : x ⟶[f] y` over a base morphism `f` is cartesian if for every
morphism `u` in the base and every lift `g' : x ⟶[u ≫ f] z` over the composite
`u ≫ f`, there is a unique morphism `l : y ⟶[u] z` over `u` such that
`l ≫ g = g'`. -/
class Cartesian {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d}
    (g : x ⟶[f] y) where
  /-- Uniqueness of the gap lift through a cartesian based-lift. -/
  uniq_lift : ∀ ⦃c' : C⦄ ⦃z : P ⁻¹ c'⦄ (u : c' ⟶ c) (g' : z ⟶[u ≫ f]  y),
    Unique {k : z ⟶[u] x // (k ≫[l] g) = g'}

/-- A morphism `g : x ⟶[f] y` over `f` is cocartesian if for all morphisms `u` in
the base and `g' : x ⟶[f ≫ u] z` over the composite `f ≫ u`, there is a unique
morphism `l : y ⟶[u] z` over `u` such that `g ≫ l = g'`. -/
class CoCartesian {P : E ⥤ C} {c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d}
    (g : x ⟶[f] y) where
  /-- Uniqueness of the cogap lift through a cocartesian based-lift. -/
  uniq_colift : ∀ ⦃d' : C⦄ ⦃z : P ⁻¹ d'⦄ (u : d ⟶ d') (g' : x ⟶[f ≫ u]  z),
    Unique { l :  y ⟶[u] z // (BasedLift.comp g l) = g' }

variable {P : E ⥤ C} {c' c d : C} {f : c ⟶ d} {x : P ⁻¹ c} {y : P ⁻¹ d}
  {x' : P ⁻¹ c'} (g : x ⟶[f] y) [Cartesian (P := P) g]

/-- `gaplift g u g'` is the canonical map from a lift `g' : x' ⟶[u ≫ f] y` to a
cartesian lift `g` of `f`. -/
def gaplift (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) : x' ⟶[u] x :=
  (Cartesian.uniq_lift (P := P) (f := f) (g := g) (z := x') u g').default.val

/-- A variant of `gaplift` for `g' : x' ⟶[f'] y` with casting along `f' = u ≫ f`
baked into the definition. -/
def gaplift' (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y) (h : f' = u ≫ f) :
    x' ⟶[u] x :=
  (Cartesian.uniq_lift (P := P) (f := f) (g := g) (z := x') u (cast h g')).default.val

@[simp]
lemma gaplift_cast (u : c' ⟶ c) {f' : c' ⟶ d} (g' : x' ⟶[f'] y)
    (h : f' = u ≫ f) : gaplift' g u g' h = gaplift g u (cast h g') := by
  rfl

/-- The composition of the gap lift and the cartesian lift is the given lift. -/
lemma gaplift_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) :
    ((gaplift g u g') ≫[l] g) = g' :=
  (Cartesian.uniq_lift (P := P) (f := f) (g := g) (z := x') u g').default.property

/-- A variant of the gaplift property for equality of the underlying morphisms. -/
@[simp]
lemma gaplift_hom_property (u : c' ⟶ c) (g' : x' ⟶[u ≫ f] y) :
    (gaplift g u g').hom ≫ g.hom = g'.hom := by
  rw [← BasedLift.comp_hom _ _]; congr 1; exact gaplift_property g u g'

/-- The uniqueness part of the universal property of the gap lift. -/
lemma gaplift_uniq {u : c' ⟶ c} (g' : x' ⟶[u ≫ f] y) (v : x' ⟶[u] x)
    (hv : v ≫[l] g = g') : v = gaplift (g := g) u g' :=
  congrArg Subtype.val
    ((Cartesian.uniq_lift (P := P) (f := f) (g := g) (z := x') u g').uniq ⟨v, hv⟩)

/-- A variant of the uniqueness lemma. -/
lemma gaplift_uniq' {u : c' ⟶ c} (v : x' ⟶[u] x) (v' : x' ⟶[u] x)
    (hv : v ≫[l] g = v' ≫[l] g) : v = v' := by
  rw [gaplift_uniq g (v' ≫[l] g) v hv]; symm; apply gaplift_uniq; rfl

/-- The gaplift of any cartesian based-lift with respect to itself is the identity. -/
lemma gaplift'_self : gaplift' g (𝟙 c) g (id_comp f).symm = BasedLift.id x := by
  simp only [gaplift_cast]
  symm
  apply gaplift_uniq
  ext
  simp [BasedLift.comp, BasedLift.id]

variable {g}

/-- The composition of gaplifts with respect to morphisms `u' : c'' ⟶ c` and
`u : c' ⟶ c` is the gap lift of the composition `u' ≫ u`. -/
lemma gaplift_comp {u : c' ⟶ c} {u' : c'' ⟶ c'} {x'' : P ⁻¹ c''}
    {g' : x' ⟶[u ≫ f] y} [Cartesian (P := P) (f := u ≫ f) g']
    {g'' : x'' ⟶[u' ≫ u ≫ f] y} :
    (gaplift  (g := g') u' g'') ≫[l] (gaplift (g := g) u g') =
    gaplift (g := g) (u' ≫ u) (BasedLift.castAssoc.invFun g'') := by
  refine gaplift_uniq (f := f) g (castAssoc.invFun g'')
    ((gaplift (g := g') u' g'') ≫[l] (gaplift (g := g) u g'))
    (by rw [BasedLift.assoc]; simp only [gaplift_property])

/-- The identity based-lift is cartesian. -/
instance instId {x : P ⁻¹ c} : Cartesian (id x) where
  uniq_lift := fun _ _ _ g' => {
    default := ⟨castCompId g', by
      simp_all only [comp, castCompId, id, comp_id]; rfl⟩
    uniq := by aesop
  }

/-- Cartesian based-lifts are closed under composition. -/
instance instComp {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'}
    {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    (g₁ : x ⟶[f₁] y) [Cartesian g₁] (g₂ : y ⟶[f₂] z) [Cartesian g₂] :
    Cartesian (g₁ ≫[l] g₂) where
  uniq_lift := fun _ _ u g' => {
    default := ⟨gaplift g₁ u (gaplift g₂ (u ≫ f₁) (castAssoc.invFun g')), by
      rw [← BasedLift.assoc_inv, gaplift_property g₁ _ _, gaplift_property g₂ _ _]; simp⟩
    uniq := by
      rintro ⟨l, hl⟩
      apply Subtype.ext
      apply gaplift_uniq g₁ (gaplift g₂ (u ≫ f₁) (castAssoc.invFun g')) l
      apply gaplift_uniq g₂ (castAssoc.invFun g') (l ≫[l] g₁)
      rw [BasedLift.assoc, hl] }

/-- The cancellation lemma for cartesian based-lifts. If `g₂ : y ⟶[f₂] z` and
`g₁ ≫[l] g₂ : z ⟶[f₂] z` are cartesian then `g₁` is cartesian. -/
@[reducible]
def instCancel {c d d' : C} {f₁ : c ⟶ d} {f₂ : d ⟶ d'}
    {x : P ⁻¹ c} {y : P ⁻¹ d} {z : P ⁻¹ d'}
    {g₁ : x ⟶[f₁] y} {g₂ : y ⟶[f₂] z} [Cartesian g₂] [Cartesian (g₁ ≫[l] g₂)] :
    Cartesian g₁ where
  uniq_lift := fun _ _ u₁ g₁' => {
    default := {
      val := gaplift (g := g₁ ≫[l] g₂) u₁ (castAssoc (g₁' ≫[l] g₂))
      property := by
        apply gaplift_uniq' g₂ _ (g₁'); rw [BasedLift.assoc]
        rw [gaplift_property _ _ _]; simp
    }
    uniq := by
      intro l
      obtain ⟨l, hl⟩ := l
      have h : (l ≫[l] (g₁ ≫[l] g₂)) = castAssoc (g₁' ≫[l] g₂) := by
        simp only [← BasedLift.assoc_inv]; rw [hl]; simp
      exact Subtype.ext
        (gaplift_uniq (g₁ ≫[l] g₂) (castAssoc (g₁' ≫[l] g₂)) l h)
  }

end BasedLift

/-- A morphism is cartesian if the gap map is unique. -/
def isCartesianMorphism {P : E ⥤ C} {x y : E} (g : x ⟶ y) : Prop :=
  ∀ ⦃z : E⦄ (u : P.obj z ⟶ P.obj x) (g' : Fiber.tauto z ⟶[u ≫ P.map g] y),
    ∃! (l : Fiber.tauto z ⟶[u] x), (l.hom ≫ g) = g'.hom

/-- The class of cartesian morphisms. -/
def CartMor (P : E ⥤ C) : MorphismProperty E := fun _ _ g => isCartesianMorphism (P := P) g

open MorphismProperty BasedLift

variable {P : E ⥤ C} {x y : E}

/-- `gapmap g gcart u g'` is a unique morphism `l` over `u` such that `l ≫ g = g'`. -/
noncomputable
def gapmap (g : x ⟶ y) (gcart : CartMor P g) {z : E} (u : P.obj z ⟶ P.obj x)
    (g' : Fiber.tauto z ⟶[u ≫ P.map g] y) : (z : E) ⟶ x :=
  (Classical.choose (gcart u g')).hom

@[simp]
lemma gapmap_over {gcart : CartMor P g} {z : E} {u : P.obj z ⟶ P.obj x}
    {g' : Fiber.tauto z ⟶[u ≫ P.map g] Fiber.tauto y} :
    P.map (gapmap g gcart u g') = u := by
  simp [gapmap]

/-- The composition of the gap map of a map `g'` and the cartesian lift `g` is
the given map `g'`. -/
@[simp]
lemma gapmap_property {g : x ⟶ y} {gcart : CartMor P g} {z : E}
    {u : P.obj z ⟶ P.obj x} {g' : Fiber.tauto z ⟶[u ≫ P.map g] y} :
    (gapmap g gcart u g') ≫ g = g'.hom := by
  apply (Classical.choose_spec (gcart u g')).1

@[simp]
lemma gapmap_uniq {gcart : CartMor P g} {z : E} {u : P.obj z ⟶ P.obj x}
    {g' : Fiber.tauto z ⟶[u ≫ P.map g] Fiber.tauto y}
    (v : Fiber.tauto z ⟶[u] x) (hv : v.hom ≫ g = g'.hom) :
    v.hom = gapmap g gcart u g' := by
  have : v = Classical.choose (gcart u g') := by
    refine (Classical.choose_spec (gcart u g')).2 v hv
  rw [this]
  simp [gapmap]

lemma gapmap_uniq' (g : x ⟶ y) (gcart : CartMor P g) {c : C} {z : P ⁻¹ c}
    (v₁ : (z : E) ⟶ x) (v₂ : (z : E) ⟶ x) (hv : v₁ ≫ g = v₂ ≫ g)
    (hv' : P.map v₁ = P.map v₂) : v₁ = v₂ := by
  let v₁' := tauto (P := P) v₁
  let v₂' := tauto (P := P) v₂
  let g' := v₂' ≫[l] tauto g
  have heq : P.map v₁ ≫ P.map g = P.map v₂ ≫ P.map g := by
    rw [← P.map_comp, ← P.map_comp, hv]
  have hv₁ : v₁'.hom ≫ g = g'.hom := by
    simp_all only [Fiber.tauto_over, tauto_hom, BasedLift.comp, v₁', v₂', g']
  have hv₂' : (BasedLift.cast hv'.symm v₂').hom ≫ g =
      (BasedLift.cast heq.symm g').hom := by
    simp [BasedLift.cast]
    rfl
  have H' := (gcart (P.map v₁) (BasedLift.cast heq.symm g')).unique hv₁ hv₂'
  injection H'

/-- `cart_id e` says that the identity morphism `𝟙 e` is cartesian. -/
lemma cart_id (e : E) : CartMor P (𝟙 e) := fun _ u g' ↦ by
  refine ⟨g'.cast ((whisker_eq u (P.map_id e)).trans (comp_id _)), ?_, ?_⟩
  · change g'.hom ≫ 𝟙 e = g'.hom
    exact comp_id _
  · intro v hv
    apply BasedLift.hom_ext
    change v.hom = g'.hom
    rw [← hv]
    exact (comp_id _).symm

/-- Cartesian morphisms are closed under composition. -/
lemma cart_comp_mem {x y z : E} (f : x ⟶ y) (g : y ⟶ z)
    (hf : CartMor P f) (hg : CartMor P g) : CartMor P (f ≫ g) := fun _ u g' => by
  obtain ⟨lg, hlg, hlg_uniq⟩ := hg (u ≫ P.map f)
    (g'.cast ((u ≫= P.map_comp f g).trans (Category.assoc u _ _).symm))
  obtain ⟨lf, hlf, hlf_uniq⟩ := hf u lg
  refine ⟨lf, ?_, ?_⟩
  · change lf.hom ≫ f ≫ g = g'.hom
    rw [← Category.assoc, hlf]
    simpa [BasedLift.cast] using hlg
  · intro v hv
    have hvlg : v.hom ≫ f = lg.hom := by
      have htemp : (v ≫[l] BasedLift.tauto f).hom ≫ g =
          (g'.cast ((u ≫= P.map_comp f g).trans (Category.assoc u _ _).symm)).hom := by
        change (v.hom ≫ f) ≫ g = g'.hom
        rw [Category.assoc]; exact hv
      have hresult := hlg_uniq (v ≫[l] BasedLift.tauto f) htemp
      exact (BasedLift.comp_hom').mp hresult
    exact hlf_uniq v hvlg

/-- Cartesian morphisms are closed under composition (as an `IsStableUnderComposition`
witness). -/
instance instCartMorIsStableUnderComposition :
    (CartMor P).IsStableUnderComposition where
  comp_mem f g hf hg := cart_comp_mem f g hf hg

variable {P : E ⥤ C} {c d : C}

/-- Given a morphism `f` in the base category `C`, the type `CartLifts P f src tgt`
consists of the based-lifts of `f` with the source `src` and the target `tgt`
which are cartesian with respect to `P`. -/
class CartBasedLifts (P : E ⥤ C) {c d : C} (f : c ⟶ d) (src : P ⁻¹ c) (tgt : P ⁻¹ d)
    extends BasedLift P f src tgt where
  /-- The based-lift is cartesian. -/
  is_cart : BasedLift.Cartesian toBasedLift

instance instCoeHomOfCartBasedLift {c d : C} (f : c ⟶ d) (src : P ⁻¹ c) (tgt : P ⁻¹ d) :
    CoeOut (CartBasedLifts P f src tgt) (src.1 ⟶ tgt.1) where
  coe := fun l ↦ l.1.hom

/-- The type of cartesian lifts of a morphism `f` with fixed target. -/
class CartLift (f : c ⟶ d) (y : P ⁻¹ d) extends Lift P f y where
  /-- The associated based-lift is cartesian. -/
  is_cart : BasedLift.Cartesian based_lift

namespace CartLift

/-- The underlying morphism of a cartesian lift in the domain category. -/
def homOf {f : c ⟶ d} {y : P ⁻¹ d} (g : CartLift (P := P) f y) :
    (g.src : E) ⟶ y := g.based_lift.hom

end CartLift

instance instCoeLiftOfCartLift {c d : C} {f : c ⟶ d} {y : P ⁻¹ d} :
    Coe (CartLift (P := P) f y) (Lift P f y) where
  coe := fun l ↦ l.toLift

/-- A cocartesian lift of `f` with fixed source. -/
class CoCartLift (f : c ⟶ d) (x : P ⁻¹ c) extends CoLift P f x where
  /-- The associated based-colift is cocartesian. -/
  is_cart : BasedLift.CoCartesian based_colift

/-- Mere existence of a cartesian lift with fixed target. -/
def HasCartLift (f : c ⟶ d) (y : P ⁻¹ d) := Nonempty (CartLift (P := P) f y)

/-- Mere existence of a cocartesian lift with fixed source. -/
def HasCoCartLift (f : c ⟶ d) (x : P ⁻¹ c) := Nonempty (CoCartLift (P := P) f x)

/-- The carrier for the subcategory of cartesian morphisms in the domain of `P`. -/
structure Cart (P : E ⥤ C) where
  /-- The underlying object in `E`. -/
  obj : E

/-- The subcategory of cartesian morphisms. -/
instance instCategoryCart {P : E ⥤ C} : Category (Cart P) where
  Hom x y := { f : x.obj ⟶ y.obj | CartMor (P := P) f }
  id x := ⟨𝟙 x.obj, cart_id x.obj⟩
  comp := @fun _ _ _ f g => ⟨f.1 ≫ g.1, cart_comp_mem f.1 g.1 f.2 g.2⟩

namespace Cart

/-- The forgetful functor from the category of cartesian morphisms to the domain
category. -/
def forget {P : E ⥤ C} : Cart P ⥤ E where
  obj := fun x => x.obj
  map := @fun _ _ f => f.1

end Cart

end CategoryTheory
