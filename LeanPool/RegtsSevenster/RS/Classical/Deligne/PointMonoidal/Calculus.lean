/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointMonoidal.Comparison

/-!
# A point-free calculus for the two tensor products

The laws of the comparison are proved by evaluating both sides on
generators.  This module collects the evaluations: the structural
morphisms of the category of super modules over a super-commutative
algebra, and of `RS.SuperVect`, applied to a generator of a tensor
product, together with the extensionality principles that reduce an
identity of maps out of a twofold or threefold graded tensor
product to its values on generators.  The comparison itself is
defined in [Comparison.lean](Comparison.lean) and its laws are
proved in [Coherence.lean](Coherence.lean).

## Contents

* `RS.whiskerRight_evenMap_tmulEE` and its fifteen companions,
  `RS.modAssoc_evenMap_ee` and its seven,
  `RS.mcTensorHom_evenMap_tmulEE` and its three,
  `RS.modComp_evenMap_apply`: the structural morphisms of the
  category of super modules, on generators.
* `RS.actEE_span_one`, `RS.actEO_span_one`: the action of a
  complex scalar through the unit of the algebra.
* `RS.svWhiskerRight_evenMap_inl` and its fifteen companions,
  `RS.svComp_evenMap_apply`, `RS.svAssoc_evenMap_ee` and its seven,
  `RS.svBraiding_evenMap_inl` and its three,
  `RS.svLeftUnitor_evenMap_inl` and `RS.svRightUnitor_evenMap_inl`
  with their odd companions: the same for `RS.SuperVect`.
* `RS.superVectHom_evenMap_apply` and its odd companion: the fibre
  functor on a morphism, on generators.
* `RS.gradedTriple_ext`, `RS.superVectTripleEven_ext`,
  `RS.superVectTripleOdd_ext`, `RS.superVectPairEven_ext`,
  `RS.superVectPairOdd_ext`: extensionality for a twofold and a
  threefold graded tensor product.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open SuperCommAlgebra (pointMod)
open SuperCommAlgebra.Mod

universe u

/-! ## One-step computations on generators

The whiskerings, the associator and the unitors of the super
modules, and the whiskerings and associator of the super vector
spaces, evaluated on the generators of a tensor product.  Each is
an instance of a computation lemma of the construction; they are
collected here so that the coherence proofs below rewrite with
concrete equations only. -/

section Steps

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}}

section ModSteps

/-- Composition of super module morphisms, even degree, on an
element. -/
theorem modComp_evenMap_apply {X Y Z : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.even) :
    (f ≫ g).evenMap x = g.evenMap (f.evenMap x) := rfl

/-- Composition of super module morphisms, odd degree, on an
element. -/
theorem modComp_oddMap_apply {X Y Z : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.odd) :
    (f ≫ g).oddMap x = g.oddMap (f.oddMap x) := rfl

variable {X Y : S.Mod.{u, u, u, u}} (f : X ⟶ Y) (C : S.Mod.{u, u, u, u})

/-- Right whiskering on an even-even generator. -/
theorem whiskerRight_evenMap_tmulEE (x : X.even) (c : C.even) :
    (f ▷ C).evenMap (tmulEE X C x c) =
      tmulEE Y C (f.evenMap x) c :=
  tensorHom_evenMap_tmulEE f (𝟙 C) x c

/-- Right whiskering on an odd-odd generator. -/
theorem whiskerRight_evenMap_tmulOO (x : X.odd) (c : C.odd) :
    (f ▷ C).evenMap (tmulOO X C x c) =
      tmulOO Y C (f.oddMap x) c :=
  tensorHom_evenMap_tmulOO f (𝟙 C) x c

/-- Right whiskering on an even-odd generator. -/
theorem whiskerRight_oddMap_tmulEO (x : X.even) (c : C.odd) :
    (f ▷ C).oddMap (tmulEO X C x c) =
      tmulEO Y C (f.evenMap x) c :=
  tensorHom_oddMap_tmulEO f (𝟙 C) x c

/-- Right whiskering on an odd-even generator. -/
theorem whiskerRight_oddMap_tmulOE (x : X.odd) (c : C.even) :
    (f ▷ C).oddMap (tmulOE X C x c) =
      tmulOE Y C (f.oddMap x) c :=
  tensorHom_oddMap_tmulOE f (𝟙 C) x c

/-- Left whiskering on an even-even generator. -/
theorem whiskerLeft_evenMap_tmulEE (a : C.even) (x : X.even) :
    (C ◁ f).evenMap (tmulEE C X a x) =
      tmulEE C Y a (f.evenMap x) :=
  tensorHom_evenMap_tmulEE (𝟙 C) f a x

/-- Left whiskering on an odd-odd generator. -/
theorem whiskerLeft_evenMap_tmulOO (a : C.odd) (x : X.odd) :
    (C ◁ f).evenMap (tmulOO C X a x) =
      tmulOO C Y a (f.oddMap x) :=
  tensorHom_evenMap_tmulOO (𝟙 C) f a x

/-- Left whiskering on an even-odd generator. -/
theorem whiskerLeft_oddMap_tmulEO (a : C.even) (x : X.odd) :
    (C ◁ f).oddMap (tmulEO C X a x) =
      tmulEO C Y a (f.oddMap x) :=
  tensorHom_oddMap_tmulEO (𝟙 C) f a x

/-- Left whiskering on an odd-even generator. -/
theorem whiskerLeft_oddMap_tmulOE (a : C.odd) (x : X.even) :
    (C ◁ f).oddMap (tmulOE C X a x) =
      tmulOE C Y a (f.evenMap x) :=
  tensorHom_oddMap_tmulOE (𝟙 C) f a x

end ModSteps

/-- A scalar multiple of the unit acts by that scalar, in even
degree. -/
theorem actEE_span_one {X : S.Mod.{u, u, u, u}} (r : ℂ)
    (z : X.even) :
    X.actEE (LinearMap.toSpanSingleton ℂ S.even S.one r) z =
      r • z := by
  change X.actEE (r • S.one) z = r • z
  rw [map_smul, LinearMap.smul_apply, X.one_act_e]

/-- A scalar multiple of the unit acts by that scalar, in odd
degree. -/
theorem actEO_span_one {X : S.Mod.{u, u, u, u}} (r : ℂ)
    (z : X.odd) :
    X.actEO (LinearMap.toSpanSingleton ℂ S.even S.one r) z =
      r • z := by
  change X.actEO (r • S.one) z = r • z
  rw [map_smul, LinearMap.smul_apply, X.one_act_o]

/-- The monoidal tensor of two morphisms on an even-even
generator. -/
theorem mcTensorHom_evenMap_tmulEE {X Y X' Y' : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (m : X.even) (n : X'.even) :
    (f ⊗ₘ g).evenMap (tmulEE X X' m n) =
      tmulEE Y Y' (f.evenMap m) (g.evenMap n) :=
  tensorHom_evenMap_tmulEE f g m n

/-- The monoidal tensor of two morphisms on an odd-odd
generator. -/
theorem mcTensorHom_evenMap_tmulOO {X Y X' Y' : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (m : X.odd) (n : X'.odd) :
    (f ⊗ₘ g).evenMap (tmulOO X X' m n) =
      tmulOO Y Y' (f.oddMap m) (g.oddMap n) :=
  tensorHom_evenMap_tmulOO f g m n

/-- The monoidal tensor of two morphisms on an even-odd
generator. -/
theorem mcTensorHom_oddMap_tmulEO {X Y X' Y' : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (m : X.even) (n : X'.odd) :
    (f ⊗ₘ g).oddMap (tmulEO X X' m n) =
      tmulEO Y Y' (f.evenMap m) (g.oddMap n) :=
  tensorHom_oddMap_tmulEO f g m n

/-- The monoidal tensor of two morphisms on an odd-even
generator. -/
theorem mcTensorHom_oddMap_tmulOE {X Y X' Y' : S.Mod.{u, u, u, u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (m : X.odd) (n : X'.even) :
    (f ⊗ₘ g).oddMap (tmulOE X X' m n) =
      tmulOE Y Y' (f.oddMap m) (g.evenMap n) :=
  tensorHom_oddMap_tmulOE f g m n

section AssocSteps

variable (M N Q : S.Mod.{u, u, u, u})

/-- The associator on the even-even-even generators. -/
theorem modAssoc_evenMap_ee (m : M.even) (n : N.even) (q : Q.even) :
    (α_ M N Q).hom.evenMap
        (tmulEE (M.tensor N) Q (tmulEE M N m n) q) =
      tmulEE M (N.tensor Q) m (tmulEE N Q n q) := by
  rw [modAssociator_hom, assocHom_evenMap_tmulEE, assocFee_tmulEE]

/-- The associator on the odd-odd-even generators. -/
theorem modAssoc_evenMap_oo (m : M.odd) (n : N.odd) (q : Q.even) :
    (α_ M N Q).hom.evenMap
        (tmulEE (M.tensor N) Q (tmulOO M N m n) q) =
      tmulOO M (N.tensor Q) m (tmulOE N Q n q) := by
  rw [modAssociator_hom, assocHom_evenMap_tmulEE, assocFee_tmulOO]

/-- The associator on the even-odd-odd generators. -/
theorem modAssoc_evenMap_eo (m : M.even) (n : N.odd) (q : Q.odd) :
    (α_ M N Q).hom.evenMap
        (tmulOO (M.tensor N) Q (tmulEO M N m n) q) =
      tmulEE M (N.tensor Q) m (tmulOO N Q n q) := by
  rw [modAssociator_hom, assocHom_evenMap_tmulOO, assocFoo_tmulEO]

/-- The associator on the odd-even-odd generators. -/
theorem modAssoc_evenMap_oe (m : M.odd) (n : N.even) (q : Q.odd) :
    (α_ M N Q).hom.evenMap
        (tmulOO (M.tensor N) Q (tmulOE M N m n) q) =
      tmulOO M (N.tensor Q) m (tmulEO N Q n q) := by
  rw [modAssociator_hom, assocHom_evenMap_tmulOO, assocFoo_tmulOE]

/-- The associator on the even-even-odd generators. -/
theorem modAssoc_oddMap_ee (m : M.even) (n : N.even) (q : Q.odd) :
    (α_ M N Q).hom.oddMap
        (tmulEO (M.tensor N) Q (tmulEE M N m n) q) =
      tmulEO M (N.tensor Q) m (tmulEO N Q n q) := by
  rw [modAssociator_hom, assocHom_oddMap_tmulEO, assocFeo_tmulEE]

/-- The associator on the odd-odd-odd generators. -/
theorem modAssoc_oddMap_oo (m : M.odd) (n : N.odd) (q : Q.odd) :
    (α_ M N Q).hom.oddMap
        (tmulEO (M.tensor N) Q (tmulOO M N m n) q) =
      tmulOE M (N.tensor Q) m (tmulOO N Q n q) := by
  rw [modAssociator_hom, assocHom_oddMap_tmulEO, assocFeo_tmulOO]

/-- The associator on the even-odd-even generators. -/
theorem modAssoc_oddMap_eo (m : M.even) (n : N.odd) (q : Q.even) :
    (α_ M N Q).hom.oddMap
        (tmulOE (M.tensor N) Q (tmulEO M N m n) q) =
      tmulEO M (N.tensor Q) m (tmulOE N Q n q) := by
  rw [modAssociator_hom, assocHom_oddMap_tmulOE, assocFoe_tmulEO]

/-- The associator on the odd-even-even generators. -/
theorem modAssoc_oddMap_oe (m : M.odd) (n : N.even) (q : Q.even) :
    (α_ M N Q).hom.oddMap
        (tmulOE (M.tensor N) Q (tmulOE M N m n) q) =
      tmulOE M (N.tensor Q) m (tmulEE N Q n q) := by
  rw [modAssociator_hom, assocHom_oddMap_tmulOE, assocFoe_tmulOE]

end AssocSteps

section SuperVectSteps

variable {V W : SuperVect} (f : V ⟶ W) (X : SuperVect)

/-- Right whiskering of super vector spaces, first summand. -/
theorem svWhiskerRight_evenMap_inl (v : V.even) (x : X.even) :
    (f ▷ X).evenMap (svEvenInl (v ⊗ₜ[ℂ] x)) =
      svEvenInl ((f : V.Hom W).evenMap v ⊗ₜ[ℂ] x) := rfl

/-- Right whiskering of super vector spaces, second summand. -/
theorem svWhiskerRight_evenMap_inr (v : V.odd) (x : X.odd) :
    (f ▷ X).evenMap (svEvenInr (v ⊗ₜ[ℂ] x)) =
      svEvenInr ((f : V.Hom W).oddMap v ⊗ₜ[ℂ] x) := rfl

/-- Right whiskering of super vector spaces, odd degree, first
summand. -/
theorem svWhiskerRight_oddMap_inl (v : V.even) (x : X.odd) :
    (f ▷ X).oddMap (svOddInl (v ⊗ₜ[ℂ] x)) =
      svOddInl ((f : V.Hom W).evenMap v ⊗ₜ[ℂ] x) := rfl

/-- Right whiskering of super vector spaces, odd degree, second
summand. -/
theorem svWhiskerRight_oddMap_inr (v : V.odd) (x : X.even) :
    (f ▷ X).oddMap (svOddInr (v ⊗ₜ[ℂ] x)) =
      svOddInr ((f : V.Hom W).oddMap v ⊗ₜ[ℂ] x) := rfl

/-- Left whiskering of super vector spaces, first summand. -/
theorem svWhiskerLeft_evenMap_inl (x : X.even) (v : V.even) :
    (X ◁ f).evenMap (svEvenInl (x ⊗ₜ[ℂ] v)) =
      svEvenInl (x ⊗ₜ[ℂ] (f : V.Hom W).evenMap v) := rfl

/-- Left whiskering of super vector spaces, second summand. -/
theorem svWhiskerLeft_evenMap_inr (x : X.odd) (v : V.odd) :
    (X ◁ f).evenMap (svEvenInr (x ⊗ₜ[ℂ] v)) =
      svEvenInr (x ⊗ₜ[ℂ] (f : V.Hom W).oddMap v) := rfl

/-- Left whiskering of super vector spaces, odd degree, first
summand. -/
theorem svWhiskerLeft_oddMap_inl (x : X.even) (v : V.odd) :
    (X ◁ f).oddMap (svOddInl (x ⊗ₜ[ℂ] v)) =
      svOddInl (x ⊗ₜ[ℂ] (f : V.Hom W).oddMap v) := rfl

/-- Left whiskering of super vector spaces, odd degree, second
summand. -/
theorem svWhiskerLeft_oddMap_inr (x : X.odd) (v : V.even) :
    (X ◁ f).oddMap (svOddInr (x ⊗ₜ[ℂ] v)) =
      svOddInr (x ⊗ₜ[ℂ] (f : V.Hom W).evenMap v) := rfl

/-- Composition of super vector space morphisms, even degree, on
an element. -/
theorem svComp_evenMap_apply {V W Y : SuperVect} (f : V ⟶ W)
    (g : W ⟶ Y) (x : V.even) :
    ((f ≫ g : V ⟶ Y) : V.Hom Y).evenMap x =
      (g : W.Hom Y).evenMap ((f : V.Hom W).evenMap x) := rfl

/-- Composition of super vector space morphisms, odd degree, on an
element. -/
theorem svComp_oddMap_apply {V W Y : SuperVect} (f : V ⟶ W)
    (g : W ⟶ Y) (x : V.odd) :
    ((f ≫ g : V ⟶ Y) : V.Hom Y).oddMap x =
      (g : W.Hom Y).oddMap ((f : V.Hom W).oddMap x) := rfl

/-- The Koszul braiding on an even-even generator. -/
theorem svBraiding_evenMap_inl (V W : SuperVect) (x : V.even)
    (y : W.even) :
    ((β_ V W).hom : V ⊗ W ⟶ W ⊗ V).evenMap
      (svEvenInl (x ⊗ₜ[ℂ] y)) = svEvenInl (y ⊗ₜ[ℂ] x) := rfl

/-- The Koszul braiding on an odd-odd generator: this is where the
sign lives. -/
theorem svBraiding_evenMap_inr (V W : SuperVect) (x : V.odd)
    (y : W.odd) :
    ((β_ V W).hom : V ⊗ W ⟶ W ⊗ V).evenMap
        (svEvenInr (x ⊗ₜ[ℂ] y)) =
      -svEvenInr (y ⊗ₜ[ℂ] x) :=
  Prod.ext neg_zero.symm rfl

/-- The Koszul braiding on an even-odd generator. -/
theorem svBraiding_oddMap_inl (V W : SuperVect) (x : V.even)
    (y : W.odd) :
    ((β_ V W).hom : V ⊗ W ⟶ W ⊗ V).oddMap
      (svOddInl (x ⊗ₜ[ℂ] y)) = svOddInr (y ⊗ₜ[ℂ] x) := rfl

/-- The Koszul braiding on an odd-even generator. -/
theorem svBraiding_oddMap_inr (V W : SuperVect) (x : V.odd)
    (y : W.even) :
    ((β_ V W).hom : V ⊗ W ⟶ W ⊗ V).oddMap
      (svOddInr (x ⊗ₜ[ℂ] y)) = svOddInl (y ⊗ₜ[ℂ] x) := rfl

/-- The associator of super vector spaces on an even-even-even
generator. -/
theorem svAssoc_evenMap_ee (V W X : SuperVect) (a : V.even)
    (b : W.even) (c : X.even) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).evenMap
        (svEvenInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svEvenInl (a ⊗ₜ[ℂ] svEvenInl (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_ee a b c

/-- The associator on an odd-odd-even generator. -/
theorem svAssoc_evenMap_oo (V W X : SuperVect) (a : V.odd)
    (b : W.odd) (c : X.even) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).evenMap
        (svEvenInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svEvenInr (a ⊗ₜ[ℂ] svOddInr (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_oo a b c

/-- The associator on an even-odd-odd generator. -/
theorem svAssoc_evenMap_eo (V W X : SuperVect) (a : V.even)
    (b : W.odd) (c : X.odd) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).evenMap
        (svEvenInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svEvenInl (a ⊗ₜ[ℂ] svEvenInr (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_eo a b c

/-- The associator on an odd-even-odd generator. -/
theorem svAssoc_evenMap_oe (V W X : SuperVect) (a : V.odd)
    (b : W.even) (c : X.odd) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).evenMap
        (svEvenInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svEvenInr (a ⊗ₜ[ℂ] svOddInl (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_oe a b c

/-- The associator on an even-even-odd generator. -/
theorem svAssoc_oddMap_ee (V W X : SuperVect) (a : V.even)
    (b : W.even) (c : X.odd) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).oddMap
        (svOddInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svOddInl (a ⊗ₜ[ℂ] svOddInl (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_ee a b c

/-- The associator on an odd-odd-odd generator. -/
theorem svAssoc_oddMap_oo (V W X : SuperVect) (a : V.odd)
    (b : W.odd) (c : X.odd) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).oddMap
        (svOddInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svOddInr (a ⊗ₜ[ℂ] svEvenInr (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_oo a b c

/-- The associator on an even-odd-even generator. -/
theorem svAssoc_oddMap_eo (V W X : SuperVect) (a : V.even)
    (b : W.odd) (c : X.even) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).oddMap
        (svOddInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svOddInl (a ⊗ₜ[ℂ] svOddInr (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_eo a b c

/-- The associator on an odd-even-even generator. -/
theorem svAssoc_oddMap_oe (V W X : SuperVect) (a : V.odd)
    (b : W.even) (c : X.even) :
    ((α_ V W X).hom : (V ⊗ W) ⊗ X ⟶ V ⊗ (W ⊗ X)).oddMap
        (svOddInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
      svOddInr (a ⊗ₜ[ℂ] svEvenInl (b ⊗ₜ[ℂ] c)) :=
  SuperVect.assocAux_oe a b c

/-- The left unitor of super vector spaces on the first summand. -/
theorem svLeftUnitor_evenMap_inl (V : SuperVect) (r : ℂ)
    (x : V.even) :
    ((λ_ V).hom : 𝟙_ SuperVect ⊗ V ⟶ V).evenMap
      (svEvenInl (r ⊗ₜ[ℂ] x)) = r • x := rfl

/-- The left unitor in odd degree, on the first summand. -/
theorem svLeftUnitor_oddMap_inl (V : SuperVect) (r : ℂ)
    (y : V.odd) :
    ((λ_ V).hom : 𝟙_ SuperVect ⊗ V ⟶ V).oddMap
      (svOddInl (r ⊗ₜ[ℂ] y)) = r • y := rfl

/-- The right unitor of super vector spaces on the first
summand. -/
theorem svRightUnitor_evenMap_inl (V : SuperVect) (x : V.even)
    (r : ℂ) :
    ((ρ_ V).hom : V ⊗ 𝟙_ SuperVect ⟶ V).evenMap
      (svEvenInl (x ⊗ₜ[ℂ] r)) = r • x := rfl

/-- The right unitor in odd degree, on the second summand. -/
theorem svRightUnitor_oddMap_inr (V : SuperVect) (y : V.odd)
    (r : ℂ) :
    ((ρ_ V).hom : V ⊗ 𝟙_ SuperVect ⟶ V).oddMap
      (svOddInr (y ⊗ₜ[ℂ] r)) = r • y := rfl

end SuperVectSteps

section HomSteps

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  {M N : S.Mod.{u, u, u, u}}

/-- Base change of a morphism, in even degree, on an element. -/
theorem superVectHom_evenMap_apply
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    (u : M ⟶ N)
    (y : (toSuperVect P M).even) :
    (superVectHom P u).evenMap y =
      toSuperVectEvenEquiv P N
        ((u ▷ pointMod P).evenMap
          ((toSuperVectEvenEquiv P M).symm y)) := rfl

/-- Base change of a morphism, in odd degree, on an element. -/
theorem superVectHom_oddMap_apply
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    (u : M ⟶ N)
    (y : (toSuperVect P M).odd) :
    (superVectHom P u).oddMap y =
      toSuperVectOddEquiv P N
        ((u ▷ pointMod P).oddMap
          ((toSuperVectOddEquiv P M).symm y)) := rfl

end HomSteps

end Steps

/-! ## Extensionality for a threefold graded tensor product -/

section TripleExt

open scoped TensorProduct

/-- **Two linear maps out of a threefold graded tensor product
agree** as soon as they agree on the four families of generators.
Both components of a threefold product of super vector spaces are
of this shape, the two `C`-slots taken in the two orders. -/
theorem gradedTriple_ext {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    {f g : ((((A₁ ⊗[ℂ] B₁) × (A₂ ⊗[ℂ] B₂)) ⊗[ℂ] C₁) ×
        (((A₁ ⊗[ℂ] B₂) × (A₂ ⊗[ℂ] B₁)) ⊗[ℂ] C₂)) →ₗ[ℂ] Z}
    (h₁ : ∀ (a : A₁) (b : B₁) (c : C₁),
      f ((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0) = g ((a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c, 0))
    (h₂ : ∀ (a : A₂) (b : B₂) (c : C₁),
      f ((0, a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c, 0) = g ((0, a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c, 0))
    (h₃ : ∀ (a : A₁) (b : B₂) (c : C₂),
      f (0, (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c) = g (0, (a ⊗ₜ[ℂ] b, 0) ⊗ₜ[ℂ] c))
    (h₄ : ∀ (a : A₂) (b : B₁) (c : C₂),
      f (0, (0, a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c) =
        g (0, (0, a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) : f = g := by
  refine LinearMap.prod_ext (TensorProduct.ext' fun w c => ?_)
    (TensorProduct.ext' fun w c => ?_)
  · exact LinearMap.congr_fun (LinearMap.prod_ext
      (f := (f.comp (LinearMap.inl ℂ _ _)).comp
        ((TensorProduct.mk ℂ _ C₁).flip c))
      (g := (g.comp (LinearMap.inl ℂ _ _)).comp
        ((TensorProduct.mk ℂ _ C₁).flip c))
      (TensorProduct.ext' fun a b => h₁ a b c)
      (TensorProduct.ext' fun a b => h₂ a b c)) w
  · exact LinearMap.congr_fun (LinearMap.prod_ext
      (f := (f.comp (LinearMap.inr ℂ _ _)).comp
        ((TensorProduct.mk ℂ _ C₂).flip c))
      (g := (g.comp (LinearMap.inr ℂ _ _)).comp
        ((TensorProduct.mk ℂ _ C₂).flip c))
      (TensorProduct.ext' fun a b => h₃ a b c)
      (TensorProduct.ext' fun a b => h₄ a b c)) w

/-- **Extensionality for the even part of a threefold product of
super vector spaces.** -/
theorem superVectTripleEven_ext {V W X : SuperVect} {Z : Type*}
    [AddCommGroup Z] [Module ℂ Z]
    {f g : ((V ⊗ W) ⊗ X).even →ₗ[ℂ] Z}
    (h₁ : ∀ (a : V.even) (b : W.even) (c : X.even),
      f (svEvenInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svEvenInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₂ : ∀ (a : V.odd) (b : W.odd) (c : X.even),
      f (svEvenInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svEvenInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₃ : ∀ (a : V.even) (b : W.odd) (c : X.odd),
      f (svEvenInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svEvenInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₄ : ∀ (a : V.odd) (b : W.even) (c : X.odd),
      f (svEvenInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svEvenInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))) : f = g :=
  gradedTriple_ext h₁ h₂ h₃ h₄

/-- **Extensionality for the odd part of a threefold product of
super vector spaces.** -/
theorem superVectTripleOdd_ext {V W X : SuperVect} {Z : Type*}
    [AddCommGroup Z] [Module ℂ Z]
    {f g : ((V ⊗ W) ⊗ X).odd →ₗ[ℂ] Z}
    (h₁ : ∀ (a : V.even) (b : W.even) (c : X.odd),
      f (svOddInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svOddInl (svEvenInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₂ : ∀ (a : V.odd) (b : W.odd) (c : X.odd),
      f (svOddInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svOddInl (svEvenInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₃ : ∀ (a : V.even) (b : W.odd) (c : X.even),
      f (svOddInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svOddInr (svOddInl (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)))
    (h₄ : ∀ (a : V.odd) (b : W.even) (c : X.even),
      f (svOddInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)) =
        g (svOddInr (svOddInr (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c))) : f = g :=
  gradedTriple_ext h₁ h₂ h₃ h₄

/-- **Extensionality for the even part of a product of super
vector spaces.** -/
theorem superVectPairEven_ext {V W : SuperVect} {Z : Type*}
    [AddCommGroup Z] [Module ℂ Z] {f g : (V ⊗ W).even →ₗ[ℂ] Z}
    (h₁ : ∀ (a : V.even) (b : W.even),
      f (svEvenInl (a ⊗ₜ[ℂ] b)) = g (svEvenInl (a ⊗ₜ[ℂ] b)))
    (h₂ : ∀ (a : V.odd) (b : W.odd),
      f (svEvenInr (a ⊗ₜ[ℂ] b)) = g (svEvenInr (a ⊗ₜ[ℂ] b))) :
    f = g :=
  LinearMap.prod_ext (TensorProduct.ext' h₁) (TensorProduct.ext' h₂)

/-- **Extensionality for the odd part of a product of super vector
spaces.** -/
theorem superVectPairOdd_ext {V W : SuperVect} {Z : Type*}
    [AddCommGroup Z] [Module ℂ Z] {f g : (V ⊗ W).odd →ₗ[ℂ] Z}
    (h₁ : ∀ (a : V.even) (b : W.odd),
      f (svOddInl (a ⊗ₜ[ℂ] b)) = g (svOddInl (a ⊗ₜ[ℂ] b)))
    (h₂ : ∀ (a : V.odd) (b : W.even),
      f (svOddInr (a ⊗ₜ[ℂ] b)) = g (svOddInr (a ⊗ₜ[ℂ] b))) :
    f = g :=
  LinearMap.prod_ext (TensorProduct.ext' h₁) (TensorProduct.ext' h₂)

end TripleExt

end RS
