/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperGamma
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEmbed
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurTransport

/-!
# Instantiation of the Γ-algebra substrate at `Ind SmallSuperVect`

`RS.SuperGamma` builds the four-block super-commutative algebra
`superGammaAlgebra` of a commutative monoid object over any
braided ℂ-linear ambient with an odd line `(o, ho, hβ, hα)`.  This
file executes the instantiation plan recorded there: the ambient
is `Ind SmallSuperVect`, the odd line is the embedded odd
generator `indOf.obj sOdd`, and the three hypotheses are proved.

* The transported monoidal, symmetric and preadditive structure on
  `SmallSuperVect` is installed from `SuperVect` across the
  small-model equivalence (`Monoidal.transport`); the scalar unit
  `ℂ ≃+* End (𝟙_ SmallSuperVect)` follows by full faithfulness of
  the inclusion.

* The three odd-line facts are proved once, by hand, in
  `SuperVect` at the standard odd line `ℂ^{0|1}` (`hβ` is the
  existing `stdSuper_braiding_neg`; `hα` is the elementwise
  computation `superOdd_coherence`), then moved along functors by
  a reusable *braided comparison* calculus: a
  `RS.BraidedComparison F` packages a unit comparison, a tensor
  comparison, and the monoidal-functor axioms for `F`, and the
  odd-line data `(ho, hβ, hα)` transports forwards along any
  comparison (`coherence_map`, `braiding_neg_map`) and reflects
  backwards along a faithful one (`coherence_reflect`,
  `braiding_neg_reflect`).  Reflection along the small-model
  inclusion lands the facts on `sOdd`; forward transport along the
  embedding comparison of `indOf` (assembled from the
  `IndSchur`/`SchurTransport` lemmas as `indOfComparison`) lifts
  them to `Ind SmallSuperVect`.

* `superGammaAlgebraInd` assembles the resulting
  `RS.SuperCommAlgebra` for any commutative monoid object `R` of
  `Ind SmallSuperVect`, with the ℂ-linear structure installed from
  the scalar unit as in `RS.ScalarLinear`.
-/

namespace RS

noncomputable section

open CategoryTheory MonoidalCategory Limits

universe v v' u u'

/-! ## Braided comparisons and transport of odd-line data

A *braided comparison* on a functor between braided monoidal
categories is monoidal-functor data up to isomorphism: a unit
comparison, a tensor comparison, and the naturality, associativity,
unitality and braiding axioms.  `indOf` carries exactly this data
through the lemmas of `RS.IndTensorExact`, `RS.IndSchur` and
`RS.SchurTransport` without a registered `Functor.Monoidal`
instance, which is why the data is packaged explicitly rather than
through the Mathlib classes.  Right unitality is derived from left
unitality through the braiding, so it is not a field. -/

section Comparison

variable {C : Type u}

/-- Monoidal-functor data up to isomorphism on `F`, with the
braiding axiom: the odd-line transport interface. -/
structure BraidedComparison
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) where
  /-- The unit comparison. -/
  unitIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  /-- The tensor comparison. -/
  tensorIso : ∀ x y : C, F.obj x ⊗ F.obj y ≅ F.obj (x ⊗ y)
  /-- Naturality of the tensor comparison in the left factor. -/
  natural_left : ∀ {x x' : C} (f : x ⟶ x') (y : C),
    (F.map f ▷ F.obj y) ≫ (tensorIso x' y).hom =
      (tensorIso x y).hom ≫ F.map (f ▷ y)
  /-- Naturality of the tensor comparison in the right factor. -/
  natural_right : ∀ (x : C) {y y' : C} (g : y ⟶ y'),
    (F.obj x ◁ F.map g) ≫ (tensorIso x y').hom =
      (tensorIso x y).hom ≫ F.map (x ◁ g)
  /-- The associativity axiom. -/
  associativity : ∀ x y z : C,
    ((tensorIso x y).hom ▷ F.obj z) ≫ (tensorIso (x ⊗ y) z).hom ≫
        F.map (α_ x y z).hom =
      (α_ (F.obj x) (F.obj y) (F.obj z)).hom ≫
        (F.obj x ◁ (tensorIso y z).hom) ≫ (tensorIso x (y ⊗ z)).hom
  /-- The left unitality axiom. -/
  left_unitality : ∀ x : C,
    (λ_ (F.obj x)).hom = (unitIso.hom ▷ F.obj x) ≫
      (tensorIso (𝟙_ C) x).hom ≫ F.map (λ_ x).hom
  /-- The braiding axiom. -/
  braiding : ∀ x y : C,
    (β_ (F.obj x) (F.obj y)).hom ≫ (tensorIso y x).hom =
      (tensorIso x y).hom ≫ F.map (β_ x y).hom

namespace BraidedComparison

/-- A braided functor carries the canonical braided comparison. -/
def ofBraidedFunctor
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] :
    BraidedComparison F where
  unitIso := Functor.Monoidal.εIso F
  tensorIso x y := Functor.Monoidal.μIso F x y
  natural_left f y := Functor.LaxMonoidal.μ_natural_left F f y
  natural_right x {_ _} g :=
    Functor.LaxMonoidal.μ_natural_right F x g
  associativity x y z := Functor.LaxMonoidal.associativity F x y z
  left_unitality x := Functor.LaxMonoidal.left_unitality F x
  braiding x y := (Functor.LaxBraided.braided x y).symm

/-- **Right unitality is derived**: the braiding turns the right
unitor of `F.obj x` into its left unitor, the braiding axiom
carries the braiding downstairs, and the braiding identity of the
base returns the right unitor. -/
theorem right_unitality
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (x : C) :
    (ρ_ (F.obj x)).hom = (F.obj x ◁ P.unitIso.hom) ≫
      (P.tensorIso x (𝟙_ C)).hom ≫ F.map (ρ_ x).hom := by
  rw [← braiding_leftUnitor (F.obj x), P.left_unitality x,
    ← BraidedCategory.braiding_naturality_right_assoc,
    reassoc_of% P.braiding x (𝟙_ C), ← Functor.map_comp,
    braiding_leftUnitor]

/-- The transported odd-square trivialization: conjugate `ho` by
the tensor and unit comparisons. -/
def square
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (o : C)
    (ho : o ⊗ o ≅ 𝟙_ C) : F.obj o ⊗ F.obj o ≅ 𝟙_ D :=
  P.tensorIso o o ≪≫ F.mapIso ho ≪≫ P.unitIso.symm

/-- The inverse of the transported odd square, in components. -/
theorem square_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (o : C)
    (ho : o ⊗ o ≅ 𝟙_ C) :
    (P.square o ho).inv =
      P.unitIso.hom ≫ F.map ho.inv ≫ (P.tensorIso o o).inv := by
  simp [square]

/-- Inverse form of left unitality. -/
theorem leftUnitor_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (x : C) :
    (λ_ (F.obj x)).inv = F.map (λ_ x).inv ≫
      (P.tensorIso (𝟙_ C) x).inv ≫ (P.unitIso.inv ▷ F.obj x) := by
  have h : λ_ (F.obj x) =
      whiskerRightIso P.unitIso (F.obj x) ≪≫
        P.tensorIso (𝟙_ C) x ≪≫ F.mapIso (λ_ x) :=
    Iso.ext (by simpa using P.left_unitality x)
  rw [h]
  simp

/-- Inverse form of right unitality. -/
theorem rightUnitor_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (x : C) :
    (ρ_ (F.obj x)).inv = F.map (ρ_ x).inv ≫
      (P.tensorIso x (𝟙_ C)).inv ≫ (F.obj x ◁ P.unitIso.inv) := by
  have h : ρ_ (F.obj x) =
      whiskerLeftIso (F.obj x) P.unitIso ≪≫
        P.tensorIso x (𝟙_ C) ≪≫ F.mapIso (ρ_ x) :=
    Iso.ext (by simpa using P.right_unitality x)
  rw [h]
  simp

/-- Inverse form of naturality in the left factor. -/
theorem natural_left_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F)
    {x x' : C} (f : x ⟶ x') (y : C) :
    (P.tensorIso x y).inv ≫ (F.map f ▷ F.obj y) =
      F.map (f ▷ y) ≫ (P.tensorIso x' y).inv := by
  rw [← cancel_mono (P.tensorIso x' y).hom]
  simp only [Category.assoc]
  rw [P.natural_left f y, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- Inverse form of naturality in the right factor. -/
theorem natural_right_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F)
    (x : C) {y y' : C} (g : y ⟶ y') :
    (P.tensorIso x y).inv ≫ (F.obj x ◁ F.map g) =
      F.map (x ◁ g) ≫ (P.tensorIso x y').inv := by
  rw [← cancel_mono (P.tensorIso x y').hom]
  simp only [Category.assoc]
  rw [P.natural_right x g, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- Inverse form of associativity. -/
theorem associativity_inv
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (x y z : C) :
    (P.tensorIso (x ⊗ y) z).inv ≫
        ((P.tensorIso x y).inv ▷ F.obj z) ≫
        (α_ (F.obj x) (F.obj y) (F.obj z)).hom =
      F.map (α_ x y z).hom ≫ (P.tensorIso x (y ⊗ z)).inv ≫
        (F.obj x ◁ (P.tensorIso y z).inv) := by
  rw [← cancel_mono (F.obj x ◁ (P.tensorIso y z).hom),
    ← cancel_mono (P.tensorIso x (y ⊗ z)).hom]
  simp only [Category.assoc]
  rw [← P.associativity x y z,
    MonoidalCategory.inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc,
    MonoidalCategory.whiskerLeft_inv_hom_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **The left odd-line pattern in components**: the transported
form of `(λ_ o).inv ≫ ho.inv ▷ o ≫ (α_ o o o).hom` is the image of
the pattern downstairs, followed by the inverse triple-tensor
comparison. -/
theorem conv_left
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (o : C)
    (ho : o ⊗ o ≅ 𝟙_ C) :
    (λ_ (F.obj o)).inv ≫ ((P.square o ho).inv ▷ F.obj o) ≫
        (α_ (F.obj o) (F.obj o) (F.obj o)).hom =
      F.map ((λ_ o).inv ≫ (ho.inv ▷ o) ≫ (α_ o o o).hom) ≫
        (P.tensorIso o (o ⊗ o)).inv ≫
        (F.obj o ◁ (P.tensorIso o o).inv) := by
  rw [P.leftUnitor_inv o, P.square_inv o ho]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
    Functor.map_comp]
  rw [MonoidalCategory.inv_hom_whiskerRight_assoc,
    reassoc_of% P.natural_left_inv ho.inv o,
    P.associativity_inv o o o]

/-- **The right odd-line pattern in components**: the transported
form of `(ρ_ o).inv ≫ o ◁ ho.inv` is the image of the pattern
downstairs, followed by the same inverse comparison. -/
theorem conv_right
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (o : C)
    (ho : o ⊗ o ≅ 𝟙_ C) :
    (ρ_ (F.obj o)).inv ≫ (F.obj o ◁ (P.square o ho).inv) =
      F.map ((ρ_ o).inv ≫ (o ◁ ho.inv)) ≫
        (P.tensorIso o (o ⊗ o)).inv ≫
        (F.obj o ◁ (P.tensorIso o o).inv) := by
  rw [P.rightUnitor_inv o, P.square_inv o ho]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.map_comp]
  rw [MonoidalCategory.whiskerLeft_inv_hom_assoc,
    reassoc_of% P.natural_right_inv o ho.inv]

/-- **Forward transport of the odd-cubed coherence**: the
hypothesis `hα` of `RS.superGammaAlgebra` moves along any braided
comparison. -/
theorem coherence_map
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) (o : C)
    (ho : o ⊗ o ≅ 𝟙_ C)
    (hα : (λ_ o).inv ≫ (ho.inv ▷ o) ≫ (α_ o o o).hom =
      (ρ_ o).inv ≫ (o ◁ ho.inv)) :
    (λ_ (F.obj o)).inv ≫ ((P.square o ho).inv ▷ F.obj o) ≫
        (α_ (F.obj o) (F.obj o) (F.obj o)).hom =
      (ρ_ (F.obj o)).inv ≫ (F.obj o ◁ (P.square o ho).inv) := by
  rw [P.conv_left o ho, P.conv_right o ho, hα]

/-- **Reflection of the odd-cubed coherence**: along a faithful
braided comparison, `hα` downstairs at the transported square
forces `hα` upstairs. -/
theorem coherence_reflect
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    (P : BraidedComparison F) [F.Faithful]
    (o : C) (ho : o ⊗ o ≅ 𝟙_ C)
    (hα : (λ_ (F.obj o)).inv ≫
        ((P.square o ho).inv ▷ F.obj o) ≫
        (α_ (F.obj o) (F.obj o) (F.obj o)).hom =
      (ρ_ (F.obj o)).inv ≫ (F.obj o ◁ (P.square o ho).inv)) :
    (λ_ o).inv ≫ (ho.inv ▷ o) ≫ (α_ o o o).hom =
      (ρ_ o).inv ≫ (o ◁ ho.inv) := by
  apply F.map_injective
  have h := (P.conv_left o ho).symm.trans
    (hα.trans (P.conv_right o ho))
  have h2 := congrArg
    (fun m => m ≫ (F.obj o ◁ (P.tensorIso o o).hom) ≫
      (P.tensorIso o (o ⊗ o)).hom) h
  simpa only [Category.assoc,
    MonoidalCategory.whiskerLeft_inv_hom_assoc,
    Iso.inv_hom_id, Category.comp_id] using h2

/-- **Forward transport of the odd braiding sign** along an
additive braided comparison. -/
theorem braiding_neg_map
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    [Preadditive C] [Preadditive D]
    [F.Additive] (P : BraidedComparison F) {o : C}
    (hβ : (β_ o o).hom = -𝟙 (o ⊗ o)) :
    (β_ (F.obj o) (F.obj o)).hom =
      -𝟙 (F.obj o ⊗ F.obj o) := by
  have h := P.braiding o o
  rw [hβ, F.map_neg, F.map_id, Preadditive.comp_neg,
    Category.comp_id] at h
  calc (β_ (F.obj o) (F.obj o)).hom
      = ((β_ (F.obj o) (F.obj o)).hom ≫
          (P.tensorIso o o).hom) ≫ (P.tensorIso o o).inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = -𝟙 (F.obj o ⊗ F.obj o) := by
        rw [h, Preadditive.neg_comp, Iso.hom_inv_id]

/-- **Reflection of the odd braiding sign** along a faithful
additive braided comparison. -/
theorem braiding_neg_reflect
    [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {D : Type u'}
    [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D] {F : C ⥤ D}
    [Preadditive C] [Preadditive D]
    [F.Additive] [F.Faithful] (P : BraidedComparison F) {o : C}
    (hβ : (β_ (F.obj o) (F.obj o)).hom =
      -𝟙 (F.obj o ⊗ F.obj o)) :
    (β_ o o).hom = -𝟙 (o ⊗ o) := by
  apply F.map_injective
  have h := P.braiding o o
  rw [hβ, Preadditive.neg_comp, Category.id_comp] at h
  rw [F.map_neg, F.map_id]
  calc F.map (β_ o o).hom
      = (P.tensorIso o o).inv ≫ ((P.tensorIso o o).hom ≫
          F.map (β_ o o).hom) := by rw [Iso.inv_hom_id_assoc]
    _ = -𝟙 (F.obj (o ⊗ o)) := by
        rw [← h, Preadditive.comp_neg, Iso.inv_hom_id]

end BraidedComparison

end Comparison

/-! ## The odd line of `SuperVect`, trivialized

The standard odd line `ℂ^{0|1}` of `SuperVect` carries the
trivialization `superOddSquare : ℂ^{0|1} ⊗ ℂ^{0|1} ≅ 𝟙`, pairing
the two odd generators; its braiding sign is
`RS.stdSuper_braiding_neg`, and the odd-cubed coherence `hα` is
the elementwise computation `superOdd_coherence`: both insertions
of the trivialized square send the odd generator `e` to
`e ⊗ e ⊗ e`. -/

section SuperVectOdd

open scoped TensorProduct

/-- Every element of a tensor product with a subsingleton factor
on the left vanishes. -/
private theorem tensor_zero_left {A M : Type} [AddCommGroup A]
    [Module ℂ A] [Subsingleton A] [AddCommGroup M] [Module ℂ M]
    (z : A ⊗[ℂ] M) : z = 0 := by
  have h0 : (LinearMap.id : A →ₗ[ℂ] A) = 0 :=
    Subsingleton.elim _ _
  calc z = TensorProduct.map LinearMap.id LinearMap.id z := by
        rw [TensorProduct.map_id]; rfl
    _ = TensorProduct.map 0 LinearMap.id z := by rw [h0]
    _ = 0 := by rw [TensorProduct.map_zero_left]; rfl

/-- Every element of a tensor product with a subsingleton factor
on the right vanishes. -/
private theorem tensor_zero_right {A M : Type} [AddCommGroup A]
    [Module ℂ A] [Subsingleton A] [AddCommGroup M] [Module ℂ M]
    (z : M ⊗[ℂ] A) : z = 0 := by
  have h0 : (LinearMap.id : A →ₗ[ℂ] A) = 0 :=
    Subsingleton.elim _ _
  calc z = TensorProduct.map LinearMap.id LinearMap.id z := by
        rw [TensorProduct.map_id]; rfl
    _ = TensorProduct.map LinearMap.id 0 z := by rw [h0]
    _ = 0 := by rw [TensorProduct.map_zero_right]; rfl

private instance {A M : Type} [AddCommGroup A] [Module ℂ A]
    [Subsingleton A] [AddCommGroup M] [Module ℂ M] :
    Subsingleton (A ⊗[ℂ] M) :=
  ⟨fun a b => by rw [tensor_zero_left a, tensor_zero_left b]⟩

private instance {A M : Type} [AddCommGroup A] [Module ℂ A]
    [Subsingleton A] [AddCommGroup M] [Module ℂ M] :
    Subsingleton (M ⊗[ℂ] A) :=
  ⟨fun a b => by rw [tensor_zero_right a, tensor_zero_right b]⟩

private instance : Subsingleton (stdSuper 0 1).even :=
  inferInstanceAs (Subsingleton (Fin 0 → ℂ))

private instance : Subsingleton (𝟙_ SuperVect).odd :=
  inferInstanceAs (Subsingleton PUnit)

private instance : Subsingleton (stdSuper 0 1 ⊗ stdSuper 0 1).odd :=
  inferInstanceAs (Subsingleton
    (((stdSuper 0 1).even ⊗[ℂ] (stdSuper 0 1).odd) ×
      ((stdSuper 0 1).odd ⊗[ℂ] (stdSuper 0 1).even)))

/-- A product with a subsingleton first factor is its second
factor. -/
private def prodZeroEquiv (A M : Type) [AddCommGroup A]
    [Module ℂ A] [AddCommGroup M] [Module ℂ M] [Subsingleton A] :
    (A × M) ≃ₗ[ℂ] M where
  toFun p := p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := (0, m)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

/-- The square of the scalar line, trivialized. -/
private def lineTensorEquiv :
    (Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ) ≃ₗ[ℂ] ℂ :=
  TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ) ≪≫ₗ TensorProduct.lid ℂ ℂ

/-- **The trivialization of the odd square in `SuperVect`**: the
even component pairs the two odd lines through `lineTensorEquiv`,
and the odd component is trivial. -/
def superOddSquare : stdSuper 0 1 ⊗ stdSuper 0 1 ≅ 𝟙_ SuperVect :=
  SuperVect.isoOfEquivs
    (prodZeroEquiv _ _ ≪≫ₗ lineTensorEquiv)
    (zeroLinearEquiv _ _)

/-- The odd generator of the standard odd line. -/
private def oddGen : Fin 1 → ℂ := fun _ => 1

private theorem oddGen_rep (x : Fin 1 → ℂ) : x = x 0 • oddGen := by
  funext i
  rw [Subsingleton.elim i 0]
  simp [oddGen]

/-- The inverse even component of the trivialization sends `1` to
the pairing tensor of the two odd generators. -/
private theorem superOddSquare_inv_evenMap_one :
    superOddSquare.inv.evenMap (1 : ℂ) =
      ((0 : (Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)),
        oddGen ⊗ₜ[ℂ] oddGen) := by
  show (prodZeroEquiv ((Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ))
      ((Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ)) ≪≫ₗ
        lineTensorEquiv).symm.toLinearMap (1 : ℂ) = _
  have hg : (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm 1 = oddGen :=
    rfl
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, lineTensorEquiv,
    TensorProduct.lid_symm_apply, TensorProduct.congr_symm_tmul,
    hg]
  rfl

/-- The pivot of the odd-cubed coherence: on the line, tensoring
the generator against the paired generator-and-argument agrees
with tensoring the argument against the paired generators. -/
private theorem line_pair_swap (x : Fin 1 → ℂ) :
    oddGen ⊗ₜ[ℂ]
        (((0 : (Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)),
            oddGen ⊗ₜ[ℂ] x) :
          ((Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)) ×
            ((Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ))) =
      x ⊗ₜ[ℂ] (0, oddGen ⊗ₜ[ℂ] oddGen) := by
  have h1 : (((0 : (Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)),
      oddGen ⊗ₜ[ℂ] (x 0 • oddGen)) :
      ((Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)) ×
        ((Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ))) =
      x 0 • (0, oddGen ⊗ₜ[ℂ] oddGen) := by
    refine Prod.ext ?_ ?_
    · exact Subsingleton.elim _ _
    · show oddGen ⊗ₜ[ℂ] (x 0 • oddGen) =
        x 0 • (oddGen ⊗ₜ[ℂ] oddGen)
      rw [TensorProduct.tmul_smul]
  conv_lhs => rw [oddGen_rep x]
  conv_rhs => rw [oddGen_rep x]
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- The odd-cubed coherence of `SuperVect`, in raw components: the
two composites agree on every argument, for any inverse components
`E`, `O` of a trivialization whose even part pairs the odd
generators. -/
private theorem raw_coherence (E : ℂ →ₗ[ℂ] ((Fin 0 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)) ×
        ((Fin 1 → ℂ) ⊗[ℂ] (Fin 1 → ℂ)))
    (O : PUnit →ₗ[ℂ] ((Fin 0 → ℂ) ⊗[ℂ] (Fin 1 → ℂ)) ×
        ((Fin 1 → ℂ) ⊗[ℂ] (Fin 0 → ℂ)))
    (hE : E 1 = (0, oddGen ⊗ₜ[ℂ] oddGen)) (x : Fin 1 → ℂ) :
    (SuperVect.assocAux (Fin 0 → ℂ) (Fin 1 → ℂ) (Fin 0 → ℂ)
        (Fin 1 → ℂ) (Fin 1 → ℂ) (Fin 0 → ℂ)).toLinearMap
      (LinearMap.prodMap (TensorProduct.map E LinearMap.id)
        (TensorProduct.map O LinearMap.id)
        ((LinearMap.inl ℂ (ℂ ⊗[ℂ] (Fin 1 → ℂ))
            (PUnit ⊗[ℂ] (Fin 0 → ℂ)) ∘ₗ
          (TensorProduct.lid ℂ (Fin 1 → ℂ)).symm.toLinearMap)
          x)) =
    LinearMap.prodMap (TensorProduct.map LinearMap.id O)
        (TensorProduct.map LinearMap.id E)
      ((LinearMap.inr ℂ ((Fin 0 → ℂ) ⊗[ℂ] PUnit)
          ((Fin 1 → ℂ) ⊗[ℂ] ℂ) ∘ₗ
        (TensorProduct.rid ℂ (Fin 1 → ℂ)).symm.toLinearMap)
        x) := by
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_symm_apply,
    TensorProduct.rid_symm_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, LinearMap.prodMap_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, map_zero, hE]
  have h := assocAux_pure (0 : Fin 0 → ℂ) oddGen
    (0 : Fin 0 → ℂ) oddGen x (0 : Fin 0 → ℂ)
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    at h
  rw [h]
  exact Prod.ext rfl (line_pair_swap x)

/-- **The odd-cubed coherence holds in `SuperVect`** at the
standard odd line: both insertions of the trivialized square send
the odd generator to the triple tensor of generators. -/
theorem superOdd_coherence :
    (λ_ (stdSuper 0 1)).inv ≫
        (superOddSquare.inv ▷ stdSuper 0 1) ≫
        (α_ (stdSuper 0 1) (stdSuper 0 1) (stdSuper 0 1)).hom =
      (ρ_ (stdSuper 0 1)).inv ≫
        (stdSuper 0 1 ◁ superOddSquare.inv) := by
  apply SuperVect.hom_ext
  · exact Subsingleton.elim _ _
  · exact LinearMap.ext fun x =>
      raw_coherence superOddSquare.inv.evenMap
        superOddSquare.inv.oddMap superOddSquare_inv_evenMap_one x

end SuperVectOdd

/-! ## The transported structure on the small model

`SmallSuperVect` receives the monoidal and symmetric structure of
`SuperVect` across the small-model equivalence, by
`Monoidal.transport`; the inclusion is then monoidal, braided,
faithful and additive, so preadditivity of the tensor and the
scalar unit follow by reflection. -/

section SmallModel

/-- The monoidal structure of the small model, transported from
`SuperVect` across the small-model equivalence. -/
noncomputable instance : MonoidalCategory SmallSuperVect :=
  Monoidal.transport smallSuperEquiv.symm

/-- The symmetry of the small model. -/
noncomputable instance : SymmetricCategory SmallSuperVect :=
  inferInstanceAs
    (SymmetricCategory (Monoidal.Transported smallSuperEquiv.symm))

/-- The inclusion is monoidal for the transported structure. -/
noncomputable instance : smallSuperInclusion.Monoidal :=
  inferInstanceAs
    ((Monoidal.equivalenceTransported
      smallSuperEquiv.symm).inverse.Monoidal)

/-- The inclusion is braided for the transported structure. -/
noncomputable instance : smallSuperInclusion.Braided :=
  inferInstanceAs
    ((Monoidal.equivalenceTransported
      smallSuperEquiv.symm).inverse.Braided)

/-- The small model is monoidal preadditive, by reflection along
the faithful additive monoidal inclusion. -/
noncomputable instance : MonoidalPreadditive SmallSuperVect :=
  monoidalPreadditive_of_faithful smallSuperInclusion

/-- The even component of a unit endomorphism, at the scalar
type. -/
private def unitEvenMap (f : End (𝟙_ SuperVect)) : ℂ →ₗ[ℂ] ℂ :=
  f.evenMap

/-- **The scalar unit of `SuperVect`**: endomorphisms of the
monoidal unit are the scalars. -/
def superVectScalarUnit : ℂ ≃+* End (𝟙_ SuperVect) where
  toFun c := ⟨c • (LinearMap.id : ℂ →ₗ[ℂ] ℂ), 0⟩
  invFun f := unitEvenMap f 1
  left_inv c := by
    show (c • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) 1 = c
    simp
  right_inv f := by
    apply SuperVect.hom_ext
    · show (unitEvenMap f 1) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) =
        unitEvenMap f
      refine LinearMap.ext fun z => ?_
      calc (unitEvenMap f 1 • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) z
          = z • unitEvenMap f 1 := by
            show unitEvenMap f 1 * z = _
            rw [smul_eq_mul, mul_comm]
        _ = unitEvenMap f (z • 1) :=
            (map_smul (unitEvenMap f) z 1).symm
        _ = unitEvenMap f z := by
            rw [smul_eq_mul, mul_one]
    · exact Subsingleton.elim _ _
  map_mul' a b := by
    apply SuperVect.hom_ext
    · show (a * b) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) =
        (a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) ∘ₗ
          (b • (LinearMap.id : ℂ →ₗ[ℂ] ℂ))
      refine LinearMap.ext fun z => ?_
      show (a * b) * z = a * (b * z)
      rw [mul_assoc]
    · exact Subsingleton.elim _ _
  map_add' a b := by
    apply SuperVect.hom_ext
    · show (a + b) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) =
        a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) +
          b • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      exact add_smul a b _
    · exact Subsingleton.elim _ _

/-- Full faithfulness of the inclusion on endomorphisms, as a ring
isomorphism; `End`-multiplication is reversed composition on both
sides, and the inclusion is functorial on the nose. -/
def smallEndRingEquiv (x : SmallSuperVect) :
    End x ≃+* End (smallSuperInclusion.obj x) :=
  { InducedCategory.homAddEquiv (C := SuperVect)
      (F := SuperVect.stdObj) (X := x) (Y := x) with
    map_mul' := fun _ _ => rfl }

/-- **The scalar unit of the small model**: transport the scalar
unit of `SuperVect` along the unit comparison of the inclusion and
pull back by full faithfulness. -/
def smallScalarUnit : ℂ ≃+* End (𝟙_ SmallSuperVect) :=
  (superVectScalarUnit.trans
    (endCongrRingEquiv
      (Functor.Monoidal.εIso smallSuperInclusion))).trans
    (smallEndRingEquiv (𝟙_ SmallSuperVect)).symm

/-- The canonical braided comparison on the inclusion. -/
noncomputable def smallComparison :
    BraidedComparison smallSuperInclusion :=
  BraidedComparison.ofBraidedFunctor smallSuperInclusion

/-- **The trivialized odd square of the small model**: the
`SuperVect` trivialization of the embedded odd generator, pulled
back through the fully faithful inclusion. -/
noncomputable def smallOddSquare : sOdd ⊗ sOdd ≅ 𝟙_ SmallSuperVect :=
  (fullyFaithfulInducedFunctor SuperVect.stdObj).preimageIso
    ((Functor.Monoidal.μIso smallSuperInclusion sOdd sOdd).symm ≪≫
      superOddSquare ≪≫
      Functor.Monoidal.εIso smallSuperInclusion)

/-- The comparison square of `smallOddSquare` is the `SuperVect`
trivialization it was pulled back from. -/
theorem smallComparison_square :
    smallComparison.square sOdd smallOddSquare = superOddSquare := by
  refine Iso.ext ?_
  show (Functor.Monoidal.μIso smallSuperInclusion sOdd sOdd).hom ≫
      smallSuperInclusion.map smallOddSquare.hom ≫
      (Functor.Monoidal.εIso smallSuperInclusion).inv =
    superOddSquare.hom
  rw [smallOddSquare, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  erw [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The braiding sign at the small odd generator**, by
reflection along the inclusion from `RS.stdSuper_braiding_neg`. -/
theorem smallOdd_braiding :
    (β_ sOdd sOdd).hom = -𝟙 (sOdd ⊗ sOdd) :=
  smallComparison.braiding_neg_reflect stdSuper_braiding_neg

/-- **The odd-cubed coherence at the small odd generator**, by
reflection along the inclusion from `RS.superOdd_coherence`. -/
theorem smallOdd_coherence :
    (λ_ sOdd).inv ≫ (smallOddSquare.inv ▷ sOdd) ≫
        (α_ sOdd sOdd sOdd).hom =
      (ρ_ sOdd).inv ≫ (sOdd ◁ smallOddSquare.inv) :=
  smallComparison.coherence_reflect sOdd smallOddSquare
    (by rw [smallComparison_square]; exact superOdd_coherence)

end SmallModel

/-! ## The embedding comparison of `indOf` -/

section IndComparison

variable {C : Type v}

/-- **The braided comparison of the ind-embedding**: the unit and
tensor comparisons of `RS.IndSchur` and `RS.SchurTransport`
assemble into a braided comparison on `indOf`, over any braided
small base. -/
def indOfComparison [SmallCategory C] [MonoidalCategory C] [BraidedCategory C] :
    BraidedComparison (indOf (C := C)) where
  unitIso := indOfUnitIso
  tensorIso x y := indOfTensorIso x y
  natural_left f y := indOfTensorIso_hom_natural_left f y
  natural_right x {_ _} g := indOfTensorIso_hom_natural_right x g
  associativity x y z := indOfTensorIso_hom_associator x y z
  left_unitality x := indOf_leftUnitor_hom x
  braiding x y := indOfTensorIso_hom_braiding x y

end IndComparison

/-! ## The odd line of `Ind SmallSuperVect` and the Γ-algebra -/

section IndAssembly

/-- **The odd line of the instantiated ambient**: the embedded odd
generator of the small model. -/
def indOddLine : Ind SmallSuperVect := indOf.obj sOdd

/-- **The trivialized odd square of the ambient**: the transported
small-model trivialization. -/
def indOddSquare :
    indOddLine ⊗ indOddLine ≅ 𝟙_ (Ind SmallSuperVect) :=
  indOfComparison.square sOdd smallOddSquare

/-- **The braiding sign at the odd line of the ambient**: the
hypothesis `hβ` of `RS.superGammaAlgebra`. -/
theorem indOdd_braiding :
    (β_ indOddLine indOddLine).hom =
      -𝟙 (indOddLine ⊗ indOddLine) :=
  haveI := indOf_additive (C := SmallSuperVect)
  indOfComparison.braiding_neg_map smallOdd_braiding

/-- **The odd-cubed coherence at the odd line of the ambient**:
the hypothesis `hα` of `RS.superGammaAlgebra`. -/
theorem indOdd_coherence :
    (λ_ indOddLine).inv ≫ (indOddSquare.inv ▷ indOddLine) ≫
        (α_ indOddLine indOddLine indOddLine).hom =
      (ρ_ indOddLine).inv ≫ (indOddLine ◁ indOddSquare.inv) :=
  indOfComparison.coherence_map sOdd smallOddSquare
    smallOdd_coherence

/-- **The Γ-algebra of the instantiated ambient**: for any
commutative monoid object `R` of `Ind SmallSuperVect`, the
morphisms out of the unit and out of the embedded odd generator
form a super-commutative ℂ-algebra under prefixed convolution —
`RS.superGammaAlgebra` at the odd line `indOddLine`, with the
ℂ-linear structure installed from the scalar unit of the small
model as in `RS.ScalarLinear`. -/
def superGammaAlgebraInd (R : Ind SmallSuperVect) [MonObj R]
    [IsCommMonObj R] : SuperCommAlgebra :=
  letI := linearOfScalarUnit (indScalarUnit smallScalarUnit)
  haveI : MonoidalLinear ℂ (Ind SmallSuperVect) :=
    monoidalLinearOfScalarUnitBraided
      (indScalarUnit smallScalarUnit)
  superGammaAlgebra R indOddLine indOddSquare indOdd_braiding
    indOdd_coherence

/-! ## Acceptance -/

/- The carriers are the ones recorded in the instantiation plan:
`R`-valued points of the unit and of the embedded odd generator. -/

example (R : Ind SmallSuperVect) [MonObj R] [IsCommMonObj R] :
    (superGammaAlgebraInd R).even =
      (𝟙_ (Ind SmallSuperVect) ⟶ R) := rfl

example (R : Ind SmallSuperVect) [MonObj R] [IsCommMonObj R] :
    (superGammaAlgebraInd R).odd = (indOf.obj sOdd ⟶ R) := rfl

end IndAssembly

end

end RS
