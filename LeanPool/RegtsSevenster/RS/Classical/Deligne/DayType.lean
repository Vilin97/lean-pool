/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Day convolution on `Type`-valued functor categories

Mathlib equips the type synonym `C ⊛⥤ V` (`MonoidalCategory.DayFunctor`)
with the Day-convolution monoidal structure, subject to instance
hypotheses: existence of the relevant pointwise left Kan extensions and
preservation of colimits of the relevant costructured-arrow shapes by
`tensorLeft`/`tensorRight` in `V`.  For `V := Type v` and `C` a small
monoidal category all of these hold via instances that Mathlib already
provides (`Type v` is monoidal closed and braided, so both tensoring
functors are left adjoints and preserve all colimits, and `Type v` has
all small colimits); the imports of `Closed.Types` and `Closed.Braided`
above are exactly what makes them synthesise.

What Mathlib does not provide is a braided (or symmetric) structure
on `C ⊛⥤ V`: `Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided`
constructs the braiding and proves the hexagons at the level of
individual `DayConvolution` structures on plain functors, but never
assembles them into a `BraidedCategory (C ⊛⥤ V)` instance.  This file
performs that assembly, at the same generality as Mathlib's
`MonoidalCategory (C ⊛⥤ V)` instance, and records the acceptance tests
for `V := Type v` at the bottom.

The Mathlib imports above are deliberate exceptions to the
`RS.Common.MathlibDeps` funnel: the Day-convolution modules are not
reachable from it.
-/

namespace RS

open CategoryTheory MonoidalCategory MonoidalCategory.DayFunctor Limits
open scoped MonoidalCategory.ExternalProduct
open scoped MonoidalCategory.DayConvolution

universe v v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁}

/-- The underlying functor of a tensor product in `C ⊛⥤ V` is a Day
convolution of the underlying functors.  Local instance: Mathlib advises
against registering `DayConvolution` instances globally. -/
local instance dayConv
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F G : C ⊛⥤ V) :
    DayConvolution F.functor G.functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution C V (C ⊛⥤ V) F G

/-- Right-nested triple Day convolutions, phrased so that instance search
finds them behind the `⊛` notation. -/
local instance dayConv₂
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F G H : C ⊛⥤ V) :
    DayConvolution F.functor (G.functor ⊛ H.functor) :=
  dayConv F (G ⊗ H)

/-- Left-nested triple Day convolutions, phrased so that instance search
finds them behind the `⊛` notation. -/
local instance dayConv₂'
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F G H : C ⊛⥤ V) :
    DayConvolution (F.functor ⊛ G.functor) H.functor :=
  dayConv (F ⊗ G) H

/-- The underlying natural transformation of a tensor product of
morphisms of `C ⊛⥤ V` is the induced morphism of Day convolutions. -/
lemma natTrans_tensorHom
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    {F F' G G' : C ⊛⥤ V} (f : F ⟶ F') (g : G ⟶ G') :
    (f ⊗ₘ g).natTrans = DayConvolution.map f.natTrans g.natTrans :=
  LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom
    (C := C) (V := V) (D := C ⊛⥤ V) f g

/-- Left whiskering in `C ⊛⥤ V`, read off on underlying natural
transformations. -/
lemma natTrans_whiskerLeft
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F : C ⊛⥤ V) {G H : C ⊛⥤ V} (g : G ⟶ H) :
    (F ◁ g).natTrans = DayConvolution.map (𝟙 F.functor) g.natTrans := by
  rw [← MonoidalCategory.id_tensorHom, natTrans_tensorHom]
  rfl

/-- Right whiskering in `C ⊛⥤ V`, read off on underlying natural
transformations. -/
lemma natTrans_whiskerRight
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    {F G : C ⊛⥤ V} (f : F ⟶ G) (H : C ⊛⥤ V) :
    (f ▷ H).natTrans = DayConvolution.map f.natTrans (𝟙 H.functor) := by
  rw [← MonoidalCategory.tensorHom_id, natTrans_tensorHom]
  rfl

open LawfulDayConvolutionMonoidalCategoryStruct in
/-- The associator of `C ⊛⥤ V`, read off on underlying natural
transformations. -/
lemma natTrans_associator
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F G H : C ⊛⥤ V) :
    (α_ F G H).hom.natTrans =
    (DayConvolution.associator F.functor G.functor H.functor).hom :=
  ι_map_associator_hom_eq_associator_hom
    (C := C) (V := V) (D := C ⊛⥤ V) F G H

/-- Inverse form of `RS.natTrans_associator`. -/
lemma natTrans_associator_inv
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)]
    (F G H : C ⊛⥤ V) :
    (α_ F G H).inv.natTrans =
    (DayConvolution.associator F.functor G.functor H.functor).inv := by
  refine (Iso.inv_ext ?_).symm
  rw [← natTrans_associator, ← comp_natTrans, Iso.hom_inv_id, id_natTrans]

section Braided

/-- The braiding on `C ⊛⥤ V`, inherited from the Day-convolution
braiding of the underlying functors. -/
def dayFunctorBraiding
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)] [BraidedCategory C]
    [BraidedCategory V]
    (F G : C ⊛⥤ V) : F ⊗ G ≅ G ⊗ F where
  hom := .mk (DayConvolution.braiding F.functor G.functor).hom
  inv := .mk (DayConvolution.braiding F.functor G.functor).inv
  hom_inv_id := by
    ext1
    exact (DayConvolution.braiding F.functor G.functor).hom_inv_id
  inv_hom_id := by
    ext1
    exact (DayConvolution.braiding F.functor G.functor).inv_hom_id

/-- The Day-convolution monoidal structure on `C ⊛⥤ V` is braided when
`C` and `V` are.  This discharges, for the type synonym, what
`Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided` proves at the
level of individual convolutions. -/
instance dayFunctorBraided
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)] [BraidedCategory C]
    [BraidedCategory V] : BraidedCategory (C ⊛⥤ V) where
  braiding := dayFunctorBraiding
  braiding_naturality_right F G H f := by
    ext1
    simp only [comp_natTrans, natTrans_whiskerLeft, natTrans_whiskerRight]
    exact DayConvolution.braiding_naturality_right F.functor f.natTrans
  braiding_naturality_left f H := by
    ext1
    simp only [comp_natTrans, natTrans_whiskerLeft, natTrans_whiskerRight]
    exact DayConvolution.braiding_naturality_left f.natTrans H.functor
  hexagon_forward F G H := by
    ext1
    simp only [comp_natTrans, natTrans_associator, natTrans_whiskerLeft,
      natTrans_whiskerRight]
    exact DayConvolution.hexagon_forward F.functor G.functor H.functor
  hexagon_reverse F G H := by
    ext1
    simp only [comp_natTrans, natTrans_associator_inv, natTrans_whiskerLeft,
      natTrans_whiskerRight]
    exact DayConvolution.hexagon_reverse F.functor G.functor H.functor

end Braided

section Symmetric

/-- The Day-convolution monoidal structure on `C ⊛⥤ V` is symmetric when
`C` and `V` are, via `DayConvolution.symmetry`. -/
instance dayFunctorSymmetric
    [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V] [MonoidalCategory C]
    [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow (tensor
      C) d) (tensorRight v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), PreservesColimitsOfShape (CostructuredArrow
      (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow ((𝟭
      C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), PreservesColimitsOfShape (CostructuredArrow
      ((tensor C).prod (𝟭 C)) d) (tensorRight v)] [SymmetricCategory C]
    [SymmetricCategory V] : SymmetricCategory (C ⊛⥤ V) where
  toBraidedCategory := inferInstance
  symmetry F G := by
    ext1
    simp only [comp_natTrans, id_natTrans]
    exact DayConvolution.symmetry F.functor G.functor

end Symmetric

end

section AcceptanceTests

/- The three target instances for `V := Type v`, `C` small monoidal.
`noncomputable` because the underlying Day-convolution data is chosen
by colimit machinery; instance *synthesis* is what is being tested. -/

noncomputable example (C : Type v) [SmallCategory C] [MonoidalCategory C] :
    MonoidalCategory (MonoidalCategory.DayFunctor C (Type v)) :=
  inferInstance

noncomputable example (C : Type v) [SmallCategory C] [MonoidalCategory C]
    [BraidedCategory C] :
    BraidedCategory (MonoidalCategory.DayFunctor C (Type v)) :=
  inferInstance

noncomputable example (C : Type v) [SmallCategory C] [MonoidalCategory C]
    [SymmetricCategory C] :
    SymmetricCategory (MonoidalCategory.DayFunctor C (Type v)) :=
  inferInstance

end AcceptanceTests

end RS
