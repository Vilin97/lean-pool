/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SandwichRetract
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagCarrier

/-!
# The zigzag laws as a sandwich retract

The triangle identities of a Mod-internal duality datum are
carrier-level statements about insertion and contraction.  This
file rewrites them inside the monoidal structure of the category
of modules: the zig triangle says exactly that the sandwich
insertion followed by the sandwich contraction is the identity,
where both legs are built from the module unitors, the module
associator and the relative tensor of morphisms.

That form is what a strong monoidal functor transports, so it is
the shape in which base change consumes the zigzag laws.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The sandwich contraction descends the carrier
contraction**: reassociating, contracting the trailing pair and
collapsing the regular factor is the carrier contraction of the
zig triangle. -/
theorem modTensorπ_sandwichCon
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensorπ A (modTensorMod A M M') M ≫
        (sandwichCon A d).hom =
      zigContract A d.pair d.pair_linear := by
  refine zigContract_unique A d.pair d.pair_linear ?_
  have hcon : (sandwichCon A d).hom =
      modTensorAssocHom A M M' M ≫
        modTensorMap A (𝟙 M) (d.pairMod) ≫
        (modTensorUnitRight A M).hom := rfl
  have key : ∀ {Z : D}
      (h : modTensor A M (modTensorMod A M' M) ⟶ Z),
      (modTensorπ A M M' ▷ M.X) ≫
          modTensorAssocMid A M M' M ≫ h =
        (α_ M.X M'.X M.X).hom ≫ (M.X ◁ modTensorπ A M' M) ≫
          modTensorπ A M (modTensorMod A M' M) ≫ h := by
    intro Z h
    rw [← Category.assoc, whiskerRight_modTensorπ_assocMid,
      modTensorAssocCover]
    repeat' erw [Category.assoc]
  have tail : modTensorπ A M (modTensorMod A M' M) ≫
      modTensorMap A (𝟙 M) (d.pairMod) ≫
      (modTensorUnitRight A M).hom =
    (M.X ◁ d.pair) ≫ actRight A M.X := by
    rw [modTensorπ_map_assoc, Mod.id_hom',
      MonoidalCategory.id_tensorHom,
      show (d.pairMod).hom = d.pair from rfl,
      modTensorUnitRight_hom, modTensorπ_desc]
    rfl
  rw [hcon, modTensorπ_assocHom_assoc]
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ tail)) ?_
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]

/-- **Naming a map out of the regular module**: inserting the name
of a module map beside the carrier and projecting is the relative
tensor of the map with the identity. -/
theorem modTensorMap_of_regular
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    (P N : Mod D A)
    (f : regularMod A ⟶ P) :
    (modTensorUnitLeft A N).hom ≫ (λ_ N.X).inv ≫
        ((η[A] ≫ f.hom) ▷ N.X) ≫ modTensorπ A P N =
      modTensorMap A f (𝟙 N) := by
  have hlin : μ[A] ≫ f.hom = (A ◁ f.hom) ≫ actLeft A P.X :=
    f.isModHom.smul_hom
  have hname : (λ_ (regularMod A).X).inv ≫
      ((η[A] ≫ f.hom) ▷ (regularMod A).X) ≫ actRight A P.X =
    f.hom := by
    simp only [actRight, MonoidalCategory.comp_whiskerRight,
      Category.assoc]
    rw [BraidedCategory.braiding_naturality_left_assoc, ← hlin,
      reassoc_of% (IsCommMonObj.mul_comm A),
      MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]
  have hcond : (P.X ◁ actLeft A N.X) ≫ modTensorπ A P N =
      (α_ P.X A N.X).inv ≫ (actRight A P.X ▷ N.X) ≫
        modTensorπ A P N := by
    have h := modTensor_condition A P N
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    rw [h, Iso.inv_hom_id_assoc]
  apply modTensor_hom_ext
  rw [modTensorπ_map, Mod.id_hom', MonoidalCategory.tensorHom_id,
    modTensorUnitLeft_hom, modTensorπ_desc_assoc,
    leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    hcond, associator_inv_naturality_left_assoc,
    ← leftUnitor_inv_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [hname]

/-- **The sandwich insertion is the copairing insertion**: on
carriers, expanding the unit and inserting the copairing is
naming the copairing beside the carrier. -/
theorem sandwichIns_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (sandwichIns A d).hom =
      (λ_ M.X).inv ≫ ((η[A] ≫ d.copair) ▷ M.X) ≫
        modTensorπ A (modTensorMod A M M') M := by
  have h := modTensorMap_of_regular A (modTensorMod A M M') M
    (d.copairMod)
  change (modTensorUnitLeft A M).inv ≫
    modTensorMap A (d.copairMod) (𝟙 M) = _
  rw [← h, Iso.inv_hom_id_assoc]
  rfl

/-- **The sandwich composite is the zig composite**: the retract
word of the double-dual sandwich has the carrier zig triangle as
its underlying morphism. -/
theorem sandwich_zig_carrier
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (sandwichIns A d ≫ sandwichCon A d).hom =
      (λ_ M.X).inv ≫ ((η[A] ≫ d.copair) ▷ M.X) ≫
        zigContract A d.pair d.pair_linear := by
  change (sandwichIns A d).hom ≫ (sandwichCon A d).hom = _
  rw [sandwichIns_hom]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (modTensorπ_sandwichCon A d)

/-- **The zig triangle is the sandwich retract identity**: a
duality datum satisfies the carrier zig law exactly when the
module is a retract of its double-dual sandwich through the
canonical insertion and contraction. -/
theorem sandwich_zig_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    sandwichIns A d ≫ sandwichCon A d = 𝟙 M ↔
      (λ_ M.X).inv ≫ ((η[A] ≫ d.copair) ▷ M.X) ≫
        zigContract A d.pair d.pair_linear = 𝟙 M.X := by
  rw [← sandwich_zig_carrier]
  constructor
  · intro h
    rw [h]
    exact Mod.id_hom' M
  · intro h
    refine Mod.Hom.ext ?_
    rw [h]
    exact (Mod.id_hom' M).symm

/-- **The dual sandwich contraction descends the dual carrier
contraction**. -/
theorem modTensorπ_sandwichConR
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    modTensorπ A M' (modTensorMod A M M') ≫
        (sandwichConR A d).hom =
      zagContract A d.pair d.pair_linear := by
  refine zagContract_unique A d.pair d.pair_linear ?_
  have hcon : (sandwichConR A d).hom =
      modTensorAssocInv A M' M M' ≫
        modTensorMap A (d.pairMod) (𝟙 M') ≫
        (modTensorUnitLeft A M').hom := rfl
  have key : ∀ {Z : D}
      (h : modTensor A (modTensorMod A M' M) M' ⟶ Z),
      (M'.X ◁ modTensorπ A M M') ≫
          modTensorAssocInvMid A M' M M' ≫ h =
        (α_ M'.X M.X M'.X).inv ≫
          (modTensorπ A M' M ▷ M'.X) ≫
          modTensorπ A (modTensorMod A M' M) M' ≫ h := by
    intro Z h
    rw [← Category.assoc, whiskerLeft_modTensorπ_assocInvMid,
      modTensorAssocInvCover]
    repeat' erw [Category.assoc]
  have tail : modTensorπ A (modTensorMod A M' M) M' ≫
      modTensorMap A (d.pairMod) (𝟙 M') ≫
      (modTensorUnitLeft A M').hom =
    (d.pair ▷ M'.X) ≫ actLeft A M'.X := by
    rw [modTensorπ_map_assoc, Mod.id_hom',
      MonoidalCategory.tensorHom_id,
      show (d.pairMod).hom = d.pair from rfl,
      modTensorUnitLeft_hom, modTensorπ_desc]
    rfl
  rw [hcon, modTensorπ_assocInv_assoc]
  refine Eq.trans (key _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ tail)) ?_
  rw [← MonoidalCategory.comp_whiskerRight_assoc]

/-- **Naming a map out of the regular module on the right**. -/
theorem modTensorMap_of_regular_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    (N P : Mod D A)
    (f : regularMod A ⟶ P) :
    (modTensorUnitRight A N).hom ≫ (ρ_ N.X).inv ≫
        (N.X ◁ (η[A] ≫ f.hom)) ≫ modTensorπ A N P =
      modTensorMap A (𝟙 N) f := by
  have hlin : μ[A] ≫ f.hom = (A ◁ f.hom) ≫ actLeft A P.X :=
    f.isModHom.smul_hom
  have hname : (ρ_ A).inv ≫ (A ◁ (η[A] ≫ f.hom)) ≫
      actLeft A P.X = f.hom := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      ← hlin, MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]
  have hcond : (actRight A N.X ▷ P.X) ≫ modTensorπ A N P =
      (α_ N.X A P.X).hom ≫ (N.X ◁ actLeft A P.X) ≫
        modTensorπ A N P := by
    have h := modTensor_condition A N P
    rw [modTensorLegM, modTensorLegN, Category.assoc] at h
    exact h
  apply modTensor_hom_ext
  rw [modTensorπ_map, Mod.id_hom', MonoidalCategory.id_tensorHom,
    modTensorUnitRight_hom, modTensorπ_desc_assoc,
    rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    hcond, associator_naturality_right_assoc,
    ← whiskerLeft_rightUnitor_inv_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [hname]

/-- **The dual sandwich insertion is the copairing insertion**. -/
theorem sandwichInsR_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (sandwichInsR A d).hom =
      (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ d.copair)) ≫
        modTensorπ A M' (modTensorMod A M M') := by
  have h := modTensorMap_of_regular_right A M'
    (modTensorMod A M M') (d.copairMod)
  change (modTensorUnitRight A M').inv ≫
    modTensorMap A (𝟙 M') (d.copairMod) = _
  rw [← h, Iso.inv_hom_id_assoc]
  rfl

/-- **The dual sandwich composite is the zag composite**. -/
theorem sandwich_zag_carrier
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    (sandwichInsR A d ≫ sandwichConR A d).hom =
      (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ d.copair)) ≫
        zagContract A d.pair d.pair_linear := by
  change (sandwichInsR A d).hom ≫ (sandwichConR A d).hom = _
  rw [sandwichInsR_hom]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (modTensorπ_sandwichConR A d)

/-- **The zag triangle is the dual sandwich retract
identity**. -/
theorem sandwich_zag_iff
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A}
    (d : ModDualityDatum A M M') :
    sandwichInsR A d ≫ sandwichConR A d = 𝟙 M' ↔
      (ρ_ M'.X).inv ≫ (M'.X ◁ (η[A] ≫ d.copair)) ≫
        zagContract A d.pair d.pair_linear = 𝟙 M'.X := by
  rw [← sandwich_zag_carrier]
  constructor
  · intro h
    rw [h]
    exact Mod.id_hom' M'
  · intro h
    refine Mod.Hom.ext ?_
    rw [h]
    exact (Mod.id_hom' M').symm

end RS
